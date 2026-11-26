-- Prove2me | solution 1 for LogLogJam.eq_18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:36:52.046872+00:00
-- url     : https://prove2.me/submissions/9b6ae858-76ab-4f1e-ac35-66551e9cc08f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LogLogJam_GaussProtocol
import Theorems.Thm_LogLogJam_eq_13
import Theorems.Thm_LogLogJam_posterior_one_step_law
import Theorems.Thm_LogLogJam_posterior_predictive_density
import Theorems.Thm_LogLogJam_history_reference_density

open LogLogJam MeasureTheory
open scoped ENNReal
open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000

private def advance (x : ℝ≥0∞) := x + x ^ (1 / 2 : ℝ)

private theorem advance_mono : Monotone advance := fun x y h =>
  add_le_add h (ENNReal.rpow_le_rpow h (by norm_num))

private theorem advance_growth (x : ℝ≥0∞) (n : ℕ) :
    x + (n : ℝ≥0∞) * x^(1/2 : ℝ) ≤ advance^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : x ≤ advance^[n] x := le_trans le_self_add ih
    rw [Function.iterate_succ_apply']
    unfold advance
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc]
    exact add_le_add ih (ENNReal.rpow_le_rpow hx (by norm_num))

private theorem advance_meas : Measurable advance :=
  measurable_id.add (measurable_id.pow_const _)

private theorem advance_iter_meas (n : ℕ) : Measurable (advance^[n]) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp advance_meas

private theorem weighted_advance_jensen {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w f : X → ℝ≥0∞) (hw : Measurable w) (hf : Measurable f)
    (hm : ∫⁻ x, w x ∂ν = 1) (n : ℕ) :
    (∫⁻ x, w x * advance^[n] (f x) ∂ν) ≤ advance^[n] (∫⁻ x, w x * f x ∂ν) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    let z := fun x => advance^[n] (f x)
    have hz : Measurable z := (advance_iter_meas n).comp hf
    have hroot : (∫⁻ x, w x * (z x)^(1/2 : ℝ) ∂ν) ≤
        (∫⁻ x, w x * z x ∂ν)^(1/2 : ℝ) := by
      have hh := ENNReal.lintegral_mul_norm_pow_le (μ := ν)
        (f := fun x => w x * z x) (g := w) (hw.mul hz).aemeasurable hw.aemeasurable
        (p := 1/2) (q := 1/2) (by norm_num) (by norm_num) (by norm_num)
      rw [hm] at hh
      simp only [ENNReal.one_rpow, mul_one] at hh
      convert hh using 1
      apply lintegral_congr
      intro x
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      have hw2 : (w x)^(1/2 : ℝ) * (w x)^(1/2 : ℝ) = w x := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)]
        norm_num
      rw [mul_right_comm, hw2]
    simp only [Function.iterate_succ_apply', advance, mul_add]
    rw [lintegral_add_left (f := fun x => w x * advance^[n] (f x)) (hw.mul hz)]
    exact add_le_add ih (hroot.trans (ENNReal.rpow_le_rpow ih (by norm_num)))

private theorem advance_iter_ofReal (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    advance^[n] (ENNReal.ofReal x) = ENNReal.ofReal (fIter n x) := by
  have hpos (m : ℕ) : 0 ≤ fIter m x := by
    induction m with
    | zero => exact hx
    | succ m ih =>
      change 0 ≤ fStep^[m+1] x
      rw [Function.iterate_succ_apply']
      exact add_nonneg ih (Real.sqrt_nonneg _)
  induction n with
  | zero => rfl
  | succ n ih =>
    change advance^[n+1] _ = ENNReal.ofReal (fStep^[n+1] x)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    change _ = ENNReal.ofReal (fIter n x + Real.sqrt (fIter n x))
    unfold advance
    rw [ENNReal.ofReal_add (hpos n) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ENNReal.ofReal_rpow_of_nonneg (hpos n) (by norm_num)]


private theorem derivMeasurable {X : Type*} [MeasurableSpace X] (q : ℝ → X → ℝ)
    (hC : ∀ x, ContDiff ℝ 1 (fun t => q t x)) (hm : ∀ t, Measurable (q t)) :
    Measurable (fun z : ℝ × X => deriv (fun t => q t z.2) z.1) := by
  apply measurable_uncurry_of_continuous_of_measurable (fun x => (hC x).continuous_deriv_one)
  intro t
  let d (n : ℕ) : ℝ := 1 / (n+1 : ℝ)
  have hlim : Tendsto d atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => by change 0 < 1 / (n+1 : ℝ); positivity⟩
  apply measurable_of_tendsto_metrizable (f := fun (n : ℕ) x => (d n)⁻¹ * (q (t+d n) x - q t x))
    (fun n => measurable_const.mul ((hm _).sub (hm _)))
  apply tendsto_pi_nhds.mpr
  intro x
  exact ((hC x).differentiable_one t).hasDerivAt.tendsto_slope_zero_right.comp hlim

private theorem posterior_potential_measurable {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam) (t : ℕ) (ht : t ≤ T) :
    Measurable (fun H : {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)} =>
      Gpot lam H.val) := by
  let G := {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
  obtain ⟨μ, hs, hc⟩ := history_reference_density P t ht
  let _ := hs
  obtain ⟨hpos, _, hC, hm, _, _⟩ := hc lam hlam
  let ν := (volume : Measure ℝ).restrict (Set.Ico 0 Real.pi)
  let q (s : ℝ) (H : G) := histDens lam s H.1
  let Q (s : ℝ) (H : G) := ENNReal.ofReal (q s H)
  let S (s : ℝ) (H : G) := ENNReal.ofReal ((deriv (fun y => Real.log (q y H)) s)^2)
  let W (s : ℝ) (H : G) := Q s H * S s H
  let Z (H : G) := postNorm lam H.1
  have hqm : Measurable (Function.uncurry q) :=
    measurable_uncurry_of_continuous_of_measurable (fun H => (hC H).continuous) hm
  have hQ : Measurable (Function.uncurry Q) := hqm.ennreal_ofReal
  have hS : Measurable (Function.uncurry S) :=
    ((derivMeasurable (fun s H => Real.log (q s H)) (fun H => (hC H).log (fun s => (hpos s H).ne'))
      (fun s => (hm s).log)).pow_const 2).ennreal_ofReal
  have hW : Measurable (Function.uncurry W) := hQ.mul hS
  have hZ (H : G) : 0 < Z H := by
    dsimp [Z,postNorm]
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    apply intervalIntegral.integral_pos Real.pi_pos (hC H).continuous.continuousOn
      (fun s _ => (hpos s H).le)
    exact ⟨0,⟨le_rfl,Real.pi_pos.le⟩,hpos 0 H⟩
  have hZi (H : G) : ENNReal.ofReal (Z H) = ∫⁻ s, Q s H ∂ν :=
    ofReal_integral_eq_lintegral_ofReal ((hC H).continuous.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
      (Eventually.of_forall fun s => (hpos s H).le)
  have hZinv (H : G) : (ENNReal.ofReal (Z H))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (hZ H)).ne'
  have point (H : G) : postFisher lam H.1 = (ENNReal.ofReal (Z H))⁻¹ * ∫⁻ s, W s H ∂ν := by
    rw [← lintegral_const_mul' _ _ (hZinv H)]
    apply lintegral_congr
    intro s
    have hl : (fun a => Real.log (post lam H.1 a)) = (fun a => Real.log (q a H) - Real.log (Z H)) := by
      funext a; exact Real.log_div (hpos a H).ne' (hZ H).ne'
    change ENNReal.ofReal (q s H / Z H) * ENNReal.ofReal
      ((deriv (fun a => Real.log (post lam H.1 a)) s)^2) = _
    rw [hl, deriv_sub_const, ENNReal.ofReal_div_of_pos (hZ H), div_eq_mul_inv]
    dsimp only [W,Q,S]
    ac_rfl
  have hpost : Measurable (fun H : G => postFisher lam H.1) := by
    simp_rw [point,hZi]
    exact (hQ.lintegral_prod_left (μ := ν)).inv.mul (hW.lintegral_prod_left (μ := ν))
  exact (measurable_const.add hpost).div_const _


private theorem sigma_meas_slice {ι : Type*} {B : ι → Type*} [∀ i, MeasurableSpace (B i)]
    {Y : Type*} [MeasurableSpace Y] (f : (Σ i, B i) → Y)
    (h : ∀ i, Measurable (fun x : B i => f ⟨i,x⟩)) : Measurable f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr (fun i => h i hs)

private theorem sumCopies_meas (t : ℕ) : Measurable (copies (t := t)) := by
  have tag : Measurable (fun o : Obs => o.1) := sigma_meas_slice _ (fun _ => measurable_const)
  exact Finset.measurable_fun_sum _ (fun i _ => tag.comp (measurable_pi_apply i))

private def admissible (o : Obs) : Prop := IsCov o.1 (Matrix.of o.2.1)

private theorem snoc_admissible {t : ℕ} (H : Hist t) (s : Seed) (y : Q s.1 → ℝ)
    (hH : ∀ i, admissible (H i)) (hs : IsCov s.1 (Matrix.of s.2)) :
    ∀ i, admissible (Fin.snoc (α := fun _ : Fin (t+1) => Obs) H ⟨s.1,(s.2,y)⟩ i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; exact hs
  · rw [Fin.snoc_castSucc]; exact hH j

private theorem attach_meas {t k : ℕ} (H : Hist t) (W : Q k → Q k → ℝ) :
    Measurable (fun y : Q k → ℝ => Fin.snoc (α := fun _ : Fin (t+1) => Obs) H ⟨k,(W,y)⟩) := by
  have mk : Measurable (Sigma.mk (β := fun j => (Q j → Q j → ℝ) × (Q j → ℝ)) k) := by
    intro B hB
    exact MeasurableSpace.measurableSet_iInf.mp hB k
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [Function.comp_def] using mk.comp (measurable_const.prodMk measurable_id)
  · simpa [Function.comp_def] using (measurable_const (a := H j) (α := Q k → ℝ))

private theorem initial_pot (lam : ℝ) (hlam : 1 < lam) :
    Gpot lam (Fin.elim0 : Hist 0) = ENNReal.ofReal (1/(8*Real.pi*energy lam)^2) := by
  have he : 0 < energy lam := by unfold energy; positivity
  simp [Gpot, postFisher, circFisher, post, histDens, one_div,
    ENNReal.ofReal_inv_of_pos (show 0 < (8*Real.pi*energy lam)^2 by positivity)]

private theorem hist_physical_mono {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ) (t : ℕ)
    (F U : Hist t → ℝ≥0∞)
    (h : ∀ H : Hist t, (∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) → F H ≤ U H) :
    histInt lam θ P t F ≤ histInt lam θ P t U := by
  induction t with
  | zero => exact h _ (fun i => Fin.elim0 i)
  | succ t ih =>
    apply ih
    intro H hH
    apply lintegral_mono_ae
    filter_upwards [P.seed_cov t H] with s hs
    apply lintegral_mono
    intro y
    apply mul_le_mul_right (h _ _) _
    exact snoc_admissible H s y hH hs

private theorem posterior_supermartingale_comparison {T : ℕ} (P : GaussProtocol T)
    (lam : ℝ) (hlam : 1 < lam) (S : ℕ) (hS : CopiesLe lam P S)
    (Φ : (t : ℕ) → Hist t → ℝ≥0∞) (F : Hist T → ℝ≥0∞)
    (hF : Measurable (fun H : {H : Hist T // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)} => F H.val))
    (hΦ : ∀ t ≤ T, Measurable (fun H : {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)} =>
      Φ t H.val))
    (hstep : ∀ t < T, ∀ H : Hist t, (∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) →
      (∫⁻ s, nextCondExp lam H s.1 s.2 (Φ (t+1)) ∂(P.seed t H)) ≤ Φ t H)
    (hterm : ∀ H : Hist T, (∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) →
      copies H ≤ S → F H ≤ Φ T H) :
    ENNReal.ofReal (1 / Real.pi) * (∫⁻ θ in Set.Ico 0 Real.pi, histInt lam θ P T F) ≤
      Φ 0 Fin.elim0 := by
  let avg (t : ℕ) (U : Hist t → ℝ≥0∞) := ENNReal.ofReal (1 / Real.pi) *
    ∫⁻ θ in Set.Ico 0 Real.pi, histInt lam θ P t U
  have hi (t : ℕ) (ht : t ≤ T) : avg t (Φ t) ≤ Φ 0 Fin.elim0 := by
    induction t with
    | zero =>
      simp [avg,histInt,Real.volume_Ico,ENNReal.ofReal_inv_of_pos Real.pi_pos,one_div]
      rw [mul_left_comm, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr Real.pi_pos).ne' ENNReal.ofReal_ne_top, mul_one]
    | succ t ih =>
      refine le_trans ?_ (ih (by omega))
      dsimp only [avg]
      rw [posterior_one_step_law P lam hlam t ht _ (hΦ _ ht)]
      gcongr with θ
      exact hist_physical_mono P lam θ t _ _ (hstep t ht)
  refine le_trans ?_ (hi T le_rfl)
  change _ ≤ ENNReal.ofReal _ * _
  gcongr with θ
  let G := {H : Hist T // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
  obtain ⟨μ, _, hx⟩ := history_reference_density P T le_rfl
  obtain ⟨hpos, _, _, hm, _, hrepr⟩ := hx lam hlam
  let b (H : Hist T) : ℝ≥0∞ := Set.indicator {H : Hist T | S < copies H} 1 H
  have hc : Measurable fun H : G => copies H.val := (sumCopies_meas T).comp measurable_subtype_coe
  have hb : Measurable fun H : G => b H.val :=
    ((measurable_const (a := (1 : ℝ≥0∞))).indicator
      (measurableSet_lt measurable_const (sumCopies_meas T))).comp measurable_subtype_coe
  have hin : (∫⁻ H : G, ENNReal.ofReal (histDens lam θ H.1) * b H.1 ∂μ) = 0 :=
    (hrepr θ b hb).symm.trans (hS θ)
  have hz := (lintegral_eq_zero_iff ((hm θ).ennreal_ofReal.mul hb)).mp hin
  rw [hrepr θ F hF, hrepr θ (Φ T) (hΦ _ le_rfl)]
  apply lintegral_mono_ae
  filter_upwards [hz] with H hzero
  apply mul_le_mul_right (hterm H.1 H.2 _) _
  by_contra! hh
  have hb1 : b H.val = 1 := by simp [b, Set.indicator_of_mem, hh]
  change ENNReal.ofReal (histDens lam θ H.val) * b H.val = 0 at hzero
  rw [hb1, mul_one] at hzero
  exact (ENNReal.ofReal_pos.mpr (hpos θ H)).ne' hzero

theorem solution {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam) (S : ℕ)
    (hS : CopiesLe lam P S) :
    expG lam P ≤ ENNReal.ofReal (fIter S (1 / (8 * Real.pi * energy lam) ^ 2)) := by
  classical
  let Φ (t : ℕ) (H : Hist t) : ℝ≥0∞ :=
    if copies H ≤ S then advance^[S-copies H] (Gpot lam H) else 0
  have hphi (t : ℕ) (ht : t ≤ T) : Measurable (fun H : {H : Hist t //
      ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)} => Φ t H.val) := by
    have hm : Measurable (fun H : {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)} => copies H.val) := (sumCopies_meas t).comp measurable_subtype_coe
    have hG := posterior_potential_measurable P lam hlam t ht
    apply Measurable.ite (measurableSet_le hm measurable_const)
    · let n := fun H : {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)} => S-copies H.val
      have hn : Measurable n := measurable_const.sub hm
      have hmprod : Measurable (fun p : ℕ × ℝ≥0∞ => advance^[p.1] p.2) :=
        measurable_from_prod_countable_right (fun j => advance_iter_meas j)
      exact hmprod.comp (hn.prodMk hG)
    · exact measurable_const
  have hstage (t : ℕ) (ht : t < T) (H : Hist t) (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) :
      (∫⁻ s, nextCondExp lam H s.1 s.2 (Φ (t+1)) ∂(P.seed t H)) ≤ Φ t H := by
    haveI := P.isMarkov t
    rw [← show (∫⁻ _s : Seed, Φ t H ∂(P.seed t H)) = Φ t H by simp]
    apply lintegral_mono_ae
    filter_upwards [P.seed_cov t H] with s hs
    let H' (y : Q s.1 → ℝ) : Hist (t+1) := Fin.snoc H ⟨s.1,(s.2,y)⟩
    have hc (y) : copies (H' y) = copies H + s.1 := by
      simp [H', copies, Fin.sum_univ_castSucc]
    have hg (y) : ∀ i, admissible ((H' y) i) := snoc_admissible H s y hH hs
    change (∫⁻ y, ENNReal.ofReal (predDens lam H s.1 s.2 y) * Φ (t+1) (H' y)) ≤ Φ t H
    by_cases hb : copies H + s.1 ≤ S
    · have hr : copies H ≤ S := by omega
      simp only [Φ, hc, if_pos hb, if_pos hr]
      let Good := {J : Hist (t+1) // ∀ i, IsCov (J i).1 (Matrix.of (J i).2.1)}
      let lift (y : Q s.1 → ℝ) : Good := ⟨H' y, hg y⟩
      have hplain : Measurable H' := attach_meas H s.2
      have hlift : Measurable lift := hplain.subtype_mk
      have hgm : Measurable (fun y => Gpot lam (H' y)) := by
        change Measurable ((fun J : Good => Gpot lam J.val) ∘ lift)
        exact Measurable.comp (posterior_potential_measurable P lam hlam (t+1) ht) hlift
      obtain ⟨hw, hmass⟩ := posterior_predictive_density lam hlam H hH s.1 s.2 hs
      refine (weighted_advance_jensen volume _ _ hw hgm hmass _).trans ?_
      have hrec := (eq_13 lam hlam H hH s.1 s.2 hs).trans (advance_growth _ _)
      have hn : S - copies H = (S-(copies H+s.1)) + s.1 := by omega
      rw [hn, Function.iterate_add_apply]
      exact (advance_mono.iterate _) hrec
    · simp [Φ, hc, hb]
  have hterm (H : Hist T) (_ : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (hb : copies H ≤ S) :
      Gpot lam H ≤ Φ T H := by
    simp only [Φ, if_pos hb]
    exact le_trans le_self_add (advance_growth _ _)
  have hh := posterior_supermartingale_comparison P lam hlam S hS Φ (Gpot lam) (posterior_potential_measurable P lam hlam T le_rfl) hphi hstage hterm
  refine hh.trans_eq ?_
  simp only [Φ, copies, Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_le, if_true, Nat.sub_zero]
  rw [initial_pot lam hlam, advance_iter_ofReal _ _ (by positivity)]

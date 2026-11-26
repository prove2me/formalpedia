-- Prove2me | solution 1 for LogLogJam.expected_batch_budget
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:27:52.352819+00:00
-- url     : https://prove2.me/submissions/9307ab0d-7dae-4439-a446-0a8515f44173

import Definitions.Def_LogLogJam_GaussProtocol
import Theorems.Thm_LogLogJam_gaussian_seed_mass_one

open LogLogJam Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

set_option maxHeartbeats 500000

private theorem sigma_meas_mk {ι : Type*} {B : ι → Type*} [∀ i, MeasurableSpace (B i)] (i : ι) :
    Measurable (Sigma.mk (β := B) i) := by
  intro s hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) i

private theorem sigma_meas_slice {ι : Type*} {B : ι → Type*} [∀ i, MeasurableSpace (B i)]
    {Y : Type*} [MeasurableSpace Y] (f : (Σ i, B i) → Y)
    (h : ∀ i, Measurable (fun x : B i => f ⟨i,x⟩)) : Measurable f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr (fun i => h i hs)

private theorem sigma_meas_tag {B : ℕ → Type*} [∀ i, MeasurableSpace (B i)] :
    Measurable (fun x : (Σ i, B i) => x.1) :=
  sigma_meas_slice _ (fun _ => measurable_const)

private def readFiber {B : ℕ → Type*} [∀ i, Inhabited (B i)] (k : ℕ) (s : Σ i, B i) : B k :=
  if h : s.1 = k then h ▸ s.2 else default

private theorem sigma_meas_read {B : ℕ → Type*} [∀ i, MeasurableSpace (B i)]
    [∀ i, Inhabited (B i)] (k : ℕ) : Measurable (readFiber (B := B) k) := by
  apply sigma_meas_slice
  intro i
  by_cases h : i = k
  · subst k; simp [readFiber]; exact measurable_id
  · simp [readFiber,h]

private theorem sigma_meas_prod {B : ℕ → Type*} [∀ i, MeasurableSpace (B i)]
    [∀ i, Inhabited (B i)] {X : Type*} [MeasurableSpace X] (f : X × (Σ i, B i) → ℝ≥0∞)
    (h : ∀ k, Measurable fun p : X × B k => f (p.1, ⟨k,p.2⟩)) : Measurable f := by
  classical
  have htag : Measurable fun p : X × (Σ i, B i) => p.2.1 := sigma_meas_tag.comp measurable_snd
  let g (k : ℕ) (p : X × (Σ i, B i)) :=
    if p.2.1 = k then f (p.1,⟨k,readFiber k p.2⟩) else 0
  have hg (k : ℕ) : Measurable (g k) := by
    apply Measurable.ite ((measurableSet_singleton k).preimage htag)
    · exact (h k).comp (measurable_fst.prodMk ((sigma_meas_read k).comp measurable_snd))
    · exact measurable_const
  have heq : f = fun p => ⨆ k, g k p := by
    funext p
    rcases p with ⟨x, ⟨i,y⟩⟩
    apply le_antisymm
    · exact le_iSup_of_le i (by simp [g, readFiber])
    · refine iSup_le fun k => ?_
      by_cases hki : i = k
      · subst k; simp [g, readFiber]
      · simp [g, hki]
  rw [heq]
  exact Measurable.iSup hg

private theorem meas_density_pair (k : ℕ) (V : Matrix (Q k) (Q k) ℝ) :
    Measurable fun p : (Q k → Q k → ℝ) × (Q k → ℝ) =>
      ENNReal.ofReal (outDens k (V + Matrix.of p.1) p.2) := by
  let D (p : (Q k → Q k → ℝ) × (Q k → ℝ)) : Matrix (Q k) (Q k) ℝ := V + Matrix.of p.1
  have hD : Continuous D := continuous_const.add continuous_fst
  have hi (i j : Q k) : Measurable (fun p => (D p)⁻¹ i j) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact hD.matrix_det.measurable.inv.mul
      ((continuous_apply j).comp ((continuous_apply i).comp hD.matrix_adjugate)).measurable
  change Measurable (fun p => ENNReal.ofReal (Real.exp (-(p.2 ⬝ᵥ ((D p)⁻¹ *ᵥ p.2))) /
    (Real.pi ^ k * Real.sqrt (D p).det)))
  simp only [dotProduct, Matrix.mulVec]
  have hy (i : Q k) : Measurable (fun p : (Q k → Q k → ℝ) × (Q k → ℝ) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  apply Measurable.ennreal_ofReal
  apply Measurable.div
  · apply Real.continuous_exp.measurable.comp
    apply Measurable.neg
    exact Finset.measurable_fun_sum _ fun i _ => (hy i).mul (Finset.measurable_fun_sum _ fun j _ =>
      (hi i j).mul (hy j))
  · exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hD.matrix_det.measurable)

private theorem meas_snoc {X : Type*} [MeasurableSpace X] {t k : ℕ}
    {h : X → Hist t} {w : X → (Q k → Q k → ℝ) × (Q k → ℝ)}
    (hh : Measurable h) (hw : Measurable w) :
    Measurable (fun p => Fin.snoc (α := fun _ : Fin (t+1) => Obs) (h p) (⟨k,w p⟩ : Obs)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [Function.comp_def] using (sigma_meas_mk (B := fun n => (Q n → Q n → ℝ) × (Q n → ℝ)) k).comp hw
  · simpa [Function.comp_def] using (measurable_pi_apply j).comp hh

private theorem measurable_next {T t : ℕ} (P : GaussProtocol T) (lam θ : ℝ)
    (F : Hist (t+1) → ℝ≥0∞) (hF : Measurable F) :
    Measurable fun H : Hist t => ∫⁻ s, ∫⁻ y,
      ENNReal.ofReal (outDens s.1 (VsqK lam θ s.1 + Matrix.of s.2) y) *
        F (Fin.snoc H ⟨s.1,(s.2,y)⟩) ∂volume ∂(P.seed t H) := by
  have := P.isMarkov t
  apply Measurable.lintegral_kernel_prod_right
  apply sigma_meas_prod
  intro k
  dsimp only [Function.uncurry]
  apply Measurable.lintegral_prod_right (ν := (volume : Measure (Q k → ℝ)))
  let X := (Hist t × (Q k → Q k → ℝ)) × (Q k → ℝ)
  have hw : Measurable (fun p : X => (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hh : Measurable (fun p : X => p.1.1) := measurable_fst.comp measurable_fst
  exact ((meas_density_pair k (VsqK lam θ k)).comp hw).mul (hF.comp (meas_snoc hh hw))

private def stepInt {t : ℕ} {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ)
    (F : Hist (t+1) → ℝ≥0∞) (H : Hist t) : ℝ≥0∞ :=
  ∫⁻ s, ∫⁻ y, ENNReal.ofReal (outDens s.1 (VsqK lam θ s.1 + Matrix.of s.2) y) *
       F (Fin.snoc H ⟨s.1,(s.2,y)⟩) ∂volume ∂(P.seed t H)

private theorem measurable_seed_integrand {t : ℕ} {lam θ : ℝ} (F : Hist (t+1) → ℝ≥0∞)
    (hF : Measurable F) (H : Hist t) :
    Measurable fun s : Seed => ∫⁻ y, ENNReal.ofReal (outDens s.1
      (VsqK lam θ s.1 + Matrix.of s.2) y) * F (Fin.snoc H ⟨s.1,(s.2,y)⟩) := by
  apply sigma_meas_slice
  intro k
  apply Measurable.lintegral_prod_right (ν := (volume : Measure (Q k → ℝ)))
  exact (meas_density_pair k (VsqK lam θ k)).mul (hF.comp (meas_snoc measurable_const measurable_id))

private theorem hist_add {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ) (t : ℕ)
    (F G : Hist t → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) :
    histInt lam θ P t (fun H => F H + G H) = histInt lam θ P t F + histInt lam θ P t G := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change histInt lam θ P t _ = histInt lam θ P t (stepInt P lam θ F) +
      histInt lam θ P t (stepInt P lam θ G)
    rw [← ih (stepInt P lam θ F) (stepInt P lam θ G) (measurable_next P lam θ F hF) (measurable_next P lam θ G hG)]
    congr 1; funext H
    simp only [stepInt, mul_add]
    rw [← lintegral_add_left (measurable_seed_integrand F hF H) _]
    apply lintegral_congr
    intro s
    apply lintegral_add_left
    exact (meas_density_pair s.1 (VsqK lam θ s.1)).comp
        (measurable_const.prodMk measurable_id) |>.mul
      (hF.comp (meas_snoc measurable_const (measurable_const.prodMk measurable_id)))

private theorem hist_scale {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ) (t : ℕ)
    (r : ℝ≥0∞) (F : Hist t → ℝ≥0∞) (hF : Measurable F) :
    histInt lam θ P t (fun H => r * F H) = r * histInt lam θ P t F := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change histInt lam θ P t _ = r * histInt lam θ P t (stepInt P lam θ F)
    rw [← ih (stepInt P lam θ F) (measurable_next P lam θ F hF)]
    congr 1; funext H
    simp only [stepInt, mul_left_comm _ r]
    rw [← lintegral_const_mul r (measurable_seed_integrand F hF H)]
    apply lintegral_congr
    intro s
    apply lintegral_const_mul
    exact (meas_density_pair s.1 (VsqK lam θ s.1)).comp
        (measurable_const.prodMk measurable_id) |>.mul
      (hF.comp (meas_snoc measurable_const (measurable_const.prodMk measurable_id)))

private theorem hist_mono {lam θ : ℝ} {T : ℕ} (P : GaussProtocol T) (t : ℕ)
    {F G : Hist t → ℝ≥0∞} (h : ∀ H, F H ≤ G H) :
    histInt lam θ P t F ≤ histInt lam θ P t G := by
  induction t with
  | zero => exact h _
  | succ t ih =>
    apply ih
    intro H
    apply lintegral_mono
    intro s
    apply lintegral_mono
    intro y
    exact mul_le_mul_right (h _) _

private theorem meas_copies (t : ℕ) : Measurable (fun H : Hist t => copies H) := by
  unfold copies
  exact Finset.measurable_fun_sum _ (fun i _ => sigma_meas_tag.comp (measurable_pi_apply i))

private theorem copies_snoc {t : ℕ} (H : Hist t) (s : Seed) (y : Q s.1 → ℝ) :
    copies (Fin.snoc H (⟨s.1,(s.2,y)⟩ : Obs)) = copies H + s.1 := by
  simp only [copies, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

theorem solution (lam : ℝ) (hlam : 1 < lam) {T : ℕ} (P : GaussProtocol T)
    (S : ℕ) (hS : CopiesLe lam P S) :
    ∑ t ∈ Finset.range T, ENNReal.ofReal (1/Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi,
      histInt lam θ P t (fun H => ∫⁻ s, (s.1 : ℝ≥0∞) ∂(P.seed t H)) ≤ S := by
  let K (t : ℕ) (H : Hist t) : ℝ≥0∞ := ∫⁻ s, (s.1 : ℝ≥0∞) ∂(P.seed t H)
  have hK (t : ℕ) : Measurable (K t) := by
    have := P.isMarkov t
    apply Measurable.lintegral_kernel_prod_right
    exact measurable_of_countable _ |>.comp (sigma_meas_tag.comp measurable_snd)
  have hmass (θ : ℝ) (t : ℕ) (s : Seed) (h : IsCov s.1 (Matrix.of s.2)) :=
    gaussian_seed_mass_one lam θ hlam s.1 s.2 h
  have hconst (θ : ℝ) (t : ℕ) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
      histInt lam θ P t (fun _ => c) = c := by
    induction t with
    | zero => rfl
    | succ t ih =>
      change histInt lam θ P t (stepInt P lam θ (fun _ => c)) = c
      apply Eq.trans _ ih
      apply congrArg (histInt lam θ P t)
      funext H
      have := P.isMarkov t
      unfold stepInt
      simp only [lintegral_mul_const' c _ hc]
      have hm : (fun s : Seed => (∫⁻ y, ENNReal.ofReal
          (outDens s.1 (VsqK lam θ s.1 + Matrix.of s.2) y))) =ᵐ[P.seed t H] fun _ => 1 := by
        filter_upwards [P.seed_cov t H] with s hs
        exact hmass θ t s hs
      rw [lintegral_congr_ae hm]
      simp
  have hterminal (θ : ℝ) :
      histInt lam θ P T (fun H => (copies H : ℝ≥0∞)) ≤ S := by
    let B := {H : Hist T | S < copies H}
    have hmB : MeasurableSet B := measurableSet_lt measurable_const (meas_copies T)
    let b := B.indicator (fun _ => (1 : ℝ≥0∞))
    have hb : Measurable b := measurable_const.indicator hmB
    calc
      _ ≤ histInt lam θ P T (fun H => (S : ℝ≥0∞) + (⊤ : ℝ≥0∞) * b H) := by
        apply hist_mono
        intro H
        by_cases h : S < copies H
        · simp [b, B, h]
        · simpa [b, B, h] using (show (copies H : ℝ≥0∞) ≤ S by exact_mod_cast le_of_not_gt h)
      _ = _ := by
        rw [hist_add P lam θ T (fun _ => (S : ℝ≥0∞)) (fun H => (⊤ : ℝ≥0∞) * b H) measurable_const (measurable_const.mul hb),
          hconst θ T S (by finiteness), hist_scale _ _ _ _ _ _ hb, show histInt lam θ P T b = 0 from hS θ]
        simp
  have hsum (θ : ℝ) (t : ℕ) : ∑ i ∈ Finset.range t, histInt lam θ P i (K i) =
      histInt lam θ P t (fun H => (copies H : ℝ≥0∞)) := by
    induction t with
    | zero => simp [histInt, copies]
    | succ t ih =>
      rw [Finset.sum_range_succ, ih,
        ← hist_add P lam θ t (fun H => (copies H : ℝ≥0∞)) (K t) ((measurable_of_countable _).comp (meas_copies t)) (hK t)]
      congr 1; funext H
      have := P.isMarkov t
      change (copies H : ℝ≥0∞) + K t H = ∫⁻ s, ∫⁻ y, _ ∂volume ∂(P.seed t H)
      calc
        _ = ∫⁻ s, (copies H : ℝ≥0∞) + s.1 ∂(P.seed t H) := by simp [lintegral_add_left measurable_const, K]
        _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [P.seed_cov t H] with s hs
          simp only [copies_snoc, Nat.cast_add]
          rw [lintegral_mul_const' _ _ (by finiteness), hmass θ t s hs, one_mul]
  let μ := volume.restrict (Set.Ico 0 Real.pi)
  have htotal (t : ℕ) :
      ∑ i ∈ Finset.range t, ∫⁻ θ, histInt lam θ P i (K i) ∂μ ≤
        ∫⁻ θ, ∑ i ∈ Finset.range t, histInt lam θ P i (K i) ∂μ := by
    induction t with
    | zero => simp
    | succ t ih =>
      simp only [Finset.sum_range_succ]
      exact (add_le_add_left ih _).trans (le_lintegral_add _ _)
  rw [← Finset.mul_sum]
  calc
    _ ≤ ENNReal.ofReal (1/Real.pi) * ∫⁻ θ, ∑ i ∈ Finset.range T, histInt lam θ P i (K i) ∂μ :=
      mul_le_mul_right (htotal T) _
    _ ≤ ENNReal.ofReal (1/Real.pi) * ∫⁻ _θ, (S : ℝ≥0∞) ∂μ := by
      gcongr with θ; rw [hsum]; exact hterminal θ
    _ = _ := by
      simp only [μ, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero]
      rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel Real.pi_ne_zero,
        ENNReal.ofReal_one, mul_one]

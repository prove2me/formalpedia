-- Prove2me | solution 1 for LogLogJam.posterior_one_step_law
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:42:25.000416+00:00
-- url     : https://prove2.me/submissions/6526b780-f7b0-4081-8183-ad29c8471452

import Theorems.Thm_LogLogJam_physical_history_likelihood
import Theorems.Thm_LogLogJam_history_reference_density
import Definitions.Def_LogLogJam_GaussProtocol

open MeasureTheory ProbabilityTheory LogLogJam Matrix
open scoped ENNReal

private theorem cov_cont (l : ℝ) (k : ℕ) : Continuous (fun θ => VsqK l θ k) := by
  apply continuous_pi
  rintro ⟨a,i⟩
  apply continuous_pi
  rintro ⟨b,j⟩
  fin_cases a <;> fin_cases b
  all_goals simp [VsqK, Vsq, rot, Matrix.kroneckerMap_apply]
  all_goals fun_prop

private theorem density_meas {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {k : ℕ} (D : X → Matrix (Q k) (Q k) ℝ)
    (hD : Continuous D) (y : X → Q k → ℝ) (hy : Measurable y) :
    Measurable (fun x => outDens k (D x) (y x)) := by
  have hi (i j : Q k) : Measurable (fun x => (D x)⁻¹ i j) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact hD.matrix_det.measurable.inv.mul
      ((continuous_apply j).comp ((continuous_apply i).comp hD.matrix_adjugate)).measurable
  have hh (i : Q k) : Measurable (fun x => y x i) := (measurable_pi_apply i).comp hy
  simp only [outDens, dotProduct, Matrix.mulVec]
  apply Measurable.div
  · apply Real.continuous_exp.measurable.comp
    exact (Finset.measurable_fun_sum _ fun i _ => (hh i).mul
      (Finset.measurable_fun_sum _ fun j _ => (hi i j).mul (hh j))).neg
  · exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hD.matrix_det.measurable)

private theorem density_nn {k : ℕ} (D : Matrix (Q k) (Q k) ℝ) (y : Q k → ℝ) :
    0 ≤ outDens k D y := by unfold outDens; positivity


set_option maxHeartbeats 1000000
noncomputable section
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

private theorem meas_snoc {X : Type*} [MeasurableSpace X] {t k : ℕ}
    {h : X → Hist t} {w : X → (Q k → Q k → ℝ) × (Q k → ℝ)}
    (hh : Measurable h) (hw : Measurable w) :
    Measurable (fun p => Fin.snoc (α := fun _ : Fin (t+1) => Obs) (h p) (⟨k,w p⟩ : Obs)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [Function.comp_def] using (sigma_meas_mk (B := fun n => (Q n → Q n → ℝ) × (Q n → ℝ)) k).comp hw
  · simpa [Function.comp_def] using (measurable_pi_apply j).comp hh


private def out (l u : ℝ) (s : Seed) (y : Q s.1 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (outDens s.1 (VsqK l u s.1 + Matrix.of s.2) y)

private def pushed {t : ℕ} (F : Hist (t+1) → ℝ≥0∞) (l u : ℝ) (H : Hist t) (s : Seed) : ℝ≥0∞ :=
  ∫⁻ y, out l u s y * F (Fin.snoc H ⟨s.1,(s.2,y)⟩)

private theorem out_joint {X : Type*} [MeasurableSpace X] (l : ℝ) (k : ℕ)
    (u : X → ℝ) (W : X → Q k → Q k → ℝ) (y : X → Q k → ℝ)
    (hu : Measurable u) (hW : Measurable W) (hy : Measurable y) :
    Measurable (fun x => out l (u x) ⟨k, W x⟩ (y x)) := by
  let D (p : (ℝ × (Q k → Q k → ℝ)) × (Q k → ℝ)) := VsqK l p.1.1 k + Matrix.of p.1.2
  have hD : Continuous D := ((cov_cont l k).comp (continuous_fst.comp continuous_fst)).add
    (continuous_snd.comp continuous_fst)
  let A (x : X) := ((u x, W x), y x)
  have ha : Measurable A := (hu.prodMk hW).prodMk hy
  let b (p : (ℝ × (Q k → Q k → ℝ)) × (Q k → ℝ)) := ENNReal.ofReal (outDens k (D p) p.2)
  have hb : Measurable b := (density_meas D hD Prod.snd measurable_snd).ennreal_ofReal
  change Measurable (b ∘ A)
  exact hb.comp ha

private theorem pushed_meas {t : ℕ} (F : Hist (t+1) → ℝ≥0∞) (hF : Measurable F)
    (l : ℝ) {X : Type*} [MeasurableSpace X] (u : X → ℝ) (H : X → Hist t)
    (hu : Measurable u) (hH : Measurable H) :
    Measurable (fun p : X × Seed => pushed F l (u p.1) (H p.1) p.2) := by
  apply sigma_meas_prod
  intro k
  change Measurable (fun p : X × (Q k → Q k → ℝ) => ∫⁻ y, out l (u p.1) ⟨k,p.2⟩ y *
    F (Fin.snoc (α := fun _ : Fin (t+1) => Obs) (H p.1) ⟨k,(p.2,y)⟩))
  apply Measurable.lintegral_prod_right (ν := (volume : Measure (Q k → ℝ)))
  apply Measurable.mul
  · exact out_joint l k _ _ _ ((hu.comp measurable_fst).comp measurable_fst)
      (measurable_snd.comp measurable_fst) measurable_snd
  · exact hF.comp (meas_snoc ((hH.comp measurable_fst).comp measurable_fst)
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

private theorem likelihood_mass {t : ℕ} (l : ℝ) (hl : 1 < l) (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) :
    ENNReal.ofReal (postNorm l H) = ∫⁻ u in Set.Ico 0 Real.pi, ENNReal.ofReal (histDens l u H) := by
  obtain ⟨hpos, _, hC⟩ := physical_history_likelihood l hl H hH
  exact ofReal_integral_eq_lintegral_ofReal
    (hC.continuous.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
    (ae_of_all _ (fun u => (hpos u).le))

private theorem likelihood_mass_pos {t : ℕ} (l : ℝ) (hl : 1 < l) (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) : 0 < postNorm l H := by
  obtain ⟨hpos, _, hC⟩ := physical_history_likelihood l hl H hH
  unfold postNorm
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact intervalIntegral.integral_pos Real.pi_pos hC.continuous.continuousOn
    (fun u _ => (hpos u).le) ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hpos 0⟩

private def admissible (o : Obs) := IsCov o.1 (Matrix.of o.2.1)
private theorem snoc_admissible {t : ℕ} (H : Hist t) (s : Seed) (y : Q s.1 → ℝ)
    (hH : ∀ i, admissible (H i)) (hs : IsCov s.1 (Matrix.of s.2)) :
    ∀ i, admissible (Fin.snoc (α := fun _ : Fin (t+1) => Obs) H ⟨s.1,(s.2,y)⟩ i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; exact hs
  · rw [Fin.snoc_castSucc]; exact hH j

private theorem predictive_weight {t : ℕ} (l : ℝ) (hl : 1 < l) (H : Hist t)
    (hH : ∀ i, admissible (H i)) (s : Seed) (hs : IsCov s.1 (Matrix.of s.2)) (y : Q s.1 → ℝ) :
    ENNReal.ofReal (postNorm l H) * ENNReal.ofReal (predDens l H s.1 s.2 y) =
    ∫⁻ u in Set.Ico 0 Real.pi, ENNReal.ofReal (histDens l u H) * out l u s y := by
  let C : Hist (t+1) := Fin.snoc H ⟨s.1,(s.2,y)⟩
  have hc (u : ℝ) : histDens l u C = histDens l u H *
      outDens s.1 (VsqK l u s.1 + Matrix.of s.2) y := by
    change (∏ i, obsDens l u (C i)) = (∏ i, obsDens l u (H i)) * _
    rw [Fin.prod_univ_castSucc]
    simp only [C, Fin.snoc_last, Fin.snoc_castSucc]
    rfl
  have hm : predDens l H s.1 s.2 y = postNorm l C / postNorm l H := by
    unfold predDens postNorm
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with u
    rw [hc]
    unfold post postNorm
    ring
  have hp := likelihood_mass_pos l hl H hH
  have hcop := likelihood_mass l hl C (snoc_admissible H s y hH hs)
  rw [hm, ENNReal.ofReal_div_of_pos hp, mul_comm (ENNReal.ofReal (postNorm l H)), ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top, hcop]
  apply lintegral_congr
  intro u
  rw [hc, ENNReal.ofReal_mul ((physical_history_likelihood l hl H hH).1 u).le]
  rfl
private theorem bayes_at_seed {t : ℕ} (l : ℝ) (hl : 1 < l) (H : Hist t)
    (hH : ∀ i, admissible (H i)) (s : Seed) (hs : IsCov s.1 (Matrix.of s.2))
    (F : Hist (t+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u in Set.Ico 0 Real.pi, ENNReal.ofReal (histDens l u H) * pushed F l u H s) =
      ENNReal.ofReal (postNorm l H) * nextCondExp l H s.1 s.2 F := by
  let I := (volume : Measure ℝ).restrict (Set.Ico 0 Real.pi)
  let q u := ENNReal.ofReal (histDens l u H)
  let v (y : Q s.1 → ℝ) := F (Fin.snoc (α := fun _ : Fin (t+1) => Obs) H ⟨s.1,(s.2,y)⟩)
  have hq : Measurable q := (physical_history_likelihood l hl H hH).2.2.continuous.measurable.ennreal_ofReal
  have hv : Measurable v := hF.comp (meas_snoc measurable_const (measurable_const.prodMk measurable_id))
  have hj : Measurable fun p : ℝ × (Q s.1 → ℝ) => q p.1 * (out l p.1 s p.2 * v p.2) :=
    (hq.comp measurable_fst).mul ((out_joint l s.1 _ _ _ measurable_fst measurable_const measurable_snd).mul
       (hv.comp measurable_snd))
  change (∫⁻ u, q u * (∫⁻ y, out l u s y * v y) ∂I) =
      ENNReal.ofReal (postNorm l H) * (∫⁻ y, ENNReal.ofReal (predDens l H s.1 s.2 y) * v y)
  have hswap u : q u * (∫⁻ y, out l u s y * v y) = ∫⁻ y, q u * (out l u s y * v y) := (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  simp_rw [hswap]
  rw [lintegral_lintegral_swap hj.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  simp_rw [← mul_assoc]
  have hsec : Measurable fun u => q u * out l u s y := hq.mul (out_joint l s.1 id (fun _ => s.2) (fun _ => y) measurable_id measurable_const measurable_const)
  rw [lintegral_mul_const (f := fun u => q u * out l u s y) _ hsec,
    predictive_weight l hl H hH s hs y]

private theorem bayes_at_history {t T : ℕ} (P : GaussProtocol T) (l : ℝ) (hl : 1 < l) (H : Hist t)
    (hH : ∀ i, admissible (H i)) (F : Hist (t+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u in Set.Ico 0 Real.pi, ENNReal.ofReal (histDens l u H) * ∫⁻ s, pushed F l u H s ∂(P.seed t H)) =
      ENNReal.ofReal (postNorm l H) * ∫⁻ s, nextCondExp l H s.1 s.2 F ∂(P.seed t H) := by
  have := P.isMarkov t
  let q u := ENNReal.ofReal (histDens l u H)
  have hq : Measurable q := (physical_history_likelihood l hl H hH).2.2.continuous.measurable.ennreal_ofReal
  have hj : Measurable fun p : ℝ × Seed => q p.1 * pushed F l p.1 H p.2 :=
    (hq.comp measurable_fst).mul (pushed_meas F hF l id (fun _ => H) measurable_id measurable_const)
  change (∫⁻ u in Set.Ico 0 Real.pi, q u * ∫⁻ s, pushed F l u H s ∂(P.seed t H)) = _
  have hswap u : q u * ∫⁻ s, pushed F l u H s ∂(P.seed t H) = ∫⁻ s, q u * pushed F l u H s ∂(P.seed t H) :=
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  simp_rw [hswap]
  rw [lintegral_lintegral_swap hj.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [P.seed_cov t H] with s hs
  exact bayes_at_seed l hl H hH s hs F hF
private theorem mixture_comparison {G : Type*} [MeasurableSpace G]
    (I : Measure ℝ) (μ : Measure G) [SigmaFinite I] [SigmaFinite μ]
    (q p : ℝ → G → ℝ≥0∞) (b Z : G → ℝ≥0∞)
    (hq : Measurable (Function.uncurry q)) (hp : Measurable (Function.uncurry p))
    (hZ : ∀ H, Z H = ∫⁻ u, q u H ∂I) (hz : ∀ H, Z H ≠ 0) (hzf : ∀ H, Z H ≠ ⊤)
    (hc : ∀ H, (∫⁻ u, q u H * p u H ∂I) = Z H * b H) :
    Measurable b ∧ ((∫⁻ u, ∫⁻ H, q u H * p u H ∂μ ∂I) = ∫⁻ u, ∫⁻ H, q u H * b H ∂μ ∂I) := by
  have hmZ : Measurable Z := by
    rw [funext hZ]; exact hq.lintegral_prod_left (μ := I)
  have hL : Measurable (Function.uncurry (fun u H => q u H * p u H)) := hq.mul hp
  have hbm : Measurable b := by
    have he (H) : b H = (Z H)⁻¹ * (∫⁻ u, q u H * p u H ∂I) := by
      rw [hc, ← mul_assoc, ENNReal.inv_mul_cancel (hz H) (hzf H), one_mul]
    rw [funext he]
    exact hmZ.inv.mul (hL.lintegral_prod_left (μ := I))
  have hR : Measurable (Function.uncurry (fun u H => q u H * b H)) := hq.mul (hbm.comp measurable_snd)
  refine ⟨hbm, ?_⟩
  rw [lintegral_lintegral_swap (μ := I) (ν := μ) (f := fun u H => q u H * p u H) hL.aemeasurable,
      lintegral_lintegral_swap (μ := I) (ν := μ) (f := fun u H => q u H * b H) hR.aemeasurable]
  apply lintegral_congr
  intro H
  have hslice : Measurable fun u => q u H := hq.comp (measurable_id.prodMk measurable_const)
  rw [hc, lintegral_mul_const (f := fun u => q u H) _ hslice, hZ H]

set_option maxHeartbeats 2000000 in
private theorem global_tower {T : ℕ} (P : GaussProtocol T) (l : ℝ) (hl : 1 < l)
    (t : ℕ) (ht : t+1 ≤ T) (F : Hist (t+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u in Set.Ico 0 Real.pi, histInt l u P (t+1) F) =
    ∫⁻ u in Set.Ico 0 Real.pi, histInt l u P t
      (fun H => ∫⁻ s, nextCondExp l H s.1 s.2 F ∂(P.seed t H)) := by
  let G := {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
  obtain ⟨μ, hσ, hr⟩ := history_reference_density P t (by omega)
  have := hσ
  have := P.isMarkov t
  obtain ⟨_, _, hC, hm, _, hrep⟩ := hr l hl
  let I := (volume : Measure ℝ).restrict (Set.Ico 0 Real.pi)
  let q (u : ℝ) (H : G) := ENNReal.ofReal (histDens l u H.1)
  let Z (H : G) := ENNReal.ofReal (postNorm l H.1)
  let p (u : ℝ) (H : Hist t) := ∫⁻ s, pushed F l u H s ∂(P.seed t H)
  let b (H : Hist t) := ∫⁻ s, nextCondExp l H s.1 s.2 F ∂(P.seed t H)
  have hq : Measurable (Function.uncurry q) :=
    (measurable_uncurry_of_continuous_of_measurable (fun H => (hC H).continuous) hm).ennreal_ofReal
  have hp : Measurable (fun a : ℝ × G => p a.1 a.2.1) := by
    let f (a : ℝ × G) := a.2.val
    have hf : Measurable f := measurable_subtype_coe.comp measurable_snd
    let κ := (P.seed t).comap f hf
    exact (pushed_meas F hF l Prod.fst f measurable_fst hf).lintegral_kernel_prod_right' (κ := κ)
  let pg (u : ℝ) (H : G) := p u H.1
  let bg (H : G) := b H.1
  have hpg : Measurable (Function.uncurry pg) := hp
  have hzm (H : G) : Z H = ∫⁻ u, q u H ∂I := likelihood_mass l hl H.val H.property
  have hz (H : G) : Z H ≠ 0 := (ENNReal.ofReal_pos.mpr (likelihood_mass_pos l hl H.val H.property)).ne'
  have hzfin (H : G) : Z H ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlocal (H : G) : (∫⁻ u, q u H * pg u H ∂I) = Z H * bg H :=
    bayes_at_history P l hl H.1 H.2 F hF
  obtain ⟨hbm, hmix⟩ := mixture_comparison I μ q pg bg Z hq hpg hzm hz hzfin hlocal
  have hleft (u : ℝ) : histInt l u P (t+1) F = ∫⁻ H : G, q u H * p u H.val ∂μ :=
    hrep u (p u) (hp.comp (measurable_const.prodMk measurable_id))
  have hright u : histInt l u P t b = ∫⁻ H : G, q u H * b H.val ∂μ := hrep u b hbm
  change (∫⁻ u, histInt l u P (t+1) F ∂I) = ∫⁻ u, histInt l u P t b ∂I
  exact (lintegral_congr hleft).trans (hmix.trans (lintegral_congr hright).symm)

private theorem physical_congr {T : ℕ} (P : GaussProtocol T) (l u : ℝ) (t : ℕ)
    (F B : Hist t → ℝ≥0∞)
    (h : ∀ H : Hist t, (∀ i, admissible (H i)) → F H = B H) :
    histInt l u P t F = histInt l u P t B := by
  induction t with
  | zero => exact h _ (fun i => Fin.elim0 i)
  | succ t ih =>
    apply ih
    intro H hH
    apply lintegral_congr_ae
    filter_upwards [P.seed_cov t H] with s hs
    apply lintegral_congr
    intro y
    exact congrArg (_ * ·) (h _ (snoc_admissible H s y hH hs))

theorem solution {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam)
    (t : ℕ) (ht : t+1 ≤ T) (F : Hist (t+1) → ℝ≥0∞)
    (hF : Measurable (fun H : {H : Hist (t+1) // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)} =>
      F H.val)) :
    ENNReal.ofReal (1 / Real.pi) * (∫⁻ θ in Set.Ico 0 Real.pi, histInt lam θ P (t+1) F) =
      ENNReal.ofReal (1 / Real.pi) * (∫⁻ θ in Set.Ico 0 Real.pi, histInt lam θ P t
        (fun H => ∫⁻ s, nextCondExp lam H s.1 s.2 F ∂(P.seed t H))) := by
  let G := {H : Hist (t+1) // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
  obtain ⟨B, hB, heq⟩ := Measurable.exists_eq_measurable_comp (f := fun H : G => H.val) hF
  have hv (H : Hist (t+1)) (hH : ∀ i, admissible (H i)) : F H = B H :=
    congrFun heq (⟨H,hH⟩ : G)
  apply congrArg (_ * ·)
  have first (u) := physical_congr P lam u (t+1) F B hv
  simp_rw [first]
  rw [global_tower P lam hlam t ht B hB]
  apply lintegral_congr
  intro u
  apply physical_congr
  intro H hH
  apply lintegral_congr_ae
  filter_upwards [P.seed_cov t H] with s hs
  apply lintegral_congr
  intro y
  exact congrArg (_ * ·) (hv _ (snoc_admissible H s y hH hs)).symm

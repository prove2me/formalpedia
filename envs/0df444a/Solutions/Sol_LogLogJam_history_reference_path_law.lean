-- Prove2me | solution 1 for LogLogJam.history_reference_path_law
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:39:11.444714+00:00
-- url     : https://prove2.me/submissions/b579ed6b-9a66-45f1-95e8-51a4dae54dc5

import Definitions.Def_LogLogJam_GaussProtocol

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

open scoped ComplexOrder

private def good (t : ℕ) : Set (Hist t) := {H | ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}

private theorem cov_closed (k : ℕ) : IsClosed {W : Matrix (Q k) (Q k) ℝ | IsCov k W} := by
  let A (W : Matrix (Q k) (Q k) ℝ) := W.map Complex.ofReal + Complex.I • (Omega k).map Complex.ofReal
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun W : Matrix (Q k) (Q k) ℝ => (W i j : ℂ) + _)
    fun_prop
  change IsClosed ({W : Matrix (Q k) (Q k) ℝ | Wᵀ = W} ∩ {W | (A W).PosSemidef})
  apply IsClosed.inter (isClosed_eq continuous_id.matrix_transpose continuous_id)
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.ofPred_and]
  apply IsClosed.inter
  · change IsClosed {W | (A W)ᴴ = A W}
    exact isClosed_eq hA.matrix_conjTranspose hA
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro v
    have hv : Continuous (fun W => star v ⬝ᵥ ((A W) *ᵥ v)) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    simp only [Complex.nonneg_iff, Set.ofPred_and]
    exact (isClosed_le continuous_const (Complex.continuous_re.comp hv)).inter
      (isClosed_eq continuous_const (Complex.continuous_im.comp hv))

private theorem good_meas (t : ℕ) : MeasurableSet (good t) := by
  have ho : MeasurableSet {o : Obs | IsCov o.1 (Matrix.of o.2.1)} := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro k
    have hc : IsClosed {W : Q k → Q k → ℝ | IsCov k (Matrix.of W)} := cov_closed k
    exact hc.measurableSet.preimage measurable_fst
  unfold good
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => ho.preimage (measurable_pi_apply i))

private theorem good_snoc {t : ℕ} (H : Hist t) (hh : H ∈ good t) (s : Seed)
    (hs : IsCov s.1 (Matrix.of s.2)) (y : Q s.1 → ℝ) :
    Fin.snoc H (⟨s.1,(s.2,y)⟩ : Obs) ∈ good (t+1) := by
  let o : Obs := ⟨s.1,(s.2,y)⟩
  let f (z : Obs) := IsCov z.1 (Matrix.of z.2.1)
  intro i
  refine Fin.lastCases (motive := fun i => f (Fin.snoc (α := fun _ : Fin (t+1) => Obs) H o i)) ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; exact hs
  · rw [Fin.snoc_castSucc]; exact hh j

private theorem supported {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ) (t : ℕ)
    (F J : Hist t → ℝ≥0∞) (he : ∀ H ∈ good t, F H = J H) :
    histInt lam θ P t F = histInt lam θ P t J := by
  induction t with
  | zero => exact he _ (fun i => Fin.elim0 i)
  | succ t ih =>
    apply ih
    intro H hh
    apply lintegral_congr_ae
    filter_upwards [P.seed_cov t H] with s hs
    apply lintegral_congr
    intro y
    rw [he _ (good_snoc H hh s hs y)]
private def appendObs {t : ℕ} (H : Hist t) (s : Seed) (y : Q s.1 → ℝ) : Hist (t+1) :=
  Fin.snoc H ⟨s.1,(s.2,y)⟩

private theorem meas_append {t : ℕ} (H : Hist t) (s : Seed) : Measurable (appendObs H s) :=
  meas_snoc measurable_const (measurable_const.prodMk measurable_id)

private def readout {t : ℕ} (H : Hist t) (s : Seed) : Measure (Hist (t+1)) :=
  volume.map (appendObs H s)

private theorem meas_readout {t : ℕ} (H : Hist t) : Measurable (readout H) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  apply sigma_meas_slice
  intro k
  have hmeas : Measurable (fun p : (Q k → Q k → ℝ) × (Q k → ℝ) =>
      A.indicator (1 : Hist (t+1) → ℝ≥0∞) (Fin.snoc H (⟨k,p⟩ : Obs))) :=
    (measurable_one.indicator hA).comp (meas_snoc measurable_const measurable_id)
  have hh : Measurable (fun W : Q k → Q k → ℝ => ∫⁻ y : Q k → ℝ,
      A.indicator (1 : Hist (t+1) → ℝ≥0∞) (appendObs H ⟨k,W⟩ y)) := by
    apply Measurable.lintegral_prod_right
    exact hmeas
  convert hh using 1
  funext W
  rw [readout,Measure.map_apply (meas_append H _) hA, ← lintegral_indicator_one (hA.preimage (meas_append H _))]
  rfl

private def stepLaw {T t : ℕ} (P : GaussProtocol T) (H : Hist t) : Measure (Hist (t+1)) :=
  (P.seed t H).bind (readout H)

private theorem int_stepLaw {T t : ℕ} (P : GaussProtocol T) (H : Hist t)
    (F : Hist (t+1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂stepLaw P H = ∫⁻ s, ∫⁻ y, F (appendObs H s y) ∂volume ∂P.seed t H := by
  rw [stepLaw,Measure.lintegral_bind (meas_readout H).aemeasurable hF.aemeasurable]
  apply lintegral_congr
  intro s
  exact lintegral_map hF (meas_append H s)

private theorem meas_stepLaw {T t : ℕ} (P : GaussProtocol T) :
    Measurable (stepLaw (t := t) P) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  let F := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hA
  have he (H : Hist t) : stepLaw P H A = ∫⁻ s, ∫⁻ y, F (appendObs H s y) ∂volume ∂P.seed t H :=
    (lintegral_indicator_one hA).symm.trans (int_stepLaw P H F hF)
  simp_rw [he]
  have := P.isMarkov t
  apply Measurable.lintegral_kernel_prod_right
  apply sigma_meas_prod
  intro k
  apply Measurable.lintegral_prod_right (ν := (volume : Measure (Q k → ℝ)))
  let X := (Hist t × (Q k → Q k → ℝ)) × (Q k → ℝ)
  have hw : Measurable (fun p : X => (p.1.2,p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hh : Measurable (fun p : X => p.1.1) := measurable_fst.comp measurable_fst
  exact hF.comp (meas_snoc hh hw)

private def rawLaw {T : ℕ} (P : GaussProtocol T) : (t : ℕ) → Measure (Hist t)
  | 0 => Measure.dirac Fin.elim0
  | t+1 => (rawLaw P t).bind (stepLaw P)

private theorem obs_nonneg (lam θ : ℝ) (o : Obs) : 0 ≤ obsDens lam θ o := by
  unfold obsDens outDens
  positivity

private theorem weighted_meas (lam θ : ℝ) (t : ℕ) :
    Measurable (fun H : Hist t => ENNReal.ofReal (histDens lam θ H)) := by
  have ho : Measurable fun o : Obs => ENNReal.ofReal (obsDens lam θ o) :=
    sigma_meas_slice _ (fun k => meas_density_pair k (VsqK lam θ k))
  simp only [histDens,ENNReal.ofReal_prod_of_nonneg (fun i _ => obs_nonneg lam θ _)]
  exact Finset.measurable_fun_prod _ (fun i _ => ho.comp (measurable_pi_apply i))

private theorem raw_rep {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ) (t : ℕ)
    (F : Hist t → ℝ≥0∞) (hF : Measurable F) :
    histInt lam θ P t F = ∫⁻ H, ENNReal.ofReal (histDens lam θ H) * F H ∂rawLaw P t := by
  induction t with
  | zero =>
    rw [rawLaw,lintegral_dirac' _ (f := fun H => ENNReal.ofReal (histDens lam θ H) * F H) ((weighted_meas lam θ 0).mul hF)]
    simp [histInt,histDens]
  | succ t ih =>
    let f (H : Hist (t+1)) := ENNReal.ofReal (histDens lam θ H) * F H
    have hf : Measurable f := (weighted_meas lam θ (t+1)).mul hF
    change histInt lam θ P t (stepInt P lam θ F) = ∫⁻ H, f H ∂(rawLaw P t).bind (stepLaw P)
    rw [ih (stepInt P lam θ F) (measurable_next P lam θ F hF),Measure.lintegral_bind (meas_stepLaw P).aemeasurable hf.aemeasurable]
    apply lintegral_congr
    intro H
    rw [int_stepLaw P H f hf]
    unfold stepInt
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro s
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro y
    change _ = ENNReal.ofReal (histDens lam θ (appendObs H s y)) * _
    let o : Obs := ⟨s.1, s.2, y⟩
    have hlast : appendObs H s y (Fin.last t) = o :=
      Fin.snoc_last (α := fun _ : Fin (t+1) => Obs) o H
    have hprev (i : Fin t) : appendObs H s y i.castSucc = H i :=
      Fin.snoc_castSucc (α := fun _ : Fin (t+1) => Obs) o H i
    have hmul : histDens lam θ (appendObs H s y) = histDens lam θ H * obsDens lam θ o := by
      unfold histDens
      rw [Fin.prod_univ_castSucc,hlast]
      simp only [hprev]
    have hnonneg : 0 ≤ histDens lam θ H := Finset.prod_nonneg (fun i _ => obs_nonneg lam θ (H i))
    rw [hmul, ENNReal.ofReal_mul hnonneg, mul_assoc]
    rfl
theorem solution {T : ℕ} (P : GaussProtocol T) (t : ℕ) (_ht : t ≤ T) :
    let G := {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
    ∃ μ : Measure G, ∀ l : ℝ, 1 < l → ∀ (s : ℝ) (Φ : Hist t → ℝ≥0∞),
      Measurable (fun H : G => Φ H.1) →
      histInt l s P t Φ = ∫⁻ H : G, ENNReal.ofReal (histDens l s H.1) * Φ H.1 ∂μ := by
  classical
  let A := good t
  have hA : MeasurableSet A := good_meas t
  refine ⟨(rawLaw P t).comap ((↑) : A → Hist t), ?_⟩
  intro l _ s Φ hΦ
  obtain ⟨F,hF,he⟩ := (MeasurableEmbedding.subtype_coe hA).exists_measurable_extend
    hΦ (fun _ => inferInstance)
  have hRestr : Measurable (A.indicator Φ) := by
    have hEq : A.indicator Φ = A.indicator F := by
      apply Set.indicator_congr
      intro H hH
      exact (congrFun he (⟨H,hH⟩ : A)).symm
    rw [hEq]
    exact hF.indicator hA
  rw [supported P l s t Φ (A.indicator Φ) (fun H hH => (Set.indicator_of_mem hH Φ).symm),
    raw_rep P l s t (A.indicator Φ) hRestr]
  change _ = ∫⁻ x : A, ENNReal.ofReal (histDens l s x.1) * Φ x.1 ∂(rawLaw P t).comap ((↑) : A → Hist t)
  rw [lintegral_subtype_comap hA (fun H => ENNReal.ofReal (histDens l s H) * Φ H),
    ← lintegral_indicator hA]
  apply lintegral_congr
  intro H
  by_cases hH : H ∈ A <;> simp [Set.indicator,hH]

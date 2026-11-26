-- Prove2me | solution 1 for LogLogJam.corollary_5_7
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:47:25.973568+00:00
-- url     : https://prove2.me/submissions/b3540ff0-ecc8-4108-88f3-ecb2813597b9

import Theorems.Thm_LogLogJam_history_reference_density
import Definitions.Def_LogLogJam_GaussProtocol
import Theorems.Thm_LogLogJam_gaussian_seed_score_centered
import Theorems.Thm_LogLogJam_gaussian_seed_mass_one
import Theorems.Thm_LogLogJam_physical_history_likelihood
import Definitions.Def_LogLogJam_postFisher
open MeasureTheory LogLogJam Filter Matrix ProbabilityTheory
open scoped ENNReal Topology ComplexOrder
set_option maxHeartbeats 1400000
private theorem gainCovPos (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    (VsqK lam θ k + Matrix.of W).PosDef := by
  have hrot : (rot θ).det = 1 := by
    simp [rot, det_fin_two, ← sq, Real.cos_sq_add_sin_sq]
  have hU : IsUnit (rot θ) := (isUnit_iff_isUnit_det _).mpr (by simp [hrot])
  have hdiag : (diagonal ![lam, lam⁻¹]).PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i <;> simp <;> positivity
  have hV : (Vsq lam θ).PosDef := by
    have h := hdiag.mul_mul_conjTranspose_same (B := rot θ)
      (vecMul_injective_of_isUnit hU)
    have heq : diagonal ![lam, lam⁻¹] = !![lam,0;0,lam⁻¹] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    simpa [Vsq, heq, conjTranspose_eq_transpose_of_trivial] using h
  apply PosDef.add_posSemidef (hV.kronecker (PosDef.one : (1 : Matrix (Fin k) (Fin k) ℝ).PosDef))
  apply posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hW.1
  · intro v
    have h := (Complex.nonneg_iff.mp (hW.2.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
    simpa [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im, Complex.re_sum] using h

set_option maxHeartbeats 700000

private theorem gainDensityMeas {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
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

private theorem centered_square {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (b db : Y → ℝ) (k : ℝ) (hb : ∀ y, 0 < b y) (hm : Measurable b)
    (hd : Measurable db) (hn : ∫⁻ y, ENNReal.ofReal (b y) ∂ν = 1)
    (hi : Integrable db ν) (hz : ∫ y, db y ∂ν = 0) :
    ∫⁻ y, ENNReal.ofReal (b y * (k + db y / b y)^2) ∂ν =
      ENNReal.ofReal (k^2) + ∫⁻ y, ENNReal.ofReal (b y * (db y / b y)^2) ∂ν := by
  let c (y : Y) := 2*k*db y
  have hci : Integrable c ν := hi.const_mul _
  have hcm : Measurable c := measurable_const.mul hd
  have hcz : ∫ y, c y ∂ν = 0 := by simp only [c, integral_const_mul, hz, mul_zero]
  have hp : (∫⁻ y, ENNReal.ofReal (c y) ∂ν) ≠ ⊤ := hci.lintegral_lt_top.ne
  have hm' : (∫⁻ y, ENNReal.ofReal (-c y) ∂ν) ≠ ⊤ := hci.neg.lintegral_lt_top.ne
  have hpm : (∫⁻ y, ENNReal.ofReal (c y) ∂ν) = ∫⁻ y, ENNReal.ofReal (-c y) ∂ν := by
    apply (ENNReal.toReal_eq_toReal_iff' hp hm').mp
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hci] at hcz
    linarith
  apply (ENNReal.add_left_inj hm').mp
  have hnegm : Measurable (fun y => ENNReal.ofReal (-c y)) := hcm.neg.ennreal_ofReal
  conv_lhs => rw [← lintegral_add_right _ hnegm]
  conv_rhs => rw [← hpm]
  have hbase : ENNReal.ofReal (k^2) = ∫⁻ y, ENNReal.ofReal (k^2 * b y) ∂ν := by
    simp_rw [ENNReal.ofReal_mul (sq_nonneg k)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hn, mul_one]
  have hbm : Measurable (fun y => ENNReal.ofReal (k^2 * b y)) := (measurable_const.mul hm).ennreal_ofReal
  rw [hbase, ← lintegral_add_left hbm,
    ← lintegral_add_right _ hcm.ennreal_ofReal]
  apply lintegral_congr
  intro y
  have hby := (hb y).le
  have hh : b y * (k + db y / b y)^2 =
      k^2 * b y + b y * (db y / b y)^2 + c y := by
    dsimp [c]; field_simp [ne_of_gt (hb y)]; ring
  have hcross : max (c y) 0 - max (-c y) 0 = c y := by grind
  have hcplus : ENNReal.ofReal (c y) = ENNReal.ofReal (max (c y) 0) := by simp
  have hcminus : ENNReal.ofReal (-c y) = ENNReal.ofReal (max (-c y) 0) := by simp
  rw [hcplus, hcminus, ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _)]
  congr 1
  linarith

private theorem pmeasDeriv {Y : Type*} [MeasurableSpace Y] (θ : ℝ) (b : ℝ → Y → ℝ)
    (hm : ∀ t, Measurable (b t)) (hd : ∀ y, DifferentiableAt ℝ (fun t => b t y) θ) :
    Measurable (fun y => deriv (fun t => b t y) θ) := by
  let d (n : ℕ) : ℝ := 1 / (n+1 : ℝ)
  have hlim : Tendsto d atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => by change 0 < 1 / (n+1 : ℝ); positivity⟩
  apply measurable_of_tendsto_metrizable (f := fun (n : ℕ) y => (d n)⁻¹ * (b (θ+d n) y - b θ y))
    (fun n => measurable_const.mul ((hm _).sub (hm _)))
  exact tendsto_pi_nhds.mpr fun y => (hd y).hasDerivAt.tendsto_slope_zero_right.comp hlim

private theorem pscore {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (p : ℝ → ℝ) (b : ℝ → Y → ℝ) (θ : ℝ)
    (hp : ∀ t, 0 < p t) (hb : ∀ t y, 0 < b t y) (hm : ∀ t, Measurable (b t))
    (hdp : DifferentiableAt ℝ p θ) (hdb : ∀ y, DifferentiableAt ℝ (fun t => b t y) θ)
    (hi : Integrable (fun y => deriv (fun t => b t y) θ) ν) (hz : ∫ y, deriv (fun t => b t y) θ ∂ν = 0)
    (hn : ∫⁻ y, ENNReal.ofReal (b θ y) ∂ν = 1) :
    (∫⁻ y, ENNReal.ofReal (p θ) * ENNReal.ofReal (b θ y) * ENNReal.ofReal ((deriv (fun t => Real.log (p t * b t y)) θ)^2) ∂ν) =
    ENNReal.ofReal (p θ) * ENNReal.ofReal ((deriv (fun t => Real.log (p t)) θ)^2) + ENNReal.ofReal (p θ) * fisherInfo ν b θ := by
  let v := deriv (fun t => Real.log (p t)) θ
  have ht y : deriv (fun t => Real.log (p t * b t y)) θ = v + deriv (fun t => b t y) θ / b θ y := by
    have eq : (fun t => Real.log (p t * b t y)) = (fun t => Real.log (p t) + Real.log (b t y)) :=
      funext fun t => Real.log_mul (hp t).ne' (hb t y).ne'
    rw [eq, deriv_fun_add (hdp.log (hp θ).ne') ((hdb y).log (hb θ y).ne')]
    rw [((hdb y).hasDerivAt.log (hb θ y).ne').deriv]
  have cen := centered_square ν (b θ) (fun y => deriv (fun t => b t y) θ) v (hb θ) (hm θ) (pmeasDeriv θ b hm hdb) hn hi hz
  simp_rw [ht, mul_assoc, ← ENNReal.ofReal_mul (hb θ _).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,cen,mul_add]
  unfold fisherInfo
  simp_rw [((hdb _).hasDerivAt.log (hb θ _).ne').deriv, ← ENNReal.ofReal_mul (hb θ _).le]
  rfl

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

private noncomputable def readFiber {B : ℕ → Type*} [∀ i, Inhabited (B i)] (k : ℕ) (s : Σ i, B i) : B k :=
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

private noncomputable def stepInt {t : ℕ} {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ)
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

private noncomputable def score {t : ℕ} (l θ : ℝ) (H : Hist t) := ENNReal.ofReal
  ((deriv (fun u => Real.log (histDens l u H)) θ)^2)

private theorem step_score {t : ℕ} (l θ : ℝ) (hl : 1 < l) (H : Hist t)
    (hH : H ∈ good t) (s : Seed) (hs : IsCov s.1 (Matrix.of s.2)) :
    (∫⁻ y, ENNReal.ofReal (outDens s.1 (VsqK l θ s.1 + Matrix.of s.2) y) *
      score l θ (Fin.snoc H ⟨s.1,(s.2,y)⟩)) = score l θ H + measFisher l s.1 s.2 θ := by
  let p u := histDens l u H
  let b u y := outDens s.1 (VsqK l u s.1 + Matrix.of s.2) y
  obtain ⟨hp,_,hpC⟩ := physical_history_likelihood l hl H hH
  have hpos u (y : Q s.1 → ℝ) : 0 < b u y := by
    have h := (gainCovPos l u hl s.1 s.2 hs).det_pos
    dsimp only [b, outDens]; positivity
  have hm u : Measurable (b u) := gainDensityMeas _ continuous_const _ measurable_id
  obtain ⟨hd,hi,hz⟩ := gaussian_seed_score_centered l θ hl s.1 s.2 hs
  have ev := pscore volume p b θ hp hpos hm (hpC.differentiable_one θ) hd hi hz
    (gaussian_seed_mass_one l θ hl s.1 s.2 hs)
  have hfac (y : Q s.1 → ℝ) (u : ℝ) :
      histDens l u (Fin.snoc H (⟨s.1,(s.2,y)⟩ : Obs)) = p u * b u y := by
    unfold histDens p
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
    rfl
  simp_rw [mul_assoc] at ev
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_add] at ev
  unfold score
  simp_rw [hfac]
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr (hp θ)).ne' ENNReal.ofReal_ne_top).mp ev

private theorem step_add {T t : ℕ} (P : GaussProtocol T) (l θ : ℝ)
    (F G : Hist (t+1) → ℝ≥0∞) (hm : Measurable F) (H : Hist t) :
    stepInt P l θ (fun J => F J + G J) H = stepInt P l θ F H + stepInt P l θ G H := by
  let q (s : Seed) (y : Q s.1 → ℝ) := ENNReal.ofReal (outDens s.1 (VsqK l θ s.1 + Matrix.of s.2) y)
  let C (s : Seed) (y : Q s.1 → ℝ) := Fin.snoc (α := fun _ : Fin (t+1) => Obs) H ⟨s.1,(s.2,y)⟩
  have hf (s : Seed) : Measurable fun y => q s y * F (C s y) :=
    ((gainDensityMeas _ continuous_const _ measurable_id).ennreal_ofReal).mul
      (hm.comp (meas_snoc measurable_const (measurable_const.prodMk measurable_id)))
  have hs : Measurable (fun s : Seed => ∫⁻ y, q s y * F (C s y)) := by
    apply sigma_meas_slice
    intro k
    apply Measurable.lintegral_prod_right (ν := (volume : Measure (Q k → ℝ)))
    exact (meas_density_pair k (VsqK l θ k)).mul (hm.comp (meas_snoc measurable_const measurable_id))
  change (∫⁻ s, ∫⁻ y, q s y * (F (C s y) + G (C s y)) ∂volume ∂P.seed t H) = _
  simp_rw [mul_add, lintegral_add_left (hf _)]
  exact lintegral_add_left hs _

private theorem hist_add {T : ℕ} (P : GaussProtocol T) (l θ : ℝ) (t : ℕ)
    (F G : Hist t → ℝ≥0∞) (hm : Measurable F) :
    histInt l θ P t (fun H => F H + G H) = histInt l θ P t F + histInt l θ P t G := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change histInt l θ P t (stepInt P l θ (fun H => F H + G H)) = _
    rw [funext (step_add P l θ F G hm)]
    exact ih _ _ (measurable_next P l θ F hm)

private theorem firstSlice {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (f : A → B → C) (h : Measurable (Function.uncurry f)) (x : A) : Measurable (f x) :=
  h.comp (measurable_prodMk_left (x := x))

theorem solution {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam) (t : ℕ)
    (ht : t + 1 ≤ T) :
    Jbar lam P (t + 1) =
      Jbar lam P t + ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi,
        histInt lam θ P t (fun H => ∫⁻ s, measFisher lam s.1 s.2 θ ∂(P.seed t H)) := by
  let G := {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
  obtain ⟨μ, hs, hc⟩ := history_reference_density P t (by omega)
  let _ := hs
  obtain ⟨hp, _, hC, hm, _, hrep⟩ := hc lam hlam
  have hS : Measurable (fun z : ℝ × G => score lam z.1 z.2.val) := by
    exact ((derivMeasurable (fun (u : ℝ) (H : G) => Real.log (histDens lam u H.val))
      (fun H => (hC H).log (fun u => (hp u H).ne')) (fun u => (hm u).log)).pow_const 2).ennreal_ofReal
  have hSlice (θ : ℝ) : Measurable (fun H : G => score lam θ H.val) :=
    firstSlice (fun u (H : G) => score lam u H.val) hS θ
  have hproto : Measurable (protoFisher lam P t) := by
    let q (u : ℝ) (H : G) := histDens lam u H.val
    have hq : Measurable (Function.uncurry q) :=
      measurable_uncurry_of_continuous_of_measurable (fun H => (hC H).continuous) hm
    have hh (θ : ℝ) : protoFisher lam P t θ = ∫⁻ H : G, ENNReal.ofReal (q θ H) * score lam θ H.val ∂μ :=
      hrep θ (score lam θ) (hSlice θ)
    have hw : Measurable (fun z : ℝ × G => ENNReal.ofReal (q z.1 z.2) * score lam z.1 z.2.val) :=
      hq.ennreal_ofReal.mul hS
    rw [funext hh]
    exact Measurable.lintegral_prod_right (ν := μ) (f := fun θ (H : G) => ENNReal.ofReal (q θ H) * score lam θ H.val) hw
  let gain (θ : ℝ) (H : Hist t) := ∫⁻ s, measFisher lam s.1 s.2 θ ∂(P.seed t H)
  have he (θ : ℝ) : protoFisher lam P (t+1) θ = protoFisher lam P t θ + histInt lam θ P t (gain θ) := by
    have := P.isMarkov t
    obtain ⟨F,hF,hEq⟩ := (MeasurableEmbedding.subtype_coe (good_meas t)).exists_measurable_extend
      (hSlice θ) (fun _ => inferInstance)
    have hEq' (H : Hist t) (hh : H ∈ good t) : F H = score lam θ H := congrFun hEq ⟨H,hh⟩
    change histInt lam θ P t (stepInt P lam θ (score lam θ)) = _
    calc
      _ = histInt lam θ P t (fun H => F H + gain θ H) := by
        apply supported
        intro H hh
        rw [hEq' H hh]
        unfold stepInt gain
        trans ∫⁻ s, score lam θ H + measFisher lam s.1 s.2 θ ∂(P.seed t H)
        · apply lintegral_congr_ae
          filter_upwards [P.seed_cov t H] with s hs
          exact step_score lam θ hlam H hh s hs
        · rw [lintegral_add_left measurable_const]
          simp
      _ = histInt lam θ P t F + histInt lam θ P t (gain θ) := hist_add P lam θ t F _ hF
      _ = _ := by
        exact congrArg (fun z => z + histInt lam θ P t (gain θ)) (supported P lam θ t F (score lam θ) hEq')
  unfold Jbar
  simp_rw [he]
  rw [lintegral_add_left hproto, mul_add]

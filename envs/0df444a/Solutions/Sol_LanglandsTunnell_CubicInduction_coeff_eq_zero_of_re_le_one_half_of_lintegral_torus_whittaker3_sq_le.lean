-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e8568f91-d67c-5915-8b51-22459a0842ac

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le
import Theorems.Thm_MeanSquare_eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

noncomputable section

namespace CoeffVanishingReduction

open Filter Topology Set

local notation "𝔾" => AdelicGL 3 (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private def realToInfiniteAdele : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

private def archInclMonoidHom :
    Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) →* Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) where
  toFun := archMatrixInclN (Fin 3) ℚ
  map_one' := archMatrixInclN_one (Fin 3) ℚ
  map_mul' := archMatrixInclN_mul (Fin 3) ℚ

private theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archInclMonoidHom (realToInfiniteAdele.mapMatrix (Matrix.of e)) := rfl

private theorem isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq]
  exact (((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr he)).map
    realToInfiniteAdele.mapMatrix).map archInclMonoidHom

private theorem coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  rw [WhittakerBlock.archRealLift3, dif_pos (isUnit_archRealMat3 he)]
  exact (isUnit_archRealMat3 he).unit_spec

private theorem archRealLift3_mul {e e' : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0)
    (he' : (Matrix.of e').det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of e') =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 e' := by
  have hmul : (Matrix.of (Matrix.of e * Matrix.of e' : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    change (Matrix.of e * Matrix.of e').det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero he he'
  apply Units.ext
  rw [Units.val_mul, coe_archRealLift3 hmul, coe_archRealLift3 he, coe_archRealLift3 he', archRealMat3_eq,
    archRealMat3_eq, archRealMat3_eq]
  change archInclMonoidHom (realToInfiniteAdele.mapMatrix (Matrix.of e * Matrix.of e')) = _
  rw [map_mul, map_mul]

private theorem archRealLift3_one : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have h1 : (Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    change (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0
    rw [Matrix.det_one]
    exact one_ne_zero
  apply Units.ext
  rw [coe_archRealLift3 h1, archRealMat3_eq, Units.val_one]
  change archInclMonoidHom (realToInfiniteAdele.mapMatrix (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1
  rw [map_one, map_one]

private def invEntries3 (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := Matrix.of.symm (Matrix.of e)⁻¹

private theorem contDiff_det3 : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

private theorem contDiff_adjugate3 (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).adjugate i j := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_three] <;> fun_prop

private theorem contDiffOn_invEntries3 :
    ContDiffOn ℝ (⊤ : ℕ∞) invEntries3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  refine ContDiffOn.congr (f := fun e i j => ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate i j) ?_ ?_
  · refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
    exact (contDiff_det3.contDiffOn.inv fun e he => he).mul (contDiff_adjugate3 i j).contDiffOn
  · intro e he
    funext i j
    simp only [invEntries3, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.of_symm_apply, Matrix.smul_apply,
      smul_eq_mul]

private theorem det_of_invEntries3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (Matrix.of (invEntries3 e)).det ≠ 0 := by
  rw [invEntries3, Equiv.apply_symm_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem archRealLift3_inv {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e)⁻¹ = WhittakerBlock.archRealLift3 (invEntries3 e) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← archRealLift3_mul he (det_of_invEntries3 he)]
  have h1 : Matrix.of e * Matrix.of (invEntries3 e) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [invEntries3, Equiv.apply_symm_apply]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr he)
  rw [h1, archRealLift3_one]

private theorem continuous_archRealMat3 : Continuous WhittakerBlock.archRealMat3 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun e : Fin 3 → Fin 3 → ℝ =>
    ((AutomorphicForm.StandardKernel.ofReal (e i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
      InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  exact (AutomorphicForm.StandardKernel.continuous_ofReal.comp
    ((continuous_apply j).comp (continuous_apply i))).prodMk continuous_const

private theorem continuousOn_archRealLift3 :
    ContinuousOn WhittakerBlock.archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine (continuous_archRealMat3.comp continuous_subtype_val).congr fun e => ?_
    exact (coe_archRealLift3 e.2).symm
  · have hinv : ContinuousOn (fun e => WhittakerBlock.archRealMat3 (invEntries3 e))
        {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
      continuous_archRealMat3.comp_continuousOn contDiffOn_invEntries3.continuousOn
    refine (continuousOn_iff_continuous_restrict.mp hinv).congr fun e => ?_
    show WhittakerBlock.archRealMat3 (invEntries3 e.1) =
      ((WhittakerBlock.archRealLift3 e.1)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ).val
    rw [archRealLift3_inv e.2, coe_archRealLift3 (det_of_invEntries3 e.2)]

private def diagEntries (z : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then z else 0

private theorem continuous_diagEntries : Continuous diagEntries := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : i = j
  · simp only [diagEntries, if_pos h]; exact continuous_id
  · simp only [diagEntries, if_neg h]; exact continuous_const

private theorem det_diagEntries (z : ℝ) : (Matrix.of (diagEntries z)).det = z ^ 3 := by
  have h : Matrix.of (diagEntries z) = Matrix.diagonal fun _ : Fin 3 => z := by
    ext i j
    simp only [Matrix.of_apply, diagEntries, Matrix.diagonal_apply]
  rw [h, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private def Lz (z : ℝ) : 𝔾 := WhittakerBlock.archRealLift3 (diagEntries z)

private theorem Lz_one : Lz 1 = 1 := by
  have h : diagEntries 1 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    funext i j
    simp only [diagEntries, Matrix.one_apply]
  unfold Lz
  rw [h]
  exact archRealLift3_one

private theorem continuousOn_Lz : ContinuousOn Lz (Set.Ioi 0) := by
  refine continuousOn_archRealLift3.comp continuous_diagEntries.continuousOn fun z hz => ?_
  show (Matrix.of (diagEntries z)).det ≠ 0
  rw [det_diagEntries]
  exact pow_ne_zero _ (ne_of_gt hz)

variable {n J : ℕ}

private def posQuad : Set ((𝔾 × ℝ) × ℝ) := {q | 0 < q.1.2 ∧ 0 < q.2}

private theorem isOpen_posQuad : IsOpen (posQuad) := by
  show IsOpen ({q : (𝔾 × ℝ) × ℝ | 0 < q.1.2} ∩ {q : (𝔾 × ℝ) × ℝ | 0 < q.2})
  exact (isOpen_lt continuous_const (continuous_snd.comp continuous_fst)).inter
    (isOpen_lt continuous_const continuous_snd)

private def coeffAt (c : Fin n → Fin J → ℝ → 𝔾 → ℂ) (q : (𝔾 × ℝ) × ℝ) : Fin n → Fin J → ℂ :=
  fun i j => if 0 < q.1.2 ∧ 0 < q.2 then c i j q.2 (Lz q.1.2 * q.1.1) else 0

private theorem coeffAt_mk (c : Fin n → Fin J → ℝ → 𝔾 → ℂ) (k : 𝔾) {z y : ℝ} (hz : 0 < z) (hy : 0 < y) :
    coeffAt c ((k, z), y) = fun i j => c i j y (Lz z * k) := by
  funext i j
  exact if_pos ⟨hz, hy⟩

private theorem continuousOn_eval (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (i : Fin n) (j : Fin J) :
    ContinuousOn (fun q : (𝔾 × ℝ) × ℝ => c i j q.2 (Lz q.1.2 * q.1.1)) posQuad := by
  have h1 : ContinuousOn (fun q : (𝔾 × ℝ) × ℝ => (q.2, Lz q.1.2 * q.1.1)) posQuad := by
    refine continuous_snd.continuousOn.prodMk
      (ContinuousOn.mul ?_ (continuous_fst.comp continuous_fst).continuousOn)
    exact continuousOn_Lz.comp (continuous_snd.comp continuous_fst).continuousOn fun q hq => hq.1
  exact (hcont i j).comp h1 fun q hq => hq.2

private theorem continuousOn_coeffAt (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (i : Fin n) (j : Fin J) :
    ContinuousOn (fun q : (𝔾 × ℝ) × ℝ => coeffAt c q i j) posQuad :=
  (continuousOn_eval c hcont i j).congr fun _ hq => if_pos hq

open scoped Classical in
private theorem measurable_coeffAt (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (i : Fin n) (j : Fin J) :
    Measurable fun q : (𝔾 × ℝ) × ℝ => coeffAt c q i j := by
  have h : (fun q : (𝔾 × ℝ) × ℝ => coeffAt c q i j) =
      posQuad.piecewise (fun q : (𝔾 × ℝ) × ℝ => c i j q.2 (Lz q.1.2 * q.1.1)) (fun _ => 0) := by
    funext q
    by_cases hq : q ∈ posQuad
    · rw [Set.piecewise_eq_of_mem _ _ _ hq]; exact if_pos hq
    · rw [Set.piecewise_eq_of_notMem _ _ _ hq]; exact if_neg hq
  rw [h]
  exact (continuousOn_eval c hcont i j).measurable_piecewise continuousOn_const isOpen_posQuad.measurableSet

private def term (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (y₁ : ℝ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin J, d i j * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))

private def dens (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (σ y₁ : ℝ) : ℝ≥0∞ :=
  (‖term e d y₁‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (y₁ ^ (σ - 3))

private def msq (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y₁ in Set.Ioc (0 : ℝ) 1, dens e d σ y₁

private theorem measurable_term (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (e : Fin n → ℂ) :
    Measurable fun r : ((𝔾 × ℝ) × ℝ) × ℝ => term e (coeffAt c r.1) r.2 := by
  unfold term
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_coeffAt c hcont i j).comp measurable_fst).mul
    (((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul
      ((Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_snd)).pow_const _))

private theorem measurable_dens (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (e : Fin n → ℂ) (σ : ℝ) :
    Measurable fun r : ((𝔾 × ℝ) × ℝ) × ℝ => dens e (coeffAt c r.1) σ r.2 := by
  unfold dens
  exact ((measurable_term c hcont e).nnnorm.coe_nnreal_ennreal.pow_const _).mul
    (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _))

private theorem measurable_msq (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (e : Fin n → ℂ) (σ : ℝ) :
    Measurable fun q : (𝔾 × ℝ) × ℝ => msq e (coeffAt c q) σ := by
  unfold msq
  exact (measurable_dens c hcont e σ).lintegral_prod_right

private def sig (m : ℕ) : ℝ := 1 + 1 / ((m : ℝ) + 2)

private theorem sig_sub_one (m : ℕ) : sig m - 1 = 1 / ((m : ℝ) + 2) := by
  unfold sig; ring

private theorem sig_sub_one_pos (m : ℕ) : 0 < sig m - 1 := by
  rw [sig_sub_one]; positivity

private theorem sig_mem (m : ℕ) : sig m ∈ Set.Ioc (1 : ℝ) 2 := by
  refine ⟨by linarith [sig_sub_one_pos m], ?_⟩
  have h : (1 : ℝ) / ((m : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  unfold sig; linarith

private theorem sig_lt {ε : ℝ} (hε : 0 < ε) {M m : ℕ} (hM : 1 / ε < M) (hm : M ≤ m) : sig m < 1 + ε := by
  have h1 : (1 : ℝ) / ε < (m : ℝ) + 2 := by
    have : (M : ℝ) ≤ m := Nat.cast_le.2 hm
    linarith
  have h2 : (1 : ℝ) / ((m : ℝ) + 2) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hε).1 h1
    linarith [mul_comm ε ((m : ℝ) + 2)]
  unfold sig; linarith

private def A (c : Fin n → Fin J → ℝ → 𝔾 → ℂ) (e : Fin n → ℂ) (m : ℕ) (q : (𝔾 × ℝ) × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (sig m - 1) * msq e (coeffAt c q) (sig m)

private def Ψ (c : Fin n → Fin J → ℝ → 𝔾 → ℂ) (e : Fin n → ℂ) (b : ℝ) (m : ℕ) (p : 𝔾 × ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Set.Icc b⁻¹ b, A c e m (p, y)

private def Θ (c : Fin n → Fin J → ℝ → 𝔾 → ℂ) (e : Fin n → ℂ) (b₀ b : ℝ) (m : ℕ) (k : 𝔾) : ℝ≥0∞ :=
  ∫⁻ z in Set.Icc b₀⁻¹ b₀, Ψ c e b m (k, z)

private theorem measurable_A (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (e : Fin n → ℂ) (m : ℕ) :
    Measurable (A c e m) :=
  (measurable_msq c hcont e (sig m)).const_mul _

private theorem measurable_Ψ (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (e : Fin n → ℂ) (b : ℝ)
    (m : ℕ) : Measurable (Ψ c e b m) := by
  unfold Ψ
  refine Measurable.lintegral_prod_right (f := fun p y => A c e m (p, y)) ?_
  exact (measurable_A c hcont e m).comp (measurable_fst.prodMk measurable_snd)

private theorem measurable_Θ (c : Fin n → Fin J → ℝ → 𝔾 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × 𝔾 => c i j p.1 p.2) {p | 0 < p.1}) (e : Fin n → ℂ) (b₀ b : ℝ)
    (m : ℕ) : Measurable (Θ c e b₀ b m) := by
  unfold Θ
  refine Measurable.lintegral_prod_right (f := fun k z => Ψ c e b m (k, z)) ?_
  exact (measurable_Ψ c hcont e b m).comp (measurable_fst.prodMk measurable_snd)

private theorem Θ_eq (c : Fin n → Fin J → ℝ → 𝔾 → ℂ) (e : Fin n → ℂ) {b₀ b : ℝ} (hb₀ : 0 < b₀⁻¹)
    (hb : 0 < b⁻¹) (m : ℕ) (k : 𝔾) :
    Θ c e b₀ b m k = ENNReal.ofReal (sig m - 1) *
      ∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y in Set.Icc b⁻¹ b, msq e (fun i j => c i j y (Lz z * k)) (sig m) := by
  simp only [Θ, Ψ, A]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun z hz => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun y hy => ?_
  rw [coeffAt_mk c k (hb₀.trans_le hz.1) (hb.trans_le hy.1)]

private theorem ae_liminf_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ m, Measurable (f m)) (h : liminf (fun m => ∫⁻ x, f m x ∂μ) atTop < ⊤) :
    ∀ᵐ x ∂μ, liminf (fun m => f m x) atTop < ⊤ :=
  ae_lt_top (Measurable.liminf hf)
    (ne_top_of_le_ne_top h.ne (lintegral_liminf_le' fun m => (hf m).aemeasurable))

private theorem exists_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : α → Prop} {s : Set α}
    (h : ∀ᵐ x ∂μ, p x) (hs : μ s ≠ 0) : ∃ x ∈ s, p x := by
  by_contra H
  exact hs (measure_mono_null (fun x hx hpx => H ⟨x, hx, hpx⟩) (ae_iff.1 h))

private theorem restrict_ne_zero_of_mem_nhds {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [μ.IsOpenPosMeasure] {s t : Set α} {x : α} (hs : s ∈ 𝓝 x)
    (ht : t ∈ 𝓝 x) : μ.restrict s t ≠ 0 := by
  obtain ⟨O, hO, hOo, hxO⟩ := mem_nhds_iff.1 (inter_mem ht hs)
  intro h0
  have h : μ.restrict s O = 0 := measure_mono_null (fun y hy => (hO hy).1) h0
  rw [Measure.restrict_apply hOo.measurableSet, Set.inter_eq_left.2 fun y hy => (hO hy).2] at h
  exact (hOo.measure_ne_zero μ ⟨x, hxO⟩) h

private theorem hM_of_liminf (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ)
    (h : liminf (fun m => ENNReal.ofReal (sig m - 1) * msq e d (sig m)) atTop < ⊤) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ σ : ℝ, 1 < σ ∧ σ < 1 + ε ∧
      ENNReal.ofReal (σ - 1) *
          ∫⁻ y in Set.Ioc (0 : ℝ) 1,
            (‖∑ i : Fin n, ∑ j : Fin J, d i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖₊ : ℝ≥0∞) ^ 2 *
              ENNReal.ofReal (y ^ (σ - 3)) ∂volume ≤
        ENNReal.ofReal C := by
  set ℓ := liminf (fun m => ENNReal.ofReal (sig m - 1) * msq e d (sig m)) atTop with hℓ
  have hℓtop : ℓ ≠ ⊤ := h.ne
  have hℓ1 : ℓ + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hℓtop, ENNReal.one_ne_top⟩
  have hfreq : ∃ᶠ m in atTop, ENNReal.ofReal (sig m - 1) * msq e d (sig m) < ℓ + 1 :=
    frequently_lt_of_liminf_lt (h := ENNReal.lt_add_right hℓtop one_ne_zero)
  refine ⟨(ℓ + 1).toReal, fun ε hε => ?_⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  obtain ⟨m, hmM, hm⟩ := frequently_atTop.1 hfreq M
  refine ⟨sig m, (sig_mem m).1, sig_lt hε hM hmM, ?_⟩
  rw [ENNReal.ofReal_toReal hℓ1]
  exact hm.le

end CoeffVanishingReduction

open CoeffVanishingReduction Filter Topology Set in
theorem solution
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ F
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (b₀ : ℝ) (hb₀ : 1 < b₀) (φ₀ : ℝ) (hφ₀ : 0 < φ₀)
    (hΦ : ∀ k ∈ B, ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) → b₀⁻¹ ≤ a 2 → a 2 ≤ b₀ →
      φ₀ ≤ ‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖)
    (hZ : ∃ C' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
        (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
          ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
              (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F
                    (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
                (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
                ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
            ENNReal.ofReal (C' / (σ - 1)))) :
    ∀ (i : Fin n) (j : Fin J), ((e i).re < 1 / 2 ∨ ((e i).re = 1 / 2 ∧ 1 ≤ (j : ℕ))) →
      ∀ y₂ : ℝ, 0 < y₂ → ∀ k ∈ interior B, c i j y₂ k = 0 := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  intro i j hij y₂ hy₂ k₀ hk₀

  set b : ℝ := max y₂ y₂⁻¹ + 1 with hb_def
  have hmax : 1 ≤ max y₂ y₂⁻¹ := by
    rcases le_or_gt 1 y₂ with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_le_inv₀ hy₂).2 h.le)
  have hb1 : 1 ≤ b := by linarith
  have hyb : y₂ < b := by linarith [le_max_left y₂ y₂⁻¹]
  have hby : b⁻¹ < y₂ := inv_lt_of_inv_lt₀ hy₂ (by linarith [le_max_right y₂ y₂⁻¹])
  have hbinv : 0 < b⁻¹ := inv_pos.2 (by linarith)
  have hb₀inv : 0 < b₀⁻¹ := inv_pos.2 (by linarith)
  have hb₀inv1 : b₀⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb₀

  obtain ⟨N, -, hNn, -, C'', hbox⟩ :=
    LanglandsTunnell.CubicInduction.exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le
      F n J e he c hcont τ hτ hexp B Φ b₀ hb₀ φ₀ hφ₀ hΦ hZ k₀ hk₀ b hb1

  have hbound : ∀ m : ℕ,
      ∫⁻ k in N, Θ c e b₀ b m k ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤ ENNReal.ofReal C'' := by
    intro m
    simp only [Θ_eq c e hb₀inv hbinv m]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc _ ≤ ENNReal.ofReal (sig m - 1) * ENNReal.ofReal (C'' / (sig m - 1)) :=
          mul_le_mul' le_rfl (hbox (sig m) (sig_mem m))
      _ = ENNReal.ofReal C'' := by
          rw [← ENNReal.ofReal_mul (sig_sub_one_pos m).le]
          congr 1
          field_simp [(sig_sub_one_pos m).ne']

  have h1 : ∀ᵐ k ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict N,
      liminf (fun m => Θ c e b₀ b m k) atTop < ⊤ := by
    refine ae_liminf_lt_top (measurable_Θ c hcont e b₀ b)
      (lt_of_le_of_lt (b := ENNReal.ofReal C'') ?_ ENNReal.ofReal_lt_top)
    exact liminf_le_of_le (h := fun a ha => (ha.exists).elim fun m hm => hm.trans (hbound m))
  have h2 : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, liminf (fun m => Θ c e b₀ b m k) atTop < ⊤ →
      ∀ᵐ z ∂(volume : Measure ℝ).restrict (Set.Icc b₀⁻¹ b₀), liminf (fun m => Ψ c e b m (k, z)) atTop < ⊤ :=
    fun k hk => ae_liminf_lt_top (fun m => (measurable_Ψ c hcont e b m).comp measurable_prodMk_left) hk
  have h3 : ∀ p : AdelicGL 3 (𝓞 ℚ) ℚ × ℝ, liminf (fun m => Ψ c e b m p) atTop < ⊤ →
      ∀ᵐ y ∂(volume : Measure ℝ).restrict (Set.Icc b⁻¹ b), liminf (fun m => A c e m (p, y)) atTop < ⊤ :=
    fun p hp => ae_liminf_lt_top (fun m => (measurable_A c hcont e m).comp measurable_prodMk_left) hp

  have h4 : ∀ q : (AdelicGL 3 (𝓞 ℚ) ℚ × ℝ) × ℝ, liminf (fun m => A c e m q) atTop < ⊤ → coeffAt c q i j = 0 :=
    fun q hq =>
      MeanSquare.eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le n J e he
        (coeffAt c q) (hM_of_liminf e (coeffAt c q) hq) i j hij
  have hae : ∀ᵐ k ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict N,
      ∀ᵐ z ∂(volume : Measure ℝ).restrict (Set.Icc b₀⁻¹ b₀),
        ∀ᵐ y ∂(volume : Measure ℝ).restrict (Set.Icc b⁻¹ b), coeffAt c ((k, z), y) i j = 0 :=
    h1.mono fun k hk => (h2 k hk).mono fun z hz => (h3 (k, z) hz).mono fun y hy => h4 _ hy

  by_contra hne
  have hq₀ : coeffAt c ((k₀, 1), y₂) i j = c i j y₂ k₀ := by
    rw [coeffAt_mk c k₀ one_pos hy₂]
    simp only [Lz_one, one_mul]
  have hca : ContinuousAt (fun q : (AdelicGL 3 (𝓞 ℚ) ℚ × ℝ) × ℝ => coeffAt c q i j) ((k₀, 1), y₂) :=
    (continuousOn_coeffAt c hcont i j).continuousAt (isOpen_posQuad.mem_nhds ⟨one_pos, hy₂⟩)
  have hev : {q : (AdelicGL 3 (𝓞 ℚ) ℚ × ℝ) × ℝ | coeffAt c q i j ≠ 0} ∈ (𝓝 k₀ ×ˢ 𝓝 (1 : ℝ)) ×ˢ 𝓝 y₂ := by
    rw [← nhds_prod_eq, ← nhds_prod_eq]
    exact hca.eventually_ne (by rwa [hq₀])
  obtain ⟨UZ, hUZ, V, hV, hsub⟩ := Filter.mem_prod_iff.1 hev
  obtain ⟨U, hU, Z, hZ', hsub'⟩ := Filter.mem_prod_iff.1 hUZ
  have hUpos : (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict N U ≠ 0 :=
    restrict_ne_zero_of_mem_nhds hNn hU
  have hZpos : (volume : Measure ℝ).restrict (Set.Icc b₀⁻¹ b₀) Z ≠ 0 :=
    restrict_ne_zero_of_mem_nhds (Icc_mem_nhds hb₀inv1 hb₀) hZ'
  have hVpos : (volume : Measure ℝ).restrict (Set.Icc b⁻¹ b) V ≠ 0 :=
    restrict_ne_zero_of_mem_nhds (Icc_mem_nhds hby hyb) hV
  obtain ⟨k, hkU, hk⟩ := exists_of_ae hae hUpos
  obtain ⟨z, hzZ, hz⟩ := exists_of_ae hk hZpos
  obtain ⟨y, hyV, hy⟩ := exists_of_ae hz hVpos
  exact hsub (Set.mk_mem_prod (hsub' (Set.mk_mem_prod hkU hzZ)) hyV) hy

end
end S_LanglandsTunnell_CubicInduction_coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le (solution)

-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b1c2b258-d87d-57ee-8a15-507f699e653f

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped ENNReal

namespace WhittakerBlockArchimedean

open LanglandsTunnell.CubicInduction

private def gaussArch : (w : InfinitePlace ℚ) → w.Completion → ℂ :=
  fun _ x => (Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℂ)

private def _root_.WhittakerBlockArchimedean.archDeriv (i j : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => deriv (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 fun a b =>
    (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) 0

p2m_export "WhittakerBlockArchimedean" "archDeriv"

private def casimir2 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => ∑ i : Fin 3, ∑ j : Fin 3, archDeriv i j (archDeriv j i φ) g

private def casimir3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDeriv i j (archDeriv j k (archDeriv k i φ)) g

private def IsCentreFinite (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  (∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m, a m • (casimir2^[m] φ) = 0) ∧
    ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m, a m • (casimir3^[m] φ) = 0

private theorem continuous_upperUnipotent3_of_entries :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (!![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_whittakerIntegrand_of_continuous (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      f (upperUnipotent3 p.1 p.2.1 p.2.2 * g) * NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1)) :=
  (hc.comp (continuous_upperUnipotent3_of_entries.mul continuous_const)).mul
    (NumberField.StandardAddChar.continuous_psiQ.comp
      (continuous_fst.add (continuous_fst.comp continuous_snd)).neg)

private theorem ae_mem_adelicBox_of_productionPins :
    ∀ᵐ z ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν,
      z ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  exact ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)

private theorem isProbabilityMeasure_ν_of_productionPins_adelicBox :
    @IsProbabilityMeasure _ (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)
    (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne' (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

private theorem integrable_adelicBox_of_continuousOn {G : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hG : ContinuousOn G (AdelicBox.adelicBox ℚ)) {M : ℝ} (hM : ∀ z ∈ AdelicBox.adelicBox ℚ, ‖G z‖ ≤ M) :
    Integrable G (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  refine Integrable.mono' (integrable_const M) ?_ (ae_mem_adelicBox_of_productionPins.mono fun z hz => hM z hz)
  rw [productionPinsOf_ν]
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  exact (hG.aestronglyMeasurable (μ := AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    (AdelicBox.measurableSet_adelicBox ℚ)).smul_measure
      (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ))⁻¹

private theorem integrable_of_continuous_productionPins {G : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hG : Continuous G) :
    Integrable G (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  obtain ⟨L, hL, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn hG.continuousOn
  exact integrable_adelicBox_of_continuousOn hG.continuousOn fun z hz => hM z (hsub hz)

private theorem continuous_integral_of_continuous_productionPins {P : Type} [TopologicalSpace P]
    {F : P → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hF : Continuous fun q : P × AdeleRing (𝓞 ℚ) ℚ => F q.1 q.2) :
    Continuous fun p => ∫ z, F p z ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  obtain ⟨L, hL, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hint : ∀ p, Integrable (F p) (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
    intro p
    have hp : Continuous fun z => F p z := hF.comp (f := fun z => (p, z)) (by fun_prop)
    exact integrable_of_continuous_productionPins hp
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  have hU : TendstoUniformlyOn (fun p z => F p z) (F p₀) (nhds p₀) L :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
      ((ContinuousMap.curry ⟨fun q : P × AdeleRing (𝓞 ℚ) ℚ => F q.1 q.2, hF⟩).continuous.tendsto p₀) L hL
  unfold ContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hU (ε / 2) (half_pos hε)] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le_const (C := ε / 2) ?_) ?_
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with z hz
    rw [← dist_eq_norm, dist_comm]
    exact (hp z (hsub hz)).le
  · rw [probReal_univ, mul_one]
    exact half_lt_self hε

private theorem integrable_whittakerIntegrand_levels (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ a b : AdeleRing (𝓞 ℚ) ℚ,
        Integrable (fun z => f (upperUnipotent3 a b z * g) * NumberField.StandardAddChar.psiQ (-(a + b)))
          (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) ∧
      (∀ a : AdeleRing (𝓞 ℚ) ℚ,
        Integrable (fun b => ∫ z, f (upperUnipotent3 a b z * g) * NumberField.StandardAddChar.psiQ (-(a + b))
          ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν)
          (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) ∧
      Integrable (fun a => ∫ b, ∫ z, f (upperUnipotent3 a b z * g) * NumberField.StandardAddChar.psiQ (-(a + b))
          ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν
          ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν)
        (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  have hj := continuous_whittakerIntegrand_of_continuous f hc g
  have hjoint : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      f (upperUnipotent3 q.1.1 q.1.2 q.2 * g) * NumberField.StandardAddChar.psiQ (-(q.1.1 + q.1.2)) :=
    hj.comp (f := fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => (q.1.1, q.1.2, q.2))
      (by fun_prop)
  have h₂ : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      ∫ z, f (upperUnipotent3 q.1 q.2 z * g) * NumberField.StandardAddChar.psiQ (-(q.1 + q.2))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
    continuous_integral_of_continuous_productionPins
      (F := fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => fun z =>
        f (upperUnipotent3 q.1 q.2 z * g) * NumberField.StandardAddChar.psiQ (-(q.1 + q.2))) hjoint
  refine ⟨fun a b => ?_, fun a => ?_, ?_⟩
  · have hz : Continuous fun z => f (upperUnipotent3 a b z * g) * NumberField.StandardAddChar.psiQ (-(a + b)) :=
      hj.comp (f := fun z => (a, b, z)) (by fun_prop)
    exact integrable_of_continuous_productionPins hz
  · have hb : Continuous fun b => ∫ z, f (upperUnipotent3 a b z * g) * NumberField.StandardAddChar.psiQ (-(a + b))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
      h₂.comp (f := fun b => (a, b)) (by fun_prop)
    exact integrable_of_continuous_productionPins hb
  · have ha : Continuous fun a => ∫ b, ∫ z, f (upperUnipotent3 a b z * g) * NumberField.StandardAddChar.psiQ (-(a + b))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
      continuous_integral_of_continuous_productionPins
        (F := fun a b => ∫ z, f (upperUnipotent3 a b z * g) * NumberField.StandardAddChar.psiQ (-(a + b))
          ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) h₂
    exact integrable_of_continuous_productionPins ha

private theorem whittaker3_sum_smul {ι : Type} [Fintype ι] (r : ι → ℝ) (ψ : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hψ : ∀ k, Continuous (ψ k)) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (fun y => ∑ k, r k • ψ k y) x =
      ∑ k, r k • whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (ψ k) x := by
  simp only [whittaker3, Finset.sum_mul, smul_mul_assoc]
  have hz : ∀ a b : AdeleRing (𝓞 ℚ) ℚ,
      (∫ z, ∑ k, r k • (ψ k (upperUnipotent3 a b z * x) * NumberField.StandardAddChar.psiQ (-(a + b)))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) =
      ∑ k, r k • ∫ z, ψ k (upperUnipotent3 a b z * x) * NumberField.StandardAddChar.psiQ (-(a + b))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
    intro a b
    rw [integral_finsetSum]
    · simp only [integral_smul]
    · exact fun k _ => ((integrable_whittakerIntegrand_levels (ψ k) (hψ k) x).1 a b).smul (r k)
  have hb : ∀ a : AdeleRing (𝓞 ℚ) ℚ,
      (∫ b, ∫ z, ∑ k, r k • (ψ k (upperUnipotent3 a b z * x) * NumberField.StandardAddChar.psiQ (-(a + b)))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) =
      ∑ k, r k • ∫ b, ∫ z, ψ k (upperUnipotent3 a b z * x) * NumberField.StandardAddChar.psiQ (-(a + b))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
    intro a
    simp only [hz]
    rw [integral_finsetSum]
    · simp only [integral_smul]
    · exact fun k _ => ((integrable_whittakerIntegrand_levels (ψ k) (hψ k) x).2.1 a).smul (r k)
  simp only [hb]
  rw [integral_finsetSum]
  · simp only [integral_smul]
  · exact fun k _ => ((integrable_whittakerIntegrand_levels (ψ k) (hψ k) x).2.2).smul (r k)

private noncomputable def archOfRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : NumberField.InfinitePlace ℚ =>
    ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.IsTotallyReal.isReal v)).symm : ℝ →+* v.Completion)

private theorem archRealMat3_eq_mapMatrix (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ (archOfRealHom.mapMatrix (Matrix.of e)) := by
  unfold WhittakerBlock.archRealMat3
  congr 1

private theorem archRealMat3_of_mul (e d : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealMat3 e * WhittakerBlock.archRealMat3 d := by
  rw [archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix,
    ← AutomorphicForm.archMatrixInclN_mul, ← map_mul archOfRealHom.mapMatrix]
  rfl

private theorem isUnit_archRealMat3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq_mapMatrix]
  have h1 : IsUnit (Matrix.of e) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 he)
  exact (h1.map archOfRealHom.mapMatrix).map (AutomorphicForm.archMatrixInclHomN (Fin 3) ℚ)

private theorem coe_archRealLift3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_of_det_ne_zero he)]
  exact IsUnit.unit_spec _

private theorem archRealLift3_of_mul {e d : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0)
    (hd : (Matrix.of d).det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 d := by
  have hed : (Matrix.of (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    show (Matrix.of e * Matrix.of d).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero he hd
  apply Units.ext
  rw [Units.val_mul, coe_archRealLift3_of_det_ne_zero he, coe_archRealLift3_of_det_ne_zero hd,
    coe_archRealLift3_of_det_ne_zero hed, archRealMat3_of_mul]

private theorem archRealLift3_one_array : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  apply Units.ext
  rw [coe_archRealLift3_of_det_ne_zero (by show (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0; simp),
    archRealMat3_eq_mapMatrix, Units.val_one]
  have h1 : archOfRealHom.mapMatrix (Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
    rw [show Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ) from rfl, map_one]
  rw [h1, AutomorphicForm.archMatrixInclN_one]

private theorem isOpen_detSet : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_compl_singleton.preimage h

private theorem exists_closedBall_subset_detSet {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall e r ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isOpen_detSet e he
  exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩

private theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

private theorem contDiff_adjugate_of (k l : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).adjugate k l := by
  fin_cases k <;> fin_cases l <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    fun_prop

private theorem contDiffOn_inv_entry (k l : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e)⁻¹ k l)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : ∀ e : Fin 3 → Fin 3 → ℝ, (Matrix.of e)⁻¹ k l = ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate k l := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  simp only [h]
  exact (contDiff_det_of.contDiffOn.inv fun e he => he).mul (contDiff_adjugate_of k l).contDiffOn

private def shiftArray (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

private theorem archDeriv_eq_deriv_shiftArray (i j : Fin 3) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv i j ψ h = deriv (fun s : ℝ => ψ (h * WhittakerBlock.archRealLift3 (shiftArray i j s))) 0 :=
  rfl

private theorem of_shiftArray_eq (i j : Fin 3) (s : ℝ) :
    Matrix.of (shiftArray i j s) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) + s • Matrix.of (Pi.single i (Pi.single j (1 : ℝ))) := by
  ext a b
  simp only [shiftArray, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Pi.single_apply,
    smul_eq_mul]
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb, Pi.single_apply]

private theorem det_of_shiftArray_ne_zero (i j : Fin 3) {s : ℝ} (hs : |s| < 1) :
    (Matrix.of (shiftArray i j s)).det ≠ 0 := by
  have hs' : s ≠ -1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1 : 1 + s ≠ 0 := fun h => hs' (by linarith)
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three, shiftArray, hs1]

private theorem archDeriv_eq_fderiv_apply_of_det_ne_zero (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hψ : WhittakerBlock.IsArchSmooth3 ψ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : (Matrix.of e).det ≠ 0) (i j : Fin 3) :
    archDeriv i j ψ (h * WhittakerBlock.archRealLift3 e) =
      fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => ψ (h * WhittakerBlock.archRealLift3 e')) e
        (Matrix.of e * Matrix.of (Pi.single i (Pi.single j (1 : ℝ))) : Matrix (Fin 3) (Fin 3) ℝ) := by
  set F : (Fin 3 → Fin 3 → ℝ) → ℂ := fun e' => ψ (h * WhittakerBlock.archRealLift3 e') with hF_def
  set D : Fin 3 → Fin 3 → ℝ :=
    (Matrix.of e * Matrix.of (Pi.single i (Pi.single j (1 : ℝ))) : Matrix (Fin 3) (Fin 3) ℝ) with hD_def
  have hF : HasFDerivAt F (fderiv ℝ F e) e := by
    have h1 : DifferentiableOn ℝ F {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
      (hψ h).differentiableOn (by simp)
    exact (h1.differentiableAt (isOpen_detSet.mem_nhds he)).hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => e + s • D) D 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add e
  have hl : HasFDerivAt F (fderiv ℝ F e) ((fun s : ℝ => e + s • D) 0) := by simpa using hF
  have hcomp := hl.comp_hasDerivAt (0 : ℝ) hcurve
  have heq : (fun s : ℝ => ψ (h * WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 (shiftArray i j s)))
      =ᶠ[nhds (0 : ℝ)] F ∘ fun s : ℝ => e + s • D := by
    filter_upwards [eventually_abs_sub_lt (0 : ℝ) zero_lt_one] with s hs
    rw [sub_zero] at hs
    show ψ (h * WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 (shiftArray i j s)) = F (e + s • D)
    have h2 : WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 (shiftArray i j s) =
        WhittakerBlock.archRealLift3 (e + s • D) := by
      rw [← archRealLift3_of_mul he (det_of_shiftArray_ne_zero i j hs), of_shiftArray_eq]
      congr 1
      ext a b
      simp only [hD_def, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
        Pi.add_apply, Pi.smul_apply, Matrix.of_apply]
    rw [hF_def, mul_assoc, h2]
  rw [archDeriv_eq_deriv_shiftArray, heq.deriv_eq, hcomp.deriv]

private theorem contDiff_mul_single (i j : Fin 3) :
    @ContDiff ℝ _ (Fin 3 → Fin 3 → ℝ) _ _ (Fin 3 → Fin 3 → ℝ) _ _ (⊤ : ℕ∞) fun e =>
      (Matrix.of e * Matrix.of (Pi.single i (Pi.single j (1 : ℝ))) : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply]
  fun_prop

private theorem isArchSmooth3_archDeriv_of_isArchSmooth3 {ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hψ : WhittakerBlock.IsArchSmooth3 ψ) (i j : Fin 3) : WhittakerBlock.IsArchSmooth3 (archDeriv i j ψ) :=
  WhittakerBlock.isArchSmooth3_archDeriv hψ i j

private theorem fderiv_archRealLift3_single_eq_sum_inv_smul_archDeriv
    (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hψ : WhittakerBlock.IsArchSmooth3 ψ) (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) (i j : Fin 3) :
    fderiv ℝ (fun e' => ψ (h * WhittakerBlock.archRealLift3 e')) e (Pi.single i (Pi.single j (1 : ℝ))) =
      ∑ k : Fin 3, (Matrix.of e)⁻¹ k i • archDeriv k j ψ (h * WhittakerBlock.archRealLift3 e) := by
  simp_rw [archDeriv_eq_fderiv_apply_of_det_ne_zero ψ hψ h he]
  have hinv : Matrix.of e * (Matrix.of e)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he)

  have key : (Pi.single i (Pi.single j (1 : ℝ)) : Fin 3 → Fin 3 → ℝ) =
      ∑ k : Fin 3, (Matrix.of e)⁻¹ k i •
        fun a b => (Matrix.of e * Matrix.of (Pi.single k (Pi.single j (1 : ℝ)))) a b := by
    funext a b
    have hai : ∑ k : Fin 3, e a k * (Matrix.of e)⁻¹ k i = if a = i then (1 : ℝ) else 0 := by
      have h1 : (Matrix.of e * (Matrix.of e)⁻¹) a i = (1 : Matrix (Fin 3) (Fin 3) ℝ) a i := by rw [hinv]
      simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] using h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.of_apply, Pi.single_apply,
      ite_apply, Pi.zero_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hb : b = j
    · simp only [hb, if_true]
      rw [← hai]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · simp [hb]
  rw [key, map_sum]
  simp only [map_smul]

private theorem continuous_archRealMat3 : Continuous WhittakerBlock.archRealMat3 := by
  refine continuous_matrix fun i j => ?_
  unfold WhittakerBlock.archRealMat3
  simp only [AutomorphicForm.archMatrixInclN, Matrix.of_apply]
  exact (AutomorphicForm.StandardKernel.continuous_ofReal.comp
    ((continuous_apply j).comp (continuous_apply i))).prodMk continuous_const

private theorem det_of_inv_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
  show ((Matrix.of e)⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem archRealLift3_inv_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e)⁻¹ =
      WhittakerBlock.archRealLift3 ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h1 : (Matrix.of e * Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    show Matrix.of e * (Matrix.of e)⁻¹ = 1
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← archRealLift3_of_mul he (det_of_inv_ne_zero he), h1, archRealLift3_one_array]

private theorem continuousOn_archRealLift3_detSet :
    ContinuousOn WhittakerBlock.archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        ((WhittakerBlock.archRealLift3 e.1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 e.1 :=
      fun e => coe_archRealLift3_of_det_ne_zero e.2
    simp only [Set.domRestrict_apply, Function.comp_def, h]
    exact continuous_archRealMat3.comp continuous_subtype_val
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        (((WhittakerBlock.archRealLift3 e.1)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 ((Matrix.of e.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
      intro e
      rw [archRealLift3_inv_of_det_ne_zero e.2]
      exact coe_archRealLift3_of_det_ne_zero (det_of_inv_ne_zero e.2)
    simp only [Set.domRestrict_apply, h]
    refine continuous_archRealMat3.comp ?_
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (contDiffOn_inv_entry k l).continuousOn.comp_continuous continuous_subtype_val fun e => e.2

private theorem exists_bound_of_isCompact (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : Continuous G) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    {S : Set (AdeleRing (𝓞 ℚ) ℚ)} (hS : IsCompact S) {e₀ : Fin 3 → Fin 3 → ℝ} {r : ℝ}
    (hr : Metric.closedBall e₀ r ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    ∃ M : ℝ, ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ e ∈ Metric.closedBall e₀ r,
      ‖G (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e))‖ ≤ M := by
  set T : Set ((AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × (Fin 3 → Fin 3 → ℝ)) :=
    (S ×ˢ S ×ˢ S) ×ˢ Metric.closedBall e₀ r with hT_def
  have hTc : IsCompact T := (hS.prod (hS.prod hS)).prod (isCompact_closedBall e₀ r)
  set m : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × (Fin 3 → Fin 3 → ℝ) → AdelicGL 3 (𝓞 ℚ) ℚ :=
    fun q => upperUnipotent3 q.1.1 q.1.2.1 q.1.2.2 * (g * WhittakerBlock.archRealLift3 q.2) with hm_def
  have hm : ContinuousOn m T := by
    refine ContinuousOn.mul ?_ (continuousOn_const.mul ?_)
    · exact (continuous_upperUnipotent3_of_entries.comp continuous_fst).continuousOn
    · exact (continuousOn_archRealLift3_detSet.mono hr).comp continuousOn_snd fun q hq => hq.2
  obtain ⟨M, hM⟩ := (hTc.image_of_continuousOn hm).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨M, fun x hx y hy z hz e he => ?_⟩
  exact hM (m ((x, y, z), e)) ⟨((x, y, z), e), ⟨⟨hx, hy, hz⟩, he⟩, rfl⟩

private noncomputable def entryFunctional (i j : Fin 3) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.proj i : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))).smulRight (1 : ℂ)

private theorem entryFunctional_apply (i j : Fin 3) (δ : Fin 3 → Fin 3 → ℝ) :
    entryFunctional i j δ = ((δ i j : ℝ) : ℂ) := by
  simp [entryFunctional]

private theorem array_eq_sum_smul_single (δ : Fin 3 → Fin 3 → ℝ) :
    δ = ∑ i : Fin 3, ∑ j : Fin 3, δ i j • (Pi.single i (Pi.single j (1 : ℝ)) : Fin 3 → Fin 3 → ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_three, Pi.single_apply]

private theorem hasFDerivAt_comp_archRealLift3 (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hψ : WhittakerBlock.IsArchSmooth3 ψ)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    HasFDerivAt (fun e' => ψ (h * WhittakerBlock.archRealLift3 e'))
      (∑ i : Fin 3, ∑ j : Fin 3, (∑ k : Fin 3, (Matrix.of e)⁻¹ k i •
        archDeriv k j ψ (h * WhittakerBlock.archRealLift3 e)) • entryFunctional i j) e := by
  have hd : DifferentiableAt ℝ (fun e' => ψ (h * WhittakerBlock.archRealLift3 e')) e :=
    ((hψ h).contDiffAt (isOpen_detSet.mem_nhds he)).differentiableAt (by simp)
  convert hd.hasFDerivAt using 1
  ext δ
  conv_rhs => rw [array_eq_sum_smul_single δ]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    entryFunctional_apply, fderiv_archRealLift3_single_eq_sum_inv_smul_archDeriv ψ hψ h he]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.real_smul, smul_eq_mul, mul_comm]

private theorem hasFDerivAt_integral_of_sum_smul_entryFunctional {α : Type} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {F : (Fin 3 → Fin 3 → ℝ) → α → ℂ} {a : Fin 3 → Fin 3 → (Fin 3 → Fin 3 → ℝ) → α → ℂ}
    {e : Fin 3 → Fin 3 → ℝ} {r : ℝ} (hr : 0 < r) {M : Fin 3 → Fin 3 → ℝ}
    (hFm : ∀ e' ∈ Metric.closedBall e r, MeasureTheory.AEStronglyMeasurable (F e') μ)
    (hFi : MeasureTheory.Integrable (F e) μ)
    (ham : ∀ i j, MeasureTheory.AEStronglyMeasurable (a i j e) μ)
    (hai : ∀ i j, MeasureTheory.Integrable (a i j e) μ)
    (hab : ∀ᵐ z ∂μ, ∀ e' ∈ Metric.closedBall e r, ∀ i j, ‖a i j e' z‖ ≤ M i j)
    (hdiff : ∀ᵐ z ∂μ, ∀ e' ∈ Metric.closedBall e r,
      HasFDerivAt (fun e'' => F e'' z) (∑ i : Fin 3, ∑ j : Fin 3, a i j e' z • entryFunctional i j) e') :
    HasFDerivAt (fun e'' => ∫ z, F e'' z ∂μ)
      (∑ i : Fin 3, ∑ j : Fin 3, (∫ z, a i j e z ∂μ) • entryFunctional i j) e := by
  have hmeas : ∀ᶠ e' in nhds e, MeasureTheory.AEStronglyMeasurable (F e') μ :=
    Filter.eventually_of_mem (Metric.closedBall_mem_nhds e hr) hFm
  have hF'm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∑ i : Fin 3, ∑ j : Fin 3, a i j e z • entryFunctional i j) μ :=
    Finset.aestronglyMeasurable_sum (f := fun i z => ∑ j : Fin 3, a i j e z • entryFunctional i j) Finset.univ
      fun i _ => Finset.aestronglyMeasurable_sum (f := fun j z => a i j e z • entryFunctional i j) Finset.univ
        fun j _ => (ham i j).smul_const (entryFunctional i j)
  have hbound : ∀ᵐ z ∂μ, ∀ e' ∈ Metric.closedBall e r,
      ‖∑ i : Fin 3, ∑ j : Fin 3, a i j e' z • entryFunctional i j‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3, M i j * ‖entryFunctional i j‖ := by
    filter_upwards [hab] with z hz e' he'
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hz e' he' i j) (norm_nonneg _)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun e' z => ∑ i : Fin 3, ∑ j : Fin 3, a i j e' z • entryFunctional i j)
    (Metric.closedBall_mem_nhds e hr) hmeas hFi hF'm hbound (MeasureTheory.integrable_const _) hdiff
  have hsum : (∫ z, ∑ i : Fin 3, ∑ j : Fin 3, a i j e z • entryFunctional i j ∂μ) =
      ∑ i : Fin 3, ∑ j : Fin 3, (∫ z, a i j e z ∂μ) • entryFunctional i j := by
    rw [MeasureTheory.integral_finsetSum _ fun i _ =>
      MeasureTheory.integrable_finsetSum _ fun j _ => (hai i j).smul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_finsetSum _ fun j _ => (hai i j).smul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_const]
  rw [hsum] at key
  exact key

private theorem norm_integral_productionPins_le {G : AdeleRing (𝓞 ℚ) ℚ → ℂ} {M : ℝ}
    (hM : ∀ z ∈ AdelicBox.adelicBox ℚ, ‖G z‖ ≤ M) :
    letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
    ‖∫ z, G z ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν‖ ≤ M := by
  letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (ae_mem_adelicBox_of_productionPins.mono fun z hz => hM z hz)
  simpa using h

private theorem exists_bound_coeff (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {C : Set (AdeleRing (𝓞 ℚ) ℚ)} (hC : IsCompact C) {e : Fin 3 → Fin 3 → ℝ} {r : ℝ}
    (hrU : Metric.closedBall e r ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    ∃ Mc : ℝ, 0 ≤ Mc ∧
      ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ e' ∈ Metric.closedBall e r, ∀ i j : Fin 3,
        ‖∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
          archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))‖ ≤ Mc := by
  have hDk : ∀ k j : Fin 3, Continuous (archDeriv k j φ) := fun k j => by simpa using hD [(k, j)]
  choose Md hMd using fun k j : Fin 3 => exists_bound_of_isCompact (archDeriv k j φ) (hDk k j) g hC hrU
  choose Mi hMi using fun k i : Fin 3 => (isCompact_closedBall e r).exists_bound_of_continuousOn
    (((contDiffOn_inv_entry k i).continuousOn).mono hrU)
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, |Mi k i| * |Md k j|,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _),
    fun x hx y hy z hz e' he' i j => ?_⟩
  have hnn : ∀ i' j' : Fin 3, 0 ≤ ∑ k : Fin 3, |Mi k i'| * |Md k j'| := fun i' j' =>
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => ?_).trans
    ((Finset.single_le_sum (fun j' _ => hnn i j') (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' _ => hnn i' j') (Finset.mem_univ i)))
  rw [norm_smul]
  exact mul_le_mul ((hMi k i e' he').trans (le_abs_self _)) ((hMd k j x hx y hy z hz e' he').trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

private theorem exists_bound_psiQ {C : Set (AdeleRing (𝓞 ℚ) ℚ)} (hC : IsCompact C) :
    ∃ Mψ : ℝ, 0 ≤ Mψ ∧ ∀ x ∈ C, ∀ y ∈ C, ‖NumberField.StandardAddChar.psiQ (-(x + y))‖ ≤ Mψ := by
  obtain ⟨M, hM⟩ := (hC.prod hC).exists_bound_of_continuousOn
    (f := fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => NumberField.StandardAddChar.psiQ (-(p.1 + p.2)))
    (NumberField.StandardAddChar.continuous_psiQ.comp (by fun_prop)).continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x hx y hy => (hM (x, y) ⟨hx, hy⟩).trans (le_max_left _ _)⟩

private theorem hasFDerivAt_innerIntegral_archRealLift3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {C : Set (AdeleRing (𝓞 ℚ) ℚ)} (hC : IsCompact C) (hBC : AdelicBox.adelicBox ℚ ⊆ C)
    {x y : AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ C) (hy : y ∈ C) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
    HasFDerivAt (fun e' => ∫ z, φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν)
      (∑ i : Fin 3, ∑ j : Fin 3, (∫ z, ∑ k : Fin 3, (Matrix.of e)⁻¹ k i •
          archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) • entryFunctional i j) e := by
  letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  have hc : Continuous φ := by simpa using hD []
  have hDk : ∀ k j : Fin 3, Continuous (archDeriv k j φ) := fun k j => by simpa using hD [(k, j)]
  obtain ⟨r, hr, hrU⟩ := exists_closedBall_subset_detSet he
  obtain ⟨Mc, -, hMc⟩ := exists_bound_coeff φ hD g hC hrU
  have hn : ∀ e' : Fin 3 → Fin 3 → ℝ, Continuous fun z : AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e') := fun e' =>
    (continuous_upperUnipotent3_of_entries.comp
      (by fun_prop : Continuous fun z : AdeleRing (𝓞 ℚ) ℚ => (x, y, z))).mul continuous_const
  have hcoefc : ∀ (i j : Fin 3) (e' : Fin 3 → Fin 3 → ℝ), Continuous fun z : AdeleRing (𝓞 ℚ) ℚ =>
      ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
        archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e')) := fun i j e' =>
    continuous_finsetSum _ fun k _ => ((hDk k j).comp (hn e')).fun_const_smul _
  refine hasFDerivAt_integral_of_sum_smul_entryFunctional hr (M := fun _ _ => Mc)
    (a := fun i j e' z => ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
      archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e')))
    (fun e' _ => (integrable_of_continuous_productionPins (hc.comp (hn e'))).aestronglyMeasurable)
    (integrable_of_continuous_productionPins (hc.comp (hn e)))
    (fun i j => (integrable_of_continuous_productionPins (hcoefc i j e)).aestronglyMeasurable)
    (fun i j => integrable_of_continuous_productionPins (hcoefc i j e)) ?_ ?_
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with z hz e' he' i j
    exact hMc x hx y hy z (hBC hz) e' he' i j
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with z hz e' he'
    have h := hasFDerivAt_comp_archRealLift3 φ hsa (upperUnipotent3 x y z * g) (hrU he')
    simpa only [mul_assoc] using h

private theorem hasFDerivAt_middleIntegral_archRealLift3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {C : Set (AdeleRing (𝓞 ℚ) ℚ)} (hC : IsCompact C) (hBC : AdelicBox.adelicBox ℚ ⊆ C)
    {x : AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ C) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
    HasFDerivAt (fun e' => ∫ y, (∫ z, φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν)
      (∑ i : Fin 3, ∑ j : Fin 3, (∫ y, (∫ z, ∑ k : Fin 3, (Matrix.of e)⁻¹ k i •
          archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) • entryFunctional i j) e := by
  letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  have hc : Continuous φ := by simpa using hD []
  have hDk : ∀ k j : Fin 3, Continuous (archDeriv k j φ) := fun k j => by simpa using hD [(k, j)]
  obtain ⟨r, hr, hrU⟩ := exists_closedBall_subset_detSet he
  obtain ⟨Mc, hMcn, hMc⟩ := exists_bound_coeff φ hD g hC hrU
  obtain ⟨Mψ, -, hMψ⟩ := exists_bound_psiQ hC
  have hψc : Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => NumberField.StandardAddChar.psiQ (-(x + y)) :=
    NumberField.StandardAddChar.continuous_psiQ.comp (by fun_prop)
  have hn : ∀ e' : Fin 3 → Fin 3 → ℝ, Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 x q.1 q.2 * (g * WhittakerBlock.archRealLift3 e') := fun e' =>
    (continuous_upperUnipotent3_of_entries.comp
      (by fun_prop : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (x, q.1, q.2))).mul continuous_const
  have hI : ∀ e' : Fin 3 → Fin 3 → ℝ, Continuous fun y =>
      (∫ z, φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y)) := fun e' =>
    (continuous_integral_of_continuous_productionPins
      (F := fun y z => φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))) (hc.comp (hn e'))).mul hψc
  have hJ : ∀ (i j : Fin 3) (e' : Fin 3 → Fin 3 → ℝ), Continuous fun y =>
      (∫ z, ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
        archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y)) := fun i j e' =>
    (continuous_integral_of_continuous_productionPins
      (F := fun y z => ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
        archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e')))
      (continuous_finsetSum _ fun k _ => ((hDk k j).comp (hn e')).fun_const_smul _)).mul hψc
  refine hasFDerivAt_integral_of_sum_smul_entryFunctional hr (M := fun _ _ => Mc * Mψ)
    (a := fun i j e' y => (∫ z, ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
        archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
      ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
        NumberField.StandardAddChar.psiQ (-(x + y)))
    (fun e' _ => (integrable_of_continuous_productionPins (hI e')).aestronglyMeasurable)
    (integrable_of_continuous_productionPins (hI e))
    (fun i j => (integrable_of_continuous_productionPins (hJ i j e)).aestronglyMeasurable)
    (fun i j => integrable_of_continuous_productionPins (hJ i j e)) ?_ ?_
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with y hy e' he' i j
    rw [norm_mul]
    exact mul_le_mul (norm_integral_productionPins_le fun z hz => hMc x hx y (hBC hy) z (hBC hz) e' he' i j)
      (hMψ x hx y (hBC hy)) (norm_nonneg _) hMcn
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with y hy e' he'
    have h := (hasFDerivAt_innerIntegral_archRealLift3 φ hsa hD g hC hBC hx (hBC hy) (hrU he')).mul_const
      (NumberField.StandardAddChar.psiQ (-(x + y)))
    refine h.congr_fderiv (Eq.symm ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, mul_comm]

private theorem continuous_innerIntegral_mul_psiQ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e' : Fin 3 → Fin 3 → ℝ) :
    Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (∫ z, φ (upperUnipotent3 q.1 q.2 z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(q.1 + q.2)) := by
  have hn : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 q.1.1 q.1.2 q.2 * (g * WhittakerBlock.archRealLift3 e') :=
    (continuous_upperUnipotent3_of_entries.comp
      (by fun_prop : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
        (q.1.1, q.1.2, q.2))).mul continuous_const
  have hI := continuous_integral_of_continuous_productionPins
    (F := fun (q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) z =>
      φ (upperUnipotent3 q.1 q.2 z * (g * WhittakerBlock.archRealLift3 e'))) (hc.comp hn)
  exact hI.mul (NumberField.StandardAddChar.continuous_psiQ.comp (by fun_prop))

private theorem continuous_middleIntegral (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (e' : Fin 3 → Fin 3 → ℝ) :
    Continuous fun x : AdeleRing (𝓞 ℚ) ℚ =>
      ∫ y, (∫ z, φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  continuous_integral_of_continuous_productionPins
    (F := fun x y => (∫ z, φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
      ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
        NumberField.StandardAddChar.psiQ (-(x + y))) (continuous_innerIntegral_mul_psiQ φ hc g e')

private theorem continuous_innerCoeffIntegral_mul_psiQ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hDk : ∀ k j : Fin 3, Continuous (archDeriv k j φ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e' : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) :
    Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (∫ z, ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
        archDeriv k j φ (upperUnipotent3 q.1 q.2 z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(q.1 + q.2)) := by
  have hn : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 q.1.1 q.1.2 q.2 * (g * WhittakerBlock.archRealLift3 e') :=
    (continuous_upperUnipotent3_of_entries.comp
      (by fun_prop : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
        (q.1.1, q.1.2, q.2))).mul continuous_const
  have hI := continuous_integral_of_continuous_productionPins
    (F := fun (q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) z => ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
      archDeriv k j φ (upperUnipotent3 q.1 q.2 z * (g * WhittakerBlock.archRealLift3 e')))
    (continuous_finsetSum _ fun k _ => ((hDk k j).comp hn).fun_const_smul _)
  exact hI.mul (NumberField.StandardAddChar.continuous_psiQ.comp (by fun_prop))

private theorem continuous_middleCoeffIntegral (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hDk : ∀ k j : Fin 3, Continuous (archDeriv k j φ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e' : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) :
    Continuous fun x : AdeleRing (𝓞 ℚ) ℚ =>
      ∫ y, (∫ z, ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
        archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  continuous_integral_of_continuous_productionPins
    (F := fun x y => (∫ z, ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
        archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
      ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
        NumberField.StandardAddChar.psiQ (-(x + y))) (continuous_innerCoeffIntegral_mul_psiQ φ hDk g e' i j)

private theorem hasFDerivAt_outerIntegral_archRealLift3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {C : Set (AdeleRing (𝓞 ℚ) ℚ)} (hC : IsCompact C) (hBC : AdelicBox.adelicBox ℚ ⊆ C)
    {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
    HasFDerivAt (fun e' => ∫ x, ∫ y, (∫ z, φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν)
      (∑ i : Fin 3, ∑ j : Fin 3, (∫ x, ∫ y, (∫ z, ∑ k : Fin 3, (Matrix.of e)⁻¹ k i •
          archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) • entryFunctional i j) e := by
  letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  have hc : Continuous φ := by simpa using hD []
  have hDk : ∀ k j : Fin 3, Continuous (archDeriv k j φ) := fun k j => by simpa using hD [(k, j)]
  obtain ⟨r, hr, hrU⟩ := exists_closedBall_subset_detSet he
  obtain ⟨Mc, hMcn, hMc⟩ := exists_bound_coeff φ hD g hC hrU
  obtain ⟨Mψ, hMψn, hMψ⟩ := exists_bound_psiQ hC
  have hFm := fun e' (_ : e' ∈ Metric.closedBall e r) =>
    (integrable_of_continuous_productionPins (continuous_middleIntegral φ hc g e')).aestronglyMeasurable
  have hFi := integrable_of_continuous_productionPins (continuous_middleIntegral φ hc g e)
  have ham := fun i j : Fin 3 =>
    (integrable_of_continuous_productionPins (continuous_middleCoeffIntegral φ hDk g e i j)).aestronglyMeasurable
  have hai := fun i j : Fin 3 => integrable_of_continuous_productionPins (continuous_middleCoeffIntegral φ hDk g e i j)
  refine hasFDerivAt_integral_of_sum_smul_entryFunctional hr (M := fun _ _ => Mc * Mψ)
    (a := fun i j e' x => ∫ y, (∫ z, ∑ k : Fin 3, (Matrix.of e')⁻¹ k i •
        archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
      ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
        NumberField.StandardAddChar.psiQ (-(x + y))
      ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν)
    hFm hFi ham hai ?_ ?_
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with x hx e' he' i j
    refine norm_integral_productionPins_le fun y hy => ?_
    rw [norm_mul]
    exact mul_le_mul (norm_integral_productionPins_le fun z hz => hMc x (hBC hx) y (hBC hy) z (hBC hz) e' he' i j)
      (hMψ x (hBC hx) y (hBC hy)) (norm_nonneg _) hMcn
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with x hx e' he'
    exact hasFDerivAt_middleIntegral_archRealLift3 φ hsa hD g hC hBC (hBC hx) (hrU he')

private theorem hasFDerivAt_whittaker3_archRealLift3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    HasFDerivAt (fun e' => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3 e'))
      (∑ i : Fin 3, ∑ j : Fin 3, (∑ k : Fin 3, (Matrix.of e)⁻¹ k i •
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (archDeriv k j φ) (g * WhittakerBlock.archRealLift3 e)) •
        entryFunctional i j) e := by
  have hDk : ∀ k j : Fin 3, Continuous (archDeriv k j φ) := fun k j => by simpa using hD [(k, j)]
  obtain ⟨C, hC, hBC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have L := hasFDerivAt_outerIntegral_archRealLift3 φ hsa hD g hC hBC he
  have hW : (fun e' : Fin 3 → Fin 3 → ℝ =>
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3 e')) = fun e' =>
      letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      ∫ x, ∫ y, (∫ z, φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e'))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
    funext e'
    simp only [whittaker3, MeasureTheory.integral_mul_const]
  have hcoef : ∀ i j : Fin 3,
      (letI := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      ∫ x, ∫ y, (∫ z, ∑ k : Fin 3, (Matrix.of e)⁻¹ k i •
          archDeriv k j φ (upperUnipotent3 x y z * (g * WhittakerBlock.archRealLift3 e))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) *
          NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) =
      ∑ k : Fin 3, (Matrix.of e)⁻¹ k i •
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (archDeriv k j φ) (g * WhittakerBlock.archRealLift3 e) := by
    intro i j
    rw [← whittaker3_sum_smul (fun k => (Matrix.of e)⁻¹ k i) (fun k => archDeriv k j φ) (fun k => hDk k j)
      (g * WhittakerBlock.archRealLift3 e)]
    simp only [whittaker3, MeasureTheory.integral_mul_const]
  rw [hW]
  simp only [← hcoef]
  exact L

private theorem differentiableAt_whittaker3_archRealLift3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    DifferentiableAt ℝ (fun e' => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3 e')) e :=
  (hasFDerivAt_whittaker3_archRealLift3 φ hsa hD g he).differentiableAt

private theorem fderiv_whittaker3_archRealLift3_apply (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) (δ : Fin 3 → Fin 3 → ℝ) :
    fderiv ℝ (fun e' => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3 e')) e δ =
      ∑ k : Fin 3, ∑ j : Fin 3, ((Matrix.of e)⁻¹ * Matrix.of δ) k j •
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (archDeriv k j φ) (g * WhittakerBlock.archRealLift3 e) := by
  rw [(hasFDerivAt_whittaker3_archRealLift3 φ hsa hD g he).fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, entryFunctional_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.of_apply]
  simp only [Finset.sum_smul, Complex.real_smul, Complex.ofReal_mul]
  simp only [Fin.sum_univ_three]
  ring

private theorem shiftedIdentityArray_eq (i j : Fin 3) (s : ℝ) :
    (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) =
      Matrix.of.symm (1 : Matrix (Fin 3) (Fin 3) ℝ) +
        s • (Pi.single i (Pi.single j (1 : ℝ)) : Fin 3 → Fin 3 → ℝ) := by
  funext a b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_symm_apply, Matrix.one_apply, Pi.single_apply,
    ite_apply, Pi.zero_apply, ite_and, mul_ite, mul_one, mul_zero]

private theorem whittaker3_archDeriv_eq_archDeriv_whittaker3_of_isArchSmooth3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w)) (i j : Fin 3) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (archDeriv i j φ) =
      archDeriv i j (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ) := by
  funext g
  have h1 : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 3) (Fin 3) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have hF := hasFDerivAt_whittaker3_archRealLift3 φ hsa hD g h1
  have hcurve : HasDerivAt (fun s : ℝ => Matrix.of.symm (1 : Matrix (Fin 3) (Fin 3) ℝ) +
      s • (Pi.single i (Pi.single j (1 : ℝ)) : Fin 3 → Fin 3 → ℝ))
      (Pi.single i (Pi.single j (1 : ℝ)) : Fin 3 → Fin 3 → ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single i (Pi.single j (1 : ℝ)) : Fin 3 → Fin 3 → ℝ)).const_add
        (Matrix.of.symm (1 : Matrix (Fin 3) (Fin 3) ℝ))
  have hcomp := hF.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)

  change _ = deriv (fun s : ℝ =>
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3
        (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) 0
  simp only [shiftedIdentityArray_eq]
  rw [show (fun s : ℝ => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3
        (Matrix.of.symm (1 : Matrix (Fin 3) (Fin 3) ℝ) +
          s • (Pi.single i (Pi.single j (1 : ℝ)) : Fin 3 → Fin 3 → ℝ)))) =
      (fun e' => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3 e')) ∘ fun s : ℝ =>
          Matrix.of.symm (1 : Matrix (Fin 3) (Fin 3) ℝ) +
            s • (Pi.single i (Pi.single j (1 : ℝ)) : Fin 3 → Fin 3 → ℝ) from rfl, hcomp.deriv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, entryFunctional_apply, smul_eq_mul]
  have hinv : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 3) (Fin 3) ℝ)))⁻¹ = 1 := by
    rw [Equiv.apply_symm_apply, inv_one]
  have hone : WhittakerBlock.archRealLift3 (Matrix.of.symm (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 :=
    archRealLift3_one_array
  simp only [hinv, hone, mul_one, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, Pi.single_apply]

private theorem isArchSmooth3_foldr_archDeriv (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (w : List (Fin 3 × Fin 3)) :
    WhittakerBlock.IsArchSmooth3 (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w) := by
  induction w with
  | nil => simpa using hsa
  | cons ij w ih => simpa using isArchSmooth3_archDeriv_of_isArchSmooth3 ih ij.1 ij.2

private theorem continuous_foldr_foldr_archDeriv (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w))
    (w w' : List (Fin 3 × Fin 3)) :
    Continuous
      (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w) w') := by
  rw [← List.foldr_append]
  exact hD (w' ++ w)

private theorem contDiffOn_nat_whittaker3_archRealLift3 (m : ℕ) :
    ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ →
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w)) →
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ContDiffOn ℝ m
          (fun e : Fin 3 → Fin 3 → ℝ =>
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3 e))
          {e | (Matrix.of e).det ≠ 0} := by
  induction m with
  | zero =>
    intro φ hsa hD g
    simp only [Nat.cast_zero, contDiffOn_zero]
    intro e he
    exact (differentiableAt_whittaker3_archRealLift3 φ hsa hD g he).continuousAt.continuousWithinAt
  | succ m ih =>
    intro φ hsa hD g
    rw [Nat.cast_succ]
    have hdiff : DifferentiableOn ℝ
        (fun e : Fin 3 → Fin 3 → ℝ =>
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ (g * WhittakerBlock.archRealLift3 e))
        {e | (Matrix.of e).det ≠ 0} :=
      fun e he => (differentiableAt_whittaker3_archRealLift3 φ hsa hD g he).differentiableWithinAt
    refine contDiffOn_succ_of_fderiv_apply hdiff (fun h => by simp at h) ?_
    intro δ

    have hD' : ∀ k j : Fin 3, ∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) (archDeriv k j φ) w) := by
      intro k j w
      simpa [List.foldr_append] using hD (w ++ [(k, j)])

    have hcoef : ∀ k j : Fin 3,
        ContDiffOn ℝ m (fun e : Fin 3 → Fin 3 → ℝ => ((Matrix.of e)⁻¹ * Matrix.of δ) k j)
          {e | (Matrix.of e).det ≠ 0} := by
      intro k j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      exact ContDiffOn.sum fun l _ => ((contDiffOn_inv_entry k l).of_le (mod_cast le_top)).mul contDiffOn_const

    have hsum : ContDiffOn ℝ m
        (fun e : Fin 3 → Fin 3 → ℝ => ∑ k : Fin 3, ∑ j : Fin 3, ((Matrix.of e)⁻¹ * Matrix.of δ) k j •
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (archDeriv k j φ) (g * WhittakerBlock.archRealLift3 e))
        {e | (Matrix.of e).det ≠ 0} :=
      ContDiffOn.sum fun k _ => ContDiffOn.sum fun j _ => (hcoef k j).smul
        (ih (archDeriv k j φ) (isArchSmooth3_archDeriv_of_isArchSmooth3 hsa k j) (hD' k j) g)
    refine hsum.congr ?_
    intro e he
    simp only [fderivWithin_of_isOpen isOpen_detSet he, fderiv_whittaker3_archRealLift3_apply φ hsa hD g he δ]

private theorem isArchSmooth3_whittaker3_of_isArchSmooth3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w)) :
    WhittakerBlock.IsArchSmooth3
      (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ) := by
  intro g
  exact contDiffOn_infty.2 fun m => contDiffOn_nat_whittaker3_archRealLift3 m φ hsa hD g

private theorem whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w)) :
    (∀ w : List (Fin 3 × Fin 3),
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w) =
          List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ)
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ) w) ∧
      WhittakerBlock.IsArchSmooth3
        (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ) := by
  have hsaw := isArchSmooth3_foldr_archDeriv φ hsa
  have hDw := continuous_foldr_foldr_archDeriv φ hD
  refine ⟨fun w => ?_, isArchSmooth3_whittaker3_of_isArchSmooth3 φ hsa hD⟩
  induction w with
  | nil => rfl
  | cons ij w ih =>
    simp only [List.foldr_cons]
    rw [whittaker3_archDeriv_eq_archDeriv_whittaker3_of_isArchSmooth3 _ (hsaw w) (hDw w) ij.1 ij.2, ih]

end WhittakerBlockArchimedean

open LanglandsTunnell.CubicInduction
open IsDedekindDomain NumberField AutomorphicForm

theorem solution
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w)) :
    (∀ w : List (Fin 3 × Fin 3),
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w) =
          List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ)
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ) w) ∧
      WhittakerBlock.IsArchSmooth3
        (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ) :=
  WhittakerBlockArchimedean.whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 φ hsa hD

end
end S_LanglandsTunnell_CubicInduction_whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 (solution)

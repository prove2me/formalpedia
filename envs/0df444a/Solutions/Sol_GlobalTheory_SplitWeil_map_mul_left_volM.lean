-- Prove2me | solution 1 for GlobalTheory.SplitWeil.map_mul_left_volM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:39:06.030843+00:00
-- url     : https://prove2.me/submissions/570df982-49e7-4680-8527-6673d500d3d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mul_mul_volM
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (h : GL n k) :
    (volM ν n n).map (fun x => h.val * x) =
      ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ))) • volM ν n n := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  haveI : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  haveI : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e : Matrix n n k ≃+ Matrix n n k :=
    { toFun := fun x => h.val * x
      invFun := fun x => (h⁻¹).val * x
      left_inv := fun x => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun x y => Matrix.mul_add _ _ _ }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  haveI := e.isAddHaarMeasure_map (volM ν n n) c1 c2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (volM ν n n).map e = c • volM ν n n :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  change (volM ν n n).map e = _
  set K : Set (Matrix n n k) := {A | ∀ i j, A i j ∈ 𝒪[k]} with hK
  have hKo : IsOpen K := SplitFlip.isOpen_intMatrix
  have hKc : IsCompact K := SplitFlip.isCompact_intMatrix
  have h0 : volM ν n n K ≠ 0 := (hKo.measure_pos _ ⟨0, fun _ _ => zero_mem _⟩).ne'
  have ht : volM ν n n K ≠ ⊤ := hKc.measure_lt_top.ne
  have hr : (volM ν n n).real K ≠ 0 := by simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, ht]
  have key := integral_comp_mul_mul_volM ν (1 : GL n k) h (K.indicator fun _ => (1 : ℂ))
  have h1 : ∫ x, K.indicator (fun _ => (1 : ℂ)) (h.val * x * (1 : GL n k).val) ∂(volM ν n n) =
      ∫ x, K.indicator (fun _ => (1 : ℂ)) x ∂((volM ν n n).map e) := by
    rw [integral_map c1.measurable.aemeasurable
      (stronglyMeasurable_const.indicator hKo.measurableSet).aestronglyMeasurable]
    simp only [Units.val_one, Matrix.mul_one]
    rfl
  rw [h1, hc, integral_smul_nnreal_measure, integral_indicator_const _ hKo.measurableSet, map_one, nabs_one,
    Real.one_rpow, mul_one] at key
  have h2 : (c : ℝ) = nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ)) := by
    refine mul_right_cancel₀ hr ?_
    simp only [NNReal.smul_def, smul_smul, Complex.real_smul, mul_one] at key
    exact_mod_cast key
  rw [hc, ← h2, ENNReal.ofReal_coe_nnreal]
  rfl
end GlobalTheory.SplitWeil

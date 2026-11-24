-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.exists_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:54.021918+00:00
-- url     : https://prove2.me/submissions/d0affe35-0dec-4bf7-a09c-b3f59d25fe4a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_trace_mul_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_trace
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_trace_eq_sum
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (w : InfinitePlace F) :
    ∃ x : Ainf F, (∀ w', w' ≠ w → x w' = 0) ∧ psiInf F ψ x ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_trace hψ
  have ha0 := trace_mul_ne_zero hψ ha
  let T : Ainf F → ℝ := fun z => ∑ u : InfinitePlace F,
    u.mult * (u.embedding a * InfinitePlace.Completion.extensionEmbedding u (z u)).re
  have hT : Continuous T := continuous_finset_sum _ fun u _ => continuous_const.mul
    (Complex.continuous_re.comp (continuous_const.mul
      ((InfinitePlace.Completion.isometry_extensionEmbedding u).continuous.comp (continuous_apply u))))
  have hemb : ∀ (u : InfinitePlace F) (x : F),
      InfinitePlace.Completion.extensionEmbedding u (algebraMap F u.Completion x) = u.embedding x :=
    fun u x => InfinitePlace.Completion.extensionEmbedding_coe u _
  have h1 : (fun z => ψ (pairA F z 0)) =
      fun z => Complex.exp (2 * Real.pi * Complex.I * ((T z : ℝ) : ℂ)) :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      (hψ.1.comp (continuous_id.prodMk continuous_const))
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hT)))
      (funext fun x => by
        have e : T (algebraMap F (Ainf F) x) = ((Algebra.trace ℚ F (a * x) : ℚ) : ℝ) := by
          rw [trace_eq_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [map_mul, ← hemb u x]
          rfl
        simp only [Function.comp_apply, ha, e, Complex.ofReal_ratCast])
  have hm : (w.mult : F) ≠ 0 := Nat.cast_ne_zero.2 w.mult_ne_zero
  let z : Ainf F := Pi.single (M := fun u : InfinitePlace F => u.Completion) w
    (algebraMap F _ (a * 2 * w.mult)⁻¹)
  have hz : ∀ w', w' ≠ w → z w' = 0 := fun w' h => Pi.single_eq_of_ne h _
  refine ⟨z, hz, ?_⟩
  have e : T z = 1 / 2 := by
    have hzw : z w = algebraMap F _ (a * 2 * w.mult)⁻¹ := Pi.single_eq_same _ _
    have hm' : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.2 w.mult_ne_zero
    have e2 : a * (a * 2 * w.mult)⁻¹ = (((2 * w.mult : ℚ)⁻¹ : ℚ) : F) := by
      push_cast
      field_simp
    simp only [T]
    rw [Finset.sum_eq_single w (fun u _ hu => by simp [hz u hu]) (by simp), hzw, hemb, ← map_mul, e2,
      map_ratCast, Complex.ratCast_re]
    push_cast
    field_simp
  have e3 : 2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [psiInf, congrFun h1 z, e, e3, Complex.exp_pi_mul_I]
  norm_num
end GlobalTheory.CompanionTheory.AdeleCharLocal

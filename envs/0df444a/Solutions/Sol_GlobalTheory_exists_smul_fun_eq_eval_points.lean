-- Prove2me | solution 1 for GlobalTheory.exists_smul_fun_eq_eval_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:27.126832+00:00
-- url     : https://prove2.me/submissions/778a7e1f-d066-4462-857f-66e100352b18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GroupLikeIntegralOfFiniteFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvalEqOfMultiplicativeOnPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O C A : Type) [CommRing O] [IsDomain O] [Field C]
    [Algebra O C] [IsFractionRing O C] [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Free O A] (κ : (A →ₐ[O] C) → C) :
    ∃ (d : O) (a : A), d ≠ 0 ∧ ∀ x : A →ₐ[O] C, x a = algebraMap O C d * κ x := by
  classical
  have hli : LinearIndependent C (fun x : A →ₐ[O] C => x.toLinearMap) :=
    linearIndependent_algHom_toLinearMap O A C
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (Finsupp.linearCombination C (fun x : A →ₐ[O] C => x.toLinearMap))
    (LinearMap.ker_eq_bot.mpr hli)
  let l : (A →ₗ[O] C) →ₗ[C] C := Finsupp.linearCombination C κ ∘ₗ g
  have hl : ∀ x : A →ₐ[O] C, l x.toLinearMap = κ x := by
    intro x
    have := LinearMap.congr_fun hg (Finsupp.single x 1)
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] at this
    simp only [l, LinearMap.comp_apply, this, Finsupp.linearCombination_single, one_smul]
  let B := Module.Free.chooseBasis O A
  let c := fun i => l (Algebra.linearMap O C ∘ₗ B.coord i)
  have hc : ∀ f : A →ₗ[O] C, l f = ∑ i, f (B i) * c i := by
    intro f
    have : f = ∑ i, f (B i) • (Algebra.linearMap O C ∘ₗ B.coord i) := by
      refine B.ext fun j => ?_
      rw [LinearMap.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Finsupp.single_apply, hij.symm]
      · simp
    conv_lhs => rw [this]
    simp only [map_sum, map_smul, smul_eq_mul, c]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) c
  choose o ho using hd
  refine ⟨d, ∑ i, o i • B i, nonZeroDivisors.coe_ne_zero d, fun x => ?_⟩
  rw [← hl, hc, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, ho, Algebra.smul_def]
  simp only [AlgHom.toLinearMap_apply]
  ring
end GlobalTheory

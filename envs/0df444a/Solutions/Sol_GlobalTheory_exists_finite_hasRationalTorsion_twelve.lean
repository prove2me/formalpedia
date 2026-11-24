-- Prove2me | solution 1 for GlobalTheory.exists_finite_hasRationalTorsion_twelve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:08:42.655855+00:00
-- url     : https://prove2.me/submissions/08603777-cc9a-4450-92a6-6d4abb9a8de4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Theorems.Thm_GlobalTheory_finite_twelve_torsion
import Theorems.Thm_GlobalTheory_hasRationalTorsion_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ∃ M : IntermediateField K L, FiniteDimensional K M ∧
      HasRationalTorsion (W.baseChange M) L 12 := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let c : (W.baseChange L).toAffine.Point → Set L
    | .zero => ∅
    | .some x y _ => {x, y}
  have hfin : (⋃ P ∈ {P : (W.baseChange L).toAffine.Point | 12 • P = 0}, c P).Finite := by
    refine finite_twelve_torsion.biUnion ?_
    rintro (_ | _) - <;> simp [c]
  have := hfin.to_subtype
  refine ⟨IntermediateField.adjoin K _, IntermediateField.finiteDimensional_adjoin
    (S := ⋃ P ∈ {P : (W.baseChange L).toAffine.Point | 12 • P = 0}, c P)
    fun x _ => Algebra.IsIntegral.isIntegral x, ?_⟩
  rw [hasRationalTorsion_iff]
  intro x y h h0
  exact ⟨⟨⟨x, IntermediateField.subset_adjoin _ _ (Set.mem_biUnion (x := .some x y h) h0
      (by simp [c]))⟩, rfl⟩,
    ⟨⟨y, IntermediateField.subset_adjoin _ _ (Set.mem_biUnion (x := .some x y h) h0
      (by simp [c]))⟩, rfl⟩⟩
end GlobalTheory

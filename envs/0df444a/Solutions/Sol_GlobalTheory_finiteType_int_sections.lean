-- Prove2me | solution 1 for GlobalTheory.finiteType_int_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:53:53.817111+00:00
-- url     : https://prove2.me/submissions/0f3fe0b8-a0b4-4962-af75-7f9d16d5aec6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace GlobalTheory
theorem _root_.solution {Z : Scheme.{0}} (π : Z ⟶ Spec (.of ℤ)) [LocallyOfFiniteType π]
    {V : Z.Opens} (hV : IsAffineOpen V) : Algebra.FiniteType ℤ Γ(Z, V) := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType π inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have h' := h.comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of ℤ)).inv.hom
    (Scheme.ΓSpecIso (.of ℤ)).symm.commRingCatIsoToRingEquiv.surjective)
  rw [← RingHom.finiteType_algebraMap]
  convert h' using 1
  exact RingHom.ext_int _ _
end GlobalTheory

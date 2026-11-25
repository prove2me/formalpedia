-- Prove2me | solution 1 for GlobalTheory.apply_genericPoint_eq_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:49.149632+00:00
-- url     : https://prove2.me/submissions/ece33fcd-ab8a-48b2-95e2-4e6e680e574d

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
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory
theorem _root_.solution {R : CommRingCat.{0}} [IsDomain R] [CharZero R]
    (g : Spec R ⟶ Spec (.of ℤ)) : g (genericPoint (Spec R)) = genericPoint (Spec (.of ℤ)) := by
  have : g = Spec.map (CommRingCat.ofHom (Int.castRingHom R)) := specZIsTerminal.hom_ext _ _
  rw [this, genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  refine PrimeSpectrum.ext ?_
  exact Ideal.comap_bot_of_injective (Int.castRingHom R) Int.cast_injective
end GlobalTheory

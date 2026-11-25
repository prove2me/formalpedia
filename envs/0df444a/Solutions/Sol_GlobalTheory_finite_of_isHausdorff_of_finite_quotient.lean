-- Prove2me | solution 1 for GlobalTheory.finite_of_isHausdorff_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:59:55.377286+00:00
-- url     : https://prove2.me/submissions/c4633b6b-14d2-4baa-83fc-83131278f208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isPrecomplete_finite_module


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
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [IsHausdorff I M]
    [Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))] : Module.Finite R M := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (M ⧸ (I • ⊤ : Submodule R M))
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (I • ⊤ : Submodule R M).mkQ g
    (Submodule.mkQ_surjective _)
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I (Fin n → R)
  exact Module.Finite.of_surjective f
    (surjective_of_mkQ_comp_surjective (I := I) (by rw [hf]; exact hg))
end GlobalTheory

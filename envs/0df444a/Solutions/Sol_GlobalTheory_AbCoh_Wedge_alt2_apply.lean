-- Prove2me | solution 1 for GlobalTheory.AbCoh.Wedge.alt2_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:11.213385+00:00
-- url     : https://prove2.me/submissions/e31968a0-b595-46a5-b6ee-9dccf08f6b3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WedgePropertyFromFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.Wedge
namespace GlobalTheory.AbCoh.Wedge
theorem _root_.solution {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) (v : Fin 2 → M) : alt2 f hf v = f (v 0) (v 1) := rfl
end GlobalTheory.AbCoh.Wedge

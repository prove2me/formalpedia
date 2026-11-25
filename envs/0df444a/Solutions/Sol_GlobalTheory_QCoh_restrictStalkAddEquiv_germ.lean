-- Prove2me | solution 1 for GlobalTheory.QCoh.restrictStalkAddEquiv_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:06:57.599802+00:00
-- url     : https://prove2.me/submissions/d704e080-5efc-4968-8a33-7915546d2414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y)
    {W : Y.Opens} (hy : y ∈ W) (s : Γ(F.restrict g, W)) :
    restrictStalkAddEquiv F g y ((F.restrict g).presheaf.germ W y hy s) =
      F.presheaf.germ (g ''ᵁ W) (g y) ⟨y, hy, rfl⟩ ((F.restrictAppIso g W).hom s) :=
  congr($(Scheme.Modules.germ_restrictStalkNatIso_hom_app g y F hy) s)
end GlobalTheory.QCoh

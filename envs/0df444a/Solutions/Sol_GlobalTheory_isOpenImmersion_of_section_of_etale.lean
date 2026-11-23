-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_of_section_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:48.778706+00:00
-- url     : https://prove2.me/submissions/33c64096-019e-4d2b-a00b-51534bac88a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s := by
  have : Etale (s ≫ f) := by rw [hs]; infer_instance
  have : Etale s := Etale.of_comp s f
  have : Mono s := (SplitMono.mk f hs).mono
  exact IsOpenImmersion.of_flat_of_mono s
end GlobalTheory

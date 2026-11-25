-- Prove2me | solution 1 for GlobalTheory.GroupConn.connectedSpace_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:45.770706+00:00
-- url     : https://prove2.me/submissions/5453639f-8e53-4619-86dd-cda918130708

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GroupConn
namespace GlobalTheory.GroupConn
theorem _root_.solution {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyConnected f]
    [ConnectedSpace S] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : ConnectedSpace X := by

  have hsec : ∀ y : S, f (s y) = y := fun y => by
    simpa using congrArg (fun g : S ⟶ S => g y) hs
  obtain ⟨y₀⟩ := (inferInstance : Nonempty S)
  refine connectedSpace_iff_connectedComponent.mpr ⟨s y₀, Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  have hbase : s (f x) ∈ connectedComponent (s y₀) :=
    (isPreconnected_range s.continuous).subset_connectedComponent ⟨y₀, rfl⟩ ⟨f x, rfl⟩
  have hfib : x ∈ connectedComponent (s (f x)) :=
    (f.isConnected_preimage_singleton (f x)).isPreconnected.subset_connectedComponent
      (show f (s (f x)) = f x from hsec (f x)) rfl
  rw [connectedComponent_eq hbase]
  exact hfib
end GlobalTheory.GroupConn

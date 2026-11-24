-- Prove2me | solution 1 for GlobalTheory.ZM.sec_eq_of_openImm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:19:14.418084+00:00
-- url     : https://prove2.me/submissions/c7c9974b-088c-4918-9181-67e54c01feed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRing
import Theorems.Thm_GlobalTheory_ZM_stalkMap_germ_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {Y : Scheme.{0}} (W : Y.Opens) (s t : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (_ : IsOpenImmersion f) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ (f.appLE W W' h).hom s = (f.appLE W W' h).hom t) : s = t := by
  apply TopCat.Presheaf.section_ext Y.sheaf W s t
  intro p hp
  obtain ⟨Z, f, _, z, W', h, hz, rfl, e⟩ := H p hp
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (f.stalkMap z))
  have e1 := stalkMap_germ_appLE f W W' h z hz s
  have e2 := stalkMap_germ_appLE f W W' h z hz t
  rw [e] at e1
  exact e1.trans e2.symm
end GlobalTheory.ZM

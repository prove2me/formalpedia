-- Prove2me | solution 1 for GlobalTheory.LinDescent.hom_ext_of_gs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:04.829867+00:00
-- url     : https://prove2.me/submissions/eec540ce-1f14-4a53-85e2-e325dffa4468

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_gs_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X}
variable {C : Type} {t : C → (X ⟶ X)}
variable [Group C] [Finite C]
namespace GlobalTheory.LinDescent
theorem _root_.solution [IsAffine Z] {W : X.Opens} (hW : IsAffineOpen W) {r r' : Z ⟶ X}
    (h : ∀ z, r z ∈ W) (h' : ∀ z, r' z ∈ W) (e : ∀ z f, gs r z W f = gs r' z W f) : r = r' := by
  have l : ⊤ ≤ r ⁻¹ᵁ W := fun z _ => h z
  have l' : ⊤ ≤ r' ⁻¹ᵁ W := fun z _ => h' z
  have e' : r.appLE W ⊤ l = r'.appLE W ⊤ l' := by
    ext f
    refine fn_ext fun z hz => ?_
    rw [gs_appLE (𝟙 Z) r z _ _ _ hz, gs_appLE (𝟙 Z) r' z _ _ _ hz, Category.id_comp,
      Category.id_comp, e]
  have : Epi (isAffineOpen_top Z).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi (isAffineOpen_top Z).fromSpec,
    ← hW.SpecMap_appLE_fromSpec r (isAffineOpen_top Z) l, e',
    hW.SpecMap_appLE_fromSpec r' (isAffineOpen_top Z)]
end GlobalTheory.LinDescent

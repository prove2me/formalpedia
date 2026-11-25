-- Prove2me | solution 1 for GlobalTheory.GenScheme.compat_pb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:04.350466+00:00
-- url     : https://prove2.me/submissions/1be7d11f-90c8-40aa-98dd-aded85b24321

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_res_pb
import Theorems.Thm_GlobalTheory_GenScheme_pb_res
import Theorems.Thm_GlobalTheory_GenScheme_pb_pb
import Theorems.Thm_GlobalTheory_GenScheme_pullU_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
open GlobalTheory.GenScheme
variable {B Z : Scheme.{0}} (L : LB B) (b : Z ⟶ B)
variable (j : L.ι) (hj : ⊤ ≤ b ⁻¹ᵁ L.U j)
variable {L}
namespace GlobalTheory.GenScheme
theorem _root_.solution {G : Scheme.{0}} {q : G ⟶ B} {u : ∀ i : L.ι, Γ(G, q ⁻¹ᵁ L.U i)ˣ}
    (hu : Compat L q u) (g : Z ⟶ G) (hg : g ≫ q = b) :
    Compat L b fun i => pb g (q ⁻¹ᵁ L.U i) (b ⁻¹ᵁ L.U i) (by rw [← hg]; exact le_rfl) (u i) := by
  subst hg
  intro i i'
  have h := congrArg (pb g (q ⁻¹ᵁ (L.U i ⊓ L.U i')) ((g ≫ q) ⁻¹ᵁ (L.U i ⊓ L.U i')) le_rfl) (hu i i')
  rw [map_mul, pb_res, pb_res, pullU_eq, pb_pb] at h
  rw [res_pb, res_pb, pullU_eq]
  exact h
end GlobalTheory.GenScheme

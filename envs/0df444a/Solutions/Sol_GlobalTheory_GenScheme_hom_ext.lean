-- Prove2me | solution 1 for GlobalTheory.GenScheme.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:42:28.104807+00:00
-- url     : https://prove2.me/submissions/d4b5e24d-3609-4413-96e9-ee426e3c48d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_res_pb
import Theorems.Thm_GlobalTheory_GenScheme_eq_extend
import Theorems.Thm_GlobalTheory_GenScheme_compat_pb

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
variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}
namespace GlobalTheory.GenScheme
theorem _root_.solution (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) {Z : Scheme.{0}}
    (j : ∀ k, (N k).ι) (g g' : Z ⟶ G) (hg : g' ≫ q = g ≫ q)
    (hj : ∀ k, ⊤ ≤ g ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)) (hj' : ∀ k, ⊤ ≤ g' ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k))
    (h : ∀ k, pb g' (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj' k) (u k (j k)) =
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj k) (u k (j k))) : g' = g := by
  have c := fun k => compat_pb (g ≫ q) (hu k) g rfl
  have c' := fun k => compat_pb (g ≫ q) (hu k) g' hg
  refine (hU Z (g ≫ q) _ c).unique ⟨hg, fun k i => ?_⟩ ⟨rfl, fun k i => rfl⟩
  have e := eq_extend (g ≫ q) (j k) (hj k) (c k) i
  have e' := eq_extend (g ≫ q) (j k) (hj k) (c' k) i
  simp only [res_pb] at e e'
  rw [h k, ← e] at e'
  exact congrArg Units.val e'
end GlobalTheory.GenScheme

-- Prove2me | solution 1 for GlobalTheory.GenScheme.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:44.125737+00:00
-- url     : https://prove2.me/submissions/4820909b-d729-4032-82a8-db109112dac8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_res_pb
import Theorems.Thm_GlobalTheory_GenScheme_compat_extend
import Theorems.Thm_GlobalTheory_GenScheme_res_extend_self

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
theorem _root_.solution (hN : ∀ k, (N k).IsLB) (hU : Univ N q u) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (t : κ → Γ(Z, ⊤)ˣ) :
    ∃ (g : Z ⟶ G) (hg : g ≫ q = b), ∀ k,
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (by subst hg; exact hj k) (u k (j k)) = t k := by
  obtain ⟨g, ⟨hg, h⟩, -⟩ := hU Z b (fun k => extend (N k) b (j k) (hj k) (t k))
    fun k => compat_extend b (j k) (hj k) (hN k) (t k)
  refine ⟨g, hg, fun k => ?_⟩
  have e : pb g (q ⁻¹ᵁ (N k).U (j k)) (b ⁻¹ᵁ (N k).U (j k)) (by rw [← hg]; exact le_rfl) (u k (j k)) =
      extend (N k) b (j k) (hj k) (t k) (j k) := Units.ext (h k (j k))
  rw [← res_extend_self b (j k) (hj k) (hN k) (t k), ← e, res_pb]
end GlobalTheory.GenScheme

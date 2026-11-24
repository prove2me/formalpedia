-- Prove2me | solution 1 for GlobalTheory.SS.FrobField.good_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:10.703162+00:00
-- url     : https://prove2.me/submissions/cd561b72-5c90-46e5-aa6f-a3149d59f85f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
import Theorems.Thm_GlobalTheory_SS_FrobField_Good_sup
import Theorems.Thm_GlobalTheory_SS_FrobField_good_bot
import Theorems.Thm_GlobalTheory_SS_FrobField_Good_basic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField
namespace GlobalTheory.SS.FrobField
theorem _root_.solution {X : Scheme.{0}} {F : End X} {q : ℕ} (hq : 0 < q)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ ∀ f, Good F q U f)
    (U : X.Opens) (hU : IsCompact (U : Set X)) (f : Γ(X, U)) : Good F q U f := by
  have key : ∃ V : Set X, (U : Set X) ⊆ V ∧ ∃ W : X.Opens, (W : Set X) = V ∧ W ≤ U ∧ ∀ f, Good F q W f := by
    refine hU.induction_on (p := fun s => ∃ V : Set X, s ⊆ V ∧ ∃ W : X.Opens, (W : Set X) = V ∧ W ≤ U ∧
      ∀ f, Good F q W f) ⟨∅, le_rfl, ⊥, rfl, bot_le, good_bot F q⟩ ?_ ?_ ?_
    · rintro s t hst ⟨V, hV, h⟩
      exact ⟨V, hst.trans hV, h⟩
    · rintro s t ⟨_, hs, V, rfl, hV, gV⟩ ⟨_, ht, W, rfl, hW, gW⟩
      exact ⟨_, Set.union_subset_union hs ht, V ⊔ W, rfl, sup_le hV hW,
        fun f => Good.sup f le_sup_left le_sup_right rfl (gV _) (gW _)⟩
    · intro x hx
      obtain ⟨V, hxV, hV, gV⟩ := H x
      obtain ⟨g, hg, hxg⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
      exact ⟨_, mem_nhdsWithin_of_mem_nhds ((X.basicOpen g).isOpen.mem_nhds hxg), _, le_rfl,
        X.basicOpen g, rfl, hg, Good.basic hq hV gV g⟩
  obtain ⟨_, h1, W, rfl, h2, g⟩ := key
  obtain rfl : U = W := le_antisymm h1 h2
  exact g f
end GlobalTheory.SS.FrobField

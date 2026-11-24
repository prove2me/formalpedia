-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:40.168854+00:00
-- url     : https://prove2.me/submissions/be64d3f7-c36a-4e0b-8581-0442841e86cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian
import Theorems.Thm_GlobalTheory_SS_OrdProd_der_one
import Theorems.Thm_GlobalTheory_SS_OrdProd_InSpan_closure
import Theorems.Thm_GlobalTheory_SS_OrdProd_appLE_cstK
import Theorems.Thm_GlobalTheory_SS_StalkGlue_exists_vf
import Theorems.Thm_GlobalTheory_SS_exists_eq_div_of_isPullback
import Theorems.Thm_GlobalTheory_SS_exists_stalk_derivation_of_isPullback


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdProd
variable {K : Type} [Field K]
namespace GlobalTheory.SS.OrdProd
theorem _root_.solution {P X Y : Over (Sp K)} (p : P ⟶ X) (q : P ⟶ Y)
    (H : IsPullback p.left q.left X.hom Y.hom) (D : VF X) :
    ∃ E : VF P, Lifts p E D ∧ Lifts q E (VF.zero Y) := by
  choose δ hδ hp hq using _root_.GlobalTheory.SS.exists_stalk_derivation_of_isPullback K P X Y p.left q.left H D
  obtain ⟨E, hE⟩ := _root_.GlobalTheory.SS.StalkGlue.exists_vf K P δ hδ
    (fun U x hx c => by
      rw [← appLE_cstK q ⊤ U le_top c]; exact hq x ⊤ U le_top hx _)
    (fun U s x hx => by
      obtain ⟨V, V', W, h₁, h₂, -, -, hW, hxW, hg⟩ :=
        _root_.GlobalTheory.SS.exists_eq_div_of_isPullback _ _ _ _ p.left q.left _ _ H x ⊤ ⊤ U trivial trivial hx
      have key : ∀ a ∈ Subring.closure (Set.range (p.left.appLE V W h₁).hom ∪
          Set.range (q.left.appLE V' W h₂).hom), ∃ a' : Γ(P.left, W), ∀ (y : P.left) (hy : y ∈ W),
          δ y ((P.left.presheaf.germ W y hy).hom a) = (P.left.presheaf.germ W y hy).hom a' := by
        intro a ha
        induction ha using Subring.closure_induction with
        | mem a ha =>
          rcases ha with ⟨u, rfl⟩ | ⟨u, rfl⟩
          · exact ⟨_, fun y hy => hp y V W h₁ hy u⟩
          · exact ⟨0, fun y hy => by rw [hq y V' W h₂ hy u, map_zero]⟩
        | zero => exact ⟨0, fun y hy => by simp⟩
        | one => exact ⟨0, fun y hy => by simp [der_one (hδ y)]⟩
        | add a b _ _ ha hb =>
          obtain ⟨r, hr⟩ := ha
          obtain ⟨r', hr'⟩ := hb
          exact ⟨r + r', fun y hy => by simp only [map_add, hr, hr']⟩
        | neg a _ ha =>
          obtain ⟨r, hr⟩ := ha
          exact ⟨-r, fun y hy => by simp only [map_neg, hr]⟩
        | mul a b _ _ ha hb =>
          obtain ⟨r, hr⟩ := ha
          obtain ⟨r', hr'⟩ := hb
          exact ⟨a * r' + b * r, fun y hy => by simp only [map_mul, map_add, hδ, hr, hr']⟩
      obtain ⟨a, ha, b, hb, hu, e⟩ := hg ((P.left.presheaf.map (homOfLE hW).op).hom s)
      obtain ⟨a', ha'⟩ := key a ha
      obtain ⟨b', hb'⟩ := key b hb
      obtain ⟨c, hc⟩ := hu.exists_left_inv
      refine ⟨W, hW, c * (b' - (P.left.presheaf.map (homOfLE hW).op).hom s * a'), hxW, fun y hy => ?_⟩
      have h1 := hb' y hy
      rw [← e, map_mul, hδ, ha'] at h1
      have h2 := congrArg (P.left.presheaf.germ W y hy).hom hc
      have h3 : (P.left.presheaf.germ W y hy).hom ((P.left.presheaf.map (homOfLE hW).op).hom s) =
          (P.left.presheaf.germ U y (hW hy)).hom s := P.left.presheaf.germ_res_apply (homOfLE hW) y hy s
      rw [map_mul, map_one] at h2
      rw [map_mul, map_sub, map_mul, ← h1, h3]
      linear_combination (-(δ y ((P.left.presheaf.germ U y (hW hy)).hom s))) * h2)
  refine ⟨E, fun V W h u => ?_, fun V W h u => ?_⟩
  · exact TopCat.Presheaf.section_ext P.left.sheaf W _ _ fun x hx => (hE W _ x hx).trans (hp x V W h hx u)
  · refine TopCat.Presheaf.section_ext P.left.sheaf W _ _ fun x hx => ((hE W _ x hx).trans (hq x V W h hx u)).trans ?_
    exact ((congrArg (P.left.presheaf.germ W x hx).hom (map_zero (q.left.appLE V W h).hom)).trans (map_zero _)).symm
end GlobalTheory.SS.OrdProd

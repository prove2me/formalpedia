-- Prove2me | solution 1 for GlobalTheory.SS.frobG_pow_and_closed_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:08.382659+00:00
-- url     : https://prove2.me/submissions/3c8ca965-f4f4-49f2-a0d1-20a95c3f325b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGPowAndClosedSubgroup
import Theorems.Thm_GlobalTheory_SS_FrobSub_Raises_mul
import Theorems.Thm_GlobalTheory_SS_FrobSub_Raises_pull
import Theorems.Thm_GlobalTheory_SS_FrobSub_Raises_of_cover
import Theorems.Thm_GlobalTheory_SS_FrobSub_pow_comm_hom
import Theorems.Thm_GlobalTheory_SS_FrobSub_isMonHom_pow

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
open GlobalTheory.SS.FrobSub
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (F : End G) (q : ℕ), FrobG G F q → (∀ m, 1 ≤ m → FrobG G (F ^ m) (q ^ m)) ∧ ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (F' : End N), IsMonHom ν → IsClosedImmersion ν.left → IsMonHom (show N ⟶ N from F') → (show N ⟶ N from F') ≫ ν = ν ≫ (show G ⟶ G from F) → FrobG N F' q := by
  intro k _ G _ _ F q hF
  refine ⟨fun m hm => ⟨isMonHom_pow G F hF.1 m, fun U hU f => ?_⟩, fun N _ ν F' _ hν hF' hc => ⟨hF', fun U hU f => ?_⟩⟩
  · obtain ⟨n, hn, h⟩ := hF.2 U hU f
    refine ⟨n, hn, ?_⟩
    have := Raises.mul F q n h m hm
    rw [mul_comm, pow_mul, pow_mul] at this
    exact this
  · have key : ∀ x : U, ∃ (W : N.left.Opens) (hW : W ≤ U) (m : ℕ), x.1 ∈ W ∧ 1 ≤ m ∧
        Raises (show N ⟶ N from F' ^ m).left (q ^ m) W ((N.left.presheaf.map (homOfLE hW).op).hom f) := by
      intro x
      obtain ⟨W, hW, hWU⟩ := ν.left.isClosedEmbedding.isInducing.isOpen_iff.1 U.isOpen
      have hx : ν.left x.1 ∈ (⟨W, hW⟩ : G.left.Opens) := by
        show x.1 ∈ ν.left ⁻¹' W
        rw [hWU]; exact x.2
      obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
      have hle : ν.left ⁻¹ᵁ V ≤ U := fun y hy => by
        have : y ∈ ν.left ⁻¹' W := hVW hy
        rwa [hWU] at this
      obtain ⟨g, hg⟩ := ν.left.app_surjective V hV ((N.left.presheaf.map (homOfLE hle).op).hom f)
      obtain ⟨m, hm, h⟩ := hF.2 V hV g
      refine ⟨_, hle, m, hxV, hm, ?_⟩
      rw [← hg]
      refine Raises.pull ν.left ?_ h
      exact congrArg (fun t => t.left) (pow_comm_hom ν F F' hc m)
    choose W hW m hxW hm hR using key
    obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover (fun x => (W x : Set N.left)) (fun x => (W x).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩)
    have hpos : 1 ≤ ∏ x ∈ t, m x := Finset.one_le_prod' fun x _ => hm x
    refine ⟨∏ x ∈ t, m x, hpos, ?_⟩
    refine Raises.of_cover (fun x : t => W x.1) (fun x => hW x.1) (fun y hy => ?_) fun x => ?_
    · obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (ht hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy'⟩
    · obtain ⟨n, hn⟩ := Finset.dvd_prod_of_mem m x.2
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => by rw [hn, h0] at hpos; simp at hpos
      rw [hn]
      exact Raises.mul F' q _ (hR x.1) n hn1
end GlobalTheory.SS

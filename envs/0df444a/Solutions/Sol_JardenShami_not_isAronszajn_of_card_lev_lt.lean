-- Prove2me | solution 1 for JardenShami.not_isAronszajn_of_card_lev_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:44.175104+00:00
-- url     : https://prove2.me/submissions/9717fd0c-038a-4b05-a20c-c868b8f81637

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_ht_subtype_of_downward
import Theorems.Thm_JardenShami_exists_le_ht_eq
import Theorems.Thm_JardenShami_exists_wellPruned_subtree_downward
import Theorems.Thm_JardenShami_le_of_le_of_le_of_ht_le
import Theorems.Thm_JardenShami_exists_nonsplitting
import Theorems.Thm_JardenShami_exists_isCofinalBranch_of_isChain
import Theorems.Thm_JardenShami_Kappa_card_eq_of_forall_exists_gt
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Tree_eq_of_le_of_le_of_ht_eq
import Theorems.Thm_JardenShami_Tree_ht_le_ht_of_le
import Theorems.Thm_JardenShami_Tree_ht_lt_height
attribute [local simp] JardenShami.Kappa.coe_mk



set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ lam : Cardinal.{w})
    (hκ : κ.IsRegular) (hlam : lam < κ) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ¬ IsAronszajn κ T := by
  rintro ⟨-, hno⟩
  obtain ⟨S, hdown, hS, hwp⟩ := exists_wellPruned_subtree_downward κ hκ T hT
  have hht : ∀ x : S, ht x = ht (x : T) := ht_subtype_of_downward hdown
  have hlevS : ∀ α : Ordinal.{w}, #(Lev S α) < lam := fun α =>
    (Cardinal.mk_le_of_injective (f := fun x : Lev S α => (⟨x.1.1, (hht x.1).symm.trans x.2⟩ :
      Lev T α)) (fun a b h => Subtype.ext (Subtype.ext
        (congrArg (fun z : Lev T α => (z : T)) h)))).trans_lt (hlev α)
  obtain ⟨a, ha⟩ := exists_nonsplitting hκ hlam hS hwp hlevS
  -- the nodes of `S` above `a` form a chain
  have ha' : ∀ b c : S, a ≤ b → a ≤ c → ht b = ht c → b = c := by
    intro b c hb hc hbc
    rcases hb.lt_or_eq with hb | rfl
    · rcases hc.lt_or_eq with hc | rfl
      · exact ha b c hb hc hbc
      · exact (eq_of_le_of_le_of_ht_eq hb.le le_rfl hbc.symm).symm
    · exact eq_of_le_of_le_of_ht_eq hc le_rfl hbc
  let C : Set T := (fun x : S => (x : T)) '' {x : S | a ≤ x}
  have hchain : IsChain (· ≤ ·) C := by
    have key : ∀ x y : S, a ≤ x → a ≤ y → ht x ≤ ht y → x ≤ y := by
      intro x y hx hy hxy
      obtain ⟨y', hy'y, hy'⟩ := exists_le_ht_eq hxy
      have hay' : a ≤ y' :=
        le_of_le_of_le_of_ht_le hy hy'y (by rw [hy']; exact ht_le_ht_of_le hx)
      exact (ha' x y' hx hay' hy'.symm) ▸ hy'y
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ -
    rcases le_total (ht x) (ht y) with h | h
    · exact Or.inl (key x y hx hy h)
    · exact Or.inr (key y x hy hx h)
  -- it has size `κ`: its heights are unbounded in `κ`
  have hCκ : κ ≤ #C := by
    have hunb : ∀ β : Kappa κ, ∃ y ∈ Set.range (fun x : C => Kappa.mk (ht (x : T))
        (hT.1 ▸ ht_lt_height (x : T))), β < y := by
      intro β
      have hγ : max (ht a + 1) ((β : Ordinal.{w}) + 1) < κ.ord := by
        have hlim := Cardinal.isSuccLimit_ord hκ.aleph0_le
        refine max_lt (hlim.add_one_lt ?_) (hlim.add_one_lt (Kappa.coe_lt_ord β))
        rw [← hS.1]
        exact ht_lt_height a
      obtain ⟨y, hy, hay⟩ := hwp.2 a _ (lt_of_lt_of_le (Order.lt_add_one_iff.2 le_rfl)
        (le_max_left _ _)) (by rw [hS.1]; exact hγ)
      refine ⟨_, ⟨⟨y, y, hay.le, rfl⟩, rfl⟩, ?_⟩
      rw [← Kappa.coe_lt_coe, Kappa.coe_mk, ← hht, show ht y = _ from hy]
      exact lt_of_lt_of_le (Order.lt_add_one_iff.2 le_rfl) (le_max_right _ _)
    have := Kappa.card_eq_of_forall_exists_gt hκ hunb
    rw [← this]
    exact Cardinal.mk_range_le
  exact hno (exists_isCofinalBranch_of_isChain hT hchain hCκ)
end JardenShami

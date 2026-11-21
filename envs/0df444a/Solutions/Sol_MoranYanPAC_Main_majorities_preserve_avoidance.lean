-- Prove2me | solution 1 for MoranYanPAC.Main.majorities_preserve_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:47:40.311189+00:00
-- url     : https://prove2.me/submissions/f8bb85ab-c76b-4343-b54f-970da2d5a1da

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_MoranYanPAC_Main_GoodFamily
import Definitions.Def_MoranYanPAC_Main_Candidates
import Definitions.Def_PrivLittlestone_witnessSpace

section
set_option autoImplicit false

open MeasureTheory

namespace MoranYanPAC.Main

theorem chk_majorities_preserve_avoidance {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (G : Finset (X → Bool)) (hgood : Good d G)
    (hG : ∀ g ∈ G, g ∈ PrivLittlestone.localUniverse H d)
    (h : X → Bool) (hh : h ∈ PrivLittlestone.localUniverse H d)
    (havoid : ∀ g ∈ G, g ∉ PrivLittlestone.witnessSpace H d Aw h) :
    majority G ∉ PrivLittlestone.witnessSpace H d Aw h := by
  classical
  intro hm
  have hmW := hm.2
  have hcard : (Aw h).card ≤ d := (hAw.1 h hh).1.trans (Nat.sub_le _ _)
  have hcov : G ⊆ (Aw h).biUnion (fun x => G.filter (fun g => g x ≠ majority G x)) := by
    intro g hg
    by_contra hn
    apply havoid g hg
    refine ⟨hG g hg, fun x hx => ?_⟩
    by_contra hne
    apply hn
    refine Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨hg, ?_⟩⟩
    rw [hmW x hx]; exact hne
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_biUnion_le (s := Aw h) (t := fun x => G.filter (fun g => g x ≠ majority G x))
  have hpos : 0 < G.card := Finset.card_pos.2 hgood.1
  have h3 : ∀ x ∈ Aw h, 2 * (d + 1) * (G.filter (fun g => g x ≠ majority G x)).card < G.card :=
    fun x _ => hgood.2 x
  have h4 : 2 * (d + 1) * G.card ≤ ∑ x ∈ Aw h, 2 * (d + 1) * (G.filter (fun g => g x ≠ majority G x)).card := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ (h1.trans h2)
  rcases (Aw h).eq_empty_or_nonempty with he | hne
  · have h0 : ((Aw h).biUnion (fun x => G.filter (fun g => g x ≠ majority G x))).card = 0 := by simp [he]
    omega
  · have h5 := Finset.sum_lt_sum_of_nonempty hne h3
    simp only [Finset.sum_const, smul_eq_mul] at h5
    have : (Aw h).card * G.card ≤ d * G.card := Nat.mul_le_mul_right _ hcard
    nlinarith

end MoranYanPAC.Main
end

theorem solution : type_of% @MoranYanPAC.Main.chk_majorities_preserve_avoidance := @MoranYanPAC.Main.chk_majorities_preserve_avoidance

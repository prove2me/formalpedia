-- Prove2me | solution 1 for GlobalTheory.UnramifiedHensel.subset_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:36:13.296595+00:00
-- url     : https://prove2.me/submissions/32b4c005-192b-4c85-a693-dd4f09f3fbba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient
import Theorems.Thm_GlobalTheory_UnramifiedHensel_exists_relation_gradient
import Theorems.Thm_GlobalTheory_UnramifiedHensel_mem_of_gradient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel
namespace GlobalTheory.UnramifiedHensel
theorem _root_.solution (K : Type) [NormedField K] [IsUltrametricDist K] (W : Subring K)
    (hW : IsClosed (W : Set K)) (hc : ∀ w ∈ W, ‖w‖ ≤ 1)
    (hres : ∀ x : K, ‖x‖ ≤ 1 → ∃ w ∈ W, ‖x - w‖ < 1) (s : Set K) (hs : s.Finite)
    (hs1 : ∀ x ∈ s, ‖x‖ ≤ 1)
    (h : ∀ (k : Type) [Field k] (φ : Subring.closure ((W : Set K) ∪ s) →+* DualNumber k),
      (∀ a : Subring.closure ((W : Set K) ∪ s), ‖(a : K)‖ = 1 → (φ a).fst ≠ 0) →
      (∀ a : Subring.closure ((W : Set K) ∪ s), (a : K) ∈ W → (φ a).snd = 0) →
      ∀ a : Subring.closure ((W : Set K) ∪ s), (a : K) ∈ s → (φ a).snd = 0) :
    s ⊆ (W : Set K) := by
  classical
  haveI : Fintype s := hs.fintype
  let A := Subring.closure ((W : Set K) ∪ s)
  let O := (NormedField.valuation (K := K)).valuationSubring
  have hO : ∀ z : K, z ∈ O ↔ ‖z‖ ≤ 1 := by
    intro z
    simp only [O, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  have hm : ∀ z : O, IsLocalRing.residue O z = 0 ↔ ‖(z : K)‖ < 1 := by
    intro z
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact Iff.rfl
  have hAO : A ≤ O.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro z (hz | hz)
    · exact (hO z).2 (hc z hz)
    · exact (hO z).2 (hs1 z hz)
  have hWA : W ≤ A := fun z hz => Subring.subset_closure (Or.inl hz)
  let x : s → A := fun i => ⟨i, Subring.subset_closure (Or.inr i.2)⟩
  let ev : MvPolynomial s W →+* A := eval₂Hom (Subring.inclusion hWA) x
  have hevK : ∀ F, ((ev F : A) : K) = eval₂ W.subtype (fun i : s => (i : K)) F := by
    intro F
    have := eval₂_comp_left A.subtype (Subring.inclusion hWA) x F
    exact this
  have hev : Function.Surjective ev := by
    rintro ⟨a, ha⟩
    have : a ∈ (A.subtype.comp ev).range := by
      refine (Subring.closure_le (t := (A.subtype.comp ev).range)).2 ?_ ha
      rintro z (hz | hz)
      · exact ⟨C ⟨z, hz⟩, by simp [ev]⟩
      · exact ⟨X ⟨z, hz⟩, by simp [ev, x]⟩
    obtain ⟨F, hF⟩ := this
    exact ⟨F, Subtype.ext hF⟩
  let inc : A →+* O := Subring.inclusion hAO
  let red : A →+* IsLocalRing.ResidueField O := (IsLocalRing.residue O).comp inc
  have hred0 : ∀ a : A, red a = 0 ↔ ‖(a : K)‖ < 1 := fun a => hm (inc a)
  have hred : ∀ c, ∃ w : W, red (ev (C w)) = c := by
    intro c
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective c
    obtain ⟨w, hw, hzw⟩ := hres z ((hO _).1 z.2)
    refine ⟨⟨w, hw⟩, ?_⟩
    symm
    rw [← sub_eq_zero]
    have : IsLocalRing.residue O (z - inc (ev (C ⟨w, hw⟩))) = 0 := by
      rw [hm]
      have : ((inc (ev (C ⟨w, hw⟩)) : O) : K) = w := by
        change ((ev (C ⟨w, hw⟩) : A) : K) = w
        rw [hevK]; simp
      push_cast
      rwa [this]
    rwa [map_sub] at this
  have hG := exists_relation_gradient ev hev red hred (fun φ h1 h2 i => by
    refine h _ φ (fun a ha => ?_) (fun a ha => ?_) _ ?_
    · rw [h1, Ne, hred0, ha]; exact lt_irrefl _
    · have : a = ev (C ⟨a, ha⟩) := Subtype.ext (by rw [hevK]; simp)
      rw [this]; exact h2 _
    · rw [hevK]; simp)
  choose G hG0 hG1 using hG
  intro z hz
  refine mem_of_gradient W hW hc (fun i : s => (i : K)) (fun i => hs1 i i.2)
    (fun i => hres i (hs1 i i.2)) G (fun i => ?_) (fun i j => ?_) ⟨z, hz⟩
  · rw [← hevK, hG0]; rfl
  · have : red ((if j = i then 1 else 0) - ev (pderiv j (G i))) = 0 := by
      rw [map_sub, hG1]; split_ifs <;> simp
    rw [hred0] at this
    rw [← hevK]
    convert this using 2
    split_ifs <;> simp
end GlobalTheory.UnramifiedHensel

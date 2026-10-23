-- Prove2me | solution 1 for JohnsonApprox1974.thm5_nodeCover_regular_faithful
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:57:34.310835+00:00
-- url     : https://prove2.me/submissions/6b5110d9-2af8-4abb-9dce-b32036c4d071

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1

open JohnsonApprox.SetCover

section JO86

variable {ι α : Type} [Fintype ι] [DecidableEq α]

/-- number of indices whose current SET has exactly one element -/
def jo86_s1 (σ : State ι α) : ℕ := (Finset.univ.filter (fun i => (σ.SET i).card = 1)).card

def jo86_Inv (S : ι → Finset α) (σ : State ι α) : Prop :=
  ∃ a b : ℕ, (∀ i, σ.SET i = S i ∩ σ.UNCOV) ∧ σ.UNCOV ⊆ ground S ∧
    σ.UNCOV.card + 2 * a + b = (ground S).card ∧ σ.SUB.card ≤ a + b ∧
    jo86_s1 σ + 2 * b ≤ 2 * a

theorem jo86_mem_ground (S : ι → Finset α) {x : α} :
    x ∈ ground S ↔ ∃ i, x ∈ S i := by
  unfold ground; simp

theorem jo86_init (S : ι → Finset α) (h2 : ∀ i, (S i).card = 2) :
    jo86_Inv S (init S) := by
  refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show S i = S i ∩ ground S
    ext x; simp only [Finset.mem_inter, jo86_mem_ground]
    exact ⟨fun h => ⟨h, i, h⟩, fun h => h.1⟩
  · exact subset_rfl
  · simp [init]
  · simp [init]
  · simp only [jo86_s1, init, h2]
    simp

theorem jo86_step (S : ι → Finset α) (h2 : ∀ i, (S i).card = 2)
    (hdeg : ∀ x ∈ ground S, (Finset.univ.filter (fun i => x ∈ S i)).card = 2)
    {σ σ' : State ι α} (hI : jo86_Inv S σ) (hs : Step S σ σ') : jo86_Inv S σ' := by
  classical
  obtain ⟨a, b, hset, hsub, hcard, hSUB, hs1⟩ := hI
  obtain ⟨j, hnh, hmax, rfl⟩ := hs
  set U := σ.UNCOV with hU
  set T := σ.SET j with hT
  have hTU : T ⊆ U := by rw [hT, hset j]; exact Finset.inter_subset_right
  have hTS : T ⊆ S j := by rw [hT, hset j]; exact Finset.inter_subset_left
  have hset' : ∀ i, σ.SET i \ T = S i ∩ (U \ T) := by
    intro i; rw [hset i]; ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hUc : (U \ T).card = U.card - T.card := Finset.card_sdiff_of_subset hTU
  have hTle : T.card ≤ U.card := Finset.card_le_card hTU
  -- T nonempty
  have hUne : U.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; exact hnh
  obtain ⟨x0, hx0⟩ := hUne
  obtain ⟨i0, hi0⟩ := (jo86_mem_ground S).1 (hsub hx0)
  have hm1 : 1 ≤ T.card := by
    have : x0 ∈ σ.SET i0 := by rw [hset i0]; exact Finset.mem_inter.2 ⟨hi0, hx0⟩
    have h1 : 1 ≤ (σ.SET i0).card := Finset.card_pos.2 ⟨x0, this⟩
    exact h1.trans (hmax i0)
  have hm2 : T.card ≤ 2 := (Finset.card_le_card hTS).trans (h2 j).le
  have hSUB' : (insert (S j) σ.SUB).card ≤ σ.SUB.card + 1 := Finset.card_insert_le _ _
  have hPj : ∀ x ∈ T, j ∈ Finset.univ.filter (fun i => x ∈ S i) := by
    intro x hx; simp [hTS hx]
  have hPerase : ∀ x ∈ T, ((Finset.univ.filter (fun i => x ∈ S i)).erase j).card = 1 := by
    intro x hx
    rw [Finset.card_erase_of_mem (hPj x hx), hdeg x (hsub (hTU hx))]
  rcases (show T.card = 1 ∨ T.card = 2 by omega) with hm | hm
  · -- m = 1
    obtain ⟨z, hz⟩ := Finset.card_eq_one.1 hm
    have hzU : z ∈ U := hTU (by rw [hz]; simp)
    have hzg : z ∈ ground S := hsub hzU
    set P := Finset.univ.filter (fun i => z ∈ S i) with hP
    have hle1 : ∀ i, (σ.SET i).card ≤ 1 := fun i => hm ▸ hmax i
    have hPsub : P ⊆ Finset.univ.filter (fun i => (σ.SET i).card = 1) := by
      intro i hi
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have : z ∈ σ.SET i := by rw [hset i]; exact Finset.mem_inter.2 ⟨hi, hzU⟩
      have := Finset.card_pos.2 ⟨z, this⟩
      have := hle1 i; omega
    have hsub' : Finset.univ.filter (fun i => ((σ.SET i) \ T).card = 1) ⊆
        Finset.univ.filter (fun i => (σ.SET i).card = 1) \ P := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, hP] at hi ⊢
      have hle : ((σ.SET i) \ T).card ≤ (σ.SET i).card := Finset.card_le_card Finset.sdiff_subset
      have hc : (σ.SET i).card = 1 := by have := hle1 i; omega
      refine ⟨hc, fun hzi => ?_⟩
      have hzs : z ∈ σ.SET i := by rw [hset i]; exact Finset.mem_inter.2 ⟨hzi, hzU⟩
      have : (σ.SET i \ T).card < (σ.SET i).card :=
        Finset.card_lt_card (Finset.sdiff_ssubset (by rw [hz]; simpa using hzs) (by rw [hz]; simp))
      omega
    have hc1 := Finset.card_le_card hsub'
    rw [Finset.card_sdiff_of_subset hPsub, hdeg z hzg] at hc1
    have hP2 := Finset.card_le_card hPsub
    rw [hdeg z hzg] at hP2
    refine ⟨a, b + 1, ?_, ?_, ?_, ?_, ?_⟩
    · exact hset'
    · exact Finset.sdiff_subset.trans hsub
    · show (U \ T).card + 2 * a + (b + 1) = _; omega
    · show (insert (S j) σ.SUB).card ≤ _; omega
    · show jo86_s1 (⟨_, _, fun i => σ.SET i \ T⟩ : State ι α) + _ ≤ _
      unfold jo86_s1 at hs1 ⊢
      simp only
      omega
  · -- m = 2
    obtain ⟨u, v, huv, huvT⟩ := Finset.card_eq_two.1 hm
    have huT : u ∈ T := by rw [huvT]; simp
    have hvT : v ∈ T := by rw [huvT]; simp
    set A := (Finset.univ.filter (fun i => u ∈ S i)).erase j ∪
      (Finset.univ.filter (fun i => v ∈ S i)).erase j with hA
    have hAc : A.card ≤ 2 := by
      have := Finset.card_union_le ((Finset.univ.filter (fun i => u ∈ S i)).erase j)
        ((Finset.univ.filter (fun i => v ∈ S i)).erase j)
      rw [hPerase u huT, hPerase v hvT] at this; exact this
    have hsub' : Finset.univ.filter (fun i => ((σ.SET i) \ T).card = 1) ⊆
        Finset.univ.filter (fun i => (σ.SET i).card = 1) ∪ A := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases hij : i = j
      · subst hij; rw [← hT, Finset.sdiff_self] at hi; simp at hi
      by_cases hd : Disjoint (σ.SET i) T
      · rw [Finset.sdiff_eq_self_of_disjoint hd] at hi
        exact Finset.mem_union_left _ (by simpa using hi)
      · rw [Finset.not_disjoint_iff] at hd
        obtain ⟨y, hyi, hyT⟩ := hd
        have hyS : y ∈ S i := by rw [hset i] at hyi; exact (Finset.mem_inter.1 hyi).1
        apply Finset.mem_union_right
        rw [huvT] at hyT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
        rcases hyT with rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hij, by simp [hyS]⟩)
        · exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hij, by simp [hyS]⟩)
    have hc1 := (Finset.card_le_card hsub').trans (Finset.card_union_le _ _)
    refine ⟨a + 1, b, ?_, ?_, ?_, ?_, ?_⟩
    · exact hset'
    · exact Finset.sdiff_subset.trans hsub
    · show (U \ T).card + 2 * (a + 1) + b = _; omega
    · show (insert (S j) σ.SUB).card ≤ _; omega
    · show jo86_s1 (⟨_, _, fun i => σ.SET i \ T⟩ : State ι α) + _ ≤ _
      unfold jo86_s1 at hs1 ⊢
      simp only
      omega

theorem jo86_greedy_bound (S : ι → Finset α) (h2 : ∀ i, (S i).card = 2)
    (hdeg : ∀ x ∈ ground S, (Finset.univ.filter (fun i => x ∈ S i)).card = 2)
    (F₁ : Finset (Finset α)) (hF : Choosable S F₁) : 3 * F₁.card ≤ 2 * (ground S).card := by
  obtain ⟨σ, hr, hh, rfl⟩ := hF
  have hI : jo86_Inv S σ := by
    clear hh
    induction hr with
    | refl => exact jo86_init S h2
    | tail _ hs ih => exact jo86_step S h2 hdeg ih hs
  obtain ⟨a, b, -, -, hcard, hSUB, hs1⟩ := hI
  have : σ.UNCOV.card = 0 := by rw [hh]; rfl
  omega

theorem jo86_opt_bound (S : ι → Finset α) (h2 : ∀ i, (S i).card = 2) :
    (ground S).card ≤ 2 * opt S := by
  obtain ⟨F', hF', heq⟩ := Finset.exists_mem_eq_inf' ⟨family S, family_mem_subcovers S⟩
    (f := Finset.card) (s := subcovers S)
  have hopt : opt S = F'.card := heq
  unfold subcovers at hF'
  rw [Finset.mem_filter, Finset.mem_powerset] at hF'
  obtain ⟨hsubF, hcov⟩ := hF'
  rw [hopt, ← hcov]
  have : ∀ s ∈ F', (id s).card ≤ 2 := by
    intro s hs
    have := hsubF hs
    unfold family at this
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 this
    exact (h2 i).le
  have := Finset.card_biUnion_le_card_mul F' id 2 this
  omega

end JO86

set_option maxHeartbeats 1000000 in
theorem solution : ¬ (∀ (k : ℕ) (hk : 1 ≤ k),
    (∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α),
        (∀ i, (S i).card = k) →
        (∀ x ∈ ground S, (Finset.univ.filter (fun i => x ∈ S i)).card = 2) →
        (∀ x ∈ ground S, ∀ y ∈ ground S, (∀ i, x ∈ S i ↔ y ∈ S i) → x = y) →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → F₁.card ≤ 2 * opt S) ∧
      (∃ (ι α : Type) (_ : Fintype ι) (_ : DecidableEq α) (S : ι → Finset α),
        (∀ i, (S i).card = k) ∧
        (∀ x ∈ ground S, (Finset.univ.filter (fun i => x ∈ S i)).card = 2) ∧
        (∀ x ∈ ground S, ∀ y ∈ ground S, (∀ i, x ∈ S i ↔ y ∈ S i) → x = y) ∧
        ∃ F₁ : Finset (Finset α), Choosable S F₁ ∧ 0 < opt S ∧
          (2 * k - 1) * opt S ≤ k * F₁.card)) := by
  intro h
  obtain ⟨ι, α, _, _, S, h2, hdeg, -, F₁, hF, hpos, hle⟩ := (h 2 (by norm_num)).2
  have h1 := jo86_greedy_bound S h2 hdeg F₁ hF
  have h3 := jo86_opt_bound S h2
  norm_num at hle
  omega

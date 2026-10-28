-- Prove2me | solution 1 for HHRControl.PV.claim_4_29
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:16:39.158912+00:00
-- url     : https://prove2.me/submissions/38dc5752-f63e-4ffe-8231-a3577c7bed2d

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

open HHRControl.PV CookPvsNP Finset

namespace C428

/-- The voter with ballot `r` votes for `x` in the election with candidate set `D`. -/
def Votes {m' : ℕ} (r : Ranking m') (D : Finset (Fin m')) (x : Fin m') : Prop :=
  ∀ y ∈ D, y ≠ x → r x < r y

instance {m' : ℕ} (r : Ranking m') (D : Finset (Fin m')) (x : Fin m') : Decidable (Votes r D x) :=
  inferInstanceAs (Decidable (∀ y ∈ D, y ≠ x → r x < r y))

lemma score_eq {m' n' : ℕ} (P : Fin n' → Ranking m') (D : Finset (Fin m')) (U : Finset (Fin n'))
    (x : Fin m') : pluralityScore P D U x = (U.filter fun v => Votes (P v) D x).card := rfl

lemma rk_inj {m' : ℕ} (r : Ranking m') {x y : Fin m'} (h : (r x : ℕ) = r y) : x = y :=
  r.injective (Fin.ext h)

lemma lt_iff {m' : ℕ} (r : Ranking m') (x y : Fin m') : r x < r y ↔ (r x : ℕ) < r y :=
  Fin.lt_def

lemma pos_of_ne {m' : ℕ} {r : Ranking m'} {x y : Fin m'} (hx : (r x : ℕ) = 0) (hne : y ≠ x) :
    0 < (r y : ℕ) := by
  rcases Nat.eq_zero_or_pos (r y : ℕ) with h | h
  · exact absurd (rk_inj r (h.trans hx.symm)) hne
  · exact h

lemma two_le_of_ne {m' : ℕ} {r : Ranking m'} {x y z : Fin m'} (hx : (r x : ℕ) = 0)
    (hy : (r y : ℕ) = 1) (hzx : z ≠ x) (hzy : z ≠ y) : 2 ≤ (r z : ℕ) := by
  have h1 := pos_of_ne hx hzx
  rcases Nat.lt_or_ge (r z : ℕ) 2 with h | h
  · have : (r z : ℕ) = 1 := by omega
    exact absurd (rk_inj r (this.trans hy.symm)) hzy
  · exact h

lemma votes_of_zero {m' : ℕ} {r : Ranking m'} {x : Fin m'} (hx : (r x : ℕ) = 0)
    (D : Finset (Fin m')) : Votes r D x := by
  intro y _ hyx
  rw [lt_iff, hx]
  exact pos_of_ne hx hyx

lemma not_votes_of_lt {m' : ℕ} {r : Ranking m'} {x y : Fin m'} {D : Finset (Fin m')} (hy : y ∈ D)
    (hlt : (r y : ℕ) < r x) : ¬ Votes r D x := by
  intro hv
  have hne : y ≠ x := fun h => by subst h; exact lt_irrefl _ hlt
  have := (lt_iff r x y).1 (hv y hy hne)
  omega

/-! ### Candidates -/

variable {m n : ℕ}

lemma candB_val (j : Fin m) : ((candB j : Fin (m + 2)) : ℕ) = j := rfl
lemma candC_val : ((candC m : Fin (m + 2)) : ℕ) = m := rfl
lemma candW_val : ((candW m : Fin (m + 2)) : ℕ) = m + 1 := rfl

lemma candB_ne_candC (j : Fin m) : candB j ≠ candC m := by
  intro h; have := congrArg Fin.val h; rw [candB_val, candC_val] at this; omega

lemma candB_ne_candW (j : Fin m) : candB j ≠ candW m := by
  intro h; have := congrArg Fin.val h; rw [candB_val, candW_val] at this; omega

lemma candC_ne_candW : candC m ≠ candW m := by
  intro h; have := congrArg Fin.val h; rw [candC_val, candW_val] at this; omega

lemma candB_inj {i j : Fin m} (h : candB i = candB j) : i = j := by
  apply Fin.ext; have := congrArg Fin.val h; rwa [candB_val, candB_val] at this

lemma cand_cases (x : Fin (m + 2)) : (∃ j, x = candB j) ∨ x = candC m ∨ x = candW m := by
  rcases x with ⟨x, hx⟩
  by_cases h : x < m
  · exact Or.inl ⟨⟨x, h⟩, rfl⟩
  · right
    by_cases h2 : x = m
    · exact Or.inl (Fin.ext h2)
    · exact Or.inr (Fin.ext (by simp only [candW_val]; omega))

/-! ### Ballot facts for the four voter types -/

section ballots
variable {r : Ranking (m + 2)} {D : Finset (Fin (m + 2))}

-- cw voter
lemma cw_votes_c (hc : (r (candC m) : ℕ) = 0) : Votes r D (candC m) := votes_of_zero hc D

lemma cw_not_votes (hc : (r (candC m) : ℕ) = 0) (hcD : candC m ∈ D) {x : Fin (m + 2)}
    (hx : x ≠ candC m) : ¬ Votes r D x :=
  not_votes_of_lt hcD (by rw [hc]; exact pos_of_ne hc hx)

-- wc voter
lemma wc_votes_w (hw : (r (candW m) : ℕ) = 0) : Votes r D (candW m) := votes_of_zero hw D

lemma wc_not_votes_of_w (hw : (r (candW m) : ℕ) = 0) (hwD : candW m ∈ D) {x : Fin (m + 2)}
    (hx : x ≠ candW m) : ¬ Votes r D x :=
  not_votes_of_lt hwD (by rw [hw]; exact pos_of_ne hw hx)

lemma wc_votes_c (hw : (r (candW m) : ℕ) = 0) (hc : (r (candC m) : ℕ) = 1)
    (hwD : candW m ∉ D) : Votes r D (candC m) := by
  intro y hy hyc
  rw [lt_iff, hc]
  have hyw : y ≠ candW m := fun h => hwD (h ▸ hy)
  have := two_le_of_ne hw hc hyw hyc
  omega

lemma wc_not_votes_of_c (hw : (r (candW m) : ℕ) = 0) (hc : (r (candC m) : ℕ) = 1)
    (hcD : candC m ∈ D) {x : Fin (m + 2)} (hxw : x ≠ candW m) (hxc : x ≠ candC m) :
    ¬ Votes r D x :=
  not_votes_of_lt hcD (by rw [hc]; have := two_le_of_ne hw hc hxw hxc; omega)

-- elem j voter
lemma elem_votes_b {j : Fin m} (hb : (r (candB j) : ℕ) = 0) : Votes r D (candB j) :=
  votes_of_zero hb D

lemma elem_not_votes_of_b {j : Fin m} (hb : (r (candB j) : ℕ) = 0) (hbD : candB j ∈ D)
    {x : Fin (m + 2)} (hx : x ≠ candB j) : ¬ Votes r D x :=
  not_votes_of_lt hbD (by rw [hb]; exact pos_of_ne hb hx)

lemma elem_votes_w {j : Fin m} (hb : (r (candB j) : ℕ) = 0) (hw : (r (candW m) : ℕ) = 1)
    (hbD : candB j ∉ D) : Votes r D (candW m) := by
  intro y hy hyw
  rw [lt_iff, hw]
  have hyb : y ≠ candB j := fun h => hbD (h ▸ hy)
  have := two_le_of_ne hb hw hyb hyw
  omega

lemma elem_not_votes_of_w {j : Fin m} (hb : (r (candB j) : ℕ) = 0) (hw : (r (candW m) : ℕ) = 1)
    (hwD : candW m ∈ D) {x : Fin (m + 2)} (hxb : x ≠ candB j) (hxw : x ≠ candW m) :
    ¬ Votes r D x :=
  not_votes_of_lt hwD (by rw [hw]; have := two_le_of_ne hb hw hxb hxw; omega)

-- set i voter
lemma set_card_le {s : Finset (Fin m)} (hS : ∀ j, j ∈ s ↔ (r (candB j) : ℕ) < s.card)
    (x : Fin (m + 2)) (hx : ∀ j, x ≠ candB j) : s.card ≤ (r x : ℕ) := by
  by_contra h
  push_neg at h
  have himg : s.image (fun j => (r (candB j) : ℕ)) ⊆ range s.card := by
    intro p hp
    simp only [mem_image] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact mem_range.2 ((hS j).1 hj)
  have hinj : Set.InjOn (fun j => (r (candB j) : ℕ)) s := by
    intro a _ b _ hab
    exact candB_inj (rk_inj r hab)
  have hcard : (s.image (fun j => (r (candB j) : ℕ))).card = s.card := card_image_of_injOn hinj
  have heq : s.image (fun j => (r (candB j) : ℕ)) = range s.card :=
    eq_of_subset_of_card_le himg (by rw [hcard, card_range])
  have : (r x : ℕ) ∈ range s.card := mem_range.2 h
  rw [← heq, mem_image] at this
  obtain ⟨j, _, hj⟩ := this
  exact hx j (rk_inj r hj.symm)

lemma set_c_lt_w {s : Finset (Fin m)} (hS : ∀ j, j ∈ s ↔ (r (candB j) : ℕ) < s.card)
    (hc : (r (candC m) : ℕ) = s.card) : (r (candC m) : ℕ) < r (candW m) := by
  have h1 := set_card_le hS (candW m) (fun j => (candB_ne_candW j).symm)
  have h2 : (r (candC m) : ℕ) ≠ r (candW m) := fun h => candC_ne_candW (rk_inj r h)
  omega

lemma set_not_votes_w {s : Finset (Fin m)} (hS : ∀ j, j ∈ s ↔ (r (candB j) : ℕ) < s.card)
    (hc : (r (candC m) : ℕ) = s.card) (hcD : candC m ∈ D) : ¬ Votes r D (candW m) :=
  not_votes_of_lt hcD (set_c_lt_w hS hc)

lemma set_not_votes_c {s : Finset (Fin m)} (hS : ∀ j, j ∈ s ↔ (r (candB j) : ℕ) < s.card)
    (hc : (r (candC m) : ℕ) = s.card) {j : Fin m} (hj : j ∈ s) (hbD : candB j ∈ D) :
    ¬ Votes r D (candC m) :=
  not_votes_of_lt hbD (by rw [hc]; exact (hS j).1 hj)

lemma set_votes_c {s : Finset (Fin m)} (hS : ∀ j, j ∈ s ↔ (r (candB j) : ℕ) < s.card)
    (hc : (r (candC m) : ℕ) = s.card) (hD : ∀ j ∈ s, candB j ∉ D) : Votes r D (candC m) := by
  intro y hy hyc
  rw [lt_iff, hc]
  rcases cand_cases y with ⟨j, rfl⟩ | rfl | rfl
  · have hjs : j ∉ s := fun hj => hD j hj hy
    have h1 : ¬ (r (candB j) : ℕ) < s.card := fun h => hjs ((hS j).2 h)
    have h2 : (r (candC m) : ℕ) ≠ r (candB j) := fun h => (candB_ne_candC j) (rk_inj r h).symm
    omega
  · exact absurd rfl hyc
  · have := set_c_lt_w hS hc; omega

end ballots

/-! ### Counting voters by type -/

lemma card_filter_exists {α β ι : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [DecidableEq ι] (τ : α → β)
    (I : Finset ι) (f : ι → β) (hf : Function.Injective f) :
    (univ.filter fun v => ∃ i ∈ I, τ v = f i).card =
      ∑ i ∈ I, (univ.filter fun v => τ v = f i).card := by
  rw [← Finset.card_biUnion]
  · congr 1; ext v; simp
  · intro i _ j _ hij
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [mem_filter] at hv hv'
    exact hij (hf (hv.2.symm.trans hv'.2))

lemma card_filter_add_compl {α : Type*} [Fintype α] [DecidableEq α] (U : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (U.filter p).card + (Uᶜ.filter p).card = (univ.filter p).card := by
  rw [← card_union_of_disjoint, ← filter_union, union_compl]
  exact disjoint_filter_filter disjoint_compl_right


/-! ### Claim 4.29, generalized to hitting sets of size at most `k` -/

section claims
variable {m n k : ℕ} {S : Fin n → Finset (Fin m)} {N : ℕ} {P : Fin N → Ranking (m + 2)}

/-- number of set-voters -/
lemma card_set_voters (τ : Fin N → VoterType m n)
    (hset : ∀ i, (univ.filter fun v => τ v = .set i).card = 2 * (k + 1)) :
    (univ.filter fun v => ∃ i, τ v = .set i).card = 2 * (n * (k + 1)) := by
  have h : (univ.filter fun v => ∃ i, τ v = .set i) =
      univ.biUnion (fun i => univ.filter fun v => τ v = .set i) := by
    ext v; simp
  rw [h, card_biUnion]
  · simp only [hset, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring
  · intro i _ j _ hij
    show Disjoint _ _
    rw [disjoint_left]
    intro v hv hv'
    rw [mem_filter] at hv hv'
    exact hij (VoterType.set.inj (hv.2.symm.trans hv'.2))

/-- number of elem-voters with index in `J` -/
lemma card_elem_voters (τ : Fin N → VoterType m n)
    (helem : ∀ j, (univ.filter fun v => τ v = .elem j).card = 2) (J : Finset (Fin m)) :
    (univ.filter fun v => ∃ j ∈ J, τ v = .elem j).card = 2 * J.card := by
  have h : (univ.filter fun v => ∃ j ∈ J, τ v = .elem j) =
      J.biUnion (fun j => univ.filter fun v => τ v = .elem j) := by
    ext v; simp
  rw [h, card_biUnion]
  · simp only [helem, sum_const, smul_eq_mul]; ring
  · intro i _ j _ hij
    show Disjoint _ _
    rw [disjoint_left]
    intro v hv hv'
    rw [mem_filter] at hv hv'
    exact hij (VoterType.elem.inj (hv.2.symm.trans hv'.2))

theorem claim429' (hP : IsConstruction428 m n k S P) (B' : Finset (Fin m)) (hcard : B'.card ≤ k)
    (hhit : IsHittingSet S B') :
    plurality.winners (m + 2) N P (B'.image candB ∪ {candC m, candW m}) univ = {candW m} := by
  obtain ⟨hk1, hkm, τ, hcw, hwc, hset, helem, hform⟩ := hP
  set D : Finset (Fin (m + 2)) := B'.image candB ∪ {candC m, candW m} with hDdef
  have hcD : candC m ∈ D := by simp [hDdef]
  have hwD : candW m ∈ D := by simp [hDdef]
  have hbD : ∀ j, candB j ∈ D ↔ j ∈ B' := by
    intro j
    simp only [hDdef, mem_union, mem_image, mem_insert, mem_singleton, candB_ne_candC,
      candB_ne_candW, or_false]
    constructor
    · rintro ⟨j', hj', h⟩; rwa [← candB_inj h]
    · intro h; exact ⟨j, h, rfl⟩
  have ha : 2 * n * (k + 1) = 2 * (n * (k + 1)) := by ring
  rw [ha] at hcw hwc
  -- the scores
  have hsc_c : pluralityScore P D univ (candC m) ≤ 2 * (m - k) + 2 * (n * (k + 1)) + 4 := by
    rw [score_eq, ← hcw]
    apply card_le_card
    intro v hv
    rw [mem_filter] at hv ⊢
    refine ⟨mem_univ _, ?_⟩
    have hf := hform v
    cases hτ : τ v with
    | cw => rfl
    | wc =>
      rw [hτ] at hf
      obtain ⟨hw, hc⟩ := hf
      exact absurd hv.2 (wc_not_votes_of_w hw hwD candC_ne_candW)
    | set i =>
      rw [hτ] at hf
      obtain ⟨hS, hc⟩ := hf
      obtain ⟨j, hj⟩ := hhit i
      rw [mem_inter] at hj
      exact absurd hv.2 (set_not_votes_c hS hc hj.1 ((hbD j).2 hj.2))
    | elem j =>
      rw [hτ] at hf
      obtain ⟨hb, hw⟩ := hf
      exact absurd hv.2 (elem_not_votes_of_w hb hw hwD (candB_ne_candC j).symm candC_ne_candW)
  have hsc_w : 2 * (n * (k + 1)) + 5 + 2 * (m - B'.card) ≤
      pluralityScore P D univ (candW m) := by
    have hE : (univ.filter fun v => ∃ j ∈ B'ᶜ, τ v = .elem j).card = 2 * (m - B'.card) := by
      rw [card_elem_voters τ helem B'ᶜ, card_compl, Fintype.card_fin]
    rw [score_eq, ← hwc, ← hE, ← card_union_of_disjoint]
    · apply card_le_card
      intro v hv
      rw [mem_union, mem_filter, mem_filter] at hv
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hf := hform v
      rcases hv with ⟨_, h⟩ | ⟨_, j, hj, h⟩
      · rw [h] at hf
        obtain ⟨hw, hc⟩ := hf
        exact wc_votes_w hw
      · rw [h] at hf
        obtain ⟨hb, hw⟩ := hf
        rw [mem_compl] at hj
        exact elem_votes_w hb hw (fun h' => hj ((hbD j).1 h'))
    · rw [disjoint_left]
      intro v hv hv'
      rw [mem_filter] at hv hv'
      obtain ⟨_, j, _, h⟩ := hv'
      rw [h] at hv
      exact absurd hv.2 (by simp)
  have hsc_b : ∀ j ∈ B', pluralityScore P D univ (candB j) ≤ 2 + 2 * (n * (k + 1)) := by
    intro j hj
    rw [score_eq]
    refine le_trans (card_le_card ?_) (le_trans (card_union_le (univ.filter fun v => τ v = .elem j)
      (univ.filter fun v => ∃ i, τ v = .set i)) ?_)
    · intro v hv
      rw [mem_filter] at hv
      rw [mem_union, mem_filter, mem_filter]
      have hf := hform v
      cases hτ : τ v with
      | cw =>
        rw [hτ] at hf
        obtain ⟨hc, hw⟩ := hf
        exact absurd hv.2 (cw_not_votes hc hcD (candB_ne_candC j))
      | wc =>
        rw [hτ] at hf
        obtain ⟨hw, hc⟩ := hf
        exact absurd hv.2 (wc_not_votes_of_w hw hwD (candB_ne_candW j))
      | set i => exact Or.inr ⟨mem_univ _, i, rfl⟩
      | elem j' =>
        rw [hτ] at hf
        obtain ⟨hb, hw⟩ := hf
        by_cases hjj : j' = j
        · subst hjj; exact Or.inl ⟨mem_univ _, rfl⟩
        · exact absurd hv.2 (elem_not_votes_of_w hb hw hwD (fun h' => hjj (candB_inj h').symm)
            (candB_ne_candW j))
    · rw [helem j, card_set_voters τ hset]
  -- arithmetic
  have hlt_c : pluralityScore P D univ (candC m) < pluralityScore P D univ (candW m) := by
    have : m - k ≤ m - B'.card := Nat.sub_le_sub_left hcard m
    omega
  have hlt_b : ∀ j ∈ B', pluralityScore P D univ (candB j) < pluralityScore P D univ (candW m) := by
    intro j hj
    have := hsc_b j hj
    omega
  -- the winner set
  show D.filter (fun x => ∀ y ∈ D, pluralityScore P D univ y ≤ pluralityScore P D univ x) = _
  ext x
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hxD, hmax⟩
    by_contra hxw
    have h := hmax (candW m) hwD
    rcases cand_cases x with ⟨j, rfl⟩ | rfl | rfl
    · have := hlt_b j ((hbD j).1 hxD); omega
    · omega
    · exact hxw rfl
  · rintro rfl
    refine ⟨hwD, fun y hy => ?_⟩
    rcases cand_cases y with ⟨j, rfl⟩ | rfl | rfl
    · exact (hlt_b j ((hbD j).1 hy)).le
    · exact hlt_c.le
    · exact le_rfl

end claims

end C428

open C428 in
theorem solution (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (B' : Finset (Fin m)) (hcard : B'.card = k)
    (hhit : IsHittingSet S B') :
    plurality.winners (m + 2) N P (B'.image candB ∪ {candC m, candW m}) Finset.univ =
      {candW m} :=
  claim429' hP B' hcard.le hhit

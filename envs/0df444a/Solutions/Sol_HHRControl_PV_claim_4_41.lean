-- Prove2me | solution 1 for HHRControl.PV.claim_4_41
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:23:25.86422+00:00
-- url     : https://prove2.me/submissions/3686da34-5a74-4264-9032-c262c0de0e7f

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

/-! ### Claim 4.40 -/

/-- Scores in the full election `(C, U)` for `U ⊆ V`: basic bounds. -/
lemma score_mono (D : Finset (Fin (m + 2))) (U : Finset (Fin N)) (x : Fin (m + 2)) :
    pluralityScore P D U x ≤ pluralityScore P D univ x := by
  rw [score_eq, score_eq]
  exact card_le_card (filter_subset_filter _ (subset_univ U))

lemma score_add_compl (D : Finset (Fin (m + 2))) (U : Finset (Fin N)) (x : Fin (m + 2)) :
    pluralityScore P D U x + pluralityScore P D Uᶜ x = pluralityScore P D univ x := by
  rw [score_eq, score_eq, score_eq]
  exact card_filter_add_compl U _

lemma not_mem_winners_univ {U : Finset (Fin N)} {x : Fin (m + 2)}
    (h : x ∉ plurality.winners (m + 2) N P univ U) :
    ∃ y, pluralityScore P univ U x < pluralityScore P univ U y := by
  have : x ∉ (univ : Finset (Fin (m + 2))).filter
      (fun x => ∀ y ∈ univ, pluralityScore P univ U y ≤ pluralityScore P univ U x) := h
  simp only [mem_filter, mem_univ, true_and, not_forall, not_le, true_implies] at this
  exact this

/-- `c` gets at least the cw-voters in `(C, V)`. -/
lemma score_c_univ_ge (τ : Fin N → VoterType m n) (hform : ∀ v, BallotForm S (τ v) (P v)) :
    (univ.filter fun v => τ v = .cw).card ≤ pluralityScore P univ univ (candC m) := by
  rw [score_eq]
  apply card_le_card
  intro v hv
  rw [mem_filter] at hv ⊢
  refine ⟨mem_univ _, ?_⟩
  have hf := hform v
  rw [hv.2] at hf
  exact cw_votes_c hf.1

/-- `w` gets exactly the wc-voters in `(C, V)` (upper bound). -/
lemma score_w_univ_le (τ : Fin N → VoterType m n) (hform : ∀ v, BallotForm S (τ v) (P v)) :
    pluralityScore P univ univ (candW m) ≤ (univ.filter fun v => τ v = .wc).card := by
  rw [score_eq]
  apply card_le_card
  intro v hv
  rw [mem_filter] at hv ⊢
  refine ⟨mem_univ _, ?_⟩
  have hf := hform v
  cases hτ : τ v with
  | cw =>
    rw [hτ] at hf
    exact absurd hv.2 (cw_not_votes hf.1 (mem_univ _) candC_ne_candW.symm)
  | wc => rfl
  | set i =>
    rw [hτ] at hf
    exact absurd hv.2 (set_not_votes_w hf.1 hf.2 (mem_univ _))
  | elem j =>
    rw [hτ] at hf
    exact absurd hv.2 (elem_not_votes_of_b hf.1 (mem_univ _) (candB_ne_candW j).symm)

/-- `b_j` gets at most the elem-`j`-voters and the set-voters in `(C, V)`. -/
lemma score_b_univ_le (τ : Fin N → VoterType m n) (hform : ∀ v, BallotForm S (τ v) (P v))
    (hset : ∀ i, (univ.filter fun v => τ v = .set i).card = 2 * (k + 1))
    (helem : ∀ j, (univ.filter fun v => τ v = .elem j).card = 2) (j : Fin m) :
    pluralityScore P univ univ (candB j) ≤ 2 + 2 * (n * (k + 1)) := by
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
      exact absurd hv.2 (cw_not_votes hf.1 (mem_univ _) (candB_ne_candC j))
    | wc =>
      rw [hτ] at hf
      exact absurd hv.2 (wc_not_votes_of_w hf.1 (mem_univ _) (candB_ne_candW j))
    | set i => exact Or.inr ⟨mem_univ _, i, rfl⟩
    | elem j' =>
      rw [hτ] at hf
      by_cases hjj : j' = j
      · subst hjj; exact Or.inl ⟨mem_univ _, rfl⟩
      · exact absurd hv.2 (elem_not_votes_of_b hf.1 (mem_univ _)
          (fun h' => hjj (candB_inj h').symm))
  · rw [helem j, card_set_voters τ hset]

theorem claim440' (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m)
    (V₁ : Finset (Fin N)) :
    candC m ∈ plurality.winners (m + 2) N P univ V₁ ∨
      candC m ∈ plurality.winners (m + 2) N P univ V₁ᶜ := by
  obtain ⟨hk1, hkm, τ, hcw, hwc, hset, helem, hform⟩ := hP
  have ha : 2 * n * (k + 1) = 2 * (n * (k + 1)) := by ring
  rw [ha] at hcw hwc
  by_contra h
  push_neg at h
  obtain ⟨d₁, hd₁⟩ := not_mem_winners_univ h.1
  obtain ⟨d₂, hd₂⟩ := not_mem_winners_univ h.2
  have hc := score_c_univ_ge τ hform
  have hw := score_w_univ_le τ hform
  have hb := score_b_univ_le τ hform hset helem
  have hsum := score_add_compl (P := P) univ V₁ (candC m)
  have hm1 := score_mono (P := P) univ V₁ d₁
  have hm2 := score_mono (P := P) univ V₁ᶜ d₂
  have hsumd : ∀ d, pluralityScore P univ V₁ d + pluralityScore P univ V₁ᶜ d =
    pluralityScore P univ univ d := fun d => score_add_compl (P := P) univ V₁ d
  rw [hcw] at hc
  rw [hwc] at hw
  rcases cand_cases d₁ with ⟨j₁, rfl⟩ | rfl | rfl <;>
    rcases cand_cases d₂ with ⟨j₂, rfl⟩ | rfl | rfl
  · have h1 := hb j₁; have h2 := hb j₂; omega
  · have h1 := hb j₁; have h2 := hsumd (candC m); omega
  · have h1 := hb j₁; omega
  · have h2 := hb j₂; have h1 := hsumd (candC m); omega
  · have h1 := hsumd (candC m); omega
  · have h1 := hsumd (candC m); omega
  · have h2 := hb j₂; omega
  · have h1 := hsumd (candC m); omega
  · have h1 := hsumd (candW m); omega


/-! ### Claim 4.30 for `n ≥ 1` -/

theorem claim430' (hP : IsConstruction428 m n k S P) (hn : 1 ≤ n) (D : Finset (Fin (m + 2)))
    (hD : D ⊆ univ.image candB ∪ {candW m})
    (hc : plurality.winners (m + 2) N P (insert (candC m) D) univ ≠ {candC m}) :
    ∃ B' : Finset (Fin m), D = B'.image candB ∪ {candW m} ∧
      plurality.winners (m + 2) N P (B'.image candB ∪ {candC m, candW m}) univ = {candW m} ∧
      B'.card ≤ k ∧ IsHittingSet S B' := by
  have hP' := hP
  obtain ⟨hk1, hkm, τ, hcw, hwc, hset, helem, hform⟩ := hP
  have ha : 2 * n * (k + 1) = 2 * (n * (k + 1)) := by ring
  rw [ha] at hcw hwc
  have hak : k + 1 ≤ n * (k + 1) := Nat.le_mul_of_pos_left (k + 1) hn
  set E := insert (candC m) D with hEdef
  have hcE : candC m ∈ E := mem_insert_self _ _
  have hDE : D ⊆ E := subset_insert _ _
  have hmemD : ∀ x ∈ D, (∃ j, x = candB j) ∨ x = candW m := by
    intro x hx
    have := hD hx
    simp only [mem_union, mem_image, mem_univ, true_and, mem_singleton] at this
    rcases this with ⟨j, hj⟩ | h
    · exact Or.inl ⟨j, hj.symm⟩
    · exact Or.inr h
  -- some `x ≠ c` of `E` has a score at least that of `c`
  have hex : ∃ x ∈ E, x ≠ candC m ∧
      pluralityScore P E univ (candC m) ≤ pluralityScore P E univ x := by
    by_contra hne
    push_neg at hne
    apply hc
    show E.filter (fun x => ∀ y ∈ E, pluralityScore P E univ y ≤ pluralityScore P E univ x) = _
    ext x
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hxE, hmax⟩
      by_contra hxc
      have h1 := hne x hxE hxc
      have h2 := hmax (candC m) hcE
      omega
    · rintro rfl
      refine ⟨hcE, fun y hy => ?_⟩
      by_cases hyc : y = candC m
      · subst hyc; exact le_rfl
      · exact (hne y hy hyc).le
  obtain ⟨x, hxE, hxc, hsc⟩ := hex
  have hxD : x ∈ D := by
    rcases mem_insert.1 hxE with h | h
    · exact absurd h hxc
    · exact h
  -- general score bounds in `E`
  have hsc_c : (univ.filter fun v => τ v = .cw).card ≤ pluralityScore P E univ (candC m) := by
    rw [score_eq]
    apply card_le_card
    intro v hv
    rw [mem_filter] at hv ⊢
    refine ⟨mem_univ _, ?_⟩
    have hf := hform v
    rw [hv.2] at hf
    exact cw_votes_c hf.1
  have hsc_b1 : ∀ j, pluralityScore P E univ (candB j) ≤ 2 * m + 2 * (n * (k + 1)) := by
    intro j
    rw [score_eq]
    refine le_trans (card_le_card ?_) (le_trans (card_union_le
      (univ.filter fun v => ∃ j' ∈ (univ : Finset (Fin m)), τ v = .elem j')
      (univ.filter fun v => ∃ i, τ v = .set i)) ?_)
    · intro v hv
      rw [mem_filter] at hv
      rw [mem_union, mem_filter, mem_filter]
      have hf := hform v
      cases hτ : τ v with
      | cw =>
        rw [hτ] at hf
        exact absurd hv.2 (cw_not_votes hf.1 hcE (candB_ne_candC j))
      | wc =>
        rw [hτ] at hf
        exact absurd hv.2 (wc_not_votes_of_c hf.1 hf.2 hcE (candB_ne_candW j) (candB_ne_candC j))
      | set i => exact Or.inr ⟨mem_univ _, i, rfl⟩
      | elem j' => exact Or.inl ⟨mem_univ _, j', mem_univ _, rfl⟩
    · rw [card_elem_voters τ helem univ, card_univ, Fintype.card_fin, card_set_voters τ hset]
  by_cases hwD : candW m ∈ D
  · -- the case `w ∈ D`
    have hwE : candW m ∈ E := hDE hwD
    have hsc_b2 : ∀ j, pluralityScore P E univ (candB j) ≤ 2 + 2 * (n * (k + 1)) := by
      intro j
      rw [score_eq]
      refine le_trans (card_le_card ?_) (le_trans (card_union_le
        (univ.filter fun v => τ v = .elem j) (univ.filter fun v => ∃ i, τ v = .set i)) ?_)
      · intro v hv
        rw [mem_filter] at hv
        rw [mem_union, mem_filter, mem_filter]
        have hf := hform v
        cases hτ : τ v with
        | cw =>
          rw [hτ] at hf
          exact absurd hv.2 (cw_not_votes hf.1 hcE (candB_ne_candC j))
        | wc =>
          rw [hτ] at hf
          exact absurd hv.2 (wc_not_votes_of_w hf.1 hwE (candB_ne_candW j))
        | set i => exact Or.inr ⟨mem_univ _, i, rfl⟩
        | elem j' =>
          rw [hτ] at hf
          by_cases hjj : j' = j
          · subst hjj; exact Or.inl ⟨mem_univ _, rfl⟩
          · exact absurd hv.2 (elem_not_votes_of_w hf.1 hf.2 hwE
              (fun h' => hjj (candB_inj h').symm) (candB_ne_candW j))
      · rw [helem j, card_set_voters τ hset]
    -- so `x = w`
    have hxw : x = candW m := by
      rcases hmemD x hxD with ⟨j, rfl⟩ | h
      · have := hsc_b2 j; omega
      · exact h
    subst hxw
    set B' : Finset (Fin m) := univ.filter (fun j => candB j ∈ D) with hB'def
    have hB' : ∀ j, j ∈ B' ↔ candB j ∈ D := by intro j; simp [hB'def]
    have hB'm : B'.card ≤ m := by
      have := card_le_univ B'; rwa [Fintype.card_fin] at this
    -- upper bound on the score of `w`
    have hsc_w : pluralityScore P E univ (candW m) ≤
        2 * (n * (k + 1)) + 5 + 2 * (m - B'.card) := by
      have hE : (univ.filter fun v => ∃ j ∈ B'ᶜ, τ v = .elem j).card = 2 * (m - B'.card) := by
        rw [card_elem_voters τ helem B'ᶜ, card_compl, Fintype.card_fin]
      rw [score_eq, ← hwc, ← hE]
      refine le_trans (card_le_card ?_) (card_union_le _ _)
      intro v hv
      rw [mem_filter] at hv
      rw [mem_union, mem_filter, mem_filter]
      have hf := hform v
      cases hτ : τ v with
      | cw =>
        rw [hτ] at hf
        exact absurd hv.2 (cw_not_votes hf.1 hcE candC_ne_candW.symm)
      | wc => exact Or.inl ⟨mem_univ _, rfl⟩
      | set i =>
        rw [hτ] at hf
        exact absurd hv.2 (set_not_votes_w hf.1 hf.2 hcE)
      | elem j =>
        rw [hτ] at hf
        by_cases hj : j ∈ B'
        · exact absurd hv.2 (elem_not_votes_of_b hf.1 (hDE ((hB' j).1 hj)) (candB_ne_candW j).symm)
        · exact Or.inr ⟨mem_univ _, j, mem_compl.2 hj, rfl⟩
    -- lower bound on the score of `c` if some `S i` is not hit
    have hsc_c2 : ∀ i, (∀ j ∈ S i, candB j ∉ D) →
        (univ.filter fun v => τ v = .cw).card + 2 * (k + 1) ≤
          pluralityScore P E univ (candC m) := by
      intro i hi
      rw [score_eq, ← hset i, ← card_union_of_disjoint]
      · apply card_le_card
        intro v hv
        rw [mem_union, mem_filter, mem_filter] at hv
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        have hf := hform v
        rcases hv with ⟨_, h⟩ | ⟨_, h⟩
        · rw [h] at hf
          exact cw_votes_c hf.1
        · rw [h] at hf
          refine set_votes_c hf.1 hf.2 (fun j hj hjE => ?_)
          rcases mem_insert.1 hjE with h' | h'
          · exact candB_ne_candC j h'
          · exact hi j hj h'
      · rw [disjoint_left]
        intro v hv hv'
        rw [mem_filter] at hv hv'
        rw [hv.2] at hv'
        exact absurd hv'.2 (by simp)
    have hhit : IsHittingSet S B' := by
      intro i
      by_contra hemp
      have hi : ∀ j ∈ S i, candB j ∉ D := by
        intro j hj hjD
        exact hemp ⟨j, mem_inter.2 ⟨hj, (hB' j).2 hjD⟩⟩
      have := hsc_c2 i hi
      omega
    have hcard : B'.card ≤ k := by omega
    refine ⟨B', ?_, claim429' hP' B' hcard hhit, hcard, hhit⟩
    ext y
    simp only [mem_union, mem_image, mem_singleton]
    constructor
    · intro hy
      rcases hmemD y hy with ⟨j, rfl⟩ | rfl
      · exact Or.inl ⟨j, (hB' j).2 hy, rfl⟩
      · exact Or.inr rfl
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · exact (hB' j).1 hj
      · exact hwD
  · -- the case `w ∉ D`: `c` is the unique winner, contradiction
    exfalso
    have hwE : candW m ∉ E := by
      intro h
      rcases mem_insert.1 h with h' | h'
      · exact candC_ne_candW h'.symm
      · exact hwD h'
    have hsc_c' : (univ.filter fun v => τ v = .cw).card + (univ.filter fun v => τ v = .wc).card ≤
        pluralityScore P E univ (candC m) := by
      rw [score_eq, ← card_union_of_disjoint]
      · apply card_le_card
        intro v hv
        rw [mem_union, mem_filter, mem_filter] at hv
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        have hf := hform v
        rcases hv with ⟨_, h⟩ | ⟨_, h⟩
        · rw [h] at hf
          exact cw_votes_c hf.1
        · rw [h] at hf
          exact wc_votes_c hf.1 hf.2 hwE
      · rw [disjoint_left]
        intro v hv hv'
        rw [mem_filter] at hv hv'
        rw [hv.2] at hv'
        exact absurd hv'.2 (by simp)
    rcases hmemD x hxD with ⟨j, rfl⟩ | rfl
    · have := hsc_b1 j
      omega
    · exact hwD hxD

/-! ### Claim 4.41 -/

lemma twoStage_TP_eq (V₁ : Finset (Fin N)) :
    twoStage .TP plurality P V₁ = plurality.winners (m + 2) N P
      (plurality.winners (m + 2) N P univ V₁ ∪ plurality.winners (m + 2) N P univ V₁ᶜ) univ :=
  rfl

/-- (3) → (1) -/
theorem hs_of_partition (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m)
    (V₁ : Finset (Fin N)) (h : twoStage .TP plurality P V₁ ≠ {candC m}) :
    ∃ B' : Finset (Fin m), B'.card ≤ k ∧ IsHittingSet S B' := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨∅, by simp, fun i => i.elim0⟩
  · have h40 := claim440' hP hmk V₁
    set W := plurality.winners (m + 2) N P univ V₁ ∪ plurality.winners (m + 2) N P univ V₁ᶜ
      with hWdef
    have hcW : candC m ∈ W := by
      rw [hWdef, mem_union]; exact h40
    have hD : W.erase (candC m) ⊆ univ.image candB ∪ {candW m} := by
      intro x hx
      rw [mem_erase] at hx
      simp only [mem_union, mem_image, mem_univ, true_and, mem_singleton]
      rcases cand_cases x with ⟨j, rfl⟩ | rfl | rfl
      · exact Or.inl ⟨j, rfl⟩
      · exact absurd rfl hx.1
      · exact Or.inr rfl
    have hc : plurality.winners (m + 2) N P (insert (candC m) (W.erase (candC m))) univ ≠
        {candC m} := by
      rw [insert_erase hcW]
      exact h
    obtain ⟨B', -, -, hcard, hhit⟩ := claim430' hP hn _ hD hc
    exact ⟨B', hcard, hhit⟩

/-- (1) → (2) -/
theorem partition_of_hs (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m)
    (B' : Finset (Fin m)) (hcard : B'.card ≤ k) (hhit : IsHittingSet S B') :
    ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m} := by
  have hP' := hP
  obtain ⟨hk1, hkm, τ, hcw, hwc, hset, helem, hform⟩ := hP
  have ha : 2 * n * (k + 1) = 2 * (n * (k + 1)) := by ring
  rw [ha] at hcw hwc
  obtain ⟨A, hA, hAcard⟩ := exists_subset_card_eq (s := univ.filter fun v => τ v = .cw) (n := 2)
    (by rw [hcw]; omega)
  obtain ⟨Bw, hBw, hBwcard⟩ := exists_subset_card_eq (s := univ.filter fun v => τ v = .wc) (n := 2)
    (by rw [hwc]; omega)
  set Ev : Finset (Fin N) := univ.filter fun v => ∃ j ∈ B', τ v = .elem j with hEvdef
  set V₁ := A ∪ Bw ∪ Ev with hV₁def
  have hAτ : ∀ v ∈ A, τ v = .cw := fun v hv => (mem_filter.1 (hA hv)).2
  have hBwτ : ∀ v ∈ Bw, τ v = .wc := fun v hv => (mem_filter.1 (hBw hv)).2
  have hEvτ : ∀ v ∈ Ev, ∃ j ∈ B', τ v = .elem j := fun v hv => (mem_filter.1 hv).2
  have hmemV₁ : ∀ v, v ∈ V₁ ↔ v ∈ A ∨ v ∈ Bw ∨ v ∈ Ev := by
    intro v; simp only [hV₁def, mem_union, or_assoc]
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
  -- the scores in `(C, V₁)`
  have hsc_c : pluralityScore P univ V₁ (candC m) = 2 := by
    rw [score_eq]
    have hfA : (V₁.filter fun v => Votes (P v) univ (candC m)) = A := by
      ext v
      rw [mem_filter, hmemV₁]
      constructor
      · rintro ⟨hv, hvote⟩
        have hf := hform v
        rcases hv with hv | hv | hv
        · exact hv
        · rw [hBwτ v hv] at hf
          exact absurd hvote (wc_not_votes_of_w hf.1 (mem_univ _) candC_ne_candW)
        · obtain ⟨j, _, hj⟩ := hEvτ v hv
          rw [hj] at hf
          exact absurd hvote (elem_not_votes_of_b hf.1 (mem_univ _) (candB_ne_candC j).symm)
      · intro hv
        have hf := hform v
        rw [hAτ v hv] at hf
        exact ⟨Or.inl hv, cw_votes_c hf.1⟩
    rw [hfA, hAcard]
  have hsc_w : pluralityScore P univ V₁ (candW m) = 2 := by
    rw [score_eq]
    have hfB : (V₁.filter fun v => Votes (P v) univ (candW m)) = Bw := by
      ext v
      rw [mem_filter, hmemV₁]
      constructor
      · rintro ⟨hv, hvote⟩
        have hf := hform v
        rcases hv with hv | hv | hv
        · rw [hAτ v hv] at hf
          exact absurd hvote (cw_not_votes hf.1 (mem_univ _) candC_ne_candW.symm)
        · exact hv
        · obtain ⟨j, _, hj⟩ := hEvτ v hv
          rw [hj] at hf
          exact absurd hvote (elem_not_votes_of_b hf.1 (mem_univ _) (candB_ne_candW j).symm)
      · intro hv
        have hf := hform v
        rw [hBwτ v hv] at hf
        exact ⟨Or.inr (Or.inl hv), wc_votes_w hf.1⟩
    rw [hfB, hBwcard]
  have hsc_b : ∀ j, pluralityScore P univ V₁ (candB j) = if j ∈ B' then 2 else 0 := by
    intro j
    rw [score_eq]
    split_ifs with hj
    · have hfE : (V₁.filter fun v => Votes (P v) univ (candB j)) =
          univ.filter fun v => τ v = .elem j := by
        ext v
        rw [mem_filter, mem_filter, hmemV₁]
        constructor
        · rintro ⟨hv, hvote⟩
          have hf := hform v
          rcases hv with hv | hv | hv
          · rw [hAτ v hv] at hf
            exact absurd hvote (cw_not_votes hf.1 (mem_univ _) (candB_ne_candC j))
          · rw [hBwτ v hv] at hf
            exact absurd hvote (wc_not_votes_of_w hf.1 (mem_univ _) (candB_ne_candW j))
          · obtain ⟨j', _, hj'⟩ := hEvτ v hv
            rw [hj'] at hf
            by_cases hjj : j' = j
            · subst hjj; exact ⟨mem_univ _, hj'⟩
            · exact absurd hvote (elem_not_votes_of_b hf.1 (mem_univ _)
                (fun h' => hjj (candB_inj h').symm))
        · rintro ⟨_, hv⟩
          have hf := hform v
          rw [hv] at hf
          refine ⟨Or.inr (Or.inr ?_), elem_votes_b hf.1⟩
          rw [hEvdef, mem_filter]
          exact ⟨mem_univ _, j, hj, hv⟩
      rw [hfE, helem j]
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro v hv hvote
      have hf := hform v
      rcases (hmemV₁ v).1 hv with hv | hv | hv
      · rw [hAτ v hv] at hf
        exact cw_not_votes hf.1 (mem_univ _) (candB_ne_candC j) hvote
      · rw [hBwτ v hv] at hf
        exact wc_not_votes_of_w hf.1 (mem_univ _) (candB_ne_candW j) hvote
      · obtain ⟨j', hj', hτ⟩ := hEvτ v hv
        rw [hτ] at hf
        by_cases hjj : j' = j
        · subst hjj; exact hj hj'
        · exact elem_not_votes_of_b hf.1 (mem_univ _) (fun h' => hjj (candB_inj h').symm) hvote
  have hsc : ∀ x, pluralityScore P univ V₁ x = if x ∈ D then 2 else 0 := by
    intro x
    rcases cand_cases x with ⟨j, rfl⟩ | rfl | rfl
    · rw [hsc_b j]
      by_cases hj : j ∈ B'
      · rw [if_pos hj, if_pos ((hbD j).2 hj)]
      · rw [if_neg hj, if_neg (fun h => hj ((hbD j).1 h))]
    · rw [hsc_c, if_pos hcD]
    · rw [hsc_w, if_pos hwD]
  have hW1 : plurality.winners (m + 2) N P univ V₁ = D := by
    show univ.filter (fun x => ∀ y ∈ univ, pluralityScore P univ V₁ y ≤
      pluralityScore P univ V₁ x) = D
    ext x
    simp only [mem_filter, mem_univ, true_and, true_implies]
    constructor
    · intro hmax
      by_contra hxD
      have := hmax (candC m)
      rw [hsc, hsc, if_pos hcD, if_neg hxD] at this
      omega
    · intro hxD y
      rw [hsc, hsc, if_pos hxD]
      split_ifs <;> omega
  -- the scores in `(C, V₁ᶜ)`
  have hsc_c' : (univ.filter fun v => τ v = .cw).card - 2 ≤
      pluralityScore P univ V₁ᶜ (candC m) := by
    rw [score_eq]
    have hsd := card_sdiff_of_subset hA
    rw [hAcard] at hsd
    rw [← hsd]
    apply card_le_card
    intro v hv
    rw [mem_sdiff, mem_filter] at hv
    rw [mem_filter, mem_compl, hmemV₁]
    have hf := hform v
    rw [hv.1.2] at hf
    refine ⟨?_, cw_votes_c hf.1⟩
    rintro (h | h | h)
    · exact hv.2 h
    · have := hBwτ v h; rw [hv.1.2] at this; exact absurd this (by simp)
    · obtain ⟨j, _, hj⟩ := hEvτ v h; rw [hv.1.2] at hj; exact absurd hj (by simp)
  have hsc_w' : pluralityScore P univ V₁ᶜ (candW m) + 2 ≤
      (univ.filter fun v => τ v = .wc).card := by
    have h1 := score_add_compl (P := P) univ V₁ (candW m)
    have h2 := score_w_univ_le τ hform
    omega
  have hsc_b' : ∀ j, pluralityScore P univ V₁ᶜ (candB j) ≤ 2 + 2 * (n * (k + 1)) := by
    intro j
    exact (score_mono (P := P) univ V₁ᶜ (candB j)).trans (score_b_univ_le τ hform hset helem j)
  have hW2 : plurality.winners (m + 2) N P univ V₁ᶜ = {candC m} := by
    show univ.filter (fun x => ∀ y ∈ univ, pluralityScore P univ V₁ᶜ y ≤
      pluralityScore P univ V₁ᶜ x) = {candC m}
    have hlt : ∀ x, x ≠ candC m →
        pluralityScore P univ V₁ᶜ x < pluralityScore P univ V₁ᶜ (candC m) := by
      intro x hx
      rcases cand_cases x with ⟨j, rfl⟩ | rfl | rfl
      · have := hsc_b' j; omega
      · exact absurd rfl hx
      · omega
    ext x
    simp only [mem_filter, mem_univ, true_and, true_implies, mem_singleton]
    constructor
    · intro hmax
      by_contra hxc
      have h1 := hmax (candC m)
      have h2 := hlt x hxc
      omega
    · rintro rfl y
      by_cases hyc : y = candC m
      · subst hyc; exact le_rfl
      · exact (hlt y hyc).le
  refine ⟨V₁, ?_⟩
  rw [twoStage_TP_eq, hW1, hW2]
  have : D ∪ {candC m} = D := union_eq_left.2 (singleton_subset_iff.2 hcD)
  rw [this]
  exact claim429' hP' B' hcard hhit

theorem claim441' (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m) :
    ((∃ B' : Finset (Fin m), B'.card ≤ k ∧ IsHittingSet S B') ↔
        ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m}) ∧
      ((∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m}) ↔
        ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ ≠ {candC m}) := by
  have hwc : ∀ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m} →
      twoStage .TP plurality P V₁ ≠ {candC m} := by
    intro V₁ h h'
    rw [h] at h'
    exact candC_ne_candW (singleton_inj.1 h').symm
  refine ⟨⟨fun ⟨B', hcard, hhit⟩ => partition_of_hs hP hmk B' hcard hhit,
    fun ⟨V₁, h⟩ => hs_of_partition hP hmk V₁ (hwc V₁ h)⟩,
    ⟨fun ⟨V₁, h⟩ => ⟨V₁, hwc V₁ h⟩, fun ⟨V₁, h⟩ => ?_⟩⟩
  obtain ⟨B', hcard, hhit⟩ := hs_of_partition hP hmk V₁ h
  exact partition_of_hs hP hmk B' hcard hhit

end claims

end C428

open C428 in
theorem solution (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m) :
    ((∃ B' : Finset (Fin m), B'.card ≤ k ∧ IsHittingSet S B') ↔
        ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m}) ∧
      ((∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m}) ↔
        ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ ≠ {candC m}) :=
  claim441' hP hmk

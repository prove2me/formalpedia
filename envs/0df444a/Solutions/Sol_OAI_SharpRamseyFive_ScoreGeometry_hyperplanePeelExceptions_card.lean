-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:12:54.541975+00:00
-- url     : https://prove2.me/submissions/146c1354-601a-4b2e-865e-2aa95b7d95b6

import Mathlib
import Definitions.Def_OAIQ060R002

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Best
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {V I : Type*} [DecidableEq V] [LinearOrder I]

lemma best_spec (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V) :
    best F hF shape X ∈ F ∧
      ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape (best F hF shape X)).card :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma chosen_mem (k : ℕ) : chosen F hF shape X k ∈ F :=
  (best_spec F hF shape _).1

lemma maximal_cell (k : ℕ) (a : I) (ha : a ∈ F) :
    (remaining F hF shape X k ∩ shape a).card ≤ (cell F hF shape X k).card :=
  (best_spec F hF shape _).2 a ha

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma remaining_antitone : Antitone (remaining F hF shape X) :=
  antitone_nat_of_succ_le (remaining_succ_subset F hF shape X)

lemma remaining_subset (k : ℕ) : remaining F hF shape X k ⊆ X :=
  remaining_antitone F hF shape X (Nat.zero_le k)

lemma cell_subset (k : ℕ) : cell F hF shape X k ⊆ remaining F hF shape X k :=
  Finset.inter_subset_left

lemma cell_card_antitone : Antitone (fun k => (cell F hF shape X k).card) := by
  apply antitone_nat_of_succ_le
  intro k
  have hle : remaining F hF shape X (k+1) ∩ shape (chosen F hF shape X (k+1)) ⊆
      remaining F hF shape X k ∩ shape (chosen F hF shape X (k+1)) :=
    Finset.inter_subset_inter_right (remaining_succ_subset F hF shape X k)
  exact (Finset.card_le_card hle).trans (maximal_cell F hF shape X k _ (chosen_mem F hF shape X _))

lemma stopIndex_stops (threshold : ℕ) (hthreshold : 0 < threshold) :
    Stop F hF shape X threshold (stopIndex F hF shape X threshold hthreshold) := Nat.find_spec _

lemma retained_subset (threshold : ℕ) (hthreshold : 0 < threshold) :
    retained F hF shape X threshold hthreshold ⊆ X := by
  unfold retained
  split
  · exact Finset.sdiff_subset
  · exact remaining_subset F hF shape X _

lemma residual_cap (threshold : ℕ) (hthreshold : 0 < threshold)
    (hn : ¬X.card ≤ 2*(X.card-(remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)).card))
    (a : I) (ha : a ∈ F) :
    (retained F hF shape X threshold hthreshold ∩ shape a).card < threshold := by
  rw [retained,ite_eq_right hn]
  have hc := (stopIndex_stops F hF shape X threshold hthreshold).resolve_left hn
  exact (maximal_cell F hF shape X _ a ha).trans_lt hc

lemma remaining_eq_sdiff_union (k : ℕ) :
    remaining F hF shape X k = X \ (Finset.range k).biUnion (fun j => shape (chosen F hF shape X j)) := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    change remaining F hF shape X k \ shape (chosen F hF shape X k) = _
    rw [ih]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range]
    change (x ∈ X ∧ ¬∃ j < k, x ∈ shape (chosen F hF shape X j)) ∧
        x ∉ shape (chosen F hF shape X k) ↔
      x ∈ X ∧ ¬∃ j < k+1, x ∈ shape (chosen F hF shape X j)
    constructor
    · rintro ⟨⟨hx,hn⟩,hk⟩
      refine ⟨hx,?_⟩
      rintro ⟨j,hj,hxj⟩
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hj | rfl
      · exact hn ⟨j,hj,hxj⟩
      · exact hk hxj
    · rintro ⟨hx,hn⟩
      refine ⟨⟨hx,?_⟩,?_⟩
      · rintro ⟨j,hj,hxj⟩
        exact hn ⟨j,Nat.lt_succ_of_lt hj,hxj⟩
      · intro hxk
        exact hn ⟨k,Nat.lt_succ_self k,hxk⟩

lemma prefix_length_bound (k threshold : ℕ)
    (hlarge : ∀ j < k, threshold ≤ (cell F hF shape X j).card) :
    k*threshold ≤ X.card := by
  have hs := Finset.sum_le_sum (s := Finset.range k) (fun j hj => hlarge j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  have hh := sum_card_add_remaining F hF shape X k
  omega

lemma tail_cap (k cap : ℕ) (hcap : (cell F hF shape X k).card ≤ cap)
    (Y : Finset V) (hY : Y ⊆ remaining F hF shape X k) (a : I) (ha : a ∈ F) :
    (Y ∩ shape a).card ≤ cap := by
  exact (Finset.card_le_card (Finset.inter_subset_inter_right hY)).trans
    ((maximal_cell F hF shape X k a ha).trans hcap)

lemma headIndex_le (J cap : ℕ) : headIndex F hF shape X J cap ≤ J :=
  Nat.find_min' _ (Or.inl le_rfl)

lemma before_head (J cap : ℕ) {j : ℕ} (hj : j < headIndex F hF shape X J cap) :
    cap < (cell F hF shape X j).card := by
  have hn := Nat.find_min (show ∃ k, J ≤ k ∨ (cell F hF shape X k).card ≤ cap from ⟨J,Or.inl le_rfl⟩) hj
  exact lt_of_not_ge (fun hh => hn (Or.inr hh))

lemma head_length_bound (J cap : ℕ) : headIndex F hF shape X J cap * cap ≤ X.card :=
  prefix_length_bound F hF shape X _ _ (fun _ hj => (before_head F hF shape X J cap hj).le)

lemma head_tail_cap (J cap : ℕ) (a : I) (ha : a ∈ F) :
    ((remaining F hF shape X (headIndex F hF shape X J cap) \ remaining F hF shape X J) ∩ shape a).card ≤ cap := by
  have hs := Nat.find_spec (show ∃ k, J ≤ k ∨ (cell F hF shape X k).card ≤ cap from ⟨J,Or.inl le_rfl⟩)
  rcases hs with h | h
  · have he : headIndex F hF shape X J cap = J := le_antisymm (headIndex_le F hF shape X J cap) h
    simp [he]
  · exact tail_cap F hF shape X _ cap h _ Finset.sdiff_subset a ha

lemma firstAt_mem (J : ℕ) (x : V) (h : firstAt F hF shape X J x < J) :
    x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) := by
  have hs := Nat.find_spec (show ∃ j, J ≤ j ∨ x ∈ shape (chosen F hF shape X j) from ⟨J,Or.inl le_rfl⟩)
  change J ≤ firstAt F hF shape X J x ∨ x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) at hs
  exact hs.resolve_left (not_le_of_gt h)

lemma firstAt_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    firstAt F hF shape X J x = j := by
  apply le_antisymm
  · exact Nat.find_min' _ (Or.inr hxj)
  · by_contra hn
    have hlt : firstAt F hF shape X J x < j := by omega
    exact hearlier _ hlt (firstAt_mem F hF shape X J x (hlt.trans hj))

lemma ownCell_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    ownCell F hF shape X J x = cell F hF shape X j := by
  rw [ownCell, firstAt_eq F hF shape X J j x hj hxj hearlier, ite_eq_left hj]

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Nonpairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SkewPairCounting
open scoped BigOperators
variable {I : Type*} [DecidableEq I]

lemma card_nonpairs (R : I → I → Prop) [DecidableRel R] (S : Finset I) :
    (nonpairs R S).card = ∑ x ∈ S, (S.filter fun y => x ≠ y ∧ ¬R x y).card := by
  simp only [nonpairs, Finset.card_filter, Finset.sum_product]

lemma nonpairs_mono (R : I → I → Prop) [DecidableRel R] {S T : Finset I}
    (h : S ⊆ T) : nonpairs R S ⊆ nonpairs R T :=
  Finset.filter_subset_filter _ (Finset.product_subset_product h h)

lemma row_partition (R : I → I → Prop) [DecidableRel R] (hR : ∀ x, ¬R x x)
    (S : Finset I) {x : I} (hx : x ∈ S) :
    (S.filter fun y => x ≠ y ∧ ¬R x y).card + (S.filter (R x)).card + 1 = S.card := by
  have he : (S.filter fun y => ¬R x y).erase x = S.filter fun y => x ≠ y ∧ ¬R x y := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_filter]
    tauto
  have hm : x ∈ S.filter fun y => ¬R x y := by simp [hx, hR x]
  have hc := Finset.card_erase_add_one hm
  rw [he] at hc
  have hp := Finset.card_filter_add_card_filter_not (s := S) (R x)
  omega

lemma sq_card_bound (R : I → I → Prop) [DecidableRel R] (hR : ∀ x, ¬R x x)
    (S : Finset I) (D : ℝ)
    (hD : ∀ x ∈ S, ((S.filter (R x)).card : ℝ) ≤ D) :
    (S.card : ℝ)^2 ≤ (nonpairs R S).card + S.card * (D+1) := by
  have hrow (x : I) (hx : x ∈ S) :
      (S.card : ℝ) ≤ (S.filter fun y => x ≠ y ∧ ¬R x y).card + (D+1) := by
    have hp : ((S.filter fun y => x ≠ y ∧ ¬R x y).card : ℝ) +
        (S.filter (R x)).card + 1 = S.card := by exact_mod_cast row_partition R hR S hx
    linarith [hD x hx]
  have hsum := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib,
    ← Nat.cast_sum, ← card_nonpairs] at hsum
  nlinarith

theorem many_nonpairs (R : I → I → Prop) [DecidableRel R]
    (hR : ∀ x, ¬R x x) (S : Finset I) (c : ℕ)
    (hc : ∀ x ∈ S, ∀ y ∈ S, R x y →
      (S.filter fun z => R x z ∧ R y z).card ≤ c)
    (hsize : 8*(c+1) ≤ S.card) :
    (S.card : ℝ)^2 ≤ 16*(nonpairs R S).card := by
  have hsz : 8*((c:ℝ)+1) ≤ S.card := by exact_mod_cast hsize
  by_cases hhigh : ∃ x ∈ S, (S.card:ℝ)/2 ≤ (S.filter (R x)).card
  · obtain ⟨x, hx, hd⟩ := hhigh
    let T := S.filter (R x)
    have hT : T ⊆ S := Finset.filter_subset _ _
    have hdeg (y : I) (hy : y ∈ T) : ((T.filter (R y)).card:ℝ) ≤ c := by
      have hy' := Finset.mem_filter.mp hy
      have he : T.filter (R y) = S.filter fun z => R x z ∧ R y z := by
        simp only [T, Finset.filter_filter]
      rw [he]
      exact_mod_cast hc x hx y hy'.1 hy'.2
    have hloc := sq_card_bound R hR T c hdeg
    have hm : ((nonpairs R T).card:ℝ) ≤ (nonpairs R S).card := by
      exact_mod_cast Finset.card_le_card (nonpairs_mono R hT)
    have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg _
    have ht0 : (0:ℝ) ≤ T.card := Nat.cast_nonneg _
    have hd' : (S.card:ℝ)/2 ≤ T.card := hd
    nlinarith [sq_nonneg ((T.card:ℝ)-(S.card:ℝ)/2),
      mul_nonneg (show 0 ≤ (T.card:ℝ)-2*((c:ℝ)+1) by linarith) ht0]
  · have hd (x : I) (hx : x ∈ S) : ((S.filter (R x)).card:ℝ) ≤ (S.card:ℝ)/2 := by
      have : ¬ (S.card:ℝ)/2 ≤ (S.filter (R x)).card := fun h => hhigh ⟨x,hx,h⟩
      exact (lt_of_not_ge this).le
    have hg := sq_card_bound R hR S ((S.card:ℝ)/2) hd
    have hn0 : (0:ℝ) ≤ (nonpairs R S).card := Nat.cast_nonneg _
    nlinarith [show (0:ℝ) ≤ c from Nat.cast_nonneg c, sq_nonneg ((S.card:ℝ)-4)]

end SharpRamseyFive.SkewPairCounting

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighParameters
open scoped BigOperators

lemma threshold_bounds {q n a : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a) (ha2 : a≤2)
    (hhigh : 2097152*q^2≤n*a^2) :
    n*a/(128*q) ≤ (threshold q n a:ℝ) ∧
    (threshold q n a:ℝ) ≤ n*a/(64*q) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hna : 1048576*q^2≤n*a := by
    have haa : a^2≤2*a := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left haa hn.le]
  have hx : 2≤n*a/(64*q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (q-1)]
  have hf := Nat.lt_floor_add_one (n*a/(64*q))
  have hfloor : n*a/(128*q)≤(threshold q n a:ℝ) := by
    dsimp [threshold]
    have he : n*a/(128*q)=(n*a/(64*q))/2 := by ring
    rw [he]
    linarith
  exact ⟨hfloor,Nat.floor_le (by positivity)⟩

lemma cap_bounds {q a : ℝ} (hq : 1≤q) (ha : 0<a) (ha2 : a≤2) :
    1024*q^2/a ≤ (cap q a:ℝ) ∧ (cap q a:ℝ) ≤ 2048*q^2/a := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hb : 1≤1024*q^2/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith [sq_nonneg (q-1)]
  refine ⟨Nat.le_ceil _,?_⟩
  have hc := Nat.ceil_lt_add_one (show 0≤1024*q^2/a by positivity)
  have he : 2048*q^2/a=2*(1024*q^2/a) := by ring
  rw [he]
  dsimp [cap,multiplicity]
  linarith

lemma multiplicity_bounds {q n a : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hnq : n^2≤100*q^5) :
    134217728*q^6/(n^2*a^3) ≤ (multiplicity q n a:ℝ) ∧
    (multiplicity q n a:ℝ) ≤ 268435456*q^6/(n^2*a^3) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have ha3 : a^3≤8 := by nlinarith [pow_le_pow_left₀ ha.le ha2 3]
  have hden : n^2*a^3 ≤ 800*q^5 := by
    calc _ ≤ (100*q^5)*8 := mul_le_mul hnq ha3 (by positivity) (by positivity)
         _ = _ := by ring
  have hb : 1≤134217728*q^6/(n^2*a^3) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have : q^5≤q^6 := by simpa only [pow_succ,mul_one] using mul_le_mul_of_nonneg_left hq (pow_nonneg hq0.le 5)
    nlinarith [pow_pos hq0 5]
  refine ⟨Nat.le_ceil _,?_⟩
  have hc := Nat.ceil_lt_add_one (show 0≤134217728*q^6/(n^2*a^3) by positivity)
  have he : 268435456*q^6/(n^2*a^3)=2*(134217728*q^6/(n^2*a^3)) := by ring
  rw [he]
  dsimp [cap,multiplicity]
  linarith

theorem high_budget_conditions {q n a : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hnq : n^2≤100*q^5) (hhigh : 2097152*q^2≤n*a^2) :
    0<threshold q n a ∧
    2*(q+1)≤(threshold q n a:ℝ) ∧
    2*n≤(multiplicity q n a:ℝ)*(threshold q n a:ℝ) ∧
    2*(cap q a:ℝ)/q≤(threshold q n a:ℝ) ∧
    4*q^2*(cap q a:ℝ)≤(multiplicity q n a:ℝ)*(threshold q n a:ℝ)^2 ∧
    64*n≤(threshold q n a:ℝ)^2 := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  obtain ⟨hM,hM'⟩ := threshold_bounds hq hn ha ha2 hhigh
  obtain ⟨hcap,hcap'⟩ := cap_bounds hq ha ha2
  obtain ⟨hu,hu'⟩ := multiplicity_bounds hq hn ha ha2 hnq
  have hM0 : (0:ℝ)<threshold q n a := (by positivity : 0<n*a/(128*q)).trans_le hM
  have hm2 : (n*a/(128*q))^2≤(threshold q n a:ℝ)^2 := pow_le_pow_left₀ (by positivity) hM 2
  have hna : 1048576*q^2≤n*a := by
    nlinarith [mul_le_mul_of_nonneg_left (show a^2≤2*a by nlinarith) hn.le]
  refine ⟨by exact_mod_cast hM0,?_,?_,?_,?_,?_⟩
  · apply le_trans _ hM
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (q-1)]
  · calc
      _ ≤ (134217728*q^6/(n^2*a^3))*(n*a/(128*q)) := by
        have he : (134217728*q^6/(n^2*a^3))*(n*a/(128*q)) =
            1048576*q^5/(n*a^2) := by field_simp; ring
        rw [he]
        apply (le_div_iff₀ (by positivity)).mpr
        have hna2 : n^2*a^2≤400*q^5 := by
          calc _ ≤ (100*q^5)*4 := mul_le_mul hnq
                 (show a^2≤4 by nlinarith) (by positivity) (by positivity)
               _ = _ := by ring
        nlinarith [pow_pos hq0 5]
      _ ≤ _ := mul_le_mul hu hM (by positivity) (by positivity)
  · calc
      _ ≤ 2*(2048*q^2/a)/q := div_le_div_of_nonneg_right (by nlinarith) hq0.le
      _ ≤ n*a/(128*q) := by
        have he : 2*(2048*q^2/a)/q=4096*q/a := by field_simp; ring
        rw [he]
        apply (div_le_div_iff₀ ha (by positivity)).mpr
        nlinarith
      _ ≤ _ := hM
  · calc
      _ ≤ 4*q^2*(2048*q^2/a) := mul_le_mul_of_nonneg_left hcap' (by positivity)
      _ = (134217728*q^6/(n^2*a^3))*(n*a/(128*q))^2 := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul hu hm2 (by positivity) (by positivity)
  · apply le_trans _ hm2
    rw [div_pow]
    apply (le_div_iff₀ (show 0<(128*q)^2 by positivity)).mpr
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn.le]

lemma head_length_condition {q n a j : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hhigh : 2097152*q^2≤n*a^2) (hj : 0≤j)
    (hjn : j*(cap q a:ℝ)≤n) : j*(q+1)≤(threshold q n a:ℝ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hM := (threshold_bounds hq hn ha ha2 hhigh).1
  have hc := (cap_bounds hq ha ha2).1
  have hjn' : j*(1024*q^2/a)≤n := (mul_le_mul_of_nonneg_left hc hj).trans hjn
  calc
    _ ≤ j*(2*q) := mul_le_mul_of_nonneg_left (by linarith) hj
    _ = (j*(1024*q^2/a))*(a/(512*q)) := by field_simp; ring
    _ ≤ n*(a/(512*q)) := mul_le_mul_of_nonneg_right hjn' (by positivity)
    _ ≤ n*a/(128*q) := by
      have he : n*(a/(512*q))=(n*a/(128*q))/4 := by ring
      rw [he]
      have : 0≤n*a/(128*q) := by positivity
      linarith
    _ ≤ _ := hM

lemma degree_multiplicity_condition {q n a χ : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a) (ha2 : a≤2) (hnq : n^2≤100*q^5) (hχ : 0≤χ) :
    8*(2*multiplicity q n a+1)≤degree q n a χ := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  obtain ⟨hu,hu'⟩ := multiplicity_bounds hq hn ha ha2 hnq
  let u₀ := 134217728*q^6/(n^2*a^3)
  have hu₀ : 0<u₀ := by dsimp [u₀]; positivity
  have huN : (0:ℝ)<(multiplicity q n a:ℝ) := hu₀.trans_le hu
  have hu1 : (1:ℝ)≤ multiplicity q n a := by exact_mod_cast (show 1≤ multiplicity q n a by exact_mod_cast huN)
  have hu'₀ : (multiplicity q n a:ℝ)≤2*u₀ := by dsimp [u₀]; convert hu' using 1; ring
  have hd := Nat.le_ceil (34359738368*q^6/(n^2*a^4)*Real.exp χ)
  have hexp : 1≤Real.exp χ := Real.one_le_exp_iff.mpr hχ
  have hd' : 128*u₀≤(degree q n a χ:ℝ) := by
    apply le_trans _ hd
    have he : 34359738368*q^6/(n^2*a^4)*Real.exp χ=256*u₀*Real.exp χ/a := by
      dsimp [u₀]
      field_simp
      ring
    rw [he]
    apply (le_div_iff₀ ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left hexp hu₀.le]
  have hh : (8:ℝ)*(2*(multiplicity q n a:ℝ)+1)≤(degree q n a χ:ℝ) := by linarith
  exact_mod_cast hh

theorem tail_exception_bound {q n a χ e : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a) (ha2 : a≤2) (hnq : n^2≤100*q^5)
    (hhigh : 2097152*q^2≤n*a^2) (he : 0≤e)
    (hbudget : e*(degree q n a χ:ℝ)^2*(threshold q n a:ℝ)^2 ≤
      4096*n^2*(2*(multiplicity q n a:ℝ)+1)^2) :
    e≤36864*q^2*Real.exp (-(2*χ)) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  let u₀ := 134217728*q^6/(n^2*a^3)
  let M₀ := n*a/(128*q)
  let D₀ := 256*u₀*Real.exp χ/a
  have hu₀ : 0<u₀ := by dsimp [u₀]; positivity
  have hM₀ : 0<M₀ := by dsimp [M₀]; positivity
  have hD₀ : 0<D₀ := by dsimp [D₀]; positivity
  obtain ⟨hu,hu'⟩ := multiplicity_bounds hq hn ha ha2 hnq
  have hu'₀ : (multiplicity q n a:ℝ)≤2*u₀ := by
    dsimp [u₀]
    convert hu' using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have huN : (0:ℝ)<(multiplicity q n a:ℝ) := hu₀.trans_le hu
  have hu1 : (1:ℝ)≤ multiplicity q n a := by
    exact_mod_cast (show 1≤ multiplicity q n a by exact_mod_cast huN)
  have hM : M₀≤(threshold q n a:ℝ) := (threshold_bounds hq hn ha ha2 hhigh).1
  have hD : D₀≤(degree q n a χ:ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    dsimp [D₀,u₀,degree]
    apply le_of_eq
    field_simp
    ring
  have h2u : 2*(multiplicity q n a:ℝ)+1≤6*u₀ := by linarith
  have hnum : 4096*n^2*(2*(multiplicity q n a:ℝ)+1)^2≤4096*n^2*(6*u₀)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2u 2) (by positivity)
  have hden : D₀^2*M₀^2≤(degree q n a χ:ℝ)^2*(threshold q n a:ℝ)^2 :=
    mul_le_mul (pow_le_pow_left₀ hD₀.le hD 2) (pow_le_pow_left₀ hM₀.le hM 2)
      (by positivity) (by positivity)
  have hh : e*(D₀^2*M₀^2)≤4096*n^2*(6*u₀)^2 := by
    calc
      _ ≤ e*((degree q n a χ:ℝ)^2*(threshold q n a:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hden he
      _ ≤ _ := by nlinarith [hbudget.trans hnum]
  calc
    e ≤ (4096*n^2*(6*u₀)^2)/(D₀^2*M₀^2) :=
      (le_div_iff₀ (by positivity)).mpr hh
    _ = _ := by
      dsimp [D₀,M₀]
      rw [Real.exp_neg,show 2*χ=χ+χ by ring,Real.exp_add]
      field_simp
      ring

lemma head_mean_condition {q n a r : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hhigh : 2097152*q^2≤n*a^2) (hr : r≤1/q) :
    2*r*(n*a/1024)≤(threshold q n a:ℝ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hM := (threshold_bounds hq hn ha ha2 hhigh).1
  calc
    _ ≤ 2*(1/q)*(n*a/1024) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (n*a/(128*q))/4 := by ring
    _ ≤ n*a/(128*q) := by
      have : 0≤n*a/(128*q) := by positivity
      linarith
    _ ≤ _ := hM

lemma tail_mean_condition {q n a r : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hnq : n^2≤100*q^5) (hhigh : 2097152*q^2≤n*a^2) (hr : r≤1/q) :
    2*r*(cap q a:ℝ)≤(threshold q n a:ℝ) := by
  have hh := (high_budget_conditions hq hn ha ha2 hnq hhigh).2.2.2.1
  have hcap : (0:ℝ) ≤ cap q a := Nat.cast_nonneg _
  calc
    _ ≤ 2*(1/q)*(cap q a:ℝ) := mul_le_mul_of_nonneg_right (by linarith) hcap
    _ = 2*(cap q a:ℝ)/q := by ring
    _ ≤ _ := hh

lemma large_exception_bound {q n a e : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a)
    (hbudget : e*(n*a/1024)^2≤(q^2+q+1)*n^2) : e≤3145728*q^2/a^2 := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hqQ : q^2+q+1≤3*q^2 := by nlinarith [sq_nonneg (q-1)]
  have hh : e*(n*a/1024)^2≤3*q^2*n^2 :=
    hbudget.trans (mul_le_mul_of_nonneg_right hqQ (sq_nonneg n))
  calc
    e ≤ (3*q^2*n^2)/(n*a/1024)^2 := (le_div_iff₀ (by positivity)).mpr hh
    _ = _ := by field_simp; ring

lemma head_exception_bound {q n a χ j e : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a) (ha2 : a≤2) (hhigh : 2097152*q^2≤n*a^2) (he : 0≤e) (hj : 0≤j)
    (hjn : j*(cap q a:ℝ)≤n)
    (hbudget : e*(degree q n a χ:ℝ)*(threshold q n a:ℝ)^2≤4*q^2*(q+1)*j*n) :
    e≤(n^2*a^3/q^3)*Real.exp (-χ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  let D₀ := 34359738368*q^6/(n^2*a^4)*Real.exp χ
  let M₀ := n*a/(128*q)
  have hD₀ : 0<D₀ := by dsimp [D₀]; positivity
  have hM₀ : 0<M₀ := by dsimp [M₀]; positivity
  have hD : D₀≤(degree q n a χ:ℝ) := Nat.le_ceil _
  have hM : M₀≤(threshold q n a:ℝ) := (threshold_bounds hq hn ha ha2 hhigh).1
  have hcap := (cap_bounds hq ha ha2).1
  have hj' : j≤n*a/(1024*q^2) := by
    have hh : j*(1024*q^2/a)≤n := (mul_le_mul_of_nonneg_left hcap hj).trans hjn
    have hh' := (le_div_iff₀ (show 0<1024*q^2/a by positivity)).mpr hh
    calc
      j ≤ n / (1024*q^2/a) := hh'
      _ = _ := div_div_eq_mul_div _ _ _
  have hnum : 4*q^2*(q+1)*j*n≤n^2*a*q/128 := by
    calc
      _ ≤ 4*q^2*(2*q)*j*n := by gcongr; linarith
      _ ≤ 4*q^2*(2*q)*(n*a/(1024*q^2))*n := by gcongr
      _ = _ := by field_simp; ring
  have hden : D₀*M₀^2≤(degree q n a χ:ℝ)*(threshold q n a:ℝ)^2 :=
    mul_le_mul hD (pow_le_pow_left₀ hM₀.le hM 2) (by positivity) (by positivity)
  have hh : e*(D₀*M₀^2)≤n^2*a*q/128 := by
    calc
      _ ≤ e*((degree q n a χ:ℝ)*(threshold q n a:ℝ)^2) := mul_le_mul_of_nonneg_left hden he
      _ ≤ _ := by nlinarith [hbudget.trans hnum]
  calc
    e ≤ (n^2*a*q/128)/(D₀*M₀^2) := (le_div_iff₀ (by positivity)).mpr hh
    _ = ((n^2*a^3/q^3)*Real.exp (-χ))/268435456 := by
      dsimp [D₀,M₀]
      rw [Real.exp_neg]
      field_simp
      ring
    _ ≤ _ := by
      have : 0≤(n^2*a^3/q^3)*Real.exp (-χ) := by positivity
      linarith

end SharpRamseyFive.HighParameters

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Training
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

lemma peel_subset (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk ⊆ X := by
  unfold peelSet
  split_ifs
  · exact retained_subset F hF shape X k hk
  · exact Finset.Subset.refl _

lemma peel_alternative (e : Prop) (he : e) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk = X\remaining F hF shape X (peelLength e F hF shape X k hk) ∨
    (peelLength e F hF shape X k hk=0 ∧ ∀i∈F,(peelSet e F hF shape X k hk∩shape i).card<k) := by
  by_cases hc : Captured F hF shape X k hk
  · left
    simp only [peelSet,ite_eq_left he,peelLength,ite_eq_left (And.intro he hc)]
    exact ite_eq_left hc
  · right
    refine ⟨by simp [peelLength,hc],?_⟩
    intro i hi
    simpa only [peelSet,ite_eq_left he] using residual_cap F hF shape X k hk hc i hi

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CommonNeighborDichotomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneOverlap
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem common_neighbor_dichotomy (A B C : Submodule K V)
    (hC : finrank K C = 3) (hAB : finrank K (A ⊓ B : Submodule K V) = 2)
    (hCA : finrank K (C ⊓ A : Submodule K V) = 2)
    (hCB : finrank K (C ⊓ B : Submodule K V) = 2) :
    A ⊓ B ≤ C ∨ C ≤ A ⊔ B := by
  by_cases h : A ⊓ B ≤ C
  · exact Or.inl h
  right
  have hi : C ⊓ (A ⊓ B) < A ⊓ B := lt_of_le_of_ne inf_le_right (by
    intro he
    apply h
    rw [← he]
    exact inf_le_left)
  have hlt := Submodule.finrank_lt_finrank_of_lt hi
  rw [hAB] at hlt
  have he := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ A) (C ⊓ B)
  have hinf : (C ⊓ A) ⊓ (C ⊓ B) = C ⊓ (A ⊓ B) := by
    ext
    simp only [Submodule.mem_inf]
    tauto
  rw [hCA, hCB, hinf] at he
  have hle : (C ⊓ A) ⊔ (C ⊓ B) ≤ C := sup_le inf_le_left inf_le_left
  have hdim := Submodule.finrank_mono hle
  rw [hC] at hdim
  have heq : (C ⊓ A) ⊔ (C ⊓ B) = C :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [← heq]
  exact sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)

theorem finrank_sup_of_plane_intersection (A B : Submodule K V)
    (hA : finrank K A = 3) (hB : finrank K B = 3)
    (hAB : finrank K (A ⊓ B : Submodule K V) = 2) :
    finrank K (A ⊔ B : Submodule K V) = 4 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hA, hB, hAB] at h
  omega

end SharpRamseyFive.RichPlaneOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneCommonNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneOverlap

section
open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
open SharpRamseyFive.SkewPairCounting
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem plane_common_neighbors (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (A B : Submodule K V) (hA : A ∈ F) (hB : B ∈ F)
    (hAB : finrank K (A ⊓ B : Submodule K V) = 2) :
    (F.filter fun C => finrank K (A ⊓ C : Submodule K V) = 2 ∧
      finrank K (B ⊓ C : Submodule K V) = 2).card ≤ 2*u := by
  classical
  have hsub : (F.filter fun C => finrank K (A ⊓ C : Submodule K V) = 2 ∧
      finrank K (B ⊓ C : Submodule K V) = 2) ⊆
      (F.filter fun C => A ⊓ B ≤ C) ∪ (F.filter fun C => C ≤ A ⊔ B) := by
    intro C hC
    obtain ⟨hCF, hCA, hCB⟩ := Finset.mem_filter.mp hC
    have hd := common_neighbor_dichotomy A B C (hF C hCF) hAB
      (by rw [inf_comm]; exact hCA) (by rw [inf_comm]; exact hCB)
    simpa only [Finset.mem_union, Finset.mem_filter, hCF, true_and] using hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := hline (A ⊓ B) hAB
  have h2 := hhyper (A ⊔ B) (finrank_sup_of_plane_intersection A B (hF A hA) (hF B hB) hAB)
  omega

theorem inf_eq_point_of_not_line (x : ℙ K V) (A B : Submodule K V)
    (hA : finrank K A = 3) (hB : finrank K B = 3) (hAB : A ≠ B)
    (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B)
    (hnot : finrank K (A ⊓ B : Submodule K V) ≠ 2) : A ⊓ B = x.submodule := by
  have hle : x.submodule ≤ A ⊓ B := le_inf hxA hxB
  have hge := Submodule.finrank_mono hle
  rw [x.finrank_submodule] at hge
  have hlt : A ⊓ B < A := lt_of_le_of_ne inf_le_left (by
    intro he
    have hab : A ≤ B := he ▸ inf_le_right
    exact hAB (Submodule.eq_of_le_of_finrank_eq hab (hA.trans hB.symm)))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hA] at hd
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [x.finrank_submodule]; omega)).symm

theorem local_skew_pairs (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (x : ℙ K V)
    (hsize : 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card) :
    ((F.filter fun A => x.submodule ≤ A).card : ℝ)^2 ≤
      16 * ((F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule).card := by
  classical
  let S := F.filter fun A => x.submodule ≤ A
  let R (A B : Submodule K V) := A ≠ B ∧ finrank K (A ⊓ B : Submodule K V) = 2
  have hc (A : Submodule K V) (hA : A ∈ S) (B : Submodule K V) (hB : B ∈ S)
      (hAB : R A B) : (S.filter fun C => R A C ∧ R B C).card ≤ 2*u := by
    apply (Finset.card_le_card ?_).trans
      (plane_common_neighbors F hF u hline hhyper A B
        (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 hAB.2)
    intro C hC
    obtain ⟨hCS, hAC, hBC⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hCS).1,hAC.2,hBC.2⟩
  have hm := many_nonpairs R (fun A h => h.1 rfl) S (2*u) hc hsize
  have hsub : nonpairs R S ⊆
      (F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule := by
    rintro ⟨A,B⟩ hp
    obtain ⟨hmem, hne,hnot⟩ := Finset.mem_filter.mp hp
    obtain ⟨hAS,hBS⟩ := Finset.mem_product.mp hmem
    obtain ⟨hAF, hxA⟩ := Finset.mem_filter.mp hAS
    obtain ⟨hBF, hxB⟩ := Finset.mem_filter.mp hBS
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hAF,hBF⟩,hne,?_⟩
    exact inf_eq_point_of_not_line x A B (hF A hAF) (hF B hBF) hne hxA hxB
      (fun h => hnot ⟨hne,h⟩)
  have hmc : ((nonpairs R S).card:ℝ) ≤
      ((F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hm.trans (mul_le_mul_of_nonneg_left hmc (by norm_num))

end

open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in

theorem sum_point_pairs_le (F : Finset (Submodule K V)) (X : Finset (ℙ K V)) :
    ∑ x ∈ X, ((F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule).card
      ≤ F.card^2 := by
  let P (x : ℙ K V) := (F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule
  have hd : (X : Set (ℙ K V)).PairwiseDisjoint P := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro p hpx hpy
    have h1 := (Finset.mem_filter.mp hpx).2.2
    have h2 := (Finset.mem_filter.mp hpy).2.2
    exact hxy (Projectivization.submodule_injective (h1.symm.trans h2))
  have hsub : X.biUnion P ⊆ F ×ˢ F := by
    intro p hp
    obtain ⟨x,_,hpx⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hpx).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hd, Finset.card_product] at hc
  simpa only [P, pow_two] using hc

theorem high_degree_second_moment (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (X : Finset (ℙ K V)) :
    ∑ x ∈ X.filter (fun x => 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card),
      ((F.filter fun A => x.submodule ≤ A).card:ℝ)^2 ≤ 16*(F.card:ℝ)^2 := by
  let Y := X.filter fun x => 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card
  have hs := Finset.sum_le_sum (s := Y) (fun x hx =>
    local_skew_pairs F hF u hline hhyper x (Finset.mem_filter.mp hx).2)
  have hp : (∑ x ∈ Y,
      (((F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule).card:ℝ)) ≤ (F.card:ℝ)^2 := by
    exact_mod_cast sum_point_pairs_le F Y
  exact hs.trans (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hp (by norm_num))

omit [FiniteDimensional K V] in

theorem plane_point_double_count (F : Finset (Submodule K V)) (X : Finset (ℙ K V)) :
    ∑ x ∈ X, (F.filter fun A => x.submodule ≤ A).card =
      ∑ A ∈ F, (X.filter fun x => x.submodule ≤ A).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem rich_plane_count (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hlarge : 64*X.card ≤ M^2) :
    (F.card:ℝ)*M ≤ 16*X.card*(2*(u:ℝ)+1) := by
  let d (x : ℙ K V) : ℝ := (F.filter fun A => x.submodule ≤ A).card
  let Y := X.filter fun x => 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card
  let Z := X.filter fun x => ¬8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card
  have hsum : (∑ x ∈ Y, d x) + ∑ x ∈ Z, d x = ∑ x ∈ X, d x :=
    Finset.sum_filter_add_sum_filter_not X _ _
  have hlow : (∑ x ∈ Z, d x) ≤ (X.card:ℝ)*(8*(2*(u:ℝ)+1)) := by
    have hl (x : ℙ K V) (hx : x ∈ Z) : d x ≤ 8*(2*(u:ℝ)+1) := by
      have hh := (Finset.mem_filter.mp hx).2
      have hnat : (F.filter fun A => x.submodule ≤ A).card ≤ 8*(2*u+1) := (lt_of_not_ge hh).le
      dsimp [d]
      exact_mod_cast hnat
    have hle := Finset.sum_le_sum hl
    have hsub : Z.card ≤ X.card := Finset.card_le_card (Finset.filter_subset _ _)
    calc
      _ ≤ (Z.card:ℝ)*(8*(2*(u:ℝ)+1)) := by simpa using hle
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) (by positivity)
  have htotal : (F.card:ℝ)*M ≤ ∑ x ∈ X, d x := by
    have hs := Finset.sum_le_sum hM
    simp only [Finset.sum_const_nat, ← plane_point_double_count] at hs
    dsimp [d]
    exact_mod_cast hs
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ => (1:ℝ)) d
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsecond := high_degree_second_moment F hF u hline hhyper X
  have hY : (Y.card:ℝ) ≤ X.card := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hsq : (∑ x ∈ Y, d x)^2 ≤ 16*(X.card:ℝ)*(F.card:ℝ)^2 := by
    calc
      _ ≤ (Y.card:ℝ)*∑ x ∈ Y, d x^2 := hcs
      _ ≤ (Y.card:ℝ)*(16*(F.card:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hsecond (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hY (sq_nonneg (F.card:ℝ))]
  have hr : (0:ℝ) ≤ (F.card:ℝ)*M := by positivity
  have hs0 : 0 ≤ ∑ x ∈ Y, d x := Finset.sum_nonneg (fun x _ => Nat.cast_nonneg _)
  have hlg : 64*(X.card:ℝ) ≤ (M:ℝ)^2 := by exact_mod_cast hlarge
  have hprod := mul_le_mul_of_nonneg_right hlg (sq_nonneg (F.card:ℝ))
  have hhigh : 2*(∑ x ∈ Y, d x) ≤ (F.card:ℝ)*M := by
    nlinarith [sq_nonneg ((F.card:ℝ)*M+2*(∑ x ∈ Y, d x))]
  linarith

end SharpRamseyFive.RichPlaneOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ExceptionalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneOverlap
open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exceptional_centers (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (X : Finset (ℙ K V)) (D : ℕ) (hD : 8*(2*u+1) ≤ D) :
    ((X.filter fun x => D ≤ (F.filter fun A => x.submodule ≤ A).card).card:ℝ)*D^2 ≤
      16*(F.card:ℝ)^2 := by
  let Y := X.filter fun x => D ≤ (F.filter fun A => x.submodule ≤ A).card
  have hsub : Y ⊆ X.filter fun x => 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card := by
    intro x hx
    obtain ⟨hxX,hxD⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxX,hD.trans hxD⟩
  have h1 : (Y.card:ℝ)*D^2 ≤ ∑ x ∈ Y, ((F.filter fun A => x.submodule ≤ A).card:ℝ)^2 := by
    have h := Finset.sum_le_sum (s := Y) (f := fun _ => (D:ℝ)^2)
      (g := fun x => ((F.filter fun A => x.submodule ≤ A).card:ℝ)^2) (by
        intro x hx
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast (Finset.mem_filter.mp hx).2)
    simpa using h
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ =>
    sq_nonneg ((F.filter fun A => x.submodule ≤ A).card:ℝ))
  exact (h1.trans h2).trans (high_degree_second_moment F hF u hline hhyper X)

end SharpRamseyFive.RichPlaneOverlap

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma inf_eq_shared_line {A B L : Submodule K V}
    (hA : finrank K A = 3) (hB : finrank K B = 3) (hL : finrank K L = 2)
    (hAB : A ≠ B) (hLA : L ≤ A) (hLB : L ≤ B) : A ⊓ B = L := by
  have hle : L ≤ A ⊓ B := le_inf hLA hLB
  have he : A ⊓ B < A := lt_of_le_of_ne inf_le_left (by
    intro he
    have hab : A ≤ B := he ▸ inf_le_right
    exact hAB (Submodule.eq_of_le_of_finrank_eq hab (hA.trans hB.symm)))
  have hge := Submodule.finrank_mono hle
  have hlt := Submodule.finrank_lt_finrank_of_lt he
  rw [hA] at hlt
  rw [hL] at hge
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem rich_planes_through_line [Finite K]
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (L : Submodule K V) (hL : finrank K L = 2) :
    (F.filter fun A => L ≤ A).card*M ≤
      X.card + (F.filter fun A => L ≤ A).card*(Nat.card K+1) := by
  let : Finite V := Module.finite_of_finite K
  let G := F.filter fun A => L ≤ A
  let Y := X.filter fun x => x.submodule ≤ L
  let T (A : Submodule K V) := X.filter fun x => x.submodule ≤ A ∧ ¬x.submodule ≤ L
  have hY : Y.card ≤ Nat.card K+1 := by
    have hi : Function.Injective (fun x : Y => (⟨x.val,(Finset.mem_filter.mp x.property).2⟩ :
        {p : ℙ K V // p.submodule ≤ L})) := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : {p : ℙ K V // p.submodule ≤ L} => z.val) he)
    have hc := Nat.card_le_card_of_injective _ hi
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_subspacePoints, hL] at hc
    simpa [Finset.sum_range_succ, add_comm] using hc
  have hdis : (G : Set (Submodule K V)).PairwiseDisjoint T := by
    intro A hA B hB hAB
    obtain ⟨hAF,hLA⟩ := Finset.mem_filter.mp hA
    obtain ⟨hBF,hLB⟩ := Finset.mem_filter.mp hB
    have he := inf_eq_shared_line (hF A hAF) (hF B hBF) hL hAB hLA hLB
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨_,hxAA,hxL⟩ := Finset.mem_filter.mp hxA
    have hxBB := (Finset.mem_filter.mp hxB).2.1
    exact hxL (he ▸ le_inf hxAA hxBB)
  have hunion : G.biUnion T ⊆ X := by
    intro x hx
    obtain ⟨A,_,hxA⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxA).1
  have hsum : ∑ A ∈ G, (T A).card ≤ X.card := by
    rw [← Finset.card_biUnion hdis]
    exact Finset.card_le_card hunion
  have hrow (A : Submodule K V) (hA : A ∈ G) : M ≤ (T A).card + Y.card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := X.filter fun x => x.submodule ≤ A) (fun x => x.submodule ≤ L)
    have hsmall : ((X.filter fun x => x.submodule ≤ A).filter fun x => x.submodule ≤ L).card ≤ Y.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxA,hxL⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxA).1,hxL⟩
    have hn : (X.filter fun x => x.submodule ≤ A).filter (fun x => ¬x.submodule ≤ L) = T A := by
      simp only [T, Finset.filter_filter]
    rw [hn] at hpart
    have hm := hM A (Finset.mem_filter.mp hA).1
    omega
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hs
  have hm := Nat.mul_le_mul_left G.card hY
  dsimp [G] at hm hs hsum
  omega

theorem rich_planes_through_line_twice [Finite K]
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hlarge : 2*(Nat.card K+1) ≤ M)
    (L : Submodule K V) (hL : finrank K L = 2) :
    (F.filter fun A => L ≤ A).card*M ≤ 2*X.card := by
  have h := rich_planes_through_line F hF X M hM L hL
  have hm := Nat.mul_le_mul_left (F.filter fun A => L ≤ A).card hlarge
  nlinarith

lemma ker_dualOfHyperplane {d : ℕ} (hdim : finrank K V = d+1)
    (A : Submodule K V) (hA : finrank K A = d) :
    LinearMap.ker (dualOfHyperplane hdim A hA).rep = A := by
  let b := dualOfHyperplane hdim A hA
  have he : b.submodule = A.dualAnnihilator := Projectivization.submodule_mk'' _ _
  have hmem : b.rep ∈ A.dualAnnihilator := by
    rw [← he, b.submodule_eq]
    exact Submodule.mem_span_singleton_self _
  have hle : A ≤ LinearMap.ker b.rep := by
    intro a ha
    exact ((Submodule.mem_dualAnnihilator b.rep).mp hmem) a ha
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hA]; omega)).symm

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RichHyperplaneVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem rich_hyperplane_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (X : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) (M : ℕ)
    (hM : ∀ b ∈ B, M ≤ (X.filter fun x => Incident x b).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card ≤ M) :
    (B.card:ℝ)*M^2 ≤ 4*(Nat.card K:ℝ)^(d-1)*X.card := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K V) := Fintype.ofFinite _
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let w (x : ℙ K V) : ℝ := if x ∈ X then 1 else 0
  have hw : ∑ x, w x = (X.card:ℝ) := by simp [w]
  have hw2 : ∑ x, w x^2 = (X.card:ℝ) := by simp [w]
  have hweight (b : ℙ K (Module.Dual K V)) :
      weightOnHyperplane w b = ((X.filter fun x => Incident x b).card:ℝ) := by
    simp [weightOnHyperplane, incidenceEntry, w, mul_ite]
  let μ : ℝ := ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card
  have hvariance := incidence_variance hdim hd w
  rw [hw,hw2] at hvariance
  have hrow (b : ℙ K (Module.Dual K V)) (hb : b ∈ B) :
      (M:ℝ)^2 ≤ 4*(weightOnHyperplane w b-μ)^2 := by
    have hm : (M:ℝ) ≤ weightOnHyperplane w b := by rw [hweight]; exact_mod_cast hM b hb
    have hmean' : 2*μ ≤ M := by dsimp [μ]; nlinarith [hmean]
    have hm0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hle : 0 ≤ 2*(weightOnHyperplane w b-μ)-(M:ℝ) := by linarith
    have hge : 0 ≤ 2*(weightOnHyperplane w b-μ)+(M:ℝ) := by linarith
    nlinarith [mul_nonneg hle hge]
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
  have hsub := Finset.sum_le_univ_sum_of_nonneg (s := B)
    (fun b => sq_nonneg (weightOnHyperplane w b-μ))
  have hvar : ∑ b, (weightOnHyperplane w b-μ)^2 ≤ (Nat.card K:ℝ)^(d-1)*X.card := hvariance
  linarith

theorem rich_subspaces_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card ≤ M) :
    (F.card:ℝ)*M^2 ≤ 4*(Nat.card K:ℝ)^(d-1)*X.card := by
  let b (A : F) : ℙ K (Module.Dual K V) := dualOfHyperplane hdim A.val (hF A.val A.property)
  let B := F.attach.image b
  have hi : Function.Injective b := by
    intro A B hAB
    apply Subtype.ext
    have h := congrArg (fun c : ℙ K (Module.Dual K V) => LinearMap.ker c.rep) hAB
    simpa only [b,ker_dualOfHyperplane] using h
  have hBc : B.card = F.card := by simp [B,Finset.card_image_of_injective _ hi]
  have hrich (c : ℙ K (Module.Dual K V)) (hc : c ∈ B) :
      M ≤ (X.filter fun x => Incident x c).card := by
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hc
    simpa only [Incident,b,ker_dualOfHyperplane] using hM A.val A.property
  have h := rich_hyperplane_variance hdim hd X B M hrich hmean
  simpa only [hBc] using h

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma card_pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) :
    (pointsInSubspace H X).card = (X.filter fun p => p.submodule ≤ H).card := by
  simp [pointsInSubspace]

lemma mem_pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) (p : ℙ K H) :
    p ∈ pointsInSubspace H X ↔ ((subspacePointsEquiv H) p).val ∈ X := by
  simp [pointsInSubspace]

lemma subspacePointsEquiv_submodule (H A : Submodule K V) (p : ℙ K H) :
    p.submodule ≤ A.comap H.subtype ↔ ((subspacePointsEquiv H) p).val.submodule ≤ A := by
  induction p using Projectivization.ind with | h v hv =>
  change (Projectivization.mk K v hv).submodule ≤ A.comap H.subtype ↔
    (Projectivization.map H.subtype H.injective_subtype (Projectivization.mk K v hv)).submodule ≤ A
  rw [Projectivization.map_mk, Projectivization.submodule_mk,
    Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem,
    Submodule.span_singleton_le_iff_mem]
  rfl

lemma card_pointsInSubspace_filter (H A : Submodule K V) (hAH : A ≤ H)
    (X : Finset (ℙ K V)) :
    ((pointsInSubspace H X).filter fun p => p.submodule ≤ A.comap H.subtype).card =
      (X.filter fun p => p.submodule ≤ A).card := by
  apply Finset.card_bij (fun p _ => ((subspacePointsEquiv H) p).val)
  · intro p hp
    obtain ⟨hpX,hpA⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(mem_pointsInSubspace H X p).mp hpX,
      (subspacePointsEquiv_submodule H A p).mp hpA⟩
  · intro p hp q hq hpq
    exact (subspacePointsEquiv H).injective (Subtype.ext hpq)
  · intro p hp
    obtain ⟨hpX,hpA⟩ := Finset.mem_filter.mp hp
    let z : {p : ℙ K V // p.submodule ≤ H} := ⟨p,hpA.trans hAH⟩
    refine ⟨(subspacePointsEquiv H).symm z, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · rw [mem_pointsInSubspace, Equiv.apply_symm_apply]
        exact hpX
      · rw [subspacePointsEquiv_submodule, Equiv.apply_symm_apply]
        exact hpA
    · simp [z]

lemma comap_subtype_finrank [FiniteDimensional K V] (H A : Submodule K V) (hAH : A ≤ H) :
    finrank K (A.comap H.subtype) = finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq H, Submodule.map_comap_subtype, inf_eq_right.mpr hAH]

lemma comap_subtype_injOn (H : Submodule K V) :
    Set.InjOn (fun A : Submodule K V => A.comap H.subtype) {A | A ≤ H} := by
  intro A hA B hB hAB
  change A ≤ H at hA
  change B ≤ H at hB
  have he := congrArg (fun W : Submodule K H => W.map H.subtype) hAB
  simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr hA, inf_eq_right.mpr hB] using he

theorem rich_hyperplanes_inside_subspace [FiniteDimensional K V] [Finite K]
    {d : ℕ} (hd : 1 ≤ d) (H : Submodule K V) (hH : finrank K H = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*
      (X.filter fun p => p.submodule ≤ H).card ≤ M) :
    ((F.filter fun A => A ≤ H).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)^(d-1)*(X.filter fun p => p.submodule ≤ H).card := by
  let G := F.filter fun A => A ≤ H
  let FH := G.image (fun A => A.comap H.subtype)
  have hc : FH.card = G.card := Finset.card_image_iff.mpr (by
    intro A hA B hB he
    exact comap_subtype_injOn H (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2 he)
  have hdimF (A : Submodule K H) (hA : A ∈ FH) : finrank K A = d := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [comap_subtype_finrank H B (Finset.mem_filter.mp hB).2]
    exact hF B (Finset.mem_filter.mp hB).1
  have hm (A : Submodule K H) (hA : A ∈ FH) :
      M ≤ ((pointsInSubspace H X).filter fun p => p.submodule ≤ A).card := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [card_pointsInSubspace_filter H B (Finset.mem_filter.mp hB).2]
    exact hM B (Finset.mem_filter.mp hB).1
  have hμ : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(pointsInSubspace H X).card ≤ M := by
    simpa only [card_pointsInSubspace] using hmean
  have hh := rich_subspaces_variance hH hd FH hdimF (pointsInSubspace H X) M hm hμ
  simpa only [hc, card_pointsInSubspace] using hh

theorem rich_planes_inside_hyperplane [FiniteDimensional K V] [Finite K]
    (H : Submodule K V) (hH : finrank K H = 4)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) 2:ℝ)/Q (Nat.card K) 3)*
      (X.filter fun p => p.submodule ≤ H).card ≤ M) :
    ((F.filter fun A => A ≤ H).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)^2*(X.filter fun p => p.submodule ≤ H).card := by
  exact rich_hyperplanes_inside_subspace (by omega : 1 ≤ (3:ℕ)) H hH F hF X M hM hmean

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MultiplicityBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.RichPlaneOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem multiplicity_budgets
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M Kp u : ℕ) (hMpos : 0 < M)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hpointcap : ∀ H : Submodule K V, finrank K H = 4 →
      (X.filter fun x => x.submodule ≤ H).card ≤ Kp)
    (hlineLarge : 2*(Nat.card K+1) ≤ M)
    (hlineNum : 2*X.card ≤ u*M)
    (hmean : 2*((Q (Nat.card K) 2:ℝ)/Q (Nat.card K) 3)*Kp ≤ M)
    (hhyperNum : 4*(Nat.card K:ℝ)^2*Kp ≤ (u:ℝ)*M^2) :
    (∀ L : Submodule K V, finrank K L = 2 → (F.filter fun A => L ≤ A).card ≤ u) ∧
    (∀ H : Submodule K V, finrank K H = 4 → (F.filter fun A => A ≤ H).card ≤ u) := by
  constructor
  · intro L hL
    have hh := (rich_planes_through_line_twice F hF X M hM hlineLarge L hL).trans hlineNum
    exact Nat.le_of_mul_le_mul_right hh hMpos
  · intro H hH
    have hcap : ((X.filter fun x => x.submodule ≤ H).card:ℝ) ≤ Kp := by exact_mod_cast hpointcap H hH
    have hμ : 2*((Q (Nat.card K) 2:ℝ)/Q (Nat.card K) 3)*
        (X.filter fun x => x.submodule ≤ H).card ≤ M :=
      (mul_le_mul_of_nonneg_left hcap (by positivity)).trans hmean
    have hv := rich_planes_inside_hyperplane H hH F hF X M hM hμ
    have hnum := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 4*(Nat.card K:ℝ)^2)
    have hc : ((F.filter fun A => A ≤ H).card:ℝ)*M^2 ≤ (u:ℝ)*M^2 :=
      hv.trans (hnum.trans hhyperNum)
    have hpos : (0:ℝ) < (M:ℝ)^2 := by positivity
    exact_mod_cast (mul_le_mul_iff_left₀ hpos).mp hc

theorem capped_rich_plane_count
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M Kp u : ℕ) (hMpos : 0 < M)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hpointcap : ∀ H : Submodule K V, finrank K H = 4 →
      (X.filter fun x => x.submodule ≤ H).card ≤ Kp)
    (hlineLarge : 2*(Nat.card K+1) ≤ M)
    (hlineNum : 2*X.card ≤ u*M)
    (hmean : 2*((Q (Nat.card K) 2:ℝ)/Q (Nat.card K) 3)*Kp ≤ M)
    (hhyperNum : 4*(Nat.card K:ℝ)^2*Kp ≤ (u:ℝ)*M^2)
    (hlarge : 64*X.card ≤ M^2) :
    (F.card:ℝ)*M ≤ 16*X.card*(2*(u:ℝ)+1) := by
  obtain ⟨hl,hh⟩ := multiplicity_budgets F hF X M Kp u hMpos hM hpointcap
    hlineLarge hlineNum hmean hhyperNum
  exact rich_plane_count F hF u hl hh X M hM hlarge

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CardFilterContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma card_filter_containment_le (X : Finset (ℙ K V)) (A : Submodule K V) :
    (X.filter fun x => x.submodule ≤ A).card ≤ ∑ i ∈ Finset.range (finrank K A), Nat.card K^i := by
  let : Finite V := Module.finite_of_finite K
  let Y := X.filter fun x => x.submodule ≤ A
  have hi : Function.Injective (fun x : Y => (⟨x.val,(Finset.mem_filter.mp x.property).2⟩ :
      {p : ℙ K V // p.submodule ≤ A})) := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : {p : ℙ K V // p.submodule ≤ A} => z.val) he)
  have hc := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_subspacePoints] at hc
  exact hc

lemma card_filter_finrank_le_two (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A ≤ 2) :
    (X.filter fun x => x.submodule ≤ A).card ≤ Nat.card K+1 := by
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hA)
    (f := fun i => Nat.card K^i) (by intros; exact Nat.zero_le _)
  have hc := (card_filter_containment_le X A).trans hle
  simpa [Finset.sum_range_succ,add_comm] using hc

omit [Finite K] in
lemma finrank_inf_lt_of_not_le (A H : Submodule K V) (hn : ¬A ≤ H) :
    finrank K (A ⊓ H : Submodule K V) < finrank K A := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro he
  exact hn (he ▸ inf_le_right)

lemma plane_noncontaining_flat_cap (X : Finset (ℙ K V)) (A H : Submodule K V)
    (hA : finrank K A = 3) (hn : ¬A ≤ H) :
    (X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ H).card ≤ Nat.card K+1 := by
  have hh := finrank_inf_lt_of_not_le A H hn
  rw [hA] at hh
  simpa only [le_inf_iff] using card_filter_finrank_le_two X (A ⊓ H) (by omega)

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma mem_flatPoints (A : Submodule K V) (x : ℙ K V) :
    x ∈ flatPoints A ↔ x.submodule ≤ A := by
  simp [flatPoints]

lemma inter_flatPoints (X : Finset (ℙ K V)) (A : Submodule K V) :
    X ∩ flatPoints A = X.filter fun x => x.submodule ≤ A := by
  ext x
  simp only [Finset.mem_inter,mem_flatPoints,Finset.mem_filter]

lemma plane_covered_cap {I : Type*} [DecidableEq I] (T : Finset I)
    (P : I → Submodule K V) (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A = 3) (hn : ∀ i ∈ T, ¬A ≤ P i)
    (hcover : ∀ x ∈ X, x.submodule ≤ A → ∃ i ∈ T, x.submodule ≤ P i) :
    (X.filter fun x => x.submodule ≤ A).card ≤ T.card*(Nat.card K+1) := by
  let Y (i : I) := X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ P i
  have hsub : X.filter (fun x => x.submodule ≤ A) ⊆ T.biUnion Y := by
    intro x hx
    obtain ⟨hxX,hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨i,hi,hxi⟩ := hcover x hxX hxA
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hxX,hxA,hxi⟩⟩
  have hsum : ∑ i ∈ T, (Y i).card ≤ ∑ _i ∈ T, (Nat.card K+1) :=
    Finset.sum_le_sum (fun i hi => plane_noncontaining_flat_cap X A (P i) hA (hn i hi))
  exact (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans (by simpa using hsum))

variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma captured_cover (J : ℕ) (x : ℙ K V)
    (hx : x ∈ X \ remaining F hF (fun i => flatPoints (P i)) X J) :
    ∃ j ∈ Finset.range J, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  rw [remaining_eq_sdiff_union] at hx
  have hxnot := (Finset.mem_sdiff.mp hx).2
  have hxX := (Finset.mem_sdiff.mp hx).1
  have hm : x ∈ (Finset.range J).biUnion (fun j => flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X j))) := by
    by_contra hn
    exact hxnot (Finset.mem_sdiff.mpr ⟨hxX,hn⟩)
  obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hm
  exact ⟨j,hj,(mem_flatPoints _ _).mp hxj⟩

lemma atlas_head_tail_cap (J cap : ℕ) (a : I) (ha : a ∈ F) :
    ((remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
      remaining F hF (fun i => flatPoints (P i)) X J).filter
      fun x => x.submodule ≤ P a).card ≤ cap := by
  have hh := head_tail_cap F hF (fun i => flatPoints (P i)) X J cap a ha
  simpa only [inter_flatPoints] using hh

lemma outside_cell_earlier (j : ℕ) (A : Submodule K V)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (y : ℙ K V) (hyX : y ∈ X) (hyA : y.submodule ≤ A)
    (hycell : y ∉ cell F hF (fun i => flatPoints (P i)) X j) :
    y ∈ X \ remaining F hF (fun i => flatPoints (P i)) X j := by
  refine Finset.mem_sdiff.mpr ⟨hyX, ?_⟩
  intro hyr
  exact hycell (Finset.mem_inter.mpr ⟨hyr, (mem_flatPoints _ _).mpr (hyA.trans hAj)⟩)

lemma earliest_plane_outside_cell_cap (j : ℕ) (A : Submodule K V)
    (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      fun y => y.submodule ≤ A).card ≤ j*(Nat.card K+1) := by
  have hs : (X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      (fun y => y.submodule ≤ A) ⊆
      (X \ remaining F hF (fun i => flatPoints (P i)) X j).filter
        (fun y => y.submodule ≤ A) := by
    intro y hy
    obtain ⟨hy,hya⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyX,hyc⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_filter.mpr ⟨outside_cell_earlier F hF P X j A hAj y hyX hya hyc,hya⟩
  have hc := plane_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i))
    (X \ remaining F hF (fun i => flatPoints (P i)) X j) A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi))
    (fun y hy _ => captured_cover F hF P X j y hy)
  exact (Finset.card_le_card hs).trans (by simpa only [Finset.card_range] using hc)

lemma surviving_plane_center_earlier (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (x : ℙ K V) (hxA : x.submodule ≤ A)
    (hrich : j*(Nat.card K+1) <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card) :
    ∃ i < j, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
  by_contra hn
  push Not at hn
  have heq := ownCell_eq F hF (fun i => flatPoints (P i)) X J j x hj
    ((mem_flatPoints _ _).mpr (hxA.trans hAj))
    (fun i hi hmem => hn i hi ((mem_flatPoints _ _).mp hmem))
  rw [heq] at hrich
  exact (not_lt_of_ge (earliest_plane_outside_cell_cap F hF P X j A hA hAj hearlier)) hrich

lemma surviving_plane_centers_cap (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((flatPoints A).filter fun x => j*(Nat.card K+1) <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card).card ≤ j*(Nat.card K+1) := by
  let C := (flatPoints A).filter fun x => j*(Nat.card K+1) <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card
  have hall (x : ℙ K V) (hx : x ∈ C) : x.submodule ≤ A :=
    (mem_flatPoints _ _).mp (Finset.mem_filter.mp hx).1
  have hc := plane_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i)) C A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi)) (by
      intro x hx hxa
      obtain ⟨i,hi,hxi⟩ := surviving_plane_center_earlier F hF P X J j hj A hA hAj hearlier
        x hxa (Finset.mem_filter.mp hx).2
      exact ⟨i,Finset.mem_range.mpr hi,hxi⟩)
  rw [Finset.filter_eq_self.mpr hall,Finset.card_range] at hc
  exact hc

lemma cell_filter_own_flat (j : ℕ) :
    ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y =>
      y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cell F hF (fun i => flatPoints (P i)) X j := by
  apply Finset.filter_eq_self.mpr
  intro y hy
  exact (mem_flatPoints _ _).mp (Finset.mem_inter.mp hy).2

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LargeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma chosen_shape_ne_of_positive_cell {i j : ℕ} (hij : i < j)
    (hpos : 0 < (cell F hF (fun i => flatPoints (P i)) X j).card) :
    P (chosen F hF (fun i => flatPoints (P i)) X i) ≠
      P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  intro he
  obtain ⟨y,hy⟩ := Finset.card_pos.mp hpos
  have hyr : y ∈ remaining F hF (fun i => flatPoints (P i)) X (i+1) :=
    remaining_antitone F hF _ X hij (cell_subset F hF _ X j hy)
  have hn := (Finset.mem_sdiff.mp hyr).2
  apply hn
  change y ∈ flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X i))
  rw [he]
  exact (Finset.mem_inter.mp hy).2

lemma largeCells_card_budget (J : ℕ) (c : ℝ) :
    ((largeCells F hF P X J c).card:ℝ)*c ≤ X.card := by
  have hs := Finset.sum_le_sum (s := largeCells F hF P X J c)
    (fun j hj => (Finset.mem_filter.mp hj).2)
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (show largeCells F hF P X J c ⊆ Finset.range J from Finset.filter_subset _ _)
    (f := fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ))
    (fun _ _ _ => Nat.cast_nonneg _)
  have hh := sum_card_add_remaining F hF (fun i => flatPoints (P i)) X J
  have hn : ∑ j ∈ Finset.range J, (cell F hF (fun i => flatPoints (P i)) X j).card ≤ X.card := by omega
  exact (hs.trans hle).trans (by exact_mod_cast hn)

lemma earlier_mem_largeCells (J : ℕ) (c : ℝ) {i j : ℕ}
    (hj : j ∈ largeCells F hF P X J c) (hij : i ≤ j) :
    i ∈ largeCells F hF P X J c := by
  obtain ⟨hjJ,hjc⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hij.trans_lt (Finset.mem_range.mp hjJ)),
    hjc.trans (by exact_mod_cast cell_card_antitone F hF (fun i => flatPoints (P i)) X hij)⟩

lemma hyperplane_intersection_cap (A H : Submodule K V)
    (hA : finrank K A = 4) (hH : finrank K H = 4) (hne : A ≠ H) :
    (flatPoints A ∩ flatPoints H).card ≤ ProjectiveIncidence.Q (Nat.card K) 2 := by
  have hnot : ¬A ≤ H := fun hh => hne (Submodule.eq_of_le_of_finrank_eq hh (hA.trans hH.symm))
  have hd := finrank_inf_lt_of_not_le A H hnot
  have hd' : finrank K (A ⊓ H : Submodule K V) ≤ 3 := by omega
  have he : flatPoints A ∩ flatPoints H =
      (flatPoints A ∩ flatPoints H).filter fun x => x.submodule ≤ A ⊓ H := by
    symm
    refine Finset.filter_eq_self.mpr ?_
    intro x hx
    exact le_inf ((mem_flatPoints _ _).mp (Finset.mem_inter.mp hx).1)
      ((mem_flatPoints _ _).mp (Finset.mem_inter.mp hx).2)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hd')
    (f := fun i => Nat.card K^i) (fun _ _ _ => Nat.zero_le _)
  have hc := (card_filter_containment_le (flatPoints A ∩ flatPoints H) (A ⊓ H)).trans hsum
  rw [← he] at hc
  exact hc

lemma largeCellIntersections_card (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (J : ℕ) (c : ℝ) (hc : 0 < c) :
    (largeCellIntersections F hF P X J c).card ≤
      (largeCells F hF P X J c).card^2*ProjectiveIncidence.Q (Nat.card K) 2 := by
  let B := largeCells F hF P X J c
  have hrow (ij : ℕ × ℕ) (hij : ij ∈ B ×ˢ B) :
      (if ij.1 = ij.2 then (∅:Finset (ℙ K V)) else
        flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X ij.1)) ∩
        flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X ij.2))).card ≤
        ProjectiveIncidence.Q (Nat.card K) 2 := by
    by_cases he : ij.1 = ij.2
    · simp [he]
    rw [ite_eq_right he]
    apply hyperplane_intersection_cap _ _ (hP _ (chosen_mem F hF _ X _)) (hP _ (chosen_mem F hF _ X _))
    have hp (j : ℕ) (hj : j ∈ B) : 0 < (cell F hF (fun i => flatPoints (P i)) X j).card := by
      have hh := hc.trans_le (Finset.mem_filter.mp hj).2
      exact_mod_cast hh
    rcases lt_or_gt_of_ne he with hij' | hji'
    · exact chosen_shape_ne_of_positive_cell F hF P X hij' (hp _ (Finset.mem_product.mp hij).2)
    · exact (chosen_shape_ne_of_positive_cell F hF P X hji' (hp _ (Finset.mem_product.mp hij).1)).symm
  have hh := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,Finset.card_product,smul_eq_mul] at hh
  exact Finset.card_biUnion_le.trans (by simpa only [sq] using hh)

theorem largeCellIntersections_budget (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (J : ℕ) (c : ℝ) (hc : 0 < c) :
    ((largeCellIntersections F hF P X J c).card:ℝ)*c^2 ≤
      (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)*(X.card:ℝ)^2 := by
  have hcard : ((largeCellIntersections F hF P X J c).card:ℝ) ≤
      ((largeCells F hF P X J c).card:ℝ)^2*(ProjectiveIncidence.Q (Nat.card K) 2:ℝ) := by
    exact_mod_cast largeCellIntersections_card F hF P X hP J c hc
  have hbudget := largeCells_card_budget F hF P X J c
  have hsquare := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hc.le) hbudget 2
  calc
    ((largeCellIntersections F hF P X J c).card:ℝ)*c^2 ≤
        ((largeCells F hF P X J c).card:ℝ)^2*(ProjectiveIncidence.Q (Nat.card K) 2:ℝ)*c^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)*
        (((largeCells F hF P X J c).card:ℝ)*c)^2 := by ring
    _ ≤ (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)*(X.card:ℝ)^2 :=
      mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg _)

lemma cellRichPlanes_variance (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3) (j M : ℕ)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*
      (cell F hF (fun i => flatPoints (P i)) X j).card ≤ M) :
    ((cellRichLines F hF P X L j M).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)^2*(cell F hF (fun i => flatPoints (P i)) X j).card := by
  let C := cell F hF (fun i => flatPoints (P i)) X j
  let G := L.filter fun A => M ≤ (C.filter fun y => y.submodule ≤ A).card
  have hG (A : Submodule K V) (hA : A ∈ G) : finrank K A = 3 :=
    hL A (Finset.mem_filter.mp hA).1
  have hm (A : Submodule K V) (hA : A ∈ G) : M ≤ (C.filter fun y => y.submodule ≤ A).card :=
    (Finset.mem_filter.mp hA).2
  have hμ : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*
      (C.filter fun y => y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)).card ≤ M := by
    simpa only [C,cell_filter_own_flat] using hmean
  have hh := rich_planes_inside_hyperplane
    (P (chosen F hF (fun i => flatPoints (P i)) X j)) (hP _ (chosen_mem F hF _ X j))
    G hG C M hm hμ
  have he : G.filter (fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cellRichLines F hF P X L j M := by
    ext A
    simp only [G,cellRichLines,Finset.mem_filter,C]
    tauto
  simpa only [he,C,cell_filter_own_flat] using hh

theorem weighted_small_cell_rich_planes (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3) (J M : ℕ)
    (c : ℝ) (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
      ProjectiveIncidence.Q (Nat.card K) 3)*c ≤ M) :
    (∑ j ∈ (Finset.range J).filter (fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ) < c),
      (j:ℝ)*(Nat.card K+1)*(cellRichLines F hF P X L j M).card)*(M:ℝ)^2 ≤
      4*(Nat.card K:ℝ)^2*(Nat.card K+1)*J*X.card := by
  let S := (Finset.range J).filter (fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ) < c)
  have hr (j : ℕ) (hj : j ∈ S) :
      (j:ℝ)*(Nat.card K+1)*(cellRichLines F hF P X L j M).card*M^2 ≤
        4*(Nat.card K:ℝ)^2*(Nat.card K+1)*J*(cell F hF (fun i => flatPoints (P i)) X j).card := by
    have hμ : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*
        (cell F hF (fun i => flatPoints (P i)) X j).card ≤ M :=
      (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hj).2.le (by positivity)).trans hmean
    have hv := cellRichPlanes_variance F hF P X hP L hL j M hμ
    have hjJ : (j:ℝ) ≤ J := by exact_mod_cast (Finset.mem_range.mp (Finset.mem_filter.mp hj).1).le
    calc
      _ = (j:ℝ)*(Nat.card K+1)*((cellRichLines F hF P X L j M).card*M^2) := by ring
      _ ≤ (j:ℝ)*(Nat.card K+1)*(4*(Nat.card K:ℝ)^2*(cell F hF (fun i => flatPoints (P i)) X j).card) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
      _ ≤ (J:ℝ)*(Nat.card K+1)*(4*(Nat.card K:ℝ)^2*(cell F hF (fun i => flatPoints (P i)) X j).card) := by gcongr
      _ = _ := by ring
  have hs : (∑ j ∈ S, ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ)) ≤ X.card := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg (show S ⊆ Finset.range J from Finset.filter_subset _ _)
      (f := fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ)) (fun _ _ _ => Nat.cast_nonneg _)
    have hn := sum_card_add_remaining F hF (fun i => flatPoints (P i)) X J
    have hh : ∑ j ∈ Finset.range J, (cell F hF (fun i => flatPoints (P i)) X j).card ≤ X.card := by omega
    exact hsub.trans (by exact_mod_cast hh)
  calc
    _ = ∑ j ∈ S, (j:ℝ)*(Nat.card K+1)*(cellRichLines F hF P X L j M).card*M^2 := by rw [Finset.sum_mul]
    _ ≤ ∑ j ∈ S, 4*(Nat.card K:ℝ)^2*(Nat.card K+1)*J*(cell F hF (fun i => flatPoints (P i)) X j).card := Finset.sum_le_sum hr
    _ = 4*(Nat.card K:ℝ)^2*(Nat.card K+1)*J*(∑ j ∈ S, ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

lemma earliest_plane_cell_rich (j M : ℕ) (hj : j*(Nat.card K+1) ≤ M)
    (A : Submodule K V) (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (hrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card) :
    M ≤ ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A).card := by
  have hcap := earliest_plane_outside_cell_cap F hF P X j A hA hAj hearlier
  have hsub : X.filter (fun y => y.submodule ≤ A) ⊆
      ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) ∪
      ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) := by
    intro y hy
    simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff] at *
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

theorem head_center_plane_count (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3) (J H M : ℕ)
    (hHJ : H ≤ J) (hM : 0 < M) (hHM : H*(Nat.card K+1) ≤ M)
    (c : ℝ) (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
      ProjectiveIncidence.Q (Nat.card K) 3)*c ≤ M) :
    (∑ A ∈ L, ((headPlaneCenters F hF P X J H M c A).card:ℝ))*(M:ℝ)^2 ≤
      4*(Nat.card K:ℝ)^2*(Nat.card K+1)*H*X.card := by
  let S := (Finset.range H).filter (fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ) < c)
  have hrow (A : Submodule K V) (hA : A ∈ L) :
      ((headPlaneCenters F hF P X J H M c A).card:ℝ) ≤
        ∑ j ∈ S, if A ∈ cellRichLines F hF P X L j M then (j:ℝ)*(Nat.card K+1) else 0 := by
    by_cases he : (headPlaneCenters F hF P X J H M c A).Nonempty
    · obtain ⟨x,hx⟩ := he
      obtain ⟨hxA,hcont,hxr,hxn⟩ := Finset.mem_filter.mp hx
      let j := Nat.find hcont
      have hjH : j < H := (Nat.find_spec hcont).1
      have hjJ := hjH.trans_le hHJ
      have hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := (Nat.find_spec hcont).2
      have hearlier (i : ℕ) (hi : i < j) : ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
        intro hiA
        exact Nat.find_min hcont hi ⟨hi.trans hjH,hiA⟩
      have hjM : j*(Nat.card K+1) ≤ M :=
        (Nat.mul_le_mul_right _ hjH.le).trans hHM
      have hjr : j*(Nat.card K+1) <
          ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card := by omega
      have hjSmall : ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ) < c := by
        by_contra hn
        have hjlarge : j ∈ largeCells F hF P X H c :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjH,le_of_not_gt hn⟩
        obtain ⟨i,hi,hxi⟩ := surviving_plane_center_earlier F hF P X J j hjJ A (hL A hA) hAj hearlier x
          ((mem_flatPoints _ _).mp hxA) hjr
        apply hxn
        have hiB := earlier_mem_largeCells F hF P X H c hjlarge hi.le
        refine Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_product.mpr ⟨hiB,hjlarge⟩,?_⟩
        simp only [ite_eq_right (ne_of_lt hi)]
        exact Finset.mem_inter.mpr ⟨(mem_flatPoints _ _).mpr hxi,
          (mem_flatPoints _ _).mpr (((mem_flatPoints _ _).mp hxA).trans hAj)⟩
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjH,hjSmall⟩
      have hfullrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card :=
        hxr.trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      have hmem : A ∈ cellRichLines F hF P X L j M :=
        Finset.mem_filter.mpr ⟨hA,hAj,earliest_plane_cell_rich F hF P X j M hjM A (hL A hA)
          hAj hearlier hfullrich⟩
      have hsub : headPlaneCenters F hF P X J H M c A ⊆
          (flatPoints A).filter (fun z => j*(Nat.card K+1) <
            ((X \ ownCell F hF (fun i => flatPoints (P i)) X J z).filter fun y => y.submodule ≤ A).card) := by
        intro z hz
        obtain ⟨hzA,_,hzr,_⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzA,by omega⟩
      have hc := (Finset.card_le_card hsub).trans
        (surviving_plane_centers_cap F hF P X J j hjJ A (hL A hA) hAj hearlier)
      have hsingle : (j:ℝ)*(Nat.card K+1) ≤ ∑ k ∈ S,
          if A ∈ cellRichLines F hF P X L k M then (k:ℝ)*(Nat.card K+1) else 0 := by
        have hh := Finset.single_le_sum (s := S)
          (f := fun k => if A ∈ cellRichLines F hF P X L k M then (k:ℝ)*(Nat.card K+1) else 0)
          (fun k _ => by positivity) hjS
        simpa only [ite_eq_left hmem] using hh
      exact (by exact_mod_cast hc : ((headPlaneCenters F hF P X J H M c A).card:ℝ) ≤
        (j:ℝ)*(Nat.card K+1)).trans hsingle
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.cast_zero]
      exact Finset.sum_nonneg (fun j _ => by positivity)
  have hsum := Finset.sum_le_sum hrow
  have hcount (j : ℕ) :
      (∑ A ∈ L, if A ∈ cellRichLines F hF P X L j M then (j:ℝ)*(Nat.card K+1) else 0) =
        (j:ℝ)*(Nat.card K+1)*(cellRichLines F hF P X L j M).card := by
    have hsub : cellRichLines F hF P X L j M ⊆ L := Finset.filter_subset _ _
    have hh := Finset.sum_subset hsub
      (f := fun A => if A ∈ cellRichLines F hF P X L j M then (j:ℝ)*(Nat.card K+1) else 0)
      (fun _ _ hn => ite_eq_right hn)
    rw [← hh]
    simp [mul_comm]
  rw [Finset.sum_comm] at hsum
  simp_rw [hcount] at hsum
  exact (mul_le_mul_of_nonneg_right hsum (sq_nonneg _)).trans
    (weighted_small_cell_rich_planes F hF P X hP L hL H M c hmean)

lemma actual_tail_hyperplane_cap
    (hcover : ∀ A : Submodule K V, finrank K A = 4 → ∃ i ∈ F, P i = A)
    (J cap : ℕ) (A : Submodule K V) (hA : finrank K A = 4) :
    ((remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
      remaining F hF (fun i => flatPoints (P i)) X J).filter fun x => x.submodule ≤ A).card ≤ cap := by
  obtain ⟨i,hi,rfl⟩ := hcover A hA
  exact atlas_head_tail_cap F hF P X J cap i hi

theorem actual_tail_rich_plane_exceptions
    (hcover : ∀ A : Submodule K V, finrank K A = 4 → ∃ i ∈ F, P i = A)
    (J cap M u D : ℕ) (hMpos : 0 < M)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (hM : ∀ A ∈ L, M ≤
      ((remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
        remaining F hF (fun i => flatPoints (P i)) X J).filter fun x => x.submodule ≤ A).card)
    (hlineLarge : 2*(Nat.card K+1) ≤ M) (hlineNum : 2*X.card ≤ u*M)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*cap ≤ M)
    (hhyperNum : 4*(Nat.card K:ℝ)^2*cap ≤ (u:ℝ)*M^2)
    (hlarge : 64*X.card ≤ M^2) (hD : 8*(2*u+1) ≤ D)
    (Y : Finset (ℙ K V)) :
    ((Y.filter fun x => D ≤ (L.filter fun A => x.submodule ≤ A).card).card:ℝ)*D^2*M^2 ≤
      4096*(X.card:ℝ)^2*(2*(u:ℝ)+1)^2 := by
  let T := remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
      remaining F hF (fun i => flatPoints (P i)) X J
  have hTX : T ⊆ X := fun _ hx => remaining_subset F hF _ X _ (Finset.mem_sdiff.mp hx).1
  have hc : T.card ≤ X.card := Finset.card_le_card hTX
  have hcap : ∀ A : Submodule K V, finrank K A = 4 → (T.filter fun x => x.submodule ≤ A).card ≤ cap :=
    actual_tail_hyperplane_cap F hF P X hcover J cap
  have hnum : 2*T.card ≤ u*M := (Nat.mul_le_mul_left _ hc).trans hlineNum
  have hlg : 64*T.card ≤ M^2 := (Nat.mul_le_mul_left _ hc).trans hlarge
  obtain ⟨hl,hh⟩ := multiplicity_budgets L hL T M cap u hMpos hM hcap hlineLarge hnum hmean hhyperNum
  have hr := capped_rich_plane_count L hL T M cap u hMpos hM hcap hlineLarge hnum hmean hhyperNum hlg
  have hex := RichPlaneOverlap.exceptional_centers L hL u hl hh Y D hD
  have hcr : (T.card:ℝ) ≤ X.card := by exact_mod_cast hc
  have hrX : (L.card:ℝ)*M ≤ 16*X.card*(2*(u:ℝ)+1) :=
    hr.trans (by gcongr)
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (L.card:ℝ)*M) hrX 2
  calc
    _ ≤ (16*(L.card:ℝ)^2)*(M:ℝ)^2 := mul_le_mul_of_nonneg_right hex (sq_nonneg _)
    _ = 16*((L.card:ℝ)*M)^2 := by ring
    _ ≤ 16*(16*X.card*(2*(u:ℝ)+1))^2 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighPlaneBudget

section
open Module GreedyTraining ProjectiveTraining RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma head_degree_sum (L : Finset (Submodule K V)) (J cap M : ℕ) (c : ℝ)
    (Y : Finset (ℙ K V)) :
    ∑ x ∈ Y, (headAt F hF P X L J cap M c x).card ≤
      ∑ A ∈ L, (headPlaneCenters F hF P X J
        (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A).card := by
  simp only [headAt,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A _
  have hs : Y.filter (fun x => x ∈ headPlaneCenters F hF P X J
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A) ⊆
      headPlaneCenters F hF P X J
        (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  simpa only [Finset.card_filter] using Finset.card_le_card hs

theorem head_exceptions (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J cap M : ℕ) (hM : 0 < M)
    (hHM : headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) ≤ M)
    (c : ℝ) (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
      ProjectiveIncidence.Q (Nat.card K) 3)*c ≤ M) (D : ℕ) (Y : Finset (ℙ K V)) :
    ((Y.filter fun x => D ≤ (headAt F hF P X L J cap M c x).card).card:ℝ)*D*M^2 ≤
      4*(Nat.card K:ℝ)^2*(Nat.card K+1)*
        headIndex F hF (fun i => flatPoints (P i)) X J cap*X.card := by
  let E := Y.filter fun x => D ≤ (headAt F hF P X L J cap M c x).card
  have hs : E.card*D ≤ ∑ x ∈ E,(headAt F hF P X L J cap M c x).card := by
    calc
      _ = ∑ _x ∈ E,D := by simp
      _ ≤ _ := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
  have hs' : (E.card:ℝ)*D ≤ ∑ A ∈ L,
      ((headPlaneCenters F hF P X J
        (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A).card:ℝ) := by
    exact_mod_cast hs.trans (head_degree_sum F hF P X L J cap M c E)
  exact (mul_le_mul_of_nonneg_right hs' (sq_nonneg _)).trans
    (head_center_plane_count F hF P X hP L hL J
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) M
      (headIndex_le F hF _ X J cap) hM hHM c hmean)

end

open Module GreedyTraining ProjectiveTraining RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

theorem tail_exceptions
    (hcover : ∀ A : Submodule K V, finrank K A = 4 → ∃ i ∈ F, P i = A)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J cap M u D : ℕ) (hMpos : 0 < M)
    (hlineLarge : 2*(Nat.card K+1) ≤ M) (hlineNum : 2*X.card ≤ u*M)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*cap ≤ M)
    (hhyperNum : 4*(Nat.card K:ℝ)^2*cap ≤ (u:ℝ)*M^2)
    (hlarge : 64*X.card ≤ M^2) (hD : 8*(2*u+1) ≤ D) (Y : Finset (ℙ K V)) :
    ((Y.filter fun x => D ≤
      ((tailPlanes F hF P X L J cap M).filter fun A => x.submodule ≤ A).card).card:ℝ)*D^2*M^2 ≤
      4096*(X.card:ℝ)^2*(2*(u:ℝ)+1)^2 := by
  apply actual_tail_rich_plane_exceptions F hF P X hcover J cap M u D hMpos
    (tailPlanes F hF P X L J cap M) (fun A hA => hL A (Finset.mem_filter.mp hA).1)
  · intro A hA
    exact (Finset.mem_filter.mp hA).2
  · exact hlineLarge
  · exact hlineNum
  · exact hmean
  · exact hhyperNum
  · exact hlarge
  · exact hD

end SharpRamseyFive.HighPlaneBudget

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighPlaneBudget

section
open Module GreedyTraining ProjectiveTraining HighParameters
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma plane_density_le : (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
    ProjectiveIncidence.Q (Nat.card K) 3 ≤ 1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).trans' Nat.zero_lt_one
  have hQ : (0:ℝ)<ProjectiveIncidence.Q (Nat.card K) 3 := by
    exact_mod_cast ProjectiveIncidence.Q_pos (Nat.card K) 3
  apply (div_le_div_iff₀ hQ hq).mpr
  have hh := ProjectiveIncidence.Q_recurrence (q := Nat.card K) (d := 3) (by omega)
  have hh' : (ProjectiveIncidence.Q (Nat.card K) 3:ℝ)=
      (Nat.card K:ℝ)*ProjectiveIncidence.Q (Nat.card K) 2+1 := by exact_mod_cast hh
  rw [hh']
  nlinarith

theorem high_exceptions_card (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (hcover : ∀ A : Submodule K V, finrank K A = 4 → ∃ i ∈ F, P i = A)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J : ℕ) (a χ : ℝ) (Y : Finset (ℙ K V))
    (hn : 0<X.card) (ha : 0<a) (ha2 : a≤2)
    (hnq : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 2097152*(Nat.card K:ℝ)^2≤X.card*a^2) (hχ : 0≤χ) :
    ((highExceptions F hF P X L J a χ Y).card:ℝ) ≤
      3145728*(Nat.card K:ℝ)^2/a^2 +
      ((X.card:ℝ)^2*a^3/(Nat.card K:ℝ)^3)*Real.exp (-χ) +
      36864*(Nat.card K:ℝ)^2*Real.exp (-2*χ) := by
  let q : ℝ := Nat.card K
  let n : ℝ := X.card
  let M := threshold q n a
  let C := HighParameters.cap q a
  let D := degree q n a χ
  let u := multiplicity q n a
  let H := headIndex F hF (fun i => flatPoints (P i)) X J C
  let E₀ := largeCellIntersections F hF P X H (n*a/1024)
  let E₁ := Y.filter fun x => D ≤ (headAt F hF P X L J C M (n*a/1024) x).card
  let E₂ := Y.filter fun x => D ≤ ((tailPlanes F hF P X L J C M).filter fun A => x.submodule ≤ A).card
  have hq : 1≤q := by dsimp [q]; exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hn' : 0<n := by dsimp [n]; exact_mod_cast hn
  obtain ⟨hM,hline,hlineNum,hcapMean,hhyperNum,hlarge⟩ := high_budget_conditions hq hn' ha ha2 hnq hhigh
  have hHC : (H:ℝ)*(C:ℝ)≤n := by
    dsimp [H,n]
    exact_mod_cast head_length_bound F hF (fun i => flatPoints (P i)) X J C
  have hHM : H*(Nat.card K+1)≤M := by
    have hh := head_length_condition hq hn' ha ha2 hhigh (Nat.cast_nonneg H) hHC
    dsimp [q,n] at hh
    exact_mod_cast hh
  have hdens := plane_density_le (K := K)
  have hheadMean := head_mean_condition hq hn' ha ha2 hhigh hdens
  have htailMean := tail_mean_condition hq hn' ha ha2 hnq hhigh hdens
  have hD := degree_multiplicity_condition hq hn' ha ha2 hnq hχ
  have hE₀ : (E₀.card:ℝ)≤3145728*q^2/a^2 := by
    apply large_exception_bound hq hn' ha
    have hh := largeCellIntersections_budget F hF P X hP H (n*a/1024) (by positivity)
    have he : (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)=q^2+q+1 := by
      simp [ProjectiveIncidence.Q,Finset.sum_range_succ,q]
      ring
    simpa only [he] using hh
  have hE₁ : (E₁.card:ℝ)≤(n^2*a^3/q^3)*Real.exp (-χ) := by
    apply head_exception_bound hq hn' ha ha2 hhigh (Nat.cast_nonneg E₁.card) (Nat.cast_nonneg H) hHC
    exact head_exceptions F hF P X hP L hL J C M hM hHM (n*a/1024) hheadMean D Y
  have hE₂ : (E₂.card:ℝ)≤36864*q^2*Real.exp (-2*χ) := by
    rw [neg_mul]
    apply tail_exception_bound (χ := χ) hq hn' ha ha2 hnq hhigh (Nat.cast_nonneg E₂.card)
    apply tail_exceptions F hF P X hcover L hL J C M u D hM
    · dsimp [q,n] at hline
      exact_mod_cast hline
    · dsimp [q,n] at hlineNum
      exact_mod_cast hlineNum
    · exact htailMean
    · exact hhyperNum
    · dsimp [q,n] at hlarge
      exact_mod_cast hlarge
    · exact hD
  have hun : (E₀ ∪ E₁ ∪ E₂).card ≤ E₀.card+E₁.card+E₂.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hun' : ((E₀ ∪ E₁ ∪ E₂).card:ℝ) ≤ (E₀.card:ℝ)+E₁.card+E₂.card := by exact_mod_cast hun
  exact hun'.trans (by dsimp [q,n] at *; linarith)

end

open Module RichPlaneGeometry HighParameters
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma capped_plane_exceptions (L : Finset (Submodule K V))
    (hL : ∀ A ∈ L, finrank K A = 3) (X : Finset (ℙ K V))
    (M C u D : ℕ) (hMpos : 0<M)
    (hcap : ∀ H : Submodule K V, finrank K H = 4 →
      (X.filter fun x => x.submodule ≤ H).card ≤ C)
    (hline : 2*(Nat.card K+1)≤M) (hnum : 2*X.card≤u*M)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
      ProjectiveIncidence.Q (Nat.card K) 3)*C≤M)
    (hhnum : 4*(Nat.card K:ℝ)^2*C≤(u:ℝ)*M^2)
    (hlarge : 64*X.card≤M^2) (hD : 8*(2*u+1)≤D) (Y : Finset (ℙ K V)) :
    ((Y.filter fun x => D≤((residualPlanes L X M).filter fun A =>
      x.submodule≤A).card).card:ℝ)*D^2*M^2≤4096*(X.card:ℝ)^2*(2*(u:ℝ)+1)^2 := by
  let R := residualPlanes L X M
  have hrank : ∀ A∈R, finrank K A=3 := fun A hA => hL A (Finset.mem_filter.mp hA).1
  have hrich : ∀ A∈R, M≤(X.filter fun x => x.submodule≤A).card :=
    fun _ hA => (Finset.mem_filter.mp hA).2
  obtain ⟨hl,hh⟩ := multiplicity_budgets R hrank X M C u hMpos hrich hcap
    hline hnum hmean hhnum
  have hr := capped_rich_plane_count R hrank X M C u hMpos hrich hcap
    hline hnum hmean hhnum hlarge
  have he := RichPlaneOverlap.exceptional_centers R hrank u hl hh Y D hD
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(R.card:ℝ)*M) hr 2
  calc
    _ ≤ (16*(R.card:ℝ)^2)*(M:ℝ)^2 := mul_le_mul_of_nonneg_right he (sq_nonneg _)
    _ = 16*((R.card:ℝ)*M)^2 := by ring
    _ ≤ 16*(16*X.card*(2*(u:ℝ)+1))^2 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

theorem residual_exceptions_card (L : Finset (Submodule K V))
    (hL : ∀ A∈L,finrank K A=3) (X Y : Finset (ℙ K V)) (a χ : ℝ)
    (hn : 0<X.card) (ha : 0<a) (ha2 : a≤2)
    (hnq : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 2097152*(Nat.card K:ℝ)^2≤X.card*a^2) (hχ : 0≤χ)
    (hcap : ∀ H : Submodule K V,finrank K H=4 →
      (X.filter fun x => x.submodule≤H).card≤HighParameters.cap (Nat.card K) a) :
    ((residualExceptions L X Y a χ).card:ℝ)≤36864*(Nat.card K:ℝ)^2*Real.exp (-2*χ) := by
  let q : ℝ := Nat.card K
  let n : ℝ := X.card
  have hq : 1≤q := by dsimp [q]; exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hn' : 0<n := by dsimp [n]; exact_mod_cast hn
  obtain ⟨hM,hline,hlineNum,_,hhyperNum,hlarge⟩ := high_budget_conditions hq hn' ha ha2 hnq hhigh
  have hmean := tail_mean_condition hq hn' ha ha2 hnq hhigh (plane_density_le (K := K))
  have hD := degree_multiplicity_condition hq hn' ha ha2 hnq hχ
  rw [neg_mul]
  apply tail_exception_bound (χ := χ) hq hn' ha ha2 hnq hhigh (Nat.cast_nonneg _)
  apply capped_plane_exceptions L hL X (threshold q n a) (HighParameters.cap q a)
    (multiplicity q n a) (degree q n a χ) hM hcap
  · dsimp [q,n] at hline
    exact_mod_cast hline
  · dsimp [q,n] at hlineNum
    exact_mod_cast hlineNum
  · exact hmean
  · exact hhyperNum
  · dsimp [q,n] at hlarge
    exact_mod_cast hlarge
  · exact hD

end SharpRamseyFive.HighPlaneBudget

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_HighOrSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

theorem high_or_small {q n a : ℝ} (_hq : 0 ≤ q) (_hn : 0 < n) (ha : 0 ≤ a)
    (hhigh : 8388608*q^2 ≤ n) :
    2097152*q^2 ≤ n*a^2 ∨ n*a^99 ≤ q^2 := by
  by_cases h : 2097152*q^2 ≤ n*a^2
  · exact Or.inl h
  right
  have hlt : n*a^2 < 2097152*q^2 := lt_of_not_ge h
  have ha2 : a^2 < (1/2:ℝ)^2 := by
    have := mul_le_mul_of_nonneg_right hhigh (sq_nonneg a)
    nlinarith
  have ha' : a ≤ 1/2 := by nlinarith
  have hp := pow_le_pow_left₀ ha ha' 97
  calc
    n*a^99 = (n*a^2)*a^97 := by ring
    _ ≤ (2097152*q^2)*(1/2:ℝ)^97 := mul_le_mul hlt.le hp (pow_nonneg ha 97) (by positivity)
    _ ≤ q^2 := by
      have hc : (2097152:ℝ)*(1/2:ℝ)^97 ≤ 1 := by norm_num
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg q)]

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma biUnion_card_real_le {ι A : Type*} [DecidableEq A] (I : Finset ι) (E : ι→Finset A)
    {e : ℝ} (hE : ∀i∈I,((E i).card:ℝ)≤e) :
    ((I.biUnion E).card:ℝ)≤I.card*e := by
  calc
    _ ≤ ∑i∈I,((E i).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le : (I.biUnion E).card≤_)
    _ ≤ ∑_i∈I,e := Finset.sum_le_sum hE
    _ = _ := by simp

lemma strengthDyads_card (m : ℕ) (δ : ℝ≥0) :
    (strengthDyads m δ).card≤Nat.clog 2 m+1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PeelingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreScalars
open scoped Topology
open Filter

lemma nonsmall_strength {q n a g : ℝ} (hq : 0<q) (hn : n=q^2*Real.exp g)
    (hg : 0≤g) (ha : 0≤a) (hlarge : q^2<n*a^99) :
    Real.exp (-g/10)<a := by
  by_contra hh
  have ha' : a≤Real.exp (-g/10) := le_of_not_gt hh
  have hp := pow_le_pow_left₀ ha ha' 99
  have he : (Real.exp (-g/10))^99≤Real.exp (-g) := by
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have hn0 : 0≤n := by rw [hn];positivity
  have hx := mul_le_mul_of_nonneg_left (hp.trans he) hn0
  have heq : n*Real.exp (-g)=q^2 := by rw [hn,mul_assoc,←Real.exp_add];simp
  rw [heq] at hx
  exact (not_lt_of_ge hx) hlarge

lemma high_exception_scalar {q n a g χ : ℝ} (hq : 0<q) (hn : n=q^2*Real.exp g)
    (hg : 0≤g) (hχ : 0≤χ) (ha : 0<a) (ha2 : a≤2)
    (haexp : Real.exp (-g/10)≤a) (hnq : n≤q^3) :
    3145728*q^2/a^2+(n^2*a^3/q^3)*Real.exp (-χ)+36864*q^2*Real.exp (-2*χ)≤
      n*(3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)) := by
  have hn0 : 0≤n := by rw [hn];positivity
  have hqn : q^2≤n := by rw [hn];nlinarith [Real.one_le_exp_iff.mpr hg,sq_nonneg q]
  have hp : Real.exp (-g/5)≤a^2 := by
    have hh := pow_le_pow_left₀ (Real.exp_nonneg (-g/10)) haexp 2
    have he : (Real.exp (-g/10))^2=Real.exp (-g/5) := by
      rw [←Real.exp_nat_mul];congr 1;norm_num;ring
    rwa [he] at hh
  have heq : n*Real.exp (-(4/5:ℝ)*g)*Real.exp (-g/5)=q^2 := by
    rw [hn,mul_assoc,mul_assoc,←Real.exp_add,←Real.exp_add]
    rw [show g+(-(4/5:ℝ)*g + -g/5)=0 by ring,Real.exp_zero,mul_one]
  have hfirst : q^2/a^2≤n*Real.exp (-(4/5:ℝ)*g) := by
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    calc
      q^2 = n*Real.exp (-(4/5:ℝ)*g)*Real.exp (-g/5) := heq.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have ha3 : a^3≤8 := by
    have hh := pow_le_pow_left₀ ha.le ha2 3
    norm_num at hh
    exact hh
  have hsecond : n^2*a^3/q^3≤8*n := by
    apply (div_le_iff₀ (pow_pos hq 3)).mpr
    calc
      n^2*a^3 ≤ n^2*8 := mul_le_mul_of_nonneg_left ha3 (sq_nonneg n)
      _ = 8*n*n := by ring
      _ ≤ 8*n*q^3 := mul_le_mul_of_nonneg_left hnq (by positivity)
      _ = _ := by ring
  have hthird : q^2*Real.exp (-2*χ)≤n*Real.exp (-χ) := by
    apply mul_le_mul hqn (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) hn0
  have h1 := mul_le_mul_of_nonneg_left hfirst (by norm_num : (0:ℝ)≤3145728)
  have h2 := mul_le_mul_of_nonneg_right hsecond (Real.exp_nonneg (-χ))
  have h3 := mul_le_mul_of_nonneg_left hthird (by norm_num : (0:ℝ)≤36864)
  convert add_le_add (add_le_add h1 h2) h3 using 1 <;> first | rfl | ring

end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type} [LinearOrder I]

theorem highPlaneExceptions_card (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V))
    (hFlat : ∀i∈F,finrank K (Flat i)=4)
    (hcover : ∀A : Submodule K V,finrank K A=4 → ∃i∈F,Flat i=A)
    (Planes : Finset (Submodule K V)) (hPlanes : ∀A∈Planes,finrank K A=3)
    (j : ℕ) (δ : ℝ≥0) (hδ : 0<δ) (χ g : ℝ) (hg : 0≤g) (hχ : 0≤χ)
    (hn : (X.card:ℝ)=(Nat.card K:ℝ)^2*Real.exp g)
    (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hori : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤X.card) (Q : Finset (ℙ K V)) :
    ((highPlaneExceptions F hF Flat X S Planes j δ χ Q).card:ℝ)≤
      X.card*((Nat.clog 2 S.card:ℝ)+1)*
        (3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hn0 : (0:ℝ)<X.card := by rw [hn];positivity
  let e : ℝ := 3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)
  have he : 0≤e := by dsimp [e];positivity
  have hh := biUnion_card_real_le (strengthDyads S.card δ)
    (fun i => if (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99
      then highExceptions F hF Flat X Planes j ((δ:ℝ)*2^i) χ Q else ∅)
    (e:=X.card*e) (by
      intro i hi
      split_ifs with hlarge
      · have ha : 0<(δ:ℝ)*2^i := by positivity
        have ha2 := (Finset.mem_filter.mp hi).2
        have hbudget := (ScoreScalars.high_or_small hq.le hn0 ha.le hhigh).resolve_right (not_le_of_gt hlarge)
        have hcount := high_exceptions_card F hF Flat X hFlat hcover Planes hPlanes j
          ((δ:ℝ)*2^i) χ Q (by exact_mod_cast hn0) ha ha2 hori hbudget hχ
        have hax := ScoreScalars.nonsmall_strength hq hn hg ha.le hlarge
        exact hcount.trans (ScoreScalars.high_exception_scalar hq hn hg hχ ha ha2 hax.le hcap)
      · simp only [Finset.card_empty,Nat.cast_zero]
        positivity)
  apply hh.trans
  have hc : ((strengthDyads S.card δ).card:ℝ)≤(Nat.clog 2 S.card:ℝ)+1 := by
    exact_mod_cast strengthDyads_card S.card δ
  calc
    _ ≤ ((Nat.clog 2 S.card:ℝ)+1)*(X.card*e) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by dsimp [e];ring

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Peeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem residualPlaneExceptions_card (Planes : Finset (Submodule K V))
    (hPlanes : ∀A∈Planes,finrank K A=3) (X S Q : Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0<δ) (χ : ℝ) (hχ : 0≤χ)
    (hori : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤X.card)
    (hcap : ∀H : Submodule K V,finrank K H=4 →
      (X.filter fun x => x.submodule≤H).card≤(Nat.card K)^2) :
    ((residualPlaneExceptions Planes X S Q δ χ).card:ℝ)≤
      X.card*((Nat.clog 2 S.card:ℝ)+1)*(36864*Real.exp (-χ)) := by
  have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hn : (0:ℝ)<X.card := (by positivity : 0<8388608*(Nat.card K:ℝ)^2).trans_le hhigh
  have hq2 : (Nat.card K:ℝ)^2≤X.card := by nlinarith only [hhigh,sq_nonneg (Nat.card K:ℝ)]
  have hh := biUnion_card_real_le (strengthDyads S.card δ)
    (fun i => if (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99
      then residualExceptions Planes X Q ((δ:ℝ)*2^i) χ else ∅)
    (e:=X.card*(36864*Real.exp (-χ))) (by
      intro i hi
      split_ifs with hlarge
      · have ha : 0<(δ:ℝ)*2^i := by positivity
        have ha2 := (Finset.mem_filter.mp hi).2
        have hbudget := (ScoreScalars.high_or_small hq0.le hn ha.le hhigh).resolve_right (not_le_of_gt hlarge)
        have hcap' : ∀H : Submodule K V,finrank K H=4 →
            (X.filter fun x => x.submodule≤H).card≤HighParameters.cap (Nat.card K) ((δ:ℝ)*2^i) := by
          intro H hH
          apply (hcap H hH).trans
          apply Nat.cast_le.mp (le_trans (b:=1024*(Nat.card K:ℝ)^2/((δ:ℝ)*2^i)) ?_ (Nat.le_ceil _))
          push_cast
          apply (le_div_iff₀ ha).mpr
          have hh := mul_le_mul_of_nonneg_left ha2 (sq_nonneg (Nat.card K:ℝ))
          nlinarith only [hh,sq_nonneg (Nat.card K:ℝ)]
        have hc := residual_exceptions_card Planes hPlanes X Q ((δ:ℝ)*2^i) χ
          (by exact_mod_cast hn) ha ha2 hori hbudget hχ hcap'
        apply hc.trans
        calc
          _ ≤ 36864*(X.card:ℝ)*Real.exp (-χ) := mul_le_mul
            (mul_le_mul_of_nonneg_left hq2 (by norm_num))
            (Real.exp_le_exp.mpr (by linarith only [hχ])) (Real.exp_nonneg _) (by positivity)
          _ = _ := by ring
      · simp only [Finset.card_empty,Nat.cast_zero]
        positivity)
  apply hh.trans
  have hc : ((strengthDyads S.card δ).card:ℝ)≤(Nat.clog 2 S.card:ℝ)+1 := by
    exact_mod_cast strengthDyads_card S.card δ
  calc
    _ ≤ ((Nat.clog 2 S.card:ℝ)+1)*(X.card*(36864*Real.exp (-χ))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HyperplaneHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [LinearOrder J]

theorem hyperplanePeelExceptions_card_oai (F : Finset J) (hF : F.Nonempty)
    (Flat : J→Submodule K V) (X XH S : Finset (ℙ K V))
    (Planes : Finset (Submodule K V))
    (hFlat : ∀i∈F,finrank K (Flat i)=4)
    (hcover : ∀H : Submodule K V,finrank K H=4 → ∃i∈F,Flat i=H)
    (hPlanes : ∀A∈Planes,finrank K A=3)
    (e : Prop) (he : e)
    (hXH : XH=peelSet e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
    (hS : S⊆XH) (δ : ℝ≥0) (hδ : 0<δ) (χ g : ℝ) (hg : 0≤g) (hχ : 0≤χ)
    (hn : (X.card:ℝ)=(Nat.card K:ℝ)^2*Real.exp g)
    (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hori : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤S.card) (Q : Finset (ℙ K V)) :
    ((hyperplanePeelExceptions F hF Flat X XH S Planes
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) δ χ Q).card:ℝ)≤
      X.card*((Nat.clog 2 S.card:ℝ)+1)*(3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)) := by
  have hHX : XH⊆X := hXH▸peel_subset e F hF (fun i=>flatPoints (Flat i)) X _ _
  have hSH : (S.card:ℝ)≤XH.card := Nat.cast_le.mpr (Finset.card_le_card hS)
  have hHXn : (XH.card:ℝ)≤X.card := Nat.cast_le.mpr (Finset.card_le_card hHX)
  unfold hyperplanePeelExceptions
  split_ifs with hc
  · exact highPlaneExceptions_card F hF Flat X S hFlat hcover Planes hPlanes _ δ hδ χ g hg hχ hn hcap hori
      (hhigh.trans (hSH.trans hHXn)) Q
  · have hres := (peel_alternative e he F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2)
        (pow_pos (Nat.card_pos (α:=K)) _)).resolve_left (by simpa only [←hXH] using hc)
    have hcapH : ∀H : Submodule K V,finrank K H=4 → (XH.filter fun x=>x.submodule≤H).card≤(Nat.card K)^2 := by
      intro H hH
      obtain ⟨i,hi,hiH⟩ := hcover H hH
      have hh := hres.2 i hi
      rw [←hXH] at hh
      have heq : (XH.filter fun x=>x.submodule≤H)=XH∩flatPoints (Flat i) := by
        ext x;simp only [Finset.mem_filter,Finset.mem_inter,mem_flatPoints,hiH]
      rw [heq]
      exact hh.le
    have hh := residualPlaneExceptions_card Planes hPlanes XH S Q δ hδ χ hχ
      ((pow_le_pow_left₀ (Nat.cast_nonneg _) hHXn 2).trans hori) (hhigh.trans hSH) hcapH
    apply hh.trans
    apply mul_le_mul (mul_le_mul_of_nonneg_right hHXn (by positivity)) _ (by positivity) (by positivity)
    have hge : 0≤3145728*Real.exp (-(4/5:ℝ)*g) := by positivity
    nlinarith only [hge,Real.exp_nonneg (-χ)]

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open Filter ParameterHierarchy MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card_oai := @OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card_oai

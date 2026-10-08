-- Prove2me | solution 1 for JuschenkoDeLaSalle.isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarselyEmbedsIn_and_not_of_containsLipschitzBinaryTree
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-10-07T14:04:36.486982+00:00
-- url     : https://prove2.me/submissions/fa16c507-a30b-4072-8413-8f88aab709c7

import Mathlib
import Definitions.Def_IntervalExchange

section

/-!
# Disproof of the JdlS milestone (conjunct 2)

`CoarselyEmbedsIn` lets the upper control `ρp` be an arbitrary function. We build a transient
bounded-geometry space (the rooted binary tree with a metric perturbed so that all distances are
distinct) that "coarsely embeds" into `Fin 2 → ℤ` in this literal sense, so conjunct 2 fails.
-/

open IntervalExchange

namespace JdlSDisproof

/-! ## Part 1: a transience criterion via a superharmonic function -/

section Chain

open Classical

variable {V : Type*}

lemma fs_summable {f : V → ℝ} (h : (Function.support f).Finite) : Summable f :=
  summable_of_ne_finset_zero (s := h.toFinset) (by simp)

lemma avoidProb_one (P : V → V → ℝ) (x₀ : V) (y : V) :
    avoidProb P x₀ 1 y = if y = x₀ then 0 else P x₀ y := rfl

lemma avoidProb_succ_succ (P : V → V → ℝ) (x₀ : V) (k : ℕ) (y : V) :
    avoidProb P x₀ (k + 2) y = if y = x₀ then 0 else ∑' z, avoidProb P x₀ (k + 1) z * P z y :=
  rfl

lemma firstReturnProb_zero (P : V → V → ℝ) (x₀ : V) : firstReturnProb P x₀ 0 = P x₀ x₀ := rfl

lemma firstReturnProb_succ (P : V → V → ℝ) (x₀ : V) (k : ℕ) :
    firstReturnProb P x₀ (k + 1) = ∑' z, avoidProb P x₀ (k + 1) z * P z x₀ := rfl

lemma avoidProb_base (P : V → V → ℝ) (x₀ : V) (k : ℕ) : avoidProb P x₀ (k + 1) x₀ = 0 := by
  cases k with
  | zero => rw [avoidProb_one, if_pos rfl]
  | succ k => rw [avoidProb_succ_succ, if_pos rfl]

variable {P : V → V → ℝ} {x₀ : V}

lemma av_props (hP0 : ∀ x y, 0 ≤ P x y) (hPf : ∀ x, (Function.support (P x)).Finite) (k : ℕ) :
    (∀ y, 0 ≤ avoidProb P x₀ (k + 1) y) ∧ (Function.support (avoidProb P x₀ (k + 1))).Finite := by
  induction k with
  | zero =>
    refine ⟨fun y => ?_, ?_⟩
    · rw [avoidProb_one]; split_ifs
      · exact le_refl _
      · exact hP0 _ _
    · apply (hPf x₀).subset
      intro y hy
      rw [Function.mem_support, avoidProb_one] at hy
      split_ifs at hy with h
      · exact absurd rfl hy
      · exact hy
  | succ k ih =>
    obtain ⟨h0, hf⟩ := ih
    have hsum : ∀ y, ∑' z, avoidProb P x₀ (k + 1) z * P z y =
        ∑ z ∈ hf.toFinset, avoidProb P x₀ (k + 1) z * P z y := by
      intro y
      apply tsum_eq_sum
      intro z hz
      simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hz
      simp [hz]
    refine ⟨fun y => ?_, ?_⟩
    · rw [avoidProb_succ_succ]; split_ifs
      · exact le_refl _
      · rw [hsum]; exact Finset.sum_nonneg fun z _ => mul_nonneg (h0 z) (hP0 z y)
    · apply (hf.toFinset.finite_toSet.biUnion fun z _ => hPf z).subset
      intro y hy
      rw [Function.mem_support, avoidProb_succ_succ] at hy
      split_ifs at hy with h
      · exact absurd rfl hy
      · rw [hsum] at hy
        obtain ⟨z, hz, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
        exact Set.mem_iUnion₂.2 ⟨z, hz, right_ne_zero_of_mul hne⟩

lemma bound (hP0 : ∀ x y, 0 ≤ P x y) (hPf : ∀ x, (Function.support (P x)).Finite)
    {φ : V → ℝ} (hφx : φ x₀ = 1) (hsup : ∀ x, x ≠ x₀ → ∑' y, P x y * φ y ≤ φ x) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), firstReturnProb P x₀ j + ∑' y, avoidProb P x₀ (k + 1) y * φ y ≤
      ∑' y, P x₀ y * φ y := by
  have hrow : ∀ x, Summable (fun y => P x y * φ y) := fun x =>
    fs_summable ((hPf x).subset (Function.support_mul_subset_left _ _))
  induction k with
  | zero =>
    rw [Finset.sum_range_one, firstReturnProb_zero, (hrow x₀).tsum_eq_add_tsum_ite x₀, hφx,
      mul_one]
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro y
    rw [avoidProb_one]
    split_ifs <;> simp
  | succ k ih =>
    refine le_trans ?_ ih
    rw [Finset.sum_range_succ, add_assoc]
    gcongr ?_ + ?_
    · exact le_refl _
    obtain ⟨h0, hf⟩ := av_props (x₀ := x₀) hP0 hPf k
    set a := avoidProb P x₀ (k + 1) with ha
    set s := hf.toFinset
    have hsum : ∀ y, ∑' z, a z * P z y = ∑ z ∈ s, a z * P z y := by
      intro y
      apply tsum_eq_sum
      intro z hz
      simp only [s, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hz
      simp [hz]
    set F : V → ℝ := fun y => ∑ z ∈ s, a z * (P z y * φ y) with hF
    have hFs : Summable F := summable_sum fun z _ => (hrow z).mul_left _
    have h1 : firstReturnProb P x₀ (k + 1) + ∑' y, avoidProb P x₀ (k + 1 + 1) y * φ y =
        ∑' y, F y := by
      rw [hFs.tsum_eq_add_tsum_ite x₀, firstReturnProb_succ, hsum]
      congr 1
      · simp only [F, hφx, mul_one]
      · apply tsum_congr
        intro y
        rw [avoidProb_succ_succ]
        split_ifs
        · simp
        · rw [hsum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun z _ => by ring
    rw [h1]
    calc ∑' y, F y = ∑ z ∈ s, a z * ∑' y, P z y * φ y := by
          simp only [F]
          rw [Summable.tsum_finsetSum (fun z _ => (hrow z).mul_left (a z))]
          exact Finset.sum_congr rfl fun z _ => tsum_mul_left
      _ ≤ ∑ z ∈ s, a z * φ z := by
          apply Finset.sum_le_sum
          intro z _
          by_cases hz : z = x₀
          · subst hz; simp [a, avoidProb_base]
          · exact mul_le_mul_of_nonneg_left (hsup z hz) (h0 z)
      _ = ∑' z, a z * φ z := by
          symm
          apply tsum_eq_sum
          intro z hz
          simp only [s, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hz
          simp [hz]

theorem not_isRecurrentChain (hP0 : ∀ x y, 0 ≤ P x y)
    (hPf : ∀ x, (Function.support (P x)).Finite)
    {φ : V → ℝ} (hφ0 : ∀ y, 0 ≤ φ y) (hφx : φ x₀ = 1)
    (hsup : ∀ x, x ≠ x₀ → ∑' y, P x y * φ y ≤ φ x) (hlt : ∑' y, P x₀ y * φ y < 1) :
    ¬ IsRecurrentChain P x₀ := by
  intro h
  have h' : HasSum (firstReturnProb P x₀) 1 := h
  have hle : ∀ N, ∑ j ∈ Finset.range N, firstReturnProb P x₀ j ≤ ∑' y, P x₀ y * φ y := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact tsum_nonneg fun y => mul_nonneg (hP0 _ _) (hφ0 _)
    | succ k =>
      have h1 := bound hP0 hPf hφx hsup k
      have h2 : 0 ≤ ∑' y, avoidProb P x₀ (k + 1) y * φ y :=
        tsum_nonneg fun y => mul_nonneg ((av_props hP0 hPf k).1 y) (hφ0 y)
      linarith
  have := le_of_tendsto' h'.tendsto_sum_nat hle
  linarith

end Chain

/-! ## Part 2: the binary tree and its tree metric -/

/-- Length of the longest common prefix. -/
def lcp : List Bool → List Bool → ℕ
  | a :: u, b :: v => if a = b then lcp u v + 1 else 0
  | _, _ => 0

lemma lcp_nil_left (v : List Bool) : lcp [] v = 0 := by cases v <;> rfl
lemma lcp_nil_right (u : List Bool) : lcp u [] = 0 := by cases u <;> rfl
lemma lcp_cons (a b : Bool) (u v : List Bool) :
    lcp (a :: u) (b :: v) = if a = b then lcp u v + 1 else 0 := rfl

lemma lcp_comm : ∀ u v : List Bool, lcp u v = lcp v u
  | [], v => by rw [lcp_nil_left, lcp_nil_right]
  | _ :: _, [] => by rw [lcp_nil_left, lcp_nil_right]
  | a :: u, b :: v => by
      rw [lcp_cons, lcp_cons, lcp_comm u v]
      by_cases h : a = b
      · subst h; rfl
      · rw [if_neg h, if_neg (Ne.symm h)]

lemma lcp_le_left : ∀ u v : List Bool, lcp u v ≤ u.length
  | [], v => by rw [lcp_nil_left]; simp
  | _ :: _, [] => by rw [lcp_nil_right]; simp
  | a :: u, b :: v => by
      have := lcp_le_left u v
      rw [lcp_cons]; split_ifs <;> simp; omega

lemma lcp_le_right (u v : List Bool) : lcp u v ≤ v.length := by
  rw [lcp_comm]; exact lcp_le_left v u

lemma lcp_append_self : ∀ u s : List Bool, lcp u (u ++ s) = u.length
  | [], s => by rw [lcp_nil_left]; rfl
  | a :: u, s => by
      rw [List.cons_append, lcp_cons, if_pos rfl, lcp_append_self u s]; rfl

lemma take_lcp : ∀ u v : List Bool, u.take (lcp u v) = v.take (lcp u v)
  | [], v => by rw [lcp_nil_left]; rfl
  | _ :: _, [] => by rw [lcp_nil_right]; rfl
  | a :: u, b :: v => by
      rw [lcp_cons]
      by_cases h : a = b
      · subst h; rw [if_pos rfl, List.take_succ_cons, List.take_succ_cons, take_lcp u v]
      · rw [if_neg h]; rfl

lemma lcp_min : ∀ u v w : List Bool, min (lcp u v) (lcp v w) ≤ lcp u w
  | [], v, w => by rw [lcp_nil_left]; simp
  | _ :: _, [], w => by rw [lcp_nil_right]; simp
  | _ :: _, _ :: _, [] => by rw [lcp_nil_right]; simp
  | a :: u, b :: v, c :: w => by
      have ih := lcp_min u v w
      rw [lcp_cons, lcp_cons, lcp_cons]
      by_cases hab : a = b
      · by_cases hbc : b = c
        · subst hab; subst hbc; rw [if_pos rfl, if_pos rfl, if_pos rfl]; omega
        · rw [if_neg hbc]; simp
      · rw [if_neg hab]; simp

/-- The tree distance. -/
def Dn (u v : List Bool) : ℕ := u.length + v.length - 2 * lcp u v

lemma Dn_comm (u v : List Bool) : Dn u v = Dn v u := by
  unfold Dn; rw [lcp_comm]; omega

lemma Dn_self (u : List Bool) : Dn u u = 0 := by
  have := lcp_append_self u []
  rw [List.append_nil] at this
  unfold Dn; omega

lemma Dn_triangle (u v w : List Bool) : Dn u w ≤ Dn u v + Dn v w := by
  have h1 := lcp_min u v w
  have h2 := lcp_le_left u v
  have h3 := lcp_le_right u v
  have h4 := lcp_le_left v w
  have h5 := lcp_le_right v w
  have h6 := lcp_le_left u w
  have h7 := lcp_le_right u w
  unfold Dn; omega

lemma Dn_le_length (u v : List Bool) : Dn u v ≤ u.length + v.length := by
  unfold Dn; omega

lemma Dn_append_single (v : List Bool) (b : Bool) : Dn (v ++ [b]) v = 1 := by
  have := lcp_append_self v [b]
  unfold Dn; rw [lcp_comm, this]; simp; omega

lemma Dn_le_one_iff (u v : List Bool) :
    Dn u v ≤ 1 ↔ u = v ∨ u = v ++ [false] ∨ u = v ++ [true] ∨ v = u ++ [false] ∨
      v = u ++ [true] := by
  constructor
  · intro h
    set m := lcp u v with hm
    have h2 := lcp_le_left u v
    have h3 := lcp_le_right u v
    have ht := take_lcp u v
    rw [← hm] at h2 h3 ht
    unfold Dn at h
    rw [← hm] at h
    have hu := List.take_append_drop m u
    have hv := List.take_append_drop m v
    rcases (by omega : (u.length = m ∧ v.length = m) ∨ (u.length = m + 1 ∧ v.length = m) ∨
        (u.length = m ∧ v.length = m + 1)) with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5⟩
    · left
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at ht
      exact ht
    · have hd : (u.drop m).length = 1 := by simp; omega
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hd
      rw [List.take_of_length_le (l := v) (by omega)] at ht
      rw [ht, hb] at hu
      cases b
      · right; left; exact hu.symm
      · right; right; left; exact hu.symm
    · have hd : (v.drop m).length = 1 := by simp; omega
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hd
      rw [List.take_of_length_le (l := u) (by omega)] at ht
      rw [← ht, hb] at hv
      cases b
      · right; right; right; left; exact hv.symm
      · right; right; right; right; exact hv.symm
  · rintro (h | h | h | h | h)
    · rw [h, Dn_self]; omega
    · rw [h, Dn_append_single]
    · rw [h, Dn_append_single]
    · rw [h, Dn_comm, Dn_append_single]
    · rw [h, Dn_comm, Dn_append_single]

/-- An injective code of binary words, `code l ≥ l.length + 1`. -/
def code : List Bool → ℕ
  | [] => 1
  | b :: l => 2 * code l + (if b then 1 else 0)

lemma code_pos : ∀ l, 1 ≤ code l
  | [] => le_refl _
  | b :: l => by have := code_pos l; unfold code; split_ifs <;> omega

lemma code_ge : ∀ l : List Bool, l.length + 1 ≤ code l
  | [] => le_refl _
  | b :: l => by have := code_ge l; simp only [code, List.length_cons]; split_ifs <;> omega

lemma code_inj : ∀ u v : List Bool, code u = code v → u = v
  | [], [] => fun _ => rfl
  | [], b :: v => by
      have := code_pos v; simp only [code]; split_ifs <;> omega
  | a :: u, [] => by
      have := code_pos u; simp only [code]; split_ifs <;> omega
  | a :: u, b :: v => by
      intro h
      simp only [code] at h
      have : a = b ∧ code u = code v := by
        cases a <;> cases b <;> simp at h ⊢ <;> omega
      rw [this.1, code_inj u v this.2]

/-! ## Part 3: the metric space -/

noncomputable def gg (l : List Bool) : ℕ := code l ^ 2

noncomputable def ee (u v : List Bool) : ℝ := |(gg u : ℝ) - gg v|

noncomputable def eps (u v : List Bool) : ℝ := 1 / 4 + 1 / (8 * (ee u v + 1))

lemma ee_nonneg (u v : List Bool) : 0 ≤ ee u v := abs_nonneg _

lemma ee_comm (u v : List Bool) : ee u v = ee v u := abs_sub_comm _ _

lemma eps_comm (u v : List Bool) : eps u v = eps v u := by unfold eps; rw [ee_comm]

lemma eps_gt (u v : List Bool) : 1 / 4 < eps u v := by
  have := ee_nonneg u v
  unfold eps; have : 0 < 1 / (8 * (ee u v + 1)) := by positivity
  linarith

lemma eps_le (u v : List Bool) : eps u v ≤ 3 / 8 := by
  have := ee_nonneg u v
  unfold eps
  have : 1 / (8 * (ee u v + 1)) ≤ 1 / 8 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
  linarith

noncomputable def trDist (u v : List Bool) : ℝ := if u = v then 0 else (Dn u v : ℝ) + eps u v

lemma trDist_self (u : List Bool) : trDist u u = 0 := by simp [trDist]

lemma trDist_comm (u v : List Bool) : trDist u v = trDist v u := by
  unfold trDist
  by_cases h : u = v
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), Dn_comm, eps_comm]

lemma trDist_nonneg (u v : List Bool) : 0 ≤ trDist u v := by
  unfold trDist; split_ifs
  · exact le_refl _
  · have := eps_gt u v; positivity

lemma trDist_triangle (u v w : List Bool) : trDist u w ≤ trDist u v + trDist v w := by
  by_cases huw : u = w
  · subst huw; rw [trDist_self]; exact add_nonneg (trDist_nonneg _ _) (trDist_nonneg _ _)
  by_cases huv : u = v
  · subst huv; rw [trDist_self, zero_add]
  by_cases hvw : v = w
  · subst hvw; rw [trDist_self, add_zero]
  unfold trDist
  rw [if_neg huw, if_neg huv, if_neg hvw]
  have h1 : ((Dn u w : ℕ) : ℝ) ≤ Dn u v + Dn v w := by exact_mod_cast Dn_triangle u v w
  linarith [eps_gt u v, eps_gt v w, eps_le u w]

lemma eq_of_trDist (u v : List Bool) (h : trDist u v = 0) : u = v := by
  by_contra hne
  unfold trDist at h
  rw [if_neg hne] at h
  have := eps_gt u v
  have : (0 : ℝ) ≤ Dn u v := Nat.cast_nonneg _
  linarith

/-- The binary tree with the perturbed tree metric. -/
def Tr : Type := List Bool

noncomputable instance : MetricSpace Tr where
  dist := trDist
  dist_self u := trDist_self u
  dist_comm u v := trDist_comm u v
  dist_triangle u v w := trDist_triangle u v w
  eq_of_dist_eq_zero h := eq_of_trDist _ _ h

lemma dist_eq (u v : List Bool) : @dist Tr _ u v = trDist u v := rfl

/-! ## Part 4: bounded geometry -/

lemma Dn_le_of_dist {u v : List Bool} {R : ℝ} (h : @dist Tr _ u v ≤ R) : (Dn u v : ℝ) ≤ R := by
  rw [dist_eq] at h
  unfold trDist at h
  split_ifs at h with huv
  · subst huv; rw [Dn_self]; simpa using h
  · linarith [eps_gt u v]

theorem boundedGeometry : HasBoundedGeometry Tr := by
  intro R _
  set K := ⌈R⌉₊
  set A : Set (ℕ × List Bool) := Set.Iic K ×ˢ {s : List Bool | s.length ≤ K}
  have hA : A.Finite := (Set.finite_Iic K).prod (List.finite_length_le Bool K)
  refine ⟨A.ncard, fun (x : List Bool) => ?_⟩
  have hsub : Metric.closedBall (α := Tr) x R ⊆
      (fun q : ℕ × List Bool => (List.take (x.length - q.1) x ++ q.2 : List Bool)) '' A := by
    intro (y : List Bool) hy0
    have hy : @dist Tr _ y x ≤ R := hy0
    have hD : Dn y x ≤ K := by
      have := Dn_le_of_dist hy
      exact_mod_cast this.trans (Nat.le_ceil R)
    rw [Dn_comm] at hD
    set m := lcp x y with hm
    have h2 := lcp_le_left x y
    have h3 := lcp_le_right x y
    have ht := take_lcp x y
    rw [← hm] at h2 h3 ht
    unfold Dn at hD
    rw [← hm] at hD
    refine ⟨(x.length - m, List.drop m y), ⟨?_, ?_⟩, ?_⟩
    · show _ ≤ K; omega
    · show (List.drop m y).length ≤ K; simp; omega
    · show List.take (x.length - (x.length - m)) x ++ List.drop m y = y
      rw [show x.length - (x.length - m) = m by omega, ht, List.take_append_drop]
  refine ⟨(hA.image _).subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub (hA.image _)).trans (Set.ncard_image_le hA)

/-! ## Part 5: the walk at radius 3/2 -/

lemma mem_ball (x y : List Bool) : y ∈ Metric.closedBall (α := Tr) x (3 / 2) ↔
    y = x ∨ y = x ++ [false] ∨ y = x ++ [true] ∨ x = y ++ [false] ∨ x = y ++ [true] := by
  show @dist Tr _ y x ≤ 3 / 2 ↔ _
  rw [dist_eq, ← Dn_le_one_iff]
  unfold trDist
  split_ifs with h
  · subst h; rw [Dn_self]; norm_num
  · constructor
    · intro h1
      have : (Dn y x : ℝ) < 2 := by linarith [eps_gt y x]
      have : Dn y x < 2 := by exact_mod_cast this
      omega
    · intro h1
      have : (Dn y x : ℝ) ≤ 1 := by exact_mod_cast h1
      linarith [eps_le y x]

noncomputable def phi (y : List Bool) : ℝ := (1 / 2 : ℝ) ^ y.length

lemma ballKernel_tsum (x : List Bool) (F : Finset (List Bool))
    (hF : Metric.closedBall (α := Tr) x (3 / 2) = (↑F : Set (List Bool))) :
    ∑' y : Tr, ballKernel Tr (3 / 2) x y * phi y = (F.card : ℝ)⁻¹ * ∑ y ∈ F, phi y := by
  classical
  show ∑' y : List Bool, ballKernel Tr (3 / 2) x y * phi y = _
  rw [Finset.mul_sum]
  rw [tsum_eq_sum (s := F)]
  · apply Finset.sum_congr rfl
    intro y hy
    unfold ballKernel
    rw [if_pos (by rw [hF]; exact Finset.mem_coe.2 hy), hF]
    exact congrArg (fun n : ℕ => ((n : ℝ))⁻¹ * phi y) (Set.ncard_coe_finset F)
  · intro y hy
    unfold ballKernel
    rw [if_neg (by rw [hF]; exact fun h => hy (Finset.mem_coe.1 h)), zero_mul]

lemma ball_nil : Metric.closedBall (α := Tr) ([] : List Bool) (3 / 2) =
    (↑({[], [false], [true]} : Finset (List Bool)) : Set (List Bool)) := by
  ext (y : List Bool)
  refine (mem_ball [] y).trans ?_
  change _ ↔ y ∈ ({[], [false], [true]} : Finset (List Bool))
  simp

lemma ball_concat (p : List Bool) (c : Bool) :
    Metric.closedBall (α := Tr) (p ++ [c]) (3 / 2) =
    (↑({p ++ [c], p, p ++ [c] ++ [false], p ++ [c] ++ [true]} : Finset (List Bool)) :
      Set (List Bool)) := by
  ext (y : List Bool)
  refine (mem_ball _ y).trans ?_
  have key : ∀ b : Bool, (p ++ [c] = y ++ [b]) ↔ (y = p ∧ b = c) := by
    intro b
    constructor
    · intro h
      have := List.append_inj' h rfl
      exact ⟨this.1.symm, (List.singleton_inj.1 this.2).symm⟩
    · rintro ⟨rfl, rfl⟩; rfl
  rw [key, key]
  simp only [Finset.coe_insert, Finset.coe_singleton]
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inl h.1)
  · rintro (h | h | h | h)
    · exact Or.inl h
    · cases c
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, rfl⟩)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

lemma ballKernel_nonneg (x y : Tr) : 0 ≤ ballKernel Tr (3 / 2) x y := by
  unfold ballKernel; split_ifs
  · positivity
  · exact le_refl _

theorem not_recurrent : ¬ IsRecurrentSpace Tr ([] : List Bool) := by
  intro h
  have hrec := h (3 / 2) (by norm_num)
  refine not_isRecurrentChain (φ := phi) (fun x y => ballKernel_nonneg x y) ?_
    (fun y => by unfold phi; positivity) (by simp [phi]) ?_ ?_ hrec
  · intro x
    obtain ⟨hfin, -⟩ := (boundedGeometry (3 / 2) (by norm_num)).choose_spec x
    apply hfin.subset
    intro y hy
    rw [Function.mem_support] at hy
    unfold ballKernel at hy
    split_ifs at hy with h1
    · exact h1
    · exact absurd rfl hy
  · intro (x : List Bool) hx
    obtain ⟨p, c, rfl⟩ := (List.eq_nil_or_concat x).resolve_left hx
    rw [List.concat_eq_append, ballKernel_tsum _ _ (ball_concat p c)]
    have hne : ∀ b, p ++ [c] ++ [b] ≠ p ++ [c] := fun b h => by
      have := congrArg List.length h; simp at this
    have hne2 : ∀ b, p ++ [c] ++ [b] ≠ p := fun b h => by
      have := congrArg List.length h; simp at this
    have hne3 : p ++ [c] ≠ p := fun h => by
      have := congrArg List.length h; simp at this
    have hne4 : p ++ [c] ++ [false] ≠ p ++ [c] ++ [true] := fun h => by
      have := List.append_inj' h rfl; simp at this
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne4,
      Finset.sum_insert, Finset.sum_insert, Finset.sum_pair hne4]
    · simp only [phi, List.length_append, List.length_singleton, pow_succ]
      push_cast
      ring_nf
      exact le_refl _
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    all_goals first
      | exact ⟨hne3, (hne _).symm, (hne _).symm⟩
      | exact ⟨(hne2 _).symm, (hne2 _).symm⟩
  · rw [ballKernel_tsum _ _ ball_nil]
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp),
      Finset.sum_insert (by simp), Finset.sum_pair (by simp)]
    simp [phi]
    norm_num

/-! ## Part 6: the literal coarse embedding -/

lemma sq_gap {a b : ℕ} (h : a ≠ b) : (a : ℝ) + b ≤ |((a ^ 2 : ℕ) : ℝ) - ((b ^ 2 : ℕ) : ℝ)| := by
  push_cast
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  rcases Nat.lt_or_gt_of_ne h with h1 | h1
  · have h2 : (a : ℝ) + 1 ≤ b := by exact_mod_cast h1
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    nlinarith [mul_nonneg (add_nonneg ha hb) (by linarith : (0 : ℝ) ≤ b - a - 1)]
  · have h2 : (b : ℝ) + 1 ≤ a := by exact_mod_cast h1
    refine le_trans ?_ (le_abs_self _)
    nlinarith [mul_nonneg (add_nonneg ha hb) (by linarith : (0 : ℝ) ≤ a - b - 1)]

lemma trDist_le_ee (u v : List Bool) : trDist u v ≤ ee u v := by
  unfold trDist
  split_ifs with h
  · exact ee_nonneg u v
  · have h1 : code u ≠ code v := fun h' => h (code_inj u v h')
    have h2 := sq_gap h1
    have h3 : ((u.length + 1 : ℕ) : ℝ) ≤ code u := by exact_mod_cast code_ge u
    have h4 : ((v.length + 1 : ℕ) : ℝ) ≤ code v := by exact_mod_cast code_ge v
    have h5 : ((Dn u v : ℕ) : ℝ) ≤ ((u.length + v.length : ℕ) : ℝ) := by
      exact_mod_cast Dn_le_length u v
    have h6 := eps_le u v
    push_cast at h3 h4 h5
    have : ee u v = |((code u ^ 2 : ℕ) : ℝ) - ((code v ^ 2 : ℕ) : ℝ)| := rfl
    linarith

/-- The (arbitrary) upper control. -/
noncomputable def rhoP (t : ℝ) : ℝ := if t = 0 then 0 else 1 / (8 * (t - ⌊t⌋ - 1 / 4)) - 1

lemma rhoP_trDist (u v : List Bool) : ee u v ≤ rhoP (trDist u v) := by
  unfold trDist
  split_ifs with h
  · subst h; unfold rhoP ee; simp
  · have he := ee_nonneg u v
    have hg := eps_gt u v
    have hl := eps_le u v
    have hne : (Dn u v : ℝ) + eps u v ≠ 0 := by positivity
    unfold rhoP
    rw [if_neg hne, Int.floor_natCast_add,
      Int.floor_eq_zero_iff.2 ⟨by linarith, by linarith⟩]
    apply le_of_eq
    push_cast
    unfold eps
    field_simp
    ring

theorem coarselyEmbeds : CoarselyEmbedsIn Tr (Fin 2 → ℤ) := by
  refine ⟨fun x _ => ((gg x : ℕ) : ℤ), id, rhoP, Filter.tendsto_id, fun (x : List Bool) (y : List Bool) => ?_⟩
  have hd : dist (fun _ : Fin 2 => ((gg x : ℕ) : ℤ)) (fun _ => ((gg y : ℕ) : ℤ)) = ee x y := by
    rw [dist_pi_const, Int.dist_eq]
    unfold ee
    push_cast
    rfl
  refine ⟨?_, ?_⟩
  · show @dist Tr _ x y ≤ _
    rw [hd, dist_eq]; exact trDist_le_ee x y
  · rw [hd]; exact rhoP_trDist x y

theorem solution : ¬ (∀ (X : Type) [MetricSpace X] (hX : HasBoundedGeometry X),
    (∀ x₀ : X, IsRecurrentSpace X x₀ →
      IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2))) ∧
    (CoarselyEmbedsIn X (Fin 2 → ℤ) → ∀ x₀ : X, IsRecurrentSpace X x₀) ∧
    (ContainsLipschitzBinaryTree X →
      ¬ IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2)))) := by
  intro h
  exact not_recurrent ((h Tr boundedGeometry).2.1 coarselyEmbeds ([] : List Bool))

end JdlSDisproof
end

open IntervalExchange
theorem solution : ¬ (∀ (X : Type) [MetricSpace X] (hX : HasBoundedGeometry X),
    (∀ x₀ : X, IsRecurrentSpace X x₀ →
      IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2))) ∧
    (CoarselyEmbedsIn X (Fin 2 → ℤ) → ∀ x₀ : X, IsRecurrentSpace X x₀) ∧
    (ContainsLipschitzBinaryTree X →
      ¬ IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2)))) :=
  JdlSDisproof.solution

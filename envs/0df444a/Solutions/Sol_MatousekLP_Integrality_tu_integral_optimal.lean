-- Prove2me | solution 1 for MatousekLP.Integrality.tu_integral_optimal
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T00:54:44.25719+00:00
-- url     : https://prove2.me/submissions/4486d685-1634-4bc6-b237-eceffbfbfb15

import Mathlib
import Definitions.Def_MatousekLP_Integrality_InequalityLP

set_option autoImplicit false

namespace TUCore

open Matrix Finset

variable {m n : ℕ}

/-- Feasibility for the slack-variable equational LP. -/
def IsFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ 0 ≤ x

def IsBoundedAbove (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ M : ℝ, ∀ x, IsFeasible A b x → c ⬝ᵥ x ≤ M

def ColumnsLinIndep (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) : Prop :=
  LinearIndependent ℝ (fun j : S => fun i : Fin m => A i (j : Fin n))

def IsBasis (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n)) : Prop :=
  B.card = m ∧ ColumnsLinIndep A B

def IsBasicFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  IsFeasible A b x ∧ ∃ B : Finset (Fin n), IsBasis A B ∧ ∀ j, j ∉ B → x j = 0

noncomputable def positiveIndices (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < x j)

/-- The column `j` of `A`. -/
def colv (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : Fin m → ℝ := fun i => A i j

lemma mulVec_eq_sum (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (hd : ∀ j, j ∉ S → d j = 0) : A *ᵥ d = ∑ j : S, d j • colv A j := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colv, mulVec, dotProduct]
  rw [Finset.sum_coe_sort S (fun j => d j * A i j)]
  rw [Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [hd j hj])]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- A dependency among the columns in `S` gives a nonzero kernel vector supported on `S`. -/
lemma dep_dir (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) (h : ¬ ColumnsLinIndep A S) :
    ∃ d : Fin n → ℝ, d ≠ 0 ∧ A *ᵥ d = 0 ∧ ∀ j, j ∉ S → d j = 0 := by
  classical
  obtain ⟨g, hg, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.mp h
  set d : Fin n → ℝ := fun j => if hj : j ∈ S then g ⟨j, hj⟩ else 0
  have hdS : ∀ j, j ∉ S → d j = 0 := fun j hj => by simp [d, hj]
  refine ⟨d, fun h0 => hj₀ ?_, ?_, hdS⟩
  · have := congrFun h0 j₀; simpa [d, j₀.2] using this
  · rw [mulVec_eq_sum A S d hdS, ← hg]
    exact Finset.sum_congr rfl fun j _ => by simp only [d, dif_pos j.2]; rfl

/-- Columns with zero entries outside an independent set determine the vector. -/
lemma eq_of_supp (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) (hS : ColumnsLinIndep A S)
    (x x' : Fin n → ℝ) (hx : ∀ j, j ∉ S → x j = 0) (hx' : ∀ j, j ∉ S → x' j = 0)
    (h : A *ᵥ x = A *ᵥ x') : x = x' := by
  set d := x - x'
  have hd : ∀ j, j ∉ S → d j = 0 := fun j hj => by simp [d, hx j hj, hx' j hj]
  have hAd : A *ᵥ d = 0 := by simp [d, mulVec_sub, h]
  have hz := (Fintype.linearIndependent_iff.mp hS) (fun j => d j)
    (by rw [mulVec_eq_sum A S d hd] at hAd; exact hAd)
  funext j
  by_cases hj : j ∈ S
  · have := hz ⟨j, hj⟩; simpa [d, sub_eq_zero] using this
  · rw [hx j hj, hx' j hj]

/-- Independent columns extend to a basis when `rank A = m`. -/
lemma extend_basis (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m) (K : Finset (Fin n))
    (hK : ColumnsLinIndep A K) : ∃ B : Finset (Fin n), K ⊆ B ∧ IsBasis A B := by
  classical
  -- a maximal independent superset
  set F := (Finset.univ : Finset (Finset (Fin n))).filter fun S => K ⊆ S ∧ ColumnsLinIndep A S
  have hF : F.Nonempty := ⟨K, by simp [F, hK]⟩
  obtain ⟨B, hBF, hBmax⟩ := F.exists_max_image Finset.card hF
  obtain ⟨hKB, hB⟩ := (Finset.mem_filter.mp hBF).2
  refine ⟨B, hKB, ?_, hB⟩
  have hle : B.card ≤ m := by
    have := hB.fintype_card_le_finrank
    simpa using this
  by_contra hne
  have hlt : B.card < m := lt_of_le_of_ne hle hne
  -- the span of the `B` columns is proper, so some column lies outside it
  have hspan : ∃ j, colv A j ∉ Submodule.span ℝ (colv A '' (B : Set (Fin n))) := by
    by_contra hall
    push Not at hall
    have hsub : Submodule.span ℝ (Set.range A.col) ≤ Submodule.span ℝ (colv A '' (B : Set (Fin n))) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hall j
    have h1 := Submodule.finrank_mono hsub
    rw [← rank_eq_finrank_span_cols, hrank] at h1
    have h2 : Module.finrank ℝ (Submodule.span ℝ (colv A '' (B : Set (Fin n)))) ≤ B.card := by
      have := finrank_range_le_card (R := ℝ) (fun j : (B : Set (Fin n)) => colv A j)
      rw [← Set.image_eq_range] at this
      simpa [Set.finrank] using this
    omega
  obtain ⟨j, hj⟩ := hspan
  have hjB : j ∉ B := fun h => hj (Submodule.subset_span ⟨j, h, rfl⟩)
  have hins : ColumnsLinIndep A (insert j B) := by
    have := LinearIndepOn.insert (v := colv A) (s := (B : Set (Fin n))) hB hj
    have h' : LinearIndepOn ℝ (colv A) ((insert j B : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert]; exact this
    exact h'
  have := hBmax (insert j B) (by simp [F, hins, hKB.trans (Finset.subset_insert _ _)])
  rw [Finset.card_insert_of_notMem hjB] at this
  omega

theorem basic_iff (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hrank : A.rank = m)
    (x : Fin n → ℝ) (hx : IsFeasible A b x) :
    IsBasicFeasible A b x ↔ ColumnsLinIndep A (positiveIndices x) := by
  classical
  constructor
  · rintro ⟨-, B, ⟨-, hB⟩, hzero⟩
    have hsub : positiveIndices x ⊆ B := by
      intro j hj
      simp only [positiveIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra h; rw [hzero j h] at hj; exact lt_irrefl _ hj
    exact hB.comp (Set.inclusion hsub) (Set.inclusion_injective hsub)
  · intro hP
    obtain ⟨B, hPB, hB⟩ := extend_basis A hrank _ hP
    refine ⟨hx, B, hB, fun j hj => ?_⟩
    have : j ∉ positiveIndices x := fun h => hj (hPB h)
    simp only [positiveIndices, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
    exact le_antisymm this (hx.2 j)

/-- One reduction step: a feasible point with dependent positive columns can be moved, without
decreasing `c ⬝ x`, to a feasible point with strictly smaller support. -/
lemma reduce_step (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hbdd : IsBoundedAbove A b c) (x : Fin n → ℝ) (hx : IsFeasible A b x)
    (hdep : ¬ ColumnsLinIndep A (positiveIndices x)) :
    ∃ x' : Fin n → ℝ, IsFeasible A b x' ∧ c ⬝ᵥ x ≤ c ⬝ᵥ x' ∧
      (positiveIndices x').card < (positiveIndices x).card := by
  classical
  obtain ⟨d₀, hd₀, hAd₀, hsupp₀⟩ := dep_dir A _ hdep
  -- a ray along `d ≥ 0` with `c ⬝ d > 0` would be unbounded
  have no_ray : ∀ d : Fin n → ℝ, A *ᵥ d = 0 → 0 ≤ d → c ⬝ᵥ d ≤ 0 := by
    intro d hAd hd0
    by_contra hpos; push Not at hpos
    obtain ⟨M, hM⟩ := hbdd
    set t := (|M| + |c ⬝ᵥ x| + 1) / (c ⬝ᵥ d)
    have ht : 0 ≤ t := div_nonneg (by positivity) hpos.le
    have hfeas : IsFeasible A b (x + t • d) :=
      ⟨by rw [mulVec_add, mulVec_smul, hAd, smul_zero, add_zero, hx.1],
        fun j => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply];
                    nlinarith [show (0 : ℝ) ≤ x j from hx.2 j, mul_nonneg ht (show (0 : ℝ) ≤ d j from hd0 j)]⟩
    have := hM _ hfeas
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    linarith [le_abs_self M, neg_abs_le (c ⬝ᵥ x)]
  -- choose a direction with a negative coordinate and `c ⬝ d ≥ 0`
  obtain ⟨d, hAd, hsupp, hcd, hneg⟩ : ∃ d : Fin n → ℝ, A *ᵥ d = 0 ∧
      (∀ j, j ∉ positiveIndices x → d j = 0) ∧ 0 ≤ c ⬝ᵥ d ∧ ∃ k, d k < 0 := by
    have hAn : A *ᵥ (-d₀) = 0 := by rw [mulVec_neg, hAd₀, neg_zero]
    have hsn : ∀ j, j ∉ positiveIndices x → (-d₀) j = 0 := fun j hj => by simp [hsupp₀ j hj]
    by_cases hnn : 0 ≤ d₀
    · -- then `-d₀` has a negative coordinate
      have hc := no_ray d₀ hAd₀ hnn
      obtain ⟨k, hk⟩ : ∃ k, d₀ k ≠ 0 := by
        by_contra h; push Not at h; exact hd₀ (funext h)
      refine ⟨-d₀, hAn, hsn, by rw [dotProduct_neg]; linarith, k, ?_⟩
      have := hnn k; simp only [Pi.zero_apply] at this
      simp only [Pi.neg_apply]; exact neg_neg_iff_pos.mpr (lt_of_le_of_ne this (Ne.symm hk))
    · obtain ⟨k, hk⟩ : ∃ k, d₀ k < 0 := by
        by_contra h; push Not at h; exact hnn (fun j => h j)
      by_cases hc : 0 ≤ c ⬝ᵥ d₀
      · exact ⟨d₀, hAd₀, hsupp₀, hc, k, hk⟩
      · push Not at hc
        by_cases hnn' : 0 ≤ -d₀
        · have := no_ray (-d₀) hAn hnn'; rw [dotProduct_neg] at this; linarith
        · obtain ⟨k', hk'⟩ : ∃ k, (-d₀) k < 0 := by
            by_contra h; push Not at h; exact hnn' (fun j => h j)
          exact ⟨-d₀, hAn, hsn, by rw [dotProduct_neg]; linarith, k', hk'⟩
  -- step until a coordinate vanishes
  set S := Finset.univ.filter fun k => d k < 0
  have hS : S.Nonempty := by obtain ⟨k, hk⟩ := hneg; exact ⟨k, by simp [S, hk]⟩
  obtain ⟨k, hkS, hkmin⟩ := S.exists_min_image (fun k => x k / (-d k)) hS
  have hk : d k < 0 := (Finset.mem_filter.mp hkS).2
  set t := x k / (-d k)
  have ht : 0 ≤ t := div_nonneg (hx.2 k) (by linarith)
  set x' := x + t • d
  have hx'nn : 0 ≤ x' := by
    intro l
    simp only [x', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hl : d l < 0
    · have := hkmin l (by simp [S, hl])
      rw [le_div_iff₀ (by linarith)] at this
      linarith [show t * -d l = -(t * d l) by ring]
    · push Not at hl
      linarith [show (0 : ℝ) ≤ x l from hx.2 l, mul_nonneg ht hl]
  have hx'k : x' k = 0 := by
    have : x k / -d k * d k = -x k := by
      rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
    simp only [x', Pi.add_apply, Pi.smul_apply, smul_eq_mul, t, this]
    ring
  refine ⟨x', ⟨by rw [mulVec_add, mulVec_smul, hAd, smul_zero, add_zero, hx.1], hx'nn⟩, ?_, ?_⟩
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; nlinarith
  · -- support shrinks: `positiveIndices x' ⊆ positiveIndices x \ {k}`
    have hk_pos : k ∈ positiveIndices x := by
      by_contra h; rw [hsupp k h] at hk; exact lt_irrefl _ hk
    apply Finset.card_lt_card
    refine ⟨fun j hj => ?_, fun hsub => ?_⟩
    · simp only [positiveIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra hxj
      have hxj0 : x j = 0 := le_antisymm (not_lt.mp hxj) (hx.2 j)
      have hdj : d j = 0 := hsupp j (by simp [positiveIndices, hxj])
      simp [x', hxj0, hdj] at hj
    · have := hsub hk_pos
      simp [positiveIndices, hx'k] at this

theorem exists_bfs_ge (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hrank : A.rank = m) (hbdd : IsBoundedAbove A b c) (x₀ : Fin n → ℝ)
    (hx₀ : IsFeasible A b x₀) :
    ∃ x : Fin n → ℝ, IsBasicFeasible A b x ∧ c ⬝ᵥ x₀ ≤ c ⬝ᵥ x := by
  classical
  suffices H : ∀ k, ∀ x, IsFeasible A b x → (positiveIndices x).card = k →
      ∃ x' : Fin n → ℝ, IsBasicFeasible A b x' ∧ c ⬝ᵥ x ≤ c ⬝ᵥ x' from
    H _ x₀ hx₀ rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx hk
    by_cases hind : ColumnsLinIndep A (positiveIndices x)
    · exact ⟨x, (basic_iff A b hrank x hx).mpr hind, le_rfl⟩
    · obtain ⟨x', hx', hc, hcard⟩ := reduce_step A b c hbdd x hx hind
      obtain ⟨x'', hx'', hc'⟩ := ih _ (hk ▸ hcard) x' hx' rfl
      exact ⟨x'', hx'', hc.trans hc'⟩

/-- A nonsingular TU square matrix sends an integral right-hand side to an integral solution. -/
lemma square_integral {k : ℕ} (D : Matrix (Fin k) (Fin k) ℝ)
    (hD : D.IsTotallyUnimodular) (hind : LinearIndependent ℝ D.col)
    (b : Fin k → ℤ) (x : Fin k → ℝ) (hx : D *ᵥ x = fun i => (b i : ℝ)) :
    ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
  classical
  have hn : D.det ≠ 0 := (isUnit_iff_ne_zero.mp
    ((isUnit_iff_isUnit_det D).mp (linearIndependent_cols_iff_isUnit.mp hind)))
  have hd := ((isTotallyUnimodular_iff D).mp hD) k id id
  have hdet : D.det = 1 ∨ D.det = -1 := by
    obtain ⟨s, hs⟩ := hd
    cases s <;> simp_all
  have he : ∀ i j, ∃ z : ℤ, (z : ℝ) = D i j := by
    intro i j
    obtain ⟨s, hs⟩ := hD.apply i j
    cases s
    · exact ⟨0, by simpa using hs⟩
    · exact ⟨-1, by simpa using hs⟩
    · exact ⟨1, by simpa using hs⟩
  choose E₀ hE using he
  let E : Matrix (Fin k) (Fin k) ℤ := E₀
  have hmap : E.map (Int.castRingHom ℝ) = D := by ext i j; exact hE i j
  have hmadj : E.adjugate.map (Int.castRingHom ℝ) = D.adjugate := by
    calc
      _ = (E.map (Int.castRingHom ℝ)).adjugate := (Int.castRingHom ℝ).map_adjugate E
      _ = _ := by rw [hmap]
  have hadj : (fun i => ((E.adjugate *ᵥ b) i : ℝ)) = D.adjugate *ᵥ (fun i => (b i : ℝ)) := by
    funext i
    change (Int.castRingHom ℝ) ((E.adjugate *ᵥ b) i) = _
    rw [(Int.castRingHom ℝ).map_mulVec]
    rw [hmadj]
    rfl
  have hsolve : D.det • x = D.adjugate *ᵥ (fun i => (b i : ℝ)) := by
    rw [← hx, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  intro i
  rcases hdet with h | h
  · refine ⟨(E.adjugate *ᵥ b) i, ?_⟩
    have hh := congrFun hadj i
    have hs := congrFun hsolve i
    simpa [h] using hh.trans hs.symm
  · refine ⟨-(E.adjugate *ᵥ b) i, ?_⟩
    have hh := congrFun hadj i
    have hs := congrFun hsolve i
    simp only [Pi.smul_apply, smul_eq_mul, h, neg_one_mul] at hs
    rw [Int.cast_neg, hh, ← hs, neg_neg]

lemma bfs_integral (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.IsTotallyUnimodular)
    (b : Fin m → ℤ) (x : Fin n → ℝ)
    (hx : IsBasicFeasible A (fun i => (b i : ℝ)) x) :
    ∀ j, ∃ z : ℤ, (z : ℝ) = x j := by
  classical
  obtain ⟨hf, B, ⟨hcard, hB⟩, hzero⟩ := hx
  let e : Fin m ≃ B := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let D : Matrix (Fin m) (Fin m) ℝ := A.submatrix id (fun j => e j)
  have hD : D.IsTotallyUnimodular := hA.submatrix _ _
  have hind : LinearIndependent ℝ D.col := hB.comp (fun j => e j) e.injective
  have hmul : D *ᵥ (fun j => x (e j)) = fun i => (b i : ℝ) := by
    rw [← hf.1]
    funext i
    simp only [mulVec, dotProduct, D, submatrix_apply, id]
    rw [e.sum_comp (fun j : B => A i j * x j)]
    rw [Finset.sum_coe_sort B (fun j => A i j * x j)]
    exact Finset.sum_subset (Finset.subset_univ B) (fun j _ hj => by rw [hzero j hj, mul_zero])
  have hz := square_integral D hD hind b _ hmul
  intro j
  by_cases hj : j ∈ B
  · simpa using hz (e.symm ⟨j, hj⟩)
  · exact ⟨0, by simp [hzero j hj]⟩

end TUCore

namespace TUCore
open Matrix Finset MatousekLP.Integrality

/-- Slack variables turn inequalities into an equational LP, preserving TU. -/
theorem integral_optimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℤ)
    (c : Fin n → ℝ) (hA : A.IsTotallyUnimodular)
    (hopt : ∃ x : Fin n → ℝ, IsOptimalIneq A (fun i => (b i : ℝ)) c x) :
    ∃ z : Fin n → ℤ, IsOptimalIneq A (fun i => (b i : ℝ)) c (fun j => (z j : ℝ)) := by
  classical
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let C : Matrix (Fin m) (Fin (n + m)) ℝ := (fromCols A 1).submatrix id e.symm
  let d : Fin (n + m) → ℝ := Sum.elim c (fun _ => 0) ∘ e.symm
  let expand (x : Fin n → ℝ) (s : Fin m → ℝ) : Fin (n + m) → ℝ := Sum.elim x s ∘ e.symm
  let left (v : Fin (n + m) → ℝ) : Fin n → ℝ := fun j => v (e (.inl j))
  let right (v : Fin (n + m) → ℝ) : Fin m → ℝ := fun i => v (e (.inr i))
  have heq (v : Fin (n + m) → ℝ) : C *ᵥ v = A *ᵥ left v + right v := by
    change (fromCols A 1).submatrix id e.symm *ᵥ v = _
    rw [submatrix_mulVec_equiv, fromCols_mulVec, one_mulVec]
    rfl
  have hcost (v : Fin (n + m) → ℝ) : d ⬝ᵥ v = c ⬝ᵥ left v := by
    simp only [dotProduct, d, Function.comp_apply]
    rw [← e.sum_comp (fun j => Sum.elim c (fun _ => 0) (e.symm j) * v j)]
    simp [Fintype.sum_sum_type, left]
  have hfeas (v : Fin (n + m) → ℝ)
      (hv : IsFeasible C (fun i => (b i : ℝ)) v) :
      IsFeasibleIneq A (fun i => (b i : ℝ)) (left v) := by
    refine ⟨?_, fun j => hv.2 (e (.inl j))⟩
    intro i
    have hi := congrFun hv.1 i
    rw [heq] at hi
    have hn := hv.2 (e (.inr i))
    change A.mulVec (left v) i + right v i = (b i : ℝ) at hi
    change 0 ≤ right v i at hn
    linarith
  have hexpand (x : Fin n → ℝ)
      (hx : IsFeasibleIneq A (fun i => (b i : ℝ)) x) :
      IsFeasible C (fun i => (b i : ℝ)) (expand x (fun i => (b i : ℝ) - (A *ᵥ x) i)) := by
    refine ⟨?_, ?_⟩
    · rw [heq]
      simp only [left, right, expand, Function.comp_apply, Equiv.symm_apply_apply,
        Sum.elim_inl, Sum.elim_inr]
      funext i
      simp
    · intro j
      obtain ⟨j, rfl⟩ := e.surjective j
      cases j with
      | inl j => simpa [expand] using hx.2 j
      | inr i => simpa [expand] using sub_nonneg.mpr (hx.1 i)
  have hCTU : C.IsTotallyUnimodular := hA.fromCols_one.submatrix _ _
  have hrank : C.rank = m := by
    have hsub : (C.submatrix id (fun i => e (.inr i))) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
      ext i j
      simp [C, submatrix, fromCols]
    have hl := C.rank_submatrix_le id (fun i => e (.inr i))
    rw [hsub, rank_one, Fintype.card_fin] at hl
    exact le_antisymm (by simpa using C.rank_le_card_height) hl
  obtain ⟨x, hx, hmax⟩ := hopt
  let v := expand x (fun i => (b i : ℝ) - (A *ᵥ x) i)
  have hv : IsFeasible C (fun i => (b i : ℝ)) v := hexpand x hx
  have hleft : left v = x := by funext j; simp [left, v, expand]
  have hbdd : IsBoundedAbove C (fun i => (b i : ℝ)) d := by
    refine ⟨c ⬝ᵥ x, fun y hy => ?_⟩
    rw [hcost]
    exact hmax _ (hfeas y hy)
  obtain ⟨v', hv', hle⟩ := exists_bfs_ge C _ d hrank hbdd v hv
  have hint := bfs_integral C hCTU b v' hv'
  choose z hz using fun j : Fin n => hint (e (.inl j))
  have hzleft : (fun j => (z j : ℝ)) = left v' := funext hz
  refine ⟨z, ?_⟩
  rw [hzleft]
  refine ⟨hfeas v' hv'.1, fun y hy => (hmax y hy).trans ?_⟩
  rw [hcost, hcost, hleft] at hle
  exact hle
end TUCore

open Matrix MatousekLP.Integrality in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℤ)
    (c : Fin n → ℝ) (hA : A.IsTotallyUnimodular)
    (hopt : ∃ x : Fin n → ℝ, IsOptimalIneq A (fun i => (b i : ℝ)) c x) :
    ∃ z : Fin n → ℤ, IsOptimalIneq A (fun i => (b i : ℝ)) c (fun j => (z j : ℝ)) :=
  TUCore.integral_optimal A b c hA hopt

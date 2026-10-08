-- Prove2me | solution 1 for MatousekLP.BFS.basic_iff_positive_columns_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:55:52.918922+00:00
-- url     : https://prove2.me/submissions/2cd3af04-25c2-4154-813c-fa7bc4cbbeb0

import Definitions.Def_MatousekLP_BFS_EquationalForm
import Mathlib

namespace BFSCore

open Matrix MatousekLP.BFS Finset

variable {m n : ℕ}

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
    push_neg at hall
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
    by_contra hpos; push_neg at hpos
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
        by_contra h; push_neg at h; exact hd₀ (funext h)
      refine ⟨-d₀, hAn, hsn, by rw [dotProduct_neg]; linarith, k, ?_⟩
      have := hnn k; simp only [Pi.zero_apply] at this
      simp only [Pi.neg_apply]; exact neg_neg_iff_pos.mpr (lt_of_le_of_ne this (Ne.symm hk))
    · obtain ⟨k, hk⟩ : ∃ k, d₀ k < 0 := by
        by_contra h; push_neg at h; exact hnn (fun j => h j)
      by_cases hc : 0 ≤ c ⬝ᵥ d₀
      · exact ⟨d₀, hAd₀, hsupp₀, hc, k, hk⟩
      · push_neg at hc
        by_cases hnn' : 0 ≤ -d₀
        · have := no_ray (-d₀) hAn hnn'; rw [dotProduct_neg] at this; linarith
        · obtain ⟨k', hk'⟩ : ∃ k, (-d₀) k < 0 := by
            by_contra h; push_neg at h; exact hnn' (fun j => h j)
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
    · push_neg at hl
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

lemma bfs_finite (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    {x | IsBasicFeasible A b x}.Finite := by
  classical
  have hsub : {x | IsBasicFeasible A b x} ⊆
      ⋃ B : Finset (Fin n), {x | IsBasicFeasible A b x ∧ IsBasis A B ∧ ∀ j, j ∉ B → x j = 0} := by
    rintro x hx
    obtain ⟨B, hB, hz⟩ := hx.2
    exact Set.mem_iUnion.mpr ⟨B, hx, hB, hz⟩
  refine Set.Finite.subset (Set.finite_iUnion fun B => Set.Subsingleton.finite ?_) hsub
  rintro x ⟨hx, hB, hz⟩ x' ⟨hx', -, hz'⟩
  exact eq_of_supp A B hB.2 x x' hz hz' (by rw [hx.1.1, hx'.1.1])

theorem optimal_bfs_exists (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hrank : A.rank = m) :
    ((∃ x, IsFeasible A b x) → IsBoundedAbove A b c → ∃ x, IsOptimal A b c x) ∧
    ((∃ x, IsOptimal A b c x) → ∃ x, IsOptimal A b c x ∧ IsBasicFeasible A b x) := by
  constructor
  · rintro ⟨x₀, hx₀⟩ hbdd
    obtain ⟨x₁, hx₁, -⟩ := exists_bfs_ge A b c hrank hbdd x₀ hx₀
    obtain ⟨x, hx, hmax⟩ := Set.exists_max_image _ (fun x => c ⬝ᵥ x) (bfs_finite A b) ⟨x₁, hx₁⟩
    refine ⟨x, hx.1, fun y hy => ?_⟩
    obtain ⟨y', hy', hle⟩ := exists_bfs_ge A b c hrank hbdd y hy
    exact hle.trans (hmax y' hy')
  · rintro ⟨x, hx, hmax⟩
    obtain ⟨x', hx', hle⟩ := exists_bfs_ge A b c hrank ⟨c ⬝ᵥ x, hmax⟩ x hx
    exact ⟨x', ⟨hx'.1, fun y hy => (hmax y hy).trans hle⟩, hx'⟩

theorem vertex_iff_bfs (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hn : 0 < n)
    (hrank : A.rank = m) (v : Fin n → ℝ) (hv : v ∈ feasibleSet A b) :
    IsVertex (feasibleSet A b) v ↔ IsBasicFeasible A b v := by
  classical
  have hvf : IsFeasible A b v := hv
  rw [basic_iff A b hrank v hvf]
  constructor
  · rintro ⟨-, c, -, hc⟩
    by_contra hdep
    obtain ⟨d, hd0, hAd, hsupp⟩ := dep_dir A _ hdep
    -- a small step in both directions stays feasible
    obtain ⟨ε, hε, hstep⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| ≤ 1 → 0 ≤ v + (s * ε) • d := by
      set M := ∑ j, |d j| + 1
      have hM : 0 < M := by positivity
      set P := positiveIndices v
      by_cases hP : P.Nonempty
      · obtain ⟨k, hkP, hkmin⟩ := P.exists_min_image v hP
        have hvk : 0 < v k := by simpa [P, positiveIndices] using hkP
        refine ⟨v k / M, div_pos hvk hM, fun s hs l => ?_⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        by_cases hl : l ∈ P
        · have hvl := hkmin l hl
          have hdl : |d l| ≤ M := by
            have := Finset.single_le_sum (f := fun j => |d j|) (fun j _ => abs_nonneg _)
              (Finset.mem_univ l)
            linarith
          have h1 : |s * (v k / M) * d l| ≤ v k := by
            rw [abs_mul, abs_mul, abs_of_pos (div_pos hvk hM)]
            calc |s| * (v k / M) * |d l| ≤ 1 * (v k / M) * M := by gcongr
              _ = v k := by field_simp
          linarith [neg_abs_le (s * (v k / M) * d l)]
        · rw [hsupp l hl, mul_zero, add_zero]; exact hvf.2 l
      · refine ⟨1, one_pos, fun s _ l => ?_⟩
        have hl : l ∉ P := fun h => hP ⟨l, h⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hsupp l hl, mul_zero,
          add_zero]
        exact hvf.2 l
    have hfeas : ∀ s : ℝ, |s| ≤ 1 → v + (s * ε) • d ∈ feasibleSet A b := fun s hs =>
      ⟨by rw [mulVec_add, mulVec_smul, hAd, smul_zero, add_zero, hvf.1], hstep s hs⟩
    have hne : ∀ s : ℝ, s ≠ 0 → v + (s * ε) • d ≠ v := by
      intro s hs h
      apply hd0
      have : (s * ε) • d = 0 := by simpa using h
      exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero hs hε.ne')
    have h1 := hc _ (hfeas 1 (by simp)) (hne 1 one_ne_zero)
    have h2 := hc _ (hfeas (-1) (by simp)) (hne (-1) (by norm_num))
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1 h2
    nlinarith
  · intro hind
    obtain ⟨-, B, hB, hz⟩ := (basic_iff A b hrank v hvf).mpr hind
    refine ⟨hv, ?_⟩
    by_cases hBu : B = Finset.univ
    · -- the feasible set is the single point `v`
      refine ⟨Pi.single ⟨0, hn⟩ 1, fun h => by simpa using congrFun h ⟨0, hn⟩, fun y hy hyv => ?_⟩
      exact absurd (eq_of_supp A B hB.2 y v (by simp [hBu]) (by simp [hBu])
        (by rw [hy.1, hvf.1])) hyv
    · obtain ⟨j₀, hj₀⟩ : ∃ j, j ∉ B := by
        by_contra h; push_neg at h; exact hBu (Finset.eq_univ_iff_forall.mpr h)
      set c : Fin n → ℝ := fun j => if j ∈ B then 0 else -1
      refine ⟨c, fun h => by simpa [c, hj₀] using congrFun h j₀, fun y hy hyv => ?_⟩
      have hcv : c ⬝ᵥ v = 0 := Finset.sum_eq_zero fun j _ => by
        by_cases hj : j ∈ B <;> simp [c, hj, hz]
      rw [hcv]
      have hcy : c ⬝ᵥ y = -∑ j ∈ Finset.univ.filter (fun j => j ∉ B), y j := by
        simp only [dotProduct, c, ite_mul, zero_mul, neg_one_mul, Finset.sum_ite,
          Finset.sum_const_zero, zero_add, Finset.sum_neg_distrib]
      rw [hcy, neg_neg_iff_pos]
      by_contra hle; push_neg at hle
      have hzero : ∀ j, j ∉ B → y j = 0 := by
        intro j hj
        have hnn : ∀ i ∈ Finset.univ.filter (fun j => j ∉ B), 0 ≤ y i := fun i _ => hy.2 i
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp
          (le_antisymm hle (Finset.sum_nonneg hnn)) j (by simp [hj])
        exact this
      exact hyv (eq_of_supp A B hB.2 y v hzero hz (by rw [hy.1, hvf.1]))

end BFSCore

open Matrix MatousekLP.BFS in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (x : Fin n → ℝ)
    (hx : IsFeasible A b x) :
    IsBasicFeasible A b x ↔ ColumnsLinIndep A (positiveIndices x) :=
  BFSCore.basic_iff A b hrank x hx

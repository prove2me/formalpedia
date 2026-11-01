-- Prove2me | solution 1 for Grunbaum2003.barany_por_binary_facet_growth
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T21:13:29.888461+00:00
-- url     : https://prove2.me/submissions/5fc6092d-89d2-4159-91f9-f07f5e15a94b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsZeroOnePolytope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

namespace BaranyPorBinaryFacetGrowth

/-! ### Part 1: Triangular numbers and explicit subset-sum representations -/

/-- The `k`-th triangular number `1 + 2 + ⋯ + k`. -/
def tri (k : ℕ) : ℕ :=
  ∑ r ∈ Finset.range k, (r + 1)

@[simp] lemma tri_zero : tri 0 = 0 := rfl
@[simp] lemma tri_one : tri 1 = 1 := rfl
lemma tri_two : tri 2 = 3 := rfl

lemma tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) :=
  Finset.sum_range_succ (fun r => r + 1) k

lemma one_le_tri {k : ℕ} (hk : 1 ≤ k) : 1 ≤ tri k := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [ Nat.add_comm 1 k', tri_succ ]
  omega

/-- Index sequence for auxiliary coordinates with `r₀` initial ones (`r₀ ∈ {3, 4}`). -/
def kSeq (r₀ j : ℕ) : ℕ :=
  if j < r₀ then 1 else j - r₀ + 2

/-- Weight sequence for auxiliary coordinates. -/
def sSeq (r₀ j : ℕ) : ℕ :=
  tri (kSeq r₀ j)

lemma one_le_kSeq (r₀ j : ℕ) : 1 ≤ kSeq r₀ j := by
  dsimp [kSeq]
  split_ifs <;> omega

lemma kSeq_le (r₀ : ℕ) {p j : ℕ} (hrp : r₀ ≤ p) (hj : j < p) :
    kSeq r₀ j ≤ p + 1 - r₀ := by
  dsimp [kSeq]
  split_ifs <;> omega

lemma one_le_sSeq (r₀ j : ℕ) : 1 ≤ sSeq r₀ j :=
  one_le_tri (one_le_kSeq r₀ j)

lemma sSeq_zero (r₀ : ℕ) (hr₀ : 1 ≤ r₀) : sSeq r₀ 0 = 1 := by
  have h0 : 0 < r₀ := hr₀
  dsimp [sSeq, kSeq]
  rw [if_pos h0]
  rfl

lemma le_sum_sSeq_range (r₀ n : ℕ) : n ≤ ∑ i ∈ Finset.range n, sSeq r₀ i := by
  calc
    n = ∑ _i ∈ Finset.range n, 1 := by simp
    _ ≤ ∑ i ∈ Finset.range n, sSeq r₀ i :=
      Finset.sum_le_sum (fun i _ => one_le_sSeq r₀ i)

lemma sSeq_le_sum_range {r₀ : ℕ} (hr₀ : 3 ≤ r₀) (j : ℕ) (hj : 1 ≤ j) :
    sSeq r₀ j ≤ ∑ i ∈ Finset.range j, sSeq r₀ i := by
  by_cases hjr : j < r₀
  · have hs : sSeq r₀ j = 1 := by
      dsimp [sSeq, kSeq]
      rw [if_pos hjr]
      rfl
    linarith [le_sum_sSeq_range r₀ j]
  · by_cases hjeq : j = r₀
    · have hs : sSeq r₀ j = 3 := by
        dsimp [sSeq, kSeq]
        rw [if_neg (by omega), hjeq, Nat.sub_self]
        rfl
      have hle := le_sum_sSeq_range r₀ j
      omega
    · have hjgt : r₀ < j := by omega
      have hsplit : Finset.range j = Finset.range ((j - 1) + 1) := by
        congr 1; omega
      rw [hsplit, Finset.sum_range_succ]
      have hk1 : kSeq r₀ (j - 1) = j - r₀ + 1 := by
        dsimp [kSeq]
        rw [if_neg (by omega)]
        omega
      have hk2 : kSeq r₀ j = (j - r₀ + 1) + 1 := by
        dsimp [kSeq]
        rw [if_neg (by omega)]
      have hs : sSeq r₀ j = sSeq r₀ (j - 1) + (j - r₀ + 2) := by
        dsimp [sSeq]
        rw [hk1, hk2, tri_succ]
      have hsum_le : j - 1 ≤ ∑ i ∈ Finset.range (j - 1), sSeq r₀ i :=
        le_sum_sSeq_range r₀ (j - 1)
      omega

lemma sSeq_le_one_add_sum_range {r₀ : ℕ} (hr₀ : 3 ≤ r₀) (j : ℕ) :
    sSeq r₀ j ≤ 1 + ∑ i ∈ Finset.range j, sSeq r₀ i := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [sSeq_zero r₀ (by omega), Finset.range_zero, Finset.sum_empty]
    omega
  · linarith [sSeq_le_sum_range hr₀ j hj]

lemma exists_finset_sum_eq {r₀ : ℕ} (hr₀ : 3 ≤ r₀) :
    ∀ (n N : ℕ), N ≤ ∑ i ∈ Finset.range n, sSeq r₀ i →
      ∃ R ⊆ Finset.range n, ∑ i ∈ R, sSeq r₀ i = N := by
  intro n
  induction' n with n ih
  · intro N hN
    simp only [Finset.range_zero, Finset.sum_empty, Nat.le_zero] at hN
    exact ⟨∅, Finset.Subset.refl _, by simp [hN]⟩
  · intro N hN
    rw [Finset.sum_range_succ] at hN
    by_cases hle : N ≤ ∑ i ∈ Finset.range n, sSeq r₀ i
    · obtain ⟨R, hRsub, hRsum⟩ := ih N hle
      exact ⟨R, hRsub.trans (Finset.range_mono (Nat.le_succ n)), hRsum⟩
    · have hsn : sSeq r₀ n ≤ 1 + ∑ i ∈ Finset.range n, sSeq r₀ i :=
        sSeq_le_one_add_sum_range hr₀ n
      have hNsub : N - sSeq r₀ n ≤ ∑ i ∈ Finset.range n, sSeq r₀ i := by omega
      obtain ⟨R, hRsub, hRsum⟩ := ih (N - sSeq r₀ n) hNsub
      have hnR : n ∉ R := fun hn => Nat.lt_irrefl n (Finset.mem_range.mp (hRsub hn))
      refine ⟨insert n R, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_range.mpr (Nat.lt_succ_self x)
        · exact Finset.range_mono (Nat.le_succ n) (hRsub hx)
      · rw [Finset.sum_insert hnR, hRsum]
        omega

lemma exists_repNat_ge_two (r₀ k : ℕ) (hr₀ : 3 ≤ r₀) (hk : 2 ≤ k) :
    ∃ R ⊆ Finset.range (r₀ + k - 2), ∑ i ∈ R, sSeq r₀ i = tri k := by
  have hj : 1 ≤ r₀ + k - 2 := by omega
  have hle : sSeq r₀ (r₀ + k - 2) ≤ ∑ i ∈ Finset.range (r₀ + k - 2), sSeq r₀ i :=
    sSeq_le_sum_range hr₀ (r₀ + k - 2) hj
  have hks : sSeq r₀ (r₀ + k - 2) = tri k := by
    dsimp [sSeq, kSeq]
    rw [if_neg (by omega)]
    congr 1
    omega
  rw [hks] at hle
  exact exists_finset_sum_eq hr₀ (r₀ + k - 2) (tri k) hle

/-- Subset of `ℕ` representing `tri k` via `sSeq r₀`. -/
noncomputable def repNat (r₀ k : ℕ) : Finset ℕ :=
  if hk0 : k = 0 then ∅
  else if hk1 : k = 1 then {0}
  else if hr₀ : 3 ≤ r₀ then
    Classical.choose (exists_repNat_ge_two r₀ k hr₀ (by omega))
  else ∅

lemma repNat_subset_range {r₀ k : ℕ} (hr₀ : 3 ≤ r₀) :
    repNat r₀ k ⊆ Finset.range (if k = 0 then 0 else if k = 1 then 1 else r₀ + k - 2) := by
  dsimp [repNat]
  split_ifs with hk0 hk1
  · exact Finset.Subset.refl _
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    simp [hx]
  · exact (Classical.choose_spec (exists_repNat_ge_two r₀ k hr₀ (by omega))).1

lemma sum_repNat {r₀ k : ℕ} (hr₀ : 3 ≤ r₀) :
    ∑ i ∈ repNat r₀ k, sSeq r₀ i = tri k := by
  dsimp [repNat]
  split_ifs with hk0 hk1
  · subst hk0; simp
  · subst hk1; simp [sSeq_zero r₀ (by omega)]
  · exact (Classical.choose_spec (exists_repNat_ge_two r₀ k hr₀ (by omega))).2

lemma mem_repNat_lt_of_kSeq {r₀ j i : ℕ} (hr₀ : 3 ≤ r₀) (hj : 1 ≤ j)
    (hi : i ∈ repNat r₀ (kSeq r₀ j)) : i < j := by
  have hsub := repNat_subset_range hr₀ hi
  rw [Finset.mem_range] at hsub
  by_cases hjr : j < r₀
  · have hk : kSeq r₀ j = 1 := by dsimp [kSeq]; rw [if_pos hjr]
    rw [hk] at hsub
    simp at hsub
    omega
  · have hk : 2 ≤ kSeq r₀ j := by dsimp [kSeq]; rw [if_neg hjr]; omega
    have hk_eq : kSeq r₀ j = j - r₀ + 2 := by dsimp [kSeq]; rw [if_neg hjr]
    have h0 : kSeq r₀ j ≠ 0 := by omega
    have h1 : kSeq r₀ j ≠ 1 := by omega
    rw [if_neg h0, if_neg h1, hk_eq] at hsub
    omega

/-- Subset of `Fin p` representing `tri k`. -/
noncomputable def repSet (r₀ p k : ℕ) : Finset (Fin p) :=
  Finset.filter (fun j : Fin p => j.val ∈ repNat r₀ k) Finset.univ

lemma sum_repSet {r₀ p k : ℕ} (hr₀ : 3 ≤ r₀) (hkp : r₀ + k ≤ p + 1) :
    ∑ j ∈ repSet r₀ p k, sSeq r₀ j.val = tri k := by
  have hsub : repNat r₀ k ⊆ Finset.range p := by
    refine (repNat_subset_range hr₀).trans (Finset.range_mono ?_)
    split_ifs <;> omega
  rw [← sum_repNat hr₀]
  refine Finset.sum_bij (fun (j : Fin p) _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [repSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj
  · intro j₁ _ j₂ _ h
    exact Fin.ext h
  · intro i hi
    have hip : i < p := Finset.mem_range.mp (hsub hi)
    refine ⟨⟨i, hip⟩, ?_, rfl⟩
    simp [repSet, hi]
  · intro _ _; rfl

lemma mem_repSet_lt {r₀ p : ℕ} (hr₀ : 3 ≤ r₀) (j r : Fin p) (hj : 1 ≤ j.val)
    (hr : r ∈ repSet r₀ p (kSeq r₀ j.val)) : r.val < j.val := by
  simp only [repSet, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  exact mem_repNat_lt_of_kSeq hr₀ hj hr

/-! ### Part 2: Initial segments of a permutation and subset-sum minimization -/

/-- The `k` indices where `π` takes values `< k`. -/
def initSeg {m : ℕ} (π : Equiv.Perm (Fin m)) (k : ℕ) : Finset (Fin m) :=
  Finset.filter (fun i : Fin m => (π i).val < k) Finset.univ

lemma mem_initSeg {m : ℕ} (π : Equiv.Perm (Fin m)) (k : ℕ) (i : Fin m) :
    i ∈ initSeg π k ↔ (π i).val < k := by
  simp [initSeg]

lemma card_initSeg {m : ℕ} (π : Equiv.Perm (Fin m)) {k : ℕ} (hk : k ≤ m) :
    (initSeg π k).card = k := by
  have hbij : (initSeg π k).card = (Finset.range k).card := by
    refine Finset.card_bij (fun i _ => (π i).val) ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_range.mpr ((mem_initSeg π k i).mp hi)
    · intro i₁ _ i₂ _ h
      exact π.injective (Fin.ext h)
    · intro r hr
      have hrm : r < m := lt_of_lt_of_le (Finset.mem_range.mp hr) hk
      refine ⟨π.symm ⟨r, hrm⟩, ?_, ?_⟩
      · rw [mem_initSeg, Equiv.apply_symm_apply]
        exact Finset.mem_range.mp hr
      · simp
  simpa using hbij

lemma sum_initSeg {m : ℕ} (π : Equiv.Perm (Fin m)) {k : ℕ} (hk : k ≤ m) :
    ∑ i ∈ initSeg π k, ((π i).val + 1) = tri k := by
  dsimp [tri]
  refine Finset.sum_bij (fun i _ => (π i).val) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_range.mpr ((mem_initSeg π k i).mp hi)
  · intro i₁ _ i₂ _ h
    exact π.injective (Fin.ext h)
  · intro r hr
    have hrm : r < m := lt_of_lt_of_le (Finset.mem_range.mp hr) hk
    refine ⟨π.symm ⟨r, hrm⟩, ?_, ?_⟩
    · rw [mem_initSeg, Equiv.apply_symm_apply]
      exact Finset.mem_range.mp hr
    · simp
  · intro _ _; rfl

lemma tri_add_sdiff_le_sum {m : ℕ} (π : Equiv.Perm (Fin m)) (S : Finset (Fin m)) :
    tri S.card + (S \ initSeg π S.card).card ≤ ∑ i ∈ S, ((π i).val + 1) := by
  set k := S.card
  set B := initSeg π k
  have hSB_card : (B \ S).card = (S \ B).card := by
    have h1 := Finset.card_sdiff_add_card_inter S B
    have h2 := Finset.card_sdiff_add_card_inter B S
    have hB : B.card = k := card_initSeg π (Finset.card_le_univ S |>.trans (by simp))
    rw [Finset.inter_comm] at h2
    omega
  have hBS_sum : ∑ i ∈ B \ S, ((π i).val + 1) ≤ (B \ S).card * k := by
    calc
      ∑ i ∈ B \ S, ((π i).val + 1) ≤ ∑ _i ∈ B \ S, k := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hiB : (π i).val < k := (mem_initSeg π k i).mp (Finset.mem_sdiff.mp hi).1
        omega
      _ = (B \ S).card * k := by simp
  have hSB_sum : (S \ B).card * (k + 1) ≤ ∑ i ∈ S \ B, ((π i).val + 1) := by
    calc
      (S \ B).card * (k + 1) = ∑ _i ∈ S \ B, (k + 1) := by simp
      _ ≤ ∑ i ∈ S \ B, ((π i).val + 1) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hiB : ¬ (π i).val < k := by
          rw [← mem_initSeg]; exact (Finset.mem_sdiff.mp hi).2
        omega
  have hsplit_B : ∑ i ∈ B, ((π i).val + 1) =
      ∑ i ∈ B \ S, ((π i).val + 1) + ∑ i ∈ B ∩ S, ((π i).val + 1) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter B S), Finset.sdiff_union_inter]
  have hsplit_S : ∑ i ∈ S, ((π i).val + 1) =
      ∑ i ∈ S \ B, ((π i).val + 1) + ∑ i ∈ S ∩ B, ((π i).val + 1) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S B), Finset.sdiff_union_inter]
  rw [Finset.inter_comm] at hsplit_B
  have hB_tri : ∑ i ∈ B, ((π i).val + 1) = tri k :=
    sum_initSeg π (Finset.card_le_univ S |>.trans (by simp))
  nlinarith

lemma eq_initSeg_of_sum_le {m : ℕ} (π : Equiv.Perm (Fin m)) (S : Finset (Fin m))
    (h : ∑ i ∈ S, ((π i).val + 1) ≤ tri S.card) : S = initSeg π S.card := by
  have hle := tri_add_sdiff_le_sum π S
  have hsdiff : (S \ initSeg π S.card).card = 0 := by omega
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hsdiff
  exact Finset.eq_of_subset_of_card_le hsdiff
    (by rw [card_initSeg π (Finset.card_le_univ S |>.trans (by simp))])

/-! ### Part 3: The 0/1-polytope construction in `Fin d → ℝ` -/

/-- First `m` coordinate indices inside `Fin d`. -/
def inlIdx {d m p : ℕ} (hmp : m + p = d) (i : Fin m) : Fin d :=
  ⟨i.val, by omega⟩

/-- Last `p` coordinate indices inside `Fin d`. -/
def inrIdx {d m p : ℕ} (hmp : m + p = d) (j : Fin p) : Fin d :=
  ⟨m + j.val, by omega⟩

/-- Combine a vector in `Fin m → ℝ` and a vector in `Fin p → ℝ` into `Fin d → ℝ`. -/
def combineVec {d m p : ℕ} (hmp : m + p = d) (x : Fin m → ℝ) (y : Fin p → ℝ) : Fin d → ℝ :=
  fun r => if h : r.val < m then x ⟨r.val, h⟩ else y ⟨r.val - m, by omega⟩

@[simp] lemma combineVec_inlIdx {d m p : ℕ} (hmp : m + p = d)
    (x : Fin m → ℝ) (y : Fin p → ℝ) (i : Fin m) :
    combineVec hmp x y (inlIdx hmp i) = x i := by
  dsimp [combineVec, inlIdx]
  rw [dif_pos i.isLt]

@[simp] lemma combineVec_inrIdx {d m p : ℕ} (hmp : m + p = d)
    (x : Fin m → ℝ) (y : Fin p → ℝ) (j : Fin p) :
    combineVec hmp x y (inrIdx hmp j) = y j := by
  dsimp [combineVec, inrIdx]
  rw [dif_neg (by omega)]
  congr 1
  ext
  simp

/-- 0/1 indicator vector associated with `S ⊆ Fin m` and `R ⊆ Fin p`. -/
def bitVec {d m p : ℕ} (hmp : m + p = d) (S : Finset (Fin m)) (R : Finset (Fin p)) :
    Fin d → ℝ :=
  combineVec hmp (fun i => if i ∈ S then 1 else 0) (fun j => if j ∈ R then 1 else 0)

lemma bitVec_zero_or_one {d m p : ℕ} (hmp : m + p = d)
    (S : Finset (Fin m)) (R : Finset (Fin p)) (r : Fin d) :
    bitVec hmp S R r = 0 ∨ bitVec hmp S R r = 1 := by
  dsimp [bitVec, combineVec]
  split_ifs <;> simp

@[simp] lemma bitVec_empty_empty {d m p : ℕ} (hmp : m + p = d) :
    bitVec hmp ∅ ∅ = 0 := by
  ext r
  dsimp [bitVec, combineVec]
  split_ifs <;> simp

/-- Primary generators `e_S + f_{R_{|S|}}`. -/
noncomputable def VSet {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) : Set (Fin d → ℝ) :=
  Set.range (fun S : Finset (Fin m) => bitVec hmp S (repSet r₀ p S.card))

/-- Secondary generators `e_T + f_{j}` for `1 ≤ j < p` and `|T| = kSeq r₀ j`. -/
noncomputable def WSet {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) : Set (Fin d → ℝ) :=
  {z | ∃ (j : Fin p) (T : Finset (Fin m)),
    1 ≤ j.val ∧ T.card = kSeq r₀ j.val ∧ z = bitVec hmp T {j}}

/-- Full generator set `VSet ∪ WSet`. -/
noncomputable def genSet {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) : Set (Fin d → ℝ) :=
  VSet r₀ hmp ∪ WSet r₀ hmp

/-- The Castillo–Ferroni 0/1-polytope inside `Fin d → ℝ`. -/
noncomputable def cfPolytope {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) : Set (Fin d → ℝ) :=
  convexHull ℝ (genSet r₀ hmp)

lemma genSet_finite {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) :
    (genSet r₀ hmp).Finite := by
  refine Set.Finite.union (Set.finite_range _) ?_
  have hsub : WSet r₀ hmp ⊆ Set.range (fun p : Fin p × Finset (Fin m) => bitVec hmp p.2 {p.1}) := by
    rintro z ⟨j, T, -, -, rfl⟩
    exact ⟨(j, T), rfl⟩
  exact (Set.finite_range _).subset hsub

lemma zero_mem_VSet {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) :
    (0 : Fin d → ℝ) ∈ VSet r₀ hmp := by
  refine ⟨∅, ?_⟩
  have hrep : repSet r₀ p 0 = ∅ := by
    ext j
    simp [repSet, repNat]
  dsimp only
  rw [Finset.card_empty, hrep, bitVec_empty_empty]

lemma zero_mem_genSet {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) :
    (0 : Fin d → ℝ) ∈ genSet r₀ hmp :=
   Or.inl (zero_mem_VSet r₀ hmp)

lemma zero_mem_cfPolytope {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) :
    (0 : Fin d → ℝ) ∈ cfPolytope r₀ hmp :=
  subset_convexHull ℝ (genSet r₀ hmp) (zero_mem_genSet r₀ hmp)

lemma cfPolytope_isZeroOne {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) :
    IsZeroOnePolytope (cfPolytope r₀ hmp) := by
  refine ⟨genSet r₀ hmp, ?_, rfl⟩
  rintro z (⟨S, rfl⟩ | ⟨j, T, -, -, rfl⟩) r <;> exact bitVec_zero_or_one hmp _ _ r

/-! ### Part 4: Supporting linear functionals and facets indexed by permutations -/

/-- The continuous linear functional `ℓ_π(z) = ∑ s_j y_j - ∑ (π(i) + 1) x_i`. -/
noncomputable def permCLM {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) : (Fin d → ℝ) →L[ℝ] ℝ :=
  (∑ j : Fin p, (sSeq r₀ j.val : ℝ) • ContinuousLinearMap.proj (inrIdx hmp j)) -
    (∑ i : Fin m, ((π i).val + 1 : ℝ) • ContinuousLinearMap.proj (inlIdx hmp i))

lemma permCLM_apply {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) (z : Fin d → ℝ) :
    permCLM r₀ hmp π z =
      (∑ j : Fin p, (sSeq r₀ j.val : ℝ) * z (inrIdx hmp j)) -
        (∑ i : Fin m, ((π i).val + 1 : ℝ) * z (inlIdx hmp i)) := by
  simp [permCLM]

lemma permCLM_bitVec {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) (S : Finset (Fin m)) (R : Finset (Fin p)) :
    permCLM r₀ hmp π (bitVec hmp S R) =
      ((∑ j ∈ R, sSeq r₀ j.val : ℕ) : ℝ) - ((∑ i ∈ S, ((π i).val + 1) : ℕ) : ℝ) := by
  rw [permCLM_apply]
  have hR : (∑ j : Fin p, (sSeq r₀ j.val : ℝ) * bitVec hmp S R (inrIdx hmp j)) =
      ((∑ j ∈ R, sSeq r₀ j.val : ℕ) : ℝ) := by
    simp only [bitVec, combineVec_inrIdx, mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_sum]
  have hS : (∑ i : Fin m, ((π i).val + 1 : ℝ) * bitVec hmp S R (inlIdx hmp i)) =
      ((∑ i ∈ S, ((π i).val + 1) : ℕ) : ℝ) := by
    simp only [bitVec, combineVec_inlIdx, mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_sum, Nat.cast_add, Nat.cast_one]
  rw [hR, hS]

lemma permCLM_nonpos_on_genSet {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) {z : Fin d → ℝ} (hz : z ∈ genSet r₀ hmp) :
    permCLM r₀ hmp π z ≤ 0 := by
  rcases hz with ⟨S, rfl⟩ | ⟨j, T, -, hTcard, rfl⟩
  · rw [permCLM_bitVec]
    have hScard : S.card ≤ m := Finset.card_le_univ S |>.trans (by simp)
    have hrep : ∑ j ∈ repSet r₀ p S.card, sSeq r₀ j.val = tri S.card :=
      sum_repSet hr₀ (by omega)
    rw [hrep, sub_nonpos, Nat.cast_le]
    linarith [tri_add_sdiff_le_sum π S]
  · rw [permCLM_bitVec, Finset.sum_singleton]
    have hrep : sSeq r₀ j.val = tri T.card := by
      dsimp [sSeq]; rw [hTcard]
    rw [hrep, sub_nonpos, Nat.cast_le]
    linarith [tri_add_sdiff_le_sum π T]

lemma permCLM_nonpos_on_cfPolytope {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) {z : Fin d → ℝ} (hz : z ∈ cfPolytope r₀ hmp) :
    permCLM r₀ hmp π z ≤ 0 := by
  have hsub : cfPolytope r₀ hmp ⊆ {w : Fin d → ℝ | permCLM r₀ hmp π w ≤ 0} := by
    refine convexHull_min (fun w hw => permCLM_nonpos_on_genSet hr₀ hrp hmp π hw) ?_
    exact convex_halfSpace_le (permCLM r₀ hmp π).isLinear 0
  exact hsub hz

/-- The exposed facet of `cfPolytope` associated with a permutation `π`. -/
noncomputable def permFacet {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) : Set (Fin d → ℝ) :=
  {z ∈ cfPolytope r₀ hmp | permCLM r₀ hmp π z = 0}

lemma zero_mem_permFacet {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) :
    (0 : Fin d → ℝ) ∈ permFacet r₀ hmp π :=
  ⟨zero_mem_cfPolytope r₀ hmp, map_zero _⟩

lemma permFacet_nonempty {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) :
    (permFacet r₀ hmp π).Nonempty :=
  ⟨0, zero_mem_permFacet r₀ hmp π⟩

lemma isExposed_permFacet {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (π : Equiv.Perm (Fin m)) :
    IsExposed ℝ (cfPolytope r₀ hmp) (permFacet r₀ hmp π) := by
  intro _
  refine ⟨permCLM r₀ hmp π, ?_⟩
  ext z
  simp only [permFacet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hz0⟩
    refine ⟨hz, fun w hw => ?_⟩
    rw [hz0]
    exact permCLM_nonpos_on_cfPolytope hr₀ hrp hmp π hw
  · rintro ⟨hz, hmax⟩
    refine ⟨hz, le_antisymm (permCLM_nonpos_on_cfPolytope hr₀ hrp hmp π hz) ?_⟩
    have h0 := hmax 0 (zero_mem_cfPolytope r₀ hmp)
    simpa using h0

/-- Primary tight point `u_k^π = e_{B_π(k)} + f_{R_k}`. -/
noncomputable def uPt {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) (k : ℕ) : Fin d → ℝ :=
  bitVec hmp (initSeg π k) (repSet r₀ p k)

/-- Secondary tight point `w_j^π = e_{B_π(k_j)} + f_{j}`. -/
noncomputable def wPt {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) (j : Fin p) : Fin d → ℝ :=
  bitVec hmp (initSeg π (kSeq r₀ j.val)) {j}

lemma uPt_mem_permFacet {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) {k : ℕ} (hk : k ≤ m) :
    uPt r₀ hmp π k ∈ permFacet r₀ hmp π := by
  have hcard : (initSeg π k).card = k := card_initSeg π hk
  have hmemV : uPt r₀ hmp π k ∈ VSet r₀ hmp := by
    refine ⟨initSeg π k, ?_⟩
    dsimp [uPt]
    rw [hcard]
  refine ⟨subset_convexHull ℝ (genSet r₀ hmp) (Or.inl hmemV), ?_⟩
  dsimp [uPt]
  rw [permCLM_bitVec, sum_repSet hr₀ (by omega), sum_initSeg π hk, sub_self]

lemma wPt_mem_permFacet {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) (j : Fin p) (hj : 1 ≤ j.val) :
    wPt r₀ hmp π j ∈ permFacet r₀ hmp π := by
  have hk_le : kSeq r₀ j.val ≤ m := by
    have := kSeq_le r₀ (by omega) j.isLt
    omega
  have hcard : (initSeg π (kSeq r₀ j.val)).card = kSeq r₀ j.val := card_initSeg π hk_le
  have hmemW : wPt r₀ hmp π j ∈ WSet r₀ hmp :=
    ⟨j, initSeg π (kSeq r₀ j.val), hj, hcard, rfl⟩
  refine ⟨subset_convexHull ℝ (genSet r₀ hmp) (Or.inr hmemW), ?_⟩
  dsimp [wPt]
  rw [permCLM_bitVec, Finset.sum_singleton, sum_initSeg π hk_le]
  dsimp [sSeq]
  rw [sub_self]

lemma permFacet_injective {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) :
    Function.Injective (permFacet r₀ hmp : Equiv.Perm (Fin m) → Set (Fin d → ℝ)) := by
  intro π₁ π₂ hEq
  have hle : ∀ (π π' : Equiv.Perm (Fin m)),
      permFacet r₀ hmp π ⊆ permFacet r₀ hmp π' →
      ∀ i : Fin m, (π' i).val ≤ (π i).val := by
    intro π π' hsub i
    set k := (π i).val + 1
    have hk_le : k ≤ m := Nat.succ_le_of_lt (π i).isLt
    have hu_mem : uPt r₀ hmp π k ∈ permFacet r₀ hmp π' :=
      hsub (uPt_mem_permFacet hr₀ hrp hmp π hk_le)
    have hclm : permCLM r₀ hmp π' (uPt r₀ hmp π k) = 0 := hu_mem.2
    dsimp [uPt] at hclm
    rw [permCLM_bitVec, sum_repSet hr₀ (by omega), sub_eq_zero] at hclm
    have hsum_eq : ∑ x ∈ initSeg π k, ((π' x).val + 1) = tri (initSeg π k).card := by
      rw [card_initSeg π hk_le]
      exact_mod_cast hclm.symm
    have hinit_eq : initSeg π k = initSeg π' k := by
      have h := eq_initSeg_of_sum_le π' (initSeg π k) (le_of_eq hsum_eq)
      rwa [card_initSeg π hk_le] at h
    have hi_mem : i ∈ initSeg π' k := by
      rw [← hinit_eq, mem_initSeg]
      exact Nat.lt_succ_self (π i).val
    rw [mem_initSeg] at hi_mem
    omega
  ext i
  exact le_antisymm (hle π₂ π₁ hEq.symm.subset i) (hle π₁ π₂ hEq.subset i)

/-! ### Part 5: Linear independence and dimension of `permFacet` and `cfPolytope` -/

/-- Auxiliary difference vector `d_j = w_j^π - u_{k_j}^π`. -/
noncomputable def dVec {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) (j : Fin p) : Fin d → ℝ :=
  wPt r₀ hmp π j - uPt r₀ hmp π (kSeq r₀ j.val)

lemma dVec_inlIdx {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) (j : Fin p) (i : Fin m) :
    dVec r₀ hmp π j (inlIdx hmp i) = 0 := by
  simp [dVec, wPt, uPt, bitVec]

lemma dVec_inrIdx_self {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) (j : Fin p) (hj : 1 ≤ j.val) :
    dVec r₀ hmp π j (inrIdx hmp j) = 1 := by
  have hj_not_mem : j ∉ repSet r₀ p (kSeq r₀ j.val) := by
    intro hmem
    exact Nat.lt_irrefl j.val (mem_repSet_lt hr₀ j j hj hmem)
  simp [dVec, wPt, uPt, bitVec, hj_not_mem]

lemma dVec_inrIdx_of_lt {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) (r j : Fin p) (hr : 1 ≤ r.val) (hrj : r.val < j.val) :
    dVec r₀ hmp π r (inrIdx hmp j) = 0 := by
  have hne : j ≠ r := fun h => by subst h; exact Nat.lt_irrefl _ hrj
  have hj_not_mem : j ∉ repSet r₀ p (kSeq r₀ r.val) := by
    intro hmem
    have := mem_repSet_lt hr₀ r j hr hmem
    omega
  simp [dVec, wPt, uPt, bitVec, hne, hj_not_mem]

/-- Point of `VSet` outside the facet hyperplane `permCLM = 0`. -/
noncomputable def extraPt {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) : Fin d → ℝ :=
  bitVec hmp {π.symm ⟨1, hm⟩} (repSet r₀ p 1)

lemma extraPt_mem_cfPolytope {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) :
    extraPt r₀ hmp hm π ∈ cfPolytope r₀ hmp := by
  refine subset_convexHull ℝ (genSet r₀ hmp) (Or.inl ?_)
  refine ⟨{π.symm ⟨1, hm⟩}, ?_⟩
  simp [extraPt]

lemma permCLM_extraPt {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) :
    permCLM r₀ hmp π (extraPt r₀ hmp hm π) = -1 := by
  dsimp [extraPt]
  rw [permCLM_bitVec, sum_repSet hr₀ (by omega), Finset.sum_singleton, Equiv.apply_symm_apply]
  norm_num

/-- Family of `d` basis vectors: index `0` is `extraPt`, `1..m` are `uPt`, `m+1..d-1` are `dVec`. -/
noncomputable def fullBasis {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) (idx : Fin d) : Fin d → ℝ :=
  if idx.val = 0 then
    extraPt r₀ hmp hm π
  else if h : idx.val ≤ m then
    uPt r₀ hmp π idx.val
  else
    dVec r₀ hmp π ⟨idx.val - m, by omega⟩

lemma fullBasis_mem_facet_direction {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) {idx : Fin d} (hidx : idx.val ≠ 0) :
    fullBasis r₀ hmp hm π idx ∈ (affineSpan ℝ (permFacet r₀ hmp π)).direction := by
  rw [direction_affineSpan]
  dsimp [fullBasis]
  rw [if_neg hidx]
  split_ifs with hle
  · have hu := uPt_mem_permFacet hr₀ hrp hmp π hle
    have h0 := zero_mem_permFacet r₀ hmp π
    simpa using vsub_mem_vectorSpan ℝ hu h0
  · set j : Fin p := ⟨idx.val - m, by omega⟩
    have hj : 1 ≤ j.val := by dsimp [j]; omega
    have hw := wPt_mem_permFacet hr₀ hrp hmp hm π j hj
    have hk_le : kSeq r₀ j.val ≤ m := by
      have := kSeq_le r₀ (by omega) j.isLt
      omega
    have hu := uPt_mem_permFacet hr₀ hrp hmp π hk_le
    exact vsub_mem_vectorSpan ℝ hw hu

lemma fullBasis_mem_polytope_direction {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) (idx : Fin d) :
    fullBasis r₀ hmp hm π idx ∈ (affineSpan ℝ (cfPolytope r₀ hmp)).direction := by
  by_cases hidx : idx.val = 0
  · rw [direction_affineSpan]
    dsimp [fullBasis]
    rw [if_pos hidx]
    have hex := extraPt_mem_cfPolytope r₀ hmp hm π
    have h0 := zero_mem_cfPolytope r₀ hmp
    simpa using vsub_mem_vectorSpan ℝ hex h0
  · have hsub : permFacet r₀ hmp π ⊆ cfPolytope r₀ hmp := fun _ hz => hz.1
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hsub)
      (fullBasis_mem_facet_direction hr₀ hrp hmp hm π hidx)

lemma permCLM_eq_zero_on_facet_direction {d m p : ℕ} (r₀ : ℕ) (hmp : m + p = d)
    (π : Equiv.Perm (Fin m)) {v : Fin d → ℝ}
    (hv : v ∈ (affineSpan ℝ (permFacet r₀ hmp π)).direction) :
    permCLM r₀ hmp π v = 0 := by
  rw [direction_affineSpan] at hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    simp [map_sub, hx.2, hy.2]
  · simp
  · intro x y _ _ hx hy
    simp [map_add, hx, hy]
  · intro a x _ hx
    simp [map_smul, hx]

lemma linearIndependent_fullBasis {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) :
    LinearIndependent ℝ (fullBasis r₀ hmp hm π) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hd_pos : 0 < d := by omega
  let idx0 : Fin d := ⟨0, hd_pos⟩
  -- Step 1: c idx0 = 0 by applying permCLM
  have hc0 : c idx0 = 0 := by
    have hmap : permCLM r₀ hmp π (∑ idx : Fin d, c idx • fullBasis r₀ hmp hm π idx) = 0 := by
      rw [hc, map_zero]
    rw [map_sum] at hmap
    have hsum : (∑ idx : Fin d, permCLM r₀ hmp π (c idx • fullBasis r₀ hmp hm π idx)) =
        c idx0 * (-1) := by
      rw [Finset.sum_eq_single idx0]
      · simp only [map_smul, smul_eq_mul]
        congr 1
        dsimp [fullBasis, idx0]
        exact permCLM_extraPt hr₀ hrp hmp hm π
      · intro idx _ hne
        have hidx0 : idx.val ≠ 0 := fun h => hne (Fin.ext h)
        simp only [map_smul, smul_eq_mul]
        rw [permCLM_eq_zero_on_facet_direction r₀ hmp π
          (fullBasis_mem_facet_direction hr₀ hrp hmp hm π hidx0), mul_zero]
      · intro h; exact (h (Finset.mem_univ idx0)).elim
    linarith
  -- Step 2: for 1 ≤ k ≤ m, the sum of c over k..m is 0, hence c = 0 on 1..m
  have hfirst_coord : ∀ r : Fin m,
      ∑ idx : Fin d, c idx * (if idx.val ≠ 0 ∧ idx.val ≤ m ∧ r.val < idx.val then (1 : ℝ) else 0) = 0 := by
    intro r
    let i := π.symm r
    have hval := congr_fun hc (inlIdx hmp i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hval
    suffices h : ∑ idx : Fin d, c idx * (if idx.val ≠ 0 ∧ idx.val ≤ m ∧ r.val < idx.val then (1 : ℝ) else 0) =
        ∑ idx : Fin d, c idx * fullBasis r₀ hmp hm π idx (inlIdx hmp i) by linarith
    refine Finset.sum_congr rfl (fun idx _ => ?_)
    by_cases h0 : idx.val = 0
    · have hidx : idx = idx0 := Fin.ext h0
      subst hidx
      simp [hc0, idx0]
    · by_cases hle : idx.val ≤ m
      · by_cases hlt : r.val < idx.val
        · have hcond : idx.val ≠ 0 ∧ idx.val ≤ m ∧ r.val < idx.val := ⟨h0, hle, hlt⟩
          rw [if_pos hcond]
          dsimp [fullBasis]
          rw [if_neg h0, dif_pos hle]
          dsimp [uPt, bitVec]
          rw [combineVec_inlIdx]
          have hi : i ∈ initSeg π idx.val := by
            rw [mem_initSeg, Equiv.apply_symm_apply]; exact hlt
          rw [if_pos hi]
        · have hcond : ¬ (idx.val ≠ 0 ∧ idx.val ≤ m ∧ r.val < idx.val) := fun h => hlt h.2.2
          rw [if_neg hcond]
          dsimp [fullBasis]
          rw [if_neg h0, dif_pos hle]
          dsimp [uPt, bitVec]
          rw [combineVec_inlIdx]
          have hi : i ∉ initSeg π idx.val := by
            rw [mem_initSeg, Equiv.apply_symm_apply]; exact hlt
          rw [if_neg hi]
      · have hcond : ¬ (idx.val ≠ 0 ∧ idx.val ≤ m ∧ r.val < idx.val) := fun h => hle h.2.1
        rw [if_neg hcond]
        dsimp [fullBasis]
        rw [if_neg h0, dif_neg hle, dVec_inlIdx]
  have hc_m : ∀ idx : Fin d, idx.val ≤ m → c idx = 0 := by
    intro idx hle
    by_cases h0 : idx.val = 0
    · have hidx : idx = idx0 := Fin.ext h0
      simpa [hidx] using hc0
    · have h1 : 1 ≤ idx.val := by omega
      let r1 : Fin m := ⟨idx.val - 1, by omega⟩
      have hr1 := hfirst_coord r1
      by_cases hlt_m : idx.val < m
      · let r2 : Fin m := ⟨idx.val, hlt_m⟩
        have hr2 := hfirst_coord r2
        have hdiff : (∑ x : Fin d, c x * (if x.val ≠ 0 ∧ x.val ≤ m ∧ r1.val < x.val then (1 : ℝ) else 0)) -
            (∑ x : Fin d, c x * (if x.val ≠ 0 ∧ x.val ≤ m ∧ r2.val < x.val then (1 : ℝ) else 0)) = c idx := by
          rw [← Finset.sum_sub_distrib, Finset.sum_eq_single idx]
          · have cond1 : idx.val ≠ 0 ∧ idx.val ≤ m ∧ r1.val < idx.val := by
              refine ⟨h0, hle, ?_⟩; dsimp [r1]; omega
            have cond2 : ¬ (idx.val ≠ 0 ∧ idx.val ≤ m ∧ r2.val < idx.val) := by
              dsimp [r2]; omega
            rw [if_pos cond1, if_neg cond2]
            ring
          · intro x _ hne
            have hx_ne : x.val ≠ idx.val := fun h => hne (Fin.ext h)
            have hiff : (x.val ≠ 0 ∧ x.val ≤ m ∧ r1.val < x.val) ↔
                (x.val ≠ 0 ∧ x.val ≤ m ∧ r2.val < x.val) := by
              dsimp [r1, r2]; omega
            by_cases hcond : x.val ≠ 0 ∧ x.val ≤ m ∧ r2.val < x.val
            · rw [if_pos (hiff.mpr hcond), if_pos hcond, sub_self]
            · rw [if_neg (mt hiff.mp hcond), if_neg hcond, sub_self]
          · intro h; exact (h (Finset.mem_univ idx)).elim
        linarith
      · have heq_m : idx.val = m := by omega
        have hsingle : (∑ x : Fin d, c x * (if x.val ≠ 0 ∧ x.val ≤ m ∧ r1.val < x.val then (1 : ℝ) else 0)) = c idx := by
          rw [Finset.sum_eq_single idx]
          · have cond1 : idx.val ≠ 0 ∧ idx.val ≤ m ∧ r1.val < idx.val := by
              refine ⟨h0, hle, ?_⟩; dsimp [r1]; omega
            rw [if_pos cond1, mul_one]
          · intro x _ hne
            have hx_ne : x.val ≠ idx.val := fun h => hne (Fin.ext h)
            have hnot : ¬ (x.val ≠ 0 ∧ x.val ≤ m ∧ r1.val < x.val) := by
              dsimp [r1]; omega
            rw [if_neg hnot, mul_zero]
          · intro h; exact (h (Finset.mem_univ idx)).elim
        linarith
  -- Step 3: downward induction on idx.val > m using upper-triangularity of dVec
  have hc_down : ∀ t : ℕ, ∀ idx : Fin d, d - t ≤ idx.val → c idx = 0 := by
    intro t
    induction' t with t ih
    · intro idx h; omega
    · intro idx hidx
      by_cases hle : idx.val ≤ m
      · exact hc_m idx hle
      · by_cases hgt : d - t ≤ idx.val
        · exact ih idx hgt
        · set j : Fin p := ⟨idx.val - m, by omega⟩
          have hj1 : 1 ≤ j.val := by dsimp [j]; omega
          have hval := congr_fun hc (inrIdx hmp j)
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hval
          have hsingle : (∑ x : Fin d, c x * fullBasis r₀ hmp hm π x (inrIdx hmp j)) = c idx := by
            rw [Finset.sum_eq_single idx]
            · dsimp [fullBasis]
              rw [if_neg (by omega), dif_neg hle]
              change c idx * dVec r₀ hmp π j (inrIdx hmp j) = c idx
              rw [dVec_inrIdx_self hr₀ hmp π j hj1, mul_one]
            · intro x _ hne
              have hx_ne : x.val ≠ idx.val := fun h => hne (Fin.ext h)
              by_cases hxm : x.val ≤ m
              · rw [hc_m x hxm, zero_mul]
              · by_cases hxt : x.val > idx.val
                · rw [ih x (by omega), zero_mul]
                · have hxl : x.val < idx.val := by omega
                  dsimp [fullBasis]
                  rw [if_neg (by omega), dif_neg hxm]
                  set r : Fin p := ⟨x.val - m, by omega⟩
                  have hr1 : 1 ≤ r.val := by dsimp [r]; omega
                  have hrj : r.val < j.val := by dsimp [r, j]; omega
                  rw [dVec_inrIdx_of_lt hr₀ hmp π r j hr1 hrj, mul_zero]
            · intro h; exact (h (Finset.mem_univ idx)).elim
          linarith
  intro idx
  exact hc_down d idx (by omega)

lemma cfPolytope_isDPolytope {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (hm : 2 ≤ m) :
    IsDPolytope (cfPolytope r₀ hmp) := by
  refine ⟨⟨genSet r₀ hmp, genSet_finite r₀ hmp, ⟨0, zero_mem_genSet r₀ hmp⟩, rfl⟩, ?_⟩
  have hli := linearIndependent_fullBasis hr₀ hrp hmp hm (1 : Equiv.Perm (Fin m))
  let S := (affineSpan ℝ (cfPolytope r₀ hmp)).direction
  let b : Fin d → S := fun idx =>
    ⟨fullBasis r₀ hmp hm 1 idx, fullBasis_mem_polytope_direction hr₀ hrp hmp hm 1 idx⟩
  have hli_S : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc
    apply hli c
    ext r
    have := congr_arg Subtype.val hc
    simpa using congr_fun this r
  have hcard_le : Fintype.card (Fin d) ≤ Module.finrank ℝ S :=
    hli_S.fintype_card_le_finrank
  have hle_top : Module.finrank ℝ S ≤ Module.finrank ℝ (Fin d → ℝ) :=
    Submodule.finrank_le S
  simp only [Fintype.card_fin, Module.finrank_fin_fun] at hcard_le hle_top
  have hfin : Module.finrank ℝ S = Module.finrank ℝ (Fin d → ℝ) := by
    rw [Module.finrank_fin_fun]; omega
  have hdir_top : (affineSpan ℝ (cfPolytope r₀ hmp)).direction = ⊤ :=
    Submodule.eq_top_of_finrank_eq hfin
  rw [eq_top_iff]
  intro x _
  have h0 : (0 : Fin d → ℝ) ∈ affineSpan ℝ (cfPolytope r₀ hmp) :=
    subset_affineSpan ℝ _ (zero_mem_cfPolytope r₀ hmp)
  have hx_sub : x -ᵥ (0 : Fin d → ℝ) ∈ (affineSpan ℝ (cfPolytope r₀ hmp)).direction := by
    rw [hdir_top]; trivial
  simpa using AffineSubspace.vadd_mem_of_mem_direction hx_sub h0

lemma finrank_permFacet {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (hm : 2 ≤ m)
    (π : Equiv.Perm (Fin m)) :
    Module.finrank ℝ (affineSpan ℝ (permFacet r₀ hmp π)).direction = d - 1 := by
  let S := (affineSpan ℝ (permFacet r₀ hmp π)).direction
  have hd_pos : 0 < d := by omega
  let z0 : Fin d := ⟨0, hd_pos⟩
  let idxSub := {idx : Fin d // idx ≠ z0}
  have hli := linearIndependent_fullBasis hr₀ hrp hmp hm π
  let b : idxSub → S := fun idx =>
    ⟨fullBasis r₀ hmp hm π idx.val,
      fullBasis_mem_facet_direction hr₀ hrp hmp hm π (fun h => idx.property (Fin.ext h))⟩
  have hli_S : LinearIndependent ℝ b := by
    have hli' : LinearIndependent ℝ (fun idx : idxSub => fullBasis r₀ hmp hm π idx.val) :=
      hli.comp Subtype.val Subtype.val_injective
    rw [Fintype.linearIndependent_iff] at hli' ⊢
    intro c hc
    apply hli' c
    ext r
    have := congr_arg Subtype.val hc
    simpa using congr_fun this r
  have hcard_idxSub : Fintype.card idxSub = d - 1 := by
    simp [idxSub, Fintype.card_subtype_compl]
  have hge : d - 1 ≤ Module.finrank ℝ S := by
    rw [← hcard_idxSub]
    exact hli_S.fintype_card_le_finrank
  have hne_top : S ≠ ⊤ := by
    intro htop
    have hex_mem : extraPt r₀ hmp hm π ∈ S := by rw [htop]; trivial
    have h0 := permCLM_eq_zero_on_facet_direction r₀ hmp π hex_mem
    have h1 := permCLM_extraPt hr₀ hrp hmp hm π
    linarith
  have hlt : Module.finrank ℝ S < d := by
    have := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne_top)
    simpa [Module.finrank_fin_fun] using this
  change Module.finrank ℝ S < d at hlt
  change Module.finrank ℝ S = d - 1
  omega

/-! ### Part 6: Finite exposed-face bound and factorial lower bound on `faceCount` -/

theorem aux_pp_finite {d k : ℕ} (V : Finset (Fin d → ℝ)) :
    {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (V : Set (Fin d → ℝ))) F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k}.Finite := by
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  have key : ∀ F F' : Set (Fin d → ℝ), F.Nonempty → IsExposed ℝ P F → F'.Nonempty →
      IsExposed ℝ P F' → F ∩ ↑V ⊆ F' → F ⊆ F' := by
    intro F F' hF hFe hF' hF'e hsub y hy
    obtain ⟨g, hg⟩ := hFe hF
    have hyP : y ∈ P := by rw [hg] at hy; exact hy.1
    have hymax : ∀ y' ∈ P, g y' ≤ g y := by rw [hg] at hy; exact hy.2
    obtain ⟨w, hw0, hw1, hwy⟩ := Finset.mem_convexHull'.mp hyP
    have hVP : ∀ v ∈ V, v ∈ P := fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    have hsum0 : ∑ v ∈ V, w v * (g y - g v) = 0 := by
      have h1 : g y = ∑ v ∈ V, w v * g v := by
        rw [← hwy, map_sum]; simp [map_smul, smul_eq_mul]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun v hv =>
      mul_nonneg (hw0 v hv) (by linarith [hymax v (hVP v hv)]))).mp hsum0
    have hF'c : Convex ℝ F' := hF'e.convex (convex_convexHull ℝ _)
    have hmem : ∀ v ∈ V.filter (fun v => w v ≠ 0), v ∈ F' := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have h1 := hterm v hv.1
      have h2 : g y - g v = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hv.2
        · exact h
      apply hsub
      refine ⟨?_, Finset.mem_coe.mpr hv.1⟩
      rw [hg]
      refine ⟨hVP v hv.1, fun y' hy' => ?_⟩
      linarith [hymax y' hy']
    have hsum1 : ∑ v ∈ V.filter (fun v => w v ≠ 0), w v = 1 := by
      rw [Finset.sum_filter_ne_zero]; exact hw1
    have hsumy : ∑ v ∈ V.filter (fun v => w v ≠ 0), w v • v = y := by
      rw [← hwy]
      refine Finset.sum_filter_of_ne (fun v _ hne => ?_)
      intro h0; rw [h0, zero_smul] at hne; exact hne rfl
    rw [← hsumy]
    exact hF'c.sum_mem (fun v hv => hw0 v (Finset.mem_filter.mp hv).1) hsum1 hmem
  refine Set.Finite.of_finite_image (f := fun F => F ∩ (V : Set (Fin d → ℝ))) ?_ ?_
  · refine (V.finite_toSet.finite_subsets).subset ?_
    rintro _ ⟨F, _, rfl⟩
    exact Set.inter_subset_right
  · intro F hF F' hF' heq
    simp only at heq
    apply subset_antisymm
    · exact key F F' hF.1 hF.2.1 hF'.1 hF'.2.1 (heq ▸ Set.inter_subset_left)
    · exact key F' F hF'.1 hF'.2.1 hF.1 hF.2.1 (heq.symm ▸ Set.inter_subset_left)

lemma factorial_le_faceCount_cfPolytope {d m p : ℕ} {r₀ : ℕ} (hr₀ : 3 ≤ r₀)
    (hrp : r₀ + m = p + 1) (hmp : m + p = d) (hm : 2 ≤ m) :
    m.factorial ≤ faceCount (cfPolytope r₀ hmp) (d - 1) := by
  dsimp [faceCount]
  let S := {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ (cfPolytope r₀ hmp) F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = d - 1}
  have hS_fin : S.Finite := by
    let V := (genSet_finite r₀ hmp).toFinset
    have hP : cfPolytope r₀ hmp = convexHull ℝ (V : Set (Fin d → ℝ)) := by
      dsimp [cfPolytope, V]
      rw [Set.Finite.coe_toFinset]
    dsimp [S]
    rw [hP]
    exact aux_pp_finite V
  have hrange_sub : Set.range (permFacet r₀ hmp) ⊆ S := by
    rintro F ⟨π, rfl⟩
    exact ⟨permFacet_nonempty r₀ hmp π,
      isExposed_permFacet hr₀ hrp hmp π,
      finrank_permFacet hr₀ hrp hmp hm π⟩
  have hcard_range : (Set.range (permFacet r₀ hmp)).ncard = m.factorial := by
    rw [Set.ncard_range_of_injective (permFacet_injective hr₀ hrp hmp),
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [← hcard_range]
  exact Set.ncard_le_ncard hrange_sub hS_fin

/-! ### Part 7: Elementary factorial and logarithmic growth inequalities -/

lemma pow_lt_factorial_add {a : ℕ} (ha : 2 ≤ a) :
    ∀ k : ℕ, a ^ k < (a + k).factorial
  | 0 => by
      simp only [pow_zero, Nat.add_zero]
      have : 2 ≤ a.factorial := by
        calc 2 = (2 : ℕ).factorial := rfl
          _ ≤ a.factorial := Nat.factorial_le ha
      omega
  | k + 1 => by
      rw [pow_succ, Nat.add_succ, Nat.factorial_succ]
      have ih := pow_lt_factorial_add ha k
      have hpos : 0 < a := by omega
      calc
        a ^ k * a < (a + k).factorial * a := Nat.mul_lt_mul_of_pos_right ih hpos
        _ ≤ (a + k).factorial * (a + k + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (a + k + 1) * (a + k).factorial := Nat.mul_comm _ _

lemma exp_growth_lt_factorial {d : ℕ} (hd : 64 ≤ d) :
    (Real.exp (1 / 16)) ^ ((d : ℝ) * Real.log (d : ℝ)) < (((d - 2) / 2).factorial : ℝ) := by
  set m := (d - 2) / 2
  set a := d / 6
  have ha2 : 2 ≤ a := by dsimp [a]; omega
  have h2a_le_m : a + a ≤ m := by dsimp [a, m]; omega
  have hpow_lt : a ^ a < m.factorial :=
    lt_of_lt_of_le (pow_lt_factorial_add ha2 a) (Nat.factorial_le h2a_le_m)
  have hpow_lt_real : ((a : ℝ) ^ a) < (m.factorial : ℝ) := by
    exact_mod_cast hpow_lt
  refine lt_of_le_of_lt ?_ hpow_lt_real
  have ha_pos : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have hd_pos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have ha_pow : (a : ℝ) ^ a = Real.exp ((a : ℝ) * Real.log (a : ℝ)) := by
    rw [← Real.rpow_natCast (a : ℝ) a, Real.rpow_def_of_pos ha_pos, mul_comm]
  rw [← Real.exp_mul, ha_pow, Real.exp_le_exp]
  have hd_le_8a : (d : ℝ) ≤ 8 * (a : ℝ) := by
    have : d ≤ 8 * a := by dsimp [a]; omega
    exact_mod_cast this
  have hd_le_sq : (d : ℝ) ≤ (a : ℝ) * (a : ℝ) := by
    have ha10 : 10 ≤ a := by dsimp [a]; omega
    have hd6 : d ≤ 6 * a + 5 := by dsimp [a]; omega
    have hnat : d ≤ a * a := by nlinarith
    exact_mod_cast hnat
  have hlog_le : Real.log (d : ℝ) ≤ 2 * Real.log (a : ℝ) := by
    have := Real.log_le_log hd_pos hd_le_sq
    rw [Real.log_mul ha_pos.ne' ha_pos.ne'] at this
    linarith
  have hlog_nonneg : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
  nlinarith

end BaranyPorBinaryFacetGrowth

open BaranyPorBinaryFacetGrowth

theorem barany_por_binary_facet_growth :
    ∃ c : ℝ, 1 < c ∧ ∃ D : ℕ, 2 ≤ D ∧
      ∀ d : ℕ, D ≤ d → ∃ P : Set (Fin d → ℝ),
        IsDPolytope P ∧ IsZeroOnePolytope P ∧
          c ^ ((d : ℝ) * Real.log (d : ℝ)) < (faceCount P (d - 1) : ℝ) := by
  refine ⟨Real.exp (1 / 16), Real.one_lt_exp_iff.mpr (by norm_num), 64, by omega, ?_⟩
  intro d hd
  let m := (d - 2) / 2
  let p := d - m
  let r₀ := d - 2 * m + 1
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hr₀ : 3 ≤ r₀ := by dsimp [r₀, m]; omega
  have hrp : r₀ + m = p + 1 := by dsimp [r₀, p, m]; omega
  have hmp : m + p = d := by dsimp [p, m]; omega
  refine ⟨cfPolytope r₀ hmp,
    cfPolytope_isDPolytope hr₀ hrp hmp hm,
    cfPolytope_isZeroOne r₀ hmp, ?_⟩
  have hfac : (m.factorial : ℝ) ≤ (faceCount (cfPolytope r₀ hmp) (d - 1) : ℝ) := by
    exact_mod_cast factorial_le_faceCount_cfPolytope hr₀ hrp hmp hm
  exact lt_of_lt_of_le (exp_growth_lt_factorial hd) hfac

end Grunbaum2003

open Grunbaum2003

theorem solution :
    ∃ c : ℝ, 1 < c ∧ ∃ D : ℕ, 2 ≤ D ∧
      ∀ d : ℕ, D ≤ d → ∃ P : Set (Fin d → ℝ),
        IsDPolytope P ∧ IsZeroOnePolytope P ∧
          c ^ ((d : ℝ) * Real.log (d : ℝ)) < (faceCount P (d - 1) : ℝ) :=
  barany_por_binary_facet_growth

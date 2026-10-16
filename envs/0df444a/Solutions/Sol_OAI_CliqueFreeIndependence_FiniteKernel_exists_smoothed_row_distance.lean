-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteKernel.exists_smoothed_row_distance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:20:47.385081+00:00
-- url     : https://prove2.me/submissions/e10e3c87-ad34-4a06-8cb4-4e45d9399e2b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean:L288-L310
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteKernel.exists_smoothed_row_distance. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_entropy_mix_gap

-- ---- from OAI.Combinatorics.CliqueFree.FiniteEntropy ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

lemma sqrt_sub_sq_le_relTerm {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ p * Real.log (p / q) - p + q := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp, Real.sq_sqrt hq]
  have hq' := hs hp
  have hsp := Real.sqrt_pos.2 hp
  have hsq := Real.sqrt_pos.2 hq'
  have h := Real.log_le_sub_one_of_pos (div_pos hsq hsp)
  have hl : Real.log (Real.sqrt q / Real.sqrt p) = -(Real.log (p / q)) / 2 := by
    rw [Real.log_div hsq.ne' hsp.ne', Real.log_sqrt hq, Real.log_sqrt hp.le,
      Real.log_div hp.ne' hq'.ne']
    ring
  rw [hl] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * p by positivity)
  have hc : p * (Real.sqrt q / Real.sqrt p) = Real.sqrt p * Real.sqrt q := by
    calc
      _ = (Real.sqrt p) ^ 2 * (Real.sqrt q / Real.sqrt p) := by rw [Real.sq_sqrt hp.le]
      _ = Real.sqrt p * Real.sqrt q := by field_simp
  have hp2 := Real.sq_sqrt hp.le
  have hq2 := Real.sq_sqrt hq
  nlinarith

lemma hellinger_le_divergence {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) ≤ divergence p q := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    sqrt_sub_sq_le_relTerm (hp.1 i) (hq.1 i) (hs i)
  simpa [divergence, sum_add_distrib, sum_sub_distrib, hp.2, hq.2] using h

lemma tv_nonneg (p q : I → ℝ) : 0 ≤ tv p q := by
  exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)

lemma tv_sq_le_hellinger {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q) :
    tv p q ^ 2 ≤ ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
  let f := fun i ↦ |Real.sqrt (p i) - Real.sqrt (q i)|
  let g := fun i ↦ Real.sqrt (p i) + Real.sqrt (q i)
  have hfactor (i : I) : |p i - q i| = f i * g i := by
    have he : p i - q i =
        (Real.sqrt (p i) - Real.sqrt (q i)) *
          (Real.sqrt (p i) + Real.sqrt (q i)) := by
      nlinarith [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i)]
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (p i) + Real.sqrt (q i))]
  have hsum : (∑ i, f i ^ 2) + (∑ i, g i ^ 2) = 4 := by
    rw [← sum_add_distrib]
    calc
      _ = (∑ i, (2 * p i + 2 * q i)) := by
        apply sum_congr rfl
        intro i _
        dsimp [f, g]
        rw [sq_abs]
        nlinarith [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i)]
      _ = 4 := by norm_num [sum_add_distrib, ← mul_sum, hp.2, hq.2]
  have hf0 : 0 ≤ ∑ i, f i ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hg4 : ∑ i, g i ^ 2 ≤ 4 := by linarith
  have hc := sum_mul_sq_le_sq_mul_sq univ f g
  have hle := mul_le_mul_of_nonneg_left hg4 hf0
  have he : (∑ i, f i ^ 2) = ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
    simp [f]
  rw [tv, show (∑ i, |p i - q i|) = ∑ i, f i * g i from sum_congr rfl (fun i _ ↦ hfactor i)]
  rw [← he]
  nlinarith

lemma tv_comm (p q : I → ℝ) : tv p q = tv q p := by
  simp only [tv, abs_sub_comm]

lemma tv_triangle (p q r : I → ℝ) : tv p r ≤ tv p q + tv q r := by
  have h := sum_le_sum (s := univ) fun i _ ↦ abs_sub_le (p i) (q i) (r i)
  simpa only [sum_add_distrib, tv, ← add_div] using div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)

lemma weighted_sq_le {a f : I → ℝ} (ha : IsProb a) :
    (∑ i, a i * f i) ^ 2 ≤ ∑ i, a i * (f i) ^ 2 := by
  let m := ∑ i, a i * f i
  have h := sum_nonneg (s := univ) fun i _ ↦
    mul_nonneg (ha.1 i) (sq_nonneg (f i - m))
  have he : (∑ i, a i * (f i - m) ^ 2) = (∑ i, a i * (f i) ^ 2) - m ^ 2 := by
    calc
      _ = ∑ i, (a i * (f i) ^ 2 - 2 * (a i * f i) * m + a i * m ^ 2) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, ← sum_mul, ha.2]
        dsimp [m]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

variable {J : Type v} [Fintype J]

/-- Mixing finitely many probability vectors. -/
lemma mix_isProb {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a)
    (hp : ∀ j, IsProb (p j)) : IsProb (fun i ↦ ∑ j, a j * p j i) := by
  refine ⟨fun i ↦ sum_nonneg fun j _ ↦ mul_nonneg (ha.1 j) ((hp j).1 i), ?_⟩
  rw [sum_comm]
  simp_rw [← mul_sum, fun j ↦ (hp j).2, mul_one]
  exact ha.2

omit [Fintype I] in
lemma mix_support {a : J → ℝ} {p : J → I → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hp : ∀ j i, 0 ≤ p j i) {j : J} (hj : 0 < a j) {i : I} (hi : 0 < p j i) :
    0 < ∑ k, a k * p k i := by
  classical
  exact (mul_pos hj hi).trans_le (single_le_sum
    (fun k _ ↦ mul_nonneg (ha k) (hp k i)) (mem_univ j))

lemma average_tv_sq_le_average_divergence {a : J → ℝ} (ha : IsProb a)
    {p q : J → I → ℝ} (hp : ∀ j, IsProb (p j)) (hq : ∀ j, IsProb (q j))
    (hs : ∀ j, 0 < a j → ∀ i, 0 < p j i → 0 < q j i) :
    (∑ j, a j * tv (p j) (q j)) ^ 2 ≤ ∑ j, a j * divergence (p j) (q j) := by
  apply (weighted_sq_le ha).trans
  apply sum_le_sum
  intro j _
  rcases (ha.1 j).eq_or_lt with hj | hj
  · simp [← hj]
  apply mul_le_mul_of_nonneg_left _ hj.le
  exact (tv_sq_le_hellinger (hp j) (hq j)).trans
    (hellinger_le_divergence (hp j) (hq j) (hs j hj))

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.FiniteKernel ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteKernel

open FiniteEntropy
variable {I : Type u} [Fintype I]

attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI
lemma stochastic_one : Stochastic (1 : Kernel I) := by
  classical
  intro i
  constructor
  · intro j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma stochastic_mul {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q) :
    Stochastic (P * Q) := by
  intro i
  exact mix_isProb (hP i) hQ

lemma stochastic_pow {P : Kernel I} (hP : Stochastic P) (n : ℕ) : Stochastic (P ^ n) := by
  classical
  induction n with
  | zero => simpa using (stochastic_one (I := I))
  | succ n ih => simpa only [pow_succ] using stochastic_mul ih hP

lemma stochastic_lazy {P : Kernel I} (hP : Stochastic P) : Stochastic (lazy P) := by
  classical
  intro i
  constructor
  · intro j
    dsimp [lazy]
    have := (hP i).1 j
    split_ifs <;> positivity
  · change (∑ j, ((if i = j then (1 : ℝ) else 0) + P i j) / 2) = 1
    rw [← sum_div, sum_add_distrib]
    simp [(hP i).2]

lemma stochastic_smoothed {P : Kernel I} (hP : Stochastic P) (j : ℕ) :
    Stochastic (smoothed P j) := stochastic_mul hP (stochastic_pow (stochastic_lazy hP) j)

lemma stationary_lazy {π : I → ℝ} {P : Kernel I} (hP : Stationary π P) :
    Stationary π (lazy P) := by
  classical
  intro j
  change (∑ i, π i * (((if i = j then 1 else 0) + P i j) / 2)) = π j
  simp only [← mul_div_assoc, mul_add, ← sum_div, sum_add_distrib,
    mul_ite, mul_one, mul_zero]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rw [hP j]
  ring

omit [Fintype I] in
lemma lazy_eq (P : Kernel I) : lazy P = (1 / 2 : ℝ) • (1 + P) := by
  classical
  ext i j
  simp [lazy, Matrix.one_apply, div_eq_mul_inv, mul_comm]

lemma commute_lazy (P : Kernel I) : Commute P (lazy P) := by
  classical
  rw [lazy_eq]
  show P * ((1 / 2 : ℝ) • (1 + P)) = ((1 / 2 : ℝ) • (1 + P)) * P
  simp [mul_add, add_mul]

lemma smoothed_succ (P : Kernel I) (j : ℕ) :
    smoothed P (j + 1) = lazy P * smoothed P j := by
  classical
  unfold smoothed
  rw [pow_succ', ← mul_assoc, (commute_lazy P).eq, mul_assoc]

lemma pair_isProb {π : I → ℝ} (hπ : IsProb π) {Q : Kernel I} (hQ : Stochastic Q) :
    IsProb (fun a : I × I ↦ π a.1 * Q a.1 a.2) := by
  constructor
  · intro a
    exact mul_nonneg (hπ.1 a.1) ((hQ a.1).1 a.2)
  · rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, fun i ↦ (hQ i).2, mul_one]
    exact hπ.2

lemma stationary_average {π : I → ℝ} {Q : Kernel I} (hQ : Stationary π Q) (f : I → ℝ) :
    (∑ i, π i * ∑ j, Q i j * f j) = ∑ j, π j * f j := by
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp_rw [← sum_mul]
  exact sum_congr rfl fun j _ ↦ by rw [hQ j]

lemma entropy_increment {π w : I → ℝ} (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    avgEntropy π w (Q * K) - avgEntropy π w K =
      ∑ i, π i * ∑ j, Q i j * divergence (K j) ((Q * K) i) := by
  have he (i : I) := entropy_mix_gap hw (hQ i) hK
  have he' : ∀ i, entropy w ((Q * K) i) - ∑ j, Q i j * entropy w (K j) =
      ∑ j, Q i j * divergence (K j) ((Q * K) i) := he
  simp_rw [← he', mul_sub, sum_sub_distrib]
  rw [stationary_average hs]
  rfl

lemma entropy_increment_tv {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    (∑ i, π i * ∑ j, Q i j * tv (K j) ((Q * K) i)) ^ 2 ≤
      avgEntropy π w (Q * K) - avgEntropy π w K := by
  rw [entropy_increment hw hQ hK hs]
  have h := average_tv_sq_le_average_divergence (pair_isProb hπ hQ)
    (fun a : I × I ↦ hK a.2) (fun a : I × I ↦ stochastic_mul hQ hK a.1)
    (fun a ha i hi ↦ mix_support (hQ a.1).1 (fun j ↦ (hK j).1)
      (pos_of_mul_pos_right ha (hπ.1 a.1)) hi)
  simpa only [Fintype.sum_prod_type, mul_assoc, ← mul_sum] using h

lemma lazy_triangle_tv {π : I → ℝ} (hπ : IsProb π) {P K : Kernel I}
    (hP : Stochastic P) :
    (∑ i, π i * ∑ j, P i j * tv (K i) (K j)) ≤
      2 * (∑ i, π i * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i)) := by
  classical
  have hi (i : I) : (∑ j, P i j * tv (K i) (K j)) ≤
      2 * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i) := by
    calc
      _ ≤ ∑ j, P i j * (tv (K i) ((lazy P * K) i) + tv (K j) ((lazy P * K) i)) := by
        apply sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ ((hP i).1 j)
        have := tv_triangle (K i) ((lazy P * K) i) (K j)
        simpa only [tv_comm ((lazy P * K) i)] using this
      _ = _ := by
        have he (f : I → ℝ) : (∑ j, lazy P i j * f j) =
            (f i + ∑ j, P i j * f j) / 2 := by
          simp only [lazy, div_mul_eq_mul_div, add_mul, ← sum_div, sum_add_distrib,
            ite_mul, one_mul, zero_mul]
          simp
        rw [he]
        simp only [mul_add, sum_add_distrib, ← sum_mul, (hP i).2, one_mul]
        ring
  calc
    _ ≤ ∑ i, π i * (2 * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i)) :=
      sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hi i) (hπ.1 i)
    _ = _ := by simp_rw [← mul_assoc, mul_comm (π _ ) 2, mul_assoc, ← mul_sum]

lemma smoothed_row_distance_sq {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P) (j : ℕ) :
    (∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z)) ^ 2 ≤
      4 * (avgEntropy π w (smoothed P (j + 1)) - avgEntropy π w (smoothed P j)) := by
  have h := entropy_increment_tv hπ hw (stochastic_lazy hP)
    (stochastic_smoothed hP j) (stationary_lazy hs)
  have hc := lazy_triangle_tv (K := smoothed P j) hπ hP
  have ha : 0 ≤ ∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z) :=
    sum_nonneg fun i _ ↦ mul_nonneg (hπ.1 i)
      (sum_nonneg fun z _ ↦ mul_nonneg ((hP i).1 z) (tv_nonneg _ _))
  have hb : 0 ≤ ∑ i, π i * ∑ z, lazy P i z * tv (smoothed P j z)
      ((lazy P * smoothed P j) i) :=
    sum_nonneg fun i _ ↦ mul_nonneg (hπ.1 i)
      (sum_nonneg fun z _ ↦ mul_nonneg ((stochastic_lazy hP i).1 z) (tv_nonneg _ _))
  rw [smoothed_succ]
  have hp := mul_nonneg (sub_nonneg.2 hc) (add_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hb) ha)
  nlinarith

/-- Entropy telescoping gives the averaged triangle-row estimate. -/
lemma exists_smoothed_row_distance {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P)
    {R : ℕ} (hR : 0 < R) {D : ℝ}
    (hD : avgEntropy π w (smoothed P R) - avgEntropy π w (smoothed P 0) ≤ D) :
    ∃ j < R, (∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z)) ^ 2 ≤
      4 * D / R := by
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hR
  have hsum : (∑ j ∈ range R, (avgEntropy π w (smoothed P (j + 1)) -
      avgEntropy π w (smoothed P j))) ≤ ∑ _j ∈ range R, D / (R : ℝ) := by
    rw [sum_range_sub (fun j ↦ avgEntropy π w (smoothed P j)) R]
    have he : (∑ _j ∈ range R, D / (R : ℝ)) = D := by
      rw [sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [he]
    exact hD
  obtain ⟨j, hj, hle⟩ := exists_le_of_sum_le (nonempty_range_iff.2 (Nat.ne_of_gt hR)) hsum
  refine ⟨j, mem_range.1 hj, ?_⟩
  calc
    _ ≤ 4 * (avgEntropy π w (smoothed P (j + 1)) - avgEntropy π w (smoothed P j)) :=
      smoothed_row_distance_sq hπ hw hP hs j
    _ ≤ 4 * (D / (R : ℝ)) := mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = _ := by ring

variable {J : Type v}

end FiniteKernel

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteKernel
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open FiniteEntropy
attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteKernel.exists_smoothed_row_distance.{u} := @_root_.OAI.CliqueFreeIndependence.FiniteKernel.exists_smoothed_row_distance.{u}

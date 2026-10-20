-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteActivity.characterSparse_detection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:41:22.325452+00:00
-- url     : https://prove2.me/submissions/a000d7d4-ef1e-4605-b318-c3d40af5afb6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteVectorDetection.lean:L60-L90
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteActivity.characterSparse_detection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FinitePeriod_periodic_sum_lower
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FinitePeriod_root_cycle_sum

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteNumeric ----
namespace OAI

/-!
# Arithmetic for the finite-tree obstruction

The parameter estimate and final rearrangement in `prop:finite-lower` hold
with the explicit absolute constant 34.
-/

namespace TreeEdit.BinaryLower.FiniteNumeric

/-- The bound on a sparse character period at any internal depth implies the
half-averaging-interval bound required by short-period detection. -/
theorem sparse_period_twice_le {k j r q : ℕ} (hk : 1 ≤ k)
    (hj : j < k) (hr : r < k)
    (hq : q ≤ 2 * k ^ (5 * j + 5 * r)) :
    2 * q ≤ 4 * k ^ (10 * k) := by
  have hp : k ^ (5 * j + 5 * r) ≤ k ^ (10 * k) :=
    Nat.pow_le_pow_right hk (by omega)
  nlinarith

end TreeEdit.BinaryLower.FiniteNumeric

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FinitePeriod ----
namespace OAI

/-!
# Short-period detection for the finite-tree obstruction

Complete-period averaging gives the short-period detection estimate in
`prop:finite-lower`.
-/

open scoped BigOperators

namespace TreeEdit.BinaryLower.FinitePeriod

/-- Short-period detection used at every sparse active internal node. -/
theorem root_short_average {z : ℂ} {q J : ℕ}
    (hq : 0 < q) (hJ : 2 * q ≤ J) (hz : ‖z‖ = 1)
    (hne : z ≠ 1) (hroot : z ^ q = 1) :
    1 ≤ (∑ s ∈ Finset.range J, ‖1 - z ^ (s + 1)‖ ^ 2) / (J : ℝ) := by
  have hperiod : Function.Periodic (fun s : ℕ => ‖1 - z ^ (s + 1)‖ ^ 2) q := by
    intro s
    have he : s + q + 1 = (s + 1) + q := by omega
    dsimp
    rw [he, pow_add, hroot, mul_one]
  have hsum := periodic_sum_lower hq hJ hperiod
    (fun s => sq_nonneg _) (root_cycle_sum hz hne hroot)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  exact (le_div_iff₀ hJpos).2 (by simpa using hsum)

/-- A character specialization in exactly the source's cheap-shift notation.
Only a period of the character value is required; it need not be a period of
`u` itself. Activity after multiplying by `R` guarantees nontriviality. -/
theorem character_short_average {A : Type*} [AddCommGroup A] [Finite A]
    (χ : AddChar A ℂ) (u : A) {q J R : ℕ}
    (hq : 0 < q) (hJ : 2 * q ≤ J)
    (hactive : χ (R • u) ≠ 1) (hperiod : χ (q • u) = 1) :
    1 ≤ (∑ s ∈ Finset.range J, ‖1 - χ ((s + 1) • u)‖ ^ 2) / (J : ℝ) := by
  have hne : χ u ≠ 1 := by
    intro h
    apply hactive
    simp [χ.map_nsmul_eq_pow, h]
  have hroot : χ u ^ q = 1 := by
    simpa only [χ.map_nsmul_eq_pow] using hperiod
  simpa only [χ.map_nsmul_eq_pow] using
    root_short_average hq hJ (χ.norm_apply u) hne hroot

end TreeEdit.BinaryLower.FinitePeriod

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.SparseCharacterPeriod ----
namespace OAI

/-!
# Periods of products supported on few children

This is the period estimate used for sparse active frequencies in
`prop:finite-lower`. An annihilating period suffices; no exact order or lcm
calculation is needed for this step.
-/

open scoped BigOperators

namespace TreeEdit.BinaryLower.FinitePeriod

lemma product_period {ι : Type*} (s : Finset ι) (Q : ℕ)
    (p : ι → ℕ) (z : ι → ℂ)
    (hz : ∀ i ∈ s, z i ^ (Q * p i) = 1) :
    (∏ i ∈ s, z i) ^ (Q * ∏ i ∈ s, p i) = 1 := by
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  obtain ⟨t, ht⟩ := Nat.mul_dvd_mul_left Q (Finset.dvd_prod_of_mem p hi)
  rw [ht, pow_mul, hz i hi, one_pow]

lemma product_period_pos {ι : Type*} (s : Finset ι) {Q : ℕ}
    (p : ι → ℕ) (hQ : 0 < Q) (hp : ∀ i ∈ s, 0 < p i) :
    0 < Q * ∏ i ∈ s, p i :=
  Nat.mul_pos hQ (Finset.prod_pos hp)

lemma product_period_upper {ι : Type*} (s : Finset ι) {Q k j : ℕ}
    (p : ι → ℕ) (hQ : Q ≤ 2 * k ^ (5 * j))
    (hp : ∀ i ∈ s, p i ≤ k ^ 5) :
    Q * ∏ i ∈ s, p i ≤ 2 * k ^ (5 * j + 5 * s.card) := by
  have hprod : (∏ i ∈ s, p i) ≤ (k ^ 5) ^ s.card := by
    calc
      (∏ i ∈ s, p i) ≤ ∏ _i ∈ s, k ^ 5 :=
        Finset.prod_le_prod' hp
      _ = (k ^ 5) ^ s.card := Finset.prod_const _
  calc
    Q * ∏ i ∈ s, p i ≤ (2 * k ^ (5 * j)) * ((k ^ 5) ^ s.card) :=
      Nat.mul_le_mul hQ hprod
    _ = 2 * k ^ (5 * j + 5 * s.card) := by
      rw [← pow_mul, pow_add]
      ring

lemma character_finset_sum {ι A : Type*} [AddCommMonoid A]
    (χ : AddChar A ℂ) (s : Finset ι) (w : ι → A) :
    χ (∑ i ∈ s, w i) = ∏ i ∈ s, χ (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [χ.map_zero_eq_one]
  | @insert a s ha ih =>
      simp [ha, χ.map_add_eq_mul, ih]

/-- The product period annihilates the character of the sum, even when the
underlying vectors outside the active set are nonzero. -/
lemma character_supported_period {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (χ : AddChar A ℂ) (s : Finset ι) (w : ι → A) (Q : ℕ) (p : ι → ℕ)
    (houtside : ∀ i, i ∉ s → χ (w i) = 1)
    (hchild : ∀ i ∈ s, (Q * p i) • w i = 0) :
    χ ((Q * ∏ i ∈ s, p i) • ∑ i, w i) = 1 := by
  have hsum : χ (∑ i, w i) = ∏ i ∈ s, χ (w i) := by
    rw [character_finset_sum]
    exact (Finset.prod_subset (Finset.subset_univ s)
      (fun i _ hi => houtside i hi)).symm
  rw [χ.map_nsmul_eq_pow, hsum]
  apply product_period
  intro i hi
  rw [← χ.map_nsmul_eq_pow, hchild i hi, χ.map_zero_eq_one]

/-- Sparse active children are detected by the source's fixed short averaging
interval. All stated inputs are local period and support facts; no Fourier
identity or edit-distance conclusion is assumed here. -/
theorem sparse_character_detection {ι A : Type*} [Fintype ι]
    [AddCommGroup A] [Finite A]
    (χ : AddChar A ℂ) (s : Finset ι) (w : ι → A)
    {k j Q R : ℕ} (p : ι → ℕ)
    (hk : 1 ≤ k) (hj : j < k) (hs : s.card < k)
    (hQpos : 0 < Q) (hQ : Q ≤ 2 * k ^ (5 * j))
    (hppos : ∀ i ∈ s, 0 < p i) (hp : ∀ i ∈ s, p i ≤ k ^ 5)
    (houtside : ∀ i, i ∉ s → χ (w i) = 1)
    (hchild : ∀ i ∈ s, (Q * p i) • w i = 0)
    (hactive : χ (R • ∑ i, w i) ≠ 1) :
    1 ≤ (∑ a ∈ Finset.range (4 * k ^ (10 * k)),
      ‖1 - χ ((a + 1) • ∑ i, w i)‖ ^ 2) / (4 * k ^ (10 * k) : ℕ) := by
  apply character_short_average χ (∑ i, w i)
    (product_period_pos s p hQpos hppos)
    (TreeEdit.BinaryLower.FiniteNumeric.sparse_period_twice_le hk hj hs
      (product_period_upper s p hQ hp)) hactive
  exact character_supported_period χ s w Q p houtside hchild

end TreeEdit.BinaryLower.FinitePeriod

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteVectorDetection ----
namespace OAI

/-!
# Actual sparse-node character tests

Short-period detection holds for the finite-tree vectors in both the
function-indexed and list-indexed presentations.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace TreeEdit.BinaryLower.FiniteVectors

end TreeEdit.BinaryLower.FiniteVectors

namespace TreeEdit.BinaryLower.FiniteActivity

/-- The exact unnormalized finite-sample detector required by
`finite_tree_spectral_bound`, with the sparse predicate and child list
indices unchanged. All hypotheses are local vector/period identities. -/
theorem characterSparse_detection {α A : Type*}
    [Fintype α] [AddCommGroup A] [Finite A] {k : ℕ}
    (w : List α → A) (v : InternalNode α k) (u : A)
    (Q R : ℕ) (p : α → ℕ) (hk : 1 ≤ k)
    (hQpos : 0 < Q) (hQ : Q ≤ 2 * k ^ (5 * v.1.val))
    (hppos : ∀ i, 0 < p i) (hp : ∀ i, p i ≤ k ^ 5)
    (hroot : w (List.ofFn v.2) = R • u)
    (hsum : u = ∑ i, w (List.ofFn v.2 ++ [i]))
    (hchild : ∀ i, (Q * p i) • w (List.ofFn v.2 ++ [i]) = 0)
    (χ : AddChar A ℂ) (hsparse : characterSparse w k v χ) :
    ((4 * k ^ (10 * k) : ℕ) : ℝ) ≤
      ∑ s : Fin (4 * k ^ (10 * k)), ‖1 - χ ((s.val + 1) • u)‖ ^ 2 := by
  let S : Finset α := Finset.univ.filter fun i => χ (w (List.ofFn v.2 ++ [i])) ≠ 1
  have hcard : S.card < k := by
    simpa only [S, Branching.activeChildCount] using hsparse.2
  have hactive : χ (R • ∑ i, w (List.ofFn v.2 ++ [i])) ≠ 1 := by
    rw [← hsum, ← hroot]
    exact hsparse.1
  have houtside : ∀ i, i ∉ S → χ (w (List.ofFn v.2 ++ [i])) = 1 := by
    intro i hi
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  have havg := FinitePeriod.sparse_character_detection χ S
    (fun i => w (List.ofFn v.2 ++ [i])) p hk v.1.isLt hcard hQpos hQ
    (fun i _ => hppos i) (fun i _ => hp i) houtside (fun i _ => hchild i) hactive
  have hJ : (0 : ℝ) < ((4 * k ^ (10 * k) : ℕ) : ℝ) := by positivity
  have hraw := (le_div_iff₀ hJ).mp havg
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => ‖1 - χ ((s + 1) • u)‖ ^ 2)]
  simpa only [one_mul, ← hsum] using hraw

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteActivity
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteActivity.characterSparse_detection := @_root_.OAI.TreeEdit.BinaryLower.FiniteActivity.characterSparse_detection

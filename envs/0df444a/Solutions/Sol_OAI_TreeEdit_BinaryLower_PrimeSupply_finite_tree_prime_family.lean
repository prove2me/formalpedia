-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.PrimeSupply.finite_tree_prime_family
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:19:11.925754+00:00
-- url     : https://prove2.me/submissions/5e9b8c07-4dd5-43fd-90d4-ab43a068744d

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open Filter Finset
open scoped Topology
theorem h49_pi_pow_lower (e C : ℕ) : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → C * k ^ e ≤ Nat.primeCounting (k ^ (e + 1)) := by
  let A : ℕ := (e+1)*(C+2)
  refine ⟨16*A^2 + 2, fun k hk => ?_⟩
  have hk2 : 2 ≤ k := by omega
  set x : ℝ := (k:ℝ) with hx
  have hx2 : (2:ℝ) ≤ x := by rw [hx]; exact_mod_cast hk2
  have hxA : (16:ℝ)*(A:ℝ)^2 ≤ x := by rw [hx]; exact_mod_cast (show 16*A^2 ≤ k by omega)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : 4*(A:ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) (by linarith)]; nlinarith
  have hlogsq : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hl2 : (1:ℝ)/2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hkey : (A:ℝ) * Real.log x ≤ x * Real.log 2 := by
    have hA0 : (0:ℝ) ≤ A := by positivity
    have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    have : (A:ℝ) * Real.log x ≤ (A:ℝ) * (2 * Real.sqrt x) := mul_le_mul_of_nonneg_left hlogsq hA0
    nlinarith
  set n : ℕ := k ^ (e+1) with hn
  have hn2 : 2 ≤ n := by
    rw [hn]; calc 2 ≤ k := hk2
      _ = k^1 := (pow_one k).symm
      _ ≤ k^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hnx : (n:ℝ) = x^(e+1) := by rw [hn, hx]; push_cast; ring
  have hlogn : Real.log n = (e+1) * Real.log x := by rw [hnx, Real.log_pow]; push_cast; ring
  have hlogn0 : 0 < Real.log n := by rw [hlogn]; positivity
  have hpi := Chebyshev.pi_ge n
  have hlog1 : Real.log ((n:ℝ)+1) ≤ 2 * Real.log n := by
    have hn2' : (2:ℝ) ≤ n := by exact_mod_cast hn2
    rw [show (2:ℝ) * Real.log n = Real.log ((n:ℝ)^2) by rw [Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hxe : (1:ℝ) ≤ x^e := one_le_pow₀ (by linarith)
  have hgoal : (C:ℝ) * x^e ≤ ((n:ℝ) * Real.log 2 - Real.log ((n:ℝ)+1)) / Real.log n := by
    rw [le_div_iff₀ hlogn0]
    have h1 : ((C:ℝ) * x^e + 2) * Real.log n ≤ (n:ℝ) * Real.log 2 := by
      have h2 : (C:ℝ) * x^e + 2 ≤ ((C:ℝ)+2) * x^e := by nlinarith
      have hAc : (A:ℝ) = ((e:ℝ)+1)*((C:ℝ)+2) := by simp [A]
      calc ((C:ℝ) * x^e + 2) * Real.log n ≤ ((C:ℝ)+2) * x^e * Real.log n :=
            mul_le_mul_of_nonneg_right h2 hlogn0.le
        _ = x^e * ((A:ℝ) * Real.log x) := by rw [hlogn, hAc]; ring
        _ ≤ x^e * (x * Real.log 2) := mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (n:ℝ) * Real.log 2 := by rw [hnx]; ring
    nlinarith
  have := hgoal.trans hpi
  have hcast : ((C * k^e : ℕ) : ℝ) = (C:ℝ) * x^e := by rw [hx]; push_cast; ring
  exact_mod_cast (hcast ▸ this)
theorem h49_pi_le_interval (a b : ℕ) :
    Nat.primeCounting b ≤ ((Finset.Icc a b).filter Nat.Prime).card + a := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  calc ((Finset.range (b+1)).filter Nat.Prime).card
      ≤ (Finset.range a ∪ (Finset.Icc a b).filter Nat.Prime).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc]
        by_cases h : x < a
        · exact Or.inl h
        · exact Or.inr ⟨⟨by omega, by omega⟩, hx.2⟩
    _ ≤ (Finset.range a).card + ((Finset.Icc a b).filter Nat.Prime).card := Finset.card_union_le _ _
    _ = _ := by rw [Finset.card_range, add_comm]

theorem h49_prime_supply : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      20 * k ^ 2 ≤ ((Finset.Icc (k ^ 4) (k ^ 5)).filter Nat.Prime).card ∧
      1600 * k < ((Finset.Icc (k ^ 2) (k ^ 3)).filter Nat.Prime).card := by
  obtain ⟨a, ha⟩ := h49_pi_pow_lower 4 2
  obtain ⟨b, hb⟩ := h49_pi_pow_lower 2 2
  refine ⟨a + b + 1601, fun k hk => ⟨?_, ?_⟩⟩
  · have h1 := ha k (by omega)
    norm_num at h1
    have h2 := h49_pi_le_interval (k^4) (k^5)
    have h3 : 20 * k^2 ≤ k^4 := by
      have : 20 ≤ k^2 := by nlinarith
      calc 20 * k^2 ≤ k^2 * k^2 := Nat.mul_le_mul_right _ this
        _ = k^4 := by ring
    omega
  · have h1 := hb k (by omega)
    norm_num at h1
    have h2 := h49_pi_le_interval (k^2) (k^3)
    have h3 : 1600 * k < k^2 := by nlinarith
    omega

theorem solution :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ p : (Fin k × Fin (20 * k)) ↪ ℕ,
        ∀ ji, Nat.Prime (p ji) ∧ k ^ 4 ≤ p ji ∧ p ji ≤ k ^ 5 := by
  obtain ⟨k₀, hk₀⟩ := h49_prime_supply
  refine ⟨k₀, fun k hk => ?_⟩
  have hc := (hk₀ k hk).1
  set S := (Finset.Icc (k ^ 4) (k ^ 5)).filter Nat.Prime with hS
  have hle : k * (20 * k) ≤ S.card := by
    calc k * (20 * k) = 20 * k^2 := by ring
      _ ≤ _ := hc
  let emb : (Fin k × Fin (20 * k)) ↪ ℕ :=
    (finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hle)).trans
      (S.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _))
  refine ⟨emb, fun ji => ?_⟩
  have hmem : emb ji ∈ S := (S.equivFin.symm _).2
  rw [hS, Finset.mem_filter, Finset.mem_Icc] at hmem
  exact ⟨hmem.2, hmem.1.1, hmem.1.2⟩


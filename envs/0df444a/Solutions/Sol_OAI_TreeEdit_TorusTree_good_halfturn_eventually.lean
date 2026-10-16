-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.good_halfturn_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:15:51.49919+00:00
-- url     : https://prove2.me/submissions/dae8a8e8-f50d-4d10-a303-c1d8b55128e3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleObstruction.lean:L106-L127
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.good_halfturn_eventually. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Theorems.Thm_OAI_TreeEdit_PrimeSupply_eventually_pi_power
import Theorems.Thm_OAI_TreeEdit_TorusTree_good_probability

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma probability_exists {A : Type*} [Fintype A] {E : A → Prop} (h : 0 < probability E) : ∃ a, E a := by
  classical
  by_contra hn
  have hz : probability E = 0 := by simp [probability, mean, not_exists.mp hn]
  linarith

end TreeEdit.FiniteProbability

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.PrimeSupply ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace PrimeSupply
open Filter

lemma primeCounting_le (n : ℕ) : n.primeCounting ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hh : n.primesLE ⊆ Finset.Icc 1 n := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.one_lt.le, (Nat.mem_primesLE.mp hp).1⟩
  simpa using Finset.card_le_card hh

lemma eventually_band_card (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ k : ℕ in atTop, k ^ a ≤ (band k a).card := by
  filter_upwards [eventually_pi_power a ha, eventually_ge_atTop 1] with k hk hk1
  have hsub : (k ^ a).primesLE ⊆ (k ^ (a + 1)).primesLE := by
    intro p hp
    obtain ⟨hpk, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpk.trans (pow_le_pow_right₀ hk1 (by omega)), hpp⟩
  rw [band, Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]
  have hh := primeCounting_le (k ^ a)
  omega

end PrimeSupply

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleObstruction ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter FiniteProbability

lemma parameter_spacing {k : ℕ} (hk : 2 ≤ k) :
    2 * ((k ^ 3) ^ k) ^ 2 < resolution k := by
  have hp : 2 < k ^ (2 * k) := by
    calc
      2 < (2 : ℕ) ^ 4 := by norm_num
      _ ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
      _ ≤ k ^ (2 * k) := pow_le_pow_right₀ (by omega) (by omega)
  have hkpos : 0 < k ^ (6 * k) := pow_pos (by omega) _
  calc
    2 * ((k ^ 3) ^ k) ^ 2 = 2 * k ^ (6 * k) := by
      rw [← pow_mul, ← pow_mul]
      congr 2
      omega
    _ < k ^ (2 * k) * k ^ (6 * k) := Nat.mul_lt_mul_of_pos_right hp hkpos
    _ = resolution k := by rw [← pow_add]; congr 1; omega

lemma probability_error_eventually : ∀ᶠ k : ℕ in atTop,
    (16 * k : ℝ) / (k ^ 2 : ℕ) + ((k ^ 3 : ℕ) : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * k ^ 2) ≤ 1 / 10 := by
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 48 (by norm_num : (0 : ℝ) ≤ 4 / 5) (by norm_num : (4 / 5 : ℝ) < 1)).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 20)
  filter_upwards [ht, eventually_ge_atTop 320] with k ht hk
  have hkreal : (320 : ℝ) ≤ k := by exact_mod_cast hk
  have hka : 1 ≤ k := by omega
  have hksq : k ≤ k ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hka (show 1 ≤ 2 by omega)
  have hb : (k : ℝ) ^ 48 * (4 / 5 : ℝ) ^ (k ^ 2) ≤ 1 / 20 := by
    calc
      _ ≤ (k : ℝ) ^ 48 * (4 / 5 : ℝ) ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hksq) (by positivity)
      _ ≤ _ := ht.le
  have hpow : ((k ^ 3 : ℕ) : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * k ^ 2) ≤ 1 / 20 := by
    calc
      _ = ((k : ℝ) ^ 48 * (4 / 5 : ℝ) ^ (k ^ 2)) ^ k := by
        push_cast
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> ring
      _ ≤ (1 / 20 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hb _
      _ ≤ (1 / 20 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hka
      _ = _ := pow_one _
  have hfrac : (16 * k : ℝ) / (k ^ 2 : ℕ) ≤ 1 / 20 := by
    push_cast
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)).mpr
    nlinarith
  linarith

lemma torus_parameters_eventually : ∀ᶠ k : ℕ in atTop,
    2 ≤ k ∧ ∃ _ : Fin (16 * k) ↪ Pool k,
      (∀ p : Pool k, 10 ≤ poolPrime p) ∧
      (∀ p : Pool k, 2 * (resolution k : ℝ)⁻¹ * poolPrime p < 1) ∧
      2 * (resolution k : ℝ)⁻¹ * (((k ^ 3) ^ k : ℕ) : ℝ) ^ 2 < 1 ∧
      (16 * k : ℝ) / Fintype.card (Pool k) + ((k ^ 3 : ℕ) : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * k ^ 2) ≤ 1 / 10 := by
  filter_upwards [PrimeSupply.eventually_band_card 2 (by omega), probability_error_eventually,
    eventually_ge_atTop 320] with k hcard herr hk
  have hk2 : 2 ≤ k := by omega
  have hcard' : k ^ 2 ≤ Fintype.card (Pool k) := by
    rw [show Fintype.card (Pool k) = (PrimeSupply.band k 2).card from Fintype.card_coe (PrimeSupply.band k 2)]
    exact hcard
  have h16 : 16 * k ≤ Fintype.card (Pool k) := by nlinarith
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin (16 * k)) ≤ Fintype.card (Pool k) by simpa using h16)
  have hR : 0 < resolution k := pow_pos (by omega) _
  have hRr : (0 : ℝ) < resolution k := by exact_mod_cast hR
  have hε : 2 * (resolution k : ℝ)⁻¹ * (((k ^ 3) ^ k : ℕ) : ℝ) ^ 2 < 1 := by
    have hh : (2 : ℝ) * ((((k ^ 3) ^ k) ^ 2 : ℕ) : ℝ) < resolution k := by exact_mod_cast parameter_spacing hk2
    push_cast at hh ⊢
    field_simp
    nlinarith
  refine ⟨hk2, j, ?_, ?_, hε, ?_⟩
  · intro p
    have hp := (pool_properties p).2.1
    nlinarith
  · intro p
    have hp := (pool_properties p).2.2
    have hu : k ^ 3 ≤ ((k ^ 3) ^ k) ^ 2 := by
      calc
        _ = (k ^ 3) ^ 1 := by simp
        _ ≤ (k ^ 3) ^ (k * 2) := pow_le_pow_right₀ (one_le_pow₀ (by omega)) (by omega)
        _ = _ := pow_mul ..
    have hh : (poolPrime p : ℝ) ≤ (((k ^ 3) ^ k : ℕ) : ℝ) ^ 2 := by exact_mod_cast hp.trans hu
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_lt hε
  · apply le_trans _ herr
    gcongr

lemma good_halfturn_eventually : ∀ᶠ k : ℕ in atTop, 2 ≤ k ∧
    ∃ (j : Fin (16 * k) ↪ Pool k) (C : Config (Pool k) (residueModulus k) (branching k) k),
      Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2) := by
  filter_upwards [torus_parameters_eventually] with k hk
  obtain ⟨hk2, j, hr10, hgrid, hε, herr⟩ := hk
  refine ⟨hk2, j, ?_⟩
  have hhalf : (resolution k : ℝ)⁻¹ ≤ ‖point 2‖ := by
    have hR : 2 ≤ resolution k := by
      calc
        2 ≤ k := hk2
        _ = k ^ 1 := by simp
        _ ≤ resolution k := pow_le_pow_right₀ (by omega) (by omega)
    have hn : ‖point 2‖ = (1 / 2 : ℝ) := by
      dsimp [point]
      simpa using AddCircle.norm_half_period_eq (1 : ℝ)
    rw [hn]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hR : (2 : ℝ) ≤ resolution k)
  have hh := good_probability (L := residueModulus k) poolPrime (fun p => (pool_properties p).1) Subtype.val_injective
    hr10 (show 1 ≤ k ^ 3 from one_le_pow₀ (by omega)) (fun p => (pool_properties p).2.2)
    (fun p => Finset.dvd_prod_of_mem _ (Finset.mem_univ p)) j hgrid hε herr k (point 2) hhalf
  have hex := probability_exists (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9 / 10) hh)
  exact hex

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter FiniteProbability


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.good_halfturn_eventually := @_root_.OAI.TreeEdit.TorusTree.good_halfturn_eventually

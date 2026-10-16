-- Prove2me | solution 1 for OAI.TreeEdit.binary_torus
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:33:26.657092+00:00
-- url     : https://prove2.me/submissions/2b98ca80-f33e-41f5-917c-f3f6a7c6a932

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/TorusLowerBound.lean:L106-L113
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TreeEdit.binary_torus.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_TreeEdit_binary_torus) verbatim and is proved by it.
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
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
import Definitions.Def_OAI_Combinatorics_TreeEdit_DistortionTransfer
import Definitions.Def_OAI_Combinatorics_TreeEdit_TorusLowerBound
import Theorems.Thm_OAI_TreeEdit_TorusTree_binaryWidth_le
import Theorems.Thm_OAI_TreeEdit_TorusTree_binary_witness
import Theorems.Thm_OAI_TreeEdit_TorusTree_good_halfturn_eventually
import Theorems.Thm_OAI_TreeEdit_sqrt_log_cap

-- ---- from OAI.Combinatorics.TreeEdit.CircleParameters ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

lemma wordLength_ge {k : ℕ} (hk : 2 ≤ k) : k ≤ wordLength k := by
  have hT : 1 ≤ repetitions k := one_le_pow₀ (by omega)
  have hm : k ≤ branching k := by
    dsimp [branching]
    have hk2 : 1 ≤ k^2 := one_le_pow₀ (by omega)
    nlinarith
  have hbase : 1 ≤ branching k * repetitions k := (show 1 ≤ branching k by omega).trans (Nat.le_mul_of_pos_right _ hT)
  exact (hm.trans (Nat.le_mul_of_pos_right _ hT)).trans (le_self_pow₀ hbase (by omega))

lemma binaryLength_ge {k : ℕ} (hk : 2 ≤ k) : k ≤ binaryLength k :=
  (wordLength_ge hk).trans (Nat.le_mul_of_pos_right _ (by dsimp [binaryWidth]; omega))

lemma branching_le_power {k : ℕ} (hk : 2 ≤ k) : branching k ≤ k^7 := by
  have h16 : 16 ≤ k^4 := by simpa using Nat.pow_le_pow_left hk 4
  calc
    _ = 16*k^3 := by dsimp [branching]; ring
    _ ≤ k^4*k^3 := Nat.mul_le_mul_right _ h16
    _ = _ := by rw [← pow_add]

lemma binaryLength_le_power {k : ℕ} (hk : 2 ≤ k) : binaryLength k ≤ k^(60*k^2) := by
  have hm := branching_le_power hk
  have hW : binaryWidth k ≤ k^8 := by
    have h40 : 40 ≤ k^6 := by have hh := Nat.pow_le_pow_left hk 6; norm_num at hh; omega
    exact (binaryWidth_le hk).trans ((Nat.mul_le_mul_right (k^2) h40).trans_eq (by rw [← pow_add]))
  have hN : wordLength k ≤ k^((7+52*k)*k) := by
    calc
      _ ≤ (k^7 * k^(52*k))^k := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hm) k
      _ = _ := by rw [← pow_add, ← pow_mul]
  calc
    _ ≤ k^((7+52*k)*k)*k^8 := Nat.mul_le_mul hN hW
    _ = k^((7+52*k)*k+8) := by rw [← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

lemma length_log_bound {k : ℕ} (hk : 2 ≤ k) :
    Real.log (binaryLength k : ℝ) ≤ 60*(k : ℝ)^2*Real.log k := by
  have hN : 0 < binaryLength k := lt_of_lt_of_le (by omega : 0 < k) (binaryLength_ge hk)
  calc
    _ ≤ Real.log ((k^(60*k^2) : ℕ) : ℝ) := Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast binaryLength_le_power hk)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CapInversion ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma near_cap {N : ℕ → ℕ} {k₀ d : ℕ} (hN : ∀ k, k₀ ≤ k → k ≤ N k)
    (hd : N k₀ ≤ d) : ∃ k, k₀ ≤ k ∧ N k ≤ d ∧ d < N (k + 1) := by
  classical
  have hex : ∃ t : ℕ, d < N (k₀ + t) := by
    refine ⟨d + 1, ?_⟩
    exact (by omega : d < k₀ + (d + 1)).trans_le (hN _ (by omega))
  let t := Nat.find hex
  have ht : d < N (k₀ + t) := Nat.find_spec hex
  have ht0 : 0 < t := by
    by_contra hn
    have he : t = 0 := by omega
    simp only [he, add_zero] at ht
    omega
  refine ⟨k₀ + (t - 1), by omega, ?_, ?_⟩
  · have hh := Nat.find_min hex (show t - 1 < Nat.find hex by dsimp [t] at ht0 ⊢; omega)
    exact Nat.le_of_not_gt hh
  · convert ht using 1
    congr 1
    omega

theorem all_caps_of_witnesses {N : ℕ → ℕ} {A : ℝ} (hA : 1 ≤ A)
    (h : ∀ᶠ k : ℕ in Filter.atTop,
      k ≤ N k ∧ Real.log (N k : ℝ) ≤ A * (k : ℝ) ^ 2 * Real.log k ∧
      ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ w ∈ W, w.length = N k) ∧
        Real.exp ((k : ℝ) * Real.log k / 2) ≤ c1 W) : BinaryLowerBound := by
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp h
  let K := max k₀ ⌈8 * A⌉₊ + 2
  have hK0 : k₀ ≤ K := by dsimp [K]; omega
  have hK2 : 2 ≤ K := by dsimp [K]; omega
  have hKA : 8 * A ≤ (K : ℝ) := by
    exact (Nat.le_ceil (8 * A)).trans (by exact_mod_cast (show ⌈8 * A⌉₊ ≤ K by dsimp [K]; omega))
  refine ⟨1 / (16 * A), by positivity, N K, ?_⟩
  intro d hd
  have hdr : 1 < (d : ℝ) := by
    have hKd : K ≤ d := (hk₀ K hK0).1.trans hd
    exact_mod_cast (by omega : 1 < d)
  obtain ⟨k, hkK, hkd, hdk⟩ := near_cap (k₀ := K)
    (fun j hj => (hk₀ j (hK0.trans hj)).1) hd
  obtain ⟨hNk, hlogk, W, hW, hlen, hdist⟩ := hk₀ k (hK0.trans hkK)
  have hlog : Real.log (d : ℝ) ≤ A * ((k : ℝ) + 1) ^ 2 * Real.log ((k : ℝ) + 1) := by
    calc
      _ ≤ Real.log (N (k + 1) : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast hdk.le)
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using (hk₀ (k + 1) (by omega)).2.1
  have hb := sqrt_log_cap hA (hKA.trans (by exact_mod_cast hkK)) hdr hlog
  have hexp : Real.exp ((1 / (16 * A)) * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤
      Real.exp ((k : ℝ) * Real.log k / 2) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (1 / (16 * A)) * (8 * A * ((k : ℝ) * Real.log k)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by field_simp; ring
  exact ⟨N k, hkd, W, hW, hlen, hexp.trans hdist⟩

lemma eventually_exponential_lower {b C : ℝ} (hb : 1 ≤ b) (hC : 1 ≤ C) (r : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      Real.exp ((k : ℝ) * Real.log k / 2) ≤ ((k : ℝ) / b) ^ k / (C * (k : ℝ) ^ r) := by
  have ht : Filter.Tendsto (fun k : ℕ => Real.log (k : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (4 * (Real.log b + Real.log C)),
    Filter.eventually_ge_atTop (max 2 (4 * r))] with k hl hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkr : 4 * (r : ℝ) ≤ k := by exact_mod_cast (by omega : 4 * r ≤ k)
  have hl0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hbpos : 0 < b := by linarith
  have hCpos : 0 < C := by linarith
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  rw [← Real.exp_log (by positivity : 0 < ((k : ℝ) / b) ^ k / (C * (k : ℝ) ^ r))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hh1 := mul_le_mul_of_nonneg_left hl hkpos.le
  have hh2 := mul_le_mul_of_nonneg_right hkr hl0
  have hh3 := mul_le_mul_of_nonneg_right hk1 hlC
  nlinarith

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.TorusLowerBound ----
namespace OAI

namespace TreeEdit

namespace TorusTree
open scoped BigOperators
open Classical Filter

lemma witnesses_eventually : ∀ᶠ k : ℕ in atTop,
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ v ∈ W, v.length = binaryLength k) ∧
      ((k : ℝ)/128)^k / (1286400*(k : ℝ)^2) ≤ c1 W := by
  filter_upwards [good_halfturn_eventually] with k hk
  obtain ⟨hk2, j, C, hgood⟩ := hk
  exact binary_witness hk2 j C hgood

end TorusTree

theorem binary_torus : BinaryLowerBound := by
  apply all_caps_of_witnesses (N := TorusTree.binaryLength) (A := 60) (by norm_num)
  filter_upwards [TorusTree.witnesses_eventually,
    eventually_exponential_lower (b := 128) (C := 1286400) (by norm_num) (by norm_num) 2,
    Filter.eventually_ge_atTop 2] with k hw he hk
  obtain ⟨W, hW, hlen, hD⟩ := hw
  exact ⟨TorusTree.binaryLength_ge hk, TorusTree.length_log_bound hk,
    W, hW, hlen, he.trans hD⟩

end TreeEdit

end OAI

-- ---- mission target ----
open OAI OAI.TreeEdit
universe u

namespace OAI
namespace TreeEdit
theorem _root_.solution : BinaryLowerBound := by
  first
    | exact OAI.TreeEdit.binary_torus
    | (apply OAI.TreeEdit.binary_torus <;> assumption)
    | (intros; apply OAI.TreeEdit.binary_torus <;> assumption)
end TreeEdit
end OAI

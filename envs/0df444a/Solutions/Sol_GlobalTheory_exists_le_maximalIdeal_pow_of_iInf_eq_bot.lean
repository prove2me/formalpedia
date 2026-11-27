-- Prove2me | solution 1 for GlobalTheory.exists_le_maximalIdeal_pow_of_iInf_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:44.030975+00:00
-- url     : https://prove2.me/submissions/ae1496e8-d004-4dfc-b905-c6abf1ebdf34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_exists_sup_maximalIdeal_pow_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R]
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (maximalIdeal R) R] (J : ℕ → Ideal R) (hJ : Antitone J) (h0 : ⨅ m, J m = ⊥)
    (k : ℕ) : ∃ m, J m ≤ maximalIdeal R ^ k := by
  set 𝔪 := maximalIdeal R
  choose s hs using exists_sup_maximalIdeal_pow_stable J hJ
  let B : ℕ → Ideal R := fun k ↦ J (s k) ⊔ 𝔪 ^ k
  have hB : ∀ k m, B k ≤ J m ⊔ 𝔪 ^ k := fun k m ↦ by
    rw [show B k = _ from (hs k (max m (s k)) (le_max_right _ _)).symm]
    exact sup_le_sup_right (hJ (le_max_left _ _)) _
  have step : ∀ k, ∀ x ∈ B k, ∃ y ∈ B (k + 1), x - y ∈ 𝔪 ^ k := fun k x hx ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hB k (s (k + 1)) hx)
    exact ⟨y, Ideal.mem_sup_left hy, by simpa using hz⟩
  choose! g hg hg' using step
  refine ⟨s k, fun x hx ↦ ?_⟩
  let f : ℕ → R := fun n ↦ Nat.rec x (fun n y ↦ g (k + n) y) n
  have hf : ∀ n, f n ∈ B (k + n) := fun n ↦ by
    induction n with
    | zero => exact Ideal.mem_sup_left hx
    | succ n ih => exact hg _ _ ih
  have hf' : ∀ n d, f n - f (n + d) ∈ 𝔪 ^ (k + n) := fun n d ↦ by
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 : f (n + d) - f (n + d + 1) ∈ 𝔪 ^ (k + n) :=
        Ideal.pow_le_pow_right (by omega) (hg' _ _ (hf (n + d)))
      simpa [add_assoc] using (𝔪 ^ (k + n)).add_mem ih h1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝔪) f fun {m n} hmn ↦ by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (by omega) (hf' m d)
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  have hL0 : L = 0 := by
    rw [← Ideal.mem_bot, ← h0, Submodule.mem_iInf]
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Submodule.mem_bot R,
      ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J m) 𝔪
        (maximalIdeal.isMaximal R).ne_top, Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hB (k + n) m (hf n))
    have hz' : z - (f n - L) ∈ 𝔪 ^ n :=
      (𝔪 ^ n).sub_mem (Ideal.pow_le_pow_right (by omega) hz) (hL n)
    have : Ideal.Quotient.mk (J m) L = (z - (f n - L)) • (1 : R ⧸ J m) := by
      rw [← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, ← e]
      convert hy using 1
      ring
    rw [this]
    exact Submodule.smul_mem_smul hz' trivial
  have h1 := hf' 0 k
  have h2 := hL k
  rw [hL0, sub_zero] at h2
  have h3 : x - f k ∈ 𝔪 ^ k := by simpa [f] using h1
  simpa using (𝔪 ^ k).add_mem h3 h2
end GlobalTheory

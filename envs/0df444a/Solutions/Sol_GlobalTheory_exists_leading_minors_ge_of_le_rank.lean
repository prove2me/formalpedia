-- Prove2me | solution 1 for GlobalTheory.exists_leading_minors_ge_of_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:25.911121+00:00
-- url     : https://prove2.me/submissions/81170494-9aaf-4a5c-abcb-212d84e44b20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank
import Theorems.Thm_GlobalTheory_exists_mem_valuation_le_of_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {r : ℕ} (A : Set (Fin r → O))
    {c : O} (hc : c ≠ 0) (hA : ∀ x : Fin r → O, c • x ∈ Submodule.span O A) :
    ∀ n : ℕ, n ≤ r → ∃ t : ℕ → Fin r → O, (∀ i, i < n → t i ∈ A) ∧
      ∀ (m : ℕ) (hm : m ≤ r), m ≤ n → v (algebraMap O C c) ^ m ≤
        v (algebraMap O C (Matrix.of fun a i : Fin m => t i (Fin.castLE hm a)).det) := by
  have hvc : v (algebraMap O C c) ≠ 0 := by
    rw [Ne, v.zero_iff]
    intro h
    exact hc (hv.hom_inj (by rw [h, map_zero]))
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro m hm h0
    obtain rfl : m = 0 := Nat.le_zero.mp h0
    simp
  | succ n ih =>
    intro hn
    obtain ⟨t, htA, ht⟩ := ih (Nat.le_of_succ_le hn)
    let coef : Fin (n + 1) → O := fun a => (-1) ^ ((a : ℕ) + n) *
      (Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b))).det
    let φ : (Fin r → O) →ₗ[O] O :=
      ∑ a : Fin (n + 1), coef a • LinearMap.proj (Fin.castLE hn a)
    have hφ : ∀ x, φ x = ∑ a : Fin (n + 1), coef a * x (Fin.castLE hn a) := by
      intro x
      simp [φ, LinearMap.sum_apply]
    have hdet : ∀ x, (Matrix.of fun a i : Fin (n + 1) =>
        Function.update t n x i (Fin.castLE hn a)).det = φ x := by
      intro x
      rw [hφ, Matrix.det_succ_column _ (Fin.last n)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : (Matrix.of fun a i : Fin (n + 1) =>
          Function.update t n x i (Fin.castLE hn a)).submatrix a.succAbove
          (Fin.last n).succAbove =
          Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b)) := by
        ext b i
        simp [Function.update_of_ne (Nat.ne_of_lt i.isLt)]
      rw [this]
      simp only [coef, Matrix.of_apply, Fin.val_last, Function.update_self]
      ring
    have hval : φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1) =
        c * (Matrix.of fun a i : Fin n => t i (Fin.castLE (Nat.le_of_succ_le hn) a)).det := by
      rw [map_smul, smul_eq_mul, hφ, Finset.sum_eq_single (Fin.last n)]
      · congr 1
        simp only [coef, Pi.single_eq_same, mul_one, Fin.val_last, Fin.succAbove_last]
        rw [← two_mul, pow_mul]
        simp only [even_two, Even.neg_pow, one_pow, one_mul]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne (fun h => hb (Fin.castLE_injective hn h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hlow : v (algebraMap O C c) ^ (n + 1) ≤
        v (algebraMap O C (φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1))) := by
      rw [hval, map_mul, map_mul, pow_succ']
      exact mul_le_mul_right (ht n _ le_rfl) _
    obtain ⟨a, haA, ha⟩ := exists_mem_valuation_le_of_mem_span v hv A φ (hA _)
      (ne_of_gt (lt_of_lt_of_le (pow_pos (pos_iff_ne_zero.mpr hvc) _) hlow))
    refine ⟨Function.update t n a, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt h)]
        exact htA i h
      · rw [Function.update_self]
        exact haA
    · intro m hm hmn
      rcases Nat.lt_or_eq_of_le hmn with h | rfl
      · have h' : m ≤ n := Nat.lt_succ_iff.mp h
        have : (Matrix.of fun b i : Fin m => Function.update t n a i (Fin.castLE hm b)) =
            Matrix.of fun b i : Fin m => t i (Fin.castLE hm b) := by
          ext b i
          simp [Function.update_of_ne (Nat.ne_of_lt (lt_of_lt_of_le i.isLt h'))]
        rw [this]
        exact ht m hm h'
      · rw [hdet]
        exact hlow.trans ha
end GlobalTheory

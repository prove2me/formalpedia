-- Prove2me | solution 1 for GlobalTheory.GramCount.quad_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:12:08.440863+00:00
-- url     : https://prove2.me/submissions/476927be-92d2-46f3-9fd3-3218dd61ca1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianQuadricAffineSubspaceResidueRing
import Theorems.Thm_GlobalTheory_GramCount_quad_sum_char_pi
import Theorems.Thm_GlobalTheory_GramCount_quad_char_skew
import Theorems.Thm_GlobalTheory_GramCount_Prim_eq_zero
import Theorems.Thm_GlobalTheory_GramCount_card_fixed_sq
import Theorems.Thm_GlobalTheory_GramCount_cj_ip
import Theorems.Thm_GlobalTheory_GramCount_ip_smul_right
import Theorems.Thm_GlobalTheory_GramCount_ip_sum_right
import Theorems.Thm_GlobalTheory_T_norm_gauss_sum_hermitian_form_linear_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B] [Fintype B]
namespace GlobalTheory.GramCount
theorem _root_.solution {B : Type} [CommRing B] [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u)
    (ω : B) (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (χ : AddChar B ℂ) (hχ : χ.IsPrimitive)
    (hχc : ∀ u, χ (c u) = χ u) (k n : ℕ) (hkn : 2 * k + 1 ≤ 2 * n) (x : Fin k → Fin n → B)
    (hx : Prim c x) (g : Fin k → B) (t : B) (ht : c t = t) :
    |(Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ)
      - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ (q : ℝ) ^ n := by
  set N := Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hN
  let F : B × (Fin k → B) → ℂ := fun z => ∑ y : Fin n → B,
    χ (z.1 * (ip c y y - t)) * χ (∑ i, z.2 i * (ip c y (x i) - g i))
  let G : B × (Fin k → B) → ℂ := fun z =>
    if c z.1 = -z.1 ∧ z.2 = 0 then (q : ℂ) ^ (2 * n) else 0
  have hF : ∑ z, F z = (N : ℂ) * (q : ℂ) ^ (2 * k + 2) := by
    simp only [F]
    rw [Finset.sum_comm]
    have h1 : ∀ y : Fin n → B, ∑ z : B × (Fin k → B),
        χ (z.1 * (ip c y y - t)) * χ (∑ i, z.2 i * (ip c y (x i) - g i)) =
        if (∀ i, ip c y (x i) = g i) ∧ ip c y y = t then (q : ℂ) ^ (2 * k + 2) else 0 := by
      intro y
      rw [Fintype.sum_prod_type]
      simp only
      rw [← Finset.sum_mul_sum, AddChar.sum_mulShift _ hχ,
        quad_sum_char_pi χ hχ (fun i => ip c y (x i) - g i)]
      have h2 : ((fun i => ip c y (x i) - g i) = 0) ↔ ∀ i, ip c y (x i) = g i := by
        simp [funext_iff, sub_eq_zero]
      simp only [h2, sub_eq_zero, hB]
      by_cases h3 : (∀ i, ip c y (x i) = g i) <;> by_cases h4 : ip c y y = t <;> simp [h3, h4]
      ring
    simp only [h1]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hN, ← Set.ncard_coe_finset]
    congr 3
    ext y
    simp
  have hG : ∑ z, G z = (q : ℂ) ^ (2 * n + 1) := by
    have h1 := (card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc
      (fun a u => by simp)).2
    rw [Nat.card_eq_fintype_card (α := B), hB] at h1
    have h2 := (Nat.pow_left_injective two_ne_zero) h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
    simp only [G]
    rw [Fintype.sum_prod_type]
    have h3 : ∀ a : B, (∑ s : Fin k → B,
        if c a = -a ∧ s = 0 then (q : ℂ) ^ (2 * n) else 0) =
        if c a = -a then (q : ℂ) ^ (2 * n) else 0 := by
      intro a
      by_cases h : c a = -a <;> simp [h]
    simp only [h3]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h4 : (Finset.univ.filter fun a : B => c a = -a).card = q := by
      rw [← h2]; congr 1
    rw [h4]; ring
  have hFG : ∀ z, ‖F z - G z‖ ≤ (q : ℝ) ^ n := by
    rintro ⟨a, s⟩
    have hv : ∀ y : Fin n → B, ∑ i, s i * (ip c y (x i) - g i) =
        ip c y (∑ i, c (s i) • x i) - ∑ i, s i * g i := by
      intro y
      simp [ip_sum_right, ip_smul_right, hc, mul_sub, Finset.sum_sub_distrib]
    by_cases ha : c a = -a
    · have h0 : F (a, s) = G (a, s) := by
        have h1 : ∀ y : Fin n → B, χ (a * (ip c y y - t)) = 1 := fun y =>
          quad_char_skew c hc hω χ hχc ha (by rw [map_sub, cj_ip c hc, ht])
        simp only [F, G, h1, one_mul, ha, true_and]
        split_ifs with hs
        · simp [hs, hB, ← pow_mul]
        · simp only [hv]
          simp only [sub_eq_add_neg, AddChar.map_add_eq_mul]
          rw [← Finset.sum_mul]
          have h2 := quad_sum_char_pi χ hχ (fun j => c ((∑ i, c (s i) • x i) j))
          rw [if_neg] at h2
          · simp only [ip]
            rw [h2, zero_mul]
          · intro h3
            apply hs
            have h4 : ∑ i, c (s i) • x i = 0 := by
              funext j
              have := congrArg c (congrFun h3 j)
              simpa only [hc, Pi.zero_apply, map_zero] using this
            have h5 := hx.eq_zero c (fun i => c (s i)) h4
            funext i
            have := congrArg c (congrFun h5 i)
            simpa only [hc, Pi.zero_apply, map_zero] using this
      rw [h0, sub_self, norm_zero]
      positivity
    · have hu : IsUnit (a + c a) := hf _ (by rw [map_add, hc, add_comm])
        (fun h => ha (by linear_combination h))
      have h1 := GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le c hc q hq hB χ hχ hχc n a hu (∑ i, c (s i) • x i)
      have h2 : F (a, s) = χ (-(a * t + ∑ i, s i * g i)) *
          ∑ y : Fin n → B, χ (a * ip c y y + ip c y (∑ i, c (s i) • x i)) := by
        simp only [F, hv, Finset.mul_sum, ← AddChar.map_add_eq_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        ring
      have h3 : G (a, s) = 0 := by simp [G, ha]
      rw [h3, sub_zero, h2, norm_mul, AddChar.norm_apply, one_mul]
      exact h1
  have hS : ‖∑ z, F z - ∑ z, G z‖ ≤ (q : ℝ) ^ (2 * k + 2) * (q : ℝ) ^ n := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le_of_le _ fun z _ => hFG z).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, hB, nsmul_eq_mul]
    push_cast
    ring
  have hE : (q : ℂ) ^ (2 * n + 1) = (q : ℂ) ^ (2 * n - (2 * k + 1)) * (q : ℂ) ^ (2 * k + 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hF, hG, hE, ← sub_mul, norm_mul] at hS
  have hq' : (0 : ℝ) < (q : ℝ) ^ (2 * k + 2) := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  have h5 : ‖(q : ℂ) ^ (2 * k + 2)‖ = (q : ℝ) ^ (2 * k + 2) := by simp
  have h6 : ‖(N : ℂ) - (q : ℂ) ^ (2 * n - (2 * k + 1))‖ =
      |(N : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    rfl
  rw [h5, h6, mul_comm] at hS
  exact le_of_mul_le_mul_left hS hq'
end GlobalTheory.GramCount

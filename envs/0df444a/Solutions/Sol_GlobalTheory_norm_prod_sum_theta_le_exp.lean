-- Prove2me | solution 1 for GlobalTheory.norm_prod_sum_theta_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:44.500101+00:00
-- url     : https://prove2.me/submissions/88e1c18d-48a4-4ac6-b585-19e382cb0627

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_NormProdSumThetaLeExp
import Theorems.Thm_GlobalTheory_norm_prod_sum_mul_le_pow
import Theorems.Thm_GlobalTheory_mul_log_mul_le_add_mul_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    TStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF) (r1 : ℕ), 2 ≤ r1 → ∀ s ∈ X.Sec 1 1, s ≠ 0 → ∀ (i Nc M : ℕ), 1 ≤ Nc → M ≤ r1 ^ (2 * PT.f E * X.r ^ 2) → ∀ (c z : Fin (2 * r1 ^ 4 * i) → Fin M → ℂ) (a : Fin (2 * r1 ^ 4 * i) → Fin M → Fin X.r → Vsp X.dim), (∀ k t, ‖c k t‖ ≤ Nc) → (∀ k t, (∀ j, ((r1 : ℂ) ^ 2) • a k t j ∈ X.L) ∧ ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L, x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a k t j) + (r1 : ℂ) • y) → (∀ k t, ‖z k t‖ ≤ ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a k t j) / Real.sqrt (X.l2 1 s)) → ‖∏ k, ∑ t, c k t * z k t‖ ≤ Real.exp (-(i * (P.ph - (2 * (r1 : ℝ) ^ 4 * (P.p3 + (Real.log Nc + 2 * PT.f E * (X.r : ℝ) ^ 2 * Real.log r1)) + ((r1 : ℝ) ^ 4 * X.r * dstar (E := E) P.m / 2) * Real.log (((r1 : ℝ) ^ 4 * X.r * dstar (E := E) P.m / 2) * P.ka0))))) := by
  intro hT E _ _ _ X DF P r1 hr1 s hs hs0 i Nc M hNc hM c z a hc ha hz
  have hf : 1 ≤ PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · have := P.hfr; rw [h] at this; omega
    · exact h
  have hr : 1 ≤ X.r := by
    rcases Nat.eq_zero_or_pos X.r with h | h
    · have := P.hfr; rw [h] at this; omega
    · exact h
  have hdN : 2 ≤ dstar (E := E) P.m := by
    have := P.hm1
    unfold dstar
    nlinarith [Nat.mul_le_mul hf this]
  have hd : (2 : ℝ) ≤ dstar (E := E) P.m := by exact_mod_cast hdN
  have hrR : (1 : ℝ) ≤ X.r := by exact_mod_cast hr
  have hr1R : (2 : ℝ) ≤ r1 := by exact_mod_cast hr1
  have hNcR : (1 : ℝ) ≤ Nc := by exact_mod_cast hNc
  have hR : (1 : ℝ) ≤ (r1 : ℝ) ^ 4 := one_le_pow₀ (by linarith)
  have hka : 1 ≤ P.ka0 := by
    have h1 : (1 : ℝ) ≤ RR (E := E) := one_le_pow₀ (by linarith [P.hrd])
    have h2 : (1 : ℝ) ≤ (dstar (E := E) P.m : ℝ) ^ 2 := one_le_pow₀ (by linarith)
    unfold Par.ka0
    nlinarith
  have hph : 0 ≤ P.ph := by
    unfold Par.ph PT.ph
    split_ifs
    · positivity
    · exact le_rfl
  have hp : X.r * P.p1 ≤ P.p3 := by
    have h2 : 0 ≤ P.p2 := by
      unfold Par.p2
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m :=
        one_le_pow₀ (by linarith)
      linarith
    unfold Par.p3
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  set d : ℝ := (dstar (E := E) P.m : ℝ) with hdd
  set R : ℝ := (r1 : ℝ) ^ 4 with hRd
  set A : ℝ := R * X.r * d / 2 with hAd
  have hA : 1 ≤ A := by
    have : 1 ≤ R * X.r := one_le_mul_of_one_le_of_one_le hR hrR
    rw [hAd]; nlinarith
  set e : ℝ := P.p3 + (A * Real.log (A * P.ka0) - P.ph) / (2 * R) with he
  have hzB : ∀ k t, ‖z k t‖ ≤ Real.exp e := by
    intro k t
    refine (hz k t).trans ?_
    obtain ⟨h1, h2⟩ := hT E X DF P r1 hr1 (a k t) (ha k t).1 (ha k t).2 s hs hs0
    rcases hph.eq_or_lt with h | h
    · refine (h2 h.symm).trans (Real.exp_le_exp.2 ?_)
      have h3 : 0 ≤ Real.log (A * P.ka0) :=
        Real.log_nonneg (one_le_mul_of_one_le_of_one_le hA hka)
      have h4 : 0 ≤ (A * Real.log (A * P.ka0) - P.ph) / (2 * R) := by
        rw [← h, sub_zero]; positivity
      linarith
    · refine (h1 h).trans ?_
      rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h3 := mul_log_mul_le_add_mul_log (A := A) (κ := P.ka0) (φ := P.ph)
        (by linarith) (by linarith) h
      have h4 : Real.log (P.ka0 * P.ph) * (X.r * d / 4) + -(Real.pi * P.ph / R) =
          (A * Real.log (P.ka0 * P.ph) - 2 * Real.pi * P.ph) / (2 * R) := by
        rw [hAd]; field_simp; ring
      have h5 : (A * Real.log (P.ka0 * P.ph) - 2 * Real.pi * P.ph) / (2 * R) ≤
          (A * Real.log (A * P.ka0) - P.ph) / (2 * R) := by
        refine div_le_div_of_nonneg_right ?_ (by linarith)
        nlinarith [Real.pi_gt_three]
      rw [he, add_assoc, h4]
      linarith
  refine (norm_prod_sum_mul_le_pow c z (by linarith) hc hzB).trans ?_
  have hMR : (M : ℝ) ≤ Real.exp (2 * PT.f E * (X.r : ℝ) ^ 2 * Real.log r1) := by
    have h1 : (M : ℝ) ≤ (r1 : ℝ) ^ (2 * PT.f E * X.r ^ 2) := by exact_mod_cast hM
    refine h1.trans (le_of_eq ?_)
    have h2 : 2 * (PT.f E : ℝ) * (X.r : ℝ) ^ 2 = ((2 * PT.f E * X.r ^ 2 : ℕ) : ℝ) := by
      push_cast; ring
    rw [h2, Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hF : (M : ℝ) * (Nc * Real.exp e) ≤
      Real.exp ((Real.log Nc + 2 * PT.f E * (X.r : ℝ) ^ 2 * Real.log r1) + e) := by
    rw [Real.exp_add _ e, Real.exp_add (Real.log Nc), Real.exp_log (by linarith)]
    calc (M : ℝ) * (Nc * Real.exp e)
        ≤ Real.exp (2 * PT.f E * (X.r : ℝ) ^ 2 * Real.log r1) * (Nc * Real.exp e) :=
          mul_le_mul_of_nonneg_right hMR (by positivity)
      _ = _ := by ring
  refine (pow_le_pow_left₀ (by positivity) hF _).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  have hR0 : R ≠ 0 := by linarith
  push_cast
  rw [← hRd, he]
  field_simp
  ring
end GlobalTheory

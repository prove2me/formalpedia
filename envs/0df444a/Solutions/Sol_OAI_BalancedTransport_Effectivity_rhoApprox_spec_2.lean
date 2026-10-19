-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.rhoApprox_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:33:11.646684+00:00
-- url     : https://prove2.me/submissions/3ef029bb-2aa9-4524-9acb-445136ebab34

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RhoAlgorithms.lean:L187-L199
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.rhoApprox_spec. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Theorems.Thm_OAI_BalancedTransport_Effectivity_nat_mul_error_shift
import Theorems.Thm_OAI_BalancedTransport_Effectivity_rhoCoeffs_spec

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FlatBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

lemma rhoJet_zero_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) : rhoJet n x = 0 := by
  simp [rhoJet, expNegInvGlue.zero_of_nonpos hx]

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RelativeForce ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity

lemma error_nonneg (n : ℕ) : 0 ≤ error n := by unfold error; positivity

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RhoAlgorithms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

lemma getD_zero_of_length_le {cs : List ℤ} {j : ℕ} (h : cs.length ≤ j) :
    cs.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma rhoPolynomial_coeff_zero (n j : ℕ) (h : (rhoCoeffs n).length ≤ j) :
    (rhoPolynomial n).coeff j = 0 := by
  rw [← rhoCoeffs_spec, getD_zero_of_length_le h]

lemma rhoPolynomial_support_subset (n : ℕ) :
    (rhoPolynomial n).support ⊆ Finset.range (rhoCoeffs n).length := by
  intro j hj
  rw [Finset.mem_range]
  by_contra h
  exact (mem_support_iff.mp hj) (rhoPolynomial_coeff_zero _ _ (le_of_not_gt h))

lemma rhoPolyValue_cast (n : ℕ) (q : ℚ) :
    (rhoPolyValue n q : ℝ) = (rhoPolynomial n).eval₂ (Int.castRingHom ℝ) (q : ℝ) := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp only [rhoPolyValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_pow,
    rhoCoeffs_spec]
  change (∑ j ∈ Finset.range (rhoCoeffs n).length, ((rhoPolynomial n).coeff j : ℝ) * (q : ℝ) ^ j) = _
  exact (Finset.sum_subset (rhoPolynomial_support_subset n) (by
    intro j _ hj
    have hz : (rhoPolynomial n).coeff j = 0 := notMem_support_iff.mp hj
    simp [hz])).symm

lemma rat_abs_le_num (q : ℚ) : |(q : ℝ)| ≤ q.num.natAbs := by
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
  have ha : ((q.num.natAbs : ℕ) : ℝ) = |(q.num : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun a : ℤ => (a : ℝ)) (Int.natCast_natAbs q.num)
  rw [← ha]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < q.den)).mpr
    (le_mul_of_one_le_right (by positivity) hden)

lemma rhoApprox_spec (n : ℕ) (q : ℚ) (p : ℕ) :
    |(rhoApprox n q p : ℝ) - rhoJet n (q : ℝ)| ≤ error p := by
  by_cases hq : q ≤ 0
  · simp [rhoApprox, hq, rhoJet_zero_of_nonpos n (Rat.cast_nonpos.mpr hq), error_nonneg]
  · have hqp : (0 : ℝ) < q := Rat.cast_pos.mpr (lt_of_not_ge hq)
    rw [rhoApprox, ite_eq_right hq, Rat.cast_mul]
    have hid : rhoJet n (q : ℝ) = (rhoPolyValue n q⁻¹ : ℝ) * Real.exp (-((q : ℝ)⁻¹)) := by
      rw [rhoJet, expNegInvGlue, ite_eq_right hqp.not_ge, rhoPolyValue_cast, Rat.cast_inv]
    rw [hid, ← mul_sub, abs_mul]
    have he := expApprox_spec (-q⁻¹) (p + (rhoPolyValue n q⁻¹).num.natAbs)
    simp only [Rat.cast_neg, Rat.cast_inv] at he
    exact (mul_le_mul (rat_abs_le_num _) he (abs_nonneg _) (by positivity)).trans
      (nat_mul_error_shift _ _)

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Polynomial
open scoped NNReal


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.rhoApprox_spec := @_root_.OAI.BalancedTransport.Effectivity.rhoApprox_spec

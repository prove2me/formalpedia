-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.NumericOp.estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:42:58.2928+00:00
-- url     : https://prove2.me/submissions/ffd9968b-0161-418d-93f1-3bf43135201f

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericBounds.lean:L53-L162
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.NumericOp.estimate. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Theorems.Thm_OAI_BalancedTransport_Effectivity_log_abs_bound
import Theorems.Thm_OAI_BalancedTransport_Effectivity_rhoApprox_spec
import Theorems.Thm_OAI_BalancedTransport_Effectivity_rhoCoeffs_spec

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FlatBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

lemma rhoJet_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (rhoJet n) (rhoJet (n + 1) x) x := by
  unfold rhoJet
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    ((rhoPolynomial n).map (Int.castRingHom ℝ)) x
  simpa [rhoJet, rhoPolynomial, ← Polynomial.eval₂_eq_eval_map,
    Polynomial.derivative_map] using h

lemma rhoJet_zero_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) : rhoJet n x = 0 := by
  simp [rhoJet, expNegInvGlue.zero_of_nonpos hx]

lemma inv_pow_mul_rho_le {x : ℝ} (hx : 0 < x) (j k : ℕ) :
    x⁻¹ ^ j * expNegInvGlue x ≤ ((j + k).factorial : ℝ) * x ^ k := by
  have hf : (0 : ℝ) < (j + k).factorial := by positivity
  have he := Real.pow_div_factorial_le_exp x⁻¹ (inv_nonneg.mpr hx.le) (j + k)
  have hdiv : x⁻¹ ^ (j + k) / Real.exp x⁻¹ ≤ ((j + k).factorial : ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    simpa [mul_comm] using (div_le_iff₀ hf).mp he
  have hid : x⁻¹ ^ j * expNegInvGlue x =
      (x⁻¹ ^ (j + k) / Real.exp x⁻¹) * x ^ k := by
    rw [expNegInvGlue, ite_eq_right hx.not_ge, Real.exp_neg, pow_add]
    field_simp
    simp [inv_mul_cancel₀ (pow_ne_zero k hx.ne')]
  rw [hid]
  exact mul_le_mul_of_nonneg_right hdiv (pow_nonneg hx.le _)

lemma polynomial_rho_seam_bound (p : Polynomial ℤ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |p.eval₂ (Int.castRingHom ℝ) x⁻¹ * expNegInvGlue x| ≤
      (rhoWeight p k : ℝ) * x ^ k := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  calc
    |∑ j ∈ p.support, (Int.castRingHom ℝ) (p.coeff j) * x⁻¹ ^ j * expNegInvGlue x| ≤
        ∑ j ∈ p.support, |(Int.castRingHom ℝ) (p.coeff j) * x⁻¹ ^ j * expNegInvGlue x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ p.support, ((p.coeff j).natAbs : ℝ) * (x⁻¹ ^ j * expNegInvGlue x) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [abs_mul, abs_of_pos hx,
        abs_of_nonneg (expNegInvGlue.nonneg x), mul_assoc]
    _ ≤ ∑ j ∈ p.support, ((p.coeff j).natAbs : ℝ) *
        (((j + k).factorial : ℝ) * x ^ k) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (inv_pow_mul_rho_le hx j k) (Nat.cast_nonneg _)
    _ = (rhoWeight p k : ℝ) * x ^ k := by
      simp [rhoWeight, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_assoc]

lemma rhoJet_bound (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoWeight (rhoPolynomial n) 0 : ℝ) := by
  by_cases hx : 0 < x
  · simpa [rhoJet] using polynomial_rho_seam_bound (rhoPolynomial n) 0 hx
  · rw [rhoJet_zero_of_nonpos n (le_of_not_gt hx), abs_zero]
    exact Nat.cast_nonneg _

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

lemma error_le_one (n : ℕ) : error n ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RhoAlgorithms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma rhoBound_eq (n k : ℕ) : rhoBound n k = rhoWeight (rhoPolynomial n) k := by
  unfold rhoBound rhoWeight
  simp only [rhoCoeffs_spec]
  exact (Finset.sum_subset (rhoPolynomial_support_subset n) (by
    intro j _ hj
    have hz : (rhoPolynomial n).coeff j = 0 := notMem_support_iff.mp hj
    simp [hz])).symm

lemma rhoJet_bound_computable (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoBound n 0 : ℝ) := by
  rw [rhoBound_eq]
  exact rhoJet_bound n x

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

lemma rhoJet_lipschitz (n : ℕ) : LipschitzWith (rhoBound (n + 1) 0 : ℝ≥0) (rhoJet n) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (rhoJet_hasDerivAt n x).differentiableAt)
  intro x
  rw [(rhoJet_hasDerivAt n x).deriv]
  exact_mod_cast rhoJet_bound_computable (n + 1) x

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveLog ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

lemma logBracket_spec {q : ℚ} (hq : 0 < q) {n c : ℕ} (hc : logBracket q n c) :
    |(Denumerable.ofNat ℚ c.unpair.1 : ℝ) - Real.log (q : ℝ)| ≤ error n := by
  let r := Denumerable.ofNat ℚ c.unpair.1
  let k := c.unpair.2
  have he₀ := (abs_le.mp (expApprox_spec (r - (1 / 2 : ℚ) ^ n) k)).1
  have he₁ := (abs_le.mp (expApprox_spec (r + (1 / 2 : ℚ) ^ n) k)).2
  simp only [Rat.cast_sub, Rat.cast_add, cast_error] at he₀ he₁
  have hb₀ := (Rat.cast_lt (K := ℝ)).mpr hc.1
  have hb₁ := (Rat.cast_lt (K := ℝ)).mpr hc.2
  change ((expApprox (r - (1 / 2 : ℚ) ^ n) k + (1 / 2 : ℚ) ^ k : ℚ) : ℝ) < _ at hb₀
  change (q : ℝ) < ((expApprox (r + (1 / 2 : ℚ) ^ n) k - (1 / 2 : ℚ) ^ k : ℚ) : ℝ) at hb₁
  simp only [Rat.cast_add, Rat.cast_sub, cast_error] at hb₀ hb₁
  have hl : (r : ℝ) - error n < Real.log (q : ℝ) :=
    (Real.lt_log_iff_exp_lt (Rat.cast_pos.mpr hq)).mpr (by linarith)
  have hu : Real.log (q : ℝ) < (r : ℝ) + error n :=
    (Real.log_lt_iff_lt_exp (Rat.cast_pos.mpr hq)).mpr (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma logApprox_spec {q : ℚ} (hq : 0 < q) (n : ℕ) :
    |(logApprox q n : ℝ) - Real.log (q : ℝ)| ≤ error n := by
  rw [logApprox, ite_eq_left hq]
  apply logBracket_spec hq
  have hh := Nat.find_spec (exists_logSearchPredicate (q,n))
  simpa only [logSearchPredicate, ite_eq_left hq, logCutoff] using hh

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma exp_difference_bound {x y T : ℝ} (hx : x ≤ T) (hy : y ≤ T) :
    |Real.exp x - Real.exp y| ≤ Real.exp T * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Iic T).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => Real.differentiableAt_exp) (fun z hz => by
        rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr hz) hy hx

lemma exp_nat_bound (n : ℕ) : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
  rw [← mul_one (n : ℝ), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _

lemma clipped_inverse_bound {x q c : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    |(max c q)⁻¹ - x⁻¹| ≤ c⁻¹ ^ 2 * |q - x| := by
  have hm : c ≤ max c q := le_max_left _ _
  have hmp := hc.trans_le hm
  have hxp := hc.trans_le hx
  have hdist : |max c q - x| ≤ |q - x| := by
    rcases le_total c q with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_of_nonpos (sub_nonpos.mpr hx),
        abs_of_nonpos (sub_nonpos.mpr (h.trans hx))]
      linarith
  have hlow : c*c ≤ max c q * x := mul_le_mul hm hx hc.le hmp.le
  calc
    |(max c q)⁻¹ - x⁻¹| = |max c q - x| / (max c q * x) := by
      rw [inv_sub_inv hmp.ne' hxp.ne', abs_div,
        abs_of_pos (mul_pos hmp hxp), abs_sub_comm]
    _ ≤ |q - x| / (c*c) := div_le_div₀ (abs_nonneg _) hdist (mul_pos hc hc) hlow
    _ = c⁻¹ ^ 2 * |q - x| := by rw [div_eq_mul_inv, mul_inv_rev]; ring

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma estimate (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℚ)
    (p C : ℕ) (s : List ℝ) (q : List ℚ) (b : List (ℕ × ℕ))
    (hi : ∀ i, |(x i : ℝ)| ≤ C) (hb : RegisterEstimate p s q b) (hv : Valid o s) :
    |real d o (fun i => (x i : ℝ)) s| ≤ ((bound o C b).1 : ℝ) ∧
    |(rational d o x p q : ℝ) - real d o (fun i => (x i : ℝ)) s| ≤
      ((bound o C b).2 : ℝ) * error p := by
  rcases o with ⟨j,r,a,b'⟩
  have hA := hb.magnitude a
  have hB := hb.magnitude b'
  have hE := hb.accuracy a
  have hF := hb.accuracy b'
  have herr := error_nonneg p
  have herr1 := error_le_one p
  have hsize : |(q.getD a 0 : ℝ)| ≤ ((b.getD a (0,0)).1 : ℝ) +
      ((b.getD a (0,0)).2 : ℝ) := by
    calc
      _ ≤ |(q.getD a 0 : ℝ) - s.getD a 0| + |s.getD a 0| :=
        by simpa only [sub_add_cancel] using abs_add_le ((q.getD a 0 : ℝ) - s.getD a 0) (s.getD a 0)
      _ ≤ ((b.getD a (0,0)).2 : ℝ) * error p + ((b.getD a (0,0)).1 : ℝ) :=
        add_le_add hE hA
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (b.getD a (0,0)).2 (α := ℝ)]
  fin_cases j <;> simp only [real, rational, rationalCase, bound, boundCase, tag, rat, left, right, Valid] at hv ⊢
  · exact ⟨rat_abs_le_num r, by simp⟩
  · exact ⟨hi _, by simp⟩
  · constructor
    · simpa only [Nat.cast_add] using (abs_add_le _ _).trans (add_le_add hA hB)
    · push_cast
      have he : (q.getD a 0 : ℝ) + (q.getD b' 0 : ℝ) - (s.getD a 0 + s.getD b' 0) =
          ((q.getD a 0 : ℝ) - s.getD a 0) + ((q.getD b' 0 : ℝ) - s.getD b' 0) := by ring
      rw [he, add_mul]
      exact (abs_add_le _ _).trans (add_le_add hE hF)
  · constructor
    · simpa only [Nat.cast_mul, abs_mul] using
        mul_le_mul hA hB (abs_nonneg _) (by positivity)
    · push_cast
      have he : (q.getD a 0 : ℝ) * (q.getD b' 0 : ℝ) - s.getD a 0 * s.getD b' 0 =
          (q.getD a 0 : ℝ) * ((q.getD b' 0 : ℝ) - s.getD b' 0) +
          s.getD b' 0 * ((q.getD a 0 : ℝ) - s.getD a 0) := by ring
      rw [he]
      calc
        _ ≤ |(q.getD a 0 : ℝ)| * |(q.getD b' 0 : ℝ) - s.getD b' 0| +
            |s.getD b' 0| * |(q.getD a 0 : ℝ) - s.getD a 0| := by
          simpa only [abs_mul] using abs_add_le
            ((q.getD a 0 : ℝ) * ((q.getD b' 0 : ℝ) - s.getD b' 0))
            (s.getD b' 0 * ((q.getD a 0 : ℝ) - s.getD a 0))
        _ ≤ (((b.getD a (0,0)).1 : ℝ) + (b.getD a (0,0)).2) *
            ((b.getD b' (0,0)).2 * error p) +
            (b.getD b' (0,0)).1 * ((b.getD a (0,0)).2 * error p) :=
          add_le_add (mul_le_mul hsize hF (abs_nonneg _) (by positivity))
            (mul_le_mul hB hE (abs_nonneg _) (by positivity))
        _ = _ := by ring
  · constructor
    · simpa only [abs_neg] using hA
    · simpa only [Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hE
  · have hh := hv rfl
    have hpos : (0 : ℝ) < ((b' + 1 : ℕ) : ℝ)⁻¹ := by positivity
    constructor
    · rw [abs_inv, abs_of_pos (hpos.trans_le hh)]
      have h := inv_anti₀ hpos hh
      simpa only [inv_inv] using h
    · push_cast
      have hh' := clipped_inverse_bound (q := (q.getD a 0 : ℝ)) hpos hh
      simp only [inv_inv] at hh'
      have hcast : max ((b' : ℝ) + 1)⁻¹ (q.getD a 0 : ℝ) =
          max (((b'+1 : ℕ) : ℝ)⁻¹) (q.getD a 0 : ℝ) := by norm_cast
      rw [hcast]
      calc
        _ ≤ (((b'+1 : ℕ) : ℝ) ^ 2) * |(q.getD a 0 : ℝ) - s.getD a 0| := hh'
        _ ≤ (((b'+1 : ℕ) : ℝ) ^ 2) * ((b.getD a (0,0)).2 * error p) :=
          mul_le_mul_of_nonneg_left hE (sq_nonneg _)
        _ = _ := by push_cast; ring
  · constructor
    · exact rhoJet_bound_computable _ _
    · have hL := (rhoJet_lipschitz a).dist_le_mul (q.getD b' 0 : ℝ) (s.getD b' 0)
      simp only [Real.dist_eq, NNReal.coe_natCast] at hL
      calc
        _ ≤ |(rhoApprox a (q.getD b' 0) p : ℝ) - rhoJet a (q.getD b' 0 : ℝ)| +
            |rhoJet a (q.getD b' 0 : ℝ) - rhoJet a (s.getD b' 0)| := abs_sub_le _ _ _
        _ ≤ error p + (rhoBound (a + 1) 0 : ℝ) * |(q.getD b' 0 : ℝ) - s.getD b' 0| :=
          add_le_add (rhoApprox_spec _ _ _) hL
        _ ≤ error p + (rhoBound (a + 1) 0 : ℝ) * ((b.getD b' (0,0)).2 * error p) :=
          add_le_add_right (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)) _
        _ = _ := by push_cast; ring
  · constructor
    · rw [abs_of_pos (Real.exp_pos _), Nat.cast_pow, Nat.cast_ofNat]
      exact (Real.exp_le_exp.mpr (le_abs_self _ |>.trans hA)).trans (exp_nat_bound _)
    · have hL := exp_difference_bound (le_abs_self _ |>.trans hsize)
        ((le_abs_self _ |>.trans hA).trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
      have hL' : |Real.exp (q.getD a 0 : ℝ) - Real.exp (s.getD a 0)| ≤
          (3 : ℝ)^((b.getD a (0,0)).1 + (b.getD a (0,0)).2) *
            ((b.getD a (0,0)).2 * error p) := by
        have hh : Real.exp ((b.getD a (0,0)).1 + (b.getD a (0,0)).2) ≤
            (3 : ℝ) ^ ((b.getD a (0,0)).1 + (b.getD a (0,0)).2) := by
          simpa only [Nat.cast_add] using exp_nat_bound ((b.getD a (0,0)).1 + (b.getD a (0,0)).2)
        exact hL.trans (mul_le_mul hh hE (abs_nonneg _) (by positivity))
      calc
        _ ≤ |(expApprox (q.getD a 0) p : ℝ) - Real.exp (q.getD a 0 : ℝ)| +
            |Real.exp (q.getD a 0 : ℝ) - Real.exp (s.getD a 0)| := abs_sub_le _ _ _
        _ ≤ error p + (3 : ℝ)^((b.getD a (0,0)).1 + (b.getD a (0,0)).2) *
            ((b.getD a (0,0)).2 * error p) := add_le_add (expApprox_spec _ _) hL'
        _ = _ := by push_cast; ring
  · change (|if 0 < r then Real.log (r : ℝ) else 0| ≤ ↑(r.num.natAbs + r⁻¹.num.natAbs)) ∧
      (|(logApprox r p : ℝ) - (if 0 < r then Real.log (r : ℝ) else 0)| ≤ ((1 : ℕ) : ℝ) * error p)
    by_cases hr : 0 < r
    · rw [ite_eq_left hr]
      exact ⟨log_abs_bound hr, by simpa using logApprox_spec hr p⟩
    · rw [ite_eq_right hr]
      exact ⟨by simpa only [abs_zero] using
        (Nat.cast_nonneg (r.num.natAbs + r⁻¹.num.natAbs) (α := ℝ)),
        by simp [logApprox, hr, error_nonneg]⟩

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.NumericOp.estimate := @_root_.OAI.BalancedTransport.Effectivity.NumericOp.estimate

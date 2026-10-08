-- Prove2me | solution 1 for MazurCampaign.no_order_eleven
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T15:39:17.417474+00:00
-- url     : https://prove2.me/submissions/efadea24-e229-4229-8793-784a8ab217e3

/-
No elliptic curve over the rationals has a rational point of order 11
(mission leaf MazurCampaign.no_order_eleven).

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/TateNFDivision.lean lines 20-22, 70-72 (the polynomial F11)
  * FLT/Assumptions/MazurProof/RationalPointsN11.lean (reduction of the order-11 Tate equation to X_1(11))
  * the leaf, assembled from the two published theorems; it follows the last step of FLT/Assumptions/MazurProof/CyclicExclusion11.lean (no_tate_order11_polynomial_solution) and src/Bridge/NoOrderEleven.lean without the intermediate polynomial-system records
-/
import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurHuang_exists_tate_equation_solution_of_addOrderOf_eq_eleven
import Theorems.Thm_MazurHuang_eq_zero_or_eq_neg_four_of_X1_eleven_equation

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/TateNFDivision.lean, lines 20-22. -/
section

namespace MazurProof.TateNFDivision

variable {K : Type*} [Field K]

/-- `ψ₁₁(0,0) / b⁴⁰`.  11 monomials, total degree 8. -/
def F11 (b c : K) : K :=
  (c ^ 3 - b * (b - c)) * (b - c) ^ 3 - b * c * (b - c - c ^ 2) ^ 3

end MazurProof.TateNFDivision

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsN11.lean (whole module, imports dropped). -/
section

/-!
# Reduction of the order-11 Tate equation to the curve 11a3

The compact Tate factor `F11(b,c)=0`, with `b≠0`, produces a noncuspidal
rational point on

`Y² = X³ + 8X² + 16X + 16`.

The only remaining arithmetic input is that every rational affine point on
this curve has `X=0` or `X=-4`.  This file proves the reduction to that exact
boundary statement by rational algebra.
-/

namespace MazurProof.RationalPointsN11

def E11AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 8 * X ^ 2 + 16 * X + 16

def E11DegenerateParameter (X : ℚ) : Prop :=
  X = 0 ∨ X = -4

theorem F11_param_identity (c t : ℚ) :
    TateNFDivision.F11 (c + c ^ 2 * t) c =
      -(c ^ 8 *
        (t ^ 5 * c ^ 2 +
          t * (t - 1) * (2 * t ^ 2 - 2 * t + 1) * c +
          (t - 1) ^ 3)) := by
  unfold TateNFDivision.F11
  ring

private theorem c_ne_zero_of_F11 {b c : ℚ}
    (hb : b ≠ 0) (hF11 : TateNFDivision.F11 b c = 0) : c ≠ 0 := by
  intro hc
  subst c
  have hb5 : b ^ 5 = 0 := by
    simpa [TateNFDivision.F11] using hF11
  exact hb ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hb5)

theorem nondegenerate_E11_point_of_F11
    {b c : ℚ} (hb : b ≠ 0) (hF11 : TateNFDivision.F11 b c = 0) :
    ∃ X Y : ℚ,
      E11AffineEquation X Y ∧ ¬ E11DegenerateParameter X := by
  have hc : c ≠ 0 := c_ne_zero_of_F11 hb hF11
  let t : ℚ := (b - c) / c ^ 2
  have hb_param : b = c + c ^ 2 * t := by
    dsimp [t]
    field_simp [hc]
    ring
  have hparam := F11_param_identity c t
  rw [← hb_param, hF11] at hparam
  have hprod : c ^ 8 *
      (t ^ 5 * c ^ 2 +
        t * (t - 1) * (2 * t ^ 2 - 2 * t + 1) * c +
        (t - 1) ^ 3) = 0 := by
    linarith
  have hQ :
      t ^ 5 * c ^ 2 +
        t * (t - 1) * (2 * t ^ 2 - 2 * t + 1) * c +
        (t - 1) ^ 3 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 8 hc)
  have ht0 : t ≠ 0 := by
    intro ht
    rw [ht] at hQ
    norm_num at hQ
  have ht1 : t ≠ 1 := by
    intro ht
    rw [ht] at hQ
    norm_num at hQ
    exact hc hQ
  let numerator : ℚ :=
    2 * t ^ 5 * c + t * (t - 1) * (2 * t ^ 2 - 2 * t + 1)
  let denominator : ℚ := t * (t - 1)
  have hden : denominator ≠ 0 := by
    exact mul_ne_zero ht0 (sub_ne_zero.mpr ht1)
  have hdisc :
      numerator ^ 2 =
        denominator ^ 2 * (1 - 4 * t * (t - 1) ^ 2) := by
    dsimp [numerator, denominator]
    calc
      (2 * t ^ 5 * c +
          t * (t - 1) * (2 * t ^ 2 - 2 * t + 1)) ^ 2 =
          (t * (t - 1) * (2 * t ^ 2 - 2 * t + 1)) ^ 2 -
            4 * t ^ 5 * (t - 1) ^ 3 := by
              linear_combination 4 * t ^ 5 * hQ
      _ = (t * (t - 1)) ^ 2 * (1 - 4 * t * (t - 1) ^ 2) := by
        ring
  let y : ℚ := numerator / denominator
  have hy : y ^ 2 = 1 - 4 * t * (t - 1) ^ 2 := by
    dsimp [y]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hden)]
    simpa [mul_comm] using hdisc
  refine ⟨-4 * t, 4 * y, ?_, ?_⟩
  · unfold E11AffineEquation
    calc
      (4 * y) ^ 2 = 16 * y ^ 2 := by ring
      _ = 16 * (1 - 4 * t * (t - 1) ^ 2) := by rw [hy]
      _ = (-4 * t) ^ 3 + 8 * (-4 * t) ^ 2 + 16 * (-4 * t) + 16 := by ring
  · intro hdeg
    rcases hdeg with hzero | hneg4
    · exact ht0 (by linarith)
    · exact ht1 (by linarith)

theorem no_F11_solution_of_E11_boundary
    (hboundary : ∀ {X Y : ℚ}, E11AffineEquation X Y → E11DegenerateParameter X) :
    ¬ ∃ b c : ℚ, b ≠ 0 ∧ TateNFDivision.F11 b c = 0 := by
  rintro ⟨b, c, hb, hF11⟩
  obtain ⟨X, Y, hcurve, hnondeg⟩ :=
    nondegenerate_E11_point_of_F11 hb hF11
  exact hnondeg (hboundary hcurve)

end MazurProof.RationalPointsN11

end

open scoped WeierstrassCurve.Affine

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 11 := by
  intro x hx
  obtain ⟨b, c, hb, hF11⟩ :=
    MazurHuang.exists_tate_equation_solution_of_addOrderOf_eq_eleven E (x : (E⁄ℚ).Point)
      (by rw [AddSubgroup.addOrderOf_coe]; exact hx)
  exact MazurProof.RationalPointsN11.no_F11_solution_of_E11_boundary
    (fun {X Y} h => MazurHuang.eq_zero_or_eq_neg_four_of_X1_eleven_equation h) ⟨b, c, hb, hF11⟩

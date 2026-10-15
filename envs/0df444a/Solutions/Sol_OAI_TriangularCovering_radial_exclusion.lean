-- Prove2me | solution 1 for OAI.TriangularCovering.radial_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:10:22.153977+00:00
-- url     : https://prove2.me/submissions/2997278e-8c3d-472f-99e3-b3c0431e44f9

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean:L259-L304
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.radial_exclusion. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Theorems.Thm_OAI_TriangularCovering_rough_angle
import Theorems.Thm_OAI_TriangularCovering_weighted_errors

-- ---- inline helpers from OAI.Geometry.TriangularCovering.CoordinateCover ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

theorem d_bounds {q : ℝ} (hq : |q| ≤ 1) : 0 ≤ d q ∧ d q ≤ 1 / 8 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [abs_le.mp hq, sq_abs q]
  constructor
  · unfold d; positivity
  · unfold d
    nlinarith [sq_nonneg q, mul_self_le_mul_self (sq_nonneg q) hq2]

theorem rough_square {ε x p : ℝ} (he : 0 ≤ ε) (hx : |x| ≤ 1) (hp : |p| ≤ 1)
    (h : |x - p / 2| ≤ ε) : |x ^ 2 - p ^ 2 / 4| ≤ 3 / 2 * ε := by
  have hsum : |x + p / 2| ≤ 3 / 2 := by
    have h' := abs_add_le x (p / 2)
    rw [abs_div] at h'
    norm_num at h'
    linarith
  calc
    |x ^ 2 - p ^ 2 / 4| = |x - p / 2| * |x + p / 2| := by
      rw [← abs_mul]; congr 1; ring
    _ ≤ ε * (3 / 2) := mul_le_mul h hsum (abs_nonneg _) he
    _ = 3 / 2 * ε := by ring

theorem cross_term_bound {ε Δ x y p q a b : ℝ}
    (he : 0 ≤ ε) (hΔ : 0 ≤ Δ) (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (hxp : |x ^ 2 - p ^ 2 / 4| ≤ 3 / 2 * ε)
    (hyq : |y ^ 2 - q ^ 2 / 4| ≤ 3 / 2 * ε)
    (ha : |a - (1 + q ^ 2) / 4| ≤ Δ / 2)
    (hb : |b - (1 + p ^ 2) / 4| ≤ Δ / 2) :
    x ^ 2 * a + y ^ 2 * b ≤ d p + d q + 3 / 2 * ε + Δ / 4 := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hp).1, (abs_le.mp hp).2]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hxa : x ^ 2 * a ≤ p ^ 2 / 4 * ((1 + q ^ 2) / 4) + 3 / 4 * ε + Δ / 8 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hxp).2 ha0
    have h2 := mul_le_mul_of_nonneg_left ha1 he
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp ha).2 (sq_nonneg p)
    have h4 := mul_le_mul_of_nonneg_right hp2 hΔ
    nlinarith
  have hyb : y ^ 2 * b ≤ q ^ 2 / 4 * ((1 + p ^ 2) / 4) + 3 / 4 * ε + Δ / 8 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hyq).2 hb0
    have h2 := mul_le_mul_of_nonneg_left hb1 he
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 (sq_nonneg q)
    have h4 := mul_le_mul_of_nonneg_right hq2 hΔ
    nlinarith
  dsimp [d]
  nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]

/-- The exact cancellation which makes the secant construction work. -/
theorem radial_identity {ε x y q p a b β γ r s : ℝ}
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b) :
    (r - 1 / 2) * (1 - ε * x * q) + (s - 1 / 2) * (1 + ε * y * p) =
      ε ^ 2 * (x ^ 2 * a + y ^ 2 * b) - ε * x * (β - q / 2) + ε * y * (γ - p / 2) := by
  have hq : r * q = y - ε * x * a := by linarith
  have hp : s * p = x + ε * y * b := by linarith
  calc
    _ = r + s - 1 - ε * x * (r * q) + ε * x * q / 2 +
        ε * y * (s * p) - ε * y * p / 2 := by ring
    _ = _ := by rw [hrs, hq, hp]; ring

theorem radial_lower_est {ε M r f : ℝ} (heLt : ε < 1)
    (hM : 0 ≤ M) (hr : 1 / 2 + ε ^ 2 * M < r) (hf : 1 - ε ≤ f) :
    ε ^ 2 * M * (1 - ε) < (r - 1 / 2) * f := by
  calc
    _ ≤ ε ^ 2 * M * f := mul_le_mul_of_nonneg_left hf (by positivity)
    _ < _ := mul_lt_mul_of_pos_right (by linarith only [hr]) (by linarith only [heLt, hf])

theorem radial_failure {ε Δ x y q p a b β γ M N r s : ℝ}
    (he0 : 0 < ε) (heLt : ε < 1) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (hxy : |x| + |y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (hM0 : 0 ≤ M) (hN0 : 0 ≤ N)
    (heβ : |β - q / 2| ≤ Δ / 4) (heγ : |γ - p / 2| ≤ Δ / 4)
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b)
    (hr : 1 / 2 + ε ^ 2 * M < r) (hs : 1 / 2 + ε ^ 2 * N < s) :
    (M + N) * (1 - ε) < (x ^ 2 * a + y ^ 2 * b) + ε / 4 := by
  have he := he0.le
  have hx1 : |x| ≤ 1 := by linarith only [hxy, abs_nonneg y]
  have hy1 : |y| ≤ 1 := by linarith only [hxy, abs_nonneg x]
  have habsq : |x * q| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hx1 hq (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hbpsq : |y * p| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hy1 hp (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hf1 : 1 - ε ≤ 1 - ε * x * q := by
    nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp habsq).2 he]
  have hf2 : 1 - ε ≤ 1 + ε * y * p := by
    nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp hbpsq).1 he]
  have hstrict1 := radial_lower_est heLt hM0 hr hf1
  have hstrict2 := radial_lower_est heLt hN0 hs hf2
  have hid := radial_identity hrs hy hx
  have herr := weighted_errors he hΔ0 hxy heβ heγ
  have herr' : ε * Δ / 4 ≤ ε ^ 2 * (ε / 4) := by
    nlinarith only [mul_le_mul_of_nonneg_left hΔ1 he]
  have hscaled : ε ^ 2 * ((M + N) * (1 - ε)) <
      ε ^ 2 * ((x ^ 2 * a + y ^ 2 * b) + ε / 4) := by
    nlinarith only [hstrict1, hstrict2, hid, herr, herr']
  exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos he0)).mp hscaled

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {ε Δ x y q p a b β γ M N r s : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (hxy : |x| + |y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (hβ : |β| ≤ 1 / 2) (hγ : |γ| ≤ 1 / 2)
    (heβ : |β - q / 2| ≤ Δ / 4) (heγ : |γ - p / 2| ≤ Δ / 4)
    (hea : |a - (1 + q ^ 2) / 4| ≤ Δ / 2)
    (heb : |b - (1 + p ^ 2) / 4| ≤ Δ / 2)
    (hM : η + d q ≤ M) (hN : η + d p ≤ N)
    (hMN : M + N ≤ 1 / 4 + 2 * η)
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b) :
    r ≤ 1 / 2 + ε ^ 2 * M ∨ s ≤ 1 / 2 + ε ^ 2 * N := by
  by_contra! hbad
  have he : 0 ≤ ε := he0.le
  have hη : 0 < η := by norm_num [η]
  have heLt : ε < 1 := by unfold η at he1; linarith only [he1]
  have hx1 : |x| ≤ 1 := by linarith only [hxy, abs_nonneg y]
  have hy1 : |y| ≤ 1 := by linarith only [hxy, abs_nonneg x]
  have hM0 : 0 ≤ M := by linarith only [hM, hη, (d_bounds hq).1]
  have hN0 : 0 ≤ N := by linarith only [hN, hη, (d_bounds hp).1]
  have hr0 : 1 / 2 < r := by linarith only [hbad.1, mul_nonneg (sq_nonneg ε) hM0]
  have hs0 : 1 / 2 < s := by linarith only [hbad.2, mul_nonneg (sq_nonneg ε) hN0]
  have hsum : r + s ≤ 1 + ε / 2 := by
    have err := weighted_errors he (by norm_num : (0 : ℝ) ≤ 2) hxy
      (by norm_num; exact hβ) (by norm_num; exact hγ)
    rw [hrs]
    linarith only [err]
  have hr1 : r ≤ 1 / 2 + ε / 2 := by linarith only [hsum, hs0]
  have hs1 : s ≤ 1 / 2 + ε / 2 := by linarith only [hsum, hr0]
  have hqrough := rough_angle he hx1 hq (by rwa [abs_of_nonneg ha0]) hr0.le hr1 hy
  have hprough : |x - p / 2| ≤ ε := by
    apply rough_angle he hy1 hp (a := -b) (by simpa [abs_of_nonneg hb0] using hb1) hs0.le hs1
    linear_combination hx
  have hcross := cross_term_bound he hΔ0 hp hq ha0 ha1 hb0 hb1
    (rough_square he hx1 hp hprough) (rough_square he hy1 hq hqrough) hea heb
  have hfail := radial_failure he0 heLt hΔ0 hΔ1 hxy hq hp hM0 hN0 heβ heγ
    hrs hy hx hbad.1 hbad.2
  have hMN' : (M + N) * ε ≤ (1 / 4 + 2 * η) * ε :=
    mul_le_mul_of_nonneg_right hMN he
  have hgap : 0 < 2 * η - (2 + 2 * η) * ε - ε ^ 2 / 4 := by
    unfold η at he1 ⊢
    have he2 : ε ^ 2 ≤ (1 / 2000 : ℝ) ^ 2 := by nlinarith only [he1, he0]
    nlinarith only [he1, he2]
  nlinarith only [hfail, hcross, hM, hN, hMN', hΔ1, hgap]

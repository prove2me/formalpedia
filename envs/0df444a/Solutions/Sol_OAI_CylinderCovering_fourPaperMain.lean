-- Prove2me | solution 1 for OAI.CylinderCovering.fourPaperMain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:57:04.225551+00:00
-- url     : https://prove2.me/submissions/3ea6cc7d-efde-4a76-bc00-8015948f1748

import Mathlib
import Definitions.Def_CylinderCovering
import Definitions.Def_OAIQ049C000
import Theorems.Thm_OAI_CylinderCovering_ruledHistorical

section
-- module Solutions.OAIQ049_CC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_CoordinateCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

/-- The maximum of d on an interval is attained at an endpoint. -/
theorem d_le_max_endpoints {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    d q ≤ max (d a) (d b) := by
  have hsq : q ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
    by_cases hq : 0 ≤ q
    · have hbb : 0 ≤ b := le_trans hq hb
      exact le_trans (sq_le_sq₀ hq hbb |>.mpr hb) (le_max_right _ _)
    · have hqa : a ≤ 0 := le_trans ha (le_of_not_ge hq)
      have hqa' : q ≤ 0 := le_of_not_ge hq
      have : q ^ 2 ≤ a ^ 2 := by nlinarith
      exact le_trans this (le_max_left _ _)
  rcases le_max_iff.mp hsq with h | h
  · apply le_trans _ (le_max_left _ _)
    dsimp [d]
    nlinarith [sq_nonneg (a ^ 2 - q ^ 2), sq_nonneg q, sq_nonneg a,
      mul_nonneg (sub_nonneg.mpr h) (sq_nonneg q)]
  · apply le_trans _ (le_max_right _ _)
    dsimp [d]
    nlinarith [sq_nonneg (b ^ 2 - q ^ 2), sq_nonneg q, sq_nonneg b,
      mul_nonneg (sub_nonneg.mpr h) (sq_nonneg q)]

theorem d_bounds {q : ℝ} (hq : |q| ≤ 1) : 0 ≤ d q ∧ d q ≤ 1 / 8 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [abs_le.mp hq, sq_abs q]
  constructor
  · unfold d; positivity
  · unfold d
    nlinarith [sq_nonneg q, mul_self_le_mul_self (sq_nonneg q) hq2]

theorem coeff_bounds {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 ≤ alpha a b ∧ alpha a b ≤ 1 / 2 ∧ |beta a b| ≤ 1 / 2 ∧
    η ≤ cutoffCoeff a b ∧ cutoffCoeff a b ≤ 1 / 8 + η := by
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have ht : |a + b| ≤ 2 := (abs_add_le a b).trans (by linarith)
  have da := d_bounds ha
  have db := d_bounds hb
  dsimp [alpha, beta, cutoffCoeff]
  constructor
  · linarith [(abs_le.mp hab).1]
  constructor
  · linarith [(abs_le.mp hab).2]
  constructor
  · rw [abs_div]; norm_num
    linarith
  constructor
  · have := le_max_left (d a) (d b); linarith
  · have := max_le da.2 db.2; linarith

theorem beta_error {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    |beta a b - q / 2| ≤ (b - a) / 4 := by
  rw [abs_le]
  dsimp [beta]
  constructor <;> linarith

theorem alpha_error {a b q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1)
    (haq : a ≤ q) (hqb : q ≤ b) :
    |alpha a b - (1 + q ^ 2) / 4| ≤ (b - a) / 2 := by
  have e : alpha a b - (1 + q ^ 2) / 4 = (a * (b - q) + q * (a - q)) / 4 := by
    dsimp [alpha]; ring
  rw [e, abs_div]
  norm_num
  have h1 : |a * (b - q)| ≤ b - q := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hqb)]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hqb) ha
  have h2 : |q * (a - q)| ≤ q - a := by
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr haq)]
    nlinarith [mul_le_of_le_one_left (sub_nonneg.mpr haq) hq]
  have h3 := abs_add_le (a * (b - q)) (q * (a - q))
  linarith

/-- First crossing in a finite sequence; no monotonicity is required. -/
theorem first_crossing {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) (z : ℝ)
    (h0 : f 0 ≤ z) (hN' : z ≤ f N) :
    ∃ j : ℕ, j < N ∧ f j ≤ z ∧ z ≤ f (j + 1) := by
  have hex : ∃ i : ℕ, 0 < i ∧ i ≤ N ∧ z ≤ f i := ⟨N, hN, le_rfl, hN'⟩
  let i := Nat.find hex
  have hi : 0 < i ∧ i ≤ N ∧ z ≤ f i := Nat.find_spec hex
  have him : i - 1 + 1 = i := by omega
  refine ⟨i - 1, by omega, ?_, by simpa [him] using hi.2.2⟩
  by_cases h : i = 1
  · simpa [h] using h0
  · have hsmall : i - 1 < Nat.find hex := by dsimp [i] at *; omega
    have hmin := Nat.find_min hex hsmall
    by_contra! hz
    exact hmin ⟨by omega, by omega, le_of_lt hz⟩

/-- A uniform first-order estimate, used only after both cutoffs fail. -/
theorem rough_angle {ε x y q a r : ℝ} (he : 0 ≤ ε)
    (hx : |x| ≤ 1) (hq : |q| ≤ 1) (ha : |a| ≤ 1 / 2)
    (hr0 : 1 / 2 ≤ r) (hr1 : r ≤ 1 / 2 + ε / 2)
    (hy : y = r * q + ε * x * a) : |y - q / 2| ≤ ε := by
  have heq : y - q / 2 = (r - 1 / 2) * q + ε * x * a := by rw [hy]; ring
  have h1 : |(r - 1 / 2) * q| ≤ ε / 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ r - 1 / 2)]
    calc
      (r - 1 / 2) * |q| ≤ (r - 1 / 2) * 1 :=
        mul_le_mul_of_nonneg_left hq (by linarith)
      _ ≤ ε / 2 := by linarith
  have h2 : |ε * x * a| ≤ ε / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg he]
    calc
      ε * |x| * |a| ≤ ε * 1 * (1 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx he) ha (abs_nonneg _) (by positivity)
      _ = ε / 2 := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

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

theorem weighted_errors {ε Δ x y e f : ℝ} (he : 0 ≤ ε) (hΔ : 0 ≤ Δ)
    (hxy : |x| + |y| ≤ 1) (he' : |e| ≤ Δ / 4) (hf : |f| ≤ Δ / 4) :
    -ε * x * e + ε * y * f ≤ ε * Δ / 4 := by
  have h1 : -ε * x * e ≤ ε * |x| * (Δ / 4) := by
    calc
      -ε * x * e ≤ |-ε * x * e| := le_abs_self _
      _ = ε * |x| * |e| := by simp [abs_mul, abs_of_nonneg he]
      _ ≤ ε * |x| * (Δ / 4) := mul_le_mul_of_nonneg_left he' (by positivity)
  have h2 : ε * y * f ≤ ε * |y| * (Δ / 4) := by
    calc
      ε * y * f ≤ |ε * y * f| := le_abs_self _
      _ = ε * |y| * |f| := by simp [abs_mul, abs_of_nonneg he]
      _ ≤ ε * |y| * (Δ / 4) := mul_le_mul_of_nonneg_left hf (by positivity)
  have h3 := mul_le_mul_of_nonneg_right hxy (show 0 ≤ ε * Δ / 4 by positivity)
  nlinarith

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

/-- Quantitative radial exclusion, with uniform constants independent of the mesh. -/
theorem radial_exclusion {ε Δ x y q p a b β γ M N r s : ℝ}
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

theorem mesh_abs_le {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) : |mesh N j| ≤ 1 := by
  have h1 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have h2 : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hstep := step_pos hN
  have hn : (N : ℝ) * step N = 2 := by
    have := mesh_last hN
    dsimp [mesh] at this
    linarith only [this]
  rw [abs_le]
  dsimp [mesh]
  constructor
  · nlinarith only [mul_nonneg h1 hstep.le]
  · nlinarith only [mul_le_mul_of_nonneg_right h2 hstep.le, hn]

theorem angular_sector {N : ℕ} (hN : 0 < N) {r z ℓ : ℝ} (hz : |z| ≤ r) :
    ∃ j : ℕ, j < N ∧
      Sector (mesh N j) (mesh N (j + 1))
        (r - ℓ * beta (mesh N j) (mesh N (j + 1)))
        (z - ℓ * alpha (mesh N j) (mesh N (j + 1))) := by
  let f : ℕ → ℝ := fun i => mesh N i * r + ℓ * (1 - mesh N i ^ 2) / 4
  have hf0 : f 0 = -r := by simp [f]
  have hfN : f N = r := by simp [f, mesh_last hN]
  obtain ⟨j, hj, hlo, hhi⟩ := first_crossing hN f z
    (by rw [hf0]; exact (abs_le.mp hz).1)
    (by rw [hfN]; exact (abs_le.mp hz).2)
  let a := mesh N j
  let b := mesh N (j + 1)
  have he0 : f j = a * (r - ℓ * beta a b) + ℓ * alpha a b := by
    change a * r + ℓ * (1 - a ^ 2) / 4 = _
    dsimp [alpha, beta]; ring
  have he1 : f (j + 1) = b * (r - ℓ * beta a b) + ℓ * alpha a b := by
    change b * r + ℓ * (1 - b ^ 2) / 4 = _
    dsimp [alpha, beta]; ring
  rw [he0] at hlo
  rw [he1] at hhi
  have hlo' : a * (r - ℓ * beta a b) ≤ z - ℓ * alpha a b := by linarith only [hlo]
  have hhi' : z - ℓ * alpha a b ≤ b * (r - ℓ * beta a b) := by linarith only [hhi]
  have hdiff : 0 < b - a := by
    change 0 < mesh N (j + 1) - mesh N j
    rw [mesh_succ]
    exact step_pos hN
  refine ⟨j, hj, ?_, hlo', hhi'⟩
  have hmul : 0 ≤ (b - a) * (r - ℓ * beta a b) := by nlinarith only [hlo', hhi']
  exact nonneg_of_mul_nonneg_right hmul hdiff

theorem cutoff_pos {ε a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : 0 < cutoff ε a b := by
  have h := (coeff_bounds ha hb).2.2.2.1
  have hM : 0 ≤ cutoffCoeff a b := by unfold η at h; linarith only [h]
  dsimp [cutoff]
  nlinarith only [mul_nonneg (sq_nonneg ε) hM]

theorem angle_in_interval {a b r z : ℝ} (hr : 0 < r) (hz : Sector a b r z) :
    a ≤ z / r ∧ z / r ≤ b := by
  exact ⟨(le_div_iff₀ hr).mpr hz.2.1, (div_le_iff₀ hr).mpr hz.2.2⟩

theorem abs_le_of_interval {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hqa : a ≤ q) (hqb : q ≤ b) : |q| ≤ 1 :=
  abs_le.mpr ⟨(abs_le.mp ha).1.trans hqa, hqb.trans (abs_le.mp hb).2⟩

theorem selected_cuts {ε Δ a b c e x y r s : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (he : |e| ≤ 1)
    (hab : b - a = Δ) (hce : e - c = Δ) (hxy : |x| + |y| ≤ 1)
    (hrs : r + s = 1 - ε * x * beta a b + ε * y * beta c e)
    (hqsec : Sector a b r (y - ε * x * alpha a b))
    (hpsec : Sector c e s (x + ε * y * alpha c e)) :
    r ≤ cutoff ε a b ∨ s ≤ cutoff ε c e := by
  by_contra! hbad
  have hr : 0 < r := lt_trans (cutoff_pos ha hb) hbad.1
  have hs : 0 < s := lt_trans (cutoff_pos hc he) hbad.2
  let q := (y - ε * x * alpha a b) / r
  let p := (x + ε * y * alpha c e) / s
  have hqI : a ≤ q ∧ q ≤ b := angle_in_interval hr hqsec
  have hpI : c ≤ p ∧ p ≤ e := angle_in_interval hs hpsec
  have hq : |q| ≤ 1 := abs_le_of_interval ha hb hqI.1 hqI.2
  have hp : |p| ≤ 1 := abs_le_of_interval hc he hpI.1 hpI.2
  have h1 := coeff_bounds ha hb
  have h2 := coeff_bounds hc he
  have hβ : |beta a b - q / 2| ≤ Δ / 4 := by simpa [hab] using beta_error hqI.1 hqI.2
  have hγ : |beta c e - p / 2| ≤ Δ / 4 := by simpa [hce] using beta_error hpI.1 hpI.2
  have hea : |alpha a b - (1 + q ^ 2) / 4| ≤ Δ / 2 := by
    simpa [hab] using alpha_error ha hq hqI.1 hqI.2
  have heb : |alpha c e - (1 + p ^ 2) / 4| ≤ Δ / 2 := by
    simpa [hce] using alpha_error hc hp hpI.1 hpI.2
  have hM : η + d q ≤ cutoffCoeff a b := by
    exact add_le_add_right (d_le_max_endpoints hqI.1 hqI.2) η
  have hN : η + d p ≤ cutoffCoeff c e := by
    exact add_le_add_right (d_le_max_endpoints hpI.1 hpI.2) η
  have hMN : cutoffCoeff a b + cutoffCoeff c e ≤ 1 / 4 + 2 * η := by
    linarith only [h1.2.2.2.2, h2.2.2.2.2]
  have hy : y = r * q + ε * x * alpha a b := by
    dsimp [q]
    field_simp
    ring
  have hx : x = s * p - ε * y * alpha c e := by
    dsimp [p]
    field_simp
    ring
  have hcut := radial_exclusion he0 he1 hΔ0 hΔ1 hxy hq hp
    h1.1 h1.2.1 h2.1 h2.2.1 h1.2.2.1 h2.2.2.1 hβ hγ hea heb hM hN hMN hrs hy hx
  exact hcut.elim (not_le.mpr hbad.1) (not_le.mpr hbad.2)

/-- Every boundary point is covered, not merely almost every point. -/
theorem finite_coordinate_cover {N : ℕ} {ε x y t : ℝ}
    (hN : 0 < N) (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hmesh : step N ≤ ε ^ 2)
    (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ j : ℕ, j < N ∧ LowerHit N j ε x y t) ∨
    (∃ j : ℕ, j < N ∧ UpperHit N j ε x y t) := by
  obtain ⟨j, hj, hjs⟩ := angular_sector hN (ℓ := ε * x) hy
  obtain ⟨k, hk, hks⟩ := angular_sector hN (ℓ := -(ε * y)) hx
  have hks' : Sector (mesh N k) (mesh N (k + 1))
      (1 - t + ε * y * beta (mesh N k) (mesh N (k + 1)))
      (x + ε * y * alpha (mesh N k) (mesh N (k + 1))) := by
    simpa only [neg_mul, sub_neg_eq_add] using hks
  have hcuts := selected_cuts he0 he1 (step_pos hN).le hmesh
    (mesh_abs_le hN hj.le) (mesh_abs_le hN hj) (mesh_abs_le hN hk.le) (mesh_abs_le hN hk)
    (mesh_succ N j) (mesh_succ N k) (by linarith only [hx, hy])
    (show (t - ε * x * beta (mesh N j) (mesh N (j + 1))) +
        (1 - t + ε * y * beta (mesh N k) (mesh N (k + 1))) =
      1 - ε * x * beta (mesh N j) (mesh N (j + 1)) +
        ε * y * beta (mesh N k) (mesh N (k + 1)) by ring) hjs hks'
  exact hcuts.elim (fun h => Or.inl ⟨j, hj, hjs, h⟩) (fun h => Or.inr ⟨k, hk, hks', h⟩)

theorem ceil_step_le {ε : ℝ} (he : 0 < ε) : step ⌈2 / ε ^ 2⌉₊ ≤ ε ^ 2 := by
  have hn := ceil_count_pos he
  have hn' : (0 : ℝ) < ⌈2 / ε ^ 2⌉₊ := by exact_mod_cast hn
  unfold step
  rw [div_le_comm₀ hn' (sq_pos_of_pos he)]
  exact Nat.le_ceil _

/-- Coverage with the exact ceiling count, in intercept coordinates. -/
theorem finite_coordinate_cover_ceil {ε x y t : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ j : ℕ, j < ⌈2 / ε ^ 2⌉₊ ∧ LowerHit ⌈2 / ε ^ 2⌉₊ j ε x y t) ∨
    (∃ j : ℕ, j < ⌈2 / ε ^ 2⌉₊ ∧ UpperHit ⌈2 / ε ^ 2⌉₊ j ε x y t) :=
  finite_coordinate_cover (ceil_count_pos he0) he0 he1 (ceil_step_le he0) hx hy

end TriangularCovering


end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Asymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section

namespace TriangularCovering

lemma sq_error {x y e : ℝ} (hx : |x| ≤ 1/2) (hy : |y| ≤ 1/2)
    (he : |x-y| ≤ e) : |x^2-y^2| ≤ e := by
  have hs : |x+y| ≤ 1 := (abs_add_le _ _).trans (by linarith only [hx,hy])
  rw [sq_sub_sq,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg (x-y)) hs).trans he

lemma areaDensity_eq (q : ℝ) :
    areaDensity q = η-1/128-q^2/64+7*q^4/128 := by
  dsimp [areaDensity,d]; ring

lemma continuous_areaDensity : Continuous areaDensity := by
  unfold areaDensity d
  fun_prop

lemma areaDensity_integral : (∫ q in (-1:ℝ)..1, areaDensity q) = -13/6000 := by
  simp_rw [areaDensity_eq]
  have hf : IntervalIntegrable (fun q : ℝ => η-1/128-q^2/64) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable (fun q : ℝ => 7*q^4/128) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh : IntervalIntegrable (fun q : ℝ => q^2/64) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add hf hg,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) hh]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul,integral_pow,integral_pow,intervalIntegral.integral_const]
  norm_num [η]

end TriangularCovering

namespace TriangularCovering

lemma count_step {N : ℕ} (hN : 0 < N) : (N : ℝ)*step N = 2 := by
  have h := mesh_last hN
  dsimp [mesh] at h
  linarith only [h]

lemma integral_mesh_sum {N : ℕ} (hN : 0 < N) :
    (∑ j : Fin N, ∫ q in mesh N j..mesh N (j+1), areaDensity q) = -13/6000 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫ q in mesh N j..mesh N (j+1), areaDensity q) N]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun _ _ => continuous_areaDensity.intervalIntegrable _ _)]
  rw [mesh_zero,mesh_last hN,areaDensity_integral]

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_TriangleArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section

namespace TriangularCovering

section Triangles
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma mem_triangle_iff (a b c x : E) : x ∈ triangle a b c ↔
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r+s ≤ 1 ∧ x = a + r • (b-a) + s • (c-a) := by
  rw [triangle_translate, triangle_zero_image]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v 0, v 1, hv.1, hv.2.1, hv.2.2, by simp [add_assoc]⟩
  · rintro ⟨r, s, hr, hs, hrs, rfl⟩
    refine ⟨r • (b-a) + s • (c-a), ?_, by simp [add_assoc]⟩
    exact ⟨![r,s], ⟨hr, hs, hrs⟩, by simp⟩

end Triangles

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma projectedCylinder_area (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) :
    area (projectedCylinder u hu a b c h).base = |inner ℝ u (cross3 (b-a) (c-a))|/2 := by
  unfold area
  rw [projectedCylinder, projection_triangle_measure hu, ENNReal.toReal_ofReal (by positivity)]

lemma projectedCylinder_mem (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) {p z : Space} (hp : p ∈ triangle a b c)
    (r : ℝ) (hz : z = p + r • u) : z ∈ (projectedCylinder u hu a b c h).carrier := by
  refine ⟨projection u p, ⟨p, hp, rfl⟩, r + inner ℝ u p, ?_⟩
  change z = projection u p + (r + inner ℝ u p) • u
  rw [hz, projection]
  module

lemma unit_mul_norm (v : Space) : ‖v‖ • unit v = v := by
  by_cases hv : v = 0
  · simp [unit, hv]
  · simp [unit, smul_smul, norm_ne_zero_iff.mpr hv]

lemma projectedCylinder_mem_direction (v : Space) (hv : v ≠ 0) (a b c : Space)
    (h : inner ℝ (unit v) (cross3 (b-a) (c-a)) ≠ 0) {p z : Space}
    (hp : p ∈ triangle a b c) (r : ℝ) (hz : z = p + r • v) :
    z ∈ (projectedCylinder (unit v) (unit_norm hv) a b c h).carrier := by
  apply projectedCylinder_mem (unit v) (unit_norm hv) a b c h hp (r * ‖v‖)
  rw [mul_smul, unit_mul_norm, hz]

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_CylinderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma H_sq : H^2 = 2 := by norm_num [H]

lemma tiltV_norm (ε A B : ℝ) : ‖tiltV ε A B‖ = Real.sqrt (1+ε^2*(A^2+2*B^2)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_coord]
  dsimp [tiltV]
  congr 1
  nlinarith only [H_sq]

lemma tiltW_norm (ε A B : ℝ) : ‖tiltW ε A B‖ = Real.sqrt (1+ε^2*(A^2+2*B^2)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_coord]
  dsimp [tiltW]
  congr 1
  nlinarith only [H_sq]

lemma lowerCylinder_area {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    area (lowerCylinder hab hT ε A B).base =
      H*(b-a)*T^2 / (2*Real.sqrt (1+ε^2*(A^2+2*B^2))) := by
  rw [lowerCylinder, projectedCylinder_area, lower_triple, tiltV_norm]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos H_pos,
    abs_of_neg (sub_neg.mpr hab), abs_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

lemma upperCylinder_area {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    area (upperCylinder hab hT ε A B).base =
      H*(b-a)*T^2 / (2*Real.sqrt (1+ε^2*(A^2+2*B^2))) := by
  rw [upperCylinder, projectedCylinder_area, upper_triple, tiltW_norm]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos H_pos,
    abs_of_neg (sub_neg.mpr hab), abs_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

lemma sector_weights {a b T y t : ℝ} (hab : a < b) (hT : 0 < T)
    (_ht0 : 0 ≤ t) (htT : t ≤ T) (hay : a*t ≤ y) (hyb : y ≤ b*t) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r+s ≤ 1 ∧ r*T+s*T=t ∧ r*(a*T)+s*(b*T)=y := by
  let r := (b*t-y)/((b-a)*T)
  let s := (y-a*t)/((b-a)*T)
  have hden : 0 < (b-a)*T := mul_pos (sub_pos.mpr hab) hT
  have hrs : r*T+s*T = t := by
    dsimp [r,s]
    field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt hT]
    ring
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hyb) hden.le
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr hay) hden.le
  refine ⟨r,s,hr,hs,?_,hrs,?_⟩
  · nlinarith only [hrs, htT, hT]
  · dsimp [r,s]
    field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt hT]
    ring

lemma lower_triangle_mem {a b T y t : ℝ} (hab : a < b) (hT : 0 < T)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hay : a*t ≤ y) (hyb : y ≤ b*t) :
    point 0 y t ∈ triangle (lowerVertices a b T 0)
      (lowerVertices a b T 1) (lowerVertices a b T 2) := by
  obtain ⟨r,s,hr,hs,hrs,het,hey⟩ := sector_weights hab hT ht0 htT hay hyb
  rw [mem_triangle_iff]
  refine ⟨r,s,hr,hs,hrs,?_⟩
  ext i
  fin_cases i <;> dsimp [lowerVertices, point]
  · ring
  · nlinarith only [hey]
  · linear_combination -H * het

lemma upper_triangle_mem {a b T x s : ℝ} (hab : a < b) (hT : 0 < T)
    (hs0 : 0 ≤ s) (hsT : s ≤ T) (hax : a*s ≤ x) (hxb : x ≤ b*s) :
    point x 0 (1-s) ∈ triangle (upperVertices a b T 0)
      (upperVertices a b T 1) (upperVertices a b T 2) := by
  obtain ⟨r,q,hr,hq,hrq,hes,hex⟩ := sector_weights hab hT hs0 hsT hax hxb
  rw [mem_triangle_iff]
  refine ⟨r,q,hr,hq,hrq,?_⟩
  ext i
  fin_cases i <;> dsimp [upperVertices, point]
  · nlinarith only [hex]
  · ring
  · linear_combination H * hes

lemma lowerCylinder_hit {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B x y t : ℝ)
    (hr0 : 0 ≤ t-ε*x*B) (hrT : t-ε*x*B ≤ T)
    (hl : a*(t-ε*x*B) ≤ y-ε*x*A) (hu : y-ε*x*A ≤ b*(t-ε*x*B)) :
    point x y t ∈ (lowerCylinder hab hT ε A B).carrier := by
  apply projectedCylinder_mem_direction (tiltV ε A B) (tiltV_ne_zero ε A B)
    _ _ _ _ (lower_triangle_mem hab hT hr0 hrT hl hu) x
  ext i
  fin_cases i <;> dsimp [point, tiltV] <;> ring

lemma upperCylinder_hit {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B x y t : ℝ)
    (hs0 : 0 ≤ 1-t+ε*y*B) (hsT : 1-t+ε*y*B ≤ T)
    (hl : a*(1-t+ε*y*B) ≤ x+ε*y*A) (hu : x+ε*y*A ≤ b*(1-t+ε*y*B)) :
    point x y t ∈ (upperCylinder hab hT ε A B).carrier := by
  apply projectedCylinder_mem_direction (tiltW ε A B) (tiltW_ne_zero ε A B)
    _ _ _ _ (upper_triangle_mem hab hT hs0 hsT hl hu) y
  ext i
  fin_cases i <;> dsimp [point, tiltW] <;> ring

end TriangularCovering

namespace TriangularCovering

lemma finiteFamily_covers {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ η/2) :
    Covers (finiteFamily ε he) := by
  rintro z ⟨x,y,t,_ht0,_ht1,hx,hy,rfl⟩
  rcases finite_coordinate_cover_ceil he hsmall hx hy with ⟨j,hj,hl⟩ | ⟨j,hj,hu⟩
  · refine ⟨Fin.cast (two_mul (n ε)).symm (Fin.castAdd (n ε) (⟨j,hj⟩ : Fin (n ε))), ?_⟩
    simp only [finiteFamily, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
      Fin.append_left]
    exact lowerCylinder_hit _ _ _ _ _ _ _ _ hl.1.1 hl.2 hl.1.2.1 hl.1.2.2
  · refine ⟨Fin.cast (two_mul (n ε)).symm (Fin.natAdd (n ε) (⟨j,hj⟩ : Fin (n ε))), ?_⟩
    simp only [finiteFamily, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
      Fin.append_right]
    exact upperCylinder_hit _ _ _ _ _ _ _ _ hu.1.1 hu.2 hu.1.2.1 hu.1.2.2

lemma finiteFamily_total (ε : ℝ) (he : 0 < ε) :
    totalArea (finiteFamily ε he) / H =
      ∑ j : Fin (n ε), normalizedTerm ε (mesh (n ε) j) (mesh (n ε) (j+1)) := by
  have hs : totalArea (finiteFamily ε he) =
      (∑ j : Fin (n ε), area (lowerFamily ε he j).base) +
      (∑ j : Fin (n ε), area (upperFamily ε he j).base) := by
    change (∑ i : Fin (2*n ε),
      (fun k : Fin (n ε+n ε) => area (Fin.append (lowerFamily ε he) (upperFamily ε he) k).base)
        ((finCongr (two_mul (n ε))) i)) = _
    rw [Equiv.sum_comp (finCongr (two_mul (n ε)))
      (fun k => area (Fin.append (lowerFamily ε he) (upperFamily ε he) k).base)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hs, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [lowerFamily, upperFamily, lowerCylinder_area, upperCylinder_area]
  dsimp [normalizedTerm, speedSq, n]
  field_simp [H_ne_zero]
  ring

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Tetrahedron
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma point_coord (z : Space) : z = point (z 0) (z 1) (z 2/H) := by
  ext i
  fin_cases i <;> dsimp [point]
  field_simp [H_ne_zero]

lemma K_halfspaces (z : Space) : z ∈ K ↔ ∀ i, inner ℝ (faceNormal i) z ≤ faceBound i := by
  constructor
  · rintro ⟨x,y,t,ht0,ht1,hx,hy,rfl⟩ i
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    fin_cases i <;> simp only [inner_coord] <;> dsimp [faceNormal,faceBound,point] <;>
      nlinarith only [H_pos, hx'.1, hx'.2, hy'.1, hy'.2]
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [inner_coord] at h0 h1 h2 h3
    dsimp [faceNormal,faceBound] at h0 h1 h2 h3
    have ht : H * (z 2 / H) = z 2 := by field_simp [H_ne_zero]
    refine ⟨z 0,z 1,z 2/H,?_,?_,?_,?_,point_coord z⟩
    · nlinarith only [h2,h3,H_pos,ht]
    · nlinarith only [h0,h1,H_pos,ht]
    · rw [abs_le]; constructor <;> nlinarith only [h0,h1,H_pos,ht]
    · rw [abs_le]; constructor <;> nlinarith only [h2,h3,H_pos,ht]

lemma K_convex : Convex ℝ K := by
  have : K = ⋂ i, {z | inner ℝ (faceNormal i) z ≤ faceBound i} := by
    ext z
    simp only [mem_iInter, mem_ofPred_eq, K_halfspaces]
  rw [this]
  exact convex_iInter (fun i => convex_halfSpace_le (innerₛₗ ℝ (faceNormal i)).isLinear (faceBound i))

lemma face_vertices_mem (i : Fin 4) (j : Fin 3) : faceVertices i j ∈ face i := by
  refine ⟨?_,?_⟩
  · rw [K_halfspaces]
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp only [inner_coord] <;> dsimp [faceVertices,faceNormal,faceBound,point] <;>
      nlinarith only [H_pos]
  · fin_cases i <;> fin_cases j <;>
      simp only [inner_coord] <;> dsimp [faceVertices,faceNormal,faceBound,point] <;> ring

lemma face_convex (i : Fin 4) : Convex ℝ (face i) :=
  K_convex.inter (convex_hyperplane (innerₛₗ ℝ (faceNormal i)).isLinear (faceBound i))

lemma face_eq_triangle (i : Fin 4) :
    face i = triangle (faceVertices i 0) (faceVertices i 1) (faceVertices i 2) := by
  apply Subset.antisymm
  · rintro z ⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hz⟩
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    rw [mem_triangle_iff]
    fin_cases i
    · have hh : x = 1-t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(t+y)/2,(t-y)/2,by linarith only [hy'.1],by linarith only [hy'.2],
        by linarith only [ht1],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : x = t-1 := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(t+y)/2,(t-y)/2,by linarith only [hy'.1],by linarith only [hy'.2],
        by linarith only [ht1],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : y = t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(1-t+x)/2,(1-t-x)/2,by linarith only [hx'.1],by linarith only [hx'.2],
        by linarith only [ht0],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : y = -t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(1-t+x)/2,(1-t-x)/2,by linarith only [hx'.1],by linarith only [hx'.2],
        by linarith only [ht0],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
  · apply convexHull_min
    · rintro z ⟨j,rfl⟩
      fin_cases j <;> exact face_vertices_mem i _
    · exact face_convex i

lemma face_cross (i : Fin 4) :
    cross3 (faceVertices i 1-faceVertices i 0) (faceVertices i 2-faceVertices i 0) =
      (![2,-2,2,-2] : Fin 4 → ℝ) i • faceNormal i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    dsimp [cross3,faceVertices,faceNormal,point,crossProduct] <;> ring

lemma face_projection_measure {u : Space} (hu : ‖u‖ = 1) (i : Fin 4) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' face i) =
      ENNReal.ofReal |inner ℝ (faceNormal i) u| := by
  rw [face_eq_triangle, projection_triangle_measure hu, face_cross,
    inner_smul_right, real_inner_comm u (faceNormal i), abs_mul]
  have hh : |(![2,-2,2,-2] : Fin 4 → ℝ) i| = 2 := by fin_cases i <;> norm_num
  rw [hh]
  congr 1
  ring

end TriangularCovering

namespace TriangularCovering

lemma tetraVertices_mem (i : Fin 4) : tetraVertices i ∈ K := by
  fin_cases i
  · exact ⟨1,0,0,by norm_num,by norm_num,by norm_num,by norm_num,rfl⟩
  · exact ⟨-1,0,0,by norm_num,by norm_num,by norm_num,by norm_num,rfl⟩
  · exact ⟨0,1,1,by norm_num,by norm_num,by norm_num,by norm_num,rfl⟩
  · exact ⟨0,-1,1,by norm_num,by norm_num,by norm_num,by norm_num,rfl⟩

lemma K_eq_convexHull : K = convexHull ℝ (range tetraVertices) := by
  apply Subset.antisymm
  · rintro z ⟨x,y,t,_ht0,_ht1,hx,hy,rfl⟩
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    refine mem_convexHull_of_exists_fintype
      (![(1-t+x)/2,(1-t-x)/2,(t+y)/2,(t-y)/2] : Fin 4 → ℝ)
      tetraVertices ?_ ?_ (fun i => mem_range_self i) ?_
    · intro i
      fin_cases i <;> dsimp <;> linarith only [hx'.1,hx'.2,hy'.1,hy'.2]
    · rw [Fin.sum_univ_four]; dsimp; ring
    · ext i
      fin_cases i <;> simp only [Fin.sum_univ_four] <;> dsimp [tetraVertices,point] <;> ring
  · exact convexHull_min (by rintro _ ⟨i,rfl⟩; exact tetraVertices_mem i) K_convex

lemma tetra_edge_length {i j : Fin 4} (hij : i ≠ j) :
    dist (tetraVertices i) (tetraVertices j) = 2 := by
  have hs : ‖tetraVertices i-tetraVertices j‖^2 = 4 := by
    rw [← real_inner_self_eq_norm_sq,inner_coord]
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals dsimp [tetraVertices,point]
    all_goals nlinarith only [H_sq]
  rw [dist_eq_norm]
  nlinarith only [hs,norm_nonneg (tetraVertices i-tetraVertices j)]

lemma tetra_affineIndependent : AffineIndependent ℝ tetraVertices := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h0 := congrArg (fun z : Space => z 0) hv
  have h1 := congrArg (fun z : Space => z 1) hv
  have h2 := congrArg (fun z : Space => z 2) hv
  simp only [Fin.sum_univ_four] at hw h0 h1 h2
  dsimp [tetraVertices,point] at h0 h1 h2
  have hh : w 2 + w 3 = 0 := by nlinarith only [h2,H_pos]
  fin_cases i <;> dsimp <;> linarith only [hw,h0,h1,hh]

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Shadows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma faceNormal_sum (u : Space) : ∑ i : Fin 4, inner ℝ (faceNormal i) u = 0 := by
  simp only [Fin.sum_univ_succ, inner_coord]
  dsimp [faceNormal]
  ring

lemma positive_face_exists {u : Space} (hu : ‖u‖ = 1) :
    ∃ i : Fin 4, 0 < inner ℝ (faceNormal i) u := by
  by_contra h
  push Not at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [inner_coord] at h0 h1 h2 h3
  dsimp [faceNormal] at h0 h1 h2 h3
  have hz : u 2 = 0 := by linarith only [h0,h1,h2,h3]
  have hx : u 0 = 0 := by nlinarith only [h0,h1,hz,H_pos]
  have hy : u 1 = 0 := by nlinarith only [h2,h3,hz,H_pos]
  have hun : u = 0 := by ext i; fin_cases i <;> assumption
  simp [hun] at hu

lemma projection_add_axis {u : Space} (hu : ‖u‖ = 1) (z : Space) (r : ℝ) :
    projection u (z+r•u) = projection u z := by
  simp only [projection, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,hu]
  module

lemma forward_face {u : Space} (hu : ‖u‖ = 1) {z : Space} (hz : z ∈ K) :
    ∃ i ∈ front u, ∃ p ∈ face i, projection u p = projection u z := by
  classical
  have hfront : (front u).Nonempty := by
    obtain ⟨i,hi⟩ := positive_face_exists hu
    exact ⟨i,(mem_front u i).mpr hi⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image (front u)
    (fun i => (faceBound i-inner ℝ (faceNormal i) z)/inner ℝ (faceNormal i) u) hfront
  let r := (faceBound i-inner ℝ (faceNormal i) z)/inner ℝ (faceNormal i) u
  have hi0 : 0 < inner ℝ (faceNormal i) u := (mem_front u i).mp hi
  have hzi := K_halfspaces z |>.mp hz
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr (hzi i)) hi0.le
  have hre : r * inner ℝ (faceNormal i) u = faceBound i-inner ℝ (faceNormal i) z := by
    dsimp [r]
    exact div_mul_cancel₀ _ (ne_of_gt hi0)
  refine ⟨i,hi,z+r•u,⟨?_,?_⟩,projection_add_axis hu z r⟩
  · rw [K_halfspaces]
    intro j
    simp only [inner_add_right,inner_smul_right]
    by_cases hj : 0 < inner ℝ (faceNormal j) u
    · have hm := hmin j ((mem_front u j).mpr hj)
      have hm' : r * inner ℝ (faceNormal j) u ≤ faceBound j-inner ℝ (faceNormal j) z :=
        (le_div_iff₀ hj).mp hm
      linarith only [hm']
    · have hn := mul_nonpos_of_nonneg_of_nonpos hr (le_of_not_gt hj)
      linarith only [hn,hzi j]
  · rw [inner_add_right,inner_smul_right,hre]
    ring

lemma shadow_front {u : Space} (hu : ‖u‖ = 1) :
    projection u '' K = ⋃ i ∈ front u, projection u '' face i := by
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨i,hi,p,hp,hpq⟩ := forward_face hu hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,⟨p,hp,hpq⟩⟩⟩
  · intro h
    obtain ⟨i,hi,p,hp,hpq⟩ := mem_iUnion.mp h |>.imp (fun _ => mem_iUnion.mp)
    exact ⟨p,hp.1,hpq⟩

lemma projected_faces_inter_subset {u : Space} {i j : Fin 4}
    (hi : i ∈ front u) (hj : j ∈ front u) :
    (projection u '' face i) ∩ (projection u '' face j) ⊆ projection u '' (face i ∩ face j) := by
  rintro q ⟨⟨p,hp,hpq⟩,⟨z,hz,hzq⟩⟩
  have hh : projection u p = projection u z := hpq.trans hzq.symm
  let r := inner ℝ u p - inner ℝ u z
  have hpe : p = z+r•u := by
    dsimp [projection] at hh
    dsimp [r]
    calc
      p = (p-inner ℝ u p•u)+inner ℝ u p•u := by abel
      _ = (z-inner ℝ u z•u)+inner ℝ u p•u := by rw [hh]
      _ = z+(inner ℝ u p-inner ℝ u z)•u := by module
  have hzi := (K_halfspaces z).mp hz.1 i
  have hpj := (K_halfspaces p).mp hp.1 j
  have he_i : inner ℝ (faceNormal i) p =
      inner ℝ (faceNormal i) z+r*inner ℝ (faceNormal i) u := by
    rw [hpe,inner_add_right,inner_smul_right]
  have he_j : inner ℝ (faceNormal j) p =
      inner ℝ (faceNormal j) z+r*inner ℝ (faceNormal j) u := by
    rw [hpe,inner_add_right,inner_smul_right]
  have hr0 : 0 ≤ r := by
    have := (mem_front u i).mp hi
    nlinarith only [hzi,hp.2,he_i,this]
  have hr1 : r ≤ 0 := by
    have := (mem_front u j).mp hj
    nlinarith only [hpj,hz.2,he_j,this]
  have hr : r = 0 := le_antisymm hr1 hr0
  have hpz : p = z := by simpa [hr] using hpe
  exact ⟨p,⟨hp,hpz.symm ▸ hz⟩,hpq⟩

end TriangularCovering

namespace TriangularCovering

lemma vertical_edge_mem (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    point ((1-t)*a) (t*b) t ∈ triangle (point a 0 0) (point 0 b 1) (point 0 b 1) := by
  rw [mem_triangle_iff]
  refine ⟨t,0,ht0,le_rfl,by linarith,?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma upper_edge_mem (y : ℝ) (hy : |y| ≤ 1) :
    point 0 y 1 ∈ triangle (point 0 (-1) 1) (point 0 1 1) (point 0 1 1) := by
  rw [mem_triangle_iff]
  refine ⟨(y+1)/2,0,by linarith [(abs_le.mp hy).1],le_rfl,
    by linarith [(abs_le.mp hy).2],?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma lower_edge_mem (x : ℝ) (hx : |x| ≤ 1) :
    point x 0 0 ∈ triangle (point (-1) 0 0) (point 1 0 0) (point 1 0 0) := by
  rw [mem_triangle_iff]
  refine ⟨(x+1)/2,0,by linarith [(abs_le.mp hx).1],le_rfl,
    by linarith [(abs_le.mp hx).2],?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma face_coord (i : Fin 4) (x y t : ℝ) :
    inner ℝ (faceNormal i) (point x y t) = faceBound i ↔
      (![x+t,-x+t,y-t,-y-t] : Fin 4 → ℝ) i = (![1,1,0,0] : Fin 4 → ℝ) i := by
  fin_cases i <;> simp only [inner_coord] <;> dsimp [faceNormal,faceBound,point]
  all_goals constructor <;> intro h <;> nlinarith only [H_pos,h]

lemma face_pair_edge {i j : Fin 4} (hij : i ≠ j) :
    ∃ a b : Space, face i ∩ face j ⊆ triangle a b b := by
  wlog hlt : i < j generalizing i j
  · obtain ⟨a,b,hab⟩ := this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
    exact ⟨a,b,by simpa only [inter_comm] using hab⟩
  fin_cases i <;> fin_cases j <;> norm_num at hlt
  · refine ⟨point 0 (-1) 1,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 1 x y t).mp hj
    dsimp at hi' hj'
    have ht : t = 1 := by linarith only [hi',hj']
    have hx0 : x = 0 := by linarith only [hi',hj']
    subst t; subst x
    exact upper_edge_mem y hy
  · refine ⟨point 1 0 0,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 2 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem 1 1 t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point 1 0 0,point 0 (-1) 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem 1 (-1) t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 1 x y t).mp hi
    have hj' := (face_coord 2 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem (-1) 1 t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 0 (-1) 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 1 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem (-1) (-1) t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 1 0 0,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 2 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    have ht : t = 0 := by linarith only [hi',hj']
    have hy0 : y = 0 := by linarith only [hi',hj']
    subst t; subst y
    exact lower_edge_mem x (by simpa using hx)

lemma cross3_self (a : Space) : cross3 a a = 0 := by
  rw [cross3_coord]
  ext i
  fin_cases i <;> dsimp <;> ring

lemma face_pair_projection_null {u : Space} (hu : ‖u‖ = 1) {i j : Fin 4} (hij : i ≠ j) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' (face i ∩ face j)) = 0 := by
  obtain ⟨a,b,hab⟩ := face_pair_edge hij
  apply measure_mono_null (image_mono hab)
  rw [projection_triangle_measure hu, cross3_self,inner_zero_right,abs_zero,zero_div,ENNReal.ofReal_zero]

lemma front_pairwise_aeDisjoint {u : Space} (hu : ‖u‖ = 1) :
    (↑(front u) : Set (Fin 4)).Pairwise
      (fun i j => AEDisjoint (Measure.euclideanHausdorffMeasure 2)
        (projection u '' face i) (projection u '' face j)) := by
  intro i hi j hj hij
  exact measure_mono_null (projected_faces_inter_subset hi hj) (face_pair_projection_null hu hij)

lemma shadow_measure {u : Space} (hu : ‖u‖ = 1) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' K) =
      ∑ i ∈ front u, ENNReal.ofReal |inner ℝ (faceNormal i) u| := by
  rw [shadow_front hu,measure_biUnion_finset₀ (front_pairwise_aeDisjoint hu)]
  · exact Finset.sum_congr rfl (fun i _ => face_projection_measure hu i)
  · intro i _hi
    rw [face_eq_triangle]
    exact ((triangle_compact _ _ _).image
      (projLinear u).continuous_of_finiteDimensional).measurableSet.nullMeasurableSet

end TriangularCovering

namespace TriangularCovering

lemma max_pos_abs (a : ℝ) : max a 0 = (|a|+a)/2 := by
  by_cases h : 0 ≤ a
  · rw [max_eq_left h,abs_of_nonneg h]; ring
  · rw [max_eq_right (le_of_not_ge h),abs_of_nonpos (le_of_not_ge h)]; ring

lemma shadowArea_positive_sum {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = ∑ i : Fin 4, max (inner ℝ (faceNormal i) u) 0 := by
  rw [shadowArea,area,shadow_measure hu,ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [front,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < inner ℝ (faceNormal i) u
  · rw [ite_eq_left h,abs_of_pos h,max_eq_left h.le]
  · rw [ite_eq_right h,max_eq_right (le_of_not_gt h)]

lemma shadowArea_abs_sum {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = (∑ i : Fin 4, |inner ℝ (faceNormal i) u|)/2 := by
  rw [shadowArea_positive_sum hu]
  simp_rw [max_pos_abs]
  rw [← Finset.sum_div,Finset.sum_add_distrib,faceNormal_sum,add_zero]

lemma abs_pair (a b : ℝ) : |a+b|+|a-b| = 2*max |a| |b| := by
  simp only [abs_eq_max_neg,max_def]
  split_ifs <;> linarith

lemma shadowArea_formula {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = max (H*|u 0|) |u 2| + max (H*|u 1|) |u 2| := by
  rw [shadowArea_abs_sum hu,Fin.sum_univ_four]
  simp only [inner_coord]
  dsimp [faceNormal]
  have h1 := abs_pair (H*u 0) (u 2)
  have h2 := abs_pair (H*u 1) (u 2)
  rw [abs_mul,abs_of_pos H_pos] at h1 h2
  have he1 : |-H*u 0+0*u 1+1*u 2| = |H*u 0-u 2| := by
    rw [← abs_neg]
    congr 1
    ring
  have he2 : |0*u 0+-H*u 1+-1*u 2| = |H*u 1+u 2| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [he1,he2]
  have he3 : |H*u 0+0*u 1+1*u 2| = |H*u 0+u 2| := by congr 1; ring
  have he4 : |0*u 0+H*u 1+-1*u 2| = |H*u 1-u 2| := by congr 1; ring
  rw [he3,he4]
  linarith only [h1,h2]

lemma shadowArea_ge_H {u : Space} (hu : ‖u‖ = 1) : H ≤ shadowArea u := by
  rw [shadowArea_formula hu]
  let A := max (H*|u 0|) |u 2|
  let B := max (H*|u 1|) |u 2|
  have hA : H*|u 0| ≤ A := le_max_left _ _
  have hB : H*|u 1| ≤ B := le_max_left _ _
  have hAz : |u 2| ≤ A := le_max_right _ _
  have hBz : |u 2| ≤ B := le_max_right _ _
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hAz
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hBz
  have hAs := pow_le_pow_left₀ (mul_nonneg H_pos.le (abs_nonneg (u 0))) hA 2
  have hBs := pow_le_pow_left₀ (mul_nonneg H_pos.le (abs_nonneg (u 1))) hB 2
  rw [mul_pow,H_sq,sq_abs] at hAs hBs
  have hAB := mul_le_mul hAz hBz (abs_nonneg _) hA0
  have hu2 := real_inner_self_eq_norm_sq u
  rw [inner_coord,hu] at hu2
  have hz2 : |u 2| * |u 2| = (u 2)^2 := by nlinarith only [sq_abs (u 2)]
  change H ≤ A+B
  nlinarith only [hu2,hAs,hBs,hAB,hz2,H_sq,H_pos,hA0,hB0]

lemma xAxis_unit : ‖tiltV 0 0 0‖ = 1 := by rw [tiltV_norm]; norm_num

lemma xAxis_shadow : shadowArea (tiltV 0 0 0) = H := by
  rw [shadowArea_formula xAxis_unit]
  dsimp [tiltV]
  simp [H_pos.le]

/-- The minimum Euclidean shadow area equals the height H. -/
theorem projection_minimum : A_min = H := by
  unfold A_min
  apply le_antisymm
  · apply csInf_le
    · exact ⟨H,by rintro a ⟨u,hu,rfl⟩; exact shadowArea_ge_H hu⟩
    · exact ⟨tiltV 0 0 0,xAxis_unit,xAxis_shadow.symm⟩
  · apply le_csInf
    · exact ⟨H,tiltV 0 0 0,xAxis_unit,xAxis_shadow.symm⟩
    · rintro a ⟨u,hu,rfl⟩
      exact shadowArea_ge_H hu

end TriangularCovering

namespace TriangularCovering

lemma normalPlane_rank {u : Space} (hu : ‖u‖ = 1) :
    Module.finrank ℝ (normalPlane u) = 2 := by
  have hun : u ≠ 0 := by intro h; simp [h] at hu
  have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hun] at h
  have hr : Module.finrank ℝ Space = 3 := by simp
  rw [hr] at h
  change 1 + Module.finrank ℝ (normalPlane u) = 3 at h
  omega

lemma normalPlane_projection {u : Space} (hu : ‖u‖ = 1) (z : Space) :
    (normalPlane u).starProjection z = projection u z := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (projection_perp hu z)
  · intro w hw
    have hw' : inner ℝ u w = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
    simp [projection,inner_smul_left,hw']

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma relativeCost_le_totalArea {m : ℕ} (c : Fin m → TriCylinder) :
    relativeCost c ≤ totalArea c/H := by
  unfold relativeCost totalArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg H_pos
    (shadowArea_ge_H (c i).unit_axis)

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Angular_AreaRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TriangularCovering
open Set MeasureTheory
open scoped Interval

lemma d_lipschitz_sharp {a q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1) :
    |d a - d q| ≤ (3 / 8 : ℝ) * |a - q| := by
  have ha2 : a ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp ha).1, (abs_le.mp ha).2]
  have hq2 : q ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have has : |a + q| ≤ 2 := (abs_add_le _ _).trans (by linarith only [ha, hq])
  have hs0 : 0 ≤ 1 + a ^ 2 + q ^ 2 := by positivity
  have hs1 : 1 + a ^ 2 + q ^ 2 ≤ 3 := by linarith only [ha2, hq2]
  have hid : d a - d q = (a - q) * ((a + q) * (1 + a ^ 2 + q ^ 2) / 16) := by
    dsimp [d]
    ring
  have hfactor : |(a + q) * (1 + a ^ 2 + q ^ 2) / 16| ≤ (3 / 8 : ℝ) := by
    rw [abs_div, abs_mul, abs_of_nonneg hs0]
    norm_num
    have hp := mul_le_mul has hs1 hs0 (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [hp]
  rw [hid, abs_mul, mul_comm (3 / 8 : ℝ)]
  exact mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)

lemma cutoffCoeff_error_sharp {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hq : a ≤ q ∧ q ≤ b) :
    |cutoffCoeff a b - (η + d q)| ≤ (3 / 8 : ℝ) * (b - a) := by
  have hqab : |q| ≤ 1 := abs_le.mpr
    ⟨(abs_le.mp ha).1.trans hq.1, hq.2.trans (abs_le.mp hb).2⟩
  have h1 := d_lipschitz_sharp ha hqab
  have h2 := d_lipschitz_sharp hb hqab
  rw [abs_of_nonpos (sub_nonpos.mpr hq.1)] at h1
  rw [abs_of_nonneg (sub_nonneg.mpr hq.2)] at h2
  have hlo := d_le_max_endpoints hq.1 hq.2
  have hhi : max (d a) (d b) ≤ d q + (3 / 8 : ℝ) * (b - a) := by
    apply max_le <;> linarith only [(abs_le.mp h1).2, (abs_le.mp h2).2, hq.1, hq.2]
  dsimp [cutoffCoeff]
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi, hq.1, hq.2]

lemma density_error_sharp {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hq : a ≤ q ∧ q ≤ b) :
    |cutoffCoeff a b - speedSq a b / 8 - areaDensity q| ≤ (b - a) / 2 := by
  have hqab : |q| ≤ 1 := abs_le.mpr
    ⟨(abs_le.mp ha).1.trans hq.1, hq.2.trans (abs_le.mp hb).2⟩
  have hc := coeff_bounds ha hb
  have hal : |alpha a b| ≤ 1 / 2 := by
    rw [abs_of_nonneg hc.1]
    exact hc.2.1
  have hq2 : q ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hqab).1, (abs_le.mp hqab).2]
  have hql : |(1 + q ^ 2) / 4| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by positivity)]
    linarith only [hq2]
  have haq := sq_error hal hql (alpha_error ha hqab hq.1 hq.2)
  have hqr : |q / 2| ≤ 1 / 2 := by
    rw [abs_div]
    norm_num
    linarith only [hqab]
  have hbq := sq_error hc.2.2.1 hqr (beta_error hq.1 hq.2)
  have hspeed : |speedSq a b - (((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2)| ≤ b - a := by
    have hid : speedSq a b - (((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2) =
        ((alpha a b) ^ 2 - ((1 + q ^ 2) / 4) ^ 2) +
          2 * ((beta a b) ^ 2 - (q / 2) ^ 2) := by
      dsimp [speedSq]
      ring
    rw [hid]
    have h := abs_add_le ((alpha a b) ^ 2 - ((1 + q ^ 2) / 4) ^ 2)
      (2 * ((beta a b) ^ 2 - (q / 2) ^ 2))
    rw [abs_mul] at h
    norm_num at h
    linarith only [h, haq, hbq]
  have hM := cutoffCoeff_error_sharp ha hb hq
  have hid : cutoffCoeff a b - speedSq a b / 8 - areaDensity q =
      (cutoffCoeff a b - (η + d q)) -
        (speedSq a b - (((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2)) / 8 := by
    dsimp [areaDensity]
    ring
  rw [hid]
  have hr := abs_add_le (cutoffCoeff a b - (η + d q))
    (-((speedSq a b - (((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2)) / 8))
  rw [← sub_eq_add_neg, abs_neg] at hr
  rw [abs_div] at hr
  norm_num at hr
  linarith only [hr, hM, hspeed]

lemma interval_density_error_sharp {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≤ b) :
    |(b - a) * (cutoffCoeff a b - speedSq a b / 8) -
      (∫ q in a..b, areaDensity q)| ≤ (b - a) ^ 2 / 2 := by
  have hu : ∀ q ∈ Ι a b,
      ‖cutoffCoeff a b - speedSq a b / 8 - areaDensity q‖ ≤ (b - a) / 2 := by
    intro q hq
    rw [Set.uIoc_of_le hab] at hq
    simpa only [Real.norm_eq_abs] using density_error_sharp ha hb ⟨hq.1.le, hq.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hu
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => cutoffCoeff a b - speedSq a b / 8)
    (g := areaDensity) (continuous_const.intervalIntegrable _ _)
    (continuous_areaDensity.intervalIntegrable _ _), intervalIntegral.integral_const,
    Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  nlinarith only [h]

lemma coefficientSum_error_sharp {N : ℕ} (hN : 0 < N) :
    |coefficientSum N + 13 / 6000| ≤ step N := by
  have hi := integral_mesh_sum hN
  have hid : coefficientSum N + 13 / 6000 =
      ∑ j : Fin N, (step N * (cutoffCoeff (mesh N j) (mesh N (j + 1)) -
        speedSq (mesh N j) (mesh N (j + 1)) / 8) -
        ∫ q in mesh N j..mesh N (j + 1), areaDensity q) := by
    rw [Finset.sum_sub_distrib, hi]
    dsimp [coefficientSum]
    ring
  rw [hid]
  calc
    _ ≤ ∑ j : Fin N, |step N * (cutoffCoeff (mesh N j) (mesh N (j + 1)) -
        speedSq (mesh N j) (mesh N (j + 1)) / 8) -
        ∫ q in mesh N j..mesh N (j + 1), areaDensity q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, (step N) ^ 2 / 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := interval_density_error_sharp (mesh_abs_le hN j.isLt.le)
        (mesh_abs_le hN j.isLt)
        (le_of_lt (by have := mesh_succ N j; have := step_pos hN; linarith))
      simpa only [mesh_succ] using h
    _ = step N := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (N : ℝ) * ((step N) ^ 2 / 2) = ((N : ℝ) * step N) * step N / 2 := by ring
        _ = step N := by rw [count_step hN]; ring

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Angular_Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace AngularTaylor

theorem inv_sqrt_remainder {x : ℝ} (hx : 0 ≤ x) :
    |1 / Real.sqrt (1 + x) - (1 - x / 2)| ≤ (3 / 8) * x ^ 2 := by
  let t := Real.sqrt (1 + x)
  have ht : 1 ≤ t := by
    dsimp [t]
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht2 : t ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hden : 0 < 2 * t * (t + 1) ^ 2 := by positivity
  have hfac : 0 ≤ (t + 2) / (2 * t * (t + 1) ^ 2) := by positivity
  have hfac1 : (t + 2) / (2 * t * (t + 1) ^ 2) ≤ 3 / 8 := by
    apply (div_le_iff₀ hden).2
    have hp : 0 ≤ (t - 1) * (3 * t ^ 2 + 9 * t + 8) :=
      mul_nonneg (sub_nonneg.mpr ht) (by positivity)
    nlinarith only [hp]
  have heq : 1 / t - (1 - x / 2) =
      x ^ 2 * ((t + 2) / (2 * t * (t + 1) ^ 2)) := by
    have hxid : x = t ^ 2 - 1 := by linarith only [ht2]
    rw [hxid]
    field_simp
    ring
  change |1 / t - (1 - x / 2)| ≤ (3 / 8) * x ^ 2
  rw [heq, abs_of_nonneg (mul_nonneg (sq_nonneg x) hfac)]
  nlinarith only [mul_le_mul_of_nonneg_left hfac1 (sq_nonneg x)]

theorem bounded_product_remainder {z M A : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hM0 : 0 ≤ M) (hM1 : M ≤ 1 / 4)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    |(1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A) -
      (1 / 4 + z * (M - A / 8))| ≤ (47 / 128) * z ^ 2 := by
  let B : ℝ := (1 / 2 + z * M) ^ 2
  let R : ℝ := 1 / Real.sqrt (1 + z * A) - (1 - z * A / 2)
  have hzM0 : 0 ≤ z * M := mul_nonneg hz0 hM0
  have hzM1 : z * M ≤ 1 / 4 := by
    nlinarith only [mul_le_mul hz1 hM1 hM0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hB0 : 0 ≤ B := sq_nonneg _
  have hB1 : B ≤ 9 / 16 := by dsimp [B]; nlinarith only [hzM0, hzM1]
  have hA2 : A ^ 2 ≤ 1 := by nlinarith only [hA0, hA1]
  have hR : |R| ≤ (3 / 8) * z ^ 2 := by
    have h := inv_sqrt_remainder (mul_nonneg hz0 hA0)
    have hb := mul_le_of_le_one_right (sq_nonneg z) hA2
    dsimp [R]
    nlinarith only [h, hb]
  have hBR : |B * R| ≤ (27 / 128) * z ^ 2 := by
    rw [abs_mul, abs_of_nonneg hB0]
    have h := mul_le_mul hB1 hR (abs_nonneg R) (by norm_num : (0 : ℝ) ≤ 9 / 16)
    nlinarith only [h]
  have hM2 : M ^ 2 ≤ 1 / 16 := by nlinarith only [hM0, hM1]
  have hMA0 : 0 ≤ M * A := mul_nonneg hM0 hA0
  have hMA1 : M * A ≤ 1 / 4 := by
    nlinarith only [mul_le_mul hM1 hA1 hA0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hZM0 : 0 ≤ z * M ^ 2 * A := by positivity
  have hZM1 : z * M ^ 2 * A ≤ 1 / 16 := by
    calc
      z * M ^ 2 * A ≤ 1 * (1 / 16) * 1 := mul_le_mul
        (mul_le_mul hz1 hM2 (sq_nonneg _) (by norm_num)) hA1 hA0 (by norm_num)
      _ = 1 / 16 := by ring
  have hG : |M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2| ≤ 5 / 32 := by
    rw [abs_le]
    constructor <;> nlinarith only [hM2, sq_nonneg M, hMA0, hMA1, hZM0, hZM1]
  have hZG : |z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2)| ≤
      z ^ 2 * (5 / 32) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hG (sq_nonneg _)
  have hid : (1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A) -
      (1 / 4 + z * (M - A / 8)) =
      B * R + z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2) := by
    dsimp [B, R]
    ring
  rw [hid]
  have hab := abs_add_le (B * R) (z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2))
  nlinarith only [hab, hZG, hBR]

end AngularTaylor

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Angular_SharpArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TriangularCovering
open Set MeasureTheory

lemma term_remainder_sharp {ε a b : ℝ} (he : |ε| ≤ 1)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≤ b) :
    |normalizedTerm ε a b - (b-a)*(1/4+ε^2*(cutoffCoeff a b-speedSq a b/8))|
      ≤ (b-a)/2*ε^4 := by
  have hc := coeff_bounds ha hb
  have hM0 : 0 ≤ cutoffCoeff a b := by
    have := hc.2.2.2.1
    dsimp [η] at this
    linarith
  have hM1 : cutoffCoeff a b ≤ 1/4 := by
    have := hc.2.2.2.2
    dsimp [η] at this
    linarith
  have hD0 : 0 ≤ speedSq a b := by unfold speedSq; positivity
  have hD1 : speedSq a b ≤ 1 := by
    have ha2 : (alpha a b)^2 ≤ 1/4 := by nlinarith only [hc.1,hc.2.1]
    have hb2 : (beta a b)^2 ≤ 1/4 := by
      nlinarith only [(abs_le.mp hc.2.2.1).1,(abs_le.mp hc.2.2.1).2]
    dsimp [speedSq]
    linarith only [ha2,hb2]
  have he2 : ε^2 ≤ 1 := by nlinarith only [(abs_le.mp he).1,(abs_le.mp he).2]
  have hh := AngularTaylor.bounded_product_remainder
    (sq_nonneg ε) he2 hM0 hM1 hD0 hD1
  have hid : normalizedTerm ε a b - (b-a)*(1/4+ε^2*(cutoffCoeff a b-speedSq a b/8)) =
      (b-a)*((1/2+ε^2*cutoffCoeff a b)^2 / Real.sqrt (1+ε^2*speedSq a b) -
        (1/4+ε^2*(cutoffCoeff a b-speedSq a b/8))) := by
    dsimp [normalizedTerm,cutoff]
    ring
  rw [hid,abs_mul,abs_of_nonneg (sub_nonneg.mpr hab)]
  have h := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hab)
  calc
    _ ≤ (b-a)*((47/128)*(ε^2)^2) := h
    _ ≤ (b-a)/2*ε^4 := by
      have := mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg (ε^2))
      nlinarith only [this]

lemma mesh_term_remainder_sharp {ε : ℝ} {N : ℕ} (he : |ε| ≤ 1) (hN : 0 < N) :
    |(∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2+ε^2 * coefficientSum N)| ≤ ε^4 := by
  let f : Fin N → ℝ := fun j => step N*(1/4+ε^2*
    (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8))
  have hsum : (∑ j : Fin N, f j) = 1/2+ε^2*coefficientSum N := by
    dsimp [f,coefficientSum]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,Finset.mul_sum]
    have heq : (∑ j : Fin N, step N * (ε^2 *
        (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8))) =
        ∑ j : Fin N, ε^2 * (step N *
        (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    congr 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have := count_step hN
    linarith only [this]
  rw [← hsum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |normalizedTerm ε (mesh N j) (mesh N (j+1))-f j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, step N/2*ε^4 := by
      apply Finset.sum_le_sum
      intro j _
      have hab : mesh N j ≤ mesh N (j+1) := (mesh_strict hN j).le
      have h := term_remainder_sharp he (mesh_abs_le hN j.isLt.le)
        (mesh_abs_le hN j.isLt) hab
      simpa only [mesh_succ,f] using h
    _ = ε^4 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      calc
        (N : ℝ)*(step N/2*ε^4) = ((N : ℝ)*step N)/2*ε^4 := by ring
        _ = ε^4 := by rw [count_step hN]; ring

lemma uniform_scalar_sum_sharp {ε : ℝ} {N : ℕ} (he : |ε| ≤ 1) (hN : 0 < N)
    (hstep : step N ≤ ε^2) :
    |(∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2-(13/6000:ℝ)*ε^2)| ≤ 2*ε^4 := by
  have hR := mesh_term_remainder_sharp he hN
  have hC := coefficientSum_error_sharp hN
  have hc : |ε^2*(coefficientSum N+13/6000)| ≤ ε^4 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc
      ε^2*|coefficientSum N+13/6000| ≤ ε^2*step N :=
        mul_le_mul_of_nonneg_left hC (sq_nonneg _)
      _ ≤ ε^2*ε^2 := mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
      _ = ε^4 := by ring
  have hid : (∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2-(13/6000:ℝ)*ε^2) =
      ((∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
        (1/2+ε^2*coefficientSum N)) + ε^2*(coefficientSum N+13/6000) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [hR,hc])

lemma finiteFamily_expansion_sharp {ε : ℝ} (he : 0 < ε) (hε : ε ≤ 1) :
    |totalArea (finiteFamily ε he)/H - (1/2-(13/6000:ℝ)*ε^2)| ≤ 2*ε^4 := by
  rw [finiteFamily_total]
  exact uniform_scalar_sum_sharp (by rwa [abs_of_pos he])
    (ceil_count_pos he) (ceil_step_le he)

lemma finiteFamily_ratio_lt_closed {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ 1/2000) :
    totalArea (finiteFamily ε he)/H < 1/2 := by
  have hε : ε ≤ 1 := by linarith only [hsmall]
  have hr := (abs_le.mp (finiteFamily_expansion_sharp he hε)).2
  have hesq : ε^2 ≤ (1/2000:ℝ)^2 :=
    (sq_le_sq₀ he.le (by norm_num)).2 hsmall
  have hc : 2*ε^2 < (13/6000:ℝ) := by norm_num at hesq; linarith only [hesq]
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos he) (sub_neg.mpr hc)
  nlinarith only [hr,hneg]

lemma finiteFamily_strict_closed {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ 1/2000) :
    totalArea (finiteFamily ε he) < A_min/2 := by
  rw [projection_minimum]
  have h := (div_lt_iff₀ H_pos).mp (finiteFamily_ratio_lt_closed he hsmall)
  linarith only [h]

lemma finiteFamily_relative_lt_closed {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ 1/2000) :
    relativeCost (finiteFamily ε he) < 1/2 :=
  (relativeCost_le_totalArea _).trans_lt (finiteFamily_ratio_lt_closed he hsmall)

lemma finiteFamily_explicit (ε : ℝ) (he : 0 < ε) :
    ExplicitAngularFamily ε (finiteFamily ε he) := by
  intro j
  simp only [lowerAngularIndex,upperAngularIndex,finiteFamily,Function.comp_apply,
    Fin.cast_cast,Fin.cast_eq_self,Fin.append_left,Fin.append_right]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem angularArea_result : AngularAreaStatement := by
  intro ε he hε
  exact ⟨finiteFamily ε he,finiteFamily_explicit ε he,finiteFamily_total ε he,
    finiteFamily_expansion_sharp he hε⟩

theorem explicitAngular_result : ExplicitAngularStatement := by
  refine ⟨projection_minimum,?_⟩
  intro ε he hsmall
  have hη : ε ≤ η/2 := by norm_num [η]; exact hsmall
  have hε : ε ≤ 1 := by linarith only [hsmall]
  exact ⟨finiteFamily ε he,finiteFamily_explicit ε he,finiteFamily_covers he hη,
    finiteFamily_expansion_sharp he hε,finiteFamily_strict_closed he hsmall,
    finiteFamily_relative_lt_closed he hsmall⟩

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_CylinderSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace Pointwise

noncomputable section
namespace CylinderCovering.Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma project_map (u t x : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    project (L u) (map t r L x) =
      project (L u) t + r • L (project u x) := by
  simp only [project, map, inner_add_right, inner_smul_right,
    L.inner_map_map, map_sub, map_smul]
  module

lemma carrier_image (B : Set E) (u t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    map t r L '' carrier B u = carrier (transportedBase B u t r L) (L u) := by
  ext z
  constructor
  · rintro ⟨x, ⟨b, hb, s, rfl⟩, rfl⟩
    refine ⟨baseMap u t r L b, ⟨b, hb, rfl⟩,
      inner ℝ (L u) t + r * s, ?_⟩
    simp only [map, baseMap, project, map_add, map_smul]
    module
  · rintro ⟨b', ⟨b, hb, rfl⟩, s, rfl⟩
    refine ⟨b + ((s - inner ℝ (L u) t) / r) • u,
      ⟨b, hb, (s - inner ℝ (L u) t) / r, rfl⟩, ?_⟩
    simp only [map, baseMap, project, map_add, map_smul, smul_add, smul_smul]
    rw [mul_div_cancel₀ _ hr]
    module

variable [MeasurableSpace E] [BorelSpace E]

lemma area_map (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) (B : Set E) :
    area (map t r L '' B) = r ^ 2 * area B := by
  unfold area
  rw [euclideanHausdorffMeasure_map t hr L B 2]
  simp [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    Real.norm_eq_abs]

lemma area_transportedBase (B : Set E) (u t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    area (transportedBase B u t r L) = r ^ 2 * area B :=
  area_map (project (L u) t) hr L B

lemma shadowArea_map (K : Set E) (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) (u : E) :
    shadowArea (map t r L '' K) (L u) = r ^ 2 * shadowArea K u := by
  unfold shadowArea
  have himage : project (L u) '' (map t r L '' K) =
      map (project (L u) t) r L '' (project u '' K) := by
    simp only [image_image]
    congr 1
    funext x
    exact project_map u t x r L
  rw [himage, area_map _ hr L]

lemma shadowArea_range_map (K : Set E) (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea (map t r L '' K) u} =
    (fun a : ℝ => r ^ 2 * a) '' {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea K u} := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨shadowArea K (L.symm u), ⟨L.symm u, by simpa using hu, rfl⟩, ?_⟩
    simpa using (shadowArea_map K t hr L (L.symm u)).symm
  · rintro ⟨b, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨L u, by simpa using hu, (shadowArea_map K t hr L u).symm⟩

lemma minimumArea_le_shadowArea (K : Set E) {u : E} (hu : ‖u‖ = 1) :
    minimumArea K ≤ shadowArea K u := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨v, hv, rfl⟩
    exact ENNReal.toReal_nonneg
  · exact ⟨u, hu, rfl⟩

lemma minimumArea_map [Nontrivial E] (K : Set E) (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    minimumArea (map t r L '' K) = r ^ 2 * minimumArea K := by
  have hne : {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea K u}.Nonempty := by
    obtain ⟨u, hu⟩ := exists_norm_eq E (show (0:ℝ) ≤ 1 by norm_num)
    exact ⟨shadowArea K u, u, hu, rfl⟩
  have hbdd : BddBelow {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea K u} := by
    refine ⟨0, ?_⟩
    rintro a ⟨u, hu, rfl⟩
    exact ENNReal.toReal_nonneg
  unfold minimumArea
  rw [shadowArea_range_map K t hr L]
  exact ((OrderIso.mulLeft₀ (r ^ 2) (sq_pos_of_ne_zero hr)).map_csInf' hne hbdd).symm

lemma areaRatio_map (B K : Set E) (u t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) :
    area (transportedBase B u t r L) / shadowArea (map t r L '' K) (L u) =
      area B / shadowArea K u := by
  rw [area_transportedBase B u t hr L, shadowArea_map K t hr L u]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hr)

end CylinderCovering.Similarity

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Ruled_Similarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RuledApproximation

lemma similarityPlane_finrank (u : Space) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (AxisPlane u) = 2 := by
  have hne : u ≠ 0 := by intro hz; simp [hz] at hu
  have hd := (Submodule.span ℝ ({u} : Set Space)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace_fin] at hd
  change 1 + Module.finrank ℝ (AxisPlane u) = 3 at hd
  omega

lemma relativeCost_le_familyArea_div_minimum (K : Set Space)
    (hK : 0 < CylinderCovering.Similarity.minimumArea K)
    {n : ℕ} (C : Fin n → Cylinder) :
    (∑ i, (C i).area / CylinderCovering.Similarity.shadowArea K (C i).axis) ≤
      familyArea C / CylinderCovering.Similarity.minimumArea K := by
  unfold familyArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hK
    (CylinderCovering.Similarity.minimumArea_le_shadowArea K (C i).unit_axis)

lemma relativeCost_lt_half_of_familyArea_lt (K : Set Space)
    (hK : 0 < CylinderCovering.Similarity.minimumArea K)
    {n : ℕ} (C : Fin n → Cylinder)
    (hcost : familyArea C < CylinderCovering.Similarity.minimumArea K / 2) :
    (∑ i, (C i).area / CylinderCovering.Similarity.shadowArea K (C i).axis) < 1 / 2 := by
  apply (relativeCost_le_familyArea_div_minimum K hK C).trans_lt
  apply (div_lt_iff₀ hK).mpr
  linarith only [hcost]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma physicalDirection_norm_sq (h : ℝ) (g : Plane) :
    ‖physicalDirection h g‖ ^ 2 = 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 := by
  rw [physicalDirection, norm_vec3_sq]
  ring

lemma inner_rawProjection (h : ℝ) (g p q : Plane) :
    inner ℝ (rawProjection h g p) (rawProjection h g q) =
      inner ℝ (planeEmbedding h p) (planeEmbedding h q) -
      inner ℝ (physicalDirection h g) (planeEmbedding h p) *
        inner ℝ (physicalDirection h g) (planeEmbedding h q) /
          ‖physicalDirection h g‖ ^ 2 := by
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  simp only [rawProjection, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (planeEmbedding h p) (physicalDirection h g)]
  field_simp [(physicalDirection_norm_pos h g).ne']
  ring

lemma rawProjection_normDet_sq (h : ℝ) (g : Plane) :
    (rawProjection h g).normDet ^ 2 = h ^ 2 / ‖physicalDirection h g‖ ^ 2 := by
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  have hd := (rawProjection h g).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hd
  rw [hd, Matrix.det_fin_two]
  simp only [Matrix.gram_apply, inner_rawProjection, EuclideanSpace.basisFun_apply,
    planeEmbedding_apply, physicalDirection, inner_vec3,
    PiLp.single_apply, Fin.isValue, ↓reduceIte, mul_zero, mul_one,
    one_mul, zero_add]
  simp only [Fin.reduceEq, ↓reduceIte]
  rw [show ‖vec3 1 (g 0) (h * g 1)‖ ^ 2 = 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 by
    rw [norm_vec3_sq]; ring]
  have hden : 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

lemma rawProjection_normDet {h : ℝ} (hh : 0 < h) (g : Plane) :
    (rawProjection h g).normDet = h / ‖physicalDirection h g‖ := by
  have hn := physicalDirection_norm_pos h g
  have hs : ((rawProjection h g).normDet * ‖physicalDirection h g‖) ^ 2 = h ^ 2 := by
    rw [mul_pow, rawProjection_normDet_sq, div_mul_cancel₀ _ (pow_ne_zero 2 hn.ne')]
  have hnon := mul_nonneg (rawProjection h g).normDet_nonneg hn.le
  apply (eq_div_iff hn.ne').mpr
  nlinarith

lemma physicalWeight_eq_inv_norm (h : ℝ) (g : Plane) :
    physicalWeight h g = 1 / ‖physicalDirection h g‖ := by
  rw [physicalWeight, ← physicalDirection_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]

lemma perpendicularProjection_normDet {h : ℝ} (hh : 0 < h) (g : Plane) :
    (perpendicularProjection h g).normDet = h * physicalWeight h g := by
  rw [perpendicularProjection, LinearMap.normDet_codRestrict, rawProjection_normDet hh,
    physicalWeight_eq_inv_norm]
  ring

lemma perpendicularPlane_finrank (u : Space) (hu : ‖u‖ = 1) :
    Module.finrank ℝ ((Submodule.span ℝ ({u} : Set Space))ᗮ) = 2 := by
  have hne : u ≠ 0 := by intro hz; simp [hz] at hu
  have hd := (Submodule.span ℝ ({u} : Set Space)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace_fin] at hd
  omega

lemma perpendicularProjection_volume {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    volume.real (perpendicularProjection h g '' P) =
      h * physicalWeight h g * volume.real P := by
  have hf := (perpendicularProjection h g).euclideanHausdorffMeasure_image_eq_normDet_mul_volume P
  have hm : (MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ Plane) : Measure ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ)) = volume := by
    convert InnerProductSpace.euclideanHausdorffMeasure_eq_volume using 1
    all_goals try with_reducible_and_instances rfl
    simp only [finrank_euclideanSpace_fin, perpendicularPlane_finrank _ (physicalUnit_norm h g)]
  rw [hm] at hf
  rw [measureReal_def, hf, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (perpendicularProjection h g).normDet_nonneg,
    perpendicularProjection_normDet hh]
  rfl

lemma perpendicularProjection_injective {h : ℝ} (hh : 0 < h) (g : Plane) :
    Function.Injective (perpendicularProjection h g) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hn
  have hz := LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hn
  rw [perpendicularProjection_normDet hh, physicalWeight_eq_inv_norm] at hz
  have hp : 0 < h * (1 / ‖physicalDirection h g‖) :=
    mul_pos hh (one_div_pos.mpr (physicalDirection_norm_pos h g))
  exact hp.ne' hz

lemma IsParallelogram.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsParallelogram P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsParallelogram (f '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨f c, f u, f v, ?_, ?_⟩
  · have hli' := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
    have heq : (f ∘ ![u, v]) = ![f u, f v] := by
      funext i
      fin_cases i <;> rfl
    rwa [heq] at hli'
  · ext x
    constructor
    · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, by simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨c + a • u + b • v, ⟨a, ha, b, hb, rfl⟩, by simp⟩

lemma projectedCylinder_area {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).area = h * volume.real P * physicalWeight h g := by
  rw [Cylinder.area, projectedCylinder, perpendicularProjection_volume hh]
  ring

lemma projectedCylinder_parallelogram {h : ℝ} (hh : 0 < h) (g : Plane)
    {P : Set Plane} (hP : IsParallelogram P) :
    (projectedCylinder h g P).parallelogram :=
  hP.linear_image _ (perpendicularProjection_injective hh g)

lemma projectedCylinder_mem_iff (h : ℝ) (g : Plane) (P : Set Plane) (x : Space) :
    x ∈ (projectedCylinder h g P).carrier ↔
      ∃ p ∈ P, ∃ s : ℝ, x = planeEmbedding h p + s • physicalDirection h g := by
  have hid (p : Plane) (t : ℝ) :
      (perpendicularProjection h g p : Space) + t • physicalUnit h g =
        planeEmbedding h p +
          (t / ‖physicalDirection h g‖ -
            inner ℝ (physicalDirection h g) (planeEmbedding h p) /
              ‖physicalDirection h g‖ ^ 2) • physicalDirection h g := by
    change (planeEmbedding h p -
      (inner ℝ (physicalDirection h g) (planeEmbedding h p) /
        ‖physicalDirection h g‖ ^ 2) • physicalDirection h g) +
      t • (‖physicalDirection h g‖⁻¹ • physicalDirection h g) = _
    simp only [div_eq_mul_inv, smul_smul]
    module
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, t, rfl⟩
    exact ⟨p, hp, _, hid p t⟩
  · rintro ⟨p, hp, s, rfl⟩
    refine ⟨perpendicularProjection h g p, ⟨p, hp, rfl⟩,
      (s + inner ℝ (physicalDirection h g) (planeEmbedding h p) /
        ‖physicalDirection h g‖ ^ 2) * ‖physicalDirection h g‖, ?_⟩
    change planeEmbedding h p + s • physicalDirection h g =
      (perpendicularProjection h g p : Space) + _ • physicalUnit h g
    rw [hid, mul_div_cancel_right₀ _ (physicalDirection_norm_pos h g).ne', add_sub_cancel_right]

lemma projectedCylinder_carrier (h : ℝ) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).carrier = firstPhysicalMap h '' auxiliaryCylinder P g := by
  ext x
  rw [projectedCylinder_mem_iff]
  constructor
  · rintro ⟨p, hp, s, rfl⟩
    refine ⟨axial s (p + s • g), ⟨s, p, hp, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, vec3, planeEmbedding, physicalDirection,
      mul_add, mul_left_comm]
  · rintro ⟨_, ⟨s, p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, s, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, vec3, planeEmbedding, physicalDirection,
      mul_add, mul_left_comm]

lemma physicalRuled_mem_projectedCylinder (h : ℝ) (v : Plane → Plane)
    (p g : Plane) (s : ℝ) {P : Set Plane} (hp : p + s • (v p - g) ∈ P) :
    vec3 s (p 0 + s * v p 0) (h * (p 1 + s * v p 1)) ∈
      (projectedCylinder h g P).carrier := by
  rw [projectedCylinder_mem_iff]
  refine ⟨p + s • (v p - g), hp, s, ?_⟩
  ext i
  fin_cases i <;> simp [planeEmbedding, physicalDirection, vec3] <;> ring

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma frameJacobian_pos (M : Coordinates ≃L[ℝ] Plane) : 0 < frameJacobian M := by
  apply abs_pos.mpr
  exact (M.trans (EuclideanSpace.equiv (Fin 2) ℝ)).toLinearEquiv.isUnit_det'.ne_zero

lemma frame_integral_image (M : Coordinates ≃L[ℝ] Plane) {K : Set Coordinates}
    (hK : MeasurableSet K) (F : Plane → ℝ) :
    (∫ p in M '' K, F p) = frameJacobian M * (∫ x in K, F (M x)) := by
  let e := EuclideanSpace.equiv (Fin 2) ℝ
  let D := M.trans e
  have himage : M '' K = e.symm '' (D '' K) := by
    rw [← image_comp]
    congr 1

  rw [himage]
  have hmp : MeasurePreserving e.symm volume volume := PiLp.volume_preserving_toLp (Fin 2)
  rw [hmp.setIntegral_image_emb e.symm.toHomeomorph.measurableEmbedding]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hK
    (fun x _ => D.hasFDerivAt.hasFDerivWithinAt) D.injective.injOn]
  rw [integral_smul]
  rfl

lemma frame_volume_image (M : Coordinates ≃L[ℝ] Plane) {K : Set Coordinates}
    (hK : MeasurableSet K) : volume.real (M '' K) = frameJacobian M * volume.real K := by
  simpa using frame_integral_image M hK (fun _ => (1 : ℝ))

lemma coordinates_closedBall (b : Coordinates) {a : ℝ} (ha : 0 ≤ a) :
    closedBall b a = Set.pi univ (fun i => Icc (b i - a) (b i + a)) := by
  ext x
  simp only [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha, Real.norm_eq_abs,
    Pi.sub_apply, Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]
  constructor <;> intro h i <;> obtain ⟨h₁, h₂⟩ := h i <;> constructor <;> linarith

lemma coordinates_closedBall_volume (b : Coordinates) {a : ℝ} (ha : 0 ≤ a) :
    volume.real (closedBall b a) = (2 * a) ^ 2 := by
  rw [coordinates_closedBall b ha, measureReal_def, volume_pi_pi]
  simp only [Real.volume_Icc, add_sub_sub_cancel, Fin.prod_univ_two]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ a + a)]
  ring

lemma coordinates_closedBall_parallelogram (b : Coordinates) {a : ℝ} (ha : 0 < a) :
    IsParallelogram (closedBall b a) := by
  let u : Coordinates := ![2*a, 0]
  let v : Coordinates := ![0, 2*a]
  refine ⟨![b 0 - a, b 1 - a], u, v, ?_, ?_⟩
  · have heq : (![u, v] : Fin 2 → Coordinates) =
        fun i => (2 * a) • Pi.basisFun ℝ (Fin 2) i := by
      funext i
      ext j
      fin_cases i <;> fin_cases j <;> simp [u, v, Pi.basisFun_apply]
    rw [heq]
    exact (Pi.basisFun ℝ (Fin 2)).linearIndependent.units_smul
      (fun _ => Units.mk0 (2 * a) (by positivity))
  · rw [coordinates_closedBall b ha.le]
    ext x
    simp only [Set.mem_pi, mem_univ, true_implies, mem_Icc, Set.mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨(x 0 - (b 0 - a)) / (2*a), ?_, (x 1 - (b 1 - a)) / (2*a), ?_, ?_⟩
      · constructor
        · exact div_nonneg (sub_nonneg.mpr (hx 0).1) (by positivity)
        · apply (div_le_one (by positivity)).mpr
          linarith [(hx 0).2]
      · constructor
        · exact div_nonneg (sub_nonneg.mpr (hx 1).1) (by positivity)
        · apply (div_le_one (by positivity)).mpr
          linarith [(hx 1).2]
      · ext i
        fin_cases i <;> simp [u, v, (by positivity : 2*a ≠ 0)]
    · rintro ⟨s, hs, t, ht, rfl⟩ i
      fin_cases i <;> simp [u, v] <;> constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Lattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma nearestInteger_mono : Monotone nearestInteger := by
  intro a b hab
  exact Int.floor_mono (by linarith)

lemma nearestInteger_error (t : ℝ) : |(nearestInteger t : ℝ) - t| ≤ 1 / 2 := by
  have h₁ := Int.floor_le (t + 1 / 2)
  have h₂ := Int.lt_floor_add_one (t + 1 / 2)
  unfold nearestInteger
  rw [abs_le]
  constructor <;> linarith

/-- An integer version of the monotone fixed-point argument. The bounded drift
with slope strictly less than one supplies both end barriers. -/
lemma integer_fixed_point_of_bounded_drift (F : ℤ → ℤ) (hF : Monotone F)
    (q B : ℝ) (hq : q < 1) (hB : ∀ i : ℤ, |(F i : ℝ) - q * i| ≤ B) :
    ∃ i : ℤ, F i = i := by
  have hq' : 0 < 1 - q := sub_pos.mpr hq
  obtain ⟨lo, hlo⟩ := exists_int_le (-B / (1 - q))
  obtain ⟨hi, hhi⟩ := exists_int_ge (B / (1 - q))
  have hbound : ∀ i : ℤ, F i ≤ i → lo ≤ i := by
    intro i hi
    have hb := (abs_le.mp (hB i)).1
    have hi' : (F i : ℝ) ≤ i := by exact_mod_cast hi
    have hreal : -B / (1 - q) ≤ (i : ℝ) := by
      apply (div_le_iff₀ hq').2
      nlinarith
    exact_mod_cast hlo.trans hreal
  have hhi' : F hi ≤ hi := by
    have hb := (abs_le.mp (hB hi)).2
    have ht := (div_le_iff₀ hq').1 hhi
    have : (F hi : ℝ) ≤ hi := by nlinarith
    exact_mod_cast this
  obtain ⟨i, hi, hmin⟩ := Int.exists_least_of_bdd ⟨lo, hbound⟩ ⟨hi, hhi'⟩
  exact ⟨i, le_antisymm hi (hmin (F i) (hF hi))⟩

/-- A useful strengthening of the lattice estimates: only the product
conditions are needed; either off-diagonal entry may be arbitrarily large. -/
theorem asymmetric_lattice_cover (alpha beta : ℝ)
    (hprod : 0 ≤ alpha * beta) (hprod' : alpha * beta < 1) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + alpha * j)| ≤ 1 / 2 ∧
      |u₂ - (beta * i + (j : ℝ))| ≤ 1 / 2 := by
  let F : ℤ → ℤ := fun i => nearestInteger
    (u₁ - alpha * (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ))
  have hmono : Monotone F := by
    intro i j hij
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    rcases mul_nonneg_iff.mp hprod with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hinner : nearestInteger (u₂ - beta * (j : ℝ)) ≤
          nearestInteger (u₂ - beta * (i : ℝ)) :=
        nearestInteger_mono (by nlinarith)
      have hinner' : (nearestInteger (u₂ - beta * (j : ℝ)) : ℝ) ≤
          (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ) := by exact_mod_cast hinner
      exact nearestInteger_mono (by nlinarith)
    · have hinner : nearestInteger (u₂ - beta * (i : ℝ)) ≤
          nearestInteger (u₂ - beta * (j : ℝ)) :=
        nearestInteger_mono (by nlinarith)
      have hinner' : (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ) ≤
          (nearestInteger (u₂ - beta * (j : ℝ)) : ℝ) := by exact_mod_cast hinner
      exact nearestInteger_mono (by nlinarith)
  have hdrift : ∀ i : ℤ,
      |(F i : ℝ) - (alpha * beta) * i| ≤
        1 / 2 + |alpha| * (1 / 2) + |u₁ - alpha * u₂| := by
    intro i
    let j := nearestInteger (u₂ - beta * (i : ℝ))
    have h₁ := nearestInteger_error (u₁ - alpha * (j : ℝ))
    have h₂ := nearestInteger_error (u₂ - beta * (i : ℝ))
    have hdecomp : (F i : ℝ) - (alpha * beta) * i =
        ((F i : ℝ) - (u₁ - alpha * j)) -
        alpha * ((j : ℝ) - (u₂ - beta * i)) + (u₁ - alpha * u₂) := by ring
    rw [hdecomp]
    calc
      _ ≤ |(F i : ℝ) - (u₁ - alpha * j)| +
          |alpha * ((j : ℝ) - (u₂ - beta * i))| + |u₁ - alpha * u₂| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 1 / 2 + |alpha| * (1 / 2) + |u₁ - alpha * u₂| := by
        rw [abs_mul]
        exact add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (abs_nonneg _))) le_rfl
  obtain ⟨i, hi⟩ := integer_fixed_point_of_bounded_drift F hmono
    (alpha * beta) _ hprod' hdrift
  let j := nearestInteger (u₂ - beta * (i : ℝ))
  refine ⟨i, j, ?_, ?_⟩
  · have h := nearestInteger_error (u₁ - alpha * (j : ℝ))
    change |(F i : ℝ) - (u₁ - alpha * (j : ℝ))| ≤ 1 / 2 at h
    rw [hi] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [← abs_neg]
    congr 1
    ring
  · have h := nearestInteger_error (u₂ - beta * (i : ℝ))
    change |(j : ℝ) - (u₂ - beta * (i : ℝ))| ≤ 1 / 2 at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [← abs_neg]
    congr 1
    ring

/-- Sliding rows have no shear bound. This is the local nilpotent model. -/
theorem sliding_rows_cover (d : ℝ) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + d * j)| ≤ 1 / 2 ∧
      |u₂ - (j : ℝ)| ≤ 1 / 2 := by
  simpa using asymmetric_lattice_cover d 0 (by simp) (by simp) u₁ u₂

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_OuterApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Closed outer neighborhoods recover a closed set even when its frontier has positive measure. -/
lemma inter_reciprocal_cthickening {E : Type*} [MetricSpace E] (K : Set E)
    (hK : IsClosed K) :
    (⋂ n : ℕ, cthickening (1 / ((n : ℝ) + 1)) K) = K := by
  apply Subset.antisymm
  · intro x hx
    have hxn : ∀ n : ℕ, infEDist x K ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      simpa only [mem_iInter, mem_cthickening_iff] using hx
    have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hz : infEDist x K = 0 := le_antisymm (ge_of_tendsto ht (.of_forall hxn)) bot_le
    exact hK.closure_subset (mem_closure_iff_infEDist_zero.mpr hz)
  · exact subset_iInter fun _ => self_subset_cthickening K

/-- Small open outer neighborhoods, not regularity of the label boundary, justify the weighted
lattice count for arbitrary compact label sets. -/
theorem exists_nice_outer_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [SFinite (volume : Measure E)]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : E → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ S : Set E, IsOpen S ∧ Bornology.IsBounded S ∧ K ⊆ S ∧ S ⊆ U ∧
      volume (frontier S) = 0 ∧ (∫ x in S, F x) < (∫ x in K, F x) + eps := by
  let R : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hR : ∀ n, 0 < R n := fun n => by dsimp [R]; positivity
  have hRlim : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let K' : ℕ → Set E := fun n => cthickening (R n) K
  have hK' : ∀ n, IsCompact (K' n) := fun _ => hK.cthickening
  have hanti : Antitone K' := by
    intro n m hnm
    apply cthickening_mono _ K
    dsimp [R]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hInt : Tendsto (fun n => ∫ x in K' n, F x) atTop (𝓝 (∫ x in K, F x)) := by
    have ht := tendsto_setIntegral_of_antitone (μ := volume)
      (fun n => (hK' n).measurableSet) hanti
      ⟨0, hF.continuousOn.integrableOn_compact (μ := volume) (hK' 0)⟩
    rwa [show (⋂ n, K' n) = K from inter_reciprocal_cthickening K hK.isClosed] at ht
  obtain ⟨d, hd, hdU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hevent : ∀ᶠ n in atTop, (∫ x in K' n, F x) < (∫ x in K, F x) + eps ∧ R n < d :=
    (hInt.eventually (Iio_mem_nhds (lt_add_of_pos_right _ heps))).and
      (hRlim.eventually (Iio_mem_nhds hd))
  obtain ⟨n, hnInt, hnd⟩ := hevent.exists
  obtain ⟨r, hr, hrnull⟩ := exists_null_frontier_thickening volume K (hR n)
  refine ⟨thickening r K, isOpen_thickening, hK.isBounded.thickening,
    self_subset_thickening hr.1 K, ?_, hrnull, ?_⟩
  · exact (thickening_subset_cthickening r K).trans
      ((cthickening_mono (hr.2.le.trans hnd.le) K).trans hdU)
  · have hsub : thickening r K ⊆ K' n :=
      (thickening_subset_cthickening r K).trans (cthickening_mono hr.2.le K)
    exact (setIntegral_mono_set
      (hF.continuousOn.integrableOn_compact (μ := volume) (hK' n))
      (.of_forall hFpos) (.of_forall hsub)).trans_lt hnInt

lemma finite_inter_coordinateGrid {S : Set (Fin 2 → ℝ)} (hS : Bornology.IsBounded S)
    {n : ℕ} (hn : n ≠ 0) : (S ∩ coordinateGrid n).Finite := by
  classical
  unfold coordinateGrid
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (Nat.cast_ne_zero.mpr hn))]
  exact ZSpan.setFinite_inter _ hS

/-- A finite lattice retained around any compact label set has arbitrarily accurate weighted
cost. The finite set is the intersection with a fixed regular outer neighborhood, so no
assumption on the boundary or positive area of `K` occurs here. -/
theorem finite_weighted_grid_outer {K U : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : (Fin 2 → ℝ) → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    (R : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ S : Set (Fin 2 → ℝ), S.Finite ∧
      S ⊆ U ∩ coordinateGrid n ∧
      (∀ b ∈ coordinateGrid n, (∃ p ∈ K, dist b p ≤ R / n) → b ∈ S) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by
  obtain ⟨O, hOo, hOb, hKO, hOU, hOf, hOI⟩ :=
    exists_nice_outer_integral hK hU hKU hF hFpos (half_pos heps)
  obtain ⟨d, hd, hdO⟩ := hK.exists_cthickening_subset_open hOo hKO
  have hsum := tendsto_tsum_div_pow_atTop_integral O F hF hOb hOo.measurableSet hOf
  have hcost : ∀ᶠ n : ℕ in atTop,
      (∑' b : ↑(O ∩ coordinateGrid n), F b) / (n : ℝ) ^ 2 <
        (∫ p in O, F p) + eps / 2 := by
    simpa only [coordinateGrid, Fintype.card_fin] using
      hsum.eventually (Iio_mem_nhds (lt_add_of_pos_right _ (half_pos heps)))
  have hsmall : ∀ᶠ n : ℕ in atTop, R / (n : ℝ) < d := by
    have ht : Tendsto (fun n : ℕ => R / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun n : ℕ => R * (n : ℝ)⁻¹) atTop (𝓝 (R * 0)))
    exact ht.eventually (Iio_mem_nhds hd)
  filter_upwards [eventually_gt_atTop 0, hcost, hsmall] with n hn hcost hnsmall
  refine ⟨hn, O ∩ coordinateGrid n, finite_inter_coordinateGrid hOb hn.ne',
    Set.inter_subset_inter_left _ hOU, ?_, ?_⟩
  · intro b hb ⟨p, hp, hbp⟩
    exact ⟨hdO ((thickening_subset_cthickening d K)
      (mem_thickening_iff.mpr ⟨p, hp, hbp.trans_lt hnsmall⟩)), hb⟩
  · linarith

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_LocalApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A quantitative derivative remainder in convex local coordinates. -/
theorem c1_local_remainder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : E → F} {U : Set E} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : E} (hp : p ∈ U) {delta : ℝ} (hd : 0 < delta) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      ‖v x - v y - fderiv ℝ v p (x - y)‖ ≤ delta * ‖x - y‖ := by
  have hdc : ContinuousAt (fderiv ℝ v) p :=
    (hv.contDiffAt (hU.mem_nhds hp)).continuousAt_fderiv (by norm_num)
  have hevent : ∀ᶠ x in 𝓝 p, ‖fderiv ℝ v x - fderiv ℝ v p‖ < delta := by
    simpa only [dist_eq_norm] using hdc.eventually (ball_mem_nhds _ hd)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hevent (hU.mem_nhds hp))
  have hsub : ball p r ⊆ U := fun x hx => (hrsub hx).2
  refine ⟨r, hr, hsub, ?_⟩
  intro x hx y hy
  apply (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le' (φ := fderiv ℝ v p)
    (fun z hz => ((hv.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => (hrsub hz).1.le) hy hx

/-- Extending a nonnegative continuous weight from a compact patch does not alter it there. -/
theorem continuous_nonneg_extension {E : Type*} [TopologicalSpace E] [NormalSpace E]
    {K : Set E} (hK : IsClosed K) {f : E → ℝ} (hf : ContinuousOn f K)
    (hn : ∀ x ∈ K, 0 ≤ f x) :
    ∃ F : E → ℝ, Continuous F ∧ (∀ x, 0 ≤ F x) ∧ Set.EqOn F f K := by
  let fc : C(K, ℝ) := ⟨_, continuousOn_iff_continuous_domRestrict.mp hf⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK fc
  refine ⟨fun x => max (g x) 0, g.continuous.max continuous_const, fun x => le_max_right _ _, ?_⟩
  intro x hx
  have hgx : g x = f x := congrArg (fun q : C(K, ℝ) => q ⟨x, hx⟩) hg
  dsimp only
  rw [hgx, max_eq_left (hn x hx)]


/-- The nonlinear local producer. Unlike tilting a continuum of lines, it produces a
finite set of intercept centers covering every label and every time simultaneously. -/
theorem local_finite_certificate {K U : Set Parameter} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (v : Parameter → Parameter)
    (A : Parameter →L[ℝ] Parameter) {L R delta : ℝ}
    (hL : 0 ≤ L) (hdelta : 0 ≤ delta) (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖v p - v b - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Parameter → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : Set Parameter, S.Finite ∧ S ⊆ U ∧
      (∀ p ∈ K, ∀ r : ℝ, |r| ≤ L → ∃ b ∈ S,
        ‖p + r • v p - (b + r • v b)‖ ≤ (1 / 2 + L * delta * R) / n) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by
  obtain ⟨n, hn, S, hSfinite, hSU, hretain, hcost⟩ :=
    (finite_weighted_grid_outer hK hU hKU hF hFpos R heps).exists
  refine ⟨n, hn, S, hSfinite, fun b hb => (hSU hb).1, ?_, hcost⟩
  intro p hp r hr
  obtain ⟨b, hbgrid, hbp, hlin⟩ := hmodel n hn p r hr
  have hbS := hretain b hbgrid ⟨p, hp, hbp⟩
  have hbp' : ‖p - b‖ ≤ R / n := by simpa [dist_eq_norm, norm_sub_rev] using hbp
  have herr := hrem p (hKU hp) b (hSU hbS).1
  refine ⟨b, hbS, ?_⟩
  calc
    ‖p + r • v p - (b + r • v b)‖ =
        ‖(p - b + r • A (p - b)) + r • (v p - v b - A (p - b))‖ := by
          congr 1
          module
    _ ≤ ‖p - b + r • A (p - b)‖ + ‖r • (v p - v b - A (p - b))‖ := norm_add_le _ _
    _ ≤ 1 / (2 * n) + L * (delta * (R / n)) := by
      apply add_le_add hlin
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (herr.trans (mul_le_mul_of_nonneg_left hbp' hdelta)) hL)
    _ = (1 / 2 + L * delta * R) / n := by ring

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_HyperbolicLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma norm_le_of_scaled_coordinates {n C : ℝ} (hn : 0 < n) (hC : 0 ≤ C)
    (x : Parameter) (hx : ∀ i, |n * x i| ≤ C) : ‖x‖ ≤ C / n := by
  rw [pi_norm_le_iff_of_nonneg (div_nonneg hC hn.le)]
  intro i
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ hn).2
  have := hx i
  rwa [abs_mul, abs_of_pos hn, mul_comm] at this

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_LocalCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma HasFiniteCover.of_fintype {ι : Type*} [Fintype ι] {shape : Cylinder → Prop}
    {S : Set Space} {A : ℝ} (C : ι → Cylinder) (hshape : ∀ i, shape (C i))
    (hcover : S ⊆ ⋃ i, (C i).carrier) (hcost : (∑ i, (C i).area) ≤ A) :
    HasFiniteCover shape S A := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, C ∘ e.symm, fun i => hshape _, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨e i, by simpa using hi⟩
  · change (∑ i : Fin (Fintype.card ι), (C (e.symm i)).area) ≤ A
    rw [e.symm.sum_comp (fun j => (C j).area)]
    exact hcost

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_HyperbolicCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma HasFiniteCover.mono {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (h : HasFiniteCover shape T A) (hST : S ⊆ T) (hAB : A ≤ B) :
    HasFiniteCover shape S B := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := h
  exact ⟨n, C, hC, hST.trans hcov, hcost.trans hAB⟩

lemma HasFiniteCover.empty (shape : Cylinder → Prop) {A : ℝ} (hA : 0 ≤ A) :
    HasFiniteCover shape ∅ A := by
  refine ⟨0, Fin.elim0, by intro i; exact i.elim0, by simp, ?_⟩
  simpa [familyArea] using hA

lemma HasFiniteCover.union {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (hS : HasFiniteCover shape S A) (hT : HasFiniteCover shape T B) :
    HasFiniteCover shape (S ∪ T) (A + B) := by
  obtain ⟨n, C, hC, hSC, hcostC⟩ := hS
  obtain ⟨m, D, hD, hTD, hcostD⟩ := hT
  refine ⟨n + m, Fin.addCases C D, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hC j
    · simpa using hD j
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hSC hx)
      exact mem_iUnion.mpr ⟨i.castAdd m, by simpa using hi⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hTD hx)
      exact mem_iUnion.mpr ⟨j.natAdd n, by simpa using hj⟩
  · simpa [familyArea, Fin.sum_univ_add] using add_le_add hcostC hcostD

lemma physicalRuled_union (h L : ℝ) (v : Plane → Plane) (S T : Set Plane) :
    physicalRuled h (S ∪ T) v L = physicalRuled h S v L ∪ physicalRuled h T v L := by
  ext z
  simp only [physicalRuled, mem_ofPred_eq, mem_union]
  aesop

lemma physicalRuled_empty (h L : ℝ) (v : Plane → Plane) : physicalRuled h ∅ v L = ∅ := by
  simp [physicalRuled]

/-- Compact pieces cut along a null frontier have exactly additive cost, even when
 the original compact set itself has a positive-area frontier. -/
lemma compact_cut_integral {K O : Set Plane} (hK : IsCompact K) (hO : IsOpen O)
    (hnull : volume (frontier O) = 0) {F : Plane → ℝ} (hF : IntegrableOn F K) :
    IsCompact (K ∩ closure O) ∧ IsCompact (K \ O) ∧
    K = (K ∩ closure O) ∪ (K \ O) ∧
    (∫ x in K, F x) = (∫ x in K ∩ closure O, F x) + (∫ x in K \ O, F x) := by
  have h₁ : IsCompact (K ∩ closure O) := hK.inter_right isClosed_closure
  have h₂ := hK.diff hO
  have hun : K = (K ∩ closure O) ∪ (K \ O) := by
    ext x
    simp only [mem_union, mem_inter_iff, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases hxO : x ∈ O
      · exact Or.inl ⟨hx, subset_closure hxO⟩
      · exact Or.inr ⟨hx, hxO⟩
    · tauto
  refine ⟨h₁, h₂, hun, ?_⟩
  nth_rw 1 [hun]
  apply setIntegral_union₀
  · show volume ((K ∩ closure O) ∩ (K \ O)) = 0
    apply measure_mono_null _ hnull
    intro x hx
    rw [frontier, hO.interior_eq]
    exact ⟨hx.1.2, hx.2.2⟩
  · exact h₂.measurableSet.nullMeasurableSet
  · exact hF.mono_set inter_subset_left
  · exact hF.mono_set sdiff_subset

/-- Finite gluing over regular open patches. Only the patch frontiers must be null;
 there is deliberately no restriction on the label set's own frontier. -/
theorem glue_finite_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) {A : ℝ}
    {ι : Type*} (s : Finset ι) (O U : ι → Set Plane)
    (hO : ∀ i ∈ s, IsOpen (O i)) (hOU : ∀ i ∈ s, closure (O i) ⊆ U i)
    (hnull : ∀ i ∈ s, volume (frontier (O i)) = 0)
    (hlocal : ∀ i ∈ s, ∀ Q : Set Plane, IsCompact Q → Q ⊆ U i →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover shape (physicalRuled h Q v L)
        (A * (∫ p in Q, F p) + eps))
    {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hcover : K ⊆ ⋃ i ∈ s, O i) {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ p in K, F p) + eps) := by
  classical
  induction s using Finset.induction_on generalizing K eps with
  | empty =>
    have hKe : K = ∅ := by simpa using hcover
    rw [hKe, physicalRuled_empty]
    simpa using HasFiniteCover.empty shape heps.le
  | @insert i s hi ih =>
    have hOi := hO i (by simp)
    obtain ⟨h₁, h₂, hun, hint⟩ := compact_cut_integral hK hOi (hnull i (by simp)) hF
    have hc₁ := hlocal i (by simp) _ h₁
      (inter_subset_right.trans (hOU i (by simp))) (eps / 2) (half_pos heps)
    have hsub : K \ O i ⊆ ⋃ j ∈ s, O j := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcover hx.1)
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact False.elim (hx.2 hxj)
      · exact mem_iUnion₂.mpr ⟨j, hj, hxj⟩
    have hc₂ := ih (fun j hj => hO j (by simp [hj]))
      (fun j hj => hOU j (by simp [hj])) (fun j hj => hnull j (by simp [hj]))
      (fun j hj => hlocal j (by simp [hj])) h₂ (hF.mono_set sdiff_subset)
      hsub (half_pos heps)
    have hc := hc₁.union hc₂
    rw [← physicalRuled_union, ← hun] at hc
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    rw [hint]
    ring

lemma physicalWeight_pos (h : ℝ) (g : Plane) : 0 < physicalWeight h g := by
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

lemma physicalWeight_continuous (h : ℝ) : Continuous (physicalWeight h) := by
  apply continuous_const.div
  · apply Real.continuous_sqrt.comp
    fun_prop
  · intro g
    exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2)).ne'

lemma exists_small_inflation (L R : ℝ) {B : ℝ} (hB : 1 < B) :
    ∃ delta : ℝ, 0 < delta ∧ (1 + 2 * L * delta * R) ^ 2 < B := by
  have hc : Continuous (fun d : ℝ => (1 + 2 * L * d * R) ^ 2) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1 + 2 * L * d * R) ^ 2 < B :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using hB))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r / 2, half_pos hr, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

/-- Compactness and null-frontier patches globalize the finite local producer. -/
theorem globalize_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) (A : ℝ) {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hpatch : ∀ p ∈ K, ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧
      ∀ Q : Set Plane, IsCompact Q → Q ⊆ V → ∀ eps : ℝ, 0 < eps →
      HasFiniteCover shape (physicalRuled h Q v L) (A * (∫ q in Q, F q) + eps))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ q in K, F q) + eps) := by
  classical
  choose V hVo hpV hloc using fun p : K => hpatch p p.property
  choose r hr hrV using fun p : K => Metric.mem_nhds_iff.mp ((hVo p).mem_nhds (hpV p))
  let O : K → Set Plane := fun p => ball (p : Plane) (r p / 2)
  have hOo : ∀ p : K, IsOpen (O p) := fun _ => isOpen_ball
  have hcover : K ⊆ ⋃ p : K, O p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (half_pos (hr ⟨p, hp⟩))⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hOo hcover
  apply glue_finite_local_covers h L v F s O V (fun p _ => hOo p) _ _
    (fun p _ => hloc p) hK hF hs heps
  · intro p _
    rw [show O p = ball (p : Plane) (r p / 2) from rfl,
      closure_ball (p : Plane) (half_pos (hr p)).ne']
    exact (closedBall_subset_ball (by linarith [hr p])).trans (hrV p)
  · intro p _
    apply measure_mono_null frontier_ball_subset_sphere
    exact MeasureTheory.Measure.addHaar_sphere volume (p : Plane) (r p / 2)

lemma exists_inflation_budget (C : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 < B ∧ B * C < C + eps := by
  have hc : Continuous (fun d : ℝ => (1+d)*C) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1+d)*C < C + eps :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using lt_add_of_pos_right C heps))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1+r/2, by linarith, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Isometries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsParallelogram.translate {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} (hP : IsParallelogram P) (a : E) :
    IsParallelogram ((fun x => a + x) '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨a+c, u, v, hli, ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    exact ⟨s, hs, t, ht, by abel_nf⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨c+s•u+t•v, ⟨s, hs, t, ht, rfl⟩, by abel_nf⟩

lemma Cylinder.rotate_carrier (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) :
    (C.rotate R).carrier = R '' C.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, t, rfl⟩
    exact ⟨(b : Space) + t • C.axis, ⟨b, hb, t, rfl⟩, by change R ((b : Space) + t • C.axis) = R b + t • R C.axis; simp⟩
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, rfl⟩
    exact ⟨rotatedPlane C.axis R b, ⟨b, hb, rfl⟩, t, by change R ((b : Space) + t • C.axis) = R b + t • R C.axis; simp⟩

lemma Cylinder.rotate_area (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) :
    (C.rotate R).area = C.area := by
  change volume.real (rotatedPlane C.axis R '' C.base) = volume.real C.base
  have he := (rotatedPlane C.axis R).measurePreserving.setIntegral_image_emb
    (rotatedPlane C.axis R).toHomeomorph.measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

lemma Cylinder.rotate_parallelogram {C : Cylinder} (hC : C.parallelogram)
    (R : Space ≃ₗᵢ[ℝ] Space) : (C.rotate R).parallelogram :=
  hC.linear_image (rotatedPlane C.axis R).toLinearMap (rotatedPlane C.axis R).injective

lemma Cylinder.translate_carrier (C : Cylinder) (q : Space) :
    (C.translate q).carrier = (fun x => q + x) '' C.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, t, rfl⟩
    refine ⟨(b : Space) + (t - inner ℝ C.axis q) • C.axis,
      ⟨b, hb, _, rfl⟩, ?_⟩
    change q + ((b : Space) + (t - inner ℝ C.axis q) • C.axis) =
      (q - (inner ℝ C.axis q) • C.axis + b) + t • C.axis
    module
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, rfl⟩
    refine ⟨C.transversePart q + b, ⟨b, hb, rfl⟩, t + inner ℝ C.axis q, ?_⟩
    change q + ((b : Space) + t • C.axis) =
      (q - (inner ℝ C.axis q) • C.axis + b) + (t + inner ℝ C.axis q) • C.axis
    module

lemma Cylinder.translate_area (C : Cylinder) (q : Space) :
    (C.translate q).area = C.area := by
  change volume.real ((fun b => C.transversePart q + b) '' C.base) = volume.real C.base
  have he := (measurePreserving_add_left volume (C.transversePart q)).setIntegral_image_emb
    (Homeomorph.addLeft (C.transversePart q)).measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

lemma Cylinder.translate_parallelogram {C : Cylinder} (hC : C.parallelogram) (q : Space) :
    (C.translate q).parallelogram := hC.translate (C.transversePart q)

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_NilpotentLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A square-zero planar operator has an orthonormal shear frame, with no bound
on the shear coefficient. -/
lemma nilpotent_frame (A : Plane →L[ℝ] Plane) (hA : A.comp A = 0) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ d : ℝ, ∀ z : Plane,
      R.symm (A (R z)) = vec2 (d * z 1) 0 := by
  classical
  have hAA (x : Plane) : A (A x) = 0 := by
    have hh := congrArg (fun T : Plane →L[ℝ] Plane => T x) hA
    exact hh
  have hex : ∃ u : Plane, ‖u‖ = 1 ∧ A u = 0 := by
    by_cases hz : A = 0
    · refine ⟨vec2 1 0, ?_, by simp [hz]⟩
      simp [vec2, EuclideanSpace.norm_eq]
    · have hx : ∃ x : Plane, A x ≠ 0 := by
        by_contra h
        push Not at h
        apply hz
        apply ContinuousLinearMap.ext
        exact h
      obtain ⟨x, hx⟩ := hx
      refine ⟨‖A x‖⁻¹ • A x, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      · simp [hAA]
  obtain ⟨u, hu, hAu⟩ := hex
  have hon : Orthonormal ℝ (({0} : Set (Fin 2)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp i.property)
    have hj : j = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp j.property)
    subst i
    subst j
    simp [hu]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let R : Plane ≃ₗᵢ[ℝ] Plane := b.repr.symm
  have hb0 : b 0 = u := hb 0 (by simp)
  have hrepr0 : b.repr (A (b 0)) = 0 := by rw [hb0, hAu, map_zero]
  let W : Plane →ₗ[ℝ] Plane := b.repr.toLinearMap.comp (A.toLinearMap.comp b.repr.symm.toLinearMap)
  have he0 : vec2 1 0 = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [vec2]
  have hW0 : W (vec2 1 0) = 0 := by
    change b.repr (A (b.repr.symm (vec2 1 0))) = 0
    rw [he0, b.repr_symm_single]
    exact hrepr0
  have hWW (z : Plane) : W (W z) = 0 := by
    simp [W, hAA]
  have hexp (z : Plane) : z = z 0 • vec2 1 0 + z 1 • vec2 0 1 := by
    ext i
    fin_cases i <;> simp [vec2]
  have hWexp (z : Plane) : W z = z 1 • W (vec2 0 1) := by
    nth_rw 1 [hexp z]
    rw [map_add, map_smul, map_smul, hW0, smul_zero, zero_add]
  have hz11 : W (vec2 0 1) 1 = 0 := by
    have hs := congrArg (fun z : Plane => z 1) (hWW (vec2 0 1))
    rw [hWexp (W (vec2 0 1))] at hs
    change W (vec2 0 1) 1 * W (vec2 0 1) 1 = 0 at hs
    exact mul_self_eq_zero.mp hs
  refine ⟨R, W (vec2 0 1) 0, fun z => ?_⟩
  change W z = _
  rw [hWexp]
  ext i
  fin_cases i
  · change z 1 * W (vec2 0 1) 0 = W (vec2 0 1) 0 * z 1
    ring
  · change z 1 * W (vec2 0 1) 1 = 0
    rw [hz11, mul_zero]

/-- A sliding-row lattice for every real shear; the retained radius is finite
but no smallness of the derivative is imposed. -/
theorem nilpotent_lattice_model (d : ℝ) :
    LatticeModel (d • shearCLM) 1 ((1+|d|)/2) := by
  intro n hn p r hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨i,j,hi,hj⟩ := sliding_rows_cover (r*d)
    ((n:ℝ)*p 0 + r*d*((n:ℝ)*p 1)) ((n:ℝ)*p 1)
  have hrd : |r*d| ≤ |d| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right hr (abs_nonneg d)
  have hd0 : |(n:ℝ)*p 0-i| ≤ (1+|d|)/2 := by
    have heq : (n:ℝ)*p 0-i =
        ((n:ℝ)*p 0+r*d*((n:ℝ)*p 1)-(i+r*d*j))-r*d*((n:ℝ)*p 1-j) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by
      rw [abs_mul]
      have hm := mul_le_mul hrd hj (abs_nonneg _) (abs_nonneg d)
      linarith)
  let b : Coordinates := ![(i:ℝ)/n,(j:ℝ)/n]
  let : NeZero n := ⟨hn.ne'⟩
  have hb : b ∈ coordinateGrid n := by
    apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
    intro k
    fin_cases k
    · exact ⟨i, by simp [b, mul_div_cancel₀ _ hnR.ne']⟩
    · exact ⟨j, by simp [b, mul_div_cancel₀ _ hnR.ne']⟩
  refine ⟨b,hb,?_,?_⟩
  · rw [dist_eq_norm, norm_sub_rev]
    apply norm_le_of_scaled_coordinates hnR (by positivity)
    intro k
    fin_cases k
    · simpa [b, mul_sub, mul_div_cancel₀ _ hnR.ne'] using hd0
    · have hj' : |(n:ℝ)*p 1-j| ≤ (1+|d|)/2 := by linarith [abs_nonneg d]
      simpa [b, mul_sub, mul_div_cancel₀ _ hnR.ne'] using hj'
  · have hbnd : ‖p-b+r • (d • shearCLM) (p-b)‖ ≤ (1/2:ℝ)/n := by
      apply norm_le_of_scaled_coordinates hnR (by norm_num)
      intro k
      fin_cases k
      · convert hi using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        simp [b,shearCLM,shearLinear,Matrix.vecHead,Matrix.vecTail]
        field_simp
        ring
      · convert hj using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        simp [b,shearCLM,shearLinear,Matrix.vecHead,Matrix.vecTail]
        field_simp
    convert hbnd using 1
    all_goals try with_reducible_and_instances rfl
    ring

lemma orthogonal_closedBall_square (R : Plane ≃ₗᵢ[ℝ] Plane) (b : Coordinates)
    {a : ℝ} (ha : 0 < a) :
    IsSquareTile (orthogonalFrame R '' closedBall b a) := by
  let M := orthogonalFrame R
  refine ⟨M b,R,2*a,by positivity,?_⟩
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    let q : Coordinates := fun i => (x i-b i)/(2*a)
    refine ⟨WithLp.toLp 2 q, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha.le] at hx
      intro i
      change |(x i-b i)/(2*a)| ≤ 1/2
      rw [abs_div, abs_of_pos (by positivity : 0 < 2*a)]
      apply (div_le_iff₀ (by positivity : 0 < 2*a)).mpr
      have hi := hx i
      change |x i-b i| ≤ a at hi
      linarith
    · change M b+(2*a) • M q = M x
      rw [← map_smul, ← map_add]
      congr 1
      ext i
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,q]
      rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) ha.ne')]
      ring
  · rintro ⟨x,hx,rfl⟩
    refine ⟨b+(2*a) • WithLp.ofLp x, ?_, ?_⟩
    · rw [coordinates_closedBall b ha.le]
      intro i _
      change b i-a ≤ b i+(2*a)*x i ∧ b i+(2*a)*x i ≤ b i+a
      have hi := abs_le.mp (hx i)
      constructor <;> nlinarith [hi.1,hi.2]
    · change M (b+(2*a) • WithLp.ofLp x) = M b + (2*a) • R x
      simp [M,orthogonalFrame]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SquareCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Convert the finite weighted lattice certificate into actual perpendicular Euclidean cylinders.
The factor is the exact area inflation caused by the derivative remainder. -/
theorem framed_local_cover_of_shape (M : Coordinates ≃L[ℝ] Plane) {h L R delta : ℝ}
    (shape : Cylinder → Prop)
    (hshape : ∀ b : Coordinates, ∀ a : ℝ, 0 < a → ∀ g : Plane,
      shape (projectedCylinder h g (M '' closedBall b a)))
    (hh : 0 < h) (hL : 0 ≤ L) (hR : 0 ≤ R) (hd : 0 ≤ delta)
    {K U : Set Coordinates} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (v : Plane → Plane) (A : Coordinates →L[ℝ] Coordinates)
    (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖M.symm (v (M p)) - M.symm (v (M b)) - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Coordinates → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    (hFval : ∀ p ∈ U, F p = physicalWeight h (v (M p)))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h (M '' K) v L)
      (h * (1 + 2 * L * delta * R) ^ 2 *
        (∫ p in M '' K, physicalWeight h (v p)) + eps) := by
  classical
  let B : ℝ := (1 + 2 * L * delta * R) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hscale : 0 < h * frameJacobian M * B := mul_pos (mul_pos hh (frameJacobian_pos M)) hB
  obtain ⟨n, hn, S, hS, hSU, hcov, hcost⟩ := local_finite_certificate hK hU hKU
    (fun p => M.symm (v (M p))) A hL hd hmodel hrem hF hFpos (div_pos heps hscale)
  let : Fintype S := hS.fintype
  let a : ℝ := (1 / 2 + L * delta * R) / n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; positivity
  let C : S → Cylinder := fun b => projectedCylinder h (v (M b)) (M '' closedBall (b : Coordinates) a)
  have harea (b : S) : (C b).area = h * frameJacobian M * (2 * a) ^ 2 * F b := by
    dsimp only [C]
    rw [projectedCylinder_area hh, frame_volume_image M isClosed_closedBall.measurableSet,
      coordinates_closedBall_volume b ha.le, hFval b (hSU b.property)]
    ring
  have hBrel : (2 * a) ^ 2 = B / (n : ℝ) ^ 2 := by
    dsimp [a, B]
    ring
  have hintegral : (∫ p in M '' K, physicalWeight h (v p)) =
      frameJacobian M * ∫ x in K, F x := by
    rw [frame_integral_image M hK.measurableSet]
    congr 1
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    exact (hFval x (hKU hx)).symm
  apply HasFiniteCover.of_fintype C
  · intro b
    exact hshape b a ha (v (M b))
  · rintro x ⟨_, ⟨p, hp, rfl⟩, s, hs, rfl⟩
    obtain ⟨b, hb, hc⟩ := hcov p hp s hs
    apply mem_iUnion.mpr
    refine ⟨⟨b, hb⟩, ?_⟩
    apply physicalRuled_mem_projectedCylinder
    refine ⟨p + s • (M.symm (v (M p)) - M.symm (v (M b))), ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      module
    · simp
  · have hsum : (∑ b : S, (C b).area) =
        (h * frameJacobian M * B) * ((∑' b : S, F b) / (n : ℝ) ^ 2) := by
      simp_rw [harea, hBrel]
      rw [tsum_fintype, ← Finset.mul_sum]
      ring
    rw [hsum, hintegral]
    have hc := (mul_lt_mul_of_pos_left hcost hscale).le
    calc
      _ ≤ (h * frameJacobian M * B) *
          ((∫ x in K, F x) + eps / (h * frameJacobian M * B)) := hc
      _ = _ := by
        rw [mul_add, mul_div_cancel₀ _ hscale.ne']
        dsimp [B]
        ring


/-- Every square-zero label has a patch whose compact subsets admit finite covers,
with one prescribed arbitrarily small area inflation. -/
theorem nilpotent_local_patch {h B : ℝ} (hh : 0 < h) (hB : 1 < B)
    {v : Plane → Plane} {U : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : Plane} (hp : p ∈ U) (hnil : (fderiv ℝ v p).comp (fderiv ℝ v p) = 0) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ K : Set Plane, IsCompact K → K ⊆ V →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover (squareProjected h) (physicalRuled h K v 1)
        (h * B * (∫ q in K, physicalWeight h (v q)) + eps) := by
  obtain ⟨Q, d, hQ⟩ := nilpotent_frame (fderiv ℝ v p) hnil
  let M := orthogonalFrame Q
  have hM (z : Coordinates) : M.symm ((fderiv ℝ v p) (M z)) = ![d*z 1,0] := by
    have hz := congrArg WithLp.ofLp (hQ (WithLp.toLp 2 z))
    exact hz
  let A : Coordinates →L[ℝ] Coordinates := d • shearCLM
  let R : ℝ := (1+|d|)/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hmodel : LatticeModel A 1 R := nilpotent_lattice_model d
  obtain ⟨delta, hd, hDB⟩ := exists_small_inflation 1 R hB
  let w : Coordinates → Coordinates := fun x => M.symm (v (M x))
  let Uc : Set Coordinates := M ⁻¹' U
  have hUco : IsOpen Uc := hU.preimage M.continuous
  have hpc : M.symm p ∈ Uc := by simpa [Uc]
  have hvc : ContDiffOn ℝ 1 (fun x => v (M x)) Uc :=
    hv.comp M.contDiff.contDiffOn (fun x hx => hx)
  have hwc : ContDiffOn ℝ 1 w Uc := M.symm.contDiff.comp_contDiffOn hvc
  have hvder := (hv.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hwd : fderiv ℝ w (M.symm p) = A := by
    have hvd : HasFDerivAt (fun x => v (M x))
        ((fderiv ℝ v p).comp M.toContinuousLinearMap) (M.symm p) := by
      have hvdp : HasFDerivAt v (fderiv ℝ v p) (M (M.symm p)) := by
        simpa using hvder.hasFDerivAt
      exact hvdp.comp (M.symm p) M.hasFDerivAt
    have hcomp := M.symm.hasFDerivAt.comp (M.symm p) hvd
    change fderiv ℝ (M.symm ∘ (fun x => v (M x))) (M.symm p) = A
    rw [hcomp.fderiv]
    ext z i
    have hz := congrArg (fun a : Coordinates => a i) (hM z)
    fin_cases i <;> simpa [A, shearCLM, shearLinear] using hz
  obtain ⟨r, hr, hrU, hrem⟩ := c1_local_remainder hUco hwc hpc hd
  let Vc := ball (M.symm p) (r / 2)
  have hrhalf : r / 2 < r := by linarith
  have hclU : closedBall (M.symm p) (r / 2) ⊆ Uc :=
    (closedBall_subset_ball hrhalf).trans hrU
  have hclF : ContinuousOn (fun x => physicalWeight h (v (M x)))
      (closedBall (M.symm p) (r / 2)) :=
    (physicalWeight_continuous h).comp_continuousOn (hvc.continuousOn.mono hclU)
  obtain ⟨F, hF, hFnon, hFeq⟩ := continuous_nonneg_extension isClosed_closedBall hclF
    (fun x _ => (physicalWeight_pos h (v (M x))).le)
  refine ⟨M '' Vc, M.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · exact ⟨M.symm p, mem_ball_self (half_pos hr), M.apply_symm_apply p⟩
  · intro K hK hKV eps heps
    let Kc := M.symm '' K
    have hKc : IsCompact Kc := hK.image M.symm.continuous
    have hKcV : Kc ⊆ Vc := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKV hq
      simpa using hx
    have himg : M '' Kc = K := by simp [Kc]
    have hc := framed_local_cover_of_shape M (squareProjected h)
      (fun b a ha g => ⟨_,g,orthogonal_closedBall_square Q b ha,rfl⟩)
      hh (by norm_num : (0:ℝ)≤1) hR.le hd.le hKc isOpen_ball hKcV v A hmodel
      (fun x hx y hy => by
        rw [← hwd]
        exact hrem x (ball_subset_ball hrhalf.le hx) y (ball_subset_ball hrhalf.le hy))
      hF hFnon (fun x hx => hFeq (ball_subset_closedBall hx)) heps
    rw [himg] at hc
    apply hc.mono Subset.rfl
    have hI : 0 ≤ ∫ q in K, physicalWeight h (v q) :=
      integral_nonneg (fun q => (physicalWeight_pos h (v q)).le)
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDB.le hh.le) hI]

/-- Finite square-tile approximation, with unrestricted local shear and arbitrary
compact labels. -/
theorem nilpotent_physical_cover {h : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hnil : ∀ p ∈ D, (fderiv ℝ v p).comp (fderiv ℝ v p) = 0)
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover (squareProjected h) (physicalRuled h D v 1)
      (h * (∫ p in D, physicalWeight h (v p)) + eps) := by
  obtain ⟨U, hU, hDU, hv⟩ := hv
  have hF : IntegrableOn (fun p => physicalWeight h (v p)) D :=
    ((physicalWeight_continuous h).comp_continuousOn (hv.continuousOn.mono hDU)).integrableOn_compact hD
  obtain ⟨B, hB, hbudget⟩ := exists_inflation_budget
    (h * ∫ p in D, physicalWeight h (v p)) (half_pos heps)
  have hc := globalize_local_covers h 1 v (fun p => physicalWeight h (v p)) (h*B) hD hF
    (fun p hp => nilpotent_local_patch hh hB hU hv (hDU hp) (hnil p hp)) (half_pos heps)
  apply hc.mono Subset.rfl
  nlinarith

lemma unitSquare_parallelogram : IsParallelogram unitSquare := by
  have he : unitSquare = (EuclideanSpace.equiv (Fin 2) ℝ).symm ''
      closedBall (0 : Coordinates) (1/2:ℝ) := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.ofLp x, ?_, rfl⟩
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
      exact hx
    · rintro ⟨y,hy,rfl⟩
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)] at hy
      exact hy
  rw [he]
  exact (coordinates_closedBall_parallelogram 0 (by norm_num : (0:ℝ)<1/2)).linear_image
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.injective

lemma IsSquareTile.parallelogram {T : Set Plane} (hT : IsSquareTile T) :
    IsParallelogram T := by
  obtain ⟨c,R,a,ha,rfl⟩ := hT
  have hi : Function.Injective (a • R.toLinearMap) := by
    intro x y hxy
    apply R.injective
    exact (smul_right_injective Plane ha.ne') hxy
  have he : (fun x => c+a • R x) '' unitSquare =
      (fun x => c+x) '' ((a • R.toLinearMap) '' unitSquare) := by
    rw [← image_comp]
    rfl
  rw [he]
  exact (unitSquare_parallelogram.linear_image (a • R.toLinearMap) hi).translate c

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Nilpotent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma physicalMaps_relation (h a : ℝ) (z : Space) :
    secondPhysicalMap h a z = vec3 0 0 (h*a) + swapReflect (firstPhysicalMap h z) := by
  ext i
  fin_cases i <;> simp [secondPhysicalMap,firstPhysicalMap,swapReflect,vec3]; ring

lemma firstPhysicalMap_injective {h : ℝ} (hh : h ≠ 0) :
    Function.Injective (firstPhysicalMap h) := by
  intro x y he
  have he0 := congrArg (fun z : Space => z 0) he
  have he1 := congrArg (fun z : Space => z 1) he
  have he2 := congrArg (fun z : Space => z 2) he
  ext i
  fin_cases i
  · exact he0
  · exact he1
  · exact (mul_left_cancel₀ hh he2)

lemma firstPhysicalMap_ruled (h : ℝ) (D : Set Plane) (G : Plane → Plane) :
    firstPhysicalMap h '' physicalRuled 1 D G 1 = physicalRuled h D G 1 := by
  ext z
  constructor
  · rintro ⟨_,⟨p,hp,s,hs,rfl⟩,rfl⟩
    exact ⟨p,hp,s,hs,by simp [firstPhysicalMap]⟩
  · rintro ⟨p,hp,s,hs,rfl⟩
    exact ⟨vec3 s (p 0+s*G p 0) (p 1+s*G p 1),
      ⟨p,hp,s,hs,by simp⟩,rfl⟩

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_CompactParallelogramApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Metric
open scoped Topology

noncomputable section
namespace RuledApproximation

theorem compact_coordinates_parallelogram_cover {K : Set Coordinates}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ P : Fin n → Set Coordinates,
      (∀ i, IsParallelogram (P i)) ∧ K ⊆ ⋃ i, P i ∧
      (∑ i, volume.real (P i)) < volume.real K + ε := by
  classical
  have hmodel : LatticeModel (0 : Coordinates →L[ℝ] Coordinates) 1 (1/2) := by
    simpa using nilpotent_lattice_model 0
  obtain ⟨m, hm, S, hS, _, hcover, hcost⟩ := local_finite_certificate
    hK isOpen_univ (subset_univ _) (fun _ => 0) 0
    (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 0 by norm_num) hmodel
    (by intros; simp) (continuous_const : Continuous (fun _ : Coordinates => (1:ℝ)))
    (fun _ => zero_le_one) hε
  let : Fintype S := hS.fintype
  let a : ℝ := (1/2) / m
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have ha : 0 < a := div_pos (by norm_num) hmR
  let e := Fintype.equivFin S
  let P : Fin (Fintype.card S) → Set Coordinates :=
    fun i => closedBall ((e.symm i : S) : Coordinates) a
  refine ⟨Fintype.card S, P, fun i => coordinates_closedBall_parallelogram _ ha, ?_, ?_⟩
  · intro p hp
    obtain ⟨b, hb, hdist⟩ := hcover p hp 0 (by norm_num)
    refine mem_iUnion.mpr ⟨e ⟨b, hb⟩, ?_⟩
    change p ∈ closedBall ((e.symm (e ⟨b, hb⟩) : S) : Coordinates) a
    simp only [Equiv.symm_apply_apply]
    rw [mem_closedBall, dist_eq_norm]
    simpa [a] using hdist
  · have harea (b : S) : volume.real (closedBall (b : Coordinates) a) = 1 / (m:ℝ)^2 := by
      rw [coordinates_closedBall_volume _ ha.le]
      dsimp [a]
      ring
    have hsum : (∑ i, volume.real (P i)) = (∑' b : S, (1:ℝ)) / (m:ℝ)^2 := by
      change (∑ i, volume.real (closedBall ((e.symm i : S) : Coordinates) a)) = _
      rw [e.symm.sum_comp (fun b : S => volume.real (closedBall (b : Coordinates) a))]
      simp only [harea, tsum_fintype, Finset.sum_div]
    rw [hsum]
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using hcost

theorem compact_parallelogram_cover {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 2) {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ P : Fin n → Set E,
      (∀ i, IsParallelogram (P i)) ∧ K ⊆ ⋃ i, P i ∧
      (∑ i, volume.real (P i)) < volume.real K + ε := by
  let e : E ≃ₗᵢ[ℝ] Plane := ((stdOrthonormalBasis ℝ E).reindex (finCongr hdim)).repr
  let M : Coordinates ≃L[ℝ] E :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.trans e.symm.toContinuousLinearEquiv
  have hmp : MeasurePreserving M volume volume :=
    e.symm.measurePreserving.comp (PiLp.volume_preserving_toLp (Fin 2))
  have harea (T : Set Coordinates) : volume.real (M '' T) = volume.real T := by
    have h := hmp.setIntegral_image_emb M.toHomeomorph.measurableEmbedding
      (fun _ => (1:ℝ)) T
    simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one] using h
  let Kc := M.symm '' K
  have hKc : IsCompact Kc := hK.image M.symm.continuous
  have himage : M '' Kc = K := by simp [Kc]
  have hvolume : volume.real Kc = volume.real K := by
    rw [← harea Kc, himage]
  obtain ⟨n, P, hP, hcover, hcost⟩ := compact_coordinates_parallelogram_cover hKc hε
  refine ⟨n, fun i => M '' P i, fun i => (hP i).linear_image M.toLinearMap M.injective,
    ?_, ?_⟩
  · intro x hx
    have hx' : M.symm x ∈ Kc := ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx')
    exact mem_iUnion.mpr ⟨i, M.symm x, hi, M.apply_symm_apply x⟩
  · simp only [harea]
    rwa [hvolume] at hcost

theorem Cylinder.compact_parallelogram_cover (C : Cylinder) (hC : IsCompact C.base)
    {ε : ℝ} (hε : 0 < ε) :
    HasFiniteCover Cylinder.parallelogram C.carrier (C.area + ε) := by
  obtain ⟨n, P, hP, hcover, hcost⟩ := RuledApproximation.compact_parallelogram_cover
    (similarityPlane_finrank C.axis C.unit_axis) hC hε
  let D : Fin n → Cylinder := fun i => ⟨C.axis, C.unit_axis, P i⟩
  refine ⟨n, D, hP, ?_, hcost.le⟩
  rintro x ⟨b, hb, s, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hb)
  exact mem_iUnion.mpr ⟨i, b, hi, s, rfl⟩

lemma HasFiniteCover.finite_iUnion {ι : Type*} [Fintype ι]
    {shape : Cylinder → Prop} (S : ι → Set Space) (A : ι → ℝ)
    (h : ∀ i, HasFiniteCover shape (S i) (A i)) :
    HasFiniteCover shape (⋃ i, S i) (∑ i, A i) := by
  classical
  have aux (s : Finset ι) : HasFiniteCover shape (⋃ i ∈ s, S i) (∑ i ∈ s, A i) := by
    induction s using Finset.induction_on with
    | empty => simpa using HasFiniteCover.empty shape (show (0:ℝ) ≤ 0 by norm_num)
    | @insert i s hi ih =>
      have heq : (⋃ j ∈ insert i s, S j) = S i ∪ ⋃ j ∈ s, S j := by
        ext x
        simp
      rw [heq, Finset.sum_insert hi]
      exact (h i).union ih
  simpa using aux Finset.univ

theorem compact_family_parallelogram_cover {n : ℕ} (C : Fin n → Cylinder)
    (hC : ∀ i, IsCompact (C i).base) {ε : ℝ} (hε : 0 < ε) :
    HasFiniteCover Cylinder.parallelogram (familySet C) (familyArea C + ε) := by
  have hδ : 0 < ε / (n + 1 : ℝ) := div_pos hε (by positivity)
  have hc := HasFiniteCover.finite_iUnion (fun i => (C i).carrier)
    (fun i => (C i).area + ε / (n + 1 : ℝ))
    (fun i => (C i).compact_parallelogram_cover (hC i) hδ)
  apply hc.mono Subset.rfl
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, familyArea]
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hmul : (n : ℝ) * (ε / (n + 1 : ℝ)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hn]
    nlinarith only [hε]
  linarith only [hmul]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_OpenBaseThickening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology

namespace CylinderCovering.OpenBaseThickening

variable {E : Type*} [MetricSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [ProperSpace E]

theorem tendsto_real_thickening (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) :
    Tendsto (fun r : ℝ => μ.real (thickening r K)) (𝓝[>] 0) (𝓝 (μ.real K)) := by
  apply (ENNReal.tendsto_toReal hK.measure_lt_top.ne).comp
  exact tendsto_measure_thickening_of_isClosed
    ⟨1, zero_lt_one, hK.isBounded.thickening.measure_lt_top.ne⟩ hK.isClosed

section FiniteFamily

variable {ι : Type*} [Fintype ι] {F : ι → Type*}
  [∀ i, MetricSpace (F i)] [∀ i, MeasurableSpace (F i)]
  [∀ i, OpensMeasurableSpace (F i)] [∀ i, ProperSpace (F i)]

theorem exists_common_thickening_two_budgets
    (μ : (i : ι) → Measure (F i)) [∀ i, IsFiniteMeasureOnCompacts (μ i)]
    (K : (i : ι) → Set (F i)) (hK : ∀ i, IsCompact (K i))
    (w : ι → ℝ) {A B : ℝ}
    (hA : (∑ i, (μ i).real (K i)) < A)
    (hB : (∑ i, w i * (μ i).real (K i)) < B) :
    ∃ r : ℝ, 0 < r ∧
      (∑ i, (μ i).real (thickening r (K i))) < A ∧
      (∑ i, w i * (μ i).real (thickening r (K i))) < B := by
  have hlimA : Tendsto (fun r : ℝ => ∑ i, (μ i).real (thickening r (K i)))
      (𝓝[>] 0) (𝓝 (∑ i, (μ i).real (K i))) := by
    exact tendsto_finsetSum _ (fun i _ => tendsto_real_thickening (μ i) (hK i))
  have hlimB : Tendsto (fun r : ℝ => ∑ i, w i * (μ i).real (thickening r (K i)))
      (𝓝[>] 0) (𝓝 (∑ i, w i * (μ i).real (K i))) := by
    exact tendsto_finsetSum _ (fun i _ =>
      tendsto_const_nhds.mul (tendsto_real_thickening (μ i) (hK i)))
  have heventA := hlimA.eventually (eventually_lt_nhds hA)
  have heventB := hlimB.eventually (eventually_lt_nhds hB)
  obtain ⟨r, hr, hrA, hrB⟩ :=
    (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioi (0 : ℝ))
      (heventA.and heventB)).exists
  exact ⟨r, hr, hrA, hrB⟩

theorem exists_open_family_two_budgets
    (μ : (i : ι) → Measure (F i)) [∀ i, IsFiniteMeasureOnCompacts (μ i)]
    (K : (i : ι) → Set (F i)) (hK : ∀ i, IsCompact (K i))
    (w : ι → ℝ) {A B : ℝ}
    (hA : (∑ i, (μ i).real (K i)) < A)
    (hB : (∑ i, w i * (μ i).real (K i)) < B) :
    ∃ U : (i : ι) → Set (F i),
      (∀ i, K i ⊆ U i ∧ IsOpen (U i) ∧ Bornology.IsBounded (U i) ∧
        MeasurableSet (U i)) ∧
      (∑ i, (μ i).real (U i)) < A ∧
      (∑ i, w i * (μ i).real (U i)) < B := by
  obtain ⟨r, hr, harea, hweighted⟩ :=
    exists_common_thickening_two_budgets μ K hK w hA hB
  refine ⟨fun i => thickening r (K i), ?_, harea, hweighted⟩
  intro i
  exact ⟨self_subset_thickening hr (K i), isOpen_thickening,
    (hK i).isBounded.thickening, isOpen_thickening.measurableSet⟩

end FiniteFamily

end CylinderCovering.OpenBaseThickening

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_OpenBaseApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation

theorem family_enlarge_open_two_budgets {n : ℕ} (C : Fin n → Cylinder)
    (S : Set Space) (hC : ∀ i, IsCompact (C i).base) {A B : ℝ}
    (hA : familyArea C < A) (hB : familyRelativeArea C S < B) :
    ∃ D : Fin n → Cylinder, (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openBounded) ∧ familySet C ⊆ familySet D ∧
      familyArea D < A ∧ familyRelativeArea D S < B := by
  classical
  have hw : (∑ i, ((C i).shadowArea S)⁻¹ * volume.real (C i).base) < B := by
    simpa only [familyRelativeArea, Cylinder.area, div_eq_mul_inv, mul_comm] using hB
  obtain ⟨U, hU, harea, hweighted⟩ :=
    CylinderCovering.OpenBaseThickening.exists_open_family_two_budgets
      (fun i => (volume : Measure ((Submodule.span ℝ ({(C i).axis} : Set Space))ᗮ)))
      (fun i => (C i).base) hC (fun i => ((C i).shadowArea S)⁻¹) hA hw
  let D : Fin n → Cylinder := fun i => ⟨(C i).axis, (C i).unit_axis, U i⟩
  refine ⟨D, fun _ => rfl, fun i => ⟨(hU i).2.1, (hU i).2.2.1, (hU i).2.2.2⟩,
    ?_, harea, ?_⟩
  · intro x hx
    obtain ⟨i, b, hb, t, ht⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, b, (hU i).1 hb, t, ht⟩
  · simpa only [familyRelativeArea, Cylinder.area, Cylinder.shadowArea,
      D, div_eq_mul_inv, mul_comm] using hweighted

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_CylinderBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace TriangularCovering

@[simp] theorem TriCylinder.toCylinder_axis (C : TriCylinder) :
    C.toCylinder.axis = C.axis := rfl

theorem TriCylinder.toCylinder_base_image (C : TriCylinder) :
    (Subtype.val : (normalPlane C.axis) → Space) '' C.toCylinder.base = C.base := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hx
    have hp : x ∈ normalPlane C.axis :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (C.perpendicular x hx)
    exact ⟨⟨x, hp⟩, hx, rfl⟩

@[simp] theorem TriCylinder.toCylinder_carrier (C : TriCylinder) :
    C.toCylinder.carrier = C.carrier := by
  ext x
  constructor
  · rintro ⟨b, hb, t, ht⟩
    exact ⟨b, hb, t, ht⟩
  · rintro ⟨b, hb, t, ht⟩
    have hp : b ∈ normalPlane C.axis :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (C.perpendicular b hb)
    exact ⟨⟨b, hp⟩, hb, t, ht⟩

@[simp] theorem TriCylinder.toCylinder_area (C : TriCylinder) :
    C.toCylinder.area = area C.base := by
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure (normalPlane C.axis)) =
      volume := by
    simpa only [normalPlane_rank C.unit_axis] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := normalPlane C.axis))
  rw [← C.toCylinder_base_image]
  change volume.real {x : normalPlane C.axis | (x : Space) ∈ C.base} =
    (Measure.euclideanHausdorffMeasure 2
      ((Subtype.val : normalPlane C.axis → Space) ''
        {x : normalPlane C.axis | (x : Space) ∈ C.base})).toReal
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image, hm]
  rfl

theorem TriCylinder.toCylinder_compact (C : TriCylinder) :
    IsCompact C.toCylinder.base := by
  have himage := C.toCylinder_base_image
  exact Subtype.isCompact_iff.mpr (himage.symm ▸ C.compact)

end TriangularCovering

namespace RuledApproximation

theorem Cylinder.shadowArea_eq_global (C : Cylinder) (S : Set Space) :
    C.shadowArea S = CylinderCovering.shadowArea S C.axis := by
  let P := TriangularCovering.normalPlane C.axis
  have hp : Module.finrank ℝ P = 2 := TriangularCovering.normalPlane_rank C.unit_axis
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure P) = volume := by
    simpa only [hp] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P))
  have himage : TriangularCovering.projection C.axis '' S =
      (Subtype.val : P → Space) '' (P.orthogonalProjectionOnto '' S) := by
    rw [image_image]
    congr 1
    funext z
    exact (TriangularCovering.normalPlane_projection C.unit_axis z).symm
  unfold Cylinder.shadowArea CylinderCovering.shadowArea TriangularCovering.area
  rw [himage, isometry_subtype_coe.euclideanHausdorffMeasure_image, hm]
  rfl

theorem familyRelativeArea_eq_global {n : ℕ} (C : Fin n → Cylinder) (S : Set Space) :
    familyRelativeArea C S = CylinderCovering.relativeCost S C := by
  simp only [familyRelativeArea, CylinderCovering.relativeCost, Cylinder.shadowArea_eq_global]

end RuledApproximation

namespace CylinderCovering

theorem openCounterexample_of_triangular {S : Set Space} {n : ℕ}
    (C : Fin n → TriangularCovering.TriCylinder)
    (hcov : triangularCovers S C)
    (harea : TriangularCovering.totalArea C < minimumShadowArea S / 2)
    (hrelative : triangularRelativeCost S C < 1 / 2) :
    ∃ D : Fin n → RuledApproximation.Cylinder,
      (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openBounded) ∧ S ⊆ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea D < minimumShadowArea S / 2 ∧
      relativeCost S D < 1 / 2 := by
  let C' : Fin n → RuledApproximation.Cylinder := fun i => (C i).toCylinder
  have harea' : RuledApproximation.familyArea C' < minimumShadowArea S / 2 := by
    simpa only [RuledApproximation.familyArea, C',
      TriangularCovering.TriCylinder.toCylinder_area, TriangularCovering.totalArea] using harea
  have hrel' : RuledApproximation.familyRelativeArea C' S < 1 / 2 := by
    simpa only [RuledApproximation.familyRelativeArea, C',
      TriangularCovering.TriCylinder.toCylinder_area,
      RuledApproximation.Cylinder.shadowArea_eq_global,
      TriangularCovering.TriCylinder.toCylinder_axis, triangularRelativeCost] using hrelative
  obtain ⟨D, haxis, hopen, hCD, hDarea, hDrelative⟩ :=
    RuledApproximation.family_enlarge_open_two_budgets C' S
      (fun i => (C i).toCylinder_compact) harea' hrel'
  refine ⟨D, haxis, hopen, ?_, hDarea, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hcov x hx
    apply hCD
    apply mem_iUnion.mpr
    exact ⟨i, by simpa only [C', TriangularCovering.TriCylinder.toCylinder_carrier] using hi⟩
  · rwa [RuledApproximation.familyRelativeArea_eq_global] at hDrelative

theorem regularOpen_of_regularTriangular
    (h : RegularTriangularCounterexampleStatement) : RegularOpenCounterexampleStatement := by
  intro S hS
  obtain ⟨n, C, hcov, harea, hrelative⟩ := h S hS
  obtain ⟨D, _, hopen, hcovD, hareaD, hrelativeD⟩ :=
    openCounterexample_of_triangular C hcov harea hrelative
  exact ⟨n, D, hopen, hcovD, hareaD, hrelativeD⟩

end CylinderCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_RegularSimplexSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace
namespace RegularSimplexSimilarity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem basis_isometry_of_gram {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c : Module.Basis ι ℝ F)
    (hgram : ∀ i j, inner ℝ (c i) (c j) = inner ℝ (b i) (b j)) :
    ∃ L : E ≃ₗᵢ[ℝ] F, ∀ i, L (b i) = c i := by
  classical
  let L := b.equiv c (Equiv.refl ι)
  have hL : ∀ i, L (b i) = c i := by
    intro i
    simp [L, Module.Basis.equiv_apply]
  have hexp (x : E) : L x = ∑ i, b.repr x i • c i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, hL]
  have hinner : ∀ x y, inner ℝ (L x) (L y) = inner ℝ x y := by
    intro x y
    calc
      inner ℝ (L x) (L y) =
          inner ℝ (∑ i, b.repr x i • c i) (∑ j, b.repr y j • c j) := by
        rw [hexp, hexp]
      _ = inner ℝ (∑ i, b.repr x i • b i) (∑ j, b.repr y j • b j) := by
        simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hgram]
      _ = inner ℝ x y := by rw [b.sum_repr, b.sum_repr]
  exact ⟨L.isometryOfInner hinner, hL⟩

theorem affine_basis_congruence {ι : Type*} [Fintype ι]
    (p : AffineBasis ι ℝ E) (q : AffineBasis ι ℝ F) (i₀ : ι)
    (hdist : ∀ i j, dist (q i) (q j) = dist (p i) (p j)) :
    ∃ L : E ≃ₗᵢ[ℝ] F, ∃ t : F, ∀ i, q i = t + L (p i) := by
  classical
  have hgram : ∀ i j, inner ℝ (q.basisOf i₀ i) (q.basisOf i₀ j) =
      inner ℝ (p.basisOf i₀ i) (p.basisOf i₀ j) := by
    intro i j
    simp only [AffineBasis.basisOf_apply, vsub_eq_sub,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm, hdist]
  obtain ⟨L, hL⟩ := basis_isometry_of_gram (p.basisOf i₀) (q.basisOf i₀) hgram
  refine ⟨L, q i₀ - L (p i₀), ?_⟩
  intro i
  by_cases hi : i = i₀
  · subst i
    abel
  · have h := hL ⟨i, hi⟩
    simp only [AffineBasis.basisOf_apply, vsub_eq_sub, map_sub] at h
    calc
      q i = (q i - q i₀) + q i₀ := by abel
      _ = (L (p i) - L (p i₀)) + q i₀ := by rw [h]
      _ = q i₀ - L (p i₀) + L (p i) := by abel

theorem simplex_congruence {n : ℕ}
    (p q : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    (hdist : ∀ i j, dist (q i) (q j) = dist (p i) (p j)) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ t : EuclideanSpace ℝ (Fin n), ∀ i, q i = t + L (p i) := by
  let bp : AffineBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin n)) :=
    ⟨p, hp, hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)⟩
  let bq : AffineBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin n)) :=
    ⟨q, hq, hq.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)⟩
  exact affine_basis_congruence bp bq 0 hdist

theorem simplex_similarity {n : ℕ}
    (p q : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    {r : ℝ} (hr : 0 < r)
    (hdist : ∀ i j, dist (q i) (q j) = r * dist (p i) (p j)) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ t : EuclideanSpace ℝ (Fin n), ∀ i, q i = t + r • L (p i) := by
  have hp' : AffineIndependent ℝ (fun i => r • p i) := by
    simpa only [Function.comp_def, AffineMap.homothety_apply, vsub_eq_sub,
      sub_zero, vadd_eq_add, add_zero] using
      hp.map' (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin n)) r)
        (AffineMap.homothety_injective _ (ne_of_gt hr))
  have hd' : ∀ i j, dist (q i) (q j) = dist (r • p i) (r • p j) := by
    intro i j
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr, hdist]
  obtain ⟨L, t, h⟩ := simplex_congruence (fun i => r • p i) q hp' hq hd'
  exact ⟨L, t, by simpa only [map_smul] using h⟩

theorem simplex_similarity_hull {n : ℕ}
    (p q : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    {r : ℝ} (hr : 0 < r)
    (hdist : ∀ i j, dist (q i) (q j) = r * dist (p i) (p j)) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ t : EuclideanSpace ℝ (Fin n),
        convexHull ℝ (range q) =
          CylinderCovering.Similarity.map t r L '' convexHull ℝ (range p) := by
  obtain ⟨L, t, h⟩ := simplex_similarity p q hp hq hr hdist
  refine ⟨L, t, ?_⟩
  let f := CylinderCovering.Similarity.affineMap t r L
  have hf : q = f ∘ p := by
    funext i
    exact h i
  rw [hf, range_comp, ← f.image_convexHull]
  rfl

theorem regular_simplex_similarity {n : ℕ}
    (p q : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hpdist : ∀ i j, i ≠ j → dist (p i) (p j) = a)
    (hqdist : ∀ i j, i ≠ j → dist (q i) (q j) = b) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ t : EuclideanSpace ℝ (Fin n),
        convexHull ℝ (range q) =
          CylinderCovering.Similarity.map t (b / a) L '' convexHull ℝ (range p) := by
  apply simplex_similarity_hull p q hp hq (div_pos hb ha)
  intro i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [hpdist i j hij, hqdist i j hij, div_mul_cancel₀ _ (ne_of_gt ha)]

end RegularSimplexSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_TriangularSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace TriangularCovering

namespace TriCylinder

lemma similarity_carrier (c : TriCylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) :
    (c.similarity t hr L).carrier = CylinderCovering.Similarity.map t r L '' c.carrier :=
  (CylinderCovering.Similarity.carrier_image c.base c.axis t hr L).symm

lemma similarity_area (c : TriCylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) :
    area (c.similarity t hr L).base = r ^ 2 * area c.base :=
  CylinderCovering.Similarity.area_transportedBase c.base c.axis t hr L

end TriCylinder

lemma similarity_totalArea {m : ℕ} (c : Fin m → TriCylinder)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    totalArea (fun i => (c i).similarity t hr L) = r ^ 2 * totalArea c := by
  simp only [totalArea, TriCylinder.similarity_area, Finset.mul_sum]

lemma similarity_covers {m : ℕ} (c : Fin m → TriCylinder) (hc : Covers c)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    ∀ x ∈ CylinderCovering.Similarity.map t r L '' K,
      ∃ i, x ∈ ((c i).similarity t hr L).carrier := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨i, hi⟩ := hc y hy
  refine ⟨i, ?_⟩
  rw [TriCylinder.similarity_carrier]
  exact ⟨y, hi, rfl⟩

lemma similarity_relativeCost {m : ℕ} (c : Fin m → TriCylinder)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    (∑ i, area ((c i).similarity t hr L).base /
      CylinderCovering.Similarity.shadowArea
        (CylinderCovering.Similarity.map t r L '' K) ((c i).similarity t hr L).axis) =
      relativeCost c := by
  unfold relativeCost
  apply Finset.sum_congr rfl
  intro i hi
  exact CylinderCovering.Similarity.areaRatio_map (c i).base K (c i).axis t hr L

theorem triangle_cover_similarity {m : ℕ} (c : Fin m → TriCylinder)
    (hc : Covers c) (harea : totalArea c < A_min / 2)
    (hrelative : relativeCost c < 1 / 2)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    ∃ d : Fin m → TriCylinder,
      (∀ x ∈ CylinderCovering.Similarity.map t r L '' K, ∃ i, x ∈ (d i).carrier) ∧
      totalArea d < CylinderCovering.Similarity.minimumArea
        (CylinderCovering.Similarity.map t r L '' K) / 2 ∧
      (∑ i, area (d i).base / CylinderCovering.Similarity.shadowArea
        (CylinderCovering.Similarity.map t r L '' K) (d i).axis) < 1 / 2 := by
  refine ⟨fun i => (c i).similarity t hr L, similarity_covers c hc t hr L, ?_, ?_⟩
  · rw [similarity_totalArea, CylinderCovering.Similarity.minimumArea_map K t hr L]
    change r ^ 2 * totalArea c < r ^ 2 * A_min / 2
    nlinarith [mul_lt_mul_of_pos_left harea (sq_pos_of_ne_zero hr)]
  · rw [similarity_relativeCost]
    exact hrelative

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_RegularCounterexamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory

noncomputable section
namespace CylinderCovering

theorem regularTriangularCounterexample_result : RegularTriangularCounterexampleStatement := by
  intro K hK
  rcases hK with ⟨v, hv, edge, hedge, hdist, rfl⟩
  obtain ⟨L, t, hsim⟩ := RegularSimplexSimilarity.regular_simplex_similarity
    TriangularCovering.tetraVertices v TriangularCovering.tetra_affineIndependent hv
    (show (0 : ℝ) < 2 by norm_num) hedge
    (fun _ _ h => TriangularCovering.tetra_edge_length h) hdist
  rw [← TriangularCovering.K_eq_convexHull] at hsim
  rw [hsim]
  have he : (0 : ℝ) < 1 / 2000 := by norm_num
  have hs : (1 / 2000 : ℝ) ≤ 1 / 2000 := le_rfl
  let C := TriangularCovering.finiteFamily (1 / 2000) he
  have hc : TriangularCovering.Covers C :=
    TriangularCovering.finiteFamily_covers he (by norm_num [TriangularCovering.η])
  obtain ⟨D, hcover, harea, hrelative⟩ := TriangularCovering.triangle_cover_similarity
    C hc (TriangularCovering.finiteFamily_strict_closed he hs)
    (TriangularCovering.finiteFamily_relative_lt_closed he hs)
    t (ne_of_gt (div_pos hedge (by norm_num : (0 : ℝ) < 2))) L
  exact ⟨_, D, hcover, harea, hrelative⟩

end CylinderCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_RegularBaseVariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering

theorem parallelogramCounterexample_of_compact {S : Set Space} {n : ℕ}
    (C : Fin n → RuledApproximation.Cylinder)
    (hcompact : ∀ i, IsCompact (C i).base)
    (hcov : S ⊆ RuledApproximation.familySet C)
    (harea : RuledApproximation.familyArea C < minimumShadowArea S / 2) :
    ∃ m : ℕ, ∃ D : Fin m → RuledApproximation.Cylinder,
      (∀ i, (D i).parallelogram) ∧ S ⊆ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea D < minimumShadowArea S / 2 ∧
      relativeCost S D < 1 / 2 := by
  have hnonneg : 0 ≤ RuledApproximation.familyArea C :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hmin : 0 < minimumShadowArea S := by linarith
  let ε := (minimumShadowArea S / 2 - RuledApproximation.familyArea C) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨m, D, hD, hCD, hcost⟩ :=
    RuledApproximation.compact_family_parallelogram_cover C hcompact hε
  have hstrict : RuledApproximation.familyArea D < minimumShadowArea S / 2 := by
    dsimp [ε] at hcost
    linarith
  refine ⟨m, D, hD, hcov.trans hCD, hstrict, ?_⟩
  exact RuledApproximation.relativeCost_lt_half_of_familyArea_lt S hmin D hstrict

theorem parallelogramCounterexample_of_triangular {S : Set Space} {n : ℕ}
    (C : Fin n → TriangularCovering.TriCylinder)
    (hcov : triangularCovers S C)
    (harea : TriangularCovering.totalArea C < minimumShadowArea S / 2) :
    ∃ m : ℕ, ∃ D : Fin m → RuledApproximation.Cylinder,
      (∀ i, (D i).parallelogram) ∧ S ⊆ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea D < minimumShadowArea S / 2 ∧
      relativeCost S D < 1 / 2 := by
  let C' : Fin n → RuledApproximation.Cylinder := fun i => (C i).toCylinder
  have harea' : RuledApproximation.familyArea C' < minimumShadowArea S / 2 := by
    simpa only [RuledApproximation.familyArea, C',
      TriangularCovering.TriCylinder.toCylinder_area, TriangularCovering.totalArea] using harea
  apply parallelogramCounterexample_of_compact C'
    (fun i => (C i).toCylinder_compact) ?_ harea'
  intro x hx
  obtain ⟨i, hi⟩ := hcov x hx
  exact mem_iUnion.mpr ⟨i, by
    simpa only [C', TriangularCovering.TriCylinder.toCylinder_carrier] using hi⟩

theorem regularParallelogramCounterexample_result :
    RegularParallelogramCounterexampleStatement := by
  intro S hS
  obtain ⟨n, C, hcov, harea, _⟩ := regularTriangularCounterexample_result S hS
  exact parallelogramCounterexample_of_triangular C hcov harea

theorem regularOpenCounterexample_result : RegularOpenCounterexampleStatement :=
  regularOpen_of_regularTriangular regularTriangularCounterexample_result

end CylinderCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Riemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CylinderCovering.RadialRiemann
open Set MeasureTheory Filter
open scoped Interval Topology

lemma point_zero (a b : ℝ) (N : ℕ) : point a b N 0 = a := by
  simp [point]

lemma point_last {a b : ℝ} {N : ℕ} (hN : 0 < N) : point a b N N = b := by
  rw [point, count_step hN]
  ring

lemma cell_dist_le {a b : ℝ} {N : ℕ} {i : Fin N} {x y : ℝ}
    (hx : x ∈ cell a b N i) (hy : y ∈ cell a b N i) :
    dist x y ≤ step a b N := by
  rw [Real.dist_eq, abs_le]
  have hs := point_succ a b N i
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma step_tendsto (a b : ℝ) :
    Tendsto (step a b) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  change Tendsto (fun N : ℕ => (b - a) / (N : ℝ)) atTop (𝓝 0)
  simpa [div_eq_mul_inv] using hi.const_mul (b - a)

lemma diagonal_continuous {a b : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b))) :
    ContinuousOn (fun t => F t t) (Icc a b) := by
  exact hF.comp (continuousOn_id.prodMk continuousOn_id) (fun _ ht => ⟨ht, ht⟩)

lemma diagonal_cell_integrable {a b : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b)))
    {N : ℕ} (i : Fin N) :
    IntervalIntegrable (fun t => F t t) volume (point a b N i) (point a b N (i+1)) := by
  have hle : point a b N i ≤ point a b N (i+1) := by
    have hs := point_succ a b N i
    have hd := step_pos hab (Nat.zero_lt_of_lt i.isLt)
    linarith
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hle]
  exact (diagonal_continuous hF).mono (cell_subset hab i)

lemma integral_mesh_sum {a b : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b)))
    {N : ℕ} (hN : 0 < N) :
    (∑ i : Fin N, ∫ t in point a b N i..point a b N (i+1), F t t) =
      ∫ t in a..b, F t t := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∫ t in point a b N i..point a b N (i+1), F t t) N]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun i hi => diagonal_cell_integrable hab hF (⟨i, hi⟩ : Fin N))]
  rw [point_zero, point_last hN]

lemma mixedSum_error {a b E : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b)))
    {N : ℕ} (hN : 0 < N) (leftTag rightTag : Fin N → ℝ)
    (hbound : ∀ i, ∀ t ∈ cell a b N i, |F (leftTag i) (rightTag i) - F t t| ≤ E) :
    |mixedSum F a b N leftTag rightTag - (∫ t in a..b, F t t)| ≤ E * (b-a) := by
  have hi := integral_mesh_sum hab hF hN
  rw [← hi, mixedSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin N, |step a b N * F (leftTag i) (rightTag i) -
      (∫ t in point a b N i..point a b N (i+1), F t t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, E * step a b N := by
      apply Finset.sum_le_sum
      intro i _
      have hle : point a b N i ≤ point a b N (i+1) := by
        have hs := point_succ a b N i
        have hd := step_pos hab hN
        linarith
      have hu : ∀ t ∈ Ι (point a b N i) (point a b N (i+1)),
          ‖F (leftTag i) (rightTag i) - F t t‖ ≤ E := by
        intro t ht
        rw [uIoc_of_le hle] at ht
        exact (hbound i t ⟨ht.1.le, ht.2⟩)
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hu
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (diagonal_cell_integrable hab hF i), intervalIntegral.integral_const,
        Real.norm_eq_abs, smul_eq_mul, point_succ,
        abs_of_nonneg (step_pos hab hN).le] at h
      exact h
    _ = E * (b-a) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (N : ℝ) * (E * step a b N) = E * ((N : ℝ) * step a b N) := by ring
        _ = E * (b-a) := by rw [count_step hN]

theorem mixedSum_tendsto {a b : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b)))
    (leftTag rightTag : (N : ℕ) → Fin N → ℝ)
    (hleft : ∀ N, IsTagged a b N (leftTag N))
    (hright : ∀ N, IsTagged a b N (rightTag N)) :
    Tendsto (fun N => mixedSum F a b N (leftTag N) (rightTag N)) atTop
      (𝓝 (∫ t in a..b, F t t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hE : 0 < ε / (2 * (b-a)) := div_pos hε (by positivity)
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc _ hE
  filter_upwards [(step_tendsto a b).eventually_lt_const hδ,
    eventually_gt_atTop (0 : ℕ)] with N hsmall hN
  rw [Real.dist_eq]
  have he := mixedSum_error hab hF hN (leftTag N) (rightTag N) (E := ε / (2*(b-a)))
    (by
      intro i t ht
      have hl := hleft N i
      have hr := hright N i
      have hdist : dist (leftTag N i, rightTag N i) (t,t) < δ := by
        rw [Prod.dist_eq]
        exact lt_of_le_of_lt (max_le (cell_dist_le hl ht) (cell_dist_le hr ht)) hsmall
      exact (hclose _ ⟨cell_subset hab i hl, cell_subset hab i hr⟩
        _ ⟨cell_subset hab i ht, cell_subset hab i ht⟩ hdist).le)
  refine he.trans_lt ?_
  have hcancel : ε / (2*(b-a)) * (b-a) = ε / 2 := by field_simp
  rw [hcancel]
  linarith

lemma collarSum_eq_mixed {a b K : ℝ} {R W : ℝ → ℝ} {N : ℕ}
    (maxTag tag : Fin N → ℝ) (hmax : ∀ i, R (maxTag i) = capMax R a b N i) :
    collarSum R W K a b N tag =
      mixedSum (fun r c => R r ^ 2 * W c) a b N maxTag tag +
      (2 * (K * step a b N)) * mixedSum (fun r c => R r * W c) a b N maxTag tag +
      (K * step a b N)^2 * mixedSum (fun _ c => W c) a b N maxTag tag := by
  simp only [collarSum, mixedSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hmax i]
  ring

theorem collarSum_tendsto {a b : ℝ} (hab : a < b) {R W : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) (hW : ContinuousOn W (Icc a b)) (K : ℝ)
    (tag : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => collarSum R W K a b N (tag N)) atTop
      (𝓝 (∫ t in a..b, R t ^ 2 * W t)) := by
  choose maxTag hmaxmem hmaxeq using
    (fun N (i : Fin N) => exists_capMax_tag hab hR i)
  have hmaxtag : ∀ N, IsTagged a b N (maxTag N) := hmaxmem
  have hRp : ContinuousOn (fun p : ℝ × ℝ => R p.1)
      ((Icc a b) ×ˢ (Icc a b)) :=
    hR.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hWp : ContinuousOn (fun p : ℝ × ℝ => W p.2)
      ((Icc a b) ×ˢ (Icc a b)) :=
    hW.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have h0 := mixedSum_tendsto hab (F := fun r c => R r ^ 2 * W c) ((hRp.pow 2).mul hWp) maxTag tag hmaxtag htag
  have h1 := mixedSum_tendsto hab (F := fun r c => R r * W c) (hRp.mul hWp) maxTag tag hmaxtag htag
  have h2 := mixedSum_tendsto hab (F := fun _ c => W c) hWp maxTag tag hmaxtag htag
  have hkd : Tendsto (fun N => K * step a b N) atTop (𝓝 0) := by
    simpa using (step_tendsto a b).const_mul K
  have hlim := (h0.add ((hkd.const_mul 2).mul h1)).add ((hkd.pow 2).mul h2)
  have heq : (fun N => collarSum R W K a b N (tag N)) =
      (fun N => mixedSum (fun r c => R r ^ 2 * W c) a b N (maxTag N) (tag N) +
      (2 * (K * step a b N)) * mixedSum (fun r c => R r * W c) a b N (maxTag N) (tag N) +
      (K * step a b N)^2 * mixedSum (fun _ c => W c) a b N (maxTag N) (tag N)) := by
    funext N
    exact collarSum_eq_mixed (maxTag N) (tag N) (hmaxeq N)
  rw [heq]
  simpa using hlim

lemma le_capMax {a b : ℝ} (hab : a < b) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) {N : ℕ} {i : Fin N} {t : ℝ}
    (ht : t ∈ cell a b N i) : R t ≤ capMax R a b N i := by
  exact le_csSup (isCompact_Icc.bddAbove_image (hR.mono (cell_subset hab i)))
    ⟨t, ht, rfl⟩

lemma projection_weight_continuousOn {E : Type*} [SeminormedAddGroup E]
    {a b : ℝ} {w : ℝ → E} (hw : ContinuousOn w (Icc a b)) :
    ContinuousOn (fun t => 1 / Real.sqrt (1 + ‖w t‖^2)) (Icc a b) := by
  apply continuousOn_const.div ((hw.norm.pow 2).const_add 1).sqrt
  intro t _
  change Real.sqrt (1 + ‖w t‖^2) ≠ 0
  exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg ‖w t‖]))

theorem physical_collar_tendsto {E : Type*} [SeminormedAddGroup E]
    {a b : ℝ} (hab : a < b) {R : ℝ → ℝ} {w : ℝ → E}
    (hR : ContinuousOn R (Icc a b)) (hw : ContinuousOn w (Icc a b)) (K κ : ℝ)
    (tag : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      κ * step a b N * (capMax R a b N i + K * step a b N)^2 /
        (2 * Real.sqrt (1 + ‖w (tag N i)‖^2))) atTop
      (𝓝 (κ * ∫ t in a..b, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2)))) := by
  have h := (collarSum_tendsto hab hR (projection_weight_continuousOn hw) K tag htag).const_mul (κ/2)
  convert h using 1
  · funext N
    simp only [collarSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · congr 1
    have hi : (∫ t in a..b, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2))) =
        (1/2 : ℝ) * ∫ t in a..b, R t^2 * (1 / Real.sqrt (1 + ‖w t‖^2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hi]
    ring

lemma exists_adjacent_interval (f : ℕ → ℝ) {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Icc (f 0) (f N)) :
    ∃ i : Fin N, x ∈ Icc (f i) (f (i+1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨⟨0, by decide⟩, hx⟩
    · by_cases hlast : x ≤ f N
      · obtain ⟨i, hi⟩ := ih (Nat.pos_of_ne_zero hzero) ⟨hx.1, hlast⟩
        exact ⟨⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self N)⟩, hi⟩
      · exact ⟨⟨N, Nat.lt_succ_self N⟩, (lt_of_not_ge hlast).le, hx.2⟩

lemma exists_cell {a b : ℝ} {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Icc a b) : ∃ i : Fin N, x ∈ cell a b N i := by
  apply exists_adjacent_interval (point a b N) hN
  simpa only [point_zero, point_last hN] using hx

end CylinderCovering.RadialRiemann

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_AreaConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CylinderCovering.RadialSweep
open Set MeasureTheory Filter
open scoped Topology

theorem frozenArea_tendsto (D : Data) (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N, RadialRiemann.IsTagged D.α D.β N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N, frozenArea D N (tag N) i) atTop
      (𝓝 (weightedArea D)) := by
  exact RadialRiemann.physical_collar_tendsto D.interval_nonempty
    D.cap_continuous D.velocity_continuous (radialError D + collar D) (kappa D) tag htag

end CylinderCovering.RadialSweep

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Freezing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RadialFreezing

theorem collar_gt_radial {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A < 2 * (A + B) + 1 := by
  linarith

theorem footprint_subset_triangle {A B R d u v m : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hu_lower : -A * d ≤ u) (hu_upper : u ≤ R + A * d)
    (hv : |v - m * u| ≤ d / 2 * |u| + B * d ^ 2) :
    -(2 * (A + B) + 1) * d ≤ u ∧
      u ≤ R + A * d ∧
      |v - m * u| ≤ d / 2 * (u + (2 * (A + B) + 1) * d) := by
  have hC : A ≤ 2 * (A + B) + 1 := le_of_lt (collar_gt_radial hA hB)
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hC) hd]
  constructor
  · exact hu_upper
  · apply hv.trans
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
      nlinarith [sq_nonneg d, mul_nonneg hA (sq_nonneg d)]
    · rw [abs_of_neg (lt_of_not_ge hu)]
      have hmul : 0 ≤ d * (u + A * d) :=
        mul_nonneg hd (by linarith)
      nlinarith [sq_nonneg d]

end RadialFreezing

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Integral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory

noncomputable section

namespace CylinderCovering.RadialIntegral

theorem transverse_integral_bound {lam : ℝ → ℝ} {M c t : ℝ}
    (_hM : 0 ≤ M) (hlam : ∀ x ∈ uIcc c t, |lam x| ≤ M) :
    |∫ x in c..t, lam x * (x - t)| ≤ M * (t - c) ^ 2 / 2 := by
  by_cases hct : c ≤ t
  · have hbound : ∀ᵐ x : ℝ, x ∈ Ioc c t →
        ‖lam x * (x - t)‖ ≤ M * (t - x) := by
      filter_upwards [] with x hx
      have hxlam := hlam x (by simpa [uIcc_of_le hct] using
        (show x ∈ Icc c t from ⟨hx.1.le, hx.2⟩))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (sub_nonpos.mpr hx.2)]
      calc
        |lam x| * -(x - t) ≤ M * -(x - t) :=
          mul_le_mul_of_nonneg_right hxlam (by linarith [hx.2])
        _ = M * (t - x) := by ring
    have hi : IntervalIntegrable (fun x : ℝ => M * (t - x)) volume c t :=
      (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
    have hb := intervalIntegral.norm_integral_le_of_norm_le hct hbound hi
    have heval : (∫ x in c..t, M * (t - x)) = M * (t - c) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun _ : ℝ => t) (g := fun x : ℝ => x)
          intervalIntegrable_const (continuous_id.intervalIntegrable c t)]
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      ring
    simpa only [Real.norm_eq_abs, heval] using hb
  · have htc : t ≤ c := le_of_not_ge hct
    have hbound : ∀ᵐ x : ℝ, x ∈ Ioc t c →
        ‖lam x * (x - t)‖ ≤ M * (x - t) := by
      filter_upwards [] with x hx
      have hxlam := hlam x (by simpa [uIcc_of_ge htc] using
        (show x ∈ Icc t c from ⟨hx.1.le, hx.2⟩))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      exact mul_le_mul_of_nonneg_right hxlam (sub_nonneg.mpr hx.1.le)
    have hi : IntervalIntegrable (fun x : ℝ => M * (x - t)) volume t c :=
      (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
    have hb := intervalIntegral.norm_integral_le_of_norm_le htc hbound hi
    have heval : (∫ x in t..c, M * (x - t)) = M * (t - c) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => t)
          (continuous_id.intervalIntegrable t c) intervalIntegrable_const]
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      ring
    rw [intervalIntegral.integral_symm, abs_neg]
    simpa only [Real.norm_eq_abs, heval] using hb

theorem radial_integral_bound {lam : ℝ → ℝ} {M c t : ℝ}
    (hlam : ∀ x ∈ uIcc c t, |lam x| ≤ M) :
    |∫ x in c..t, lam x| ≤ M * |t - c| := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := c) (b := t) (C := M) (f := lam) (fun x hx => by
      simpa only [Real.norm_eq_abs] using hlam x (uIoc_subset_uIcc hx))
  simpa only [Real.norm_eq_abs, mul_comm] using hb

theorem integral_eq_sub_of_within_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b c t : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ x in c..t, f' x) = f t - f c := by
  have forward : ∀ c t : ℝ, c ∈ Icc a b → t ∈ Icc a b → c ≤ t →
      (∫ x in c..t, f' x) = f t - f c := by
    intro c t hc ht hct
    have hsub : Icc c t ⊆ Icc a b := fun x hx =>
      ⟨hc.1.trans hx.1, hx.2.trans ht.2⟩
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hct (hf.mono hsub)
    · intro x hx
      have hax : a < x := hc.1.trans_lt hx.1
      have hxb : x < b := hx.2.trans_le ht.2
      exact (hderiv x ⟨hax.le, hxb.le⟩).hasDerivAt (Icc_mem_nhds hax hxb)
    · exact ContinuousOn.intervalIntegrable_of_Icc hct (hf'.mono hsub)
  by_cases hct : c ≤ t
  · exact forward c t hc ht hct
  · rw [intervalIntegral.integral_symm, forward t c ht hc (le_of_not_ge hct)]
    abel

theorem integral_footprint {lam : ℝ → ℝ} {M L d c t m rho R s : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hlam : ∀ x ∈ uIcc c t, |lam x| ≤ M)
    (htc : |t - c| ≤ d) (htm : |t - m| ≤ d / 2)
    (hs : |s| ≤ L) (hrho : 0 ≤ rho) (hR : rho ≤ R) :
    let u := rho + s * (∫ x in c..t, lam x);
    let v := t * u + s * (∫ x in c..t, lam x * (x - t));
    -(L * M) * d ≤ u ∧ u ≤ R + (L * M) * d ∧
      |v - m * u| ≤ d / 2 * |u| + (L * M / 2) * d ^ 2 := by
  dsimp only
  have hI : |∫ x in c..t, lam x| ≤ M * d :=
    (radial_integral_bound hlam).trans (mul_le_mul_of_nonneg_left htc hM)
  have hsq : (t - c) ^ 2 ≤ d ^ 2 := by
    have := sq_le_sq₀ (abs_nonneg (t - c)) hd |>.mpr htc
    simpa only [sq_abs] using this
  have hJ : |∫ x in c..t, lam x * (x - t)| ≤ M * d ^ 2 / 2 :=
    (transverse_integral_bound hM hlam).trans (by nlinarith [mul_le_mul_of_nonneg_left hsq hM])
  have hrad : |s * (∫ x in c..t, lam x)| ≤ L * M * d := by
    rw [abs_mul]
    calc
      |s| * |∫ x in c..t, lam x| ≤ L * (M * d) :=
        mul_le_mul hs hI (abs_nonneg _) hL
      _ = L * M * d := by ring
  have htrans : |s * (∫ x in c..t, lam x * (x - t))| ≤
      (L * M / 2) * d ^ 2 := by
    rw [abs_mul]
    calc
      |s| * |∫ x in c..t, lam x * (x - t)| ≤ L * (M * d ^ 2 / 2) :=
        mul_le_mul hs hJ (abs_nonneg _) hL
      _ = (L * M / 2) * d ^ 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · have := (abs_le.mp hrad).1
    linarith
  · have := (abs_le.mp hrad).2
    linarith
  · rw [show t * (rho + s * (∫ x in c..t, lam x)) +
        s * (∫ x in c..t, lam x * (x - t)) -
        m * (rho + s * (∫ x in c..t, lam x)) =
        (t - m) * (rho + s * (∫ x in c..t, lam x)) +
        s * (∫ x in c..t, lam x * (x - t)) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right htm (abs_nonneg _)) htrans

theorem aligned_increment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℝ → E} {lam : ℝ → ℝ} {a b c t : ℝ} {p q : E}
    (hw : ContinuousOn w (Icc a b)) (hlam : ContinuousOn lam (Icc a b))
    (hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt w (lam x • (p + x • q)) (Icc a b) x)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    w t - w c = (∫ x in c..t, lam x) • (p + t • q) +
      (∫ x in c..t, lam x * (x - t)) • q := by
  have hsub : uIcc c t ⊆ Icc a b := uIcc_subset_Icc hc ht
  have hvel : ContinuousOn (fun x => lam x • (p + x • q)) (Icc a b) :=
    hlam.smul (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  rw [← integral_eq_sub_of_within_deriv hw hvel hderiv hc ht]
  have hpoint : (fun x => lam x • (p + x • q)) =
      (fun x => lam x • (p + t • q) + (lam x * (x - t)) • q) := by
    funext x
    module
  rw [hpoint]
  have hrad : IntervalIntegrable (fun x => lam x • (p + t • q)) volume c t :=
    ((hlam.mono hsub).smul continuousOn_const).intervalIntegrable
  have htrans : IntervalIntegrable (fun x => (lam x * (x - t)) • q) volume c t :=
    (((hlam.mono hsub).mul (continuous_id.sub continuous_const).continuousOn).smul
      continuousOn_const).intervalIntegrable
  rw [intervalIntegral.integral_add hrad htrans]
  simp only [intervalIntegral.integral_smul_const]

theorem aligned_frozen_intercept
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℝ → E} {lam : ℝ → ℝ} {a b c t rho s : ℝ} {p q p0 : E}
    (hw : ContinuousOn w (Icc a b)) (hlam : ContinuousOn lam (Icc a b))
    (hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt w (lam x • (p + x • q)) (Icc a b) x)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    let u := rho + s * (∫ x in c..t, lam x);
    let v := t * u + s * (∫ x in c..t, lam x * (x - t));
    p0 + rho • (p + t • q) + s • (w t - w c) = p0 + u • p + v • q := by
  dsimp only
  rw [aligned_increment hw hlam hderiv hc ht]
  module

theorem aligned_footprint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℝ → E} {lam : ℝ → ℝ}
    {a b c t m rho R s M L d : ℝ} {p q p0 : E}
    (hw : ContinuousOn w (Icc a b)) (hlam : ContinuousOn lam (Icc a b))
    (hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt w (lam x • (p + x • q)) (Icc a b) x)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hbound : ∀ x ∈ Icc a b, |lam x| ≤ M)
    (htc : |t - c| ≤ d) (htm : |t - m| ≤ d / 2)
    (hs : |s| ≤ L) (hrho : 0 ≤ rho) (hR : rho ≤ R) :
    ∃ u v : ℝ,
      p0 + rho • (p + t • q) + s • (w t - w c) = p0 + u • p + v • q ∧
      -(L * M) * d ≤ u ∧ u ≤ R + (L * M) * d ∧
      |v - m * u| ≤ d / 2 * |u| + (L * M / 2) * d ^ 2 := by
  let u := rho + s * (∫ x in c..t, lam x)
  let v := t * u + s * (∫ x in c..t, lam x * (x - t))
  refine ⟨u, v, aligned_frozen_intercept hw hlam hderiv hc ht, ?_⟩
  exact integral_footprint hM hL hd
    (fun x hx => hbound x (uIcc_subset_Icc hc ht hx)) htc htm hs hrho hR

end CylinderCovering.RadialIntegral

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Triangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped BigOperators

namespace CylinderCovering.RadialTriangle

lemma mem_region_iff {l r m d : ℝ} {p : ℝ × ℝ} :
    p ∈ region l r m d ↔ l ≤ p.1 ∧ p.1 ≤ r ∧
      m * p.1 - d / 2 * (p.1-l) ≤ p.2 ∧
      p.2 ≤ m * p.1 + d / 2 * (p.1-l) := by
  simp only [region, mem_ofPred_eq, abs_le]
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> exact ⟨h₁, h₂, by linarith, by linarith⟩

lemma region_convex (l r m d : ℝ) : Convex ℝ (region l r m d) := by
  intro x hx y hy a b ha hb hab
  have hb_eq : b = 1-a := by linarith
  subst b
  rw [mem_region_iff] at hx hy ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx.1 ha, mul_le_mul_of_nonneg_left hy.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.1 ha, mul_le_mul_of_nonneg_left hy.2.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.2.1 ha,
      mul_le_mul_of_nonneg_left hy.2.2.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.2.2 ha,
      mul_le_mul_of_nonneg_left hy.2.2.2 hb]

lemma vertices_mem_region {l r m d : ℝ} (hlr : l ≤ r) (hd : 0 ≤ d)
    (i : Fin 3) : vertices l r m d i ∈ region l r m d := by
  have hwidth : 0 ≤ d / 2 * (r-l) := mul_nonneg (by positivity) (sub_nonneg.mpr hlr)
  rw [mem_region_iff]
  fin_cases i <;> norm_num [vertices] <;> (try constructor) <;> nlinarith

lemma region_eq_convexHull {l r m d : ℝ} (hlr : l < r) (hd : 0 < d) :
    region l r m d = convexHull ℝ (range (vertices l r m d)) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨hu₁, hu₂, hv₁, hv₂⟩ := mem_region_iff.mp hp
    let w : Fin 3 → ℝ := ![(r-p.1)/(r-l),
      (d/2*(p.1-l) - (p.2-m*p.1))/(d*(r-l)),
      (d/2*(p.1-l) + (p.2-m*p.1))/(d*(r-l))]
    have hrl : r-l ≠ 0 := ne_of_gt (sub_pos.mpr hlr)
    have hdd : d ≠ 0 := ne_of_gt hd
    have hden : 0 < d*(r-l) := mul_pos hd (sub_pos.mpr hlr)
    refine mem_convexHull_of_exists_fintype w (vertices l r m d) ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · exact div_nonneg (sub_nonneg.mpr hu₂) (sub_pos.mpr hlr).le
      · change 0 ≤ (d/2*(p.1-l) - (p.2-m*p.1))/(d*(r-l))
        exact div_nonneg (by linarith) hden.le
      · change 0 ≤ (d/2*(p.1-l) + (p.2-m*p.1))/(d*(r-l))
        exact div_nonneg (by linarith) hden.le
    · simp [w, Fin.sum_univ_succ]
      field_simp [hrl, hdd]
      ring
    · exact fun i => mem_range_self i
    · ext <;> simp [w, vertices, Fin.sum_univ_succ]
      all_goals field_simp [hrl, hdd]
      all_goals ring
  · refine convexHull_min ?_ (region_convex l r m d)
    rintro _ ⟨i, rfl⟩
    exact vertices_mem_region hlr.le hd.le i

end CylinderCovering.RadialTriangle

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace RadialProjection
open TriangularCovering Set MeasureTheory
open scoped InnerProductSpace

theorem collar_projection_area (p₀ e a b w : Space) (l r m d : ℝ)
    (he : ‖e‖ = 1) (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) (hd : 0 ≤ d) :
    area (projection (TriangularCovering.unit (e + w)) '' triangle
      (p₀ + l • a + (m * l) • b)
      (p₀ + r • a + (m * r - d / 2 * (r - l)) • b)
      (p₀ + r • a + (m * r + d / 2 * (r - l)) • b)) =
      Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) *
        d * (r - l) ^ 2 / (2 * Real.sqrt (1 + ‖w‖ ^ 2)) := by
  unfold area
  rw [projection_triangle_measure (unit_norm (sideways_ne_zero he hw)),
    ENNReal.toReal_ofReal (by positivity), collar_cross, inner_smul_right,
    abs_mul, abs_of_nonneg (mul_nonneg hd (sq_nonneg _)),
    normal_projection_factor he ha hb hw]
  ring

lemma coordinate_region_image (p₀ a b : Space) {l r m d : ℝ}
    (hlr : l < r) (hd : 0 < d) :
    coordinateAffine p₀ a b '' CylinderCovering.RadialTriangle.region l r m d =
      triangle (p₀ + l • a + (m * l) • b)
        (p₀ + r • a + (m * r - d / 2 * (r - l)) • b)
        (p₀ + r • a + (m * r + d / 2 * (r - l)) • b) := by
  rw [CylinderCovering.RadialTriangle.region_eq_convexHull hlr hd,
    (coordinateAffine p₀ a b).image_convexHull, triangle]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

end RadialProjection

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace CylinderCovering.RadialSweep

lemma scalar_le_bound (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    |D.lam t| ≤ scalarBound D := by
  exact le_csSup (isCompact_Icc.bddAbove_image D.scalar_continuous.abs) ⟨t, ht, rfl⟩

lemma cell_midpoint_bound (D : Data) {N : ℕ} {i : Fin N} {t : ℝ}
    (ht : t ∈ RadialRiemann.cell D.α D.β N i) :
    |t - midpoint D N i| ≤ RadialRiemann.step D.α D.β N / 2 := by
  have hstep := RadialRiemann.point_succ D.α D.β N i
  rw [abs_le]
  unfold midpoint
  constructor <;> linarith [ht.1, ht.2]

lemma frozenTriangle_eq (D : Data) (N : ℕ) (i : Fin N) :
    frozenTriangle D N i = TriangularCovering.triangle
      (coordinateMap D (leftTip D N, midpoint D N i * leftTip D N))
      (coordinateMap D (rightEdge D N i, midpoint D N i * rightEdge D N i -
        RadialRiemann.step D.α D.β N / 2 * (rightEdge D N i - leftTip D N)))
      (coordinateMap D (rightEdge D N i, midpoint D N i * rightEdge D N i +
        RadialRiemann.step D.α D.β N / 2 * (rightEdge D N i - leftTip D N))) := rfl

theorem localSweep_frozen_enclosure (D : Data) {N : ℕ} (i : Fin N) {c : ℝ}
    (hc : c ∈ RadialRiemann.cell D.α D.β N i) {z : Space}
    (hz : z ∈ localSweep D N i) :
    ∃ p ∈ frozenTriangle D N i, ∃ s : ℝ, z = p + s • (D.e + D.w c) := by
  obtain ⟨t, ht, ρ, hρ, s, hs, rfl⟩ := hz
  have hci := RadialRiemann.cell_subset D.interval_nonempty i hc
  have hti := RadialRiemann.cell_subset D.interval_nonempty i ht
  have hd := RadialRiemann.step_pos D.interval_nonempty (Nat.zero_lt_of_lt i.isLt)
  have htc : |t - c| ≤ RadialRiemann.step D.α D.β N := by
    simpa only [Real.dist_eq] using RadialRiemann.cell_dist_le ht hc
  have hR : ρ ≤ RadialRiemann.capMax D.R D.α D.β N i :=
    hρ.2.trans (RadialRiemann.le_capMax D.interval_nonempty D.cap_continuous ht)
  obtain ⟨u, v, huv, hu₀, hu₁, hv⟩ := RadialIntegral.aligned_footprint
    (p0 := D.p₀) D.velocity_continuous D.scalar_continuous D.aligned hci hti
    (scalarBound_nonneg D) D.length_pos.le hd.le (fun x hx => scalar_le_bound D hx)
    htc (cell_midpoint_bound D ht) hs hρ.1 hR
  have htri := RadialFreezing.footprint_subset_triangle
    (radialError_nonneg D) (div_nonneg (radialError_nonneg D) (by norm_num)) hd.le
    hu₀ hu₁ hv
  have hcollar : 2 * (radialError D + radialError D / 2) + 1 = collar D := by
    unfold collar
    ring
  rw [hcollar] at htri
  refine ⟨coordinateMap D (u, v), ?_, s, ?_⟩
  · rw [frozenTriangle_eq]
    simp only [coordinateMap]
    rw [← RadialProjection.coordinate_region_image D.p₀ D.a D.b
      (m := midpoint D N i) (leftTip_lt_rightEdge D (Nat.zero_lt_of_lt i.isLt) i) hd]
    refine ⟨(u, v), ?_, rfl⟩
    change leftTip D N ≤ u ∧ u ≤ rightEdge D N i ∧
      |v - midpoint D N i * u| ≤ RadialRiemann.step D.α D.β N / 2 * (u - leftTip D N)
    simpa only [leftTip, rightEdge, neg_mul, sub_neg_eq_add] using htri
  · dsimp [coordinateMap] at *
    calc
      D.p₀ + ρ • (D.a + t • D.b) + s • (D.e + D.w t) =
          (D.p₀ + ρ • (D.a + t • D.b) + s • (D.w t - D.w c)) +
            s • (D.e + D.w c) := by module
      _ = D.p₀ + u • D.a + v • D.b + s • (D.e + D.w c) := by rw [huv]

lemma frozenCylinder_axis (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    (frozenCylinder D N tag htag i).axis = direction D (tag i) := rfl

lemma frozenCylinder_base (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    (frozenCylinder D N tag htag i).base = frozenBase D N tag i := rfl

lemma frozenCylinder_area (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    TriangularCovering.area (frozenCylinder D N tag htag i).base = frozenArea D N tag i := by
  rw [frozenCylinder_base]
  have h := RadialProjection.collar_projection_area D.p₀ D.e D.a D.b (D.w (tag i))
    (leftTip D N) (rightEdge D N i) (midpoint D N i) (RadialRiemann.step D.α D.β N)
    D.normal_unit D.a_perp D.b_perp
    (D.velocity_perp (tag i) (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
    (RadialRiemann.step_pos D.interval_nonempty (Nat.zero_lt_of_lt i.isLt)).le
  change TriangularCovering.area (TriangularCovering.projection _ '' frozenTriangle D N i) = _
  rw [frozenTriangle_eq]
  change TriangularCovering.area (TriangularCovering.projection
    (TriangularCovering.unit (D.e + D.w (tag i))) '' _) = _
  simp only [coordinateMap]
  rw [show TriangularCovering.area
      (TriangularCovering.projection (TriangularCovering.unit (D.e + D.w (tag i))) ''
        TriangularCovering.triangle _ _ _) = _ from h]
  unfold frozenArea kappa leftTip rightEdge
  ring

lemma localSweep_mem_frozenCylinder (D : Data) {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) {z : Space}
    (hz : z ∈ localSweep D N i) : z ∈ (frozenCylinder D N tag htag i).carrier := by
  obtain ⟨p, hp, s, hz⟩ := localSweep_frozen_enclosure D i (htag i) hz
  exact TriangularCovering.projectedCylinder_mem_direction
    (D.e + D.w (tag i))
    (direction_ne_zero D (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
    (frozenVertices D N i 0) (frozenVertices D N i 1) (frozenVertices D N i 2)
    (frozen_nondegenerate D tag htag i) hp s hz

theorem aligned_radial_sweep : AlignedStatement := by
  intro D tag htag
  refine ⟨fun N => frozenCylinder D N (tag N) (htag N), ?_, ?_⟩
  · intro N hN
    constructor
    · intro i
      exact ⟨frozenCylinder_axis D N (tag N) (htag N) i,
        frozenCylinder_base D N (tag N) (htag N) i,
        frozenCylinder_area D N (tag N) (htag N) i⟩
    · rintro z ⟨t, ht, ρ, hρ, s, hs, hz⟩
      obtain ⟨i, hi⟩ := RadialRiemann.exists_cell hN ht
      exact ⟨i, localSweep_mem_frozenCylinder D (tag N) (htag N) i
        ⟨t, hi, ρ, hρ, s, hs, hz⟩⟩
  · convert frozenArea_tendsto D tag htag using 1
    all_goals try with_reducible_and_instances rfl
    funext N
    apply Finset.sum_congr rfl
    intro i _
    exact frozenCylinder_area D N (tag N) (htag N) i

end CylinderCovering.RadialSweep

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_ActualSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section
namespace RadialActualSweep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem compact_projected_image (u : E) {S : Set E} (hS : IsCompact S) :
    IsCompact ((fun x : E => x - (inner ℝ u x) • u) '' S) := by
  apply hS.image
  exact continuous_id.sub ((continuous_const.inner continuous_id).smul continuous_const)

theorem projected_image_perpendicular {u : E} (hu : ‖u‖ = 1) (S : Set E) :
    ∀ z ∈ (fun x : E => x - (inner ℝ u x) • u) '' S, inner ℝ u z = 0 := by
  rintro z ⟨x, hx, rfl⟩
  simp [inner_sub_right, inner_smul_right, hu]

theorem subset_projected_cylinder (u : E) (S : Set E) :
    S ⊆ {x | ∃ b ∈ (fun y : E => y - (inner ℝ u y) • u) '' S,
      ∃ r : ℝ, x = b + r • u} := by
  intro x hx
  exact ⟨x - (inner ℝ u x) • u, ⟨x, hx, rfl⟩, inner ℝ u x, by simp⟩

theorem projection_add_axis {u : E} (hu : ‖u‖ = 1) (x : E) (r : ℝ) :
    (x + r • u) - (inner ℝ u (x + r • u)) • u = x - (inner ℝ u x) • u := by
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hu,
    one_pow, mul_one, add_smul]
  abel

theorem projected_image_subset_of_intercepts {u : E} (hu : ‖u‖ = 1)
    {S T : Set E}
    (hST : ∀ x ∈ S, ∃ t ∈ T, ∃ r : ℝ, x = t + r • u) :
    (fun x : E => x - (inner ℝ u x) • u) '' S ⊆
      (fun x : E => x - (inner ℝ u x) • u) '' T := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨t, ht, r, rfl⟩ := hST x hx
  exact ⟨t, ht, (projection_add_axis hu t r).symm⟩

theorem limsup_le_of_nonneg_of_le_tendsto {cost bound : ℕ → ℝ} {A : ℝ}
    (hcost : ∀ n, 0 ≤ cost n) (hle : cost ≤ᶠ[atTop] bound)
    (hbound : Tendsto bound atTop (𝓝 A)) :
    limsup cost atTop ≤ A := by
  calc
    limsup cost atTop ≤ limsup bound atTop :=
      limsup_le_limsup hle (isCoboundedUnder_le_of_le atTop hcost)
        hbound.isBoundedUnder_le
    _ = A := hbound.limsup_eq

theorem compact_radial_sweep {J : Set ℝ} (hJ : IsCompact J)
    (R : ℝ → ℝ) (w : ℝ → E) (hR : ContinuousOn R J) (hw : ContinuousOn w J)
    (hRnonneg : ∀ t ∈ J, 0 ≤ R t) (p₀ a b e : E) (L : ℝ) :
    IsCompact {x : E | ∃ t ∈ J, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ R t ∧
      ∃ s : ℝ, |s| ≤ L ∧ x = p₀ + ρ • (a + t • b) + s • (e + w t)} := by
  let D : Set (ℝ × ℝ × ℝ) := J ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (-L) L)
  let F : ℝ × ℝ × ℝ → E := fun p =>
    p₀ + (p.2.1 * R p.1) • (a + p.1 • b) + p.2.2 • (e + w p.1)
  have hD : IsCompact D := hJ.prod (isCompact_Icc.prod isCompact_Icc)
  have hRD : ContinuousOn (fun p : ℝ × ℝ × ℝ => R p.1) D :=
    hR.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hwD : ContinuousOn (fun p : ℝ × ℝ × ℝ => w p.1) D :=
    hw.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hF : ContinuousOn F D := by
    dsimp [F]
    exact (continuousOn_const.add
      ((continuous_snd.fst.continuousOn.mul hRD).smul
        (continuousOn_const.add (continuous_fst.continuousOn.smul continuousOn_const)))).add
      (continuous_snd.snd.continuousOn.smul (continuousOn_const.add hwD))
  have heq : F '' D = {x : E | ∃ t ∈ J, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ R t ∧
      ∃ s : ℝ, |s| ≤ L ∧ x = p₀ + ρ • (a + t • b) + s • (e + w t)} := by
    ext x
    constructor
    · rintro ⟨⟨t, q, s⟩, hp, rfl⟩
      rcases hp with ⟨ht, hq, hs⟩
      exact ⟨t, ht, q * R t, mul_nonneg hq.1 (hRnonneg t ht),
        by simpa using mul_le_mul_of_nonneg_right hq.2 (hRnonneg t ht), s, abs_le.mpr hs, rfl⟩
    · rintro ⟨t, ht, ρ, hρ, hρR, s, hs, rfl⟩
      by_cases hRt : R t = 0
      · have hρ0 : ρ = 0 := by linarith
        refine ⟨(t, 0, s), ⟨ht, ⟨by norm_num, by norm_num⟩, abs_le.mp hs⟩, ?_⟩
        simp [F, hρ0]
      · have hRtpos : 0 < R t := lt_of_le_of_ne (hRnonneg t ht) (Ne.symm hRt)
        refine ⟨(t, ρ / R t, s), ⟨ht, ⟨div_nonneg hρ hRtpos.le,
          (div_le_one hRtpos).mpr hρR⟩, abs_le.mp hs⟩, ?_⟩
        simp [F, div_mul_cancel₀ ρ hRt]
  rw [← heq]
  exact hD.image_of_continuousOn hF

end RadialActualSweep

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_PartitionCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace CylinderCovering.RadialPartitionCover

theorem exists_interval_in_chain (p : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Icc (p 0) (p N)) :
    ∃ i : ℕ, i < N ∧ t ∈ Icc (p i) (p (i + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by omega, ht⟩
    · by_cases htN : t ≤ p N
      · obtain ⟨i, hi, hti⟩ := ih (Nat.pos_of_ne_zero hzero) ⟨ht.1, htN⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, hti⟩
      · exact ⟨N, Nat.lt_succ_self N, ⟨(lt_of_not_ge htN).le, ht.2⟩⟩

theorem iUnion_intervals_eq (p : ℕ → ℝ) (hp : Monotone p)
    {N : ℕ} (hN : 0 < N) :
    (⋃ i : Fin N, Icc (p i) (p (i + 1))) = Icc (p 0) (p N) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ⟨(hp (Nat.zero_le i)).trans hi.1,
      hi.2.trans (hp (Nat.succ_le_of_lt i.isLt))⟩
  · intro ht
    obtain ⟨i, hi, hti⟩ := exists_interval_in_chain p hN ht
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hti⟩

open RadialRiemann

theorem equal_cells_cover {a b : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 0 < N) :
    (⋃ i : Fin N, cell a b N i) = Icc a b := by
  have hd : 0 ≤ step a b N := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N)
  have hp : Monotone (point a b N) := by
    intro i j hij
    dsimp [point]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) hd)
  have hlast : point a b N N = b := by
    have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    dsimp [point, step]
    field_simp
    ring
  have h := iUnion_intervals_eq (point a b N) hp hN
  rw [hlast] at h
  simpa only [cell, point, Nat.cast_zero, zero_mul, add_zero] using h

theorem cell_subset_interval {a b : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 0 < N)
    (i : Fin N) : cell a b N i ⊆ Icc a b := by
  intro t ht
  rw [← equal_cells_cover hab hN]
  exact mem_iUnion.mpr ⟨i, ht⟩

end CylinderCovering.RadialPartitionCover

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_ActualEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
noncomputable section
namespace CylinderCovering.RadialSweep

theorem raw_direction_ne_zero (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    D.e + D.w t ≠ 0 := by
  intro h
  have hh := congrArg (fun x => inner ℝ D.e x) h
  simp only [inner_add_right, real_inner_self_eq_norm_sq, D.normal_unit,
    one_pow, D.velocity_perp t ht, add_zero, inner_zero_right] at hh
  norm_num at hh

theorem actual_direction_unit (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    ‖direction D t‖ = 1 := by
  have hn : ‖D.e + D.w t‖ ≠ 0 := norm_ne_zero_iff.mpr (raw_direction_ne_zero D ht)
  rw [direction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]

theorem localSweep_compact (D : Data) {N : ℕ} (hN : 0 < N) (i : Fin N) :
    IsCompact (localSweep D N i) := by
  have hsub := RadialPartitionCover.cell_subset_interval D.interval_nonempty.le hN i
  simpa only [localSweep, mem_Icc, and_assoc] using
    _root_.OAI.RadialActualSweep.compact_radial_sweep
      (show IsCompact (RadialRiemann.cell D.α D.β N i) from isCompact_Icc)
      D.R D.w (D.cap_continuous.mono hsub) (D.velocity_continuous.mono hsub)
      (fun t ht => D.cap_nonneg t (hsub ht)) D.p₀ D.a D.b D.e D.L

theorem iUnion_localSweep (D : Data) {N : ℕ} (hN : 0 < N) :
    (⋃ i : Fin N, localSweep D N i) = sweep D := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, t, ht, ρ, hρ, s, hs, hz⟩ := mem_iUnion.mp hz
    exact ⟨t, RadialPartitionCover.cell_subset_interval D.interval_nonempty.le hN i ht,
      ρ, hρ, s, hs, hz⟩
  · rintro ⟨t, ht, ρ, hρ, s, hs, hz⟩
    rw [← RadialPartitionCover.equal_cells_cover D.interval_nonempty.le hN] at ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨i, t, hi, ρ, hρ, s, hs, hz⟩

theorem actualBase_compact (D : Data) {N : ℕ} (hN : 0 < N)
    (tag : Fin N → ℝ) (i : Fin N) : IsCompact (actualBase D N tag i) :=
  _root_.OAI.RadialActualSweep.compact_projected_image _ (localSweep_compact D hN i)

theorem actualBase_covers (D : Data) {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ) :
    ∀ z ∈ sweep D, ∃ i : Fin N,
      z ∈ cylinder (direction D (tag i)) (actualBase D N tag i) := by
  intro z hz
  rw [← iUnion_localSweep D hN] at hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  exact ⟨i, _root_.OAI.RadialActualSweep.subset_projected_cylinder _ _ hi⟩

theorem actualSweepStatement_of_aligned
    (hAligned : AlignedStatement)
    (hlocal : ∀ (D : Data) (N : ℕ), 0 < N → ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag → ∀ i : Fin N,
        actualBase D N tag i ⊆ frozenBase D N tag i) :
    ActualSweepStatement := by
  intro D tag htag
  obtain ⟨C, hC, hlim⟩ := hAligned D tag htag
  have hbase (N : ℕ) (hN : 0 < N) (i : Fin N) :
      (C N i).base = frozenBase D N (tag N) i := ((hC N hN).1 i).2.1
  have hinc (N : ℕ) (hN : 0 < N) (i : Fin N) :
      actualBase D N (tag N) i ⊆ (C N i).base := by
    rw [hbase N hN i]
    exact hlocal D N hN (tag N) (htag N) i
  have hle (N : ℕ) (hN : 0 < N) :
      actualCost D N (tag N) ≤ TriangularCovering.totalArea (C N) := by
    apply Finset.sum_le_sum
    intro i _
    exact ENNReal.toReal_mono (C N i).finite_area (measure_mono (hinc N hN i))
  have hle_eventually : (fun N => actualCost D N (tag N)) ≤ᶠ[atTop]
      (fun N => TriangularCovering.totalArea (C N)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact hle N hN
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    refine ⟨?_, actualBase_covers D hN (tag N)⟩
    intro i
    have ht : tag N i ∈ Icc D.α D.β :=
      RadialPartitionCover.cell_subset_interval D.interval_nonempty.le hN i (htag N i)
    have hu : ‖direction D (tag N i)‖ = 1 := actual_direction_unit D ht
    have hc := actualBase_compact D hN (tag N) i
    refine ⟨hu, hc, hc.measurableSet, ?_, ?_, hlocal D N hN (tag N) (htag N) i⟩
    · exact ne_top_of_le_ne_top (C N i).finite_area (measure_mono (hinc N hN i))
    · exact _root_.OAI.RadialActualSweep.projected_image_perpendicular hu (localSweep D N i)
  · intro ε hε
    have hupper : ∀ᶠ N in atTop, TriangularCovering.totalArea (C N) < weightedArea D + ε :=
      hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
    filter_upwards [hle_eventually, hupper] with N hN hupperN
    exact hN.trans hupperN.le
  · apply _root_.OAI.RadialActualSweep.limsup_le_of_nonneg_of_le_tendsto
    · intro N
      exact Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
    · exact hle_eventually
    · exact hlim

theorem actualBase_subset_frozenBase (D : Data) {N : ℕ}
    (tag : Fin N → ℝ) (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    actualBase D N tag i ⊆ frozenBase D N tag i := by
  apply _root_.OAI.RadialActualSweep.projected_image_subset_of_intercepts
    (direction_unit D (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
  intro z hz
  obtain ⟨p, hp, s, hz⟩ := localSweep_frozen_enclosure D i (htag i) hz
  refine ⟨p, hp, s * ‖D.e + D.w (tag i)‖, ?_⟩
  rw [hz, direction, smul_smul]
  congr 1
  congr 1
  have hn : ‖D.e + D.w (tag i)‖ ≠ 0 := norm_ne_zero_iff.mpr
    (direction_ne_zero D (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
  field_simp

theorem actual_radial_sweep : ActualSweepStatement := by
  apply actualSweepStatement_of_aligned aligned_radial_sweep
  intro D N hN tag htag i
  exact actualBase_subset_frozenBase D tag htag i

end CylinderCovering.RadialSweep

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Nilpotent_C1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RuledApproximation

theorem nilpotentC1 :
  ∀ (D : Set Plane) (G : Plane → Plane), IsCompact D → SmoothNear 1 D G →
    (∀ b ∈ D, (fderiv ℝ G b).comp (fderiv ℝ G b) = 0) →
    ∀ h eps : ℝ, 0 < h → 0 < eps →
    ∃ n : ℕ, ∃ T : Fin n → Set Plane, ∃ g : Fin n → Plane,
      (∀ i, IsSquareTile (T i)) ∧
      physicalRuled 1 D G 1 ⊆ ⋃ i, auxiliaryCylinder (T i) (g i) ∧
      (∑ i, volume.real (T i) * physicalWeight h (g i)) ≤
        (∫ b in D, physicalWeight h (G b)) + eps ∧
      ∀ a : ℝ, ∃ C₁ C₂ : Fin n → Cylinder,
        (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
          (C₁ i).carrier = firstPhysicalMap h '' auxiliaryCylinder (T i) (g i) ∧
          (C₂ i).carrier = secondPhysicalMap h a '' auxiliaryCylinder (T i) (g i) ∧
          (C₁ i).area = h * volume.real (T i) * physicalWeight h (g i) ∧
          (C₂ i).area = h * volume.real (T i) * physicalWeight h (g i)) := by
  intro D G hD hG hnil h eps hh heps
  obtain ⟨n,C,hC,hcov,hcost⟩ := nilpotent_physical_cover hh hD hG hnil (mul_pos hh heps)
  choose T g hT hCT using hC
  refine ⟨n,T,g,hT,?_,?_,?_⟩
  · intro z hz
    have hz' : firstPhysicalMap h z ∈ physicalRuled h D G 1 := by
      rw [← firstPhysicalMap_ruled]
      exact mem_image_of_mem _ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hz')
    rw [hCT i,projectedCylinder_carrier] at hi
    obtain ⟨x,hx,hx'⟩ := hi
    have he : x = z := firstPhysicalMap_injective hh.ne' hx'
    exact mem_iUnion.mpr ⟨i, he ▸ hx⟩
  · simp_rw [familyArea,hCT,projectedCylinder_area hh] at hcost
    have he : (∑ i, h * volume.real (T i) * physicalWeight h (g i)) =
        h * ∑ i, volume.real (T i) * physicalWeight h (g i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hcost
    nlinarith
  · intro a
    let C₁ : Fin n → Cylinder := fun i => projectedCylinder h (g i) (T i)
    let C₂ : Fin n → Cylinder := fun i =>
      ((C₁ i).rotate swapReflect).translate (vec3 0 0 (h*a))
    refine ⟨C₁,C₂,fun i => ?_⟩
    have hP : (C₁ i).parallelogram := projectedCylinder_parallelogram hh _ (hT i).parallelogram
    refine ⟨hP,Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram hP swapReflect) _,
      projectedCylinder_carrier h _ _,?_,projectedCylinder_area hh _ _,?_⟩
    · dsimp only [C₂]
      rw [Cylinder.translate_carrier,Cylinder.rotate_carrier,projectedCylinder_carrier,
        ← image_comp,← image_comp]
      congr 1
      funext z
      exact (physicalMaps_relation h a z).symm
    · dsimp only [C₂]
      rw [Cylinder.translate_area,Cylinder.rotate_area]
      exact projectedCylinder_area hh _ _

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Results
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CylinderCovering

theorem nilpotentC1 : RuledApproximation.NilpotentC1Statement :=
  RuledApproximation.nilpotentC1

theorem angularExplicit : AngularExplicitStatement :=
  ⟨TriangularCovering.angularArea_result, TriangularCovering.explicitAngular_result⟩

theorem radialAligned : RadialSweep.AlignedStatement := RadialSweep.aligned_radial_sweep

theorem radialActualSweep : RadialSweep.ActualSweepStatement :=
  RadialSweep.actual_radial_sweep

theorem regularParallelogramCounterexample : RegularParallelogramCounterexampleStatement :=
  regularParallelogramCounterexample_result

theorem regularOpenCounterexample : RegularOpenCounterexampleStatement :=
  regularOpenCounterexample_result

end CylinderCovering

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CylinderCovering

theorem fourPaperMain_oai :
    AngularExplicitStatement ∧
    RuledApproximation.HyperbolicStatement ∧
    RuledApproximation.NilpotentC1Statement ∧
    RegularParallelogramCounterexampleStatement ∧
    RegularOpenCounterexampleStatement ∧
    RadialSweep.AlignedStatement ∧
    RadialSweep.ActualSweepStatement := by
  exact ⟨angularExplicit, ruledHistorical.1, nilpotentC1,
    regularParallelogramCounterexample, regularOpenCounterexample,
    radialAligned, radialActualSweep⟩

end CylinderCovering

end OAI
end

theorem solution : type_of% @OAI.CylinderCovering.fourPaperMain_oai := @OAI.CylinderCovering.fourPaperMain_oai

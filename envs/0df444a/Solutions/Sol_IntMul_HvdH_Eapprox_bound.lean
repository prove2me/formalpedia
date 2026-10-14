-- Prove2me | solution 1 for IntMul.HvdH.Eapprox_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T00:01:41.183974+00:00
-- url     : https://prove2.me/submissions/3dc8bde6-c88f-4d53-b7f5-48fb2eb650a7

import Definitions.Def_IntMul_HvdH_EApprox
import Theorems.Thm_IntMul_HvdH_expNeg_bound

open Complex

namespace IntMul.HvdH.EPf
open IntMul.HvdH

/-- A pair of integers as a Gaussian integer in `ℂ`. -/
def toC (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

@[simp] lemma toC_re (p : ℤ × ℤ) : (toC p).re = p.1 := by simp [toC]
@[simp] lemma toC_im (p : ℤ × ℤ) : (toC p).im = p.2 := by simp [toC]

lemma norm_le_of_re_im {z : ℂ} {c : ℝ} (hre : |z.re| ≤ c) (him : |z.im| ≤ c) :
    ‖z‖ ≤ 3 / 2 * c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hre
  have h1 : z.re ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h2 : z.im ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have : ‖z‖ ^ 2 ≤ (3 / 2 * c) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this

lemma tdiv_err (m D : ℤ) (hD : 0 < D) : |((m.tdiv D : ℤ) : ℝ) - (m : ℝ) / D| ≤ 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 := Int.tmod_lt_of_pos m hD
  have h2 := Int.lt_tmod_of_pos m hD
  rw [Int.tmod_def] at h1 h2
  have h1' : (m : ℝ) - D * (m.tdiv D : ℤ) < D := by exact_mod_cast h1
  have h2' : -(D : ℝ) < m - D * (m.tdiv D : ℤ) := by exact_mod_cast h2
  have e : ((m.tdiv D : ℤ) : ℝ) - (m : ℝ) / D = -((m - D * (m.tdiv D : ℤ)) / D) := by
    field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos hD', div_le_one hD', abs_le]
  constructor <;> linarith

lemma natdiv_bound (m n : ℕ) (hn : 0 < n) : |((m / n : ℕ) : ℝ) - (m : ℝ) / n| ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((m / n : ℕ) : ℝ) * n ≤ m := by exact_mod_cast Nat.div_mul_le_self m n
  have h2 : (m : ℝ) < ((m / n : ℕ) + 1 : ℝ) * n := by
    have := Nat.lt_mul_div_succ m hn
    have : (m : ℝ) < (n : ℝ) * ((m / n : ℕ) + 1 : ℝ) := by exact_mod_cast this
    linarith
  have h3 : (m : ℝ) / n < (m / n : ℕ) + 1 := by rw [div_lt_iff₀ hn']; linarith
  have h4 : ((m / n : ℕ) : ℝ) ≤ m / n := by rw [le_div_iff₀ hn']; linarith
  rw [abs_le]; constructor <;> linarith

/-- The exact weight `e_j = e^{-π (j - sk/t)² / α²}`. -/
lemma hasSum_geom_int {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs) ((1 + r) / (1 - r)) := by
  have h1 : HasSum (fun n : ℕ => r ^ ((n : ℤ).natAbs)) (1 / (1 - r)) := by
    simpa [one_div] using hasSum_geometric_of_lt_one hr0 hr1
  have h2 : HasSum (fun n : ℕ => r ^ ((-((n : ℤ) + 1)).natAbs)) (r / (1 - r)) := by
    have e : (fun n : ℕ => r ^ ((-((n : ℤ) + 1)).natAbs)) = fun n : ℕ => r * r ^ n := by
      funext n; rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ, mul_comm]
    rw [e, div_eq_mul_inv]; exact (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have : 1 - r ≠ 0 := by linarith
  rw [show (1 + r) / (1 - r) = 1 / (1 - r) + r / (1 - r) by field_simp]
  exact h1.of_nat_of_neg_add_one h2

lemma exp_neg_pi_half_le : Real.exp (-Real.pi / 2) ≤ 1 / 4.3 := by
  have hpi := Real.pi_gt_d2
  have h := Real.quadratic_le_exp_of_nonneg (x := Real.pi / 4) (by positivity)
  have e : Real.exp (Real.pi / 2) = Real.exp (Real.pi / 4) * Real.exp (Real.pi / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hq : 2.09 ≤ Real.exp (Real.pi / 4) := by nlinarith
  have h2 : 4.3 ≤ Real.exp (Real.pi / 2) := by rw [e]; nlinarith
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.exp_neg, inv_eq_one_div,
    div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith


lemma ceilSqrt_sq (p : ℕ) : p ≤ ceilSqrt p * ceilSqrt p := by
  unfold ceilSqrt
  split_ifs with h
  · exact (Nat.lt_succ_sqrt p).le
  · push Not at h; exact h


lemma bOf_bounds (s t : ℕ) (hs : 0 < s) (l : ℤ) :
    -(s : ℤ) ≤ 2 * bOf s t l ∧ 2 * bOf s t l < s := by
  have hs2 : (0 : ℤ) < 2 * s := by omega
  have h1 := Int.ediv_mul_le (2 * t * l + s) hs2.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (2 * t * l + s) hs2
  unfold bOf
  generalize (2 * (t : ℤ) * l + s) / (2 * s) = q at h1 h2 ⊢
  constructor <;> nlinarith

lemma eKz_lower (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) (l h : ℤ) (hh : h ≠ 0) :
    (s : ℤ) ^ 2 * (|h| * (|h| - 1)) ≤ eKz s t l h := by
  obtain ⟨a1, a2⟩ := bOf_bounds s t hs l
  obtain ⟨c1, c2⟩ := bOf_bounds s t hs (l + h)
  unfold eKz
  set b1 := bOf s t l
  set b2 := bOf s t (l + h)
  have ha : 1 ≤ |h| := Int.one_le_abs hh
  have hb1 : 2 * |b1| ≤ s := by cases abs_cases b1 <;> omega
  have hb2 : 2 * |b2| ≤ s := by cases abs_cases b2 <;> omega
  have htR : (s : ℤ) ≤ t := by exact_mod_cast hst
  have e1 : |(t : ℤ) * h| = t * |h| := by rw [abs_mul, abs_of_nonneg (by positivity)]
  have e2 : |(t : ℤ) * h| ≤ |t * h + b1| + |b1| := by
    have := abs_sub_abs_le_abs_sub ((t : ℤ) * h) (-b1)
    rw [abs_neg, sub_neg_eq_add] at this; linarith
  set X := |(t : ℤ) * h + b1|
  have hX : (s : ℤ) * (2 * |h| - 1) ≤ 2 * X := by nlinarith
  have hX0 : 0 ≤ (s : ℤ) * (2 * |h| - 1) := mul_nonneg (by positivity) (by linarith)
  have hsq : ((s : ℤ) * (2 * |h| - 1)) ^ 2 ≤ (2 * X) ^ 2 := pow_le_pow_left₀ hX0 hX 2
  have hX2 : ((t : ℤ) * h + b1) ^ 2 = X ^ 2 := (sq_abs _).symm
  have hb2sq : 4 * b2 ^ 2 ≤ (s : ℤ) ^ 2 := by
    have : (2 * |b2|) ^ 2 ≤ (s : ℤ) ^ 2 := pow_le_pow_left₀ (by positivity) hb2 2
    nlinarith [sq_abs b2]
  nlinarith

lemma eEx_nonneg (s t α : ℕ) (l h : ℤ) : 0 ≤ eEx s t α l h := by
  unfold eEx; split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

/-- For `h ≠ 0`, `e_{ℓ,h} ≤ e^{-πα² |h|(|h|-1)}`. -/
lemma eEx_le (s t α : ℕ) (hs : 0 < s) (hst : s ≤ t) (l h : ℤ) (hh : h ≠ 0) :
    eEx s t α l h ≤ Real.exp (-(Real.pi * α ^ 2 * ((h.natAbs : ℝ) * (h.natAbs - 1)))) := by
  unfold eEx; rw [if_neg hh]
  apply Real.exp_le_exp.2
  have hK := eKz_lower s t hs hst l h hh
  have hK' : (s : ℝ) ^ 2 * ((h.natAbs : ℝ) * (h.natAbs - 1)) ≤ (eKz s t l h : ℝ) := by
    have hn : (h.natAbs : ℝ) = ((|h| : ℤ) : ℝ) := by rw [Nat.cast_natAbs]
    rw [hn]; exact_mod_cast hK
  have hsR : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  have : Real.pi * α ^ 2 * ((h.natAbs : ℝ) * (h.natAbs - 1)) ≤ Real.pi * α ^ 2 * (eKz s t l h : ℝ) / s ^ 2 := by
    rw [le_div_iff₀ hsR]
    have := mul_le_mul_of_nonneg_left hK' (by positivity : (0 : ℝ) ≤ Real.pi * α ^ 2)
    linarith
  linarith

lemma eEx_le_one (s t α : ℕ) (hs : 0 < s) (hst : s ≤ t) (l h : ℤ) : eEx s t α l h ≤ 1 := by
  by_cases hh : h = 0
  · simp [eEx, hh]
  · refine (eEx_le s t α hs hst l h hh).trans (Real.exp_le_one_iff.2 ?_)
    have : (1 : ℝ) ≤ h.natAbs := by exact_mod_cast Int.natAbs_pos.2 hh
    have : 0 ≤ Real.pi * α ^ 2 * ((h.natAbs : ℝ) * (h.natAbs - 1)) := by
      apply mul_nonneg (by positivity); nlinarith
    linarith

/-- Per-term error: `‖eTerm h - 2^p e_{ℓ,h} u_{ℓ+h}‖ ≤ 5/2` (in units of `2^{-p}`). -/
lemma eTerm_err (p s t α l : ℕ) (hs : 0 < s) (hst : s ≤ t) (U : ℕ → ℤ × ℤ)
    (hU : ∀ i, ‖toC (U i)‖ ≤ 2 ^ p) (h : ℤ) :
    ‖toC (eTerm p s t α l U h) -
      2 ^ p * (((eEx s t α l h : ℝ) : ℂ) * (toC (U ((l + h) % s).toNat) / 2 ^ p))‖ ≤ 5 / 2 := by
  by_cases hh : h = 0
  · simp [eTerm, eEx, hh, toC]; norm_num
  set V := U ((l + h) % s).toNat
  set e := eEx s t α l h
  have he0 : 0 ≤ e := eEx_nonneg s t α l h
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hK0 : 0 ≤ eKz s t l h := by
    have := eKz_lower s t hs hst l h hh
    have ha : 1 ≤ |h| := Int.one_le_abs hh
    have : 0 ≤ (s : ℤ) ^ 2 * (|h| * (|h| - 1)) := by
      apply mul_nonneg (by positivity); nlinarith
    linarith
  set J : ℕ := α ^ 2 * (eKz s t l h).toNat
  have hx := expNeg_bound p (s ^ 2) J (by positivity)
  have hJ : Real.pi * (J : ℝ) / ((s ^ 2 : ℕ) : ℝ) = Real.pi * α ^ 2 * (eKz s t l h : ℝ) / s ^ 2 := by
    simp only [J]
    have : (((eKz s t l h).toNat : ℕ) : ℝ) = (eKz s t l h : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hK0
    push_cast; rw [this]; ring
  rw [hJ] at hx
  have hee : Real.exp (-(Real.pi * α ^ 2 * (eKz s t l h : ℝ) / s ^ 2)) = e := by
    simp only [e, eEx, if_neg hh]
  rw [hee] at hx
  set x := expNeg p (s ^ 2) J
  have hx' : |(x : ℝ) - 2 ^ p * e| ≤ 1 := hx
  have hT : eTerm p s t α l U h = ((x * V.1).tdiv (2 ^ p), (x * V.2).tdiv (2 ^ p)) := by
    simp only [eTerm, if_neg hh]; rfl
  rw [hT]
  have hpZ : (0 : ℤ) < 2 ^ p := by positivity
  have hround : ‖toC ((x * V.1).tdiv (2 ^ p), (x * V.2).tdiv (2 ^ p)) - (x : ℂ) * toC V / 2 ^ p‖ ≤ 3 / 2 := by
    have hsC : (((2 ^ p : ℤ) : ℝ) : ℂ) = (2 : ℂ) ^ p := by push_cast; rfl
    refine (norm_le_of_re_im (c := 1) ?_ ?_).trans (by norm_num)
    · rw [← hsC, Complex.sub_re, Complex.div_ofReal_re, toC_re]
      have h := tdiv_err (x * V.1) (2 ^ p) hpZ
      convert h using 2
      simp [toC]
    · rw [← hsC, Complex.sub_im, Complex.div_ofReal_im, toC_im]
      have h := tdiv_err (x * V.2) (2 ^ p) hpZ
      convert h using 2
      simp [toC]
  have happ : ‖(x : ℂ) * toC V / 2 ^ p - 2 ^ p * (((e : ℝ) : ℂ) * (toC V / 2 ^ p))‖ ≤ 1 := by
    have e2 : (x : ℂ) * toC V / 2 ^ p - 2 ^ p * (((e : ℝ) : ℂ) * (toC V / 2 ^ p))
        = ((((x : ℝ) - 2 ^ p * e) / 2 ^ p : ℝ) : ℂ) * toC V := by
      push_cast; field_simp
    rw [e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hp]
    calc |(x : ℝ) - 2 ^ p * e| / 2 ^ p * ‖toC V‖ ≤ 1 / 2 ^ p * 2 ^ p :=
          mul_le_mul (div_le_div_of_nonneg_right hx' hp.le) (hU _) (norm_nonneg _) (by positivity)
      _ = 1 := by field_simp
  calc _ ≤ ‖toC ((x * V.1).tdiv (2 ^ p), (x * V.2).tdiv (2 ^ p)) - (x : ℂ) * toC V / 2 ^ p‖
        + ‖(x : ℂ) * toC V / 2 ^ p - 2 ^ p * (((e : ℝ) : ℂ) * (toC V / 2 ^ p))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 / 2 + 1 := add_le_add hround happ
    _ = 5 / 2 := by norm_num

lemma eWidth_ge (p α : ℕ) (hα : 1 ≤ α) : ceilSqrt p ≤ α * (eWidth p α - 1) := by
  unfold eWidth
  have := Nat.lt_mul_div_succ (ceilSqrt p + α - 1) (show 0 < α by omega)
  simp only [Nat.add_sub_cancel]
  rw [mul_add, mul_one] at this
  generalize α * ((ceilSqrt p + α - 1) / α) = P at this ⊢
  omega

/-- Lemma 4.11: the truncated fixed-point sum approximates `2^p (E u)_ℓ` within `5m + 5`. -/
theorem Eapprox_bound (p s t α l : ℕ) (hs : 0 < s) (hst : s ≤ t) (hα : 1 ≤ α)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖toC (U i)‖ ≤ 2 ^ p) :
    ‖toC (Eapprox p s t α U l) - 2 ^ p * Eexact s t α (fun i => toC (U i) / 2 ^ p) l‖
      ≤ 5 * eWidth p α + 5 := by
  set m := eWidth p α with hmdef
  have hm1 : 1 ≤ m := by simp only [hmdef, eWidth]; exact Nat.le_add_left 1 _
  have hqm := eWidth_ge p α hα
  rw [← hmdef] at hqm
  set q := ceilSqrt p
  have hqp : p ≤ q * q := ceilSqrt_sq p
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hαR : (1 : ℝ) ≤ α := by exact_mod_cast hα
  set u : ℕ → ℂ := fun i => toC (U i) / 2 ^ p
  have hu : ∀ i, ‖u i‖ ≤ 1 := by
    intro i; simp only [u]; rw [norm_div, norm_pow, Complex.norm_two, div_le_one hp]; exact hU i
  set g : ℤ → ℂ := fun h => ((eEx s t α l h : ℝ) : ℂ) * u ((l + h) % s).toNat with hg
  have hgE : Eexact s t α u l = ∑' h, g h := rfl
  have hgn : ∀ h, ‖g h‖ ≤ eEx s t α l h := by
    intro h; simp only [hg]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (eEx_nonneg _ _ _ _ _)]
    calc eEx s t α l h * ‖u ((l + h) % s).toNat‖ ≤ eEx s t α l h * 1 :=
          mul_le_mul_of_nonneg_left (hu _) (eEx_nonneg _ _ _ _ _)
      _ = _ := mul_one _
  -- summability
  have hgsum : Summable g := by
    have hr1 : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
    have hsg := (hasSum_geom_int (Real.exp_pos (-Real.pi)).le hr1).summable.mul_left (Real.exp Real.pi)
    refine Summable.of_norm_bounded hsg (fun h => (hgn h).trans ?_)
    by_cases hh : h = 0
    · simp [eEx, hh]; positivity
    refine (eEx_le s t α hs hst l h hh).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hn : (1 : ℝ) ≤ h.natAbs := by exact_mod_cast Int.natAbs_pos.2 hh
    have : (h.natAbs : ℝ) - 1 ≤ α ^ 2 * ((h.natAbs : ℝ) * (h.natAbs - 1)) := by
      have h1 : (1 : ℝ) ≤ α ^ 2 := by nlinarith
      have h2 : 0 ≤ (h.natAbs : ℝ) - 1 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg (by linarith : (0:ℝ) ≤ h.natAbs) h2), mul_nonneg h2 h2]
    nlinarith [Real.pi_pos]
  -- the window
  set W : Finset ℤ := (Finset.range (2 * m + 1)).map
    ⟨fun i : ℕ => (i : ℤ) - m, fun a b h => by simpa using h⟩ with hW
  have hWmem : ∀ h, h ∉ W → m + 1 ≤ h.natAbs := by
    intro h hj
    by_contra hcon; push Not at hcon
    apply hj
    rw [hW, Finset.mem_map]
    refine ⟨(h + m).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · show (((h + m).toNat : ℕ) : ℤ) - m = h; omega
  have halg : toC (Eapprox p s t α U l) = ∑ h ∈ W, toC (eTerm p s t α l U h) := by
    rw [hW, Finset.sum_map]
    simp only [Eapprox, toC, Int.cast_sum, Function.Embedding.coeFn_mk]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    rfl
  rw [hgE, halg, ← hgsum.sum_add_tsum_compl (s := W), mul_add, Finset.mul_sum]
  have hsplit : ∑ h ∈ W, toC (eTerm p s t α l U h) - (∑ h ∈ W, 2 ^ p * g h + 2 ^ p * ∑' x : ↑(↑W : Set ℤ)ᶜ, g x)
      = ∑ h ∈ W, (toC (eTerm p s t α l U h) - 2 ^ p * g h) - 2 ^ p * ∑' x : ↑(↑W : Set ℤ)ᶜ, g x := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  -- window part
  have hwin : ‖∑ h ∈ W, (toC (eTerm p s t α l U h) - 2 ^ p * g h)‖ ≤ (2 * m + 1) * (5 / 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ h ∈ W, ‖toC (eTerm p s t α l U h) - 2 ^ p * g h‖ ≤ ∑ _h ∈ W, (5 / 2 : ℝ) :=
          Finset.sum_le_sum (fun h _ => eTerm_err p s t α l hs hst U hU h)
      _ = (2 * m + 1) * (5 / 2) := by
          rw [Finset.sum_const, hW, Finset.card_map, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  -- tail part
  set r : ℝ := Real.exp (-(Real.pi * α ^ 2 * m / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hmR1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hrq : r ≤ 1 / 4.3 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_pi_half_le
    have : (1 : ℝ) ≤ α ^ 2 * m := by nlinarith
    nlinarith [Real.pi_pos]
  have hr1 : r < 1 := by linarith
  set F : ℤ → ℝ := fun h => r ^ (m - 1) * r ^ h.natAbs with hF
  have hhas : HasSum F (r ^ (m - 1) * ((1 + r) / (1 - r))) :=
    (hasSum_geom_int hr0 hr1).mul_left _
  have htail : ‖∑' x : ↑(↑W : Set ℤ)ᶜ, g x‖ ≤ r ^ (m - 1) * ((1 + r) / (1 - r)) := by
    rw [tsum_subtype (↑W : Set ℤ)ᶜ g]
    refine tsum_of_norm_bounded hhas (fun h => ?_)
    by_cases hj : h ∈ (↑W : Set ℤ)ᶜ
    · rw [Set.indicator_of_mem hj]
      have hjW : h ∉ W := by simpa using hj
      have hn := hWmem h hjW
      have hh : h ≠ 0 := by omega
      refine (hgn h).trans ((eEx_le s t α hs hst l h hh).trans ?_)
      simp only [hF]
      rw [← pow_add, hr, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have hnR : (m : ℝ) + 1 ≤ h.natAbs := by exact_mod_cast hn
      have e : (((m - 1 + h.natAbs : ℕ)) : ℝ) = m - 1 + h.natAbs := by
        rw [Nat.cast_add, Nat.cast_sub hm1]; simp
      rw [e]
      have key : (m : ℝ) * (m - 1 + h.natAbs) / 2 ≤ (h.natAbs : ℝ) * (h.natAbs - 1) := by
        nlinarith
      have hpa : (0 : ℝ) ≤ Real.pi * α ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left key hpa
      have e2 : ((m : ℝ) - 1 + h.natAbs) * -(Real.pi * α ^ 2 * m / 2)
          = -(Real.pi * α ^ 2 * ((m : ℝ) * (m - 1 + h.natAbs) / 2)) := by ring
      rw [e2]; linarith
    · rw [Set.indicator_of_notMem hj, norm_zero]; simp only [hF]; positivity
  -- numerics: 2^p r^{m-1} ≤ 1
  have hrm : (2 : ℝ) ^ p * r ^ (m - 1) ≤ 1 := by
    have e1 : r ^ (m - 1) = Real.exp (((m - 1 : ℕ) : ℝ) * (-(Real.pi * α ^ 2 * m / 2))) := by
      rw [Real.exp_nat_mul]
    have e2 : (2 : ℝ) ^ p = Real.exp (p * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    rw [e1, e2, ← Real.exp_add, Real.exp_le_one_iff]
    have hm1R : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1]; simp
    rw [hm1R]
    have hqmR : (q : ℝ) ≤ α * ((m : ℝ) - 1) := by
      have : ((q : ℕ) : ℝ) ≤ ((α * (m - 1) : ℕ) : ℝ) := by exact_mod_cast hqm
      rw [Nat.cast_mul, Nat.cast_sub hm1] at this; simpa using this
    have hqpR : (p : ℝ) ≤ q * q := by exact_mod_cast hqp
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have h1 : (p : ℝ) ≤ (α * ((m : ℝ) - 1)) ^ 2 := by nlinarith
    have h2 : (α * ((m : ℝ) - 1)) ^ 2 ≤ α ^ 2 * m * ((m : ℝ) - 1) := by
      have : 0 ≤ (m : ℝ) - 1 := by linarith
      nlinarith [sq_nonneg (α : ℝ)]
    have hl := Real.log_two_lt_d9
    have hpi := Real.pi_gt_d2
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have h3 : Real.pi / 2 * (p : ℝ) ≤ Real.pi / 2 * (α ^ 2 * m * ((m : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    have e3 : ((m : ℝ) - 1) * -(Real.pi * α ^ 2 * m / 2) = -(Real.pi / 2 * (α ^ 2 * m * ((m : ℝ) - 1))) := by
      ring
    rw [e3]
    nlinarith [mul_le_mul_of_nonneg_left hl.le hp0]
  have hgeo : (1 + r) / (1 - r) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have htail2 : ‖(2 : ℂ) ^ p * ∑' x : ↑(↑W : Set ℤ)ᶜ, g x‖ ≤ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_two]
    calc (2 : ℝ) ^ p * ‖∑' x : ↑(↑W : Set ℤ)ᶜ, g x‖
        ≤ 2 ^ p * (r ^ (m - 1) * ((1 + r) / (1 - r))) := mul_le_mul_of_nonneg_left htail hp.le
      _ = (2 ^ p * r ^ (m - 1)) * ((1 + r) / (1 - r)) := by ring
      _ ≤ 1 * 2 := mul_le_mul hrm hgeo (by positivity) (by norm_num)
      _ = 2 := by norm_num
  linarith

end IntMul.HvdH.EPf

open IntMul.HvdH in
theorem solution (p s t α l : ℕ) (hs : 0 < s) (hst : s ≤ t) (hα : 1 ≤ α)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I‖ ≤ 2 ^ p) :
    ‖(((Eapprox p s t α U l).1 : ℂ) + ((Eapprox p s t α U l).2 : ℂ) * Complex.I) -
      2 ^ p * Eexact s t α (fun i => (((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I) / 2 ^ p) l‖
      ≤ 5 * eWidth p α + 5 :=
  IntMul.HvdH.EPf.Eapprox_bound p s t α l hs hst hα U hU

-- Prove2me | solution 1 for IntMul.HvdH.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-08T23:23:49.930992+00:00
-- url     : https://prove2.me/submissions/f7841614-857e-4f2c-af79-cca60f0429b7

import Mathlib
import Definitions.Def_IntMul_HvdH_Resampling

open Real IntMul.HvdH

namespace IntMulLemma46

lemma beta_abs (s t : ℕ) (j : ℤ) : |beta s t j| ≤ 1 / 2 := by
  unfold beta nearest
  set x : ℝ := (t : ℝ) * j / s
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]; constructor <;> linarith

lemma beta_periodic (s t : ℕ) (hs : (s : ℝ) ≠ 0) (j m : ℤ) :
    beta s t (j + m * s) = beta s t j := by
  unfold beta nearest
  have : (t : ℝ) * ((j + m * s : ℤ) : ℝ) / s = (t : ℝ) * j / s + ((m * t : ℤ) : ℝ) := by
    push_cast; field_simp
  rw [this, show (t : ℝ) * j / s + ((m * t : ℤ) : ℝ) + 1 / 2 = ((t : ℝ) * j / s + 1 / 2) + ((m * t : ℤ) : ℝ)
    by ring, Int.floor_add_intCast]
  push_cast; ring

/-- The exponent estimate of Lemma 4.6: for `h ≠ 0`,
`(ρh + β)² - β'² ≥ 2(ρ - 1)(|h| - 1/2)²` when `ρ ≥ 1` and `|β|, |β'| ≤ 1/2`. -/
lemma expo_bound (ρ β β' : ℝ) (hρ : 1 ≤ ρ) (hβ : |β| ≤ 1 / 2) (hβ' : |β'| ≤ 1 / 2)
    (h : ℤ) (hh : h ≠ 0) :
    2 * (ρ - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 ≤ (ρ * h + β) ^ 2 - β' ^ 2 := by
  have habs : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have hlow : ρ * (|(h : ℝ)| - 1 / 2) ≤ |ρ * h + β| := by
    have : |ρ * (h : ℝ)| - |β| ≤ |ρ * h + β| := by
      have := abs_sub_abs_le_abs_sub (ρ * (h : ℝ)) (-β); simpa [sub_neg_eq_add, abs_neg] using this
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < ρ)] at this
    nlinarith
  have hnn : 0 ≤ ρ * (|(h : ℝ)| - 1 / 2) := by nlinarith
  have hsq : (ρ * (|(h : ℝ)| - 1 / 2)) ^ 2 ≤ (ρ * h + β) ^ 2 := by
    rw [← sq_abs (ρ * h + β)]; exact pow_le_pow_left₀ hnn hlow 2
  have hβ'2 : β' ^ 2 ≤ 1 / 4 := by
    have := sq_abs β'; nlinarith [abs_nonneg β']
  have hq : 1 / 4 ≤ (|(h : ℝ)| - 1 / 2) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (ρ - 1)]

/-- `(n + 1/2)² ≥ 1/4 + 2n` for natural `n`. -/
lemma half_sq (n : ℕ) : 1 / 4 + 2 * (n : ℝ) ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
  have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  nlinarith

/-- `2.01 e^{-πx/2} < 2^{-x}` for `x ≥ 1`. -/
lemma second_ineq (x : ℝ) (hx : 1 ≤ x) : 2.01 * rexp (-π * x / 2) < (2 : ℝ) ^ (-x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpi := Real.pi_gt_three
  have hl2 := Real.log_two_lt_d9
  set y : ℝ := x * (π / 2 - Real.log 2)
  have hy : 0.8 ≤ y := by
    have : (0.8 : ℝ) ≤ π / 2 - Real.log 2 := by norm_num at hl2 ⊢; linarith
    calc (0.8 : ℝ) ≤ 1 * (π / 2 - Real.log 2) := by linarith
      _ ≤ x * (π / 2 - Real.log 2) := by apply mul_le_mul_of_nonneg_right hx; linarith
  have hey : (2.01 : ℝ) < rexp y := by
    have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ y)
    nlinarith
  have : rexp (Real.log 2 * -x) = rexp (-π * x / 2) * rexp y := by
    rw [← Real.exp_add]; congr 1; simp only [y]; ring
  rw [this]
  have := Real.exp_pos (-π * x / 2)
  nlinarith

/-- `2 / (1 - e^{-2c}) < 2.01` once `c ≥ 6`. -/
lemma geom_factor (c : ℝ) (hc : 6 ≤ c) : 2 / (1 - rexp (-2 * c)) < 2.01 := by
  have h4 : (13 : ℝ) ≤ rexp 4 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4); norm_num at this; linarith
  have h12 : (2197 : ℝ) ≤ rexp 12 := by
    have : rexp 12 = rexp 4 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have := pow_le_pow_left₀ (by norm_num) h4 3
    norm_num at this ⊢; linarith
  have hq : rexp (-2 * c) ≤ 1 / 2197 := by
    have : rexp (-2 * c) ≤ rexp (-12) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg] at this
    calc rexp (-2 * c) ≤ (rexp 12)⁻¹ := this
      _ ≤ 1 / 2197 := by rw [one_div]; exact inv_anti₀ (by norm_num) h12
  have hpos : 0 < 1 - rexp (-2 * c) := by linarith
  rw [div_lt_iff₀ hpos]; nlinarith

/-- The off-centre Gaussian tail used in Lemma 4.6. -/
noncomputable def tailFn (c : ℝ) (L : ℤ) (j : ℤ) : ℝ :=
  if j = L then 0 else rexp (-c * (|((j - L : ℤ) : ℝ)| - 1 / 2) ^ 2)

lemma tail_summable_and_le (c : ℝ) (hc : 0 < c) (L : ℤ) :
    Summable (tailFn c L) ∧ ∑' j, tailFn c L j ≤ 2 * rexp (-c / 4) / (1 - rexp (-2 * c)) := by
  set q : ℝ := rexp (-2 * c) with hq_def
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq_def, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  set φ : ℤ → ℝ := fun h => if h = 0 then 0 else rexp (-c * (|(h : ℝ)| - 1 / 2) ^ 2) with hφ
  have hshift : ∀ h : ℤ, tailFn c L (L + h) = φ h := by
    intro h; simp only [tailFn, hφ, add_sub_cancel_left, add_eq_left]
  have hφ0 : ∀ h, 0 ≤ φ h := by intro h; simp only [hφ]; split_ifs <;> positivity
  -- each half is dominated by e^{-c/4} q^n
  have hb : ∀ n : ℕ, rexp (-c * (((n : ℝ) + 1) - 1 / 2) ^ 2) ≤ rexp (-c / 4) * q ^ n := by
    intro n
    rw [hq_def, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := half_sq n
    have e : ((n : ℝ) + 1) - 1 / 2 = (n : ℝ) + 1 / 2 := by ring
    rw [e]; nlinarith
  have hpos : ∀ n : ℕ, φ ((n : ℤ) + 1) = rexp (-c * (((n : ℝ) + 1) - 1 / 2) ^ 2) := by
    intro n
    simp only [hφ]
    rw [if_neg (by omega)]
    congr 3; push_cast; rw [abs_of_nonneg (by positivity)]
  have hneg : ∀ n : ℕ, φ (-((n : ℤ) + 1)) = rexp (-c * (((n : ℝ) + 1) - 1 / 2) ^ 2) := by
    intro n
    simp only [hφ]
    rw [if_neg (by omega)]
    congr 3; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
  have hgeo : Summable fun n : ℕ => rexp (-c / 4) * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hs1 : Summable fun n : ℕ => φ ((n : ℤ) + 1) :=
    Summable.of_nonneg_of_le (fun n => hφ0 _) (fun n => (hpos n).le.trans (hb n)) hgeo
  have hs2 : Summable fun n : ℕ => φ (-((n : ℤ) + 1)) :=
    Summable.of_nonneg_of_le (fun n => hφ0 _) (fun n => (hneg n).le.trans (hb n)) hgeo
  have hs0 : Summable fun n : ℕ => φ (n : ℤ) := by
    rw [← summable_nat_add_iff 1]; simpa using hs1
  have hsZ : Summable φ := Summable.of_nat_of_neg_add_one hs0 (by simpa using hs2)
  have hsum_geo : ∑' n : ℕ, rexp (-c / 4) * q ^ n = rexp (-c / 4) / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]; exact (div_eq_mul_inv _ _).symm
  have hT : ∑' h : ℤ, φ h ≤ 2 * rexp (-c / 4) / (1 - q) := by
    rw [tsum_of_nat_of_neg_add_one hs0 (by simpa using hs2), hs0.tsum_eq_zero_add]
    have e0 : φ ((0 : ℕ) : ℤ) = 0 := by simp [hφ]
    have h1 : ∑' n : ℕ, φ (((n + 1 : ℕ) : ℤ)) ≤ rexp (-c / 4) / (1 - q) := by
      rw [← hsum_geo]
      refine Summable.tsum_le_tsum (fun n => ?_) (by simpa using hs1) hgeo
      have := hpos n; push_cast at this ⊢; rw [this]; exact hb n
    have h2 : ∑' n : ℕ, φ (-((n : ℤ) + 1)) ≤ rexp (-c / 4) / (1 - q) := by
      rw [← hsum_geo]
      exact Summable.tsum_le_tsum (fun n => (hneg n).le.trans (hb n)) hs2 hgeo
    rw [e0]
    have : 2 * rexp (-c / 4) / (1 - q) = rexp (-c / 4) / (1 - q) + rexp (-c / 4) / (1 - q) := by ring
    linarith
  have hcomp : tailFn c L = φ ∘ (Equiv.subRight L) := by
    funext j
    simp only [Function.comp_apply, Equiv.subRight_apply]
    rw [← hshift (j - L), add_sub_cancel]
  refine ⟨?_, ?_⟩
  · rw [hcomp]; exact (Equiv.summable_iff (Equiv.subRight L)).2 hsZ
  · rw [hcomp]
    show ∑' j, φ (Equiv.subRight L j) ≤ _
    rw [Equiv.tsum_eq (Equiv.subRight L) φ]
    exact hT

/-- Regrouping a complex sum over `ℤ` by residue classes mod `s`. -/
noncomputable def resEquiv (s : ℕ) [NeZero s] : ZMod s × ℤ ≃ ℤ :=
  Equiv.ofBijective (fun p => (p.1.val : ℤ) + p.2 * s) <| by
    constructor
    · rintro ⟨r, m⟩ ⟨r', m'⟩ h
      simp only at h
      have hr : r = r' := by
        have := congrArg (fun z : ℤ => (z : ZMod s)) h
        simpa using this
      subst hr
      have hs : (s : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne s
      have : m * s = m' * s := by linarith
      simp only [Prod.mk.injEq, true_and]
      exact mul_right_cancel₀ hs this
    · intro j
      refine ⟨((j : ZMod s), j / s), ?_⟩
      simp only
      rw [ZMod.val_intCast]
      have := Int.emod_add_mul_ediv j s
      linarith [mul_comm (j / (s : ℤ)) (s : ℤ)]

lemma sum_residuesC (s : ℕ) [NeZero s] (h : ℤ → ℂ) (hs : Summable h) :
    ∑ r : ZMod s, ∑' m : ℤ, h ((r.val : ℤ) + m * s) = ∑' j : ℤ, h j := by
  rw [← (resEquiv s).tsum_eq]
  have hsp : Summable (h ∘ resEquiv s) := (resEquiv s).summable_iff.2 hs
  rw [show (∑' c : ZMod s × ℤ, h (resEquiv s c)) = ∑' c, (h ∘ resEquiv s) c from rfl,
    hsp.tsum_prod, tsum_fintype]
  rfl

end IntMulLemma46

open IntMulLemma46 Complex in
theorem solution (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (α : ℝ) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * theta s t) :
    ‖errE s t α‖ < 2.01 * Real.exp (-π * α ^ 2 * theta s t / 2) ∧
      2.01 * Real.exp (-π * α ^ 2 * theta s t / 2) < (2 : ℝ) ^ (-(α ^ 2 * theta s t)) := by
  refine ⟨?_, ?_⟩
  swap
  · have := second_ineq (α ^ 2 * theta s t) hθ
    convert this using 3; ring
  have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hs0 : (s : ℝ) ≠ 0 := hspos.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hstR : (s : ℝ) < t := by exact_mod_cast hst
  set ρ : ℝ := (t : ℝ) / s with hρ_def
  have hρ : 1 ≤ ρ := (one_le_div hspos).2 hstR.le
  have hθρ : theta s t = ρ - 1 := rfl
  set c : ℝ := 2 * π * (α ^ 2 * theta s t) with hc_def
  have hc6 : 6 ≤ c := by
    have := Real.pi_gt_three
    rw [hc_def]; nlinarith
  have hc0 : 0 < c := by linarith
  set B : ℝ := 2 * rexp (-c / 4) / (1 - rexp (-2 * c)) with hB_def
  have hq1 : rexp (-2 * c) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hB0 : 0 ≤ B := by
    rw [hB_def]; exact div_nonneg (by positivity) (by linarith)
  have hB : B < 2.01 * rexp (-π * α ^ 2 * theta s t / 2) := by
    have h1 := geom_factor c hc6
    have hexp : rexp (-c / 4) = rexp (-π * α ^ 2 * theta s t / 2) := by
      congr 1; rw [hc_def]; ring
    rw [show B = 2 / (1 - rexp (-2 * c)) * rexp (-c / 4) by rw [hB_def]; ring, hexp]
    exact mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
  refine lt_of_le_of_lt ?_ hB
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun u => ?_
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hB0 (norm_nonneg u))]
  intro ℓ
  -- the row index ℓ and the selected row k = [tℓ/s] of 𝓣
  set L : ℤ := ((ℓ.val : ℕ) : ℤ) with hL_def
  have hL0 : (0 : ℝ) ≤ L := by rw [hL_def]; positivity
  have hLs : (L : ℝ) ≤ s - 1 := by
    have h : ℓ.val + 1 ≤ s := ZMod.val_lt ℓ
    have : ((ℓ.val : ℕ) : ℝ) + 1 ≤ s := by exact_mod_cast h
    rw [hL_def]; push_cast; linarith
  set k : ℤ := nearest ((t : ℝ) * ((ℓ.val : ℕ) : ℝ) / s) with hk_def
  have hk0 : 0 ≤ k := by
    rw [hk_def, nearest]; apply Int.floor_nonneg.2; positivity
  have hkt : k < t := by
    rw [hk_def, nearest, Int.floor_lt]
    have h1 : (t : ℝ) * ((ℓ.val : ℕ) : ℝ) / s ≤ (t : ℝ) * (s - 1) / s := by
      apply div_le_div_of_nonneg_right _ hspos.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [hL_def] using hLs
    have h2 : (t : ℝ) * (s - 1) / s = t - ρ := by rw [hρ_def]; field_simp
    have h3 : (1 : ℝ) < ρ := (one_lt_div hspos).2 hstR
    push_cast; linarith
  have hkval : ((((k : ℤ) : ZMod t).val : ℕ) : ℝ) = (k : ℝ) := by
    have h := ZMod.val_intCast (n := t) k
    rw [Int.emod_eq_of_lt hk0 (by exact_mod_cast hkt)] at h
    exact_mod_cast h
  have hβL : beta s t L = (t : ℝ) * L / s - k := by
    simp only [beta, hk_def, hL_def, Int.cast_natCast]
  -- the coefficient of u_j in row ℓ of 𝓝u
  set a : ℤ → ℝ := fun j => rexp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k : ℝ) / t - (j : ℝ) / s) ^ 2) *
    rexp (π * α ^ 2 * beta s t j ^ 2) with ha_def
  have ha_alt : ∀ j : ℤ, a j =
      rexp (-(π * α ^ 2) * ((ρ * ((j - L : ℤ) : ℝ) + beta s t L) ^ 2 - beta s t j ^ 2)) := by
    intro j
    simp only [ha_def]
    rw [← Real.exp_add]
    congr 1
    rw [hβL, hρ_def]
    push_cast
    field_simp
    ring
  have haL : a L = 1 := by
    rw [ha_alt]; simp
  have ha_le : ∀ j, j ≠ L → a j ≤ rexp (-c * (|((j - L : ℤ) : ℝ)| - 1 / 2) ^ 2) := by
    intro j hj
    rw [ha_alt]
    apply Real.exp_le_exp.2
    have hx := expo_bound ρ (beta s t L) (beta s t j) hρ (beta_abs _ _ _) (beta_abs _ _ _)
      (j - L) (sub_ne_zero.2 hj)
    have hpa : 0 ≤ π * α ^ 2 := by positivity
    have : c = π * α ^ 2 * (2 * (ρ - 1)) := by rw [hc_def, hθρ]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hx hpa]
  have ha_nonneg : ∀ j, 0 ≤ a j := fun j => by rw [ha_def]; positivity
  have htail := tail_summable_and_le c hc0 L
  have ha_sum : Summable a := by
    refine Summable.of_nonneg_of_le ha_nonneg (fun j => ?_)
      (htail.1.add (hasSum_ite_eq L (1 : ℝ)).summable)
    by_cases hj : j = L
    · subst hj; simp [haL, tailFn]
    · have := ha_le j hj
      simp only [tailFn, if_neg hj]; simpa [hj] using this
  have hF : Summable fun j : ℤ => ((a j : ℝ) : ℂ) * u (j : ZMod s) := by
    refine Summable.of_norm_bounded (g := fun j => a j * ‖u‖) (ha_sum.mul_right _) fun j => ?_
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (ha_nonneg j)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u _) (ha_nonneg j)
  -- row ℓ of 𝓝u as one sum over ℤ
  have hN : (normN s t α u) ℓ = ∑' j : ℤ, ((a j : ℝ) : ℂ) * u (j : ZMod s) := by
    simp only [normN, ContinuousLinearMap.comp_apply, rowDel, resT, diagD, toCLM,
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, latticeMatrix, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.diagonal_apply,
      Finset.sum_ite_eq]
    rw [← sum_residuesC s _ hF]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ofReal_tsum, ← tsum_mul_right]
    congr 1; funext m
    have hcast : ((((r.val : ℕ) : ℤ) + m * s : ℤ) : ZMod s) = r := by simp
    rw [hcast, ← hk_def, hkval]
    simp only [ha_def]
    rw [beta_periodic s t hs0 ((r.val : ℕ) : ℤ) m]
    push_cast
    ring
  have hrow : (errE s t α u) ℓ = ∑' j : ℤ, (if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s)) := by
    rw [errE, sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply, hN,
      hF.tsum_eq_add_tsum_ite L, haL]
    have : ((L : ℤ) : ZMod s) = ℓ := by rw [hL_def]; simp
    rw [this]
    simp
  rw [hrow]
  have hbound : ∀ j : ℤ, ‖(if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s))‖ ≤
      tailFn c L j * ‖u‖ := by
    intro j
    by_cases hj : j = L
    · simp [hj, tailFn]
    · simp only [if_neg hj, tailFn]
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (ha_nonneg j)]
      exact mul_le_mul (ha_le j hj) (norm_le_pi_norm u _) (norm_nonneg _) (by positivity)
  have hF2 : Summable fun j : ℤ => ‖(if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (htail.1.mul_right _)
  calc ‖∑' j : ℤ, (if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s))‖
      ≤ ∑' j : ℤ, ‖(if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s))‖ :=
        norm_tsum_le_tsum_norm hF2
    _ ≤ ∑' j : ℤ, tailFn c L j * ‖u‖ := Summable.tsum_le_tsum hbound hF2 (htail.1.mul_right _)
    _ = (∑' j : ℤ, tailFn c L j) * ‖u‖ := tsum_mul_right
    _ ≤ B * ‖u‖ := by gcongr; exact htail.2

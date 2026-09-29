-- Prove2me | solution 1 for MTT.cuspForm_bounded_near_rational
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T13:35:28.381591+00:00
-- url     : https://prove2.me/submissions/8a0e6910-4cb2-4281-a2e1-407b8540a9b9

import Definitions.Def_MTT_Cohomology
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped MatrixGroups ModularForm BigOperators
open UpperHalfPlane Filter Complex CongruenceSubgroup

namespace P2MCB

variable {N k : ℕ}

def mk2 (a b c d : ℤ) (h : a * d - b * c = 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![a, b; c, d], by simp [Matrix.det_fin_two_of]; linarith⟩

theorem e00 (a b c d : ℤ) (h : a * d - b * c = 1) : ((mk2 a b c d h).val 0 0 : ℤ) = a := rfl
theorem e01 (a b c d : ℤ) (h : a * d - b * c = 1) : ((mk2 a b c d h).val 0 1 : ℤ) = b := rfl
theorem e10 (a b c d : ℤ) (h : a * d - b * c = 1) : ((mk2 a b c d h).val 1 0 : ℤ) = c := rfl
theorem e11 (a b c d : ℤ) (h : a * d - b * c = 1) : ((mk2 a b c d h).val 1 1 : ℤ) = d := rfl

/-- The translation by `N`. -/
def TN (N : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℤ := ModularGroup.T ^ (N : ℤ)

theorem TN_mem (N : ℕ) : TN N ∈ CongruenceSubgroup.Gamma N := by
  have h := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  rwa [Int.natAbs_natCast] at h

theorem gamma_le_gamma1 (N : ℕ) :
    CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma1 N := by
  intro g hg
  rw [CongruenceSubgroup.Gamma_mem] at hg
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem conj_mem_GammaOne (N : ℕ) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((σ * TN N * σ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ)
      ∈ MTT.GammaOne N :=
  Subgroup.mem_map_of_mem _ (gamma_le_gamma1 N ((CongruenceSubgroup.Gamma_normal N).conj_mem _
    (TN_mem N) σ))

theorem slash_TN (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (⇑f ∣[(k : ℤ)] σ) ∣[(k : ℤ)] (TN N) = ⇑f ∣[(k : ℤ)] σ := by
  rw [← SlashAction.slash_mul]
  have hg : σ * TN N = (σ * TN N * σ⁻¹) * σ := by group
  rw [hg, SlashAction.slash_mul]
  congr 1
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ (conj_mem_GammaOne N σ)

theorem glent (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((g.val i j : ℤ) : ℝ) := rfl

theorem TN_denom (N : ℕ) (z : ℍ) :
    UpperHalfPlane.denom ((TN N : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ) z = 1 := by
  simp only [TN, UpperHalfPlane.denom, glent, ModularGroup.coe_T_zpow]
  simp

theorem TN_smul (N : ℕ) (z : ℂ) (hz : 0 < z.im) :
    (TN N : Matrix.SpecialLinearGroup (Fin 2) ℤ) • UpperHalfPlane.ofComplex z
      = UpperHalfPlane.ofComplex (z + (N : ℝ)) := by
  have hzN : 0 < (z + ((N : ℝ) : ℂ)).im := by simpa using hz
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.ofComplex_apply_of_im_pos hzN,
    TN, UpperHalfPlane.modular_T_zpow_smul]
  ext
  simp [add_comm]

theorem periodic (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Function.Periodic ((⇑f ∣[(k : ℤ)] σ) ∘ UpperHalfPlane.ofComplex) (N : ℝ) := by
  intro z
  by_cases hz : 0 < z.im
  · have h := congrFun (slash_TN f σ) (UpperHalfPlane.ofComplex z)
    rw [ModularForm.SL_slash_apply, TN_denom, TN_smul N z hz] at h
    simpa using h
  · have h1 : UpperHalfPlane.ofComplex (z + ((N : ℝ) : ℂ)) = UpperHalfPlane.ofComplex z :=
      UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos (by simpa using not_lt.mp hz)
        (not_lt.mp hz)
    simp only [Function.comp_apply]
    rw [h1]

theorem decay (hN : 0 < N) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (⇑f ∣[(k : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / N) := by
  have : NeZero N := ⟨hN.ne'⟩
  have hzero : IsZeroAtImInfty (⇑f ∣[(k : ℤ)] σ) := CuspFormClass.zero_at_infty_slash f σ
  exact hzero.exp_decay_atImInfty (by exact_mod_cast hN) (periodic f σ)
    ((CuspFormClass.holo f).slash (k : ℤ) ((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      GL (Fin 2) ℝ)) hzero.boundedAtFilter

/-! ### The geometry: the point that `σ` carries to `r + it` -/

/-- `-d/q + i/(q² t)`, the preimage of `p/q + i t` under `σ = [[p,b],[q,d]]`. -/
def wc (d q : ℤ) (t : ℝ) : ℂ :=
  ((-(d : ℝ) / (q : ℝ) : ℝ) : ℂ) + ((1 / ((q : ℝ) ^ 2 * t) : ℝ) : ℂ) * Complex.I

theorem wc_im (d q : ℤ) (t : ℝ) : (wc d q t).im = 1 / ((q : ℝ) ^ 2 * t) := by
  simp only [wc, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]

theorem wc_im_pos {d q : ℤ} (hq : 0 < q) {t : ℝ} (ht : 0 < t) : 0 < (wc d q t).im := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [wc_im]
  positivity

theorem wc_eq {d q : ℤ} {t : ℝ} (hq : (q : ℂ) ≠ 0) (ht : ((t : ℝ) : ℂ) ≠ 0) :
    wc d q t = -(d : ℂ) / (q : ℂ) + Complex.I / ((q : ℂ) ^ 2 * ((t : ℝ) : ℂ)) := by
  simp only [wc, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_intCast]
  ring

theorem cast_ne (q : ℤ) (hq : 0 < q) : (q : ℂ) ≠ 0 := by
  exact_mod_cast hq.ne'

theorem cast_ne' {t : ℝ} (ht : 0 < t) : ((t : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast ht.ne'

theorem denom_val {q d : ℤ} (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    (q : ℂ) * wc d q t + (d : ℂ) = Complex.I / ((q : ℂ) * ((t : ℝ) : ℂ)) := by
  rw [wc_eq (cast_ne q hq) (cast_ne' ht)]
  field_simp [cast_ne q hq, cast_ne' ht]
  ring

theorem num_val {p b q d : ℤ} (h : p * d - b * q = 1) (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    (p : ℂ) * wc d q t + (b : ℂ)
      = (((p : ℂ) / (q : ℂ)) + Complex.I * ((t : ℝ) : ℂ)) * (Complex.I / ((q : ℂ) * ((t : ℝ) : ℂ))) := by
  have hC : (p : ℂ) * (d : ℂ) - (b : ℂ) * (q : ℂ) = 1 := by exact_mod_cast h
  rw [wc_eq (cast_ne q hq) (cast_ne' ht)]
  field_simp [cast_ne q hq, cast_ne' ht]
  linear_combination (-((q : ℂ) * ((t : ℝ) : ℂ))) * hC
    + (-((q : ℂ) * ((t : ℝ) : ℂ))) * Complex.I_sq

/-! ### Transporting the estimate along `σ` -/

theorem denom_sigma {p b q d : ℤ} (h : p * d - b * q = 1) (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    UpperHalfPlane.denom ((mk2 p b q d h : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ)
      (UpperHalfPlane.ofComplex (wc d q t)) = Complex.I / ((q : ℂ) * ((t : ℝ) : ℂ)) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (wc_im_pos hq ht)]
  simp only [UpperHalfPlane.denom, glent, e10, e11, UpperHalfPlane.coe_mk]
  push_cast
  exact denom_val hq ht

theorem smul_sigma {p b q d : ℤ} (h : p * d - b * q = 1) (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    (mk2 p b q d h : Matrix.SpecialLinearGroup (Fin 2) ℤ) • UpperHalfPlane.ofComplex (wc d q t)
      = UpperHalfPlane.ofComplex ((((p : ℝ) / (q : ℝ) : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ)) := by
  have him : 0 < ((((p : ℝ) / (q : ℝ) : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ)).im := by simpa using ht
  have hX : Complex.I / ((q : ℂ) * ((t : ℝ) : ℂ)) ≠ 0 :=
    div_ne_zero Complex.I_ne_zero (mul_ne_zero (cast_ne q hq) (cast_ne' ht))
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (wc_im_pos hq ht),
    UpperHalfPlane.ofComplex_apply_of_im_pos him]
  ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [e00, e01, e10, e11, UpperHalfPlane.coe_mk, eq_intCast, map_intCast]
  push_cast
  rw [num_val h hq ht, denom_val hq ht, mul_div_assoc, div_self hX, mul_one]

theorem norm_id {p b q d : ℤ} (h : p * d - b * q = 1) (hq : 0 < q) {t : ℝ} (ht : 0 < t)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    ‖f (UpperHalfPlane.ofComplex ((((p : ℝ) / (q : ℝ) : ℝ) : ℂ) + Complex.I * ((t : ℝ) : ℂ)))‖
        * ((q : ℝ) * t) ^ k
      = ‖(⇑f ∣[(k : ℤ)] (mk2 p b q d h : Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (UpperHalfPlane.ofComplex (wc d q t))‖ := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hs := ModularForm.SL_slash_apply (k := (k : ℤ)) (⇑f) (mk2 p b q d h)
    (UpperHalfPlane.ofComplex (wc d q t))
  rw [smul_sigma h hq ht, denom_sigma h hq ht] at hs
  rw [hs, norm_mul, norm_zpow]
  have hnorm : ‖Complex.I / ((q : ℂ) * ((t : ℝ) : ℂ))‖ = ((q : ℝ) * t)⁻¹ := by
    rw [norm_div, Complex.norm_I, norm_mul]
    simp [abs_of_pos hq', abs_of_pos ht]
  rw [hnorm, ← zpow_natCast ((q : ℝ) * t) k, inv_zpow, zpow_neg, inv_inv]

/-! ### An elementary bound -/

theorem pow_exp_bounded (m : ℕ) {α : ℝ} (hα : 0 < α) (Y₀ : ℝ) :
    ∃ C : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → Y ^ m * Real.exp (-α * Y) ≤ C := by
  have htend : Filter.Tendsto (fun Y : ℝ => Y ^ m * Real.exp (-α * Y)) atTop (nhds 0) := by
    refine (isLittleO_pow_exp_pos_mul_atTop m hα).tendsto_div_nhds_zero.congr fun Y => ?_
    rw [div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (htend.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := Y₀) (b := T)).exists_bound_of_continuousOn
    (f := fun Y : ℝ => Y ^ m * Real.exp (-α * Y)) (by fun_prop)
  refine ⟨max 1 B, fun Y hY => ?_⟩
  by_cases hYT : T ≤ Y
  · exact le_trans (hT Y hYT).le (le_max_left _ _)
  · exact le_trans (le_trans (le_abs_self _) (hB Y ⟨hY, (not_le.mp hYT).le⟩)) (le_max_right _ _)

/-! ### Continuity along the ray -/

theorem continuousOn_hray (ρ : ℝ) :
    ContinuousOn (fun t : ℝ => UpperHalfPlane.ofComplex ((ρ : ℂ) + Complex.I * t)) (Set.Ioi 0) := by
  simp only [UpperHalfPlane.ofComplex_apply_eq_ite, continuousOn_iff_continuous_domRestrict,
    continuous_induced_rng]
  have hc : Continuous (fun t : ℝ => (ρ : ℂ) + Complex.I * t) := by fun_prop
  exact (hc.comp continuous_subtype_val).congr (by simp +contextual)



end P2MCB

open P2MCB in
theorem solution {N k : ℕ} (hN : 0 < N) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t))‖ ≤ C := by
  have hq : (0 : ℤ) < (r.den : ℤ) := by exact_mod_cast r.pos
  have hq' : (0 : ℝ) < ((r.den : ℤ) : ℝ) := by exact_mod_cast hq
  have hcop : Int.gcd r.num (r.den : ℤ) = 1 := by simpa [Int.gcd] using r.reduced
  have hbez : (1 : ℤ) = r.num * Int.gcdA r.num (r.den : ℤ)
      + (r.den : ℤ) * Int.gcdB r.num (r.den : ℤ) := by
    have hg := Int.gcd_eq_gcd_ab r.num (r.den : ℤ)
    rw [hcop] at hg
    exact_mod_cast hg
  have hdet : r.num * Int.gcdA r.num (r.den : ℤ)
      - (-(Int.gcdB r.num (r.den : ℤ))) * (r.den : ℤ) = 1 := by linarith
  set d : ℤ := Int.gcdA r.num (r.den : ℤ) with hd
  set bb : ℤ := -(Int.gcdB r.num (r.den : ℤ)) with hbb
  set σ : Matrix.SpecialLinearGroup (Fin 2) ℤ := mk2 r.num bb (r.den : ℤ) d hdet with hσ
  -- rewrite the base point
  have hpt : ((r : ℚ) : ℂ) = (((r.num : ℝ) / ((r.den : ℤ) : ℝ) : ℝ) : ℂ) := by
    rw [Rat.cast_def]
    push_cast
    ring
  simp only [hpt]
  -- exponential decay of the slashed form
  obtain ⟨M0, hM0⟩ := Asymptotics.isBigO_iff.mp (decay hN f σ)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hM0
  set M : ℝ := max M0 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  set α : ℝ := 2 * Real.pi / (N : ℝ) with hα
  have hαpos : 0 < α := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  set Y₀ : ℝ := max A 1 with hY₀
  have hY₀pos : 0 < Y₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨C1, hC1⟩ := pow_exp_bounded k hαpos Y₀
  set t₀ : ℝ := 1 / (((r.den : ℤ) : ℝ) ^ 2 * Y₀) with ht₀
  have ht₀pos : 0 < t₀ := by rw [ht₀]; positivity
  -- the middle interval
  obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := min t₀ 1) (b := (1 : ℝ))).exists_bound_of_continuousOn
    (f := fun t : ℝ => ‖f (UpperHalfPlane.ofComplex ((((r.num : ℝ) / ((r.den : ℤ) : ℝ) : ℝ) : ℂ)
      + Complex.I * t))‖)
    ((((CuspFormClass.holo f).continuous.comp_continuousOn
        (continuousOn_hray ((r.num : ℝ) / ((r.den : ℤ) : ℝ)))).norm).mono
      (fun t (ht : t ∈ Set.Icc (min t₀ 1) (1:ℝ)) =>
        Set.mem_Ioi.mpr (lt_of_lt_of_le (lt_min ht₀pos zero_lt_one) ht.1)))
  refine ⟨max (M * ((r.den : ℤ) : ℝ) ^ k * C1) C2, fun t ht ht1 => ?_⟩
  by_cases hsmall : t ≤ min t₀ 1
  · -- small t : use the decay
    have htt₀ : t ≤ t₀ := le_trans hsmall (min_le_left _ _)
    set Y : ℝ := 1 / (((r.den : ℤ) : ℝ) ^ 2 * t) with hY
    have hYpos : 0 < Y := by rw [hY]; positivity
    have hYge : Y₀ ≤ Y := by
      have h2 : t * (((r.den : ℤ) : ℝ) ^ 2 * Y₀) ≤ 1 := by
        rw [ht₀, le_div_iff₀ (by positivity)] at htt₀
        exact htt₀
      rw [hY, le_div_iff₀ (by positivity)]
      nlinarith [h2]
    have hWim : (UpperHalfPlane.ofComplex (wc d (r.den : ℤ) t)).im = Y := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (wc_im_pos hq ht)]
      exact wc_im _ _ _
    have hbound : ‖(⇑f ∣[(k : ℤ)] σ) (UpperHalfPlane.ofComplex (wc d (r.den : ℤ) t))‖
        ≤ M * Real.exp (-α * Y) := by
      have h1 := hA _ (by rw [hWim]; exact le_trans (le_max_left _ _) hYge)
      simp only [Set.mem_ofPred_eq] at h1
      rw [hWim, Real.norm_of_nonneg (Real.exp_nonneg _)] at h1
      have heq : (-2 * Real.pi * Y / (N : ℝ)) = -α * Y := by rw [hα]; ring
      rw [heq] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
    have hprod : (((r.den : ℤ) : ℝ) * t) * (((r.den : ℤ) : ℝ) * Y) = 1 := by
      rw [hY]; field_simp
    have hkey : ‖f (UpperHalfPlane.ofComplex ((((r.num : ℝ) / ((r.den : ℤ) : ℝ) : ℝ) : ℂ)
        + Complex.I * t))‖
        = ‖(⇑f ∣[(k : ℤ)] σ) (UpperHalfPlane.ofComplex (wc d (r.den : ℤ) t))‖
          * (((r.den : ℤ) : ℝ) * Y) ^ k := by
      rw [← norm_id hdet hq ht f, mul_assoc, ← mul_pow, hprod, one_pow, mul_one]
    rw [hkey]
    refine le_trans ?_ (le_max_left _ _)
    calc ‖(⇑f ∣[(k : ℤ)] σ) (UpperHalfPlane.ofComplex (wc d (r.den : ℤ) t))‖
          * (((r.den : ℤ) : ℝ) * Y) ^ k
        ≤ (M * Real.exp (-α * Y)) * (((r.den : ℤ) : ℝ) * Y) ^ k := by
          exact mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = M * ((r.den : ℤ) : ℝ) ^ k * (Y ^ k * Real.exp (-α * Y)) := by
          rw [mul_pow]; ring
      _ ≤ M * ((r.den : ℤ) : ℝ) ^ k * C1 := by
          exact mul_le_mul_of_nonneg_left (hC1 Y hYge) (by positivity)
  · refine le_trans ?_ (le_max_right _ _)
    simpa using hC2 t ⟨(not_le.mp hsmall).le, ht1⟩

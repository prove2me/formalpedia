-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b95eea3a-97eb-5b4c-9093-49637593f1e8

import Definitions.Def_LanglandsTunnell_JLConverse
import Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse

namespace ArchZetaUniform

open Complex Set MeasureTheory

private theorem mul_sub_sq_le (E d : ℝ) : E * d - d ^ 2 ≤ E ^ 2 / 4 := by
  nlinarith [sq_nonneg (d - E / 2)]

private theorem re_sub_sq (z s : ℂ) : ((z - s) ^ 2).re = (z.re - s.re) ^ 2 - (z.im - s.im) ^ 2 := by
  rw [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

private theorem norm_le_of_norm_le_on_lines {F : ℂ → ℂ} (hF : Differentiable ℂ F) {σL σR C E : ℝ}
    (hLR : σL < σR) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hbd : ∀ z : ℂ, (z.re = σL ∨ z.re = σR) → ‖F z‖ ≤ C * Real.exp (E * |z.im|))
    (hfo : ∃ C' E' : ℝ, ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR → ‖F z‖ ≤ C' * Real.exp (E' * |z.im|))
    {s : ℂ} (hsL : σL ≤ s.re) (hsR : s.re ≤ σR) :
    ‖F s‖ ≤ C * Real.exp ((σR - σL) ^ 2 + E ^ 2 / 4) * Real.exp (E * |s.im|) := by
  obtain ⟨C', E', hfo⟩ := hfo
  set L : ℝ := σR - σL with hLdef
  have hL0 : 0 < L := by rw [hLdef]; linarith
  set B : ℝ := C * Real.exp (L ^ 2 + E ^ 2 / 4) * Real.exp (E * |s.im|) with hBdef
  have hB0 : 0 ≤ B := by positivity
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set C'' : ℝ := max C' 1 with hC''
  set E'' : ℝ := max E' 0 with hE''
  have hC''1 : 1 ≤ C'' := le_max_right _ _
  have hC''0 : 0 < C'' := lt_of_lt_of_le one_pos hC''1
  have hE''0 : 0 ≤ E'' := le_max_right _ _
  have hfo' : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR → ‖F z‖ ≤ C'' * Real.exp (E'' * |z.im|) := by
    intro z h1 h2
    calc ‖F z‖ ≤ C' * Real.exp (E' * |z.im|) := hfo z h1 h2
      _ ≤ C'' * Real.exp (E' * |z.im|) := by
          gcongr
          exact le_max_left _ _
      _ ≤ C'' * Real.exp (E'' * |z.im|) := by
          gcongr
          exact le_max_left _ _
  set a : ℝ := |s.im| with ha
  set R : ℝ := max (E'' + 1) (E'' * a + L ^ 2 + (Real.log C'' - Real.log δ)) with hR
  set T : ℝ := a + R with hT
  have hR1 : E'' + 1 ≤ R := le_max_left _ _
  have hR2 : E'' * a + L ^ 2 + (Real.log C'' - Real.log δ) ≤ R := le_max_right _ _
  have hR0 : 0 ≤ R := by linarith
  have ha0 : 0 ≤ a := abs_nonneg _
  have hT0 : 0 < T := by linarith
  have hTT : -T < T := by linarith
  set G : ℂ → ℂ := fun z => F z * Complex.exp ((z - s) ^ 2) with hG
  have hGd : Differentiable ℂ G := hF.mul ((differentiable_id.sub_const s).pow 2).cexp
  have hre : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR → ((z - s) ^ 2).re ≤ L ^ 2 - (z.im - s.im) ^ 2 := by
    intro z h1 h2
    rw [re_sub_sq]
    have hzr : |z.re - s.re| ≤ L := by
      rw [abs_le]; constructor <;> linarith
    have : (z.re - s.re) ^ 2 ≤ L ^ 2 := by
      calc (z.re - s.re) ^ 2 = |z.re - s.re| ^ 2 := (sq_abs _).symm
        _ ≤ L ^ 2 := by gcongr
    linarith
  have hnormG : ∀ z : ℂ, ‖G z‖ = ‖F z‖ * Real.exp (((z - s) ^ 2).re) := by
    intro z
    simp only [hG, norm_mul, Complex.norm_exp]
  have hfront : ∀ z ∈ frontier (Ioo σL σR ×ℂ Ioo (-T) T), ‖G z‖ ≤ B + δ := by
    intro z hz
    rw [frontier_reProdIm, closure_Ioo hLR.ne, frontier_Ioo hLR, closure_Ioo hTT.ne,
      frontier_Ioo hTT] at hz
    rcases hz with ⟨hzre, hzim⟩ | ⟨hzre, hzim⟩
    · have h1 : σL ≤ z.re := hzre.1
      have h2 : z.re ≤ σR := hzre.2
      have hzT : |z.im| = T := by
        rcases hzim with h | h
        · rw [h, abs_neg, abs_of_pos hT0]
        · rw [h, abs_of_pos hT0]
      have hdist : R ≤ |z.im - s.im| := by
        have := abs_sub_abs_le_abs_sub z.im s.im
        rw [hzT] at this
        linarith
      have hsq : R ^ 2 ≤ (z.im - s.im) ^ 2 := by
        calc R ^ 2 ≤ |z.im - s.im| ^ 2 := by gcongr
          _ = (z.im - s.im) ^ 2 := sq_abs _
      calc ‖G z‖ = ‖F z‖ * Real.exp (((z - s) ^ 2).re) := hnormG z
        _ ≤ C'' * Real.exp (E'' * |z.im|) * Real.exp (L ^ 2 - (z.im - s.im) ^ 2) := by
            gcongr
            · exact hfo' z h1 h2
            · exact hre z h1 h2
        _ ≤ C'' * Real.exp (E'' * T) * Real.exp (L ^ 2 - R ^ 2) := by
            rw [hzT]
            gcongr
        _ = C'' * Real.exp (E'' * a + L ^ 2 + (E'' * R - R ^ 2)) := by
            rw [mul_assoc, ← Real.exp_add, hT]
            congr 1
            congr 1
            ring
        _ ≤ C'' * Real.exp (E'' * a + L ^ 2 - R) := by
            gcongr
            nlinarith [hR1, hR0]
        _ ≤ C'' * Real.exp (Real.log δ - Real.log C'') :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hR2])) hC''0.le
        _ = δ := by
            rw [Real.exp_sub, Real.exp_log hδ, Real.exp_log hC''0]
            field_simp
        _ ≤ B + δ := le_add_of_nonneg_left hB0
    · have hzre' : z.re = σL ∨ z.re = σR := by
        simpa [mem_insert_iff, mem_singleton_iff] using hzre
      have h1 : σL ≤ z.re := by
        rcases hzre' with h | h
        · rw [h]
        · rw [h]; exact hLR.le
      have h2 : z.re ≤ σR := by
        rcases hzre' with h | h
        · rw [h]; exact hLR.le
        · rw [h]
      have hkey : E * |z.im| - (z.im - s.im) ^ 2 ≤ E * |s.im| + E ^ 2 / 4 := by
        have ht : |z.im| ≤ |s.im| + |z.im - s.im| := by
          have := abs_add_le s.im (z.im - s.im)
          rwa [add_sub_cancel] at this
        have hd := mul_sub_sq_le E |z.im - s.im|
        rw [sq_abs] at hd
        nlinarith [hE, ht, hd, abs_nonneg (z.im - s.im)]
      calc ‖G z‖ = ‖F z‖ * Real.exp (((z - s) ^ 2).re) := hnormG z
        _ ≤ C * Real.exp (E * |z.im|) * Real.exp (L ^ 2 - (z.im - s.im) ^ 2) := by
            gcongr
            · exact hbd z hzre'
            · exact hre z h1 h2
        _ = C * Real.exp (L ^ 2 + (E * |z.im| - (z.im - s.im) ^ 2)) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 1
            congr 1
            ring
        _ ≤ B := by
            rw [hBdef, mul_assoc, ← Real.exp_add]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hkey])) hC
        _ ≤ B + δ := le_add_of_nonneg_right hδ.le
  have hs_cl : s ∈ closure (Ioo σL σR ×ℂ Ioo (-T) T) := by
    rw [closure_reProdIm, closure_Ioo hLR.ne, closure_Ioo hTT.ne]
    refine ⟨⟨hsL, hsR⟩, ?_, ?_⟩
    · show -T ≤ s.im
      have := neg_abs_le s.im
      linarith
    · show s.im ≤ T
      have := le_abs_self s.im
      linarith
  have hbdd : Bornology.IsBounded (Ioo σL σR ×ℂ Ioo (-T) T) :=
    (Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hGd.diffContOnCl hfront hs_cl
  have hGs : G s = F s := by simp [hG]
  rwa [hGs] at hmax

private theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ Real.exp (N * x) := by
  calc (1 + x) ^ N ≤ (Real.exp x) ^ N := by
        gcongr
        linarith [Real.add_one_le_exp x]
    _ = Real.exp (N * x) := (Real.exp_nat_mul x N).symm

private theorem norm_inv_Gamma_le (c : ℝ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ w : ℂ, w.re = c → ‖(Complex.Gamma w)⁻¹‖ ≤ C * Real.exp (E * |w.im|) := by
  obtain ⟨A, N, hst⟩ :=
    Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im c c
  set K : Set ℂ := (fun t : ℝ => (c : ℂ) + t * I) '' Icc (-1 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    (Complex.differentiable_one_div_Gamma.continuous.continuousOn)
  refine ⟨max (max B 0) (max A 0), N + Real.pi / 2, le_max_of_le_left (le_max_right _ _),
    by positivity, ?_⟩
  intro w hw
  have hexp1 : 1 ≤ Real.exp ((N + Real.pi / 2) * |w.im|) := Real.one_le_exp (by positivity)
  by_cases him : 1 ≤ |w.im|
  · obtain ⟨-, hlow⟩ := hst w hw.ge hw.le him
    have hpos : 0 < ‖Complex.Gamma w‖ := by
      rcases (norm_nonneg (Complex.Gamma w)).eq_or_lt with h | h
      · rw [← h, mul_zero] at hlow
        exact absurd hlow (not_le.mpr (Real.exp_pos _))
      · exact h
    have hq : ‖Complex.Gamma w‖⁻¹ * Real.exp (-(Real.pi / 2) * |w.im|) ≤ A * (1 + |w.im|) ^ N := by
      rw [inv_mul_eq_div, div_le_iff₀ hpos]
      exact hlow
    have hPe : 0 ≤ (1 + |w.im|) ^ N * Real.exp (Real.pi / 2 * |w.im|) := by positivity
    calc ‖(Complex.Gamma w)⁻¹‖
        = ‖Complex.Gamma w‖⁻¹ * Real.exp (-(Real.pi / 2) * |w.im|) * Real.exp (Real.pi / 2 * |w.im|) := by
          rw [norm_inv, mul_assoc, ← Real.exp_add,
            show -(Real.pi / 2) * |w.im| + Real.pi / 2 * |w.im| = 0 by ring, Real.exp_zero, mul_one]
      _ ≤ A * (1 + |w.im|) ^ N * Real.exp (Real.pi / 2 * |w.im|) := by gcongr
      _ = A * ((1 + |w.im|) ^ N * Real.exp (Real.pi / 2 * |w.im|)) := by ring
      _ ≤ max (max B 0) (max A 0) * ((1 + |w.im|) ^ N * Real.exp (Real.pi / 2 * |w.im|)) := by
          gcongr
          exact le_max_of_le_right (le_max_left _ _)
      _ ≤ max (max B 0) (max A 0) * (Real.exp (N * |w.im|) * Real.exp (Real.pi / 2 * |w.im|)) := by
          gcongr
          exact one_add_pow_le_exp (abs_nonneg _) N
      _ = max (max B 0) (max A 0) * Real.exp ((N + Real.pi / 2) * |w.im|) := by
          rw [← Real.exp_add]
          ring_nf
  · have hwK : w ∈ K := by
      refine ⟨w.im, ⟨?_, ?_⟩, ?_⟩
      · linarith [abs_le.mp (not_le.mp him).le]
      · linarith [abs_le.mp (not_le.mp him).le]
      · apply Complex.ext <;> simp [hw]
    calc ‖(Complex.Gamma w)⁻¹‖ ≤ B := hB w hwK
      _ ≤ max (max B 0) (max A 0) := le_max_of_le_left (le_max_left _ _)
      _ = max (max B 0) (max A 0) * 1 := (mul_one _).symm
      _ ≤ max (max B 0) (max A 0) * Real.exp ((N + Real.pi / 2) * |w.im|) := by
          gcongr

private theorem abs_im_add_half_le (s μ : ℂ) {E : ℝ} (hE : 0 ≤ E) :
    E * |((s + μ) / 2).im| ≤ E / 2 * |μ.im| + E / 2 * |s.im| := by
  have h1 : ((s + μ) / 2).im = (s.im + μ.im) / 2 := by simp
  rw [h1, abs_div, abs_two]
  have := abs_add_le s.im μ.im
  nlinarith [this, abs_nonneg (s.im + μ.im)]

private theorem norm_inv_Gammaℝ_le (c : ℝ) (μ : ℂ) (hc : 0 < c + μ.re) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ s : ℂ, s.re = c →
      Gammaℝ (s + μ) ≠ 0 ∧ ‖(Gammaℝ (s + μ))⁻¹‖ ≤ C * Real.exp (E * |s.im|) := by
  obtain ⟨C, E, hC, hE, h⟩ := norm_inv_Gamma_le ((c + μ.re) / 2)
  refine ⟨Real.pi ^ ((c + μ.re) / 2) * (C * Real.exp (E / 2 * |μ.im|)), E / 2, by positivity,
    by positivity, ?_⟩
  intro s hs
  have hre : ((s + μ) / 2).re = (c + μ.re) / 2 := by simp [hs]
  have hΓ : Complex.Gamma ((s + μ) / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hre]; linarith)
  have hπ : (Real.pi : ℂ) ^ (-(s + μ) / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
  refine ⟨by rw [Gammaℝ_def]; exact mul_ne_zero hπ hΓ, ?_⟩
  have h1 : ‖((Real.pi : ℂ) ^ (-(s + μ) / 2))⁻¹‖ = Real.pi ^ ((c + μ.re) / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_neg Real.pi_pos.le]
    congr 1
    simp [hs]
    ring
  have h2 := h ((s + μ) / 2) hre
  have h3 := abs_im_add_half_le s μ hE
  calc ‖(Gammaℝ (s + μ))⁻¹‖
      = Real.pi ^ ((c + μ.re) / 2) * ‖(Complex.Gamma ((s + μ) / 2))⁻¹‖ := by
        rw [Gammaℝ_def, mul_inv, norm_mul, h1]
    _ ≤ Real.pi ^ ((c + μ.re) / 2) * (C * Real.exp (E * |((s + μ) / 2).im|)) := by gcongr
    _ ≤ Real.pi ^ ((c + μ.re) / 2) * (C * Real.exp (E / 2 * |μ.im| + E / 2 * |s.im|)) := by gcongr
    _ = Real.pi ^ ((c + μ.re) / 2) * (C * Real.exp (E / 2 * |μ.im|)) * Real.exp (E / 2 * |s.im|) := by
        rw [Real.exp_add]; ring

private theorem norm_inv_Gammaℂ_le (c : ℝ) (ν : ℂ) (hc : 0 < c + ν.re) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ s : ℂ, s.re = c →
      Gammaℂ (s + ν) ≠ 0 ∧ ‖(Gammaℂ (s + ν))⁻¹‖ ≤ C * Real.exp (E * |s.im|) := by
  obtain ⟨C, E, hC, hE, h⟩ := norm_inv_Gamma_le (c + ν.re)
  refine ⟨2⁻¹ * (2 * Real.pi) ^ (c + ν.re) * (C * Real.exp (E * |ν.im|)), E, by positivity, hE, ?_⟩
  intro s hs
  have hre : (s + ν).re = c + ν.re := by simp [hs]
  have hΓ : Complex.Gamma (s + ν) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hre]; exact hc)
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ^ (-(s + ν)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast h2π.ne')
  have hG : Gammaℂ (s + ν) = 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-(s + ν)) * Complex.Gamma (s + ν) := by
    rw [Gammaℂ_def]; push_cast; ring
  refine ⟨by rw [hG]; exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) hΓ, ?_⟩
  have h1 : ‖(((2 * Real.pi : ℝ) : ℂ) ^ (-(s + ν)))⁻¹‖ = (2 * Real.pi) ^ (c + ν.re) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos h2π, ← Real.rpow_neg h2π.le]
    congr 1
    simp [hs]
  have h2 := h (s + ν) hre
  have h3 : E * |(s + ν).im| ≤ E * |ν.im| + E * |s.im| := by
    have : (s + ν).im = s.im + ν.im := by simp
    rw [this]
    nlinarith [abs_add_le s.im ν.im, hE]
  calc ‖(Gammaℂ (s + ν))⁻¹‖
      = 2⁻¹ * (2 * Real.pi) ^ (c + ν.re) * ‖(Complex.Gamma (s + ν))⁻¹‖ := by
        rw [hG, mul_inv, mul_inv, norm_mul, norm_mul, h1, norm_inv, Complex.norm_two]
    _ ≤ 2⁻¹ * (2 * Real.pi) ^ (c + ν.re) * (C * Real.exp (E * |(s + ν).im|)) := by gcongr
    _ ≤ 2⁻¹ * (2 * Real.pi) ^ (c + ν.re) * (C * Real.exp (E * |ν.im| + E * |s.im|)) := by gcongr
    _ = 2⁻¹ * (2 * Real.pi) ^ (c + ν.re) * (C * Real.exp (E * |ν.im|)) * Real.exp (E * |s.im|) := by
        rw [Real.exp_add]; ring

private theorem norm_inv_multiset_prod_le (f : ℂ → ℂ → ℂ) (c : ℝ) (m : Multiset ℂ)
    (h : ∀ μ ∈ m, ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ s : ℂ, s.re = c →
      f μ s ≠ 0 ∧ ‖(f μ s)⁻¹‖ ≤ C * Real.exp (E * |s.im|)) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ s : ℂ, s.re = c →
      (m.map fun μ => f μ s).prod ≠ 0 ∧ ‖((m.map fun μ => f μ s).prod)⁻¹‖ ≤ C * Real.exp (E * |s.im|) := by
  induction m using Multiset.induction_on with
  | empty =>
    refine ⟨1, 0, zero_le_one, le_rfl, fun s _ => ?_⟩
    simp
  | cons a m ih =>
    obtain ⟨C₁, E₁, hC₁, hE₁, h₁⟩ := h a (Multiset.mem_cons_self a m)
    obtain ⟨C₂, E₂, hC₂, hE₂, h₂⟩ := ih (fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ))
    refine ⟨C₁ * C₂, E₁ + E₂, by positivity, by positivity, fun s hs => ?_⟩
    obtain ⟨hz₁, hb₁⟩ := h₁ s hs
    obtain ⟨hz₂, hb₂⟩ := h₂ s hs
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine ⟨mul_ne_zero hz₁ hz₂, ?_⟩
    calc ‖(f a s * (m.map fun μ => f μ s).prod)⁻¹‖ = ‖(f a s)⁻¹‖ * ‖((m.map fun μ => f μ s).prod)⁻¹‖ := by
          rw [mul_inv, norm_mul]
      _ ≤ C₁ * Real.exp (E₁ * |s.im|) * (C₂ * Real.exp (E₂ * |s.im|)) := by gcongr
      _ = C₁ * C₂ * Real.exp ((E₁ + E₂) * |s.im|) := by
          rw [add_mul, Real.exp_add]; ring

private theorem norm_inv_archFactor_le (Q : RealArchParam) (c : ℝ)
    (hR : ∀ μ ∈ Q.gammaR, 0 < c + μ.re) (hC : ∀ ν ∈ Q.gammaC, 0 < c + ν.re) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ s : ℂ, s.re = c →
      Q.archFactor s ≠ 0 ∧ ‖(Q.archFactor s)⁻¹‖ ≤ C * Real.exp (E * |s.im|) := by
  obtain ⟨C₁, E₁, hC₁, hE₁, h₁⟩ := norm_inv_multiset_prod_le (fun μ s => Gammaℝ (s + μ)) c Q.gammaR
    (fun μ hμ => norm_inv_Gammaℝ_le c μ (hR μ hμ))
  obtain ⟨C₂, E₂, hC₂, hE₂, h₂⟩ := norm_inv_multiset_prod_le (fun ν s => Gammaℂ (s + ν)) c Q.gammaC
    (fun ν hν => norm_inv_Gammaℂ_le c ν (hC ν hν))
  refine ⟨C₁ * C₂, E₁ + E₂, by positivity, by positivity, fun s hs => ?_⟩
  obtain ⟨hz₁, hb₁⟩ := h₁ s hs
  obtain ⟨hz₂, hb₂⟩ := h₂ s hs
  refine ⟨by rw [RealArchParam.archFactor]; exact mul_ne_zero hz₁ hz₂, ?_⟩
  calc ‖(Q.archFactor s)⁻¹‖ = ‖((Q.gammaR.map fun μ => Gammaℝ (s + μ)).prod)⁻¹‖ *
        ‖((Q.gammaC.map fun ν => Gammaℂ (s + ν)).prod)⁻¹‖ := by
        rw [RealArchParam.archFactor, mul_inv, norm_mul]
    _ ≤ C₁ * Real.exp (E₁ * |s.im|) * (C₂ * Real.exp (E₂ * |s.im|)) := by gcongr
    _ = C₁ * C₂ * Real.exp ((E₁ + E₂) * |s.im|) := by
        rw [add_mul, Real.exp_add]; ring

private theorem exists_shift_bound (Q : RealArchParam) :
    ∃ T : ℝ, (∀ μ ∈ Q.gammaR, -μ.re ≤ T) ∧ ∀ ν ∈ Q.gammaC, -ν.re ≤ T := by
  cases Q with
  | principal u₁ a₁ u₂ a₂ =>
    refine ⟨max (-(u₁ + signShift a₁).re) (-(u₂ + signShift a₂).re), ?_, ?_⟩
    · intro μ hμ
      simp only [RealArchParam.gammaR, Multiset.insert_eq_cons, Multiset.mem_cons,
        Multiset.mem_singleton] at hμ
      rcases hμ with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
    · intro ν hν
      simp [RealArchParam.gammaC] at hν
  | discrete u k hk =>
    refine ⟨-(u + (k : ℂ) / 2).re, ?_, ?_⟩
    · intro μ hμ
      simp [RealArchParam.gammaR] at hμ
    · intro ν hν
      simp only [RealArchParam.gammaC, Multiset.mem_singleton] at hν
      rw [hν]

private theorem epsilonFactor_ne_zero (Q : RealArchParam) : Q.epsilonFactor ≠ 0 := by
  have hs : ∀ b : ZMod 2, signEpsilon b ≠ 0 := by
    intro b
    unfold signEpsilon
    split_ifs
    · exact one_ne_zero
    · exact I_ne_zero
  cases Q with
  | principal u₁ a₁ u₂ a₂ => exact mul_ne_zero (hs a₁) (hs a₂)
  | discrete u k hk => exact pow_ne_zero _ I_ne_zero

section Datum

variable {P : RealArchParam} (D : ArchDatumR P)

private noncomputable def wt (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹

private theorem one_le_wt (g : Matrix (Fin 2) (Fin 2) ℝ) : 1 ≤ wt g := by
  unfold wt
  have := abs_nonneg (g 0 0); have := abs_nonneg (g 0 1); have := abs_nonneg (g 1 0)
  have := abs_nonneg (g 1 1); have := inv_nonneg.mpr (abs_nonneg g.det)
  linarith

private noncomputable def rho (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := Real.sqrt (g 1 0 ^ 2 + g 1 1 ^ 2)

private noncomputable def kmat (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![g 1 1 / rho g, -g 1 0 / rho g; g 1 0 / rho g, g 1 1 / rho g]

private noncomputable def Yc (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := g.det / rho g ^ 2

private noncomputable def Xc (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (g 0 0 * g 1 0 + g 0 1 * g 1 1) / g.det

private theorem det_two (g : Matrix (Fin 2) (Fin 2) ℝ) : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

private theorem rho_sq (g : Matrix (Fin 2) (Fin 2) ℝ) : rho g ^ 2 = g 1 0 ^ 2 + g 1 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem rho_pos {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : 0 < rho g := by
  unfold rho
  apply Real.sqrt_pos.mpr
  by_contra h
  have h10 : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
  have h11 : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
  apply hg
  rw [det_two, h10, h11]; ring

private theorem Yc_ne_zero {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : Yc g ≠ 0 :=
  div_ne_zero hg (pow_ne_zero _ (rho_pos hg).ne')

private theorem kmat_isK {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : ArchR.IsK (kmat g) := by
  have hρ := rho_pos hg
  have hρ0 : rho g ≠ 0 := hρ.ne'
  have hρ2 := rho_sq g
  rw [ArchR.IsK, Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    (try field_simp) <;> first | ring1 | linarith [hρ2]

private theorem diagOne_mul_eq {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (y : ℝ) :
    ArchR.diagOne y * g =
      rho g • (ArchR.unip (y * Yc g * Xc g) * (ArchR.diagOne (y * Yc g) * kmat g)) := by
  have hρ := rho_pos hg
  have hρ0 : rho g ≠ 0 := hρ.ne'
  have hq : g 1 0 ^ 2 + g 1 1 ^ 2 ≠ 0 := by rw [← rho_sq]; exact pow_ne_zero _ hρ0
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by rwa [det_two] at hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ArchR.diagOne, ArchR.unip, kmat, Yc, Xc, rho_sq, Matrix.det_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply] <;>
    (try field_simp) <;> ring1

private theorem norm_psi (x : ℝ) : ‖ArchR.psi x‖ = 1 := by
  rw [ArchR.psi, Complex.norm_exp]
  simp

private theorem norm_quasiChar {y : ℝ} (hy : y ≠ 0) (u : ℂ) (a : ZMod 2) :
    ‖ArchR.quasiChar u a y‖ = |y| ^ u.re := by
  rw [ArchR.quasiChar, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hy)]
  have : ‖(if a = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ))‖ = 1 := by
    split_ifs
    · simp
    · rcases hy.lt_or_gt with h | h
      · simp [sign_neg h]
      · simp [sign_pos h]
  rw [this, mul_one]

private theorem norm_centralChar_of_pos {r : ℝ} (hr : 0 < r) :
    ‖ArchR.centralChar P r‖ = r ^ P.centralExponent.re := by
  rw [ArchR.centralChar, norm_quasiChar hr.ne', abs_of_pos hr]

private theorem norm_W_diagOne_mul {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (y : ℝ) :
    ‖D.W (ArchR.diagOne y * g)‖ =
      rho g ^ (1 + P.centralExponent.re) * ‖D.W (ArchR.diagOne (y * Yc g) * kmat g)‖ := by
  have hρ := rho_pos hg
  rw [diagOne_mul_eq hg, D.central_law _ _ hρ.ne', D.unip_law, norm_mul, norm_mul, norm_mul,
    norm_centralChar_of_pos hρ, norm_psi, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs,
    abs_of_pos hρ, Real.rpow_add hρ, Real.rpow_one]
  ring

private theorem norm_mul_kernel {y : ℝ} (hy : y ≠ 0) (c : ℂ) (u : ℂ) (a : ZMod 2) (s : ℂ) :
    ‖c * ArchR.quasiChar u a y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹‖ = ‖c‖ * |y| ^ (s.re + u.re - 2) := by
  have hay : 0 < |y| := abs_pos.mpr hy
  rw [norm_mul, norm_mul, norm_mul, norm_quasiChar hy, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hay, Complex.norm_real, Real.norm_eq_abs, abs_abs,
    ← Real.rpow_neg_one, Complex.sub_re, Complex.one_re]
  rw [mul_assoc, mul_assoc, ← Real.rpow_add hay, ← Real.rpow_add hay]
  ring_nf

private theorem norm_zetaIntegrand {y : ℝ} (hy : y ≠ 0) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) :
    ‖ArchR.zetaIntegrand D.W g u a s y‖ = ‖D.W (ArchR.diagOne y * g)‖ * |y| ^ (s.re + u.re - 2) :=
  norm_mul_kernel hy _ u a s

private theorem norm_zetaIntegrand_sub {y : ℝ} (hy : y ≠ 0) (g g' : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2)
    (s : ℂ) : ‖ArchR.zetaIntegrand D.W g u a s y - ArchR.zetaIntegrand D.W g' u a s y‖ =
      ‖D.W (ArchR.diagOne y * g) - D.W (ArchR.diagOne y * g')‖ * |y| ^ (s.re + u.re - 2) := by
  rw [ArchR.zetaIntegrand, ArchR.zetaIntegrand, ← sub_mul, ← sub_mul, ← sub_mul]
  exact norm_mul_kernel hy _ u a s

private theorem norm_W_le_near_zero : ∃ C₀ σ₀ : ℝ, 0 ≤ C₀ ∧ ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ),
    ArchR.IsK k → y ≠ 0 → |y| ≤ 1 → ‖D.W (ArchR.diagOne y * k)‖ ≤ C₀ * |y| ^ (-σ₀) := by
  obtain ⟨C, σ, h⟩ := D.decay_zero 0
  refine ⟨max C 0, σ, le_max_right _ _, fun y k hk hy hy1 => ?_⟩
  have := h y k hk hy hy1
  rw [norm_iteratedFDerivWithin_zero] at this
  have hW : ArchR.asPi D.W (ArchR.diagOneMulCoords y k) = D.W (ArchR.diagOne y * k) := by
    simp [ArchR.asPi, ArchR.diagOneMulCoords]
  rw [hW] at this
  exact this.trans (by gcongr; exact le_max_left _ _)

private theorem norm_W_le_near_top (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ),
    ArchR.IsK k → 1 ≤ |y| → ‖D.W (ArchR.diagOne y * k)‖ ≤ C * |y| ^ (-(N : ℝ)) := by
  obtain ⟨C, h⟩ := D.decay_top 0 N
  refine ⟨max C 0, le_max_right _ _, fun y k hk hy1 => ?_⟩
  have := h y k hk hy1
  rw [norm_iteratedFDerivWithin_zero] at this
  have hW : ArchR.asPi D.W (ArchR.diagOneMulCoords y k) = D.W (ArchR.diagOne y * k) := by
    simp [ArchR.asPi, ArchR.diagOneMulCoords]
  rw [hW] at this
  exact this.trans (by gcongr; exact le_max_left _ _)

private theorem exists_dominator : ∃ p₀ : ℝ, ∀ p : ℝ, p₀ ≤ p → ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (z : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → z ≠ 0 →
      ‖D.W (ArchR.diagOne z * k)‖ * |z| ^ (p - 2) ≤ K₀ * (1 + z ^ 2)⁻¹ := by
  obtain ⟨C₀, σ₀, hC₀, h₀⟩ := norm_W_le_near_zero D
  refine ⟨σ₀ + 2, fun p hp => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := norm_W_le_near_top D (Nat.ceil p)
  refine ⟨2 * max C₀ C₁, by positivity, fun z k hk hz => ?_⟩
  have haz : 0 < |z| := abs_pos.mpr hz
  have hz2 : 0 < 1 + z ^ 2 := by positivity
  rcases le_or_gt |z| 1 with hz1 | hz1
  ·
    have hsq : z ^ 2 ≤ 1 := by
      calc z ^ 2 = |z| ^ 2 := (sq_abs z).symm
        _ ≤ 1 := pow_le_one₀ (abs_nonneg z) hz1
    calc ‖D.W (ArchR.diagOne z * k)‖ * |z| ^ (p - 2)
        ≤ C₀ * |z| ^ (-σ₀) * |z| ^ (p - 2) := by
          gcongr
          exact h₀ z k hk hz hz1
      _ = C₀ * |z| ^ (p - 2 - σ₀) := by
          rw [mul_assoc, ← Real.rpow_add haz]; ring_nf
      _ ≤ C₀ * 1 := by
          gcongr
          exact Real.rpow_le_one (abs_nonneg z) hz1 (by linarith)
      _ ≤ 2 * max C₀ C₁ * (1 + z ^ 2)⁻¹ := by
          rw [mul_one, ← div_eq_mul_inv, le_div_iff₀ hz2]
          nlinarith [le_max_left C₀ C₁, hC₀]
  ·
    have h1z : 1 ≤ z ^ 2 := by
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ |z| ^ 2 := by gcongr
        _ = z ^ 2 := sq_abs z
    calc ‖D.W (ArchR.diagOne z * k)‖ * |z| ^ (p - 2)
        ≤ C₁ * |z| ^ (-(Nat.ceil p : ℝ)) * |z| ^ (p - 2) := by
          gcongr
          exact h₁ z k hk hz1.le
      _ = C₁ * |z| ^ (p - 2 - Nat.ceil p) := by
          rw [mul_assoc, ← Real.rpow_add haz]; ring_nf
      _ ≤ C₁ * |z| ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1.le (by linarith [Nat.le_ceil p])) hC₁
      _ = C₁ * (z ^ 2)⁻¹ := by
          rw [Real.rpow_neg (abs_nonneg z), Real.rpow_two, sq_abs]
      _ ≤ C₁ * (2 * (1 + z ^ 2)⁻¹) := by
          gcongr
          have hzz : 0 < z ^ 2 := by rw [← sq_abs]; exact pow_pos haz 2
          rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hzz hz2]
          linarith
      _ ≤ max C₀ C₁ * (2 * (1 + z ^ 2)⁻¹) := by
          gcongr
          exact le_max_right _ _
      _ = 2 * max C₀ C₁ * (1 + z ^ 2)⁻¹ := by ring

private theorem norm_W_mul_rpow_le {p K₀ : ℝ}
    (hK : ∀ (z : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → z ≠ 0 →
      ‖D.W (ArchR.diagOne z * k)‖ * |z| ^ (p - 2) ≤ K₀ * (1 + z ^ 2)⁻¹)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {y : ℝ} (hy : y ≠ 0) :
    ‖D.W (ArchR.diagOne y * g)‖ * |y| ^ (p - 2) ≤
      rho g ^ (1 + P.centralExponent.re) * (K₀ * |Yc g| ^ (2 - p)) * (1 + (Yc g * y) ^ 2)⁻¹ := by
  have hρ := rho_pos hg
  have hY := Yc_ne_zero hg
  have haY : 0 < |Yc g| := abs_pos.mpr hY
  have hz : Yc g * y ≠ 0 := mul_ne_zero hY hy
  rw [norm_W_diagOne_mul D hg, mul_comm y (Yc g)]
  have hyz : |y| = |Yc g * y| / |Yc g| := by
    rw [abs_mul]; field_simp
  have hkey := hK (Yc g * y) (kmat g) (kmat_isK hg) hz
  calc rho g ^ (1 + P.centralExponent.re) * ‖D.W (ArchR.diagOne (Yc g * y) * kmat g)‖ * |y| ^ (p - 2)
      = rho g ^ (1 + P.centralExponent.re) *
          ((‖D.W (ArchR.diagOne (Yc g * y) * kmat g)‖ * |Yc g * y| ^ (p - 2)) * |Yc g| ^ (2 - p)) := by
        rw [hyz, Real.div_rpow (abs_nonneg _) haY.le, div_eq_mul_inv, ← Real.rpow_neg haY.le, neg_sub]
        ring
    _ ≤ rho g ^ (1 + P.centralExponent.re) * ((K₀ * (1 + (Yc g * y) ^ 2)⁻¹) * |Yc g| ^ (2 - p)) := by
        gcongr
    _ = rho g ^ (1 + P.centralExponent.re) * (K₀ * |Yc g| ^ (2 - p)) * (1 + (Yc g * y) ^ 2)⁻¹ := by ring

private theorem ae_ne_zero : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
  rw [ae_iff]
  simp

private theorem integral_const_mul_inv_one_add_sq {c Y : ℝ} (hY : Y ≠ 0) :
    Integrable (fun y : ℝ => c * (1 + (Y * y) ^ 2)⁻¹) ∧
      ∫ y : ℝ, c * (1 + (Y * y) ^ 2)⁻¹ = c * (|Y|⁻¹ * Real.pi) := by
  constructor
  · refine Integrable.const_mul ?_ c
    exact (integrable_inv_one_add_sq).comp_mul_left' hY
  · have hcv := Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) Y
    rw [integral_const_mul, hcv, integral_univ_inv_one_add_sq, smul_eq_mul, abs_inv]

private theorem norm_zetaIntegral_le {p K₀ : ℝ}
    (hK : ∀ (z : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → z ≠ 0 →
      ‖D.W (ArchR.diagOne z * k)‖ * |z| ^ (p - 2) ≤ K₀ * (1 + z ^ 2)⁻¹)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (u : ℂ) (a : ZMod 2) {s : ℂ} (hs : s.re + u.re = p) :
    ‖∫ y : ℝ, ArchR.zetaIntegrand D.W g u a s y‖ ≤
      rho g ^ (1 + P.centralExponent.re) * K₀ * Real.pi * |Yc g| ^ (1 - p) := by
  have hρ := rho_pos hg
  have hY := Yc_ne_zero hg
  have haY : 0 < |Yc g| := abs_pos.mpr hY
  set c : ℝ := rho g ^ (1 + P.centralExponent.re) * (K₀ * |Yc g| ^ (2 - p)) with hc
  obtain ⟨hint, hval⟩ := integral_const_mul_inv_one_add_sq (c := c) hY
  have hval' : ∫ y : ℝ, c * (1 + (Yc g * y) ^ 2)⁻¹ =
      rho g ^ (1 + P.centralExponent.re) * K₀ * Real.pi * |Yc g| ^ (1 - p) := by
    rw [hval, hc]
    have : |Yc g| ^ (1 - p) = |Yc g| ^ (2 - p) * |Yc g|⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add haY]; ring_nf
    rw [this]; ring
  rw [← hval']
  refine norm_integral_le_of_norm_le hint ?_
  filter_upwards [ae_ne_zero] with y hy
  rw [norm_zetaIntegrand D hy, hs]
  exact norm_W_mul_rpow_le D hK hg hy

private theorem abs_le_rho_left (g : Matrix (Fin 2) (Fin 2) ℝ) : |g 1 0| ≤ rho g :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg (g 1 1)])

private theorem abs_le_rho_right (g : Matrix (Fin 2) (Fin 2) ℝ) : |g 1 1| ≤ rho g :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg (g 1 0)])

private theorem rho_le_wt (g : Matrix (Fin 2) (Fin 2) ℝ) : rho g ≤ wt g := by
  have h : rho g ≤ |g 1 0| + |g 1 1| := by
    unfold rho
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg (g 1 0), abs_nonneg (g 1 1), sq_abs (g 1 0), sq_abs (g 1 1)]
  unfold wt
  have := abs_nonneg (g 0 0); have := abs_nonneg (g 0 1); have := inv_nonneg.mpr (abs_nonneg g.det)
  linarith

private theorem abs_det_le (g : Matrix (Fin 2) (Fin 2) ℝ) : |g.det| ≤ (|g 0 0| + |g 0 1|) * rho g := by
  rw [det_two]
  calc |g 0 0 * g 1 1 - g 0 1 * g 1 0| ≤ |g 0 0 * g 1 1| + |g 0 1 * g 1 0| := abs_sub _ _
    _ = |g 0 0| * |g 1 1| + |g 0 1| * |g 1 0| := by rw [abs_mul, abs_mul]
    _ ≤ |g 0 0| * rho g + |g 0 1| * rho g := by
        gcongr
        · exact abs_le_rho_right g
        · exact abs_le_rho_left g
    _ = (|g 0 0| + |g 0 1|) * rho g := by ring

private theorem top_le_wt (g : Matrix (Fin 2) (Fin 2) ℝ) : |g 0 0| + |g 0 1| ≤ wt g := by
  unfold wt
  have := abs_nonneg (g 1 0); have := abs_nonneg (g 1 1); have := inv_nonneg.mpr (abs_nonneg g.det)
  linarith

private theorem inv_wt_le_abs_det {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : (wt g)⁻¹ ≤ |g.det| := by
  have hw := one_le_wt g
  have hd : 0 < |g.det| := abs_pos.mpr hg
  rw [inv_le_comm₀ (by linarith) hd]
  unfold wt
  have := abs_nonneg (g 0 0); have := abs_nonneg (g 0 1); have := abs_nonneg (g 1 0)
  have := abs_nonneg (g 1 1)
  linarith

private theorem inv_wt_sq_le_rho {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : ((wt g) ^ 2)⁻¹ ≤ rho g := by
  have hw := one_le_wt g
  have hw0 : 0 < wt g := by linarith
  have h4 : (wt g)⁻¹ ≤ wt g * rho g := by
    calc (wt g)⁻¹ ≤ |g.det| := inv_wt_le_abs_det hg
      _ ≤ (|g 0 0| + |g 0 1|) * rho g := abs_det_le g
      _ ≤ wt g * rho g := by
          gcongr
          · exact (rho_pos hg).le
          · exact top_le_wt g
  calc ((wt g) ^ 2)⁻¹ = (wt g)⁻¹ * (wt g)⁻¹ := by rw [sq, mul_inv]
    _ ≤ (wt g * rho g) * (wt g)⁻¹ := by gcongr
    _ = rho g := by field_simp

private theorem abs_Yc_le {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : |Yc g| ≤ (wt g) ^ 6 := by
  have hw := one_le_wt g
  have hw0 : 0 < wt g := by linarith
  have hρ := rho_pos hg
  have hρw := inv_wt_sq_le_rho hg
  rw [Yc, abs_div, abs_of_pos (pow_pos hρ 2), div_le_iff₀ (pow_pos hρ 2)]
  calc |g.det| ≤ (|g 0 0| + |g 0 1|) * rho g := abs_det_le g
    _ ≤ wt g * wt g := by
        gcongr
        · exact top_le_wt g
        · exact rho_le_wt g
    _ = (wt g) ^ 6 * (((wt g) ^ 2)⁻¹) ^ 2 := by
        rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (by positivity)]
        ring
    _ ≤ (wt g) ^ 6 * (rho g) ^ 2 := by gcongr

private theorem abs_Yc_inv_le {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : |Yc g|⁻¹ ≤ (wt g) ^ 3 := by
  have hw := one_le_wt g
  have hw0 : 0 < wt g := by linarith
  have hρ := rho_pos hg
  have hd : 0 < |g.det| := abs_pos.mpr hg
  rw [Yc, abs_div, abs_of_pos (pow_pos hρ 2), inv_div, div_le_iff₀ hd]
  calc rho g ^ 2 ≤ (wt g) ^ 2 := pow_le_pow_left₀ hρ.le (rho_le_wt g) 2
    _ = (wt g) ^ 3 * (wt g)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hw0.ne']
        ring
    _ ≤ (wt g) ^ 3 * |g.det| := by
        gcongr
        exact inv_wt_le_abs_det hg

private theorem rpow_le_wt_rpow {w x a b : ℝ} (hw : 1 ≤ w) (hx : 0 < x)
    (hlo : w ^ (-a) ≤ x) (hhi : x ≤ w ^ b) (e : ℝ) : x ^ e ≤ w ^ (max a b * |e|) := by
  have hw0 : 0 < w := by linarith
  rcases le_or_gt 0 e with he | he
  · calc x ^ e ≤ (w ^ b) ^ e := Real.rpow_le_rpow hx.le hhi he
      _ = w ^ (b * e) := by rw [← Real.rpow_mul hw0.le]
      _ ≤ w ^ (max a b * |e|) := by
          apply Real.rpow_le_rpow_of_exponent_le hw
          rw [abs_of_nonneg he]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) he
  · calc x ^ e ≤ (w ^ (-a)) ^ e := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hw0 _) hlo he.le
      _ = w ^ (-a * e) := by rw [← Real.rpow_mul hw0.le]
      _ ≤ w ^ (max a b * |e|) := by
          apply Real.rpow_le_rpow_of_exponent_le hw
          rw [abs_of_neg he]
          nlinarith [le_max_left a b, he]

private theorem rho_rpow_le {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (e : ℝ) :
    rho g ^ e ≤ (wt g) ^ (2 * |e|) := by
  have hw := one_le_wt g
  have hw0 : 0 < wt g := by linarith
  have hlo : (wt g) ^ (-2 : ℝ) ≤ rho g := by
    rw [Real.rpow_neg hw0.le, Real.rpow_two]
    exact inv_wt_sq_le_rho hg
  have hhi : rho g ≤ (wt g) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact rho_le_wt g
  have h := rpow_le_wt_rpow hw (rho_pos hg) hlo hhi e
  rwa [show max (2 : ℝ) 1 = 2 by norm_num] at h

private theorem abs_Yc_rpow_le {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (e : ℝ) :
    |Yc g| ^ e ≤ (wt g) ^ (6 * |e|) := by
  have hw := one_le_wt g
  have hw0 : 0 < wt g := by linarith
  have haY : 0 < |Yc g| := abs_pos.mpr (Yc_ne_zero hg)
  have hlo : (wt g) ^ (-3 : ℝ) ≤ |Yc g| := by
    rw [Real.rpow_neg hw0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      inv_le_comm₀ (pow_pos hw0 3) haY]
    exact abs_Yc_inv_le hg
  have hhi : |Yc g| ≤ (wt g) ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact abs_Yc_le hg
  have h := rpow_le_wt_rpow hw haY hlo hhi e
  rwa [show max (3 : ℝ) 6 = 6 by norm_num] at h

private theorem exists_line_data (u : ℂ) (a : ZMod 2) :
    ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c →
      D.zeta_abscissa < c + u.re ∧
      (∃ CL EL : ℝ, 0 ≤ CL ∧ 0 ≤ EL ∧ ∀ z : ℂ, z.re = c →
        (P.twist u a).archFactor z ≠ 0 ∧ ‖((P.twist u a).archFactor z)⁻¹‖ ≤ CL * Real.exp (EL * |z.im|)) ∧
      (∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (z : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → z ≠ 0 →
        ‖D.W (ArchR.diagOne z * k)‖ * |z| ^ (c + u.re - 2) ≤ K₀ * (1 + z ^ 2)⁻¹) := by
  obtain ⟨p₀, hp₀⟩ := exists_dominator D
  obtain ⟨T, hTR, hTC⟩ := exists_shift_bound (P.twist u a)
  refine ⟨max (max (T + 1) (D.zeta_abscissa + 1 - u.re)) (p₀ - u.re), fun c hc => ?_⟩
  have hcT : T + 1 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hcA : D.zeta_abscissa + 1 - u.re ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hcp : p₀ - u.re ≤ c := le_trans (le_max_right _ _) hc
  refine ⟨by linarith, ?_, hp₀ (c + u.re) (by linarith)⟩
  exact norm_inv_archFactor_le (P.twist u a) c
    (fun μ hμ => by linarith [hTR μ hμ]) (fun ν hν => by linarith [hTC ν hν])

private theorem exists_line_bound (u : ℂ) (a : ZMod 2) :
    ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∃ (C E : ℝ) (N : ℕ), 0 ≤ C ∧ 0 ≤ E ∧
      ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 → ∀ s : ℂ, s.re = c →
        ‖D.zetaEntire g u a s‖ ≤ C * (wt g) ^ N * Real.exp (E * |s.im|) := by
  obtain ⟨c₀, hdat⟩ := exists_line_data D u a
  refine ⟨c₀, fun c hc => ?_⟩
  obtain ⟨hcA, ⟨CL, EL, hCL, hEL, hL⟩, ⟨K₀, hK₀, hK⟩⟩ := hdat c hc
  set e₁ : ℝ := 1 + P.centralExponent.re with he₁
  set e₂ : ℝ := 1 - (c + u.re) with he₂
  refine ⟨CL * (K₀ * Real.pi), EL, Nat.ceil (2 * |e₁| + 6 * |e₂|), by positivity, hEL, ?_⟩
  intro g hg s hs
  have hw := one_le_wt g
  have hw0 : 0 < wt g := by linarith
  obtain ⟨hLz, hLb⟩ := hL s hs
  have hzeq := D.zeta_eq g u a s hg (by rw [hs]; exact hcA)
  have hΦ : D.zetaEntire g u a s =
      ((P.twist u a).archFactor s)⁻¹ * ∫ y : ℝ, ArchR.zetaIntegrand D.W g u a s y := by
    rw [hzeq, ← mul_assoc, inv_mul_cancel₀ hLz, one_mul]
  have hZ := norm_zetaIntegral_le D hK hg u a (s := s) (by rw [hs])
  have hρe : rho g ^ e₁ ≤ (wt g) ^ (2 * |e₁|) := rho_rpow_le hg e₁
  have hYe : |Yc g| ^ e₂ ≤ (wt g) ^ (6 * |e₂|) := abs_Yc_rpow_le hg e₂
  have hpow : (wt g) ^ (2 * |e₁|) * (wt g) ^ (6 * |e₂|) ≤ (wt g) ^ (Nat.ceil (2 * |e₁| + 6 * |e₂|)) := by
    rw [← Real.rpow_add hw0, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hw (Nat.le_ceil _)
  calc ‖D.zetaEntire g u a s‖
      = ‖((P.twist u a).archFactor s)⁻¹‖ * ‖∫ y : ℝ, ArchR.zetaIntegrand D.W g u a s y‖ := by
        rw [hΦ, norm_mul]
    _ ≤ (CL * Real.exp (EL * |s.im|)) * (rho g ^ e₁ * K₀ * Real.pi * |Yc g| ^ e₂) := by gcongr
    _ = CL * (K₀ * Real.pi) * (rho g ^ e₁ * |Yc g| ^ e₂) * Real.exp (EL * |s.im|) := by ring
    _ ≤ CL * (K₀ * Real.pi) * ((wt g) ^ (2 * |e₁|) * (wt g) ^ (6 * |e₂|)) * Real.exp (EL * |s.im|) := by
        gcongr
    _ ≤ CL * (K₀ * Real.pi) * (wt g) ^ (Nat.ceil (2 * |e₁| + 6 * |e₂|)) * Real.exp (EL * |s.im|) := by
        gcongr

private theorem wt_weyl_mul (g : Matrix (Fin 2) (Fin 2) ℝ) : wt (ArchR.weyl * g) = wt g := by
  have hdet : (ArchR.weyl * g).det = g.det := by
    rw [Matrix.det_mul]
    simp [ArchR.weyl, Matrix.det_fin_two_of]
  have h00 : (ArchR.weyl * g) 0 0 = g 1 0 := by simp [ArchR.weyl, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (ArchR.weyl * g) 0 1 = g 1 1 := by simp [ArchR.weyl, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (ArchR.weyl * g) 1 0 = -g 0 0 := by simp [ArchR.weyl, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (ArchR.weyl * g) 1 1 = -g 0 1 := by simp [ArchR.weyl, Matrix.mul_apply, Fin.sum_univ_two]
  unfold wt
  rw [hdet, h00, h01, h10, h11, abs_neg, abs_neg]
  ring

private theorem det_weyl_mul_ne_zero {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : (ArchR.weyl * g).det ≠ 0 := by
  rw [Matrix.det_mul]
  simpa [ArchR.weyl, Matrix.det_fin_two_of] using hg

private theorem strip_bound (u : ℂ) (a : ZMod 2) (σ₁ σ₂ : ℝ) :
    ∃ (C A : ℝ) (N : ℕ), ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖D.zetaEntire g u a s‖ ≤
          C * (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N * Real.exp (A * |s.im|) := by
  obtain ⟨cR₀, hR⟩ := exists_line_bound D u a
  obtain ⟨cL₀, hLft⟩ := exists_line_bound D (-(u + P.centralExponent)) (a + P.centralSign)
  set cL : ℝ := max cL₀ (1 - σ₁) with hcL
  set σL : ℝ := 1 - cL with hσL
  set σR : ℝ := max (max cR₀ σ₂) (σL + 1) with hσR
  obtain ⟨CR, ER, NR, hCR, hER, hbR⟩ := hR σR (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨CL, EL, NL, hCL, hEL, hbL⟩ := hLft cL (le_max_left _ _)
  have hσL1 : σL ≤ σ₁ := by
    have : 1 - σ₁ ≤ cL := le_max_right _ _
    rw [hσL]; linarith
  have hσR2 : σ₂ ≤ σR := le_trans (le_max_right _ _) (le_max_left _ _)
  have hLR : σL < σR := by
    have : σL + 1 ≤ σR := le_max_right _ _
    linarith
  have hε := epsilonFactor_ne_zero (P.twist u a)
  set Cε : ℝ := ‖((P.twist u a).epsilonFactor)⁻¹‖ with hCε
  set C₀ : ℝ := max CR (Cε * CL) with hC₀def
  set E₀ : ℝ := max ER EL with hE₀def
  set N₀ : ℕ := max NR NL with hN₀def
  have hC₀ : 0 ≤ C₀ := le_max_of_le_left hCR
  have hE₀ : 0 ≤ E₀ := le_max_of_le_left hER
  refine ⟨C₀ * Real.exp ((σR - σL) ^ 2 + E₀ ^ 2 / 4), E₀, N₀, fun g hg s hs₁ hs₂ => ?_⟩
  have hw := one_le_wt g
  have hw0 : 0 < wt g := by linarith
  have hbd : ∀ z : ℂ, (z.re = σL ∨ z.re = σR) →
      ‖D.zetaEntire g u a z‖ ≤ C₀ * (wt g) ^ N₀ * Real.exp (E₀ * |z.im|) := by
    intro z hz
    rcases hz with hz | hz
    · have hΦ : D.zetaEntire g u a z = ((P.twist u a).epsilonFactor)⁻¹ *
          D.zetaEntire (ArchR.weyl * g) (-(u + P.centralExponent)) (a + P.centralSign) (1 - z) := by
        rw [D.functional_equation g u a z hg, ← mul_assoc, inv_mul_cancel₀ hε, one_mul]
      have hre : (1 - z).re = cL := by
        rw [Complex.sub_re, Complex.one_re, hz, hσL]; ring
      have him : |(1 - z).im| = |z.im| := by
        rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      have hb := hbL (ArchR.weyl * g) (det_weyl_mul_ne_zero hg) (1 - z) hre
      rw [wt_weyl_mul, him] at hb
      calc ‖D.zetaEntire g u a z‖
          = Cε * ‖D.zetaEntire (ArchR.weyl * g) (-(u + P.centralExponent)) (a + P.centralSign) (1 - z)‖ := by
            rw [hΦ, norm_mul]
        _ ≤ Cε * (CL * (wt g) ^ NL * Real.exp (EL * |z.im|)) := by gcongr
        _ = (Cε * CL) * (wt g) ^ NL * Real.exp (EL * |z.im|) := by ring
        _ ≤ C₀ * (wt g) ^ N₀ * Real.exp (E₀ * |z.im|) := by
            gcongr
            all_goals first | exact hw | exact le_max_right _ _
    · calc ‖D.zetaEntire g u a z‖ ≤ CR * (wt g) ^ NR * Real.exp (ER * |z.im|) := hbR g hg z hz
        _ ≤ C₀ * (wt g) ^ N₀ * Real.exp (E₀ * |z.im|) := by
            gcongr
            all_goals first | exact hw | exact le_max_left _ _
  have hkey := norm_le_of_norm_le_on_lines (D.zetaEntire_differentiable g u a) hLR
    (mul_nonneg hC₀ (pow_nonneg hw0.le N₀)) hE₀ hbd (D.zetaEntire_finiteOrder g u a σL σR)
    (show σL ≤ s.re by linarith) (show s.re ≤ σR by linarith)
  calc ‖D.zetaEntire g u a s‖
      ≤ C₀ * (wt g) ^ N₀ * Real.exp ((σR - σL) ^ 2 + E₀ ^ 2 / 4) * Real.exp (E₀ * |s.im|) := hkey
    _ = C₀ * Real.exp ((σR - σL) ^ 2 + E₀ ^ 2 / 4) * (wt g) ^ N₀ * Real.exp (E₀ * |s.im|) := by ring
    _ = C₀ * Real.exp ((σR - σL) ^ 2 + E₀ ^ 2 / 4) *
          (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N₀ * Real.exp (E₀ * |s.im|) := rfl

private theorem continuous_matrixOf : Continuous (fun M : Fin 2 → Fin 2 → ℝ => Matrix.of M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply j).comp (continuous_apply i)

private theorem continuous_matrixOfSymm : Continuous (fun g : Matrix (Fin 2) (Fin 2) ℝ => Matrix.of.symm g) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_id.matrix_elem i j

private theorem isOpen_glSet : IsOpen ArchR.glSet := by
  have : ArchR.glSet = (fun M : Fin 2 → Fin 2 → ℝ => (Matrix.of M).det) ⁻¹' {0}ᶜ := rfl
  rw [this]
  exact isOpen_compl_singleton.preimage continuous_matrixOf.matrix_det

private theorem continuousAt_W {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : ContinuousAt D.W g := by
  have h1 : ContinuousOn (ArchR.asPi D.W) ArchR.glSet := D.smooth.continuousOn
  have hmem : Matrix.of.symm g ∈ ArchR.glSet := by
    show (Matrix.of (Matrix.of.symm g)).det ≠ 0
    simpa using hg
  have h2 : ContinuousAt (ArchR.asPi D.W) (Matrix.of.symm g) := h1.continuousAt (isOpen_glSet.mem_nhds hmem)
  have hW : D.W = fun h => ArchR.asPi D.W (Matrix.of.symm h) := by
    funext h
    simp [ArchR.asPi]
  rw [hW]
  exact h2.comp continuous_matrixOfSymm.continuousAt

private theorem det_diagOne_mul_ne_zero {y : ℝ} (hy : y ≠ 0) {h : Matrix (Fin 2) (Fin 2) ℝ} (hh : h.det ≠ 0) :
    (ArchR.diagOne y * h).det ≠ 0 := by
  rw [Matrix.det_mul]
  refine mul_ne_zero ?_ hh
  simp [ArchR.diagOne, Matrix.det_fin_two_of, hy]

private theorem continuous_diagOne : Continuous (fun y : ℝ => ArchR.diagOne y) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne]
  all_goals fun_prop

private theorem continuousAt_W_diagOne_mul {y : ℝ} (hy : y ≠ 0) {h₀ : Matrix (Fin 2) (Fin 2) ℝ} (hh₀ : h₀.det ≠ 0) :
    ContinuousAt (fun h : Matrix (Fin 2) (Fin 2) ℝ => D.W (ArchR.diagOne y * h)) h₀ := by
  have hc : Continuous (fun h : Matrix (Fin 2) (Fin 2) ℝ => ArchR.diagOne y * h) :=
    continuous_const.matrix_mul continuous_id
  exact ContinuousAt.comp (f := fun h : Matrix (Fin 2) (Fin 2) ℝ => ArchR.diagOne y * h)
    (continuousAt_W D (det_diagOne_mul_ne_zero hy hh₀)) hc.continuousAt

private theorem continuousOn_W_diagOne {h : Matrix (Fin 2) (Fin 2) ℝ} (hh : h.det ≠ 0) :
    ContinuousOn (fun y : ℝ => D.W (ArchR.diagOne y * h)) {0}ᶜ := by
  intro y hy
  have hy' : y ≠ 0 := hy
  have hc : Continuous (fun y : ℝ => ArchR.diagOne y * h) := continuous_diagOne.matrix_mul continuous_const
  have h2 : ContinuousAt (fun y : ℝ => D.W (ArchR.diagOne y * h)) y :=
    ContinuousAt.comp (f := fun y : ℝ => ArchR.diagOne y * h) (continuousAt_W D (det_diagOne_mul_ne_zero hy' hh))
      hc.continuousAt
  exact h2.continuousWithinAt

private theorem aestronglyMeasurable_diff {h h₀ : Matrix (Fin 2) (Fin 2) ℝ} (hh : h.det ≠ 0) (hh₀ : h₀.det ≠ 0)
    (p : ℝ) : AEStronglyMeasurable
      (fun y : ℝ => ‖D.W (ArchR.diagOne y * h) - D.W (ArchR.diagOne y * h₀)‖ * |y| ^ (p - 2)) volume := by
  rw [← restrict_compl_singleton (μ := volume) (0 : ℝ)]
  refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_singleton 0).compl
  refine ((continuousOn_W_diagOne D hh).sub (continuousOn_W_diagOne D hh₀)).norm.mul ?_
  exact continuous_abs.continuousOn.rpow_const fun y hy => Or.inl (abs_ne_zero.mpr hy)

private theorem continuousAt_wt {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : ContinuousAt wt g := by
  have he : ∀ i j : Fin 2, Continuous fun g : Matrix (Fin 2) (Fin 2) ℝ => |g i j| :=
    fun i j => (continuous_id.matrix_elem i j).abs
  have hd : ContinuousAt (fun g : Matrix (Fin 2) (Fin 2) ℝ => |g.det|⁻¹) g :=
    ((continuous_id.matrix_det).abs.continuousAt).inv₀ (abs_ne_zero.mpr hg)
  have h := ((((continuous_const (y := (1 : ℝ))).add (he 0 0)).add (he 0 1)).add (he 1 0)).add (he 1 1)
  exact h.continuousAt.add hd

private theorem eventually_det_ne_zero_and_wt_le {h₀ : Matrix (Fin 2) (Fin 2) ℝ} (hh₀ : h₀.det ≠ 0) :
    ∀ᶠ h in nhds h₀, h.det ≠ 0 ∧ wt h ≤ wt h₀ + 1 := by
  have h1 : ∀ᶠ h in nhds h₀, h.det ≠ 0 :=
    (continuous_id.matrix_det).continuousAt.eventually_ne hh₀
  have h2 : ∀ᶠ h in nhds h₀, wt h ∈ Iio (wt h₀ + 1) :=
    (continuousAt_wt hh₀).eventually_mem (Iio_mem_nhds (lt_add_one _))
  filter_upwards [h1, h2] with h hh hw
  exact ⟨hh, le_of_lt hw⟩

private theorem dominator_le_of_wt_le {p K₀ W₁ : ℝ} (hK₀ : 0 ≤ K₀) {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (hgw : wt g ≤ W₁) (y : ℝ) :
    rho g ^ (1 + P.centralExponent.re) * (K₀ * |Yc g| ^ (2 - p)) * (1 + (Yc g * y) ^ 2)⁻¹ ≤
      W₁ ^ (2 * |1 + P.centralExponent.re|) * (K₀ * W₁ ^ (6 * |2 - p|)) * (1 + ((W₁ ^ 3)⁻¹ * y) ^ 2)⁻¹ := by
  have hw := one_le_wt g
  have hw0 : 0 < wt g := by linarith
  have hW : 1 ≤ W₁ := hw.trans hgw
  have hW0 : 0 < W₁ := by linarith
  have haY : 0 < |Yc g| := abs_pos.mpr (Yc_ne_zero hg)
  have h1 : rho g ^ (1 + P.centralExponent.re) ≤ W₁ ^ (2 * |1 + P.centralExponent.re|) :=
    (rho_rpow_le hg _).trans (Real.rpow_le_rpow hw0.le hgw (by positivity))
  have h2 : |Yc g| ^ (2 - p) ≤ W₁ ^ (6 * |2 - p|) :=
    (abs_Yc_rpow_le hg _).trans (Real.rpow_le_rpow hw0.le hgw (by positivity))
  have h3 : (W₁ ^ 3)⁻¹ ≤ |Yc g| := by
    have hY3 : ((wt g) ^ 3)⁻¹ ≤ |Yc g| := inv_le_of_inv_le₀ haY (abs_Yc_inv_le hg)
    exact (inv_anti₀ (pow_pos hw0 3) (pow_le_pow_left₀ hw0.le hgw 3)).trans hY3
  have h4 : (1 + (Yc g * y) ^ 2)⁻¹ ≤ (1 + ((W₁ ^ 3)⁻¹ * y) ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    have : |(W₁ ^ 3)⁻¹ * y| ≤ |Yc g * y| := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (W₁ ^ 3)⁻¹)]
      exact mul_le_mul_of_nonneg_right h3 (abs_nonneg y)
    have hsq : ((W₁ ^ 3)⁻¹ * y) ^ 2 ≤ (Yc g * y) ^ 2 := by
      rw [← sq_abs ((W₁ ^ 3)⁻¹ * y), ← sq_abs (Yc g * y)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    linarith
  gcongr

private theorem tendsto_integral_diff {h₀ : Matrix (Fin 2) (Fin 2) ℝ} (hh₀ : h₀.det ≠ 0) {p K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK : ∀ (z : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → z ≠ 0 →
      ‖D.W (ArchR.diagOne z * k)‖ * |z| ^ (p - 2) ≤ K₀ * (1 + z ^ 2)⁻¹) :
    Filter.Tendsto
      (fun h : Matrix (Fin 2) (Fin 2) ℝ =>
        ∫ y : ℝ, ‖D.W (ArchR.diagOne y * h) - D.W (ArchR.diagOne y * h₀)‖ * |y| ^ (p - 2))
      (nhds h₀) (nhds 0) := by
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))
  set W₁ : ℝ := wt h₀ + 1 with hW₁
  have hW₁0 : 0 < W₁ := by have := one_le_wt h₀; rw [hW₁]; linarith
  set B : ℝ := W₁ ^ (2 * |1 + P.centralExponent.re|) * (K₀ * W₁ ^ (6 * |2 - p|)) with hB
  have hc0 : (W₁ ^ 3)⁻¹ ≠ 0 := by positivity
  obtain ⟨hint, -⟩ := integral_const_mul_inv_one_add_sq (c := 2 * B) hc0
  have hev := eventually_det_ne_zero_and_wt_le hh₀
  have hlim := tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => 2 * B * (1 + ((W₁ ^ 3)⁻¹ * y) ^ 2)⁻¹)
    (μ := volume) (l := nhds h₀)
    (F := fun (h : Matrix (Fin 2) (Fin 2) ℝ) (y : ℝ) =>
      ‖D.W (ArchR.diagOne y * h) - D.W (ArchR.diagOne y * h₀)‖ * |y| ^ (p - 2))
    (f := fun _ => 0) ?_ ?_ hint ?_
  · simpa using hlim
  · filter_upwards [hev] with h hh
    exact aestronglyMeasurable_diff D hh.1 hh₀ p
  · filter_upwards [hev] with h hh
    filter_upwards [ae_ne_zero] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    have hb := norm_W_mul_rpow_le D hK hh.1 hy
    have hb₀ := norm_W_mul_rpow_le D hK hh₀ hy
    have hd := dominator_le_of_wt_le (P := P) (p := p) hK₀ hh.1 hh.2 y
    have hd₀ := dominator_le_of_wt_le (P := P) (p := p) (W₁ := wt h₀ + 1) hK₀ hh₀ (by linarith) y
    calc ‖D.W (ArchR.diagOne y * h) - D.W (ArchR.diagOne y * h₀)‖ * |y| ^ (p - 2)
        ≤ (‖D.W (ArchR.diagOne y * h)‖ + ‖D.W (ArchR.diagOne y * h₀)‖) * |y| ^ (p - 2) := by
          gcongr
          exact norm_sub_le _ _
      _ = ‖D.W (ArchR.diagOne y * h)‖ * |y| ^ (p - 2) + ‖D.W (ArchR.diagOne y * h₀)‖ * |y| ^ (p - 2) := by
          ring
      _ ≤ B * (1 + ((W₁ ^ 3)⁻¹ * y) ^ 2)⁻¹ + B * (1 + ((W₁ ^ 3)⁻¹ * y) ^ 2)⁻¹ :=
          add_le_add (hb.trans hd) (hb₀.trans hd₀)
      _ = 2 * B * (1 + ((W₁ ^ 3)⁻¹ * y) ^ 2)⁻¹ := by ring
  · filter_upwards [ae_ne_zero] with y hy
    have hc := (continuousAt_W_diagOne_mul D hy hh₀).tendsto
    have h1 := (hc.sub_const (D.W (ArchR.diagOne y * h₀))).norm.mul_const (|y| ^ (p - 2))
    simpa using h1

private theorem norm_sub_le_on_line {u : ℂ} {a : ZMod 2} {c : ℝ} (hA : D.zeta_abscissa < c + u.re) {CL EL : ℝ}
    (hL : ∀ z : ℂ, z.re = c →
      (P.twist u a).archFactor z ≠ 0 ∧ ‖((P.twist u a).archFactor z)⁻¹‖ ≤ CL * Real.exp (EL * |z.im|))
    {h h₀ : Matrix (Fin 2) (Fin 2) ℝ} (hh : h.det ≠ 0) (hh₀ : h₀.det ≠ 0) {z : ℂ} (hz : z.re = c) :
    ‖D.zetaEntire h u a z - D.zetaEntire h₀ u a z‖ ≤ CL * Real.exp (EL * |z.im|) *
      ∫ y : ℝ, ‖D.W (ArchR.diagOne y * h) - D.W (ArchR.diagOne y * h₀)‖ * |y| ^ (c + u.re - 2) := by
  obtain ⟨hLz, hLb⟩ := hL z hz
  have hΦ : ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 → D.zetaEntire g u a z =
      ((P.twist u a).archFactor z)⁻¹ * ∫ y : ℝ, ArchR.zetaIntegrand D.W g u a z y := by
    intro g hg
    rw [D.zeta_eq g u a z hg (by rw [hz]; exact hA), ← mul_assoc, inv_mul_cancel₀ hLz, one_mul]
  have hintg := D.zeta_integrable h u a z hh (by rw [hz]; exact hA)
  have hintg₀ := D.zeta_integrable h₀ u a z hh₀ (by rw [hz]; exact hA)
  have hdiff : ‖(∫ y : ℝ, ArchR.zetaIntegrand D.W h u a z y) - ∫ y : ℝ, ArchR.zetaIntegrand D.W h₀ u a z y‖ ≤
      ∫ y : ℝ, ‖D.W (ArchR.diagOne y * h) - D.W (ArchR.diagOne y * h₀)‖ * |y| ^ (c + u.re - 2) := by
    rw [← integral_sub hintg hintg₀]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with y hy
    show ‖ArchR.zetaIntegrand D.W h u a z y - ArchR.zetaIntegrand D.W h₀ u a z y‖ = _
    rw [norm_zetaIntegrand_sub D hy, hz]
  rw [hΦ h hh, hΦ h₀ hh₀, ← mul_sub, norm_mul]
  exact mul_le_mul hLb hdiff (norm_nonneg _) ((norm_nonneg _).trans hLb)

private theorem continuousAt_zetaEntire (u : ℂ) (a : ZMod 2) (s : ℂ) {g₀ : Matrix (Fin 2) (Fin 2) ℝ}
    (hg₀ : g₀.det ≠ 0) :
    ContinuousAt (fun g : Matrix (Fin 2) (Fin 2) ℝ => D.zetaEntire g u a s) g₀ := by

  obtain ⟨cR₀, hdatR⟩ := exists_line_data D u a
  obtain ⟨cL₀, hdatL⟩ := exists_line_data D (-(u + P.centralExponent)) (a + P.centralSign)
  set cL : ℝ := max cL₀ (1 - s.re) with hcL
  set σL : ℝ := 1 - cL with hσL
  set σR : ℝ := max (max cR₀ s.re) (σL + 1) with hσR
  obtain ⟨hAR, ⟨CR, ER, hCR, hER, hLR'⟩, ⟨KR, hKR, hKRb⟩⟩ :=
    hdatR σR (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨hAL, ⟨CL, EL, hCL, hEL, hLL'⟩, ⟨KL, hKL, hKLb⟩⟩ := hdatL cL (le_max_left _ _)
  have hσLs : σL ≤ s.re := by
    have : 1 - s.re ≤ cL := le_max_right _ _
    rw [hσL]; linarith
  have hσRs : s.re ≤ σR := le_trans (le_max_right _ _) (le_max_left _ _)
  have hLR : σL < σR := by
    have : σL + 1 ≤ σR := le_max_right _ _
    linarith
  have hε := epsilonFactor_ne_zero (P.twist u a)
  set Cε : ℝ := ‖((P.twist u a).epsilonFactor)⁻¹‖ with hCε
  set E₀ : ℝ := max ER EL with hE₀def
  have hE₀ : 0 ≤ E₀ := le_max_of_le_left hER

  set δR : Matrix (Fin 2) (Fin 2) ℝ → ℝ := fun h =>
    ∫ y : ℝ, ‖D.W (ArchR.diagOne y * h) - D.W (ArchR.diagOne y * g₀)‖ * |y| ^ (σR + u.re - 2) with hδR
  set δL : Matrix (Fin 2) (Fin 2) ℝ → ℝ := fun h =>
    ∫ y : ℝ, ‖D.W (ArchR.diagOne y * (ArchR.weyl * h)) - D.W (ArchR.diagOne y * (ArchR.weyl * g₀))‖ *
      |y| ^ (cL + (-(u + P.centralExponent)).re - 2) with hδL
  have hδR0 : ∀ h, 0 ≤ δR h := fun h => integral_nonneg fun y => by positivity
  have hδL0 : ∀ h, 0 ≤ δL h := fun h => integral_nonneg fun y => by positivity
  have htR : Filter.Tendsto δR (nhds g₀) (nhds 0) := tendsto_integral_diff D hg₀ hKR hKRb
  have htL : Filter.Tendsto δL (nhds g₀) (nhds 0) := by
    have hw : Continuous (fun h : Matrix (Fin 2) (Fin 2) ℝ => ArchR.weyl * h) :=
      continuous_const.matrix_mul continuous_id
    have := tendsto_integral_diff D (det_weyl_mul_ne_zero hg₀) hKL hKLb
    exact this.comp hw.continuousAt

  set K : ℝ := Real.exp ((σR - σL) ^ 2 + E₀ ^ 2 / 4) * Real.exp (E₀ * |s.im|) with hKdef
  have hbound : ∀ᶠ h in nhds g₀, ‖D.zetaEntire h u a s - D.zetaEntire g₀ u a s‖ ≤
      (CR * δR h + Cε * CL * δL h) * K := by
    filter_upwards [eventually_det_ne_zero_and_wt_le hg₀] with h hh
    have hhd := hh.1

    have hF : Differentiable ℂ (fun z => D.zetaEntire h u a z - D.zetaEntire g₀ u a z) :=
      (D.zetaEntire_differentiable h u a).sub (D.zetaEntire_differentiable g₀ u a)
    have hfo : ∃ C' E' : ℝ, ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR →
        ‖D.zetaEntire h u a z - D.zetaEntire g₀ u a z‖ ≤ C' * Real.exp (E' * |z.im|) := by
      obtain ⟨C₁, D₁, h₁⟩ := D.zetaEntire_finiteOrder h u a σL σR
      obtain ⟨C₂, D₂, h₂⟩ := D.zetaEntire_finiteOrder g₀ u a σL σR
      refine ⟨|C₁| + |C₂|, max (max D₁ D₂) 0, fun z hz1 hz2 => ?_⟩
      have e1 : Real.exp (D₁ * |z.im|) ≤ Real.exp (max (max D₁ D₂) 0 * |z.im|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) (abs_nonneg _))
      have e2 : Real.exp (D₂ * |z.im|) ≤ Real.exp (max (max D₁ D₂) 0 * |z.im|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) (abs_nonneg _))
      calc ‖D.zetaEntire h u a z - D.zetaEntire g₀ u a z‖
          ≤ ‖D.zetaEntire h u a z‖ + ‖D.zetaEntire g₀ u a z‖ := norm_sub_le _ _
        _ ≤ C₁ * Real.exp (D₁ * |z.im|) + C₂ * Real.exp (D₂ * |z.im|) := add_le_add (h₁ z hz1 hz2) (h₂ z hz1 hz2)
        _ ≤ |C₁| * Real.exp (D₁ * |z.im|) + |C₂| * Real.exp (D₂ * |z.im|) := by
            gcongr
            · exact le_abs_self _
            · exact le_abs_self _
        _ ≤ |C₁| * Real.exp (max (max D₁ D₂) 0 * |z.im|) + |C₂| * Real.exp (max (max D₁ D₂) 0 * |z.im|) := by
            gcongr
        _ = (|C₁| + |C₂|) * Real.exp (max (max D₁ D₂) 0 * |z.im|) := by ring
    have hbd : ∀ z : ℂ, (z.re = σL ∨ z.re = σR) → ‖D.zetaEntire h u a z - D.zetaEntire g₀ u a z‖ ≤
        (CR * δR h + Cε * CL * δL h) * Real.exp (E₀ * |z.im|) := by
      intro z hz
      have hexpR : Real.exp (ER * |z.im|) ≤ Real.exp (E₀ * |z.im|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      have hexpL : Real.exp (EL * |z.im|) ≤ Real.exp (E₀ * |z.im|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
      have hR0 : 0 ≤ CR * δR h := mul_nonneg hCR (hδR0 h)
      have hL0 : 0 ≤ Cε * CL * δL h := by have := hδL0 h; positivity
      rcases hz with hz | hz
      ·
        have hre : (1 - z).re = cL := by
          rw [Complex.sub_re, Complex.one_re, hz, hσL]; ring
        have him : |(1 - z).im| = |z.im| := by
          rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
        have hΦ : ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 → D.zetaEntire g u a z =
            ((P.twist u a).epsilonFactor)⁻¹ *
              D.zetaEntire (ArchR.weyl * g) (-(u + P.centralExponent)) (a + P.centralSign) (1 - z) := by
          intro g hg
          rw [D.functional_equation g u a z hg, ← mul_assoc, inv_mul_cancel₀ hε, one_mul]
        have hline := norm_sub_le_on_line D hAL hLL' (det_weyl_mul_ne_zero hhd) (det_weyl_mul_ne_zero hg₀) hre
        rw [him] at hline
        calc ‖D.zetaEntire h u a z - D.zetaEntire g₀ u a z‖
            = Cε * ‖D.zetaEntire (ArchR.weyl * h) (-(u + P.centralExponent)) (a + P.centralSign) (1 - z) -
                D.zetaEntire (ArchR.weyl * g₀) (-(u + P.centralExponent)) (a + P.centralSign) (1 - z)‖ := by
              rw [hΦ h hhd, hΦ g₀ hg₀, ← mul_sub, norm_mul]
          _ ≤ Cε * (CL * Real.exp (EL * |z.im|) * δL h) := by gcongr
          _ = Cε * CL * δL h * Real.exp (EL * |z.im|) := by ring
          _ ≤ (CR * δR h + Cε * CL * δL h) * Real.exp (E₀ * |z.im|) := by
              gcongr
              linarith
      ·
        have hline := norm_sub_le_on_line D hAR hLR' hhd hg₀ hz
        calc ‖D.zetaEntire h u a z - D.zetaEntire g₀ u a z‖ ≤ CR * Real.exp (ER * |z.im|) * δR h := hline
          _ = CR * δR h * Real.exp (ER * |z.im|) := by ring
          _ ≤ (CR * δR h + Cε * CL * δL h) * Real.exp (E₀ * |z.im|) := by
              gcongr
              linarith
    have hC : 0 ≤ CR * δR h + Cε * CL * δL h := by
      have := hδR0 h; have := hδL0 h; positivity
    have hkey := norm_le_of_norm_le_on_lines hF hLR hC hE₀ hbd hfo hσLs hσRs
    calc ‖D.zetaEntire h u a s - D.zetaEntire g₀ u a s‖
        ≤ (CR * δR h + Cε * CL * δL h) * Real.exp ((σR - σL) ^ 2 + E₀ ^ 2 / 4) * Real.exp (E₀ * |s.im|) := hkey
      _ = (CR * δR h + Cε * CL * δL h) * K := by rw [hKdef]; ring

  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun h => norm_nonneg _) hbound ?_
  have : Filter.Tendsto (fun h => (CR * δR h + Cε * CL * δL h) * K) (nhds g₀)
      (nhds ((CR * 0 + Cε * CL * 0) * K)) :=
    ((htR.const_mul CR).add (htL.const_mul (Cε * CL))).mul_const K
  simpa using this

private theorem continuousOn_zetaEntire (u : ℂ) (a : ZMod 2) (s : ℂ) :
    ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => D.zetaEntire (Matrix.of M) u a s) ArchR.glSet := by
  intro M₀ hM₀
  have hg₀ : (Matrix.of M₀).det ≠ 0 := hM₀
  have h := continuousAt_zetaEntire D u a s hg₀
  exact (h.comp continuous_matrixOf.continuousAt).continuousWithinAt

private theorem main (u : ℂ) (a : ZMod 2) :
    (∀ σ₁ σ₂ : ℝ, ∃ (C A : ℝ) (N : ℕ), ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖D.zetaEntire g u a s‖ ≤
          C * (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N * Real.exp (A * |s.im|)) ∧
    ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => D.zetaEntire (Matrix.of M) u a s) ArchR.glSet :=
  ⟨fun σ₁ σ₂ => strip_bound D u a σ₁ σ₂, fun s => continuousOn_zetaEntire D u a s⟩

end Datum

end ArchZetaUniform

theorem solution
    {P : RealArchParam} (D : ArchDatumR P) (u : ℂ) (a : ZMod 2) :
    (∀ σ₁ σ₂ : ℝ, ∃ (C A : ℝ) (N : ℕ), ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖D.zetaEntire g u a s‖ ≤
          C * (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N * Real.exp (A * |s.im|)) ∧
    ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => D.zetaEntire (Matrix.of M) u a s) ArchR.glSet := by
  exact ArchZetaUniform.main D u a

end S_LanglandsTunnell_Converse_ArchDatumR_exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn (solution)

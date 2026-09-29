-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.exists_lt_mellin_W_diagOne_ne_zero_of_weightZero_of_parity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cdb10fe7-bbef-5c0f-bbd0-4d25dd1d3099

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_mellin_W_diagOne_ne_zero_of_weightZero_of_parity

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace Ws23TMNZ

open LanglandsTunnell.Converse.ArchR

noncomputable def rotM (c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d / Real.sqrt (c ^ 2 + d ^ 2), -c / Real.sqrt (c ^ 2 + d ^ 2); c / Real.sqrt (c ^ 2 + d ^ 2), d / Real.sqrt (c ^ 2 + d ^ 2)]

theorem sqrt_pos_of {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : 0 < Real.sqrt (c ^ 2 + d ^ 2) := by
  apply Real.sqrt_pos.2
  rcases h with h | h
  · have := sq_pos_of_ne_zero h; positivity
  · have := sq_pos_of_ne_zero h; positivity

theorem det_rotM {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : (rotM c d).det = 1 := by
  have hr := sqrt_pos_of h
  have hr2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  rw [rotM, Matrix.det_fin_two_of]
  field_simp
  linarith [hr2]

noncomputable def rotGL {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM c d) (by rw [det_rotM h]; exact one_ne_zero)

theorem rotGL_coe {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : ((rotGL h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM c d := rfl

theorem rotGL_mem {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : rotGL h ∈ rowIsometrySubgroup₀ ℝ := by
  have hr := sqrt_pos_of h
  have hr2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotGL_coe, det_rotM h], ?_, ?_⟩
  · rw [rotGL_coe, det_rotM h, norm_one]
  · intro x y
    simp only [rotGL_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    linear_combination (-(x ^ 2 + y ^ 2)) * hr2

theorem archWeightCharℝ_zero (r : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 r : ℂˣ) : ℂ) = 1 := by
  show ((((archWeightOneℝ r) ^ (0 : ℤ)) : ℂˣ) : ℂ) = 1
  rw [zpow_zero, Units.val_one]

theorem continuousOn_torus {P : RealArchParam} (D : ArchDatumR P) :
    ContinuousOn (fun τ : ℝ => D.W (diagOne τ)) {τ | τ ≠ 0} := by
  have hc : Continuous fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j : Fin 2 → Fin 2 → ℝ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hmaps : Set.MapsTo (fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j : Fin 2 → Fin 2 → ℝ))
      {τ | τ ≠ 0} glSet := by
    intro τ hτ
    show (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0
    rw [Matrix.det_fin_two]
    simpa using hτ
  have h := D.smooth.continuousOn.comp hc.continuousOn hmaps
  refine h.congr fun τ _ => ?_
  show D.W (diagOne τ) = D.W (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)
  rfl

theorem exists_torus_ne_zero {P : RealArchParam} (D : ArchDatumR P)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) :
    ∃ τ : ℝ, τ ≠ 0 ∧ D.W (diagOne τ) ≠ 0 := by
  obtain ⟨g, hg⟩ := hDnz
  set G : Matrix (Fin 2) (Fin 2) ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) with hG
  set c : ℝ := G 1 0 with hc
  set d : ℝ := G 1 1 with hd
  have hdet : G.det ≠ 0 := by
    rw [hG]; exact (Matrix.isUnits_det_units g).ne_zero
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    rw [Matrix.det_fin_two, ← hc, ← hd, h.1, h.2]; ring
  set r : ℝ := Real.sqrt (c ^ 2 + d ^ 2) with hr
  have hr0 : 0 < r := sqrt_pos_of hcd
  have hr2 : r ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)

  set α : ℝ := (G 0 0 * d - G 0 1 * c) / r with hα
  set β : ℝ := (G 0 0 * c + G 0 1 * d) / r with hβ
  set Xm : Matrix (Fin 2) (Fin 2) ℝ := !![α, β; 0, r] with hXm
  have hXrot : Xm * rotM c d = G := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, ← hr]
      field_simp
      linear_combination (-(G 0 0)) * hr2
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, ← hr]
      field_simp
      linear_combination (-(G 0 1)) * hr2
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, ← hr, ← hc]
      field_simp
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, ← hr, ← hd]
      field_simp
  have hαr : α * r ≠ 0 := by
    have h1 : Xm.det = α * r := by rw [hXm, Matrix.det_fin_two_of]; ring
    have h2 : Xm.det * (rotM c d).det = G.det := by rw [← Matrix.det_mul, hXrot]
    rw [det_rotM hcd, mul_one, h1] at h2
    rw [h2]; exact hdet
  have hα0 : α ≠ 0 := fun h => hαr (by rw [h, zero_mul])
  set Xg : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero Xm
    (by rw [hXm, Matrix.det_fin_two_of]; simpa using hαr) with hXg
  have hXg_coe : ((Xg : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Xm := rfl

  have h1 : D.W G = D.W Xm := by
    have h := hDW ⟨rotGL hcd, rotGL_mem hcd⟩ Xg
    rw [archWeightCharℝ_zero, one_mul, hXg_coe] at h
    rw [← h]
    congr 1
    rw [Units.val_mul, hXg_coe]
    exact hXrot.symm

  have hXm_eq : Xm = r • (unip (β / r) * diagOne (α / r)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hXm, unip, diagOne, Matrix.smul_apply] <;>
      field_simp
  have h2 : D.W Xm = centralChar P r * ((|r| : ℝ) : ℂ) * (psi (β / r) * D.W (diagOne (α / r))) := by
    rw [hXm_eq, D.central_law r _ hr0.ne', D.unip_law]
  refine ⟨α / r, div_ne_zero hα0 hr0.ne', fun h0 => hg ?_⟩
  show D.W G = 0
  rw [h1, h2, h0, mul_zero, mul_zero]

end Ws23TMNZ

namespace Ws23TMNZ

open LanglandsTunnell.Converse.ArchR Set

theorem archFactor_twist_ne_zero (u₁ u₂ : ℂ) (c : ZMod 2) {s : ℂ} (hs : ‖u₁‖ + ‖u₂‖ + 1 < s.re) :
    ((RealArchParam.principal u₁ c u₂ c).twist 0 c).archFactor s ≠ 0 := by
  have hcc : c + c = 0 := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h | h <;> subst h <;> decide
  simp only [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC, hcc, signShift_zero,
    add_zero, Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  have h1 : 0 < (s + u₁).re := by
    rw [Complex.add_re]; have := Complex.abs_re_le_norm u₁; have := neg_abs_le u₁.re; linarith [norm_nonneg u₂]
  have h2 : 0 < (s + u₂).re := by
    rw [Complex.add_re]; have := Complex.abs_re_le_norm u₂; have := neg_abs_le u₂.re; linarith [norm_nonneg u₁]
  exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h1) (Complex.Gammaℝ_ne_zero_of_re_pos h2)

theorem quasiChar_zero_neg {c : ZMod 2} {t : ℝ} (ht : 0 < t) :
    quasiChar 0 c (-t) = (-1 : ℂ) ^ c.val := by
  unfold quasiChar
  rw [Complex.cpow_zero, one_mul]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h | h <;> subst h
  · simp
  · rw [if_neg (by decide)]
    have hs : SignType.sign (-t) = -1 := by rw [Left.sign_neg, sign_pos ht]
    rw [hs]
    simp [show (1 : ZMod 2).val = 1 from rfl]

theorem quasiChar_zero_pos {c : ZMod 2} {t : ℝ} (ht : 0 < t) : quasiChar 0 c t = 1 := by
  unfold quasiChar
  rw [Complex.cpow_zero, one_mul]
  split_ifs
  · rfl
  · rw [sign_pos ht]; simp

theorem neg_one_pow_mul_self (c : ZMod 2) : (-1 : ℂ) ^ c.val * (-1 : ℂ) ^ c.val = 1 := by
  rw [← mul_pow, neg_mul_neg, one_mul, one_pow]

end Ws23TMNZ

open Ws23TMNZ LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR Set in
theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) (x₀ : ℝ) :
    ∃ x : ℝ, x₀ < x ∧ MellinConvergent (fun τ : ℝ => D.W (ArchR.diagOne τ)) (x : ℂ) ∧
      mellin (fun τ : ℝ => D.W (ArchR.diagOne τ)) (x : ℂ) ≠ 0 := by
  set f : ℝ → ℂ := fun τ => D.W (diagOne τ) with hf

  have hDW' : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ) := fun r x => by
    rw [hDW0, archWeightCharℝ_zero, one_mul]
  obtain ⟨τ₀, hτ₀, hne⟩ := exists_torus_ne_zero D hDW' hDnz
  have hcont := continuousOn_torus D

  set A : ℝ := D.zeta_abscissa with hA
  have hkey : ∀ s : ℂ, A < s.re →
      MellinConvergent f (s - 1) ∧
        2 * mellin f (s - 1) = (P₂.twist 0 c).archFactor s * D.zetaEntire 1 0 c s := by
    intro s hs
    have hdet : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by simp
    have hs' : D.zeta_abscissa < s.re + (0 : ℂ).re := by simpa using hs
    have hint := D.zeta_integrable 1 0 c s hdet hs'
    have heq := D.zeta_eq 1 0 c s hdet hs'

    have hpos : ∀ t ∈ Ioi (0 : ℝ), zetaIntegrand D.W 1 0 c s t = (t : ℂ) ^ (s - 1 - 1) • f t := by
      intro t ht
      have ht : 0 < t := ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
      simp only [zetaIntegrand, Matrix.mul_one, quasiChar_zero_pos ht, abs_of_pos ht, smul_eq_mul, hf]
      rw [show s - 1 - 1 = (s - 1) + (-1 : ℂ) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_neg_one]
      ring
    have hneg : ∀ t ∈ Ioi (0 : ℝ), zetaIntegrand D.W 1 0 c s (-t) = zetaIntegrand D.W 1 0 c s t := by
      intro t ht
      have ht : 0 < t := ht
      simp only [zetaIntegrand, Matrix.mul_one, quasiChar_zero_pos ht, quasiChar_zero_neg ht, abs_neg, hpar t ht.ne']
      linear_combination (D.W (diagOne t) * (((|t| : ℝ) : ℂ) ^ (s - 1)) * (((|t| : ℝ) : ℂ))⁻¹) * neg_one_pow_mul_self c
    have hI : IntegrableOn (zetaIntegrand D.W 1 0 c s) (Ioi 0) := hint.integrableOn
    have hconv : MellinConvergent f (s - 1) := (hI.congr_fun hpos measurableSet_Ioi)
    refine ⟨hconv, ?_⟩
    have hsplit := intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hI
    have hIic : ∫ t in Iic (0 : ℝ), zetaIntegrand D.W 1 0 c s t = ∫ t in Ioi (0 : ℝ), zetaIntegrand D.W 1 0 c s t := by
      rw [← neg_zero, ← integral_comp_neg_Ioi 0 (zetaIntegrand D.W 1 0 c s), neg_zero]
      exact setIntegral_congr_fun measurableSet_Ioi hneg
    have hmel : ∫ t in Ioi (0 : ℝ), zetaIntegrand D.W 1 0 c s t = mellin f (s - 1) := by
      rw [mellin]; exact setIntegral_congr_fun measurableSet_Ioi hpos
    rw [← heq, ← hsplit, hIic, hmel]
    ring

  by_contra hcon
  push Not at hcon
  set B : ℝ := max (max x₀ (A - 1)) (‖u₁‖ + ‖u₂‖ + 1) + 1 with hB
  have hBx : x₀ + 1 ≤ B := by have := le_max_left (max x₀ (A - 1)) (‖u₁‖ + ‖u₂‖ + 1); have := le_max_left x₀ (A - 1); linarith
  have hBA : A ≤ B := by have := le_max_left (max x₀ (A - 1)) (‖u₁‖ + ‖u₂‖ + 1); have := le_max_right x₀ (A - 1); linarith
  have hBu : ‖u₁‖ + ‖u₂‖ + 1 < B := by have := le_max_right (max x₀ (A - 1)) (‖u₁‖ + ‖u₂‖ + 1); linarith

  have hzero : ∀ x : ℝ, B < x → D.zetaEntire 1 0 c (x : ℂ) = 0 := by
    intro x hx
    have hxA : A < ((x : ℂ)).re := by simp; linarith
    obtain ⟨hconv, hk⟩ := hkey x hxA
    have hm : mellin f ((x : ℂ) - 1) = 0 := by
      have h := hcon (x - 1) (by linarith)
      have : ((x - 1 : ℝ) : ℂ) = (x : ℂ) - 1 := by push_cast; ring
      rw [this] at h
      exact h hconv
    rw [hm, mul_zero] at hk
    have hAF : (P₂.twist 0 c).archFactor (x : ℂ) ≠ 0 := by
      rw [hP]; exact archFactor_twist_ne_zero u₁ u₂ c (by simp; linarith)
    exact (mul_eq_zero.1 hk.symm).resolve_left hAF

  have hent : AnalyticOnNhd ℂ (D.zetaEntire 1 0 c) univ :=
    (D.zetaEntire_differentiable 1 0 c).differentiableOn.analyticOnNhd isOpen_univ
  have hall : ∀ z : ℂ, D.zetaEntire 1 0 c z = 0 := by
    have z₀mem : ((B + 1 : ℝ) : ℂ) ∈ (univ : Set ℂ) := mem_univ _
    rcases (hent _ z₀mem).eventually_eq_zero_or_eventually_ne_zero with h | h
    · intro z
      exact hent.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ z₀mem h (mem_univ z)
    · exfalso
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
      obtain ⟨ε, hε, hball⟩ := h
      have hpt : dist (((B + 1 + ε / 2 : ℝ)) : ℂ) ((B + 1 : ℝ) : ℂ) < ε := by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [show B + 1 + ε / 2 - (B + 1) = ε / 2 by ring, abs_of_pos (by linarith)]
        linarith
      have hne' : ((B + 1 + ε / 2 : ℝ) : ℂ) ≠ ((B + 1 : ℝ) : ℂ) := by
        intro h; have := Complex.ofReal_injective h; linarith
      exact hball hpt hne' (hzero _ (by linarith))

  have hmel0 : ∀ w : ℂ, A - 1 < w.re → mellin f w = 0 := by
    intro w hw
    obtain ⟨-, hk⟩ := hkey (w + 1) (by simp; linarith)
    rw [hall, mul_zero, show w + 1 - 1 = w by ring] at hk
    exact (mul_eq_zero.1 hk).resolve_left two_ne_zero

  have hfzero : ∀ x : ℝ, 0 < x → f x = 0 := by
    intro x hx
    have hconvB : MellinConvergent f (B : ℂ) := by
      have := (hkey ((B : ℂ) + 1) (by simp; linarith)).1
      rwa [show (B : ℂ) + 1 - 1 = (B : ℂ) by ring] at this
    have hline : ∀ y : ℝ, mellin f ((B : ℂ) + (y : ℂ) * Complex.I) = 0 := fun y =>
      hmel0 _ (by simp; linarith)
    have hvert : Complex.VerticalIntegrable (mellin f) B := by
      have : (fun y : ℝ => mellin f ((B : ℂ) + (y : ℂ) * Complex.I)) = 0 := funext hline
      rw [Complex.VerticalIntegrable, this]; exact integrable_zero _ _ _
    have hcx : ContinuousAt f x := (hcont x hx.ne').continuousAt (isOpen_ne.mem_nhds hx.ne')
    have hinv := mellinInv_mellin_eq B f hx hconvB hvert hcx
    rw [← hinv, mellinInv]
    simp only [hline, smul_zero, integral_zero]

  rcases lt_or_gt_of_ne hτ₀ with hlt | hgt
  · apply hne
    have h := hpar (-τ₀) (neg_ne_zero.2 hτ₀)
    rw [neg_neg] at h
    have h0 := hfzero (-τ₀) (by linarith)
    simp only [hf] at h0
    rw [h, h0, mul_zero]
  · exact hne (hfzero τ₀ hgt)

#print axioms solution

end S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_mellin_W_diagOne_ne_zero_of_weightZero_of_parity
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_mellin_W_diagOne_ne_zero_of_weightZero_of_parity (solution)

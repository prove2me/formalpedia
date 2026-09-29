-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6b427374-eac4-5a43-9111-280bdc22b05d

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Theorems.Thm_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

namespace Ws46
namespace G5DS

theorem bottom_row_unipotent_mul {n : GL (Fin 2) ℝ} (hn : n ∈ realUnipotent) (g : GL (Fin 2) ℝ) (j : Fin 2) :
    ((n * g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 j = (g : Matrix (Fin 2) (Fin 2) ℝ) 1 j := by
  obtain ⟨x, rfl⟩ := hn
  change (((unipotentGL2 (Multiplicative.toAdd x)) * g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 j = _
  rw [Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem bottom_row_sq_mul_rowIsometry (g : GL (Fin 2) ℝ) {κ : GL (Fin 2) ℝ} (hκ : κ ∈ rowIsometrySubgroup ℝ) :
    ((g * κ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + ((g * κ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 =
      (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 := by
  have h := hκ.2 ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1)
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  exact h

theorem upperUnit_val (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    ((upperUnit a b t ha ht : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, t] := rfl

theorem det_upperUnit (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (upperUnit a b t ha ht) : ℝˣ) : ℝ) = a * t := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnit_val, Matrix.det_fin_two_of]
  ring

theorem toReal_measure_unitInterval_pos
    (μN : @Measure ↥realUnipotent (@Subtype.instMeasurableSpace _ _ (borel (GL (Fin 2) ℝ)))) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ [μN.IsHaarMeasure],
    0 < (μN {n : ↥realUnipotent | ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  intro _

  let ι : ℝ → ↥realUnipotent := fun x => ⟨unipotentGL2Hom (Multiplicative.ofAdd x), ⟨Multiplicative.ofAdd x, rfl⟩⟩
  have hιc : Continuous ι := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun x : ℝ => ((unipotentGL2 (Multiplicative.toAdd (Multiplicative.ofAdd x)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      simp only [toAdd_ofAdd, unipotentGL2_coe]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    · show Continuous fun x : ℝ => (((unipotentGL2 (Multiplicative.toAdd (Multiplicative.ofAdd x)))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      have : ∀ x : ℝ, (((unipotentGL2 x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, -x; 0, 1] := fun x => rfl
      simp only [toAdd_ofAdd, this]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hentry : ∀ x : ℝ, (((ι x : ↥realUnipotent) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = x := by
    intro x
    show ((unipotentGL2 (Multiplicative.toAdd (Multiplicative.ofAdd x)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = x
    simp
  have hsurj : ∀ n : ↥realUnipotent, n = ι ((((n : ↥realUnipotent) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) := by
    rintro ⟨n, ⟨x, rfl⟩⟩
    apply Subtype.ext
    show unipotentGL2Hom x = unipotentGL2Hom (Multiplicative.ofAdd _)
    congr 1
  set I : Set ↥realUnipotent := {n : ↥realUnipotent | ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}

  have hIeq : I = ι '' Set.Icc 0 1 := by
    ext n
    constructor
    · intro hn
      exact ⟨_, hn, (hsurj n).symm⟩
    · rintro ⟨x, hx, rfl⟩
      show (((ι x : ↥realUnipotent) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1
      rw [hentry]; exact hx
  have hIcpt : IsCompact I := by rw [hIeq]; exact isCompact_Icc.image hιc
  have hfin : μN I < ⊤ := hIcpt.measure_lt_top

  have hcont : Continuous fun n : ↥realUnipotent => ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 :=
    (Units.continuous_val.matrix_elem 0 1).comp continuous_subtype_val
  have hU : IsOpen {n : ↥realUnipotent | ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Ioo (0 : ℝ) 1} :=
    isOpen_Ioo.preimage hcont
  have hUne : {n : ↥realUnipotent | ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Ioo (0 : ℝ) 1}.Nonempty :=
    ⟨ι (1 / 2), by show (((ι (1/2) : ↥realUnipotent) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Ioo (0:ℝ) 1; rw [hentry]; norm_num⟩
  have hpos : 0 < μN I :=
    lt_of_lt_of_le (hU.measure_pos μN hUne) (measure_mono fun n hn => ⟨hn.1.le, hn.2.le⟩)
  exact ENNReal.toReal_pos hpos.ne' hfin.ne

end Ws46.G5DS

open Ws46.G5DS in
theorem solution :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure)
      (μN : Measure realUnipotent) [μN.IsHaarMeasure],
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (k : ℕ) (_hk : 1 ≤ k) (C : ℂ) (W W' : GL (Fin 2) ℝ → ℂ)
        (_hW : Measurable W) (_hW' : Measurable W')
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * W' (n * g) = W g * W' g)
        (_hK : ∀ κ ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * κ) * W' (g * κ) = W g * W' g)
        (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
          W (upperUnit a₁ 0 a₂ h₁ h₂.ne') * W' (upperUnit a₁ 0 a₂ h₁ h₂.ne') =
            if 0 < a₁ then C * (((a₁ / a₂ : ℝ) : ℂ) ^ k * Complex.exp (-(4 * Real.pi * (a₁ / a₂) : ℝ))) else 0)
        (σ₀ : ℝ) (_hσ₀ : 0 ≤ σ₀)
        (_hint : ∀ s : ℂ, σ₀ < s.re → Integrable
          (fun g : GL (Fin 2) ℝ =>
            (W g * (W' g * Complex.exp (-(Real.pi *
                (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
              (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN))),
      ∀ s : ℂ, σ₀ < s.re →
        rsArchIntegral RSCarrier.archMeasure μN (s + 1 / 2) W
            (fun g : GL (Fin 2) ℝ => W' g * Complex.exp (-(Real.pi *
                (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) =
          (C' : ℂ) * C * ((4 * (Real.pi : ℂ)) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
            ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  intro _hHaar μN _
  obtain ⟨c, hc, hIw⟩ := LanglandsTunnell.Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal _hHaar
  have hIpos := toReal_measure_unitInterval_pos μN
  refine ⟨c / (μN {n : ↥realUnipotent |
      ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal / 2, by positivity, ?_⟩
  intro k hk C W W' hW hW' hN hK hT σ₀ hσ₀ hint s hs
  have hs0 : 0 < s.re := lt_of_le_of_lt hσ₀ hs
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk : 0 < (s + (k : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]; linarith

  have hGc : Continuous fun g : GL (Fin 2) ℝ => Complex.exp (-(Real.pi *
      (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)) := by
    have h1 : Continuous fun g : GL (Fin 2) ℝ => (Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2)) :=
      (continuous_const.mul (((Units.continuous_val.matrix_elem 1 0).pow 2).add
        ((Units.continuous_val.matrix_elem 1 1).pow 2)))
    exact ((Complex.continuous_ofReal.comp h1).neg).cexp
  have hF : Measurable fun g : GL (Fin 2) ℝ => W' g * Complex.exp (-(Real.pi *
      (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)) :=
    hW'.mul hGc.measurable
  have hNF : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ,
      W (n * g) * (W' (n * g) * Complex.exp (-(Real.pi *
        ((((n * g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 +
          (((n * g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) =
      W g * (W' g * Complex.exp (-(Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) := by
    intro n hn g
    rw [bottom_row_unipotent_mul hn g 0, bottom_row_unipotent_mul hn g 1, ← mul_assoc, ← mul_assoc, hN n hn g]
  have hKF : ∀ κ ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ = 1 → ∀ g : GL (Fin 2) ℝ,
      W (g * κ) * (W' (g * κ) * Complex.exp (-(Real.pi *
        ((((g * κ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 +
          (((g * κ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) =
      W g * (W' g * Complex.exp (-(Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) := by
    intro κ hκ hdet g
    rw [bottom_row_sq_mul_rowIsometry g hκ, ← mul_assoc, ← mul_assoc, hK κ hκ hdet g]
  have key := hIw μN (s + 1 / 2) W _ hNF hKF hW hF (hint s hs)
  rw [key]

  have hpt : ∀ a₂ : ℝ, 0 < a₂ → ∀ a₁ : ℝ,
      (if h : a₁ ≠ 0 ∧ 0 < a₂ then
          let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
          ((W p * (W' p * Complex.exp (-(Real.pi *
              (((p : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((p : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
            (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))) *
            (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
        else 0) =
      (Set.Ioi (0 : ℝ)).indicator (fun a₁ : ℝ =>
        (C * Complex.exp (-(Real.pi * a₂ ^ 2 : ℝ)) * ((a₂ : ℂ) ^ s / (a₂ : ℂ) ^ k)) *
          ((a₁ : ℂ) ^ (s + (k : ℂ) - 1 - 1) * Complex.exp (-(((4 * Real.pi / a₂ : ℝ) : ℂ) * (a₁ : ℂ))))) a₁ := by
    intro a₂ ha₂ a₁
    rcases lt_trichotomy a₁ 0 with ha₁ | ha₁ | ha₁
    ·
      rw [dif_pos ⟨ha₁.ne, ha₂⟩, Set.indicator_of_notMem (fun h : a₁ ∈ Set.Ioi (0:ℝ) => lt_asymm ha₁ h)]
      dsimp only
      have hprof := hT a₁ a₂ ha₁.ne ha₂
      rw [if_neg (not_lt.mpr ha₁.le)] at hprof
      rw [← mul_assoc (W _), hprof, zero_mul, zero_mul, zero_mul]
    ·
      subst ha₁
      rw [dif_neg (fun h => h.1 rfl), Set.indicator_of_notMem (by simp : (0:ℝ) ∉ Set.Ioi 0)]
    ·
      rw [dif_pos ⟨ha₁.ne', ha₂⟩, Set.indicator_of_mem (Set.mem_Ioi.mpr ha₁)]
      dsimp only
      have hprof := hT a₁ a₂ ha₁.ne' ha₂
      rw [if_pos ha₁] at hprof
      rw [← mul_assoc (W _), hprof, det_upperUnit, upperUnit_val]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [abs_of_pos (mul_pos ha₁ ha₂), show s + 1 / 2 - 1 / 2 = s by ring]
      have ha₁' : (a₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha₁.ne'
      have ha₂' : (a₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha₂.ne'
      have e1 : (((a₁ * a₂ : ℝ)) : ℂ) ^ s = (a₁ : ℂ) ^ s * (a₂ : ℂ) ^ s := by
        push_cast; exact Complex.mul_cpow_ofReal_nonneg ha₁.le ha₂.le s
      have e2 : (((a₁ / a₂ : ℝ)) : ℂ) ^ k = (a₁ : ℂ) ^ (k : ℂ) / (a₂ : ℂ) ^ k := by
        push_cast; rw [div_pow, Complex.cpow_natCast]
      have e3 : (((a₁ ^ 2)⁻¹ : ℝ) : ℂ) = (a₁ : ℂ) ^ (-(2 : ℂ)) := by
        push_cast; rw [Complex.cpow_neg, ← Complex.cpow_natCast]; norm_num
      have e4 : (a₁ : ℂ) ^ (k : ℂ) * (a₁ : ℂ) ^ s * (a₁ : ℂ) ^ (-(2 : ℂ)) = (a₁ : ℂ) ^ (s + (k : ℂ) - 1 - 1) := by
        rw [← Complex.cpow_add _ _ ha₁', ← Complex.cpow_add _ _ ha₁']; congr 1; ring
      have e5 : Complex.exp (-((4 * Real.pi * (a₁ / a₂) : ℝ) : ℂ)) = Complex.exp (-(((4 * Real.pi / a₂ : ℝ) : ℂ) * (a₁ : ℂ))) := by
        congr 1; push_cast; ring
      have e6 : Complex.exp (-((Real.pi * ((0 : ℝ) ^ 2 + a₂ ^ 2) : ℝ) : ℂ)) = Complex.exp (-((Real.pi * a₂ ^ 2 : ℝ) : ℂ)) := by
        congr 1; push_cast; ring
      rw [e1, e2, e3, e5, e6]
      calc C * ((a₁ : ℂ) ^ (k : ℂ) / (a₂ : ℂ) ^ k * Complex.exp (-(((4 * Real.pi / a₂ : ℝ) : ℂ) * (a₁ : ℂ)))) *
              Complex.exp (-(Real.pi * a₂ ^ 2 : ℝ)) * ((a₁ : ℂ) ^ s * (a₂ : ℂ) ^ s) * (a₁ : ℂ) ^ (-(2 : ℂ))
          = (C * Complex.exp (-(Real.pi * a₂ ^ 2 : ℝ)) * ((a₂ : ℂ) ^ s / (a₂ : ℂ) ^ k)) *
              (((a₁ : ℂ) ^ (k : ℂ) * (a₁ : ℂ) ^ s * (a₁ : ℂ) ^ (-(2 : ℂ))) *
                Complex.exp (-(((4 * Real.pi / a₂ : ℝ) : ℂ) * (a₁ : ℂ)))) := by
            field_simp
        _ = _ := by rw [e4]

  have hinner : ∀ a₂ : ℝ, 0 < a₂ →
      (∫ a₁ : ℝ, (if h : a₁ ≠ 0 ∧ 0 < a₂ then
          let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
          ((W p * (W' p * Complex.exp (-(Real.pi *
              (((p : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((p : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
            (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))) *
            (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
        else 0)) =
      (C * Complex.exp (-(Real.pi * a₂ ^ 2 : ℝ)) * ((a₂ : ℂ) ^ s / (a₂ : ℂ) ^ k)) *
        ((1 / ((4 * Real.pi / a₂ : ℝ) : ℂ)) ^ (s + (k : ℂ) - 1) * Complex.Gamma (s + (k : ℂ) - 1)) := by
    intro a₂ ha₂
    rw [show (fun a₁ : ℝ => (if h : a₁ ≠ 0 ∧ 0 < a₂ then
          let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
          ((W p * (W' p * Complex.exp (-(Real.pi *
              (((p : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((p : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
            (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))) *
            (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
        else 0)) = (Set.Ioi (0 : ℝ)).indicator (fun a₁ : ℝ =>
        (C * Complex.exp (-(Real.pi * a₂ ^ 2 : ℝ)) * ((a₂ : ℂ) ^ s / (a₂ : ℂ) ^ k)) *
          ((a₁ : ℂ) ^ (s + (k : ℂ) - 1 - 1) * Complex.exp (-(((4 * Real.pi / a₂ : ℝ) : ℂ) * (a₁ : ℂ)))))
        from funext (hpt a₂ ha₂)]
    rw [MeasureTheory.integral_indicator measurableSet_Ioi, MeasureTheory.integral_const_mul,
      Complex.integral_cpow_mul_exp_neg_mul_Ioi hsk (by positivity)]

  have hK : ∀ a₂ : ℝ, 0 < a₂ →
      (C * Complex.exp (-(Real.pi * a₂ ^ 2 : ℝ)) * ((a₂ : ℂ) ^ s / (a₂ : ℂ) ^ k)) *
        ((1 / ((4 * Real.pi / a₂ : ℝ) : ℂ)) ^ (s + (k : ℂ) - 1) * Complex.Gamma (s + (k : ℂ) - 1)) =
      (C * ((4 * (Real.pi : ℂ)) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1))) *
        ((a₂ : ℂ) ^ (2 * s - 1) * Complex.exp (-((Real.pi : ℂ) * ((a₂ ^ 2 : ℝ) : ℂ)))) := by
    intro a₂ ha₂
    have ha₂' : (a₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha₂.ne'
    have h4π : (0 : ℝ) < 4 * Real.pi := by positivity
    have f1 : (1 / ((4 * Real.pi / a₂ : ℝ) : ℂ)) ^ (s + (k : ℂ) - 1) =
        (a₂ : ℂ) ^ (s + (k : ℂ) - 1) * (4 * (Real.pi : ℂ)) ^ (-(s + (k : ℂ) - 1)) := by
      rw [show (1 / ((4 * Real.pi / a₂ : ℝ) : ℂ)) = ((a₂ : ℝ) : ℂ) * (((4 * Real.pi)⁻¹ : ℝ) : ℂ) by
        push_cast; field_simp]
      rw [Complex.mul_cpow_ofReal_nonneg ha₂.le (inv_nonneg.mpr h4π.le)]
      congr 1
      have harg : (4 * (Real.pi : ℂ)).arg ≠ Real.pi := by
        rw [show (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring,
          Complex.arg_ofReal_of_nonneg h4π.le]
        exact Real.pi_ne_zero.symm
      rw [show (((4 * Real.pi)⁻¹ : ℝ) : ℂ) = (4 * (Real.pi : ℂ))⁻¹ by simp, Complex.inv_cpow _ _ harg,
        Complex.cpow_neg]
    have f2 : (a₂ : ℂ) ^ s / (a₂ : ℂ) ^ k * (a₂ : ℂ) ^ (s + (k : ℂ) - 1) = (a₂ : ℂ) ^ (2 * s - 1) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_sub _ _ ha₂', ← Complex.cpow_add _ _ ha₂']
      congr 1; ring
    have f3 : Complex.exp (-(Real.pi * a₂ ^ 2 : ℝ)) = Complex.exp (-((Real.pi : ℂ) * ((a₂ ^ 2 : ℝ) : ℂ))) := by
      congr 1; push_cast; ring
    rw [f1, f3]
    calc C * Complex.exp (-((Real.pi : ℂ) * ((a₂ ^ 2 : ℝ) : ℂ))) * ((a₂ : ℂ) ^ s / (a₂ : ℂ) ^ k) *
          ((a₂ : ℂ) ^ (s + (k : ℂ) - 1) * (4 * (Real.pi : ℂ)) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1))
        = (C * ((4 * (Real.pi : ℂ)) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1))) *
          (((a₂ : ℂ) ^ s / (a₂ : ℂ) ^ k * (a₂ : ℂ) ^ (s + (k : ℂ) - 1)) *
            Complex.exp (-((Real.pi : ℂ) * ((a₂ ^ 2 : ℝ) : ℂ)))) := by ring
      _ = _ := by rw [f2]

  have hgauss : ∫ a₂ : ℝ in Set.Ioi 0, (a₂ : ℂ) ^ (2 * s - 1) * Complex.exp (-((Real.pi : ℂ) * ((a₂ ^ 2 : ℝ) : ℂ))) =
      (1 / 2 : ℂ) * ((1 / (Real.pi : ℂ)) ^ s * Complex.Gamma s) := by
    have hsub := MeasureTheory.integral_comp_rpow_Ioi
      (fun y : ℝ => (1 / 2 : ℂ) * ((y : ℂ) ^ (s - 1) * Complex.exp (-((Real.pi : ℂ) * (y : ℂ))))) (p := 2) two_ne_zero
    rw [MeasureTheory.integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hs0 Real.pi_pos] at hsub
    rw [← hsub]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    simp only [Complex.real_smul]
    have g1 : ((x ^ (2 : ℝ) : ℝ) : ℂ) ^ (s - 1) = (x : ℂ) ^ (2 * (s - 1)) := by
      rw [Complex.ofReal_cpow hx0.le, Complex.cpow_mul]
      · push_cast; ring_nf
      · rw [← Complex.ofReal_log hx0.le]; push_cast
        simp [Real.pi_pos]
      · rw [← Complex.ofReal_log hx0.le]; push_cast
        simp [Real.pi_pos.le]
    have g2 : ((|(2:ℝ)| * x ^ ((2:ℝ) - 1) : ℝ) : ℂ) = 2 * (x : ℂ) := by
      rw [abs_of_pos two_pos, show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]; push_cast; ring
    have g3 : (x : ℂ) * (x : ℂ) ^ (2 * (s - 1)) = (x : ℂ) ^ (2 * s - 1) := by
      rw [show (x : ℂ) ^ (2 * s - 1) = (x : ℂ) ^ ((1 : ℂ) + 2 * (s - 1)) by congr 1; ring,
        Complex.cpow_add _ _ hx', Complex.cpow_one]
    have g4 : ((x ^ (2:ℝ) : ℝ) : ℂ) = ((x ^ 2 : ℝ) : ℂ) := by
      rw [Real.rpow_two]
    rw [g2, g1, g4]
    symm
    calc (2 : ℂ) * (x : ℂ) * ((1 / 2 : ℂ) * ((x : ℂ) ^ (2 * (s - 1)) * Complex.exp (-((Real.pi : ℂ) * ((x ^ 2 : ℝ) : ℂ)))))
        = ((x : ℂ) * (x : ℂ) ^ (2 * (s - 1))) * Complex.exp (-((Real.pi : ℂ) * ((x ^ 2 : ℝ) : ℂ))) := by ring
      _ = (x : ℂ) ^ (2 * s - 1) * Complex.exp (-((Real.pi : ℂ) * ((x ^ 2 : ℝ) : ℂ))) := by rw [g3]

  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun a₂ ha₂ => (hinner a₂ ha₂).trans (hK a₂ ha₂)),
    MeasureTheory.integral_const_mul, hgauss]
  have hπinv : (1 / (Real.pi : ℂ)) ^ s = (Real.pi : ℂ) ^ (-s) := by
    rw [Complex.cpow_neg, one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm)]
  rw [hπinv]
  push_cast
  ring

end S_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair (solution)

-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fd44887c-568c-56b1-abef-68c6a69eefe1

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23K4

open Set Filter MeasureTheory

theorem norm_integrand (β t : ℝ) (ht : 0 < t) (c : ℂ) :
    ‖((t : ℂ) ^ ((((β + 2 : ℝ) : ℂ)) - 1)) • (c / (t : ℂ))‖ = ‖c‖ * t ^ β := by
  rw [norm_smul, show (((β + 2 : ℝ) : ℂ) - 1) = (((β + 1 : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.ofReal_re, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht, Real.rpow_add ht, Real.rpow_one]
  field_simp

theorem lintegral_lt_top_of_mellinConvergent (c : ℝ → ℂ) (β : ℝ)
    (h : MellinConvergent (fun t : ℝ => c t / (t : ℂ)) ((β + 2 : ℝ) : ℂ)) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖c y‖ * y ^ β) < ⊤ := by
  have hfi := h.hasFiniteIntegral
  rw [HasFiniteIntegral] at hfi
  refine lt_of_le_of_lt (le_of_eq ?_) hfi
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [← ofReal_norm, norm_integrand β t ht (c t)]

theorem aemeasurable_of_mellinConvergent (c : ℝ → ℂ) (s : ℂ)
    (h : MellinConvergent (fun t : ℝ => c t / (t : ℂ)) s) :
    AEMeasurable c (volume.restrict (Ioi (0 : ℝ))) := by
  have hG : AEMeasurable (fun t : ℝ => ((t : ℂ) ^ (s - 1)) • (c t / (t : ℂ)))
      (volume.restrict (Ioi (0 : ℝ))) := h.aestronglyMeasurable.aemeasurable
  have hpow : Measurable fun t : ℝ => ((t : ℂ) ^ (s - 1)) :=
    (Complex.measurable_ofReal.pow_const _)
  have hF : AEMeasurable (fun t : ℝ => (t : ℂ) * (((t : ℂ) ^ (s - 1))⁻¹ * (((t : ℂ) ^ (s - 1)) • (c t / (t : ℂ)))))
      (volume.restrict (Ioi (0 : ℝ))) :=
    Complex.measurable_ofReal.aemeasurable.mul (hpow.inv.aemeasurable.mul hG)
  refine hF.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
  have hp0 : (t : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl ht0
  rw [smul_eq_mul, ← mul_assoc ((t : ℂ) ^ (s - 1))⁻¹, inv_mul_cancel₀ hp0, one_mul, mul_div_cancel₀ _ ht0]

theorem lintegral_bound (W : ℝ → ℂ) (c₀ c₁ : ℝ → ℂ) (s₁ C : ℝ) (hC : 0 ≤ C)
    (h₀ : ∀ s : ℂ, s₁ < s.re → MellinConvergent (fun t : ℝ => c₀ t / (t : ℂ)) s)
    (h₁ : ∀ s : ℂ, s₁ < s.re → MellinConvergent (fun t : ℝ => c₁ t / (t : ℂ)) s)
    (hbd : ∀ y : ℝ, 0 < y → ‖W y‖ + ‖W (-y)‖ ≤ C * (‖c₀ y‖ + ‖c₁ y‖)) :
    ∀ β : ℝ, s₁ < β →
      ∫⁻ y in Ioi (0 : ℝ), (‖W y‖ₑ + ‖W (-y)‖ₑ) * ENNReal.ofReal (y ^ β) < ⊤ := by
  intro β hβ
  have hs : s₁ < (((β + 2 : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; linarith
  have I₀ := lintegral_lt_top_of_mellinConvergent c₀ β (h₀ _ hs)
  have I₁ := lintegral_lt_top_of_mellinConvergent c₁ β (h₁ _ hs)
  have A₀ : AEMeasurable (fun y : ℝ => ENNReal.ofReal (‖c₀ y‖ * y ^ β)) (volume.restrict (Ioi (0 : ℝ))) :=
    ((aemeasurable_of_mellinConvergent c₀ _ (h₀ _ hs)).norm.mul (measurable_id.pow_const β).aemeasurable).ennreal_ofReal
  have hle : ∀ y ∈ Ioi (0 : ℝ), (‖W y‖ₑ + ‖W (-y)‖ₑ) * ENNReal.ofReal (y ^ β) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (‖c₀ y‖ * y ^ β) + ENNReal.ofReal (‖c₁ y‖ * y ^ β)) := by
    intro y hy
    have hyβ : 0 ≤ y ^ β := Real.rpow_nonneg (le_of_lt hy) β
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ← ENNReal.ofReal_mul (add_nonneg (norm_nonneg _) (norm_nonneg _)),
      ← ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) hyβ) (mul_nonneg (norm_nonneg _) hyβ),
      ← ENNReal.ofReal_mul hC]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hbd y hy, hyβ, norm_nonneg (c₀ y), norm_nonneg (c₁ y)]
  calc ∫⁻ y in Ioi (0 : ℝ), (‖W y‖ₑ + ‖W (-y)‖ₑ) * ENNReal.ofReal (y ^ β)
      ≤ ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal C * (ENNReal.ofReal (‖c₀ y‖ * y ^ β) + ENNReal.ofReal (‖c₁ y‖ * y ^ β)) :=
        setLIntegral_mono' measurableSet_Ioi hle
    _ = ENNReal.ofReal C * ((∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖c₀ y‖ * y ^ β)) +
          ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖c₁ y‖ * y ^ β)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' A₀]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨I₀, I₁⟩)

theorem of_two_combinations (W : ℝ → ℂ) (k₀ k₁ : ℂ) (hk : k₀ ≠ k₁) (s₁ : ℝ)
    (h₀ : ∀ s : ℂ, s₁ < s.re → MellinConvergent (fun t : ℝ => (W t + k₀ * W (-t)) / (t : ℂ)) s)
    (h₁ : ∀ s : ℂ, s₁ < s.re → MellinConvergent (fun t : ℝ => (W t + k₁ * W (-t)) / (t : ℂ)) s) :
    (∀ β : ℝ, s₁ < β → ∫⁻ y in Ioi (0 : ℝ), (‖W y‖ₑ + ‖W (-y)‖ₑ) * ENNReal.ofReal (y ^ β) < ⊤) ∧
      AEMeasurable W (volume.restrict (Ioi (0 : ℝ))) ∧
      AEMeasurable (fun y : ℝ => W (-y)) (volume.restrict (Ioi (0 : ℝ))) := by
  have hd : k₀ - k₁ ≠ 0 := sub_ne_zero.2 hk

  have eV : ∀ y : ℝ, W (-y) = (k₀ - k₁)⁻¹ * ((W y + k₀ * W (-y)) - (W y + k₁ * W (-y))) := by
    intro y; field_simp; ring
  have eW : ∀ y : ℝ, W y = (k₀ - k₁)⁻¹ * (k₀ * (W y + k₁ * W (-y)) - k₁ * (W y + k₀ * W (-y))) := by
    intro y; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · refine lintegral_bound W (fun t => W t + k₀ * W (-t)) (fun t => W t + k₁ * W (-t)) s₁
      (‖(k₀ - k₁)⁻¹‖ * (1 + ‖k₀‖ + ‖k₁‖)) (by positivity) h₀ h₁ ?_
    intro y hy
    have n1 : ‖W y‖ ≤ ‖(k₀ - k₁)⁻¹‖ * (‖k₀‖ * ‖W y + k₁ * W (-y)‖ + ‖k₁‖ * ‖W y + k₀ * W (-y)‖) := by
      calc ‖W y‖ = ‖(k₀ - k₁)⁻¹ * (k₀ * (W y + k₁ * W (-y)) - k₁ * (W y + k₀ * W (-y)))‖ := congrArg _ (eW y)
        _ ≤ ‖(k₀ - k₁)⁻¹‖ * (‖k₀‖ * ‖W y + k₁ * W (-y)‖ + ‖k₁‖ * ‖W y + k₀ * W (-y)‖) := by
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          calc ‖k₀ * (W y + k₁ * W (-y)) - k₁ * (W y + k₀ * W (-y))‖
              ≤ ‖k₀ * (W y + k₁ * W (-y))‖ + ‖k₁ * (W y + k₀ * W (-y))‖ := norm_sub_le _ _
            _ = ‖k₀‖ * ‖W y + k₁ * W (-y)‖ + ‖k₁‖ * ‖W y + k₀ * W (-y)‖ := by rw [norm_mul, norm_mul]
    have n2 : ‖W (-y)‖ ≤ ‖(k₀ - k₁)⁻¹‖ * (‖W y + k₀ * W (-y)‖ + ‖W y + k₁ * W (-y)‖) := by
      calc ‖W (-y)‖ = ‖(k₀ - k₁)⁻¹ * ((W y + k₀ * W (-y)) - (W y + k₁ * W (-y)))‖ := congrArg _ (eV y)
        _ ≤ ‖(k₀ - k₁)⁻¹‖ * (‖W y + k₀ * W (-y)‖ + ‖W y + k₁ * W (-y)‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    have := norm_nonneg ((k₀ - k₁)⁻¹)
    nlinarith [n1, n2, norm_nonneg k₀, norm_nonneg k₁, norm_nonneg (W y + k₀ * W (-y)), norm_nonneg (W y + k₁ * W (-y)),
      mul_nonneg this (norm_nonneg (W y + k₀ * W (-y))), mul_nonneg this (norm_nonneg (W y + k₁ * W (-y))),
      mul_nonneg (mul_nonneg this (norm_nonneg k₀)) (norm_nonneg (W y + k₀ * W (-y))),
      mul_nonneg (mul_nonneg this (norm_nonneg k₁)) (norm_nonneg (W y + k₁ * W (-y))),
      mul_nonneg (mul_nonneg this (norm_nonneg k₀)) (norm_nonneg (W y + k₁ * W (-y))),
      mul_nonneg (mul_nonneg this (norm_nonneg k₁)) (norm_nonneg (W y + k₀ * W (-y)))]
  · have hA := aemeasurable_of_mellinConvergent _ _ (h₀ ((s₁ + 1 : ℝ) : ℂ) (by simp))
    have hB := aemeasurable_of_mellinConvergent _ _ (h₁ ((s₁ + 1 : ℝ) : ℂ) (by simp))
    have : W = fun y => (k₀ - k₁)⁻¹ * (k₀ * (W y + k₁ * W (-y)) - k₁ * (W y + k₀ * W (-y))) := funext eW
    rw [this]
    exact ((hB.const_mul k₀).sub (hA.const_mul k₁)).const_mul _
  · have hA := aemeasurable_of_mellinConvergent _ _ (h₀ ((s₁ + 1 : ℝ) : ℂ) (by simp))
    have hB := aemeasurable_of_mellinConvergent _ _ (h₁ ((s₁ + 1 : ℝ) : ℂ) (by simp))
    have : (fun y : ℝ => W (-y)) = fun y => (k₀ - k₁)⁻¹ * ((W y + k₀ * W (-y)) - (W y + k₁ * W (-y))) := funext eV
    rw [this]
    exact (hA.sub hB).const_mul _

theorem of_reflection (W : ℝ → ℂ) (k₀ k : ℂ) (hk : 1 + k₀ * k ≠ 0) (s₁ : ℝ)
    (hrefl : ∀ t : ℝ, W (-t) = k * W t)
    (h₀ : ∀ s : ℂ, s₁ < s.re → MellinConvergent (fun t : ℝ => (W t + k₀ * W (-t)) / (t : ℂ)) s) :
    (∀ β : ℝ, s₁ < β → ∫⁻ y in Ioi (0 : ℝ), (‖W y‖ₑ + ‖W (-y)‖ₑ) * ENNReal.ofReal (y ^ β) < ⊤) ∧
      AEMeasurable W (volume.restrict (Ioi (0 : ℝ))) ∧
      AEMeasurable (fun y : ℝ => W (-y)) (volume.restrict (Ioi (0 : ℝ))) := by
  have eW : ∀ y : ℝ, W y = (1 + k₀ * k)⁻¹ * (W y + k₀ * W (-y)) := by
    intro y
    rw [hrefl y, show W y + k₀ * (k * W y) = (1 + k₀ * k) * W y by ring, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · refine lintegral_bound W (fun t => W t + k₀ * W (-t)) (fun t => W t + k₀ * W (-t)) s₁
      (‖(1 + k₀ * k)⁻¹‖ * (1 + ‖k‖)) (by positivity) h₀ h₀ ?_
    intro y hy
    have n1 : ‖W y‖ = ‖(1 + k₀ * k)⁻¹‖ * ‖W y + k₀ * W (-y)‖ := by
      calc ‖W y‖ = ‖(1 + k₀ * k)⁻¹ * (W y + k₀ * W (-y))‖ := congrArg _ (eW y)
        _ = _ := norm_mul _ _
    have n2 : ‖W (-y)‖ = ‖k‖ * ‖W y‖ := by rw [hrefl, norm_mul]
    nlinarith [n1, n2, norm_nonneg k, norm_nonneg (W y + k₀ * W (-y)), norm_nonneg ((1 + k₀ * k)⁻¹),
      mul_nonneg (norm_nonneg ((1 + k₀ * k)⁻¹)) (norm_nonneg (W y + k₀ * W (-y))),
      mul_nonneg (norm_nonneg k) (mul_nonneg (norm_nonneg ((1 + k₀ * k)⁻¹)) (norm_nonneg (W y + k₀ * W (-y))))]
  · have hA := aemeasurable_of_mellinConvergent _ _ (h₀ ((s₁ + 1 : ℝ) : ℂ) (by simp))
    have : W = fun y => (1 + k₀ * k)⁻¹ * (W y + k₀ * W (-y)) := funext eW
    rw [this]; exact hA.const_mul _
  · have hA := aemeasurable_of_mellinConvergent _ _ (h₀ ((s₁ + 1 : ℝ) : ℂ) (by simp))
    have : (fun y : ℝ => W (-y)) = fun y => k * ((1 + k₀ * k)⁻¹ * (W y + k₀ * W (-y))) := by
      funext y
      calc W (-y) = k * W y := hrefl y
        _ = k * ((1 + k₀ * k)⁻¹ * (W y + k₀ * W (-y))) := by rw [← eW y]
    rw [this]; exact (hA.const_mul _).const_mul _

theorem of_support (W : ℝ → ℂ) (k₀ : ℂ) (s₁ : ℝ)
    (hzero : ∀ y : ℝ, 0 < y → W (-y) = 0)
    (h₀ : ∀ s : ℂ, s₁ < s.re → MellinConvergent (fun t : ℝ => (W t + k₀ * W (-t)) / (t : ℂ)) s) :
    (∀ β : ℝ, s₁ < β → ∫⁻ y in Ioi (0 : ℝ), (‖W y‖ₑ + ‖W (-y)‖ₑ) * ENNReal.ofReal (y ^ β) < ⊤) ∧
      AEMeasurable W (volume.restrict (Ioi (0 : ℝ))) ∧
      AEMeasurable (fun y : ℝ => W (-y)) (volume.restrict (Ioi (0 : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · refine lintegral_bound W (fun t => W t + k₀ * W (-t)) (fun t => W t + k₀ * W (-t)) s₁ 1 zero_le_one h₀ h₀ ?_
    intro y hy
    simp only [hzero y hy, mul_zero, add_zero, norm_zero, one_mul]
    linarith [norm_nonneg (W y)]
  · have hA := aemeasurable_of_mellinConvergent _ _ (h₀ ((s₁ + 1 : ℝ) : ℂ) (by simp))
    refine hA.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hzero t ht, mul_zero, add_zero]
  · refine (aemeasurable_const (b := (0 : ℂ))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hzero t ht).symm

theorem zmod2_eq_add_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a = b + 1 := by
  revert h; revert a b; decide

theorem zmod2_add_eq_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a + b = 1 := by
  revert h; revert a b; decide

theorem neg_one_pow_val_ne {a b : ZMod 2} (h : a ≠ b) : (-1 : ℂ) ^ a.val ≠ (-1 : ℂ) ^ b.val := by
  have ha : a = 0 ∨ a = 1 := by clear h; revert a; decide
  have hb : b = 0 ∨ b = 1 := by clear h ha; revert b; decide
  have v0 : ZMod.val (0 : ZMod 2) = 0 := rfl
  have v1 : ZMod.val (1 : ZMod 2) = 1 := rfl
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl h
  · rw [v0, v1]; norm_num
  · rw [v0, v1]; norm_num
  · exact absurd rfl h

theorem one_add_neg_one_pow_val_mul_self (a : ZMod 2) : 1 + (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ a.val ≠ 0 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

end Ws23K4

theorem solution
    (P : RealArchParam)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (par : ZMod 2) :
    ∃ s₁ : ℝ, (∀ β : ℝ, s₁ < β →
        ∫⁻ y in Set.Ioi (0 : ℝ), (‖Wr par default y‖ₑ + ‖Wr par default (-y)‖ₑ) * ENNReal.ofReal (y ^ β) < ⊤) ∧
      AEMeasurable (fun y : ℝ => Wr par default y) (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      AEMeasurable (fun y : ℝ => Wr par default (-y)) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  classical
  have hR : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _

  set W : ℝ → ℂ := fun y => Wr par default y with hWdef

  have conv : ∀ (c : ℂ) (s : ℂ),
      MellinConvergent (fun t : ℝ => (Wr par default t + c * Wr par default (-(t : ℂ))) / (t : ℂ)) s →
        MellinConvergent (fun t : ℝ => (W t + c * W (-t)) / (t : ℂ)) s := by
    intro c s h
    have : (fun t : ℝ => (W t + c * W (-t)) / (t : ℂ)) =
        fun t : ℝ => (Wr par default t + c * Wr par default (-(t : ℂ))) / (t : ℂ) := by
      funext t; simp only [hWdef, Complex.ofReal_neg]
    rw [this]; exact h

  obtain ⟨s₀, H₀⟩ := hWr4 par default hR par (Or.inl rfl)
  have M₀ : ∀ s : ℂ, s₀ < s.re → MellinConvergent (fun t : ℝ => (W t + (-1 : ℂ) ^ par.val * W (-t)) / (t : ℂ)) s :=
    fun s hs => conv _ _ (H₀ s hs).1

  suffices h : ∃ s₁ : ℝ, (∀ β : ℝ, s₁ < β →
        ∫⁻ y in Set.Ioi (0 : ℝ), (‖W y‖ₑ + ‖W (-y)‖ₑ) * ENNReal.ofReal (y ^ β) < ⊤) ∧
      AEMeasurable W (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      AEMeasurable (fun y : ℝ => W (-y)) (volume.restrict (Set.Ioi (0 : ℝ))) by
    simpa only [hWdef, Complex.ofReal_neg] using h
  rcases P with ⟨u₁, a₁, u₂, a₂⟩ | ⟨u₀, n, hn⟩
  · by_cases ha : a₂ = a₁
    · subst ha
      by_cases hp : par = a₂
      ·
        refine ⟨s₀, Ws23K4.of_reflection W ((-1 : ℂ) ^ par.val) ((-1 : ℂ) ^ a₂.val) ?_ s₀ ?_ M₀⟩
        · rw [hp]; exact Ws23K4.one_add_neg_one_pow_val_mul_self a₂
        · intro t
          have := hWr1 par default hR u₁ u₂ a₂ rfl hp t
          simpa only [hWdef, Complex.ofReal_neg] using this
      ·
        have hp' : par = a₂ + 1 := Ws23K4.zmod2_eq_add_one_of_ne hp
        obtain ⟨s₀', H₁⟩ := hWr3 par default hR u₁ u₂ a₂ rfl hp'
        have M₁ : ∀ s : ℂ, max s₀ s₀' < s.re →
            MellinConvergent (fun t : ℝ => (W t + (-1 : ℂ) ^ a₂.val * W (-t)) / (t : ℂ)) s :=
          fun s hs => conv _ _ (H₁ s (lt_of_le_of_lt (le_max_right _ _) hs)).1
        refine ⟨max s₀ s₀', Ws23K4.of_two_combinations W ((-1 : ℂ) ^ par.val) ((-1 : ℂ) ^ a₂.val) ?_ (max s₀ s₀')
          (fun s hs => M₀ s (lt_of_le_of_lt (le_max_left _ _) hs)) M₁⟩
        exact Ws23K4.neg_one_pow_val_ne hp
    ·
      have hcs : (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign = 1 :=
        Ws23K4.zmod2_add_eq_one_of_ne (Ne.symm ha)
      obtain ⟨s₀', H₁⟩ := hWr4 par default hR (par + 1) (Or.inr (by rw [hcs]))
      have M₁ : ∀ s : ℂ, max s₀ s₀' < s.re →
          MellinConvergent (fun t : ℝ => (W t + (-1 : ℂ) ^ (par + 1).val * W (-t)) / (t : ℂ)) s :=
        fun s hs => conv _ _ (H₁ s (lt_of_le_of_lt (le_max_right _ _) hs)).1
      refine ⟨max s₀ s₀', Ws23K4.of_two_combinations W ((-1 : ℂ) ^ par.val) ((-1 : ℂ) ^ (par + 1).val) ?_ (max s₀ s₀')
        (fun s hs => M₀ s (lt_of_le_of_lt (le_max_left _ _) hs)) M₁⟩
      exact Ws23K4.neg_one_pow_val_ne (fun h => by
        have := congrArg (· + par) h; simp [add_assoc] at this)
  ·
    refine ⟨s₀, Ws23K4.of_support W ((-1 : ℂ) ^ par.val) s₀ ?_ M₀⟩
    intro y hy
    have := hWr2 par default hR u₀ n hn rfl (-y) (by linarith)
    simpa only [hWdef] using this

end S_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top (solution)

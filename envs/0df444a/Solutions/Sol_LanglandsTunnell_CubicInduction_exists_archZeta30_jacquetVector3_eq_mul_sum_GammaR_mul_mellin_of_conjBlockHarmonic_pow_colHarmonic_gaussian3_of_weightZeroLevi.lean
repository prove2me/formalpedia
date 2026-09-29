-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b9ad5746-d894-559c-b3aa-0c9cf9b72b2f

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Theorems.Thm_LanglandsTunnell_integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum
import Theorems.Thm_LanglandsTunnell_hermite_fourfold_reflection_eq_sum_filter
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

open LanglandsTunnell.Converse.ArchR Set in
theorem solution
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (m : ℕ) (hm : 1 ≤ m)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ m) * gaussian3 M)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (H : ℕ → ℝ → ℂ)
    (hH : ∀ j : ℕ, H j = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((m : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      (∀ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c)),
        MellinConvergent (H T.2.1) (s + (T.2.2 : ℂ) - 1)) ∧
      archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
        (κ : ℂ) * (4 * (Real.pi : ℂ)) * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + (e : ZMod 2)).val) * (a : ℂ) ^ m *
          ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
              (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c)),
            ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ T.1.1)) *
              Complex.Gammaℝ (s + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1) (s + (T.2.2 : ℂ) - 1) := by
  classical

  set Adm := ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
      (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
        ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c)) with hAdm
  set cT : (ℕ × ℕ) × (ℕ × ℕ) → ℂ := fun T => (-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) /
      ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ T.1.1) with hcT

  set F : ℝ → ℝ → ℝ → ℂ := fun y y₁ y₂ =>
      quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (m + 2) : ℝ)) : ℂ) * centralChar P₂ y₂ *
        (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
        D.W (diagOne ((a : ℝ) * y * y₁ / y₂)) with hF
  set mono : (ℕ × ℕ) × (ℕ × ℕ) → ℝ → ℝ → ℝ → ℂ := fun T y y₁ y₂ =>
      ((((y₁⁻¹) ^ T.1.2 * (y₂⁻¹) ^ T.2.1 * ((a : ℝ) * y * y₁) ^ T.2.2 : ℝ)) : ℂ) with hmono

  have hc4 : ∀ T : (ℕ × ℕ) × (ℕ × ℕ), ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ => ((q.1 : ℝ) : ℂ) ^ (s - 2) * (F q.1 q.2.1 q.2.2 * mono T q.1 q.2.1 q.2.2))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) ∧
      MellinConvergent (H T.2.1) (s + (T.2.2 : ℂ) - 1) ∧
      ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) * ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), F y y₁ y₂ * mono T y y₁ y₂ =
        (a : ℂ) ^ T.2.2 * ((1 / 2 : ℂ) * Complex.Gammaℝ (s + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1) (s + (T.2.2 : ℂ) - 1)) := by
    intro T
    obtain ⟨σ₀, h⟩ := LanglandsTunnell.CubicInduction.integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
      a ha D u₃ a₃ m T.1.2 T.2.1 T.2.2 (H T.2.1) (hH T.2.1)
    refine ⟨σ₀, fun s hs => ?_⟩
    obtain ⟨h1, h2, h3⟩ := h s hs
    refine ⟨?_, h2, ?_⟩
    · simpa only [hF, hmono, mul_assoc] using h1
    · simpa only [hF, hmono, mul_assoc] using h3
  choose σT hσT using hc4

  obtain ⟨σ₃, hc3⟩ := LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
    a ha psiInf hpsiInf D hDW0 u₃ a₃ m hm S hS u₁ u₂ c hP₂eq hpar ν_mul κ hκ σ e hσ E hE

  set σS : ℝ := ∑ T ∈ Adm, max (σT T) 0 with hσS
  have hσT_le : ∀ T ∈ Adm, σT T ≤ σS := fun T hT =>
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun T => max (σT T) 0) (fun _ _ => le_max_right _ _) hT)
  refine ⟨max σ₃ σS, fun s hs => ?_⟩
  have hs3 : σ₃ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsT : ∀ T ∈ Adm, σT T < s.re := fun T hT => lt_of_le_of_lt ((hσT_le T hT).trans (le_max_right _ _)) hs
  refine ⟨fun T hT => (hσT T s (hsT T hT)).2.1, ?_⟩
  obtain ⟨hκpos, hZ⟩ := hc3 s hs3
  rw [hZ]

  have hbr : ∀ y y₁ y₂ : ℝ,
      ((∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
        (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val *
          (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
        (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ c.val *
          (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
        (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ a₃.val *
          (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m)) =
      4 * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + (e : ZMod 2)).val) * ∑ T ∈ Adm, cT T * mono T y y₁ y₂ := by
    intro y y₁ y₂
    rw [LanglandsTunnell.integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum,
      LanglandsTunnell.integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum,
      LanglandsTunnell.integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum,
      LanglandsTunnell.integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum]
    have h2 := LanglandsTunnell.hermite_fourfold_reflection_eq_sum_filter m a₃ c (e : ZMod 2)
      (((1 / y₁ : ℝ)) : ℂ) (((1 / y₂ : ℝ)) : ℂ) ((((a : ℝ) * y * y₁ : ℝ)) : ℂ)
    have e1 : (((1 / y₁ : ℝ)) : ℂ) - (((1 / y₂ : ℝ)) : ℂ) - ((((a : ℝ) * y * y₁ : ℝ)) : ℂ) = (((1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ)) : ℂ) := by push_cast; ring
    have e2 : -(((1 / y₁ : ℝ)) : ℂ) - (((1 / y₂ : ℝ)) : ℂ) + ((((a : ℝ) * y * y₁ : ℝ)) : ℂ) = (((-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ)) : ℂ) := by push_cast; ring
    have e3 : (((1 / y₁ : ℝ)) : ℂ) - (((1 / y₂ : ℝ)) : ℂ) + ((((a : ℝ) * y * y₁ : ℝ)) : ℂ) = (((1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ)) : ℂ) := by push_cast; ring
    have e4 : -(((1 / y₁ : ℝ)) : ℂ) - (((1 / y₂ : ℝ)) : ℂ) - ((((a : ℝ) * y * y₁ : ℝ)) : ℂ) = (((-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ)) : ℂ) := by push_cast; ring
    rw [e1, e2, e3, e4] at h2
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [hcT, hmono]
    push_cast
    ring

  set μ3 : Measure (ℝ × ℝ × ℝ) := (volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) with hμ3
  set term : (ℕ × ℕ) × (ℕ × ℕ) → ℝ × ℝ × ℝ → ℂ := fun T q => ((q.1 : ℝ) : ℂ) ^ (s - 2) * (F q.1 q.2.1 q.2.2 * mono T q.1 q.2.1 q.2.2) with hterm
  have hint : ∀ T ∈ Adm, Integrable (term T) μ3 := fun T hT => (hσT T s (hsT T hT)).1
  set full : ℝ × ℝ × ℝ → ℂ := fun q => (4 * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + (e : ZMod 2)).val)) * ∑ T ∈ Adm, cT T * term T q with hfull
  have hfullint : Integrable full μ3 := by
    refine Integrable.const_mul (integrable_finsetSum _ fun T hT => (hint T hT).const_mul (cT T)) _

  have hiter : ∀ G : ℝ × ℝ × ℝ → ℂ, Integrable G μ3 →
      ∫ q, G q ∂μ3 = ∫ y in Ioi (0 : ℝ), ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), G (y, y₁, y₂) := by
    intro G hG
    rw [hμ3] at hG ⊢
    rw [integral_prod _ hG]
    refine integral_congr_ae ?_
    filter_upwards [hG.prod_right_ae] with y hy
    rw [integral_prod _ hy]

  have hL : (∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
        ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
          quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (m + 2) : ℝ)) : ℂ) * centralChar P₂ y₂ *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
            D.W (diagOne ((a : ℝ) * y * y₁ / y₂)) *
            ((∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
              (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val *
                (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
              (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ c.val *
                (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
              (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ a₃.val *
                (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m))) =
      ∫ q, full q ∂μ3 := by
    rw [hiter full hfullint]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₁ _ => ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₂ _ => ?_
    rw [hbr y y₁ y₂]
    simp only [hfull, hterm, hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  rw [hL]
  have hsum : ∫ q, full q ∂μ3 =
      (4 * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + (e : ZMod 2)).val)) * ∑ T ∈ Adm, cT T *
        ((a : ℂ) ^ T.2.2 * ((1 / 2 : ℂ) * Complex.Gammaℝ (s + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1) (s + (T.2.2 : ℂ) - 1))) := by
    simp only [hfull]
    rw [integral_const_mul, integral_finsetSum _ fun T hT => (hint T hT).const_mul (cT T)]
    congr 1
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [integral_const_mul, hiter (term T) (hint T hT)]
    congr 1
    rw [← (hσT T s (hsT T hT)).2.2]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hterm]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₁ _ => ?_
    rw [← integral_const_mul]
  rw [hsum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [hcT]
  ring

#print axioms solution

end S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi (solution)

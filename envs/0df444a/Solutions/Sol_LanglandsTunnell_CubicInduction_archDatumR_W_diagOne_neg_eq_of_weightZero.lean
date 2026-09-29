-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.archDatumR_W_diagOne_neg_eq_of_weightZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/59678b4d-29fa-53c7-8bf8-3ca4d4070e09

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_archDatumR_W_diagOne_neg_eq_of_weightZero

set_option autoImplicit false

noncomputable section

namespace K5ParityWeightZero

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

theorem exists_unit_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (t : ℝ) :
    ∃ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = Real.exp t ∧
      extensionEmbedding w (x : w.Completion) = (Real.exp t : ℂ) := by
  set y : w.Completion := (ringEquivRealOfIsReal hw).symm (Real.exp t) with hy
  have hey : extensionEmbeddingOfIsReal hw y = Real.exp t := by
    rw [← ringEquivRealOfIsReal_apply, hy, RingEquiv.apply_symm_apply]
  have hey' : extensionEmbedding w y = (Real.exp t : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hw, hey]
  have hnorm : ‖y‖ = Real.exp t := by
    have := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y
    rw [← this, hey', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact (Real.exp_pos t).ne' hnorm.symm
  exact ⟨Units.mk0 y hy0, hnorm, hey'⟩

theorem re_eq_zero_of_isArchCompAt_of_isReal {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (huμ : IsUnitaryChar (𝓞 K) K μ)
    {w : InfinitePlace K} (hw : w.IsReal) {u : ℂ} {a : ℤ} (h : IsArchCompAt K μ w u a) : u.re = 0 := by
  obtain ⟨x, hxn, hxe⟩ := exists_unit_of_isReal (K := K) hw 1
  have h1 : ‖((archLocalChar μ w x : ℂˣ) : ℂ)‖ = 1 := huμ _
  rw [h x, hxn, hxe, div_self (by exact_mod_cast (Real.exp_pos 1).ne'), one_zpow, mul_one,
    Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le), Complex.norm_exp,
    Real.exp_eq_one_iff] at h1
  have hm : (w.mult : ℝ) ≠ 0 := mult_coe_ne_zero
  simp only [Complex.ofReal_one, one_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at h1
  rcases mul_eq_zero.mp h1 with h' | h'
  · exact absurd h' hm
  · exact h'

theorem diagOne_mul_diagonal (τ : ℝ) :
    ArchR.diagOne τ * Matrix.diagonal ![(-1 : ℝ), 1] = ArchR.diagOne (-τ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem det_diagOne (τ : ℝ) : (ArchR.diagOne τ).det = τ := by
  simp [ArchR.diagOne, Matrix.det_fin_two_of]

end K5ParityWeightZero

end

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (hk₀min : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1))
    (hk₀ : k₀ = 0)
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (τ : ℝ) (hτ : τ ≠ 0) :
    D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c₁.val * D.W (ArchR.diagOne τ) := by

  subst hk₀
  subst hP₂eq

  have hc : c₂ = c₁ := by
    have h := (hk₀min.1 u₁ u₂ c₁ c₂ rfl).2
    rw [Int.cast_zero] at h
    have key : ∀ a b : ZMod 2, 0 = a + b → b = a := by decide
    exact key c₁ c₂ h
  subst c₂

  have hgen : ∀ q : ℤ, Odd q → u₁ - u₂ ≠ (q : ℂ) := by
    rcases hP₂ with ⟨w₁, w₂, h₁, h₂, -, -, -, -, hP⟩ | ⟨wC, hC, -, hP⟩
    · simp only [RealArchParam.principal.injEq] at hP
      obtain ⟨hu₁, -, hu₂, -⟩ := hP
      have hre₁ : u₁.re = 0 := hu₁ ▸ K5ParityWeightZero.re_eq_zero_of_isArchCompAt_of_isReal hμ.2.2 h₁ (huR w₁ h₁)
      have hre₂ : u₂.re = 0 := hu₂ ▸ K5ParityWeightZero.re_eq_zero_of_isArchCompAt_of_isReal hμ.2.2 h₂ (huR w₂ h₂)
      intro q hq heq
      have hre := congrArg Complex.re heq
      rw [Complex.sub_re, hre₁, hre₂, sub_zero, Complex.intCast_re] at hre
      have hq0 : q = 0 := by exact_mod_cast hre.symm
      rw [hq0] at hq
      exact absurd hq (by decide)
    · rcases hP with ⟨_, hP⟩ | ⟨-, hP⟩
      · exact absurd hP (by simp)
      · simp only [RealArchParam.principal.injEq] at hP
        obtain ⟨-, h0, -, h1⟩ := hP
        exact absurd (h0.symm.trans h1) (by decide)
  have hdet : (ArchR.diagOne τ).det ≠ 0 := by rw [K5ParityWeightZero.det_diagOne]; exact hτ
  have key := ArchDatumR.W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
    u₁ u₂ c₁ hgen D hDW hDE (ArchR.diagOne τ) hdet
  rw [K5ParityWeightZero.diagOne_mul_diagonal] at key
  exact key

end S_LanglandsTunnell_CubicInduction_archDatumR_W_diagOne_neg_eq_of_weightZero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_archDatumR_W_diagOne_neg_eq_of_weightZero (solution)

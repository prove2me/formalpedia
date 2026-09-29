-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightOneLevi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a47ebd5e-a6da-57c2-a33a-dddf58a55247

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

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_twoSheet_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_Converse_exists_odd_isAdmissibleTwist
import Theorems.Thm_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
import Theorems.Thm_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv
import Theorems.Thm_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real
import Theorems.Thm_LanglandsTunnell_mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightOneLevi
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws48K6BDtwo

noncomputable def Hfam {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℚ) (n : ℕ) (u₃ : ℂ) (j : ℕ) (b : ZMod 2) :
    ℝ → ℂ :=
  fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((n : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)

noncomputable def Zsum {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℚ) (m n : ℕ) (u₃ : ℂ) (a₃ : ZMod 2)
    (e : ℤ) (s : ℂ) : ℂ :=
  ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = (e : ZMod 2) + a₃)),
            ((-1 : ℂ) ^ (T.2.1 + T.2.2) *
              ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ T.1.1))) *
              Complex.Gammaℝ (s + u₃ + (T.1.2 : ℂ)) * mellin (Hfam D a n u₃ T.2.1 ((e : ZMod 2) + (T.2.2 : ZMod 2))) (s + (T.2.2 : ℂ) - 1)

open scoped Classical in

theorem assembly
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
    (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)

    (hk₀ : k₀ = 1) (μ₁ μ₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) (hc : c₁ ≠ c₂) (ρ : ℂ)
    (hD : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hρ0 : ρ ≠ 0)
    (e : ℤ) (he : e = 0 ∨ e = 1)
    (hdom : ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ Zsum D a m n (uR w₀ h₀) (aR w₀ h₀) e s ≠ 0) :
    ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
      ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0 := by
  classical
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha

  obtain ⟨κ, hκpos, hκ⟩ :=
    AutomorphicForm.StandardKernel.exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv ν_mul

  obtain ⟨σ, hσadm, hσarch⟩ : ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
      ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e := by
    rcases he with rfl | rfl
    · obtain ⟨χ, hχ, -, -, hχa⟩ :=
        LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le ∅ (fun _ => 3)
          (fun v hv => absurd hv (Finset.notMem_empty v))
      exact ⟨χ, hχ, hχa⟩
    · obtain ⟨χ, hχ, hχa⟩ := LanglandsTunnell.Converse.exists_odd_isAdmissibleTwist
      exact ⟨χ, hχ, hχa⟩

  subst hk₀
  have hDW1 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ ((1 : ℕ) : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ) := fun r x => by
    exact_mod_cast hDW r x
  have hcol1 : (ε' = -1 ∧ (n : ℤ) = ((1 : ℕ) : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - (1 : ℕ)) := by
    exact_mod_cast hcol

  obtain ⟨σ₀, hA⟩ :=
    LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_twoSheet_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
      a ha psiInf hpsiInf D 1 hDW1 (uR w₀ h₀) (aR w₀ h₀) m n ε' hcol1 S hS ν_mul κ hκ σ e hσarch E hE
      (Hfam D a n (uR w₀ h₀)) (fun j b => rfl)

  obtain ⟨s, hs, hne⟩ := hdom σ₀
  refine ⟨σ, hσadm, s, ?_⟩
  rw [(hA s hs).2]
  have hε' : (ε' : ℂ) ≠ 0 := by
    rcases hcol with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκpos.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  refine mul_ne_zero (mul_ne_zero hκ0 (mul_ne_zero (mul_ne_zero two_ne_zero hπ) (pow_ne_zero _ (mul_ne_zero hε' haC)))) ?_
  exact hne

open scoped Classical in

theorem assembly_of_MG_real
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
    (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)

    (hk₀ : k₀ = 1) (μ₁ μ₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) (hc : c₁ ≠ c₂) (ρ : ℂ)
    (hD : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hρ0 : ρ ≠ 0)
    (e : ℤ) (he : e = 0 ∨ e = 1)
    (hA : ∀ (j : ℕ) (b : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (Hfam D a n (uR w₀ h₀) j b) (x : ℂ) ≠ 0 ∧
      ‖mellin (Hfam D a n (uR w₀ h₀) j b) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) *
          mellin (Hfam D a n (uR w₀ h₀) j b) (x : ℂ)‖ ≤ ε * x * ‖mellin (Hfam D a n (uR w₀ h₀) j b) (x : ℂ)‖)
    (hB : ∀ (j : ℕ) (b b' : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (Hfam D a n (uR w₀ h₀) (j + 1) b') ((x : ℂ) - 1)‖ ≤ ε * ‖mellin (Hfam D a n (uR w₀ h₀) j b) (x : ℂ)‖) :
    ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
      ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0 := by
  classical
  have hne : (((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
      (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
        ((T.1.2 : ZMod 2) = (e : ZMod 2) + aR w₀ h₀))).Nonempty := by
    set i₀ : ℕ := ((e : ZMod 2) + aR w₀ h₀).val with hi₀
    have hi₀le : i₀ ≤ 1 := by
      have := ZMod.val_lt ((e : ZMod 2) + aR w₀ h₀); omega
    refine ⟨((0, i₀), (0, m - i₀)), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega, ?_⟩
    rw [hi₀]; exact ZMod.natCast_zmod_val _
  refine assembly K hdeg μ hμ uR aR uC kC huR huC ω hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D k₀
    hDW hDE hDnz hk₀min m hm n ε' hcol S hS hk₀ μ₁ μ₂ c₁ c₂ hP₂eq hc ρ hD hρ0 e he (fun σ₀ => ?_)
  obtain ⟨s, hs, hne'⟩ :=
    LanglandsTunnell.exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real m a ha (uR w₀ h₀) (aR w₀ h₀) e
      hne (Hfam D a n (uR w₀ h₀)) hA hB σ₀
  exact ⟨(s : ℂ), by simpa using hs, hne'⟩

theorem Hfam_succ {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℚ) (n : ℕ) (u₃ : ℂ) (j : ℕ) (b : ZMod 2) :
    Hfam D a n u₃ (j + 1) b = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ (((n : ℂ) - u₃ - 1 - (j : ℂ)) - 1) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ) := by
  funext σ'
  simp only [Hfam, Nat.cast_succ]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
  congr 2
  ring

noncomputable def Hx (a : ℝ) (C p q κ : ℂ) : ℝ → ℂ :=
  fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)

noncomputable def Cb (a : ℚ) (ρ : ℂ) (b : ZMod 2) : ℂ := if (0 : ℚ) < a then ρ else (-1 : ℂ) ^ b.val * ρ

theorem Cb_ne_zero (a : ℚ) {ρ : ℂ} (hρ : ρ ≠ 0) (b : ZMod 2) : Cb a ρ b ≠ 0 := by
  unfold Cb; split_ifs
  · exact hρ
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hρ

theorem signShift_add_signShift_of_ne {x y : ZMod 2} (hxy : x ≠ y) : signShift x + signShift y = 1 := by
  unfold signShift
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) x with hx | hx <;>
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) y with hy | hy <;> subst hx hy <;> simp_all

theorem centralChar_mul_abs_of_principal_pos {P₂ : RealArchParam} {μ₁ μ₂ : ℂ} {c₁ c₂ : ZMod 2}
    (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) {w : ℝ} (hw : 0 < w) :
    ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ) = ((w : ℝ) : ℂ) ^ (μ₁ + μ₂ + 1) := by
  have hif : (if c₁ + c₂ = 0 then (1 : ℂ) else ((SignType.sign w : ℝ) : ℂ)) = 1 := by
    split_ifs
    · rfl
    · rw [sign_pos hw]; simp
  have hw0 : ((w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  rw [ArchR.centralChar, ArchR.quasiChar, hP₂eq, RealArchParam.centralExponent, RealArchParam.centralSign, hif, mul_one,
    abs_of_pos hw, show ((w : ℝ) : ℂ) ^ (μ₁ + μ₂ + 1) = ((w : ℝ) : ℂ) ^ (μ₁ + μ₂) * ((w : ℝ) : ℂ) from by
      rw [Complex.cpow_add _ _ hw0, Complex.cpow_one]]

theorem mellin_congr_Ioi {f g : ℝ → ℂ} (h : ∀ t ∈ Set.Ioi (0 : ℝ), f t = g t) : mellin f = mellin g := by
  funext s
  unfold mellin
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [h t ht]

theorem Hfam_eq_Hx {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℚ) (ha : a ≠ 0) (n : ℕ) (u₃ : ℂ)
    {μ₁ μ₂ : ℂ} {c₁ c₂ : ZMod 2} (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) (ρ : ℂ)
    (hD : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (j : ℕ) (b : ZMod 2) {σ' : ℝ} (hσ : 0 < σ') :
    Hfam D a n u₃ j b σ' =
      Hx (a : ℝ) (Cb a ρ b) (μ₁ + signShift (c₁ + b)) (μ₂ + signShift (c₂ + b))
        (μ₁ + μ₂ + 1 + ((n : ℂ) - u₃ - 1 - (j : ℂ))) σ' := by
  have hpm : ((-1 : ℂ) ^ b.val) * ((-1 : ℂ) ^ b.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  simp only [Hfam, Hx]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
  have hw0 : ((w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  have hτ : 0 < |(a : ℝ)| * σ' / w := by
    have : 0 < |(a : ℝ)| := abs_pos.2 (by exact_mod_cast ha)
    positivity
  have hk : ((w : ℝ) : ℂ) ^ (μ₁ + μ₂ + 1 + ((n : ℂ) - u₃ - 1 - (j : ℂ))) =
      ((w : ℝ) : ℂ) ^ (μ₁ + μ₂ + 1) * ((w : ℝ) : ℂ) ^ ((n : ℂ) - u₃ - 1 - (j : ℂ)) := Complex.cpow_add _ _ hw0
  rw [centralChar_mul_abs_of_principal_pos hP₂eq hw, hk]
  rcases lt_or_gt_of_ne ha with hneg | hpos
  ·
    have e1 : (a : ℝ) * (σ' / w) = -(|(a : ℝ)| * σ' / w) := by
      rw [abs_of_neg (by exact_mod_cast hneg)]; ring
    have hC : Cb a ρ b = (-1 : ℂ) ^ b.val * ρ := if_neg (not_lt.2 hneg.le)
    rw [e1, neg_neg, hC]
    have key : D.W (ArchR.diagOne (-(|(a : ℝ)| * σ' / w))) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (|(a : ℝ)| * σ' / w)) =
        (-1 : ℂ) ^ b.val * (ρ * ((|(a : ℝ)| * σ' / w : ℝ) : ℂ) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((|(a : ℝ)| * σ' / w) / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) *
                (Real.exp (-(Real.pi * ((|(a : ℝ)| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) := by
      have h := hD b _ hτ
      linear_combination ((-1 : ℂ) ^ b.val) * h - (D.W (ArchR.diagOne (-(|(a : ℝ)| * σ' / w)))) * hpm
    rw [key]
    ring
  ·
    have e1 : (a : ℝ) * (σ' / w) = |(a : ℝ)| * σ' / w := by
      rw [abs_of_pos (by exact_mod_cast hpos)]; ring
    have hC : Cb a ρ b = ρ := if_pos hpos
    rw [e1, hC, hD b _ hτ]
    ring

theorem mellin_Hfam_eq {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℚ) (ha : a ≠ 0) (n : ℕ) (u₃ : ℂ)
    {μ₁ μ₂ : ℂ} {c₁ c₂ : ZMod 2} (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) (ρ : ℂ)
    (hD : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (j : ℕ) (b : ZMod 2) :
    mellin (Hfam D a n u₃ j b) =
      mellin (Hx (a : ℝ) (Cb a ρ b) (μ₁ + signShift (c₁ + b)) (μ₂ + signShift (c₂ + b))
        (μ₁ + μ₂ + 1 + ((n : ℂ) - u₃ - 1 - (j : ℂ)))) :=
  mellin_congr_Ioi fun σ' hσ => Hfam_eq_Hx D a ha n u₃ hP₂eq ρ hD j b hσ

end Ws48K6BDtwo

open Ws48K6BDtwo in
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
    (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)

    (hk₀ : k₀ = 1) (μ₁ μ₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) (hc : c₁ ≠ c₂) (ρ : ℂ)
    (hD : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hρ0 : ρ ≠ 0) :
    ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
      ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0 := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha

  have hsum : ∀ b : ZMod 2,
      (μ₁ + signShift (c₁ + b)) + (μ₂ + signShift (c₂ + b)) = μ₁ + μ₂ + 1 := by
    intro b
    have h := signShift_add_signShift_of_ne (x := c₁ + b) (y := c₂ + b) (fun h => hc (add_right_cancel h))
    linear_combination h

  have MG : ∀ (j : ℕ) (b b' : ZMod 2), ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (Hfam D a n (uR w₀ h₀) j b) (x : ℂ) ≠ 0 ∧
      ‖mellin (Hfam D a n (uR w₀ h₀) j b) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * ((a : ℝ) : ℂ) ^ 2) *
          mellin (Hfam D a n (uR w₀ h₀) j b) (x : ℂ)‖ ≤ δ * x * ‖mellin (Hfam D a n (uR w₀ h₀) j b) (x : ℂ)‖ ∧
      ‖mellin (Hfam D a n (uR w₀ h₀) (j + 1) b') ((x : ℂ) - 1)‖ ≤ δ * ‖mellin (Hfam D a n (uR w₀ h₀) j b) (x : ℂ)‖ := by
    intro j b b' δ hδ
    have hκ : μ₁ + μ₂ + 1 + ((n : ℂ) - uR w₀ h₀ - 1 - ((j + 1 : ℕ) : ℂ)) =
        μ₁ + μ₂ + 1 + ((n : ℂ) - uR w₀ h₀ - 1 - (j : ℂ)) - 1 := by
      push_cast; ring
    rw [mellin_Hfam_eq D a ha n (uR w₀ h₀) hP₂eq ρ hD j b, mellin_Hfam_eq D a ha n (uR w₀ h₀) hP₂eq ρ hD (j + 1) b', hκ]
    obtain ⟨R, hR⟩ :=
      LanglandsTunnell.mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep (a : ℝ) ha'
        (μ₁ + signShift (c₁ + b)) (μ₂ + signShift (c₂ + b)) (μ₁ + μ₂ + 1 + ((n : ℂ) - uR w₀ h₀ - 1 - (j : ℂ)))
        (Cb a ρ b) (Cb_ne_zero a hρ0 b)
        (μ₁ + signShift (c₁ + b')) (μ₂ + signShift (c₂ + b')) (Cb a ρ b') (le_of_eq (by rw [hsum, hsum]))
        (Hx (a : ℝ) (Cb a ρ b) (μ₁ + signShift (c₁ + b)) (μ₂ + signShift (c₂ + b))
          (μ₁ + μ₂ + 1 + ((n : ℂ) - uR w₀ h₀ - 1 - (j : ℂ))))
        (Hx (a : ℝ) (Cb a ρ b') (μ₁ + signShift (c₁ + b')) (μ₂ + signShift (c₂ + b'))
          (μ₁ + μ₂ + 1 + ((n : ℂ) - uR w₀ h₀ - 1 - (j : ℂ)) - 1))
        (Hx (a : ℝ) (Cb a ρ b) (μ₁ + signShift (c₁ + b)) (μ₂ + signShift (c₂ + b))
          (μ₁ + μ₂ + 1 + ((n : ℂ) - uR w₀ h₀ - 1 - (j : ℂ)) - 2))
        rfl rfl rfl δ hδ
    exact ⟨R, fun x hx => ⟨(hR x hx).1, (hR x hx).2.1, (hR x hx).2.2.1⟩⟩
  refine assembly_of_MG_real K hdeg μ hμ uR aR uC kC huR huC ω hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D k₀
    hDW hDE hDnz hk₀min m hm n ε' hcol S hS hk₀ μ₁ μ₂ c₁ c₂ hP₂eq hc ρ hD hρ0 0 (Or.inl rfl) ?_ ?_
  · intro j b δ hδ
    obtain ⟨R, hR⟩ := MG j b b δ hδ
    refine ⟨R, fun x hx => ⟨(hR x hx).1, ?_⟩⟩
    have := (hR x hx).2.1
    simpa only [Complex.ofReal_ratCast] using this
  · intro j b b' δ hδ
    obtain ⟨R, hR⟩ := MG j b b' δ hδ
    exact ⟨R, fun x hx => (hR x hx).2.2⟩

end S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightOneLevi
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightOneLevi (solution)

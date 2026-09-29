-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_discreteLevi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/23f1f64f-7588-5855-9ba4-8035c0672f68

import Theorems.Thm_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real
import Theorems.Thm_LanglandsTunnell_mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep
import Theorems.Thm_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_twoSheet_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_Converse_exists_odd_isAdmissibleTwist
import Theorems.Thm_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
import Theorems.Thm_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_discreteLevi
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false

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
    (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)

    (μ : ℂ) (k : ℕ) (hk : 1 ≤ k) (hP₂eq : P₂ = RealArchParam.discrete μ k hk) (ρ : ℂ)
    (hDpos : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (μ + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ))))
    (hDneg : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0)
    (hρ0 : ρ ≠ 0) :
    ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
      ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0 := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha

  obtain ⟨κ, hκpos, hκ⟩ := AutomorphicForm.StandardKernel.exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv ν_mul

  have hk₀Z : k₀ = (k : ℤ) + 1 := hk₀min.2 μ k hk hP₂eq
  have hDW' : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ ((k + 1 : ℕ) : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro r x; rw [hDW r x, hk₀Z]; push_cast; rfl
  have hcol' : (ε' = -1 ∧ (n : ℤ) = ((k + 1 : ℕ) : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - (k + 1 : ℕ)) := by
    rcases hcol with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by rw [h2, hk₀Z]; push_cast; ring⟩
    · exact Or.inr ⟨h1, by rw [h2, hk₀Z]; push_cast; ring⟩

  have htw : ∀ e' : ZMod 2, ∃ (e : ℤ) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e) ∧ ((e : ZMod 2)) = e' := by
    intro e'
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) e' with h3 | h3
    · obtain ⟨χ, hχ, -, -, hχa⟩ := LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le ∅ (fun _ => 3)
        (fun v hv => absurd hv (Finset.notMem_empty v))
      exact ⟨0, χ, hχ, hχa, by rw [h3]; decide⟩
    · obtain ⟨χ, hχ, hχa⟩ := LanglandsTunnell.Converse.exists_odd_isAdmissibleTwist
      exact ⟨1, χ, hχ, hχa, by rw [h3]; decide⟩

  set u₃ : ℂ := uR w₀ h₀ with hu₃
  set a₃ : ZMod 2 := aR w₀ h₀ with ha₃
  set H : ℕ → ZMod 2 → ℝ → ℂ := fun j b σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((n : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ) with hH

  have hA : ∀ (e : ℤ) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ),
      (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e) →
      ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
        (∀ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
            (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = (e : ZMod 2) + a₃)),
          MellinConvergent (H T.2.1 ((e : ZMod 2) + (T.2.2 : ZMod 2))) (s + (T.2.2 : ℂ) - 1)) ∧
        archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
          (κ : ℂ) * (2 * (Real.pi : ℂ) * ((ε' : ℂ) * (a : ℂ)) ^ n) *
            ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
            (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = (e : ZMod 2) + a₃)),
              ((-1 : ℂ) ^ (T.2.1 + T.2.2) *
                ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                  ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                    (4 * (Real.pi : ℂ)) ^ T.1.1))) *
                Complex.Gammaℝ (s + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1 ((e : ZMod 2) + (T.2.2 : ZMod 2))) (s + (T.2.2 : ℂ) - 1) :=
    fun e σ hσ =>
      LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_twoSheet_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
        a ha psiInf hpsiInf D (k + 1) hDW' u₃ a₃ m n ε' hcol' S hS ν_mul κ hκ σ e hσ E hE H (fun j b => rfl)

  obtain ⟨e, σ, hσadm, hσarch, -⟩ := htw 0
  refine ⟨σ, hσadm, ?_⟩
  obtain ⟨σ₀, hσ₀⟩ := hA e σ hσarch

  have hρ0' : ρ ≠ 0 := hρ0
  set βd : ℂ := μ + (k : ℂ) / 2 + 1 with hβd

  set εa : ZMod 2 → ℂ := fun b => if (0 : ℝ) < (a : ℝ) then 1 else (-1 : ℂ) ^ b.val with hεa
  have hεa0 : ∀ b, εa b ≠ 0 := by
    intro b; simp only [hεa]; split_ifs
    · exact one_ne_zero
    · exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have habs0 : 0 < |(a : ℝ)| := abs_pos.2 ha'

  have hcomb : ∀ (b : ZMod 2) (σ' w : ℝ), 0 < σ' → 0 < w →
      D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w)))) =
        εa b * ρ * ((2 : ℂ) * ((((|(a : ℝ)| * σ' / w : ℝ)) : ℂ) ^ βd * (Real.exp (-(2 * Real.pi * (|(a : ℝ)| * σ' / w))) : ℂ))) := by
    intro b σ' w hσ hw
    have hy : 0 < |(a : ℝ)| * σ' / w := by positivity
    rcases lt_or_gt_of_ne ha' with hneg | hpos
    · have e1 : (a : ℝ) * (σ' / w) = -(|(a : ℝ)| * σ' / w) := by rw [abs_of_neg hneg]; ring
      rw [e1, neg_neg, hDneg _ hy, hDpos _ hy, zero_add]
      simp only [hεa, if_neg (not_lt.2 hneg.le)]
      ring
    · have e1 : (a : ℝ) * (σ' / w) = |(a : ℝ)| * σ' / w := by rw [abs_of_pos hpos]; ring
      rw [e1, hDpos _ hy, hDneg _ hy, mul_zero, add_zero]
      simp only [hεa, if_pos hpos]
      ring

  have hcc : ∀ w : ℝ, 0 < w → ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ) = ((w : ℝ) : ℂ) ^ (P₂.centralExponent + 1) := by
    intro w hw
    have hw0 : ((w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
    simp only [ArchR.centralChar, ArchR.quasiChar, abs_of_pos hw, sign_pos hw, SignType.coe_one, Complex.ofReal_one, ite_self,
      mul_one]
    rw [Complex.cpow_add _ _ hw0, Complex.cpow_one]

  set kap : ℕ → ℂ := fun j => P₂.centralExponent + 1 + ((n : ℂ) - u₃ - 1 - (j : ℂ)) with hkap
  set HJ : ℕ → ZMod 2 → ℝ → ℂ := fun j b σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (εa b * ρ * (((|(a : ℝ)| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ (βd - 1) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|(a : ℝ)| * σ' / w) / r : ℝ) : ℂ) ^ βd * (Real.exp (-(Real.pi * ((|(a : ℝ)| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ kap j * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ) with hHJ

  have hHeq : ∀ (j : ℕ) (b : ZMod 2) (σ' : ℝ), 0 < σ' → H j b σ' = HJ j b σ' := by
    intro j b σ' hσ
    simp only [hH, hHJ]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun w (hw : (0:ℝ) < w) => ?_)
    have hy : 0 < |(a : ℝ)| * σ' / w := by positivity
    have hy0 : ((((|(a : ℝ)| * σ' / w : ℝ)) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
    have hw0 : ((w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
    have hK := LanglandsTunnell.mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul (βd - 1) _ hy
    rw [show βd - 1 + 1 = βd by ring] at hK
    have hwpow : ((w : ℝ) : ℂ) ^ kap j = ((w : ℝ) : ℂ) ^ (P₂.centralExponent + 1) * ((w : ℝ) : ℂ) ^ ((n : ℂ) - u₃ - 1 - (j : ℂ)) := by
      simp only [hkap]; rw [Complex.cpow_add _ _ hw0]
    have hypow : ((((|(a : ℝ)| * σ' / w : ℝ)) : ℂ)) * ((((|(a : ℝ)| * σ' / w : ℝ)) : ℂ)) ^ (βd - 1) =
        ((((|(a : ℝ)| * σ' / w : ℝ)) : ℂ)) ^ βd := by
      rw [Complex.cpow_sub _ _ hy0, Complex.cpow_one]; field_simp
    rw [hcomb b σ' w hσ hw, hK, hcc w hw, hwpow, ← hypow]
    ring
  have hmel : ∀ (j : ℕ) (b : ZMod 2), mellin (H j b) = mellin (HJ j b) := by
    intro j b; funext z
    simp only [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi (fun σ' hσ' => by rw [hHeq j b σ' hσ'])
  have hMG : ∀ (j : ℕ) (b b' : ZMod 2), ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (H j b) (x : ℂ) ≠ 0 ∧
      ‖mellin (H j b) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (((a : ℝ) : ℝ) : ℂ) ^ 2) * mellin (H j b) (x : ℂ)‖
          ≤ δ * x * ‖mellin (H j b) (x : ℂ)‖ ∧
      ‖mellin (H (j + 1) b') ((x : ℂ) - 1)‖ ≤ δ * ‖mellin (H j b) (x : ℂ)‖ ∧
      ‖mellin (H (j + 2) b) (x : ℂ)‖ ≤ δ * ‖mellin (H j b) (x : ℂ)‖ := by
    intro j b b'
    have e1 : kap (j + 1) = kap j - 1 := by simp only [hkap]; push_cast; ring
    have e2 : kap (j + 2) = kap j - 2 := by simp only [hkap]; push_cast; ring
    rw [hmel j b, hmel (j + 1) b', hmel (j + 2) b]
    refine LanglandsTunnell.mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep (a : ℝ) ha'
      (βd - 1) βd (kap j) (εa b * ρ) (mul_ne_zero (hεa0 b) hρ0') (βd - 1) βd (εa b' * ρ) le_rfl
      (HJ j b) (HJ (j + 1) b') (HJ (j + 2) b) ?_ ?_ ?_
    · rw [hHJ]
    · rw [hHJ]; simp only [e1]
    · rw [hHJ]; simp only [e2]
  have hne : (((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
      (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = (e : ZMod 2) + a₃))).Nonempty := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) ((e : ZMod 2) + a₃) with h0 | h1
    · refine ⟨((0, 0), (0, m)), ?_⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega, ?_⟩
      rw [h0]; simp
    · refine ⟨((0, 1), (0, m - 1)), ?_⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega, ?_⟩
      rw [h1]; simp
  have hcast : (((a : ℝ) : ℝ) : ℂ) = (a : ℂ) := Complex.ofReal_ratCast a
  obtain ⟨s, hs, hsum⟩ := LanglandsTunnell.exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real m a ha u₃ a₃ e hne H
    (fun j b ε hε => by
      obtain ⟨R, hR⟩ := hMG j b b ε hε
      refine ⟨R, fun x hx => ⟨(hR x hx).1, ?_⟩⟩
      have h2 := (hR x hx).2.1
      rwa [hcast] at h2)
    (fun j b b' ε hε => by
      obtain ⟨R, hR⟩ := hMG j b b' ε hε
      exact ⟨R, fun x hx => (hR x hx).2.2.1⟩)
    σ₀
  refine ⟨(s : ℂ), ?_⟩
  obtain ⟨-, hZ⟩ := hσ₀ (s : ℂ) (by simpa using hs)
  rw [hZ]
  have hε'0 : (ε' : ℂ) ≠ 0 := by
    rcases hcol with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> norm_num
  have hκ0 : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκpos.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  exact mul_ne_zero (mul_ne_zero hκ0 (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
    (pow_ne_zero _ (mul_ne_zero hε'0 ha0)))) hsum

#print axioms solution

end S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_discreteLevi
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_discreteLevi (solution)

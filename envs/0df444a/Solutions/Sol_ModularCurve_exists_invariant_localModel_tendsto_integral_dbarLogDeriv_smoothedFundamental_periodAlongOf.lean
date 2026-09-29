-- Prove2me | solution 1 for ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/61358620-991e-5e5e-8efe-b788f051a5fc

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_SmoothedFundamental
import Theorems.Thm_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex
import Theorems.Thm_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate
import Theorems.Thm_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
p2m_attr_erase "instance" "FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

p2m_open "UpperHalfPlane~I"
open MeasureTheory Filter Complex Set
open scoped MatrixGroups Topology Real ComplexConjugate ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "periodAlongOf clamp01_of_mem segmentPoint periodAlong smoothedFundamental exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex tendsto_integral_mul_smoothedFundamental_mul_finsum_translate contDiff_and_finsum_smoothedFundamental_eq_one exists_hasEquivariantPrimitiveOf periodAlongOf_apply_eq_sub_of_hasDerivAt"
namespace DivisorTerm
p2m_open "ModularCurve"

theorem coe_ofComplex {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

section Primitives

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

def Eg (g : CuspForm Γ 2) (z : ℂ) : ℂ :=
  ModularCurve.periodAlongOf Γ UpperHalfPlane.I (ofComplex z) g

theorem hasDerivAt_affine (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a + (s : ℂ) * b) (b - a) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have := ((h1.const_sub 1).mul_const a).add (h1.mul_const b)
  convert this using 1; rfl; rfl; ring

theorem segmentPoint_eq_of_mem {τ₀ τ₁ : ℍ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ModularCurve.segmentPoint τ₀ τ₁ t = (1 - (t : ℂ)) * τ₀ + (t : ℂ) * τ₁ := by
  simp only [ModularCurve.segmentPoint, ModularCurve.clamp01_of_mem ht, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem hasDerivAt_Eg (g : CuspForm Γ 2) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (Eg Γ g) (g (ofComplex z)) z := by
  obtain ⟨P, hP⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ g
  have hfun : Eg Γ g = fun w => (P ∘ ofComplex) w - P UpperHalfPlane.I := by
    funext w
    simp only [Eg, ModularCurve.periodAlongOf_apply_eq_sub_of_hasDerivAt Γ g hP.1, Function.comp]
  rw [hfun]
  have h1 : HasDerivAt (P ∘ ofComplex) (g (ofComplex z)) z := by
    have := hP.1 (ofComplex z)
    rwa [coe_ofComplex hz] at this
  exact h1.sub_const _

theorem Eg_coe (g : CuspForm Γ 2) (τ : ℍ) :
    Eg Γ g τ = ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ g := by
  simp [Eg, ofComplex_apply]

theorem g_smul (g : CuspForm Γ 2) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    g (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * g τ := by
  have := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  simpa using this

end Primitives

theorem finite_moving (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L) :
    {γ : SL(2, ℤ) | ((fun τ : ℍ => γ • τ) '' K ∩ L).Nonempty}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ) (T := ℍ) hK hL
  set φ : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ with hφ
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) hab
    simpa [hφ] using this
  refine Finite.of_finite_image ?_ hinj.injOn
  refine (h.image Subtype.val).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg, rfl⟩

scoped instance finite_stabilizer (Γ : Subgroup SL(2, ℤ)) (s : ℍ) : Finite (MulAction.stabilizer Γ s) := by
  have hf0 : {γ : SL(2, ℤ) | γ • s = s}.Finite := by
    refine (finite_moving {s} {s} isCompact_singleton isCompact_singleton).subset ?_
    intro γ hγ
    exact ⟨s, ⟨s, rfl, hγ⟩, rfl⟩
  have hf : {γ : Γ | (γ : SL(2, ℤ)) • s = s}.Finite := hf0.preimage Subtype.val_injective.injOn
  have : (MulAction.stabilizer Γ s : Set Γ) = {γ : Γ | (γ : SL(2, ℤ)) • s = s} := by
    ext γ; rfl
  exact (this ▸ hf).to_subtype

theorem main {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S, (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer Γ s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ) (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :
    ∃ V : ℂ → ℂ,
      (∀ (γ : Γ) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ (T : ℝ) (g : CuspForm Γ 2),
        Integrable fun z : ℂ => g (ofComplex z) * h T z *
          ((fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z)) ∧
      ∀ g : CuspForm Γ 2,
        Tendsto (fun T : ℝ => 2 / Real.pi * ∫ z : ℂ, g (ofComplex z) * h T z *
            ((fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z)) atTop
          (𝓝 (∑ s ∈ S, 2 * (n s : ℂ) / (Nat.card (MulAction.stabilizer Γ s) : ℂ) *
              ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g)) := by
  classical
  obtain ⟨V, b, m, F, hV1, hV2, hV3, hF, hm, hae⟩ :=
    ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex Γ hneg
      S n hn hcov hinj hdvd hdeg

  set Per : ℍ → ℂ → ℂ := fun s z => ∑ᶠ γ : Γ, F s (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
    conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) with hPer
  set dV : ℂ → ℂ := fun z => (fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z
    with hdV

  have hunf : ∀ (g : CuspForm Γ 2), ∀ s ∈ S,
      (∀ T : ℝ, Integrable fun z : ℂ => g (ofComplex z) * h T z * Per s z) ∧
      Tendsto (fun T : ℝ => ∫ z : ℂ, g (ofComplex z) * h T z * Per s z) atTop
        (𝓝 (∫ z : ℂ, g (ofComplex z) * F s z)) := by
    intro g s hs
    obtain ⟨hFc, hFcs, hFU, -⟩ := hF s hs
    exact ModularCurve.tendsto_integral_mul_smoothedFundamental_mul_finsum_translate Γ (F s)
      hFc hFcs hFU g (CuspFormClass.holo g).continuous (fun γ hγ τ => g_smul Γ g hγ τ) h hh

  have hh0 : ∀ T z, ¬ 0 < z.im → h T z = 0 := by
    intro T z hz
    rw [hh]
    have h3 := (ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one Γ T).2.2.1
    by_contra h'
    apply hz
    apply h3
    apply subset_tsupport
    rw [Function.mem_support]
    intro h0; apply h'; simp [h0]

  have hae' : ∀ (T : ℝ) (g : CuspForm Γ 2),
      (fun z : ℂ => g (ofComplex z) * h T z * dV z) =ᵐ[volume]
        fun z => ∑ s ∈ S, (m s : ℂ) / 2 * (g (ofComplex z) * h T z * Per s z) := by
    intro T g
    filter_upwards [hae] with z hz
    by_cases him : 0 < z.im
    · rw [hdV]; dsimp only
      rw [hz him, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    · simp [hh0 T z him]
  have hint : ∀ (T : ℝ) (g : CuspForm Γ 2),
      Integrable fun z => ∑ s ∈ S, (m s : ℂ) / 2 * (g (ofComplex z) * h T z * Per s z) := by
    intro T g
    exact integrable_finsetSum _ fun s hs => ((hunf g s hs).1 T).const_mul _
  refine ⟨V, hV1, hV2, hV3, fun T g => (hint T g).congr (hae' T g).symm, fun g => ?_⟩

  have heq : ∀ T : ℝ, ∫ z : ℂ, g (ofComplex z) * h T z * dV z =
      ∑ s ∈ S, (m s : ℂ) / 2 * ∫ z : ℂ, g (ofComplex z) * h T z * Per s z := by
    intro T
    rw [integral_congr_ae (hae' T g), integral_finsetSum _ fun s hs => ((hunf g s hs).1 T).const_mul _]
    exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
  have hlim : Tendsto (fun T : ℝ => 2 / Real.pi * ∫ z : ℂ, g (ofComplex z) * h T z * dV z) atTop
      (𝓝 (2 / Real.pi * ∑ s ∈ S, (m s : ℂ) / 2 * ∫ z : ℂ, g (ofComplex z) * F s z)) := by
    simp_rw [heq]
    exact (tendsto_finset_sum _ fun s hs => ((hunf g s hs).2).const_mul _).const_mul _

  have hpair : ∀ s ∈ S, ∫ z : ℂ, g (ofComplex z) * F s z = Real.pi * (Eg Γ g s - Eg Γ g b) := by
    intro s hs
    exact ((hF s hs).2.2.2 (Eg Γ g) (fun z => g (ofComplex z)) fun z hz => hasDerivAt_Eg Γ g hz).2
  have hm' : ∀ s ∈ S, (m s : ℂ) = 2 * (n s : ℂ) / (Nat.card (MulAction.stabilizer Γ s) : ℂ) := by
    intro s hs
    have hc : (Nat.card (MulAction.stabilizer Γ s) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer Γ s)).ne'
    have h := congrArg (fun k : ℤ => (k : ℂ)) (hm s hs)
    push_cast at h
    field_simp
    linear_combination h
  have hsum : ∑ s ∈ S, (m s : ℂ) = 0 := by
    rw [Finset.sum_congr rfl hm']
    have : ∑ s ∈ S, 2 * (n s : ℂ) / (Nat.card (MulAction.stabilizer Γ s) : ℂ) =
        2 * ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer Γ s) : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, hdeg, mul_zero]
  convert hlim using 2
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Finset.mul_sum]
  have : ∑ s ∈ S, 2 / (Real.pi : ℂ) * ((m s : ℂ) / 2 * ∫ z : ℂ, g (ofComplex z) * F s z) =
      ∑ s ∈ S, ((m s : ℂ) * Eg Γ g s - (m s : ℂ) * Eg Γ g b) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hpair s hs]; field_simp
  rw [this, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hm' s hs, Eg_coe]

end ModularCurve.DivisorTerm
p2m_reactivate "P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.ModularCurve P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.ModularCurve.DivisorTerm"
p2m_reactivate "P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.ModularCurve P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.ModularCurve.DivisorTerm"

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer Γ s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ)
    (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :
    ∃ V : ℂ → ℂ,
      (∀ (γ : Γ) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ (T : ℝ) (g : CuspForm Γ 2),
        Integrable fun z : ℂ => g (ofComplex z) * h T z *
          ((fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z)) ∧
      ∀ g : CuspForm Γ 2,
        Tendsto (fun T : ℝ => 2 / Real.pi * ∫ z : ℂ, g (ofComplex z) * h T z *
            ((fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z)) atTop
          (𝓝 (∑ s ∈ S, 2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer Γ s) : ℂ) *
              ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g)) :=
  ModularCurve.DivisorTerm.main hneg S n hn hcov hinj hdvd hdeg h hh

end S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
end P2MW
export P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf (solution)

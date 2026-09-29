-- Prove2me | solution 1 for ModularCurve.coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9b97801e-3740-5e8b-be63-a08c45b15379

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries
open scoped MatrixGroups ModularForm Manifold

namespace X1DegDiamond

local notation "GL↑(" Γ ")" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

class IsLevel (Γ : Subgroup SL(2, ℤ)) : Prop where
  T_mem : ModularGroup.T ∈ Γ

class Normalizes (Δ Γ : Subgroup SL(2, ℤ)) : Prop where
  conj_mem : ∀ ⦃γ A : SL(2, ℤ)⦄, γ ∈ Δ → A ∈ Γ → γ * A * γ⁻¹ ∈ Γ

section QExp

variable {Γ : Subgroup SL(2, ℤ)}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem one_mem_strictPeriods [IsLevel Γ] : (1 : ℝ) ∈ (GL↑(Γ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (IsLevel.T_mem (Γ := Γ))]
  exact AddSubgroup.mem_zmultiples 1

variable [IsLevel Γ]

theorem qC_mul {a b : ℤ} (f : ModularForm GL↑(Γ) a) (g : ModularForm GL↑(Γ) b) :
    qC ((⇑f : ℍ → ℂ) * ⇑g) = qC ⇑f * qC ⇑g := by
  rw [qC, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g, map_mul]
  rfl

theorem qC_coe_mul {a b : ℤ} (f : ModularForm GL↑(Γ) a) (g : ModularForm GL↑(Γ) b) :
    qC (⇑(f.mul g)) = qC ⇑f * qC ⇑g := by
  rw [ModularForm.coe_mul, qC_mul]

theorem qC_add {a : ℤ} (f g : ModularForm GL↑(Γ) a) :
    qC (⇑(f + g)) = qC ⇑f + qC ⇑g := by
  rw [ModularForm.coe_add, qC, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g,
    map_add]
  rfl

theorem qC_neg {a : ℤ} (f : ModularForm GL↑(Γ) a) : qC (⇑(-f)) = -qC ⇑f := by
  rw [ModularForm.coe_neg, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f,
    map_neg]
  rfl

theorem qC_smul {a : ℤ} (c : ℂ) (f : ModularForm GL↑(Γ) a) : qC (⇑(c • f)) = c • qC ⇑f := by
  rw [ModularForm.IsGLPos.coe_smul, qC,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f, qC,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by
  rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by
  rw [qC, qExpansion_one, map_one]

theorem qC_coe_zero {a : ℤ} : qC (⇑(0 : ModularForm GL↑(Γ) a)) = 0 := by
  rw [ModularForm.coe_zero]; exact qC_zero

theorem qC_coe_one : qC (⇑(1 : ModularForm GL↑(Γ) 0)) = 1 := by
  rw [ModularForm.one_coe_eq_one]; exact qC_one

variable [Γ.FiniteIndex]

theorem hasSum_qC {a : ℤ} (f : ModularForm GL↑(Γ) a) (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 (⇑f)).coeff m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods)
    f.holo' (ModularFormClass.bdd_at_infty f) τ

theorem coe_eq_of_qC_eq {a b : ℤ} (f : ModularForm GL↑(Γ) a) (g : ModularForm GL↑(Γ) b)
    (h : qC ⇑f = qC ⇑g) : (⇑f : ℍ → ℂ) = ⇑g := by
  have h' : qExpansion 1 (⇑f) = qExpansion 1 (⇑g) := HahnSeries.ofPowerSeries_injective h
  funext τ
  have hf := hasSum_qC f τ
  have hg := hasSum_qC g τ
  rw [h'] at hf
  exact hf.unique hg

theorem qC_eq_zero_iff {a : ℤ} (f : ModularForm GL↑(Γ) a) : qC ⇑f = 0 ↔ f = 0 := by
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f, qC]
  constructor
  · intro h
    exact HahnSeries.ofPowerSeries_injective (by rw [h, map_zero])
  · intro h; rw [h, map_zero]

end QExp

section Slash

variable {Γ Δ : Subgroup SL(2, ℤ)} {k : ℤ}

theorem isBoundedAt_slash [Γ.FiniteIndex] (f : ModularForm GL↑(Γ) k) (γ : SL(2, ℤ))
    {c : OnePoint ℝ} (hc : IsCusp c GL↑(Γ)) : IsBoundedAt c ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) k := by
  have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z GL↑(Γ)).mp hc
  have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) GL↑(Γ) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    exact hcSL.smul_of_mem ⟨γ, rfl⟩
  exact IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

def slashForm [Γ.FiniteIndex] [Normalizes Δ Γ] (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)
    (f : ModularForm GL↑(Γ) k) : ModularForm GL↑(Γ) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ Γ := Normalizes.conj_mem hγ hA
    have hGL : (γ : GL (Fin 2) ℝ) * (A : GL (Fin 2) ℝ)
        = ((γ * A * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) := by
      simp only [map_mul, map_inv, inv_mul_cancel_right]
    show ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (A : GL (Fin 2) ℝ)
      = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hconj)
  holo' := f.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    exact isBoundedAt_slash f γ hc

@[scoped simp] theorem coe_slashForm [Γ.FiniteIndex] [Normalizes Δ Γ] (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)
    (f : ModularForm GL↑(Γ) k) :
    (⇑(slashForm γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem coe_slashForm_SL [Γ.FiniteIndex] [Normalizes Δ Γ] (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)
    (f : ModularForm GL↑(Γ) k) :
    (⇑(slashForm γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [coe_slashForm, ModularForm.SL_slash]

theorem slash_inv_slash (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ⁻¹) ∣[k] γ = F := by
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

theorem slash_slash_inv (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ) ∣[k] γ⁻¹ = F := by
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem slashForm_ne_zero [Γ.FiniteIndex] [Normalizes Δ Γ] {γ : SL(2, ℤ)} (hγ : γ ∈ Δ)
    {f : ModularForm GL↑(Γ) k} (hf : f ≠ 0) : slashForm γ hγ f ≠ 0 := by
  intro h
  apply hf
  have h1 : (⇑(slashForm γ hγ f) : ℍ → ℂ) = 0 := by rw [h]; rfl
  rw [coe_slashForm_SL] at h1
  have h2 : (⇑f : ℍ → ℂ) = 0 := by
    rw [← slash_slash_inv (k := k) (⇑f) γ, h1, SlashAction.zero_slash]
  exact DFunLike.ext' (h2.trans ModularForm.coe_zero.symm)

end Slash

section Ratio

variable (Γ : Subgroup SL(2, ℤ)) {Δ : Subgroup SL(2, ℤ)} [IsLevel Γ] [Γ.FiniteIndex]

def IsRatio (x : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm GL↑(Γ) k), qC ⇑g ≠ 0 ∧ x = qC ⇑f / qC ⇑g

variable {Γ}

theorem isRatio_of_eq {k : ℤ} (f g : ModularForm GL↑(Γ) k) (hg : qC ⇑g ≠ 0) :
    IsRatio Γ (qC ⇑f / qC ⇑g) :=
  ⟨k, f, g, hg, rfl⟩

theorem qC_coe_one_ne_zero : qC (⇑(1 : ModularForm GL↑(Γ) 0)) ≠ 0 := by
  rw [qC_coe_one]; exact one_ne_zero

theorem isRatio_zero : IsRatio Γ 0 :=
  ⟨0, 0, 1, qC_coe_one_ne_zero, by rw [qC_coe_zero, zero_div]⟩

theorem isRatio_one : IsRatio Γ 1 :=
  ⟨0, 1, 1, qC_coe_one_ne_zero, by rw [qC_coe_one, div_one]⟩

theorem IsRatio.add {x y : LaurentSeries ℂ} (hx : IsRatio Γ x) (hy : IsRatio Γ y) :
    IsRatio Γ (x + y) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  obtain ⟨k', f', g', hg', rfl⟩ := hy
  refine ⟨k + k', f.mul g' + g.mul f', g.mul g', ?_, ?_⟩
  · rw [qC_coe_mul]; exact mul_ne_zero hg hg'
  · rw [qC_add, qC_coe_mul, qC_coe_mul, qC_coe_mul, div_add_div _ _ hg hg']

theorem IsRatio.neg {x : LaurentSeries ℂ} (hx : IsRatio Γ x) : IsRatio Γ (-x) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  exact ⟨k, -f, g, hg, by rw [qC_neg]; ring⟩

theorem IsRatio.mul {x y : LaurentSeries ℂ} (hx : IsRatio Γ x) (hy : IsRatio Γ y) :
    IsRatio Γ (x * y) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  obtain ⟨k', f', g', hg', rfl⟩ := hy
  refine ⟨k + k', f.mul f', g.mul g', ?_, ?_⟩
  · rw [qC_coe_mul]; exact mul_ne_zero hg hg'
  · rw [qC_coe_mul, qC_coe_mul, div_mul_div_comm]

theorem IsRatio.inv {x : LaurentSeries ℂ} (hx : IsRatio Γ x) : IsRatio Γ x⁻¹ := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  by_cases hf : qC ⇑f = 0
  · rw [hf, zero_div, inv_zero]; exact isRatio_zero
  · exact ⟨k, g, f, hf, by rw [inv_div]⟩

theorem isRatio_C (c : ℂ) : IsRatio Γ (HahnSeries.C c) := by
  refine ⟨0, c • (1 : ModularForm GL↑(Γ) 0), 1, qC_coe_one_ne_zero, ?_⟩
  rw [qC_smul, qC_coe_one, div_one, ← HahnSeries.C_mul_eq_smul, mul_one]

variable (Γ) in

def ratioField : Subfield (LaurentSeries ℂ) where
  carrier := {x | IsRatio Γ x}
  mul_mem' := IsRatio.mul
  one_mem' := isRatio_one
  add_mem' := IsRatio.add
  zero_mem' := isRatio_zero
  neg_mem' := IsRatio.neg
  inv_mem' _ := IsRatio.inv

variable [Normalizes Δ Γ]

theorem qC_slash_ne_zero (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) {k : ℤ} {g : ModularForm GL↑(Γ) k}
    (hg : qC ⇑g ≠ 0) : qC ((⇑g : ℍ → ℂ) ∣[k] γ) ≠ 0 := by
  rw [← coe_slashForm_SL γ hγ, Ne, qC_eq_zero_iff]
  exact slashForm_ne_zero hγ (fun h => hg ((qC_eq_zero_iff g).mpr h))

theorem cross (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) {k k' : ℤ} (f g : ModularForm GL↑(Γ) k)
    (f' g' : ModularForm GL↑(Γ) k') (hg : qC ⇑g ≠ 0) (hg' : qC ⇑g' ≠ 0)
    (h : qC ⇑f / qC ⇑g = qC ⇑f' / qC ⇑g') :
    qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ)
      = qC ((⇑f' : ℍ → ℂ) ∣[k'] γ) / qC ((⇑g' : ℍ → ℂ) ∣[k'] γ) := by
  rw [div_eq_div_iff hg hg'] at h
  have hfun : (⇑(f.mul g') : ℍ → ℂ) = ⇑(f'.mul g) := by
    apply coe_eq_of_qC_eq
    rw [qC_coe_mul, qC_coe_mul, h, mul_comm]
  rw [ModularForm.coe_mul, ModularForm.coe_mul] at hfun
  have hsl : ((⇑f : ℍ → ℂ) * ⇑g') ∣[k + k'] γ = ((⇑f' : ℍ → ℂ) * ⇑g) ∣[k' + k] γ := by
    rw [hfun, add_comm]
  rw [ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2] at hsl
  have hq : qC ((⇑f : ℍ → ℂ) ∣[k] γ) * qC ((⇑g' : ℍ → ℂ) ∣[k'] γ)
      = qC ((⇑f' : ℍ → ℂ) ∣[k'] γ) * qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    have := congrArg qC hsl
    rwa [← coe_slashForm_SL γ hγ f, ← coe_slashForm_SL γ hγ g',
      ← coe_slashForm_SL γ hγ f', ← coe_slashForm_SL γ hγ g, qC_mul, qC_mul,
      coe_slashForm_SL, coe_slashForm_SL, coe_slashForm_SL, coe_slashForm_SL] at this
  rw [div_eq_div_iff (qC_slash_ne_zero γ hγ hg) (qC_slash_ne_zero γ hγ hg')]
  exact hq

def pull (γ : SL(2, ℤ)) (x : ratioField Γ) : LaurentSeries ℂ :=
  qC ((⇑(x.2.choose_spec.choose) : ℍ → ℂ) ∣[x.2.choose] γ)
    / qC ((⇑(x.2.choose_spec.choose_spec.choose) : ℍ → ℂ) ∣[x.2.choose] γ)

theorem pull_eq (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x : ratioField Γ) {k : ℤ}
    (f g : ModularForm GL↑(Γ) k) (hg : qC ⇑g ≠ 0)
    (hx : (x : LaurentSeries ℂ) = qC ⇑f / qC ⇑g) :
    pull γ x = qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
  have hspec := x.2.choose_spec.choose_spec.choose_spec
  exact cross γ hγ _ _ f g hspec.1 hg (hspec.2.symm.trans hx)

theorem pull_one (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) : pull γ (1 : ratioField Γ) = 1 := by
  rw [pull_eq γ hγ 1 (1 : ModularForm GL↑(Γ) 0) 1 qC_coe_one_ne_zero
    (by rw [qC_coe_one, div_one]; rfl)]
  exact div_self (qC_slash_ne_zero γ hγ qC_coe_one_ne_zero)

theorem pull_zero (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) : pull γ (0 : ratioField Γ) = 0 := by
  rw [pull_eq γ hγ 0 (0 : ModularForm GL↑(Γ) 0) 1 qC_coe_one_ne_zero
    (by rw [qC_coe_zero, zero_div]; rfl), ModularForm.coe_zero, SlashAction.zero_slash, qC_zero,
    zero_div]

theorem pull_mul (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x y : ratioField Γ) :
    pull γ (x * y) = pull γ x * pull γ y := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  obtain ⟨k', f', g', hg', hy⟩ := y.2
  have hxy : ((x * y : ratioField Γ) : LaurentSeries ℂ) = qC ⇑(f.mul f') / qC ⇑(g.mul g') := by
    rw [Subfield.coe_mul, hx, hy, qC_coe_mul, qC_coe_mul, div_mul_div_comm]
  rw [pull_eq γ hγ x f g hg hx, pull_eq γ hγ y f' g' hg' hy,
    pull_eq γ hγ (x * y) (f.mul f') (g.mul g') (by rw [qC_coe_mul]; exact mul_ne_zero hg hg') hxy,
    ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2]
  rw [← coe_slashForm_SL γ hγ f, ← coe_slashForm_SL γ hγ f', ← coe_slashForm_SL γ hγ g,
    ← coe_slashForm_SL γ hγ g', qC_mul, qC_mul, div_mul_div_comm]

theorem pull_add (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x y : ratioField Γ) :
    pull γ (x + y) = pull γ x + pull γ y := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  obtain ⟨k', f', g', hg', hy⟩ := y.2
  have hxy : ((x + y : ratioField Γ) : LaurentSeries ℂ)
      = qC ⇑(f.mul g' + g.mul f') / qC ⇑(g.mul g') := by
    rw [Subfield.coe_add, hx, hy, qC_add, qC_coe_mul, qC_coe_mul, qC_coe_mul,
      div_add_div _ _ hg hg']
  rw [pull_eq γ hγ x f g hg hx, pull_eq γ hγ y f' g' hg' hy,
    pull_eq γ hγ (x + y) _ (g.mul g') (by rw [qC_coe_mul]; exact mul_ne_zero hg hg') hxy,
    ModularForm.coe_add, SlashAction.add_slash, ModularForm.coe_mul, ModularForm.coe_mul,
    ModularForm.coe_mul, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2,
    ModularForm.mul_slash_SL2]
  have e1 : qC ((⇑f : ℍ → ℂ) ∣[k] γ * (⇑g' : ℍ → ℂ) ∣[k'] γ
        + (⇑g : ℍ → ℂ) ∣[k] γ * (⇑f' : ℍ → ℂ) ∣[k'] γ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ) * qC ((⇑g' : ℍ → ℂ) ∣[k'] γ)
        + qC ((⇑g : ℍ → ℂ) ∣[k] γ) * qC ((⇑f' : ℍ → ℂ) ∣[k'] γ) := by
    rw [← coe_slashForm_SL γ hγ f, ← coe_slashForm_SL γ hγ f', ← coe_slashForm_SL γ hγ g,
      ← coe_slashForm_SL γ hγ g', ← ModularForm.coe_mul, ← ModularForm.coe_mul,
      ← ModularForm.coe_add, qC_add, qC_coe_mul, qC_coe_mul]
  have e2 : qC ((⇑g : ℍ → ℂ) ∣[k] γ * (⇑g' : ℍ → ℂ) ∣[k'] γ)
      = qC ((⇑g : ℍ → ℂ) ∣[k] γ) * qC ((⇑g' : ℍ → ℂ) ∣[k'] γ) := by
    rw [← coe_slashForm_SL γ hγ g, ← coe_slashForm_SL γ hγ g', qC_mul]
  rw [e1, e2, div_add_div _ _ (qC_slash_ne_zero γ hγ hg) (qC_slash_ne_zero γ hγ hg')]

def pullHom (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) : ratioField Γ →+* LaurentSeries ℂ where
  toFun := pull γ
  map_one' := pull_one γ hγ
  map_mul' := pull_mul γ hγ
  map_zero' := pull_zero γ hγ
  map_add' := pull_add γ hγ

theorem pull_mem (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x : ratioField Γ) : pull γ x ∈ ratioField Γ := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  rw [pull_eq γ hγ x f g hg hx, ← coe_slashForm_SL γ hγ f, ← coe_slashForm_SL γ hγ g]
  exact isRatio_of_eq _ _ (by rw [coe_slashForm_SL]; exact qC_slash_ne_zero γ hγ hg)

theorem pull_pull_inv (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x : ratioField Γ) :
    pull γ ⟨pull γ⁻¹ x, pull_mem γ⁻¹ (inv_mem hγ) x⟩ = x := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  have hg' : qC (⇑(slashForm γ⁻¹ (inv_mem hγ) g)) ≠ 0 := by
    rw [coe_slashForm_SL]; exact qC_slash_ne_zero γ⁻¹ (inv_mem hγ) hg
  rw [pull_eq γ hγ _ (slashForm γ⁻¹ (inv_mem hγ) f) (slashForm γ⁻¹ (inv_mem hγ) g) hg'
    (by rw [coe_slashForm_SL, coe_slashForm_SL]; exact pull_eq γ⁻¹ (inv_mem hγ) x f g hg hx),
    coe_slashForm_SL, coe_slashForm_SL, slash_inv_slash, slash_inv_slash, hx]

end Ratio

section Rational

open ModularCurve IntermediateField

variable {Γ Δ : Subgroup SL(2, ℤ)}

abbrev toC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem toC_injective : Function.Injective toC := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact (algebraMap ℚ ℂ).injective this

theorem toC_intSeriesC {f : ℍ → ℂ} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) : toC (intSeriesC ℚ p) = qC f := by
  ext n
  rw [coeffMap_coeff, intSeriesC, qC, ← hp, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · exact map_zero _
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

theorem toC_ratio {f g : ℍ → ℂ} {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    toC (intSeriesC ℚ pf / intSeriesC ℚ pg) = qC f / qC g := by
  rw [map_div₀, toC_intSeriesC hf, toC_intSeriesC hg]

theorem qC_ne_zero_of_intSeriesC_ne_zero {g : ℍ → ℂ} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← toC_intSeriesC hg]
  exact fun h => hg0 (toC_injective (by rw [h, map_zero]))

theorem toC_algebraMap (c : ℚ) :
    toC (algebraMap ℚ (LaurentSeries ℚ) c) = HahnSeries.C (algebraMap ℚ ℂ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

variable [IsLevel Γ] [Γ.FiniteIndex]

theorem toC_mem_ratioField {x : LaurentSeries ℚ}
    (hx : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ)) :
    toC x ∈ ratioField Γ := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      rw [toC_ratio hf hg]
      exact isRatio_of_eq f g (qC_ne_zero_of_intSeriesC_ne_zero hg hg0)
  | algebraMap c => rw [toC_algebraMap]; exact isRatio_C _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

def iota : qExpFunctionFieldC ℚ Γ →+* ratioField Γ :=
  (toC.comp (algebraMap (qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ))).codRestrict (ratioField Γ)
    (fun x => toC_mem_ratioField x.2)

@[scoped simp] theorem coe_iota (x : qExpFunctionFieldC ℚ Γ) :
    ((iota x : ratioField Γ) : LaurentSeries ℂ) = toC x :=
  rfl

def jC : qExpFunctionFieldC ℚ Γ →+* LaurentSeries ℂ :=
  toC.comp (algebraMap (qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ))

theorem jC_apply (x : qExpFunctionFieldC ℚ Γ) : jC x = toC x := rfl

theorem jC_injective : Function.Injective (jC (Γ := Γ)) :=
  toC_injective.comp Subtype.val_injective

variable (Γ Δ) in

def RationalSlash : Prop :=
  ∀ (k : ℤ) (f : ModularForm GL↑(Γ) k) (p : PowerSeries ℤ), IsIntegralQExp f p → ∀ γ ∈ Δ,
    ∃ (D : ℤ) (f₁ : ModularForm GL↑(Γ) k) (p₁ : PowerSeries ℤ), D ≠ 0 ∧ IsIntegralQExp f₁ p₁ ∧
      (⇑f₁ : ℍ → ℂ) = (D : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] γ)

variable [Normalizes Δ Γ] (hR : RationalSlash Γ Δ) (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)

def psi : qExpFunctionFieldC ℚ Γ →+* LaurentSeries ℂ :=
  (pullHom γ hγ).comp iota

theorem psi_apply (x : qExpFunctionFieldC ℚ Γ) : psi γ hγ x = pull γ (iota x) := rfl

include hR in

theorem exists_psi_generator_eq {k : ℤ} (f g : ModularForm GL↑(Γ) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ y : qExpFunctionFieldC ℚ Γ,
      psi γ hγ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
        = toC y := by
  have hqg : qC ⇑g ≠ 0 := qC_ne_zero_of_intSeriesC_ne_zero hg hg0
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ := hR k f pf hf γ hγ
  obtain ⟨D', g₁, p₁', hD', hp₁', hg₁⟩ := hR k g pg hg γ hγ
  have hqf₁ : qC ⇑f₁ = (D : ℂ) • qC ((⇑f : ℍ → ℂ) ∣[k] γ) := by
    have : (⇑f₁ : ℍ → ℂ) = ⇑((D : ℂ) • slashForm γ hγ f) := by
      rw [hf₁, ModularForm.IsGLPos.coe_smul, coe_slashForm_SL]
    rw [this, qC_smul, coe_slashForm_SL]
  have hqg₁ : qC ⇑g₁ = (D' : ℂ) • qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    have : (⇑g₁ : ℍ → ℂ) = ⇑((D' : ℂ) • slashForm γ hγ g) := by
      rw [hg₁, ModularForm.IsGLPos.coe_smul, coe_slashForm_SL]
    rw [this, qC_smul, coe_slashForm_SL]
  have hF : IsIntegralQExp (⇑(((D' : ℤ) : ℂ) • f₁)) (PowerSeries.C (D' : ℤ) * p₁) := by
    unfold IsIntegralQExp at hp₁ ⊢
    rw [map_mul, PowerSeries.map_C, hp₁, ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods _ f₁, PowerSeries.smul_eq_C_mul,
      eq_intCast]
  have hG : IsIntegralQExp (⇑(((D : ℤ) : ℂ) • g₁)) (PowerSeries.C (D : ℤ) * p₁') := by
    unfold IsIntegralQExp at hp₁' ⊢
    rw [map_mul, PowerSeries.map_C, hp₁', ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods _ g₁, PowerSeries.smul_eq_C_mul,
      eq_intCast]
  have hqG : qC (⇑(((D : ℤ) : ℂ) • g₁)) = ((D : ℂ) * D') • qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    rw [qC_smul, hqg₁, smul_smul]
  have hqF : qC (⇑(((D' : ℤ) : ℂ) • f₁)) = ((D' : ℂ) * D) • qC ((⇑f : ℍ → ℂ) ∣[k] γ) := by
    rw [qC_smul, hqf₁, smul_smul]
  have hG0 : intSeriesC ℚ (PowerSeries.C (D : ℤ) * p₁') ≠ 0 := by
    intro h0
    have h1 : qC (⇑(((D : ℤ) : ℂ) • g₁)) = 0 := by rw [← toC_intSeriesC hG, h0, map_zero]
    rw [hqG, ← HahnSeries.C_mul_eq_smul, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact HahnSeries.C_ne_zero
        (mul_ne_zero (Int.cast_ne_zero.mpr hD) (Int.cast_ne_zero.mpr hD')) h1
    · exact qC_slash_ne_zero γ hγ hqg h1
  refine ⟨⟨intSeriesC ℚ (PowerSeries.C (D' : ℤ) * p₁) / intSeriesC ℚ (PowerSeries.C (D : ℤ) * p₁'),
    div_mem_qExpFunctionFieldC _ _ hF hG hG0⟩, ?_⟩
  rw [psi_apply, pull_eq γ hγ _ f g hqg (by rw [coe_iota]; exact toC_ratio hf hg)]
  show _ = toC (intSeriesC ℚ (PowerSeries.C (D' : ℤ) * p₁)
    / intSeriesC ℚ (PowerSeries.C (D : ℤ) * p₁'))
  rw [toC_ratio hF hG, hqF, hqG, mul_comm (D' : ℂ) (D : ℂ), ← HahnSeries.C_mul_eq_smul,
    ← HahnSeries.C_mul_eq_smul, mul_div_mul_left _ _ ?_]
  exact HahnSeries.C_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hD) (Int.cast_ne_zero.mpr hD'))

include hR in

theorem exists_psi_eq (x : qExpFunctionFieldC ℚ Γ) :
    ∃ y : qExpFunctionFieldC ℚ Γ, psi γ hγ x = toC y := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ) := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      exact exists_psi_generator_eq hR γ hγ f g hf hg hg0
  | algebraMap c =>
      refine ⟨⟨algebraMap ℚ (LaurentSeries ℚ) c, IntermediateField.algebraMap_mem _ c⟩, ?_⟩
      let j₁ : ℚ →+* qExpFunctionFieldC ℚ Γ := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
        (qExpFunctionFieldC ℚ Γ) (fun c => IntermediateField.algebraMap_mem _ c)
      exact RingHom.congr_fun
        (Subsingleton.elim ((psi γ hγ).comp j₁) (toC.comp (algebraMap ℚ (LaurentSeries ℚ)))) c
  | add y z hy hz ihy ihz =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      obtain ⟨z₁, hz₁⟩ := ihz hz
      refine ⟨y₁ + z₁, ?_⟩
      have : (⟨y + z, add_mem hy hz⟩ : qExpFunctionFieldC ℚ Γ) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, hy₁, hz₁, ← map_add]
      rfl
  | inv y hy ihy =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      refine ⟨y₁⁻¹, ?_⟩
      have : (⟨y⁻¹, inv_mem hy⟩ : qExpFunctionFieldC ℚ Γ) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, hy₁, ← map_inv₀]
      rfl
  | mul y z hy hz ihy ihz =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      obtain ⟨z₁, hz₁⟩ := ihz hz
      refine ⟨y₁ * z₁, ?_⟩
      have : (⟨y * z, mul_mem hy hz⟩ : qExpFunctionFieldC ℚ Γ) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, hy₁, hz₁, ← map_mul]
      rfl

include hR in
theorem psi_mem_range (x : qExpFunctionFieldC ℚ Γ) : psi γ hγ x ∈ (jC (Γ := Γ)).range := by
  obtain ⟨y, hy⟩ := exists_psi_eq hR γ hγ x
  exact ⟨y, hy.symm⟩

def eC : qExpFunctionFieldC ℚ Γ ≃+* (jC (Γ := Γ)).range :=
  RingEquiv.ofBijective (jC (Γ := Γ)).rangeRestrict
    ⟨fun x y h => jC_injective (by
        have := congrArg (fun z : (jC (Γ := Γ)).range => (z : LaurentSeries ℂ)) h
        simpa only [RingHom.coe_rangeRestrict] using this),
      RingHom.rangeRestrict_surjective _⟩

theorem jC_eC_symm (z : (jC (Γ := Γ)).range) :
    jC ((eC (Γ := Γ)).symm z) = (z : LaurentSeries ℂ) := by
  conv_rhs => rw [← (eC (Γ := Γ)).apply_symm_apply z]
  rfl

def sigma0 : qExpFunctionFieldC ℚ Γ →+* qExpFunctionFieldC ℚ Γ :=
  (eC (Γ := Γ)).symm.toRingHom.comp
    ((psi γ hγ).codRestrict (jC (Γ := Γ)).range (psi_mem_range hR γ hγ))

theorem jC_sigma0 (x : qExpFunctionFieldC ℚ Γ) : jC (sigma0 hR γ hγ x) = psi γ hγ x := by
  show jC ((eC (Γ := Γ)).symm _) = _
  rw [jC_eC_symm]
  rfl

theorem sigma0_injective : Function.Injective (sigma0 hR γ hγ) := by
  intro x y h
  have h1 : psi γ hγ x = psi γ hγ y := by rw [← jC_sigma0 hR, ← jC_sigma0 hR, h]
  exact (psi γ hγ).injective h1

theorem sigma0_surjective : Function.Surjective (sigma0 hR γ hγ) := by
  intro x
  refine ⟨sigma0 hR γ⁻¹ (inv_mem hγ) x, jC_injective ?_⟩
  rw [jC_sigma0, psi_apply]
  have hι : iota (sigma0 hR γ⁻¹ (inv_mem hγ) x)
      = ⟨pull γ⁻¹ (iota x), pull_mem γ⁻¹ (inv_mem hγ) (iota x)⟩ := by
    apply Subtype.ext
    show jC (sigma0 hR γ⁻¹ (inv_mem hγ) x) = pull γ⁻¹ (iota x)
    rw [jC_sigma0, psi_apply]
  rw [hι, pull_pull_inv γ hγ]
  rfl

def sigma : qExpFunctionFieldC ℚ Γ ≃+* qExpFunctionFieldC ℚ Γ :=
  RingEquiv.ofBijective (sigma0 hR γ hγ) ⟨sigma0_injective hR γ hγ, sigma0_surjective hR γ hγ⟩

theorem sigma_apply (x : qExpFunctionFieldC ℚ Γ) : sigma hR γ hγ x = sigma0 hR γ hγ x := rfl

theorem toC_sigma (x : qExpFunctionFieldC ℚ Γ) :
    toC ((sigma hR γ hγ x : qExpFunctionFieldC ℚ Γ) : LaurentSeries ℚ) = pull γ (iota x) := by
  rw [sigma_apply, ← jC_apply, jC_sigma0, psi_apply]

theorem toC_sigma_generator {k : ℤ} (f g : ModularForm GL↑(Γ) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    toC ((sigma hR γ hγ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
        qExpFunctionFieldC ℚ Γ) : LaurentSeries ℚ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
  rw [toC_sigma,
    pull_eq γ hγ _ f g (qC_ne_zero_of_intSeriesC_ne_zero hg hg0) (by rw [coe_iota]; exact toC_ratio hf hg)]

end Rational

section StretchPiece

variable {ℓ : ℕ}

private theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem heckeDiagMatrix_mul_eq (hℓ : ℓ ≠ 0) {γ γ₁ : SL(2, ℤ)}
    (h00 : γ₁ 0 0 = γ 0 0) (h01 : γ₁ 0 1 = (ℓ : ℤ) * γ 0 1)
    (h10 : (ℓ : ℤ) * γ₁ 1 0 = γ 1 0) (h11 : γ₁ 1 1 = γ 1 1) :
    heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.mapGL ℝ γ₁ * heckeDiagMatrix ℓ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, mapGL_coe_eq, mapGL_coe_eq, val_heckeDiagMatrix hℓ]
  have e10 : ((γ 1 0 : ℤ) : ℝ) = (ℓ : ℝ) * ((γ₁ 1 0 : ℤ) : ℝ) := by
    rw [← h10]; push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h11, e10, mul_comm]

end StretchPiece

section Level

open ModularCurve IntermediateField

theorem conj_mem_Gamma1 {M : ℕ} {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ Gamma1 M) :
    γ * A * γ⁻¹ ∈ Gamma1 M := by
  have hA0 : A ∈ Gamma0 M := Gamma1_in_Gamma0 M hA
  set A₀ : Gamma0 M := ⟨A, hA0⟩
  set γ₀ : Gamma0 M := ⟨γ, hγ⟩
  have hA1 : A₀ ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M A).mp hA
  haveI : (Gamma1' M).Normal := by
    show ((Gamma0Map M).ker).Normal
    infer_instance
  have hconj : γ₀ * A₀ * γ₀⁻¹ ∈ Gamma1' M := Subgroup.Normal.conj_mem inferInstance A₀ hA1 γ₀
  rw [Gamma1_to_Gamma0_mem] at hconj
  rw [Gamma1_mem]
  exact hconj

theorem Gamma0_le_of_dvd {N N' : ℕ} (h : N ∣ N') : Gamma0 N' ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom h (ZMod N)) hA
  rwa [map_intCast, map_zero] at this

scoped instance isLevel_Gamma1 (M : ℕ) : IsLevel (Gamma1 M) :=
  ⟨by simp [Gamma1_mem, ModularGroup.T]⟩

scoped instance normalizes_Gamma0_Gamma1 (M : ℕ) : Normalizes (Gamma0 M) (Gamma1 M) :=
  ⟨fun _ _ hγ hA => conj_mem_Gamma1 hγ hA⟩

theorem cocycle_level {N N' t : ℕ} [NeZero t] (h : N * t ∣ N') :
    ∀ γ ∈ Gamma1 N', ∃ γ₁ ∈ Gamma1 N,
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (t : ℤ) * γ 0 1 ∧ (t : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  have hγ' := (Gamma1_mem N' γ).mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  obtain ⟨r, hr⟩ := h
  have hN'c : ((N' : ℕ) : ℤ) ∣ γ 1 0 := by
    have := hγ'.2.2; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hN'c
  rw [hr, Nat.cast_mul, Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (t : ℤ) * γ 0 1; (N : ℤ) * (r * c'), γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  have hNN' : N ∣ N' := ⟨t * r, by rw [hr]; ring⟩
  refine ⟨⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma1_mem]
    obtain ⟨h00, h11, -⟩ := hγ'
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (ZMod.castHom hNN' (ZMod N)) h00
      rw [map_intCast, map_one] at this
      exact this
    · have := congrArg (ZMod.castHom hNN' (ZMod N)) h11
      rw [map_intCast, map_one] at this
      exact this
    · show (((N : ℤ) * (r * c') : ℤ) : ZMod N) = 0
      push_cast; rw [ZMod.natCast_self, zero_mul]
  · rfl
  · rfl
  · show (t : ℤ) * ((N : ℤ) * (r * c')) = γ 1 0
    linear_combination -hc'
  · rfl

theorem exists_gammas_level {N N' t : ℕ} [NeZero t] (h : N * t ∣ N') {d : ℕ} (hd : d.Coprime N') :
    ∃ γ γ' : SL(2, ℤ), γ ∈ Gamma0 N' ∧ γ' ∈ Gamma0 N ∧
      ((γ 0 0 : ℤ) : ZMod N') = d ∧ ((γ' 0 0 : ℤ) : ZMod N) = d ∧
      heckeDiagMatrix t * Matrix.SpecialLinearGroup.mapGL ℝ γ
        = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix t := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hd
  obtain ⟨r, hr⟩ := h
  have hdet : Matrix.det !![(d : ℤ), -v; (N' : ℤ), u] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination huv
  have hdet' : Matrix.det !![(d : ℤ), -(v * t); (N : ℤ) * r, u] = 1 := by
    rw [Matrix.det_fin_two_of]
    have hN' : (N' : ℤ) = (N : ℤ) * t * r := by rw [hr]; push_cast; ring
    linear_combination huv - (v : ℤ) * hN'
  refine ⟨⟨_, hdet⟩, ⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma0_mem]
    show (((N' : ℤ)) : ZMod N') = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  · rw [Gamma0_mem]
    show ((((N : ℤ) * r : ℤ)) : ZMod N) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]
  · show (((d : ℤ)) : ZMod N') = (d : ZMod N')
    rw [Int.cast_natCast]
  · show (((d : ℤ)) : ZMod N) = (d : ZMod N)
    rw [Int.cast_natCast]
  · refine heckeDiagMatrix_mul_eq (NeZero.ne t) rfl ?_ ?_ rfl
    · show -((v : ℤ) * t) = (t : ℤ) * (-v)
      ring
    · show (t : ℤ) * ((N : ℤ) * r) = (N' : ℤ)
      rw [hr]; push_cast; ring

theorem toC_qExpand (ℓ : ℕ) [NeZero ℓ] (x : LaurentSeries ℚ) :
    toC (qExpand ℚ ℓ x) = qExpand ℂ ℓ (toC x) := by
  ext n
  by_cases hn : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [coeffMap_coeff, ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hn,
      ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hn, map_zero]

theorem ringHom_ext_adjoin {S : Set (LaurentSeries ℚ)} {R : Type*} [DivisionRing R]
    (φ ψ : IntermediateField.adjoin ℚ S →+* R)
    (h : ∀ (x : LaurentSeries ℚ) (hx : x ∈ S),
      φ ⟨x, IntermediateField.subset_adjoin ℚ S hx⟩ = ψ ⟨x, IntermediateField.subset_adjoin ℚ S hx⟩) :
    φ = ψ := by
  refine RingHom.ext fun x => ?_
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact h y hy
  | algebraMap c =>
      let j₁ : ℚ →+* IntermediateField.adjoin ℚ S := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
        (IntermediateField.adjoin ℚ S) (fun c => IntermediateField.algebraMap_mem _ c)
      exact RingHom.congr_fun (Subsingleton.elim (φ.comp j₁) (ψ.comp j₁)) c
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz]

abbrev FB (M : ℕ) : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gamma1 M)

theorem FB_le_of_dvd {N N' : ℕ} (h : N ∣ N') : FB N ≤ FB N' :=
  x1FunctionFieldC_le_of_dvd ℚ h

section Genuine

variable {N N' : ℕ} [NeZero N] [NeZero N'] {d : ℕ}
  {σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N} (hσ : IsDiamondAut N d σ)
  {σ' : x1FunctionField N' ≃ₐ[ℚ] x1FunctionField N'} (hσ' : IsDiamondAut N' d σ')

theorem toC_diamond_generator {M : ℕ} [NeZero M] {e : ℕ}
    {σ₀ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M} (hσ₀ : IsDiamondAut M e σ₀)
    {γ₀ : SL(2, ℤ)} (hγ₀ : γ₀ ∈ Gamma0 M)
    (hγ₀d : ((γ₀ 0 0 : ℤ) : ZMod M) = e) {k : ℤ}
    (f g : ModularForm GL↑(Gamma1 M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    toC ((σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
        x1FunctionField M) : LaurentSeries ℚ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ₀) / qC ((⇑g : ℍ → ℂ) ∣[k] γ₀) := by
  have H := hσ₀.2 k f g pf pg hf hg hg0 γ₀ hγ₀ hγ₀d
  rw [eq_div_iff (qC_slash_ne_zero (Γ := Gamma1 M) γ₀ hγ₀ (qC_ne_zero_of_intSeriesC_ne_zero hg hg0))]
  exact H

variable {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N') (hγd : ((γ 0 0 : ℤ) : ZMod N') = d)

include hσ hσ' hγ hγd in

theorem incl_generator (h : N ∣ N') {k : ℤ} (f g : ModularForm GL↑(Gamma1 N) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((σ' ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, FB_le_of_dvd h (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          x1FunctionField N') : LaurentSeries ℚ)
      = ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
          x1FunctionField N) : LaurentSeries ℚ) := by
  apply toC_injective
  have hle' : GL↑(Gamma1 N') ≤ GL↑(Gamma1 N) := Subgroup.map_mono (Gamma1_le_of_dvd h)
  have hf' : IsIntegralQExp (restrictForm hle' f) pf := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hf
  have hg' : IsIntegralQExp (restrictForm hle' g) pg := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hg
  have hγN : γ ∈ Gamma0 N := Gamma0_le_of_dvd h hγ
  have hγdN : ((γ 0 0 : ℤ) : ZMod N) = d := by
    have := congrArg (ZMod.castHom h (ZMod N)) hγd
    rwa [map_intCast, map_natCast] at this
  have e : (⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
        FB_le_of_dvd h (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : x1FunctionField N')
      = ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC _ _ hf' hg' hg0⟩ := rfl
  rw [e, toC_diamond_generator hσ' hγ hγd (restrictForm hle' f) (restrictForm hle' g) hf' hg' hg0,
    coe_restrictForm, coe_restrictForm, toC_diamond_generator hσ hγN hγdN f g hf hg hg0]

include hσ hσ' hγ hγd in

theorem incl_all (h : N ∣ N') (y : LaurentSeries ℚ) (hy : y ∈ FB N) :
    ((σ' ⟨y, FB_le_of_dvd h hy⟩ : x1FunctionField N') : LaurentSeries ℚ)
      = ((σ ⟨y, hy⟩ : x1FunctionField N) : LaurentSeries ℚ) := by
  let incl : FB N →+* FB N' :=
    (algebraMap (FB N) (LaurentSeries ℚ)).codRestrict (FB N') (fun z => FB_le_of_dvd h z.2)
  let φ : FB N →+* LaurentSeries ℚ :=
    (algebraMap (FB N') (LaurentSeries ℚ)).comp (σ'.toRingEquiv.toRingHom.comp incl)
  let ψ : FB N →+* LaurentSeries ℚ :=
    (algebraMap (FB N) (LaurentSeries ℚ)).comp σ.toRingEquiv.toRingHom
  have H : φ = ψ := by
    refine ringHom_ext_adjoin φ ψ ?_
    intro x hx
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
    exact incl_generator hσ hσ' hγ hγd h f g hf hg hg0
  exact RingHom.congr_fun H ⟨y, hy⟩

end Genuine

end Level

section BaseChange

open ModularCurve IntermediateField AlgebraicCurve

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (ℓ : ℕ) [NeZero ℓ]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ ℓ x) = qExpand L ℓ (coeffEmb L x) := by
  ext n
  by_cases hn : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [coeffEmb_coeff, ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hn,
      ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hn, map_zero]

local notation "ℚbar" => AlgebraicClosure ℚ

theorem isBaseChangeAutOf_diamondAutBar (M d : ℕ) :
    IsBaseChangeAutOf ℚbar (diamondAut M d) (diamondAutBar M d) := by
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover ℚbar
    (x1FunctionField M) (diamondAut M d).toRingEquiv
  exact isBaseChangeAutOf_baseChangeAut ⟨τ, fun y => hτ y⟩

end BaseChange

section TransportDia

open ModularCurve IntermediateField AlgebraicCurve

local notation "ℚbar" => AlgebraicClosure ℚ

scoped instance finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

scoped instance isLevel_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : IsLevel (CohCarrier.GammaH M H) :=
  ⟨ModularCurve.translation_mem_GammaH M H⟩

scoped instance normalizes_Gamma0_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Normalizes (Gamma0 M) (CohCarrier.GammaH M H) :=
  ⟨fun γ _ hγ hA => CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨_, hA⟩⟩

abbrev FH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : IntermediateField ℚ (LaurentSeries ℚ) :=
  qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)

theorem FH_le_FB (M : ℕ) (H : Subgroup (ZMod M)ˣ) : FH M H ≤ FB M :=
  qExpFunctionFieldC_mono ℚ (ModularCurve.Gamma1_le_GammaH M H)

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {d : ℕ}

theorem toC_diamondH_generator {dH : (ZMod M)ˣ}
    {σH : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H} (hσH : IsDiamondAutHBar M H dH σH)
    {γ₀ : SL(2, ℤ)} (hγ₀ : γ₀ ∈ Gamma0 M) (hγ₀d : ((γ₀ 0 0 : ℤ) : ZMod M) = (dH : ZMod M)) {k : ℤ}
    (f g : ModularForm GL↑(CohCarrier.GammaH M H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ y : LaurentSeries ℚ, y ∈ FH M H ∧
      ((σH ⟨coeffEmb ℚbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
            coeffEmb_mem_laurentBaseChange ℚbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y ∧
      toC y = qC ((⇑f : ℍ → ℂ) ∣[k] γ₀) / qC ((⇑g : ℍ → ℂ) ∣[k] γ₀) := by
  obtain ⟨y, hy, hσ, hprod⟩ := hσH k f g pf pg hf hg hg0 γ₀ hγ₀ hγ₀d
  refine ⟨y, hy, hσ, ?_⟩
  rw [eq_div_iff (qC_slash_ne_zero (Γ := CohCarrier.GammaH M H) γ₀ hγ₀ (qC_ne_zero_of_intSeriesC_ne_zero hg hg0))]

  have e1 : qC ((⇑g : ℍ → ℂ) ∣[k] γ₀) = qC ((⇑g : ℍ → ℂ) ∣[k] (γ₀ : GL (Fin 2) ℝ)) := by rw [ModularForm.SL_slash]
  have e2 : qC ((⇑f : ℍ → ℂ) ∣[k] γ₀) = qC ((⇑f : ℍ → ℂ) ∣[k] (γ₀ : GL (Fin 2) ℝ)) := by rw [ModularForm.SL_slash]
  rw [e1, e2]
  exact hprod

theorem transport_generator {dH : (ZMod M)ˣ}
    {σH : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H} (hσH : IsDiamondAutHBar M H dH σH)
    {σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M} (hσ : IsDiamondAut M d σ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγd : ((γ 0 0 : ℤ) : ZMod M) = d) (hdH : (dH : ZMod M) = d)
    {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((σH ⟨coeffEmb ℚbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
            coeffEmb_mem_laurentBaseChange ℚbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          xHFunctionFieldBar M H) : LaurentSeries ℚbar)
      = coeffEmb ℚbar ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            FH_le_FB M H (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : x1FunctionField M) : LaurentSeries ℚ) := by
  obtain ⟨y, -, hσy, hy⟩ := toC_diamondH_generator hσH hγ (hγd.trans hdH.symm) f g hf hg hg0
  rw [hσy]
  congr 1
  apply toC_injective
  have hle : GL↑(Gamma1 M) ≤ GL↑(CohCarrier.GammaH M H) := Subgroup.map_mono (ModularCurve.Gamma1_le_GammaH M H)
  have hf' : IsIntegralQExp (restrictForm hle f) pf := by rw [IsIntegralQExp, coe_restrictForm]; exact hf
  have hg' : IsIntegralQExp (restrictForm hle g) pg := by rw [IsIntegralQExp, coe_restrictForm]; exact hg
  have e : (⟨intSeriesC ℚ pf / intSeriesC ℚ pg, FH_le_FB M H (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : x1FunctionField M)
      = ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC _ _ hf' hg' hg0⟩ := rfl
  rw [hy, e, toC_diamond_generator hσ hγ hγd (restrictForm hle f) (restrictForm hle g) hf' hg' hg0,
    coe_restrictForm, coe_restrictForm]

theorem transport_all {dH : (ZMod M)ˣ}
    {σH : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H} (hσH : IsDiamondAutHBar M H dH σH)
    {σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M} (hσ : IsDiamondAut M d σ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγd : ((γ 0 0 : ℤ) : ZMod M) = d) (hdH : (dH : ZMod M) = d)
    (y : LaurentSeries ℚ) (hy : y ∈ FH M H) :
    ((σH ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩ : xHFunctionFieldBar M H) : LaurentSeries ℚbar)
      = coeffEmb ℚbar ((σ ⟨y, FH_le_FB M H hy⟩ : x1FunctionField M) : LaurentSeries ℚ) := by

  let inclBar : FH M H →+* xHFunctionFieldBar M H :=
    { toFun := fun z => ⟨coeffEmb ℚbar (z : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚbar z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let φ : FH M H →+* LaurentSeries ℚbar :=
    (algebraMap (xHFunctionFieldBar M H) (LaurentSeries ℚbar)).comp (σH.toRingEquiv.toRingHom.comp inclBar)
  let incl : FH M H →+* FB M :=
    (algebraMap (FH M H) (LaurentSeries ℚ)).codRestrict (FB M) (fun z => FH_le_FB M H z.2)
  let ψ : FH M H →+* LaurentSeries ℚbar :=
    (coeffEmb ℚbar).comp ((algebraMap (FB M) (LaurentSeries ℚ)).comp (σ.toRingEquiv.toRingHom.comp incl))
  have Hφψ : φ = ψ := by
    refine ringHom_ext_adjoin φ ψ ?_
    intro x hx
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
    exact transport_generator hσH hσ hγ hγd hdH f g hf hg hg0
  exact RingHom.congr_fun Hφψ ⟨y, hy⟩

theorem comp_diamondAutHBar_eq (hin : HeckeDiamondInputsAll M)
    (ι : xHFunctionFieldBar M H →ₐ[ℚbar] x1FunctionFieldBar M)
    (hι : ∀ x, ((ι x : x1FunctionFieldBar M) : LaurentSeries ℚbar) = (x : LaurentSeries ℚbar))
    (hd : Nat.Coprime d M) :
    ι.comp (diamondAutHBar M H (ZMod.unitOfCoprime d hd) : xHFunctionFieldBar M H →ₐ[ℚbar] xHFunctionFieldBar M H)
      = (diamondAutBar M d : x1FunctionFieldBar M →ₐ[ℚbar] x1FunctionFieldBar M).comp ι := by

  have hσH : IsDiamondAutHBar M H (ZMod.unitOfCoprime d hd) (diamondAutHBar M H (ZMod.unitOfCoprime d hd)) :=
    (ModularCurve.heckeDiamondInputsHAll M H).isDiamondAutHBar _
  have hσ : IsDiamondAut M d (diamondAut M d) := isDiamondAut_diamondAut (hin.2 d hd).1
  have hB := isBaseChangeAutOf_diamondAutBar M d
  obtain ⟨γ, -, hγ, -, hγd, -, -⟩ := exists_gammas_level (N := M) (N' := M) (t := 1) (by simp) hd
  have hdH : ((ZMod.unitOfCoprime d hd : (ZMod M)ˣ) : ZMod M) = d := ZMod.coe_unitOfCoprime d hd
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := ℚbar)
    (s := ⇑(coeffEmb ℚbar) '' ((xHFunctionField M H) : Set (LaurentSeries ℚ))) rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  apply Subtype.ext
  show ((ι (diamondAutHBar M H (ZMod.unitOfCoprime d hd) ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩) :
      x1FunctionFieldBar M) : LaurentSeries ℚbar)
    = ((diamondAutBar M d (ι ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩) : x1FunctionFieldBar M) :
      LaurentSeries ℚbar)
  rw [hι]
  have eι : ι ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩
      = (⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar (FH_le_FB M H hy)⟩ : x1FunctionFieldBar M) :=
    Subtype.ext (hι _)
  rw [transport_all hσH hσ hγ hγd hdH y hy, eι]
  exact (hB ⟨y, FH_le_FB M H hy⟩).symm

end TransportDia

end X1DegDiamond
p2m_reactivate "P2MW.S_ModularCurve_coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq.X1DegDiamond"

end
p2m_reactivate "P2MW.S_ModularCurve_coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq.X1DegDiamond"

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))
    (d : ℕ) (hd : Nat.Coprime d M) (x : ↥(ModularCurve.xHFunctionFieldBar M H)) :
    ι (ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime d hd) x) =
      ModularCurve.diamondAutBar M d (ι x) :=
  AlgHom.congr_fun (X1DegDiamond.comp_diamondAutHBar_eq (M := M) (H := H) (d := d) hin ι hι hd) x

end S_ModularCurve_coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq
end P2MW
export P2MW.S_ModularCurve_coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq (solution)

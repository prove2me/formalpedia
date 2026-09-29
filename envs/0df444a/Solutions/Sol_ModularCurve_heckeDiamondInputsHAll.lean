-- Prove2me | solution 1 for ModularCurve.heckeDiamondInputsHAll
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bfcbbabf-36b0-57b3-957f-85b26a846220

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDiamondInputsHAll
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace A2HDIA

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev Γ (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    Γ M H ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • Γ M H := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ M H) k) :
    ModularForm (Γ M H) k :=
  restrictForm (le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ M H) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem slashForm_mul_apply {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm (Γ M H) k₁) (g : ModularForm (Γ M H) k₂) :
    ⇑(slashForm γ hγ (f.mul g)) = ⇑(slashForm γ hγ f) * ⇑(slashForm γ hγ g) := by
  simp only [coe_slashForm, ModularForm.coe_mul, ← ModularForm.SL_slash]
  exact ModularForm.mul_slash_SL2 k₁ k₂ γ f g

theorem slashForm_add {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f g : ModularForm (Γ M H) k) :
    slashForm γ hγ (f + g) = slashForm γ hγ f + slashForm γ hγ g := by
  ext τ
  simp only [coe_slashForm, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply,
    ModularForm.add_apply]

theorem slashForm_smul {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (c : ℂ) (f : ModularForm (Γ M H) k) :
    ⇑(slashForm γ hγ (c • f)) = c • ⇑(slashForm γ hγ f) := by
  simp only [coe_slashForm, ModularForm.IsGLPos.coe_smul, ← ModularForm.SL_slash,
    ModularForm.SL_smul_slash]

theorem slashForm_slashForm {k : ℤ} (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma0 M)
    (f : ModularForm (Γ M H) k) :
    slashForm δ hδ (slashForm γ hγ f) = slashForm (γ * δ) (mul_mem hγ hδ) f := by
  ext τ
  simp only [coe_slashForm, map_mul, SlashAction.slash_mul]

theorem slashForm_of_mem {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγH : γ ∈ CohCarrier.GammaH M H)
    (f : ModularForm (Γ M H) k) : slashForm γ hγ f = f := by
  ext τ
  exact congrFun (SlashInvariantForm.slash_action_eqn f _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hγH)) τ

theorem slashForm_one {k : ℤ} (f : ModularForm (Γ M H) k) : slashForm 1 (one_mem _) f = f :=
  slashForm_of_mem 1 _ (one_mem _) f

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γ M H) k₁) (g : ModularForm (Γ M H) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods]

theorem qC_add {k : ℤ} (f g : ModularForm (Γ M H) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γ M H) k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γ M H) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ M H) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem ιC_injective : Function.Injective ιC :=
  RingHom.injective _

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem qC_ιC_ne_zero {k : ℤ} {g : ModularForm (Γ M H) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ ιC_injective).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ M H) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ιC_ne_zero hg hg0 ((qC_eq_zero_iff g).mpr h)

section Ratio

theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

theorem intSeriesC_neg' {K : Type*} [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

variable (M H)

abbrev S : Set (LaurentSeries ℚ) := intFormRatiosC ℚ (CohCarrier.GammaH M H)

variable {M H}

theorem mul_mem_S {a b : LaurentSeries ℚ} (ha : a ∈ S M H) (hb : b ∈ S M H) : a * b ∈ S M H := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

theorem add_mem_S {a b : LaurentSeries ℚ} (ha : a ∈ S M H) (hb : b ∈ S M H) : a + b ∈ S M H := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos one_mem_strictPeriods, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods,
      ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg₁0 hg₂0]

theorem neg_mem_S {a : LaurentSeries ℚ} (ha : a ∈ S M H) : -a ∈ S M H := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f).symm
  · rw [intSeriesC_neg', neg_div]

theorem inv_mem_S {a : LaurentSeries ℚ} (ha : a ∈ S M H) : a⁻¹ ∈ S M H := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, _root_.inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · refine ⟨k, g, f, pg, pf, hg, hf, hf0, ?_⟩
    rw [inv_div]

theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm (Γ M H) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (Γ M H) 0) : ℍ → ℂ) := by
  funext z
  rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
    mul_one]

theorem isIntegralQExp_const (n : ℤ) :
    IsIntegralQExp ((ModularForm.const (n : ℂ) : ModularForm (Γ M H) 0) : ℍ → ℂ) (PowerSeries.C n) := by
  rw [IsIntegralQExp, PowerSeries.map_C, coe_const_eq_smul_one,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, ModularForm.qExpansion_one,
    PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]

theorem algebraMap_mem_S (c : ℚ) : algebraMap ℚ (LaurentSeries ℚ) c ∈ S M H := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), isIntegralQExp_const _, ?_, ?_, ?_⟩
  · have := isIntegralQExp_const (M := M) (H := H) (c.den : ℤ)
    push_cast at this
    exact this
  · rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr hden
  · rw [intSeriesC, intSeriesC, PowerSeries.map_C, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply, eq_intCast,
      eq_intCast, eq_div_iff ((map_ne_zero_iff _ HahnSeries.C_injective).mpr hden), ← map_mul]
    congr 1
    push_cast
    exact Rat.mul_den_eq_num c

variable (M H) in

def SField : IntermediateField ℚ (LaurentSeries ℚ) where
  carrier := S M H
  mul_mem' ha hb := mul_mem_S ha hb
  one_mem' := by simpa using algebraMap_mem_S (M := M) (H := H) 1
  add_mem' ha hb := add_mem_S ha hb
  zero_mem' := by simpa using algebraMap_mem_S (M := M) (H := H) 0
  algebraMap_mem' c := algebraMap_mem_S c
  inv_mem' a ha := inv_mem_S ha

theorem mem_S_of_mem {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField M H) : y ∈ S M H := by
  have hle : xHFunctionField M H ≤ SField M H := IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

end Ratio

section Cancel

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ M H) k₁) (f₂ : ModularForm (Γ M H) k₂)
    (f₃ : ModularForm (Γ M H) k₃) (f₄ : ModularForm (Γ M H) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γ M H) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : qC (⇑D) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos one_mem_strictPeriods (f₁.mul f₂)
      (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, qC, hsub, map_sub]
    change qC (⇑f₁ * ⇑f₂) - qC (⇑f₃ * ⇑f₄) = 0
    rw [qC_mul, qC_mul, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, ModularForm.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

theorem slash_mul_eq {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ M H) k₁) (f₂ : ModularForm (Γ M H) k₂)
    (f₃ : ModularForm (Γ M H) k₃) (f₄ : ModularForm (Γ M H) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(slashForm γ hγ f₁) * ⇑(slashForm γ hγ f₂) : ℍ → ℂ) =
      ⇑(slashForm γ hγ f₃) * ⇑(slashForm γ hγ f₄) := by
  have h' := congrArg (fun F : ℍ → ℂ => F ∣[k₁ + k₂] γ) h
  rw [ModularForm.mul_slash_SL2] at h'
  conv at h' => rhs; rw [← hk, ModularForm.mul_slash_SL2]
  simpa only [coe_slashForm, ModularForm.SL_slash] using h'

theorem slashForm_congr {k : ℤ} {γ γ' : SL(2, ℤ)} (h : γ = γ') (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (f : ModularForm (Γ M H) k) : slashForm γ hγ f = slashForm γ' hγ' f := by
  subst h; rfl

theorem slashForm_inv_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ M H) k) :
    slashForm γ⁻¹ (inv_mem hγ) (slashForm γ hγ f) = f := by
  rw [slashForm_slashForm, slashForm_congr (mul_inv_cancel γ) _ (one_mem _), slashForm_one]

theorem slashForm_slashForm_inv {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ M H) k) :
    slashForm γ hγ (slashForm γ⁻¹ (inv_mem hγ) f) = f := by
  rw [slashForm_slashForm, slashForm_congr (inv_mul_cancel γ) _ (one_mem _), slashForm_one]

theorem slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {f : ModularForm (Γ M H) k}
    (hf : f ≠ 0) : slashForm γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← slashForm_inv_slashForm γ hγ f, h]
  ext τ
  simp [coe_slashForm]

theorem qC_slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm (Γ M H) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    qC (slashForm γ hγ g) ≠ 0 := fun h =>
  slashForm_ne_zero γ hγ (ne_zero_of_intSeriesC_ne_zero hg hg0) ((qC_eq_zero_iff _).mp h)

end Cancel

section Img

variable (H) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)

def IsImg (x y : LaurentSeries ℚ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (Γ M H) k) (pf pg : PowerSeries ℤ),
    IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC ℚ pg ≠ 0 ∧
      x = intSeriesC ℚ pf / intSeriesC ℚ pg ∧ ιC y * qC (slashForm γ hγ g) = qC (slashForm γ hγ f)

variable {H γ hγ}

theorem IsImg.apply_rep {x y : LaurentSeries ℚ} (h : IsImg H γ hγ x y) {k : ℤ}
    (f g : ModularForm (Γ M H) k) (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) (hx : x = intSeriesC ℚ pf / intSeriesC ℚ pg) :
    ιC y * qC (slashForm γ hγ g) = qC (slashForm γ hγ f) := by
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, hx₂, hy⟩ := h

  have hcross : intSeriesC ℚ pf * intSeriesC ℚ pg₂ = intSeriesC ℚ pf₂ * intSeriesC ℚ pg := by
    rw [← div_eq_div_iff hg0 hg₂0, ← hx, ← hx₂]
  have hq : qC f * qC g₂ = qC f₂ * qC g := by
    have := congrArg ιC hcross
    rwa [map_mul, map_mul, ιC_intSeriesC hf, ιC_intSeriesC hg₂, ιC_intSeriesC hf₂,
      ιC_intSeriesC hg] at this
  have hfun := mul_eq_mul_of_qC f g₂ f₂ g (add_comm k₂ k) hq
  have hsl := slash_mul_eq f g₂ f₂ g (add_comm k₂ k) hfun γ hγ
  have hqs : qC (slashForm γ hγ f) * qC (slashForm γ hγ g₂) =
      qC (slashForm γ hγ f₂) * qC (slashForm γ hγ g) := by
    rw [← qC_mul, ← qC_mul, hsl]
  have hne := qC_slashForm_ne_zero γ hγ hg₂ hg₂0
  apply mul_right_cancel₀ hne
  calc ιC y * qC (slashForm γ hγ g) * qC (slashForm γ hγ g₂)
      = ιC y * qC (slashForm γ hγ g₂) * qC (slashForm γ hγ g) := by ring
    _ = qC (slashForm γ hγ f₂) * qC (slashForm γ hγ g) := by rw [hy]
    _ = qC (slashForm γ hγ f) * qC (slashForm γ hγ g₂) := hqs.symm

theorem IsImg.unique {x y y' : LaurentSeries ℚ} (h : IsImg H γ hγ x y) (h' : IsImg H γ hγ x y') :
    y = y' := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx, hy'⟩ := h'
  have hy := h.apply_rep f g pf pg hf hg hg0 hx
  rw [← hy'] at hy
  exact ιC_injective (mul_right_cancel₀ (qC_slashForm_ne_zero γ hγ hg hg0) hy)

theorem IsImg.mul {x₁ y₁ x₂ y₂ : LaurentSeries ℚ} (h₁ : IsImg H γ hγ x₁ y₁) (h₂ : IsImg H γ hγ x₂ y₂) :
    IsImg H γ hγ (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl, hy₂⟩ := h₂
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]
  · rw [slashForm_mul_apply, slashForm_mul_apply, qC_mul, qC_mul, map_mul, ← hy₁, ← hy₂]
    ring

theorem IsImg.add {x₁ y₁ x₂ y₂ : LaurentSeries ℚ} (h₁ : IsImg H γ hγ x₁ y₁) (h₂ : IsImg H γ hγ x₂ y₂) :
    IsImg H γ hγ (x₁ + x₂) (y₁ + y₂) := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl, hy₂⟩ := h₂
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos one_mem_strictPeriods, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods,
      ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg₁0 hg₂0]
  · rw [slashForm_add, ModularForm.coe_add, qC_add, slashForm_mul_apply, slashForm_mul_apply,
      slashForm_mul_apply, qC_mul, qC_mul, qC_mul, map_add, ← hy₁, ← hy₂]
    ring

theorem IsImg.neg {x y : LaurentSeries ℚ} (h : IsImg H γ hγ x y) : IsImg H γ hγ (-x) (-y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl, hy⟩ := h
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f).symm
  · rw [intSeriesC_neg', neg_div]
  · have hneg : ⇑(slashForm γ hγ (-f)) = -⇑(slashForm γ hγ f) := by
      simp only [coe_slashForm, ModularForm.coe_neg, SlashAction.neg_slash]
    rw [hneg, qC_neg, map_neg, ← hy]
    ring

theorem isIntegralQExp_one' :
    IsIntegralQExp ((1 : ModularForm (Γ M H) 0) : ℍ → ℂ) 1 := by
  rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one

theorem slashForm_one_form : slashForm γ hγ (1 : ModularForm (Γ M H) 0) = 1 := by
  ext τ
  simp only [coe_slashForm, ModularForm.one_coe_eq_one]
  rw [ModularForm.is_invariant_one' γ]

theorem IsImg.one : IsImg H γ hγ 1 1 := by
  refine ⟨0, 1, 1, 1, 1, isIntegralQExp_one', isIntegralQExp_one', by simp, by simp, ?_⟩
  rw [map_one, one_mul, slashForm_one_form]

theorem IsImg.zero : IsImg H γ hγ 0 0 := by
  refine ⟨0, 0, 1, 0, 1, ?_, isIntegralQExp_one', by simp, by simp, ?_⟩
  · rw [ModularForm.coe_zero]; exact isIntegralQExp_zero
  · rw [map_zero, zero_mul]
    have : slashForm γ hγ (0 : ModularForm (Γ M H) 0) = 0 := by
      ext τ; simp [coe_slashForm]
    rw [this, ModularForm.coe_zero, qC_zero]

theorem IsImg.symm {x y : LaurentSeries ℚ} (h : IsImg H γ hγ x y) (hyS : y ∈ S M H) :
    IsImg H γ⁻¹ (inv_mem hγ) y x := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx, hy⟩ := h
  obtain ⟨kP, P, Q, pP, pQ, hP, hQ, hQ0, rfl⟩ := hyS
  refine ⟨kP, P, Q, pP, pQ, hP, hQ, hQ0, rfl, ?_⟩

  have hQ' : qC Q ≠ 0 := qC_ιC_ne_zero hQ hQ0
  have h1 : qC P * qC (slashForm γ hγ g) = qC (slashForm γ hγ f) * qC Q := by
    rw [← hy, map_div₀, ιC_intSeriesC hP, ιC_intSeriesC hQ, div_mul_eq_mul_div, div_mul_cancel₀ _ hQ']
  have hfun := mul_eq_mul_of_qC P (slashForm γ hγ g) (slashForm γ hγ f) Q (add_comm k kP) h1
  have hsl := slash_mul_eq P (slashForm γ hγ g) (slashForm γ hγ f) Q (add_comm k kP) hfun γ⁻¹ (inv_mem hγ)
  rw [slashForm_inv_slashForm, slashForm_inv_slashForm] at hsl
  have hq : qC (slashForm γ⁻¹ (inv_mem hγ) P) * qC g = qC f * qC (slashForm γ⁻¹ (inv_mem hγ) Q) := by
    rw [← qC_mul, ← qC_mul, hsl]
  rw [hx, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
  have hg' : qC g ≠ 0 := qC_ιC_ne_zero hg hg0
  rw [div_mul_eq_mul_div, div_eq_iff hg']
  exact hq.symm

theorem IsImg.congr_γ {γ' : SL(2, ℤ)} (e : γ = γ') {hγ' : γ' ∈ Gamma0 M} {x y : LaurentSeries ℚ}
    (h : IsImg H γ hγ x y) : IsImg H γ' hγ' x y := by
  subst e; exact h

end Img

section Sigma

variable (M H) in

def SlashRational : Prop :=
  ∀ (k : ℤ) (f : ModularForm (Γ M H) k) (pf : PowerSeries ℤ), IsIntegralQExp f pf →
    ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      ∃ D : ℤ, D ≠ 0 ∧ ∃ p : PowerSeries ℤ, IsIntegralQExp ((D : ℂ) • (⇑f ∣[k] (γ : GL (Fin 2) ℝ))) p

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)

theorem intSeriesC_C_mul (K : Type*) [Field K] (n : ℤ) (p : PowerSeries ℤ) :
    intSeriesC K (PowerSeries.C n * p) = HahnSeries.C (n : K) * intSeriesC K p := by
  rw [intSeriesC_mul, intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]

theorem ιC_C (c : ℚ) : ιC (HahnSeries.C c) = HahnSeries.C (c : ℂ) := by
  rw [ιC, coeffMap]
  ext n
  simp

theorem isIntegralQExp_smul_smul {k : ℤ} (F : ModularForm (Γ M H) k) {D : ℤ} (E : ℤ) {p : PowerSeries ℤ}
    (hp : IsIntegralQExp ((D : ℂ) • ⇑F) p) :
    IsIntegralQExp (⇑(((E : ℂ) * D) • F)) (PowerSeries.C E * p) := by
  rw [IsIntegralQExp] at hp ⊢
  rw [map_mul, PowerSeries.map_C, hp, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods _ F,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods _ F, PowerSeries.smul_eq_C_mul,
    PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, eq_intCast]

theorem ιC_intSeriesC_smul {k : ℤ} {F : ModularForm (Γ M H) k} {D : ℤ} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp ((D : ℂ) • ⇑F) p) : ιC (intSeriesC ℚ p) = HahnSeries.C (D : ℂ) * qC F := by
  rw [ιC_intSeriesC hp, qC_smul]

theorem exists_isImg (hW : SlashRational M H) {x : LaurentSeries ℚ} (hx : x ∈ S M H) :
    ∃ y ∈ S M H, IsImg H γ hγ x y := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨Df, hDf, pf', hpf'⟩ := hW k f pf hf γ hγ
  obtain ⟨Dg, hDg, pg', hpg'⟩ := hW k g pg hg γ hγ
  change IsIntegralQExp ((Df : ℂ) • ⇑(slashForm γ hγ f)) pf' at hpf'
  change IsIntegralQExp ((Dg : ℂ) • ⇑(slashForm γ hγ g)) pg' at hpg'
  have hF' := isIntegralQExp_smul_smul (slashForm γ hγ f) Dg hpf'
  have hG' := isIntegralQExp_smul_smul (slashForm γ hγ g) Df hpg'
  have hv : qC (slashForm γ hγ g) ≠ 0 := qC_slashForm_ne_zero γ hγ hg hg0
  have hDf' : (HahnSeries.C (Df : ℂ) : LaurentSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.C_injective).mpr (by exact_mod_cast hDf)
  have hDg' : (HahnSeries.C (Dg : ℂ) : LaurentSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.C_injective).mpr (by exact_mod_cast hDg)
  have hG'0 : intSeriesC ℚ (PowerSeries.C Df * pg') ≠ 0 := by
    intro h0
    have := congrArg ιC h0
    rw [intSeriesC_C_mul, map_mul, map_zero, ιC_intSeriesC_smul hpg', ιC_C] at this
    push_cast at this
    exact (mul_ne_zero hDf' (mul_ne_zero hDg' hv)) this
  refine ⟨_, ⟨k, _, _, _, _, hF', hG', hG'0, rfl⟩, k, f, g, pf, pg, hf, hg, hg0, rfl, ?_⟩
  rw [map_div₀, intSeriesC_C_mul, intSeriesC_C_mul, map_mul, map_mul, ιC_intSeriesC_smul hpf',
    ιC_intSeriesC_smul hpg', ιC_C, ιC_C]
  push_cast
  field_simp

variable (hW : SlashRational M H)

def σfun (x : xHFunctionField M H) : xHFunctionField M H :=
  ⟨Classical.choose (exists_isImg γ hγ hW (mem_S_of_mem x.2)),
    intFormRatiosC_subset ℚ _ (Classical.choose_spec (exists_isImg γ hγ hW (mem_S_of_mem x.2))).1⟩

theorem isImg_σfun (x : xHFunctionField M H) : IsImg H γ hγ (x : LaurentSeries ℚ) (σfun γ hγ hW x) :=
  (Classical.choose_spec (exists_isImg γ hγ hW (mem_S_of_mem x.2))).2

def σHom : xHFunctionField M H →+* xHFunctionField M H where
  toFun := σfun γ hγ hW
  map_one' := Subtype.ext ((isImg_σfun γ hγ hW 1).unique IsImg.one)
  map_mul' x y := Subtype.ext
    ((isImg_σfun γ hγ hW (x * y)).unique ((isImg_σfun γ hγ hW x).mul (isImg_σfun γ hγ hW y)))
  map_zero' := Subtype.ext ((isImg_σfun γ hγ hW 0).unique IsImg.zero)
  map_add' x y := Subtype.ext
    ((isImg_σfun γ hγ hW (x + y)).unique ((isImg_σfun γ hγ hW x).add (isImg_σfun γ hγ hW y)))

theorem σHom_apply (x : xHFunctionField M H) : σHom γ hγ hW x = σfun γ hγ hW x := rfl

theorem isImg_σHom (x : xHFunctionField M H) : IsImg H γ hγ (x : LaurentSeries ℚ) (σHom γ hγ hW x) :=
  isImg_σfun γ hγ hW x

theorem σHom_inv_apply (x : xHFunctionField M H) :
    σHom γ⁻¹ (inv_mem hγ) hW (σHom γ hγ hW x) = x := by
  apply Subtype.ext
  refine (isImg_σHom γ⁻¹ (inv_mem hγ) hW (σHom γ hγ hW x)).unique ?_
  exact (isImg_σHom γ hγ hW x).symm (mem_S_of_mem (σHom γ hγ hW x).2)

theorem σHom_apply_inv (x : xHFunctionField M H) :
    σHom γ hγ hW (σHom γ⁻¹ (inv_mem hγ) hW x) = x := by
  apply Subtype.ext
  refine (isImg_σHom γ hγ hW (σHom γ⁻¹ (inv_mem hγ) hW x)).unique ?_
  exact ((isImg_σHom γ⁻¹ (inv_mem hγ) hW x).symm
    (mem_S_of_mem (σHom γ⁻¹ (inv_mem hγ) hW x).2)).congr_γ (inv_inv γ)

def σRingEquiv : xHFunctionField M H ≃+* xHFunctionField M H :=
  { σHom γ hγ hW with
    invFun := σHom γ⁻¹ (inv_mem hγ) hW
    left_inv := σHom_inv_apply γ hγ hW
    right_inv := σHom_apply_inv γ hγ hW }

def σAlgEquiv : xHFunctionField M H ≃ₐ[ℚ] xHFunctionField M H :=
  AlgEquiv.ofRingEquiv (f := σRingEquiv γ hγ hW) fun c => by
    have := RingHom.ext_rat ((σHom γ hγ hW).comp (algebraMap ℚ (xHFunctionField M H)))
      (algebraMap ℚ (xHFunctionField M H))
    exact congrFun (congrArg DFunLike.coe this) c

theorem σAlgEquiv_apply (x : xHFunctionField M H) : σAlgEquiv γ hγ hW x = σHom γ hγ hW x := rfl

end Sigma

section Assembly

variable [NeZero M]

omit [NeZero M] in
theorem mem_GammaH_of_upperLeft (γd : Gamma0 M) {d : (ZMod M)ˣ}
    (hγd : CohCarrier.gamma0Units M γd = d⁻¹) {γ' : SL(2, ℤ)} (hγ' : γ' ∈ Gamma0 M)
    (hd : ((γ' 0 0 : ℤ) : ZMod M) = (d : ZMod M)) :
    γ' * (γd : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨mul_mem hγ' (inv_mem γd.2), ?_⟩
  have hu : (CohCarrier.gamma0Units M ⟨γ', hγ'⟩)⁻¹ = d := Units.ext hd
  have hprod : (⟨γ' * (γd : SL(2, ℤ))⁻¹, mul_mem hγ' (inv_mem γd.2)⟩ : Gamma0 M) = ⟨γ', hγ'⟩ * γd⁻¹ :=
    rfl
  rw [hprod, map_mul, map_inv, hγd, inv_inv, ← hu, mul_inv_cancel]
  exact one_mem H

theorem exists_algEquiv_of_slashRational (hW : SlashRational M H) (d : (ZMod M)ˣ) :
    ∃ σ : xHFunctionField M H ≃ₐ[ℚ] xHFunctionField M H,
      ∀ (k : ℤ) (f g : ModularForm (Γ M H) k) (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf)
        (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
        (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
        coeffMap (algebraMap ℚ ℂ)
              ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
                xHFunctionField M H) : LaurentSeries ℚ) *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ))) := by
  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  refine ⟨σAlgEquiv (γd : SL(2, ℤ)) γd.2 hW, ?_⟩
  intro k f g pf pg hf hg hg0 γ' hγ' hd
  have key := (isImg_σHom (γd : SL(2, ℤ)) γd.2 hW
    ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩).apply_rep
    f g pf pg hf hg hg0 rfl
  have hδ := mem_GammaH_of_upperLeft (H := H) γd hγd hγ' hd
  have hslash : ∀ h : ModularForm (Γ M H) k,
      slashForm γ' hγ' h = slashForm (γd : SL(2, ℤ)) γd.2 h := fun h => by
    rw [slashForm_congr (show γ' = γ' * (γd : SL(2, ℤ))⁻¹ * γd by rw [inv_mul_cancel_right]) hγ'
        (mul_mem (mul_mem hγ' (inv_mem γd.2)) γd.2) h,
      ← slashForm_slashForm _ _ (mul_mem hγ' (inv_mem γd.2)) γd.2,
      slashForm_of_mem _ _ hδ]
  change ιC _ * qC (⇑(slashForm γ' hγ' g)) = qC (⇑(slashForm γ' hγ' f))
  rw [hslash g, hslash f]
  exact key

theorem slashRational : SlashRational M H := by
  intro k f pf hf γ hγ
  have hle : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ M H :=
    Subgroup.map_mono (Gamma1_le_GammaH M H)
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M (restrictForm hle f) hf γ hγ
  refine ⟨D, hD, p₁, ?_⟩
  rw [IsIntegralQExp, hp₁, hf₁]
  rfl

end Assembly

end A2HDIA
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsHAll.A2HDIA"

namespace A2HDIH

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix AlgebraicCurve IntermediateField HahnSeries

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ}

def conjMat (ℓ : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0, (ℓ : ℤ) * γ 0 1; γ 1 0 / ℓ, γ 1 1]

theorem det_conjMat (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : (conjMat ℓ γ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (ℓ : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (ℓ : ℤ) * c / ℓ = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

def conjSL (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : SL(2, ℤ) := ⟨conjMat ℓ γ, det_conjMat γ h⟩

@[scoped simp] theorem conjSL_apply_00 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : conjSL γ h 0 0 = γ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) :
    conjSL γ h 0 1 = (ℓ : ℤ) * γ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) :
    conjSL γ h 1 0 = γ 1 0 / ℓ := rfl
@[scoped simp] theorem conjSL_apply_11 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : conjSL γ h 1 1 = γ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) : (ℓ : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem] at hγ
  have : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  exact (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this

theorem conjSL_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL γ (dvd_of_mem_Gamma0_mul hγ) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have : (conjSL γ (dvd_of_mem_Gamma0_mul hγ)) 1 0 = M * c := by
    show γ 1 0 / ℓ = M * c
    rw [hc]; push_cast
    rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
    exact Int.mul_ediv_cancel_left _ hℓ'
  rw [this]; push_cast
  simp

theorem conjSL_mem_GammaH {γ : SL(2, ℤ)} (hγH : γ ∈ CohCarrier.GammaH M H)
    (hγ : γ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL γ (dvd_of_mem_Gamma0_mul hγ) ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff] at hγH ⊢
  obtain ⟨hγ0, hH⟩ := hγH
  refine ⟨conjSL_mem_Gamma0 hγ hℓ, ?_⟩
  convert hH using 1
  rfl

theorem heckeDiag_mul_mul_inv {γ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ γ 1 0) (hℓ : ℓ ≠ 0) :
    ModularForm.heckeDiagMatrix ℓ * (γ : GL (Fin 2) ℝ) * (ModularForm.heckeDiagMatrix ℓ)⁻¹ =
      ((conjSL γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : (conjSL γ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show γ 1 0 / ℓ = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hℓ'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem inf_le_conj (hℓ : ℓ ≠ 0) :
    ((CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (ModularForm.heckeDiagMatrix ℓ)⁻¹ •
        (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) := by
  rintro x ⟨γ, hγ, rfl⟩
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, conjSL_mem_GammaH hγH hγ0 hℓ, (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hγ0) hℓ).symm⟩

theorem T_mem_inf : ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods : (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

end Group
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsHAll.A2HDIA"

section LevelRaise

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ]

def levelRaise {k : ℤ} (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm ((CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (inf_le_conj (NeZero.ne ℓ)) (ModularForm.translate f (ModularForm.heckeDiagMatrix ℓ))

theorem levelRaise_apply {k : ℤ} (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (τ : ℍ) : levelRaise (ℓ := ℓ) f τ = f (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] ModularForm.heckeDiagMatrix ℓ) τ) = _
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]

theorem coe_levelRaise {k : ℤ} (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ⇑(levelRaise (ℓ := ℓ) f) = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (levelRaise_apply f)

theorem coeff_qExpansion_levelRaise {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 (levelRaise (ℓ := ℓ) f)) =
      if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (qExpansion 1 f) else 0 := by
  rw [coe_levelRaise]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f one_mem_strictPeriods (NeZero.ne ℓ) n

def expandInt (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0

omit [NeZero ℓ] in
theorem coeff_expandInt (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (expandInt ℓ p) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0 := by
  rw [expandInt, PowerSeries.coeff_mk]

theorem isIntegralQExp_levelRaise {k : ℤ}
    {f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k} {pf : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) : IsIntegralQExp (levelRaise (ℓ := ℓ) f) (expandInt ℓ pf) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [coeff_expandInt, coeff_qExpansion_levelRaise]
  split_ifs with h
  · exact hf.coeff _
  · simp

theorem intSeriesC_expandInt (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (expandInt ℓ p) = qExpand K ℓ (intSeriesC K p) := by
  ext m
  simp only [intSeriesC]
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity)]
      simp only [PowerSeries.coeff_map, coeff_expandInt]
      have hj' : 0 ≤ j := le_of_not_gt hj
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [PowerSeries.coeff_map, coeff_expandInt, if_neg, map_zero]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem heckeBetaHDefined : HeckeBetaHDefined M H ℓ := by
  intro y hy

  suffices h : xHFunctionField M H ≤ (xHTopFunctionFieldC ℚ M H (M * ℓ)).comap (qExpandₐ ℓ) from h hy
  change IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  change qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ xHTopFunctionFieldC ℚ M H (M * ℓ)
  rw [map_div₀, ← intSeriesC_expandInt, ← intSeriesC_expandInt]
  have hg0' : intSeriesC ℚ (expandInt ℓ pg) ≠ 0 := by
    rw [intSeriesC_expandInt]
    exact fun h => hg0 (qExpand_injective ℓ (by rw [h, map_zero]))
  exact div_mem_qExpFunctionFieldC (levelRaise (ℓ := ℓ) f) (levelRaise (ℓ := ℓ) g)
    (isIntegralQExp_levelRaise hf) (isIntegralQExp_levelRaise hg) hg0'

end LevelRaise
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsHAll.A2HDIA"

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem transcendental_map (φ : F →ₐ[K] F') {x : F} (hx : Transcendental K x) :
    Transcendental K (φ x) := by
  rintro ⟨p, hp0, hp⟩
  refine hx ⟨p, hp0, ?_⟩
  rw [Polynomial.aeval_algHom_apply] at hp
  exact (map_eq_zero_iff φ (RingHom.injective (φ : F →+* F'))).mp hp

theorem finiteAlong_of_finiteDimensional_adjoin (φ : F →ₐ[K] F') (x : F)
    [h : FiniteDimensional (IntermediateField.adjoin K ({φ x} : Set F')) F'] : FiniteAlong K φ := by
  letI := algebraAlong φ
  show Module.Finite F F'
  set E := IntermediateField.adjoin K ({φ x} : Set F')
  have hE : E ≤ φ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := Module.finite_def.mp h
  refine Module.finite_def.mpr ⟨s, ?_⟩
  rw [eq_top_iff]
  rintro y -
  have hy : y ∈ Submodule.span E (s : Set F') := by rw [hs]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha =>
      obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp (hE c.2)
      have : (c • a : F') = b • a := by
        show (c : F') * a = φ.toRingHom b * a
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hb]
      rw [this]
      exact Submodule.smul_mem _ b ha

theorem isIntegral_of_finiteAlong (φ : F →ₐ[K] F') (h : FiniteAlong K φ) : φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := h
  intro y
  exact Algebra.IsIntegral.isIntegral (R := F) y

end Along
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsHAll.A2HDIA"

section Hecke

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

local notation "L" => AlgebraicClosure ℚ

scoped instance : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance : (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (Gamma1_le_GammaH M H)

theorem hasPrincipalDivisors_of_exists {K T : Type*} [Field K] [CharZero K] [Field T] [Algebra K T]
    (hT : ∃ x : T, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set T)) T) :
    HasPrincipalDivisors K T := by
  obtain ⟨x, hx, hfd⟩ := hT
  haveI := hfd
  exact AlgebraicCurve.hasPrincipalDivisors_of_transcendental K x hx

theorem finiteAlong_of_exists {K B T : Type*} [Field K] [Field B] [Field T] [Algebra K B] [Algebra K T]
    (hT : ∃ x : T, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set T)) T)
    (hB : ∃ x : B, Transcendental K x) (φ : B →ₐ[K] T) : FiniteAlong K φ := by
  obtain ⟨xT, hxT, hfdT⟩ := hT
  obtain ⟨xB, hxB⟩ := hB
  haveI := hfdT
  have htr : Transcendental K (φ xB) := transcendental_map φ hxB
  haveI := AlgebraicCurve.finiteDimensional_adjoin_of_transcendental xT htr
  exact finiteAlong_of_finiteDimensional_adjoin φ xB

theorem hasPrincipalDivisors_top :
    HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) :=
  hasPrincipalDivisors_of_exists
    (ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) T_mem_inf)

theorem finiteAlong_of_hom
    (φ : laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : FiniteAlong L φ :=
  finiteAlong_of_exists
    (ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) T_mem_inf)
    ((ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (CohCarrier.GammaH M H) (translation_mem_GammaH M H)).imp fun _ hx => hx.1) φ

omit [NeZero M] in
theorem charZero_bot : CharZero (xHFunctionFieldBar M H) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (xHFunctionFieldBar M H)).injective

theorem heckeInputsHAlong : HeckeInputsHAlong L M H ℓ := by
  have hfinα : FiniteAlong L (heckeAlphaHBar L M H ℓ) := finiteAlong_of_hom M H ℓ _
  have hfinβ : FiniteAlong L (heckeBetaHBar L M H ℓ) := finiteAlong_of_hom M H ℓ _
  have hα : HeckeAlphaHBarIntegral L M H ℓ := isIntegral_of_finiteAlong _ hfinα
  have hβ : HeckeBetaHBarIntegral L M H ℓ := isIntegral_of_finiteAlong _ hfinβ
  haveI := hasPrincipalDivisors_top M H ℓ
  haveI := charZero_bot M H
  have hsepα := AlgebraicCurve.separableAlong_of_charZero _ hα
  have hsepβ := AlgebraicCurve.separableAlong_of_charZero _ hβ
  exact heckeInputsHAlong_intro heckeBetaHDefined hα hβ
    (AlgebraicCurve.fundamentalIdentityAlong _ hβ hfinβ hsepβ) hfinα
    (AlgebraicCurve.normFormulaAlong _ hfinα hsepα)

end Hecke
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsHAll.A2HDIA"

section Diamond

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem exists_isDiamondAutHBar (d : (ZMod M)ˣ) :
    ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ := by
  obtain ⟨σ₀, hσ₀⟩ := A2HDIA.exists_algEquiv_of_slashRational (A2HDIA.slashRational (H := H)) d
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ)
    (xHFunctionField M H) σ₀.toRingEquiv
  refine ⟨τ, ?_⟩
  intro k f g pf pg hf hg hg0 γ hγ hd
  refine ⟨(σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
      xHFunctionField M H), SetLike.coe_mem _, ?_, hσ₀ k f g pf pg hf hg hg0 γ hγ hd⟩
  exact hτ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩

end Diamond
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsHAll.A2HDIA"

end A2HDIH
p2m_reactivate "P2MW.S_ModularCurve_heckeDiamondInputsHAll.A2HDIA P2MW.S_ModularCurve_heckeDiamondInputsHAll.A2HDIH"

open ModularCurve in
theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.HeckeDiamondInputsHAll M H :=
  ⟨fun ℓ hℓ => by
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact A2HDIH.heckeInputsHAlong M H ℓ,
   fun d => A2HDIH.exists_isDiamondAutHBar M H d⟩

end
end S_ModularCurve_heckeDiamondInputsHAll
end P2MW
export P2MW.S_ModularCurve_heckeDiamondInputsHAll (solution)

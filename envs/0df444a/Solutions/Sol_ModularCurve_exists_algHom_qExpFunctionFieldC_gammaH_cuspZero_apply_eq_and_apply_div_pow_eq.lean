-- Prove2me | solution 1 for ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/253a1402-6fd9-545f-b5c4-7b3661e75e62

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff
import Theorems.Thm_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash
import Theorems.Thm_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve HahnSeries
open scoped Real MatrixGroups ModularForm Manifold Pointwise

namespace XHCuspZero

local notation "Γᴳ(" M ", " H ")" =>
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "ℤ̄" => (integralClosure ℤ ℂ)

section Groups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γᴳ(M, H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

scoped instance finiteIndex_GammaH [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

variable {M H} in
private theorem _root_.XHCuspZero.conj_mem {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ CohCarrier.GammaH M H) :
    γ * A * γ⁻¹ ∈ CohCarrier.GammaH M H :=
  CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨A, hA⟩

p2m_export "XHCuspZero" "conj_mem"
theorem Gamma1_le : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γᴳ(M, H) :=
  Subgroup.map_mono (Gamma1_le_GammaH M H)

theorem GammaH_le_SL : Γᴳ(M, H) ≤ 𝒮ℒ := Subgroup.map_le_range _ _

theorem T_zpow_mem_Gamma : ModularGroup.T ^ (M : ℤ) ∈ CongruenceSubgroup.Gamma M := by
  rw [Gamma_mem]
  simp only [ModularGroup.coe_T_zpow]
  simp

theorem Gamma_le_Gamma1 : CongruenceSubgroup.Gamma M ≤ Gamma1 M := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem conj_T_zpow_mem (β : SL(2, ℤ)) : β * ModularGroup.T ^ (M : ℤ) * β⁻¹ ∈ CohCarrier.GammaH M H :=
  Gamma1_le_GammaH M H (Gamma_le_Gamma1 M ((Gamma_normal M).conj_mem _ (T_zpow_mem_Gamma M) β))

theorem coeGL_mul (β γ : SL(2, ℤ)) :
    ((β * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) β γ

end Groups

section Analytic

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem natCast_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)

theorem isBoundedAtImInfty_slash (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) :
    IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) := by
  rw [← ModularForm.SL_slash]; exact ModularFormClass.bdd_at_infty_slash f β

theorem mdifferentiable_slash (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) :=
  f.holo'.slash k _

theorem natCast_mem_strictPeriods_conj (β : SL(2, ℤ)) :
    (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ β)⁻¹ • Γᴳ(M, H)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    inv_inv, ConjAct.toConjAct_smul]
  refine ⟨_, conj_T_zpow_mem M H β, ?_⟩
  have hT : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (M : ℤ)) =
      Matrix.GeneralLinearGroup.upperRightHom (M : ℝ) := by
    apply Units.ext
    ext i j
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]
  rw [map_mul, map_mul, map_inv, hT]

theorem periodic_slash (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) :
    Periodic (((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) ∘ ofComplex) (M : ℝ) := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ β))
    (natCast_mem_strictPeriods_conj (M := M) (H := H) β)
  rwa [SlashInvariantForm.coe_translate] at this

theorem hasSum_slash (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))).coeff n •
      Periodic.qParam (M : ℝ) τ ^ n) (((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) τ) :=
  hasSum_qExpansion natCast_pos (periodic_slash f β) (mdifferentiable_slash f β)
    (isBoundedAtImInfty_slash f β) τ

theorem analyticAt_cuspFunction_slash (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))) 0 :=
  analyticAt_cuspFunction_zero natCast_pos (periodic_slash f β) (mdifferentiable_slash f β)
    (isBoundedAtImInfty_slash f β)

theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

def qg (β : SL(2, ℤ)) (f : ModularForm Γᴳ(M, H) k) : PowerSeries ℂ :=
  qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))

theorem qg_eq (β : SL(2, ℤ)) (f : ModularForm Γᴳ(M, H) k) :
    qg β f = qExpansion M ((⇑f : ℍ → ℂ) ∣[k] β) := by
  rw [ModularForm.SL_slash]; rfl

theorem coeff_qg_eq_of_hasSum (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) {c : ℕ → ℂ}
    (hc : ∀ τ : ℍ, HasSum (fun n : ℕ => c n • Periodic.qParam (M : ℝ) τ ^ n)
      (((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) τ)) (n : ℕ) :
    (qg β f).coeff n = c n :=
  (qExpansion_coeff_unique' natCast_pos (analyticAt_cuspFunction_slash f β) hc n).symm

theorem qParam_vadd (t : ℝ) (τ : ℍ) :
    Periodic.qParam (M : ℝ) (((t +ᵥ τ : ℍ) : ℂ)) =
      Complex.exp (2 * π * Complex.I * t / M) * Periodic.qParam (M : ℝ) τ := by
  simp only [Periodic.qParam, UpperHalfPlane.coe_vadd]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_qg_of_coe_eq_smul {k' : ℤ} (f' : ModularForm Γᴳ(M, H) k') (f : ModularForm Γᴳ(M, H) k)
    (c : ℂ) (δ : SL(2, ℤ)) (hk : k' = k)
    (hf' : (⇑f' : ℍ → ℂ) = c • ((⇑f : ℍ → ℂ) ∣[k] (δ : GL (Fin 2) ℝ))) (β : SL(2, ℤ)) (n : ℕ) :
    (qg β f').coeff n = c * (qg (δ * β) f).coeff n := by
  subst hk
  apply coeff_qg_eq_of_hasSum
  intro τ
  have happ : ((⇑f' : ℍ → ℂ) ∣[k'] (β : GL (Fin 2) ℝ)) τ =
      c * ((⇑f : ℍ → ℂ) ∣[k'] ((δ * β : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ := by
    rw [hf']
    have h1 : ((c • ((⇑f : ℍ → ℂ) ∣[k'] (δ : GL (Fin 2) ℝ))) ∣[k'] (β : GL (Fin 2) ℝ)) =
        c • (((⇑f : ℍ → ℂ) ∣[k'] (δ : GL (Fin 2) ℝ)) ∣[k'] (β : GL (Fin 2) ℝ)) :=
      ModularForm.SL_smul_slash k' β _ c
    rw [h1, coeGL_mul, SlashAction.slash_mul, Pi.smul_apply, smul_eq_mul]
  rw [happ]
  have := (hasSum_slash f (δ * β) τ).mul_left c
  convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  funext m
  simp only [qg, smul_eq_mul]; ring

theorem coeff_qg_mul_T_zpow (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) (j : ℤ) (n : ℕ) :
    (qg (β * ModularGroup.T ^ j) f).coeff n =
      Complex.exp (2 * π * Complex.I * j / M) ^ n * (qg β f).coeff n := by
  apply coeff_qg_eq_of_hasSum
  intro τ
  have happ : ((⇑f : ℍ → ℂ) ∣[k] ((β * ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
      ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) ((j : ℝ) +ᵥ τ) := by
    rw [coeGL_mul, SlashAction.slash_mul]
    set φ : ℍ → ℂ := (⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ) with hφ
    have h1 : (φ ∣[k] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
        (φ ∣[k] (ModularGroup.T ^ j : SL(2, ℤ))) τ := rfl
    rw [h1, ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_zpow_smul]
    have hden : UpperHalfPlane.denom (ModularGroup.T ^ j : SL(2, ℤ)) τ = 1 := by
      rw [ModularGroup.denom_apply]
      simp only [ModularGroup.coe_T_zpow]
      simp
    rw [hden, one_zpow, mul_one]
  rw [happ]
  have := hasSum_slash f β ((j : ℝ) +ᵥ τ)
  convert this using 1
  funext m
  rw [qParam_vadd, mul_pow, smul_eq_mul, smul_eq_mul]
  simp only [qg]
  push_cast
  ring

theorem coeff_qg_mul_neg_one (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) (n : ℕ) :
    (qg (β * (-1)) f).coeff n = (-1 : ℂ) ^ (-k) * (qg β f).coeff n := by
  apply coeff_qg_eq_of_hasSum
  intro τ
  have happ : ((⇑f : ℍ → ℂ) ∣[k] ((β * (-1) : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
      (-1 : ℂ) ^ (-k) * ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) τ := by
    rw [coeGL_mul, SlashAction.slash_mul]
    set φ : ℍ → ℂ := (⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ) with hφ
    have h1 : (φ ∣[k] (((-1 : SL(2, ℤ))) : GL (Fin 2) ℝ)) τ = (φ ∣[k] (-1 : SL(2, ℤ))) τ := rfl
    rw [h1, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
    have hden : UpperHalfPlane.denom (-1 : SL(2, ℤ)) τ = -1 := by
      rw [ModularGroup.denom_apply]
      simp
    rw [hden, mul_comm]
  rw [happ]
  have := (hasSum_slash f β τ).mul_left ((-1 : ℂ) ^ (-k))
  convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  funext m
  simp only [qg, smul_eq_mul]; ring

theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam (M : ℝ) τ ^ M := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  push_cast
  field_simp

theorem one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem slash_SL_levelOne (F : ModularForm 𝒮ℒ k) (β : SL(2, ℤ)) :
    (F : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ) = F :=
  SlashInvariantForm.slash_action_eqn F _ ⟨β, rfl⟩

theorem coeff_qg_levelOne (F : ModularForm 𝒮ℒ k) (β : SL(2, ℤ)) (n : ℕ) :
    (qg β (restrictForm (GammaH_le_SL M H) F)).coeff n =
      if (M : ℕ) ∣ n then (qExpansion 1 (⇑F : ℍ → ℂ)).coeff (n / M) else 0 := by
  classical
  set c : ℕ → ℂ := fun n => if (M : ℕ) ∣ n then (qExpansion 1 (⇑F : ℍ → ℂ)).coeff (n / M) else 0 with hc
  show (qg β (restrictForm (GammaH_le_SL M H) F)).coeff n = c n
  apply coeff_qg_eq_of_hasSum
  intro τ
  rw [coe_restrictForm, slash_SL_levelOne]
  have h1 := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL) F.holo'
    (ModularFormClass.bdd_at_infty F) τ
  have hMpos : 0 < M := NeZero.pos M
  have hinj : Function.Injective fun m : ℕ => M * m := mul_right_injective₀ hMpos.ne'
  have hsupp : ∀ x ∉ Set.range (fun m : ℕ => M * m),
      (fun m => c m • Periodic.qParam (M : ℝ) τ ^ m) x = 0 := by
    intro x hx
    have : ¬ (M : ℕ) ∣ x := by
      rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
    simp [hc, this]
  refine (hinj.hasSum_iff hsupp).1 ?_
  convert h1 using 1
  funext m
  simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hMpos]
  rw [qParam_one_eq_pow (M := M) τ, ← pow_mul]

end Analytic

section LevelOne

open EisensteinSeries

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

def E4cube : ModularForm 𝒮ℒ 12 := (ModularForm.E₄.pow 3).mcast (by norm_num)

def Delta : ModularForm 𝒮ℒ 12 := CuspForm.discriminant

theorem coe_Delta : ((Delta : ModularForm 𝒮ℒ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

def pE : PowerSeries ℤ := eisenstein4 ^ 3

def pD : PowerSeries ℤ := PowerSeries.X * dedekindEtaUnit

theorem isIntegralQExp_E4cube : IsIntegralQExp ((E4cube : ModularForm 𝒮ℒ 12) : ℍ → ℂ) pE := by
  rw [IsIntegralQExp, E4cube, ModularForm.coe_mcast, pE, map_pow, isIntegralQExp_E4,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem isIntegralQExp_Delta : IsIntegralQExp ((Delta : ModularForm 𝒮ℒ 12) : ℍ → ℂ) pD := by
  rw [IsIntegralQExp, coe_Delta]
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

def e4cube : ModularForm Γᴳ(M, H) 12 := restrictForm (GammaH_le_SL M H) E4cube

def delta : ModularForm Γᴳ(M, H) 12 := restrictForm (GammaH_le_SL M H) Delta

theorem isIntegralQExp_e4cube : IsIntegralQExp ((e4cube M H : ModularForm Γᴳ(M, H) 12) : ℍ → ℂ) pE :=
  isIntegralQExp_E4cube

theorem isIntegralQExp_delta : IsIntegralQExp ((delta M H : ModularForm Γᴳ(M, H) 12) : ℍ → ℂ) pD :=
  isIntegralQExp_Delta

variable (K : Type*) [Field K]

theorem coeff_intSeriesC_natCast (p : PowerSeries ℤ) (n : ℕ) :
    (intSeriesC K p).coeff (n : ℤ) = ((PowerSeries.coeff n p : ℤ) : K) := by
  rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]

theorem coeff_intSeriesC_of_neg (p : PowerSeries ℤ) {m : ℤ} (hm : m < 0) :
    (intSeriesC K p).coeff m = 0 :=
  ofPowerSeries_coeff_of_neg _ hm

theorem intSeriesC_pD_ne_zero : intSeriesC K pD ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff ((1 : ℕ) : ℤ)) h
  simp only [HahnSeries.coeff_zero, coeff_intSeriesC_natCast] at h1
  rw [pD, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit] at h1
  simp at h1

theorem jqModC_mul_delta : jqModC K * intSeriesC K pD = intSeriesC K pE := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, pD, pE, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

theorem jqModC_eq_div : jqModC K = intSeriesC K pE / intSeriesC K pD := by
  rw [eq_div_iff (intSeriesC_pD_ne_zero K), jqModC_mul_delta]

def slMk (p r a s : ℤ) (h : p * s - r * a = 1) : SL(2, ℤ) :=
  ⟨!![p, r; a, s], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

theorem coe_slMk_GL (p r a s : ℤ) (h : p * s - r * a = 1) :
    ((slMk p r a s h : SL(2, ℤ)) : GL (Fin 2) ℝ).val = !![(p : ℝ), r; a, s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slMk]

theorem GammaH_le_conj_SL :
    Γᴳ(M, H) ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix M)⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨γ, hγ, rfl⟩
  have hγ0 : γ ∈ Gamma0 M := CohCarrier.GammaH_le_Gamma0 H hγ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  have hγ' : ((γ 1 0 : ℤ) : ZMod M) = 0 := by
    simpa [CongruenceSubgroup.Gamma0_mem] using hγ0
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ'
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have hN : (M : ℕ) ≠ 0 := NeZero.ne M
  refine ⟨slMk (γ 0 0) (M * γ 0 1) c (γ 1 1) (by linear_combination hdet + (γ 0 1) * hc), ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change ((slMk _ _ _ _ _ : SL(2, ℤ)) : GL (Fin 2) ℝ).val * (ModularForm.heckeDiagMatrix M).val =
    (ModularForm.heckeDiagMatrix M).val * ((γ : GL (Fin 2) ℝ)).val
  rw [coe_slMk_GL, ModularForm.val_heckeDiagMatrix hN]
  have hc' : ((γ 1 0 : ℤ) : ℝ) = M * c := by exact_mod_cast hc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc'] <;> ring

variable {M H} in

def raise {k : ℤ} (F : ModularForm 𝒮ℒ k) : ModularForm Γᴳ(M, H) k :=
  ((M : ℝ) ^ (k - 1))⁻¹ •
    restrictForm (GammaH_le_conj_SL M H) (ModularForm.translate F (ModularForm.heckeDiagMatrix M))

theorem coe_raise {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ((raise F : ModularForm Γᴳ(M, H) k) : ℍ → ℂ) =
      ((M : ℂ) ^ (k - 1))⁻¹ • ((F : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix M) := by
  rw [raise, ModularForm.coe_smul, coe_restrictForm, ModularForm.coe_translate]
  funext τ
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem raise_apply {k : ℤ} (F : ModularForm 𝒮ℒ k) (τ : ℍ) :
    (raise F : ModularForm Γᴳ(M, H) k) τ = F (ModularForm.heckeDiagMatrix M • τ) := by
  rw [show (raise F : ModularForm Γᴳ(M, H) k) τ = ((raise F : ModularForm Γᴳ(M, H) k) : ℍ → ℂ) τ from rfl,
    coe_raise, Pi.smul_apply, smul_eq_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne M),
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact zpow_ne_zero _ (by exact_mod_cast NeZero.ne M)

def spread (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if (M : ℕ) ∣ n then PowerSeries.coeff (n / M) p else 0

theorem coeff_spread (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (spread M p) = if (M : ℕ) ∣ n then PowerSeries.coeff (n / M) p else 0 := by
  rw [spread, PowerSeries.coeff_mk]

theorem qParam_heckeDiag_smul (τ : ℍ) :
    Periodic.qParam 1 ((ModularForm.heckeDiagMatrix M • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ M := by
  simp only [Periodic.qParam]
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne M), ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem isIntegralQExp_raise {k : ℤ} (F : ModularForm 𝒮ℒ k) {p : PowerSeries ℤ}
    (hp : IsIntegralQExp (F : ℍ → ℂ) p) :
    IsIntegralQExp ((raise F : ModularForm Γᴳ(M, H) k) : ℍ → ℂ) (spread M p) := by
  classical
  rw [isIntegralQExp_iff]
  intro n
  set c : ℕ → ℂ := fun n => if (M : ℕ) ∣ n then ((PowerSeries.coeff (n / M) p : ℤ) : ℂ) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam 1 τ ^ m)
      ((raise F : ModularForm Γᴳ(M, H) k) τ) := by
    intro τ
    rw [raise_apply]
    have h1 := hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL) F.holo'
      (ModularFormClass.bdd_at_infty F) (ModularForm.heckeDiagMatrix M • τ)
    have hMpos : 0 < M := NeZero.pos M
    have hinj : Function.Injective fun m : ℕ => M * m := mul_right_injective₀ hMpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => M * m),
        (fun m => c m • Periodic.qParam 1 τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (M : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hMpos]
    rw [qParam_heckeDiag_smul, ← pow_mul, hp.coeff m]
  have := ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods M H) hsum n
  rw [← this, hc, coeff_spread]
  dsimp only
  split_ifs <;> simp

theorem intSeriesC_spread (p : PowerSeries ℤ) :
    intSeriesC K (spread M p) = qExpand K M (intSeriesC K p) := by
  ext m
  by_cases hMm : (M : ℤ) ∣ m
  · obtain ⟨t, rfl⟩ := hMm
    rw [qExpand_coeff_mul]
    rcases lt_or_ge t 0 with ht | ht
    · rw [coeff_intSeriesC_of_neg K _ ht, coeff_intSeriesC_of_neg K]
      exact mul_neg_of_pos_of_neg (by exact_mod_cast NeZero.pos M) ht
    · lift t to ℕ using ht
      rw [show (M : ℤ) * (t : ℤ) = ((M * t : ℕ) : ℤ) by push_cast; ring, coeff_intSeriesC_natCast,
        coeff_intSeriesC_natCast, coeff_spread, if_pos (dvd_mul_right M t),
        Nat.mul_div_cancel_left _ (NeZero.pos M)]
  · rw [qExpand_coeff_of_not_dvd M _ hMm]
    rcases lt_or_ge m 0 with hm | hm
    · exact coeff_intSeriesC_of_neg K _ hm
    · lift m to ℕ using hm
      rw [coeff_intSeriesC_natCast, coeff_spread, if_neg, Int.cast_zero]
      rintro ⟨t, rfl⟩
      exact hMm ⟨t, by push_cast; ring⟩

theorem jqNModC_eq_div : jqNModC K M = intSeriesC K (spread M pE) / intSeriesC K (spread M pD) := by
  rw [jqNModC, jqModC_eq_div, intSeriesC_spread, intSeriesC_spread, map_div₀]

theorem intSeriesC_spread_pD_ne_zero : intSeriesC K (spread M pD) ≠ 0 := by
  rw [intSeriesC_spread]
  exact fun h => intSeriesC_pD_ne_zero K (qExpand_injective M (h.trans (map_zero _).symm))

end LevelOne

section Hermite

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem had_ne {a d : ℕ} (ha : a ≠ 0) (hd : d ≠ 0) : (a : ℝ) * d ≠ 0 := by
  exact_mod_cast (Nat.mul_ne_zero ha hd)

def beta {a d : ℕ} (s : ℤ) (ha : a ≠ 0) (hd : d ≠ 0) : GL (Fin 2) ℝ :=
  ModularForm.upperTriangularGL a s d (had_ne ha hd)

section beta
variable {a d : ℕ} (s : ℤ) (ha : a ≠ 0) (hd : d ≠ 0)

theorem val_beta : ((beta s ha hd : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), s; 0, d] :=
  rfl

theorem det_beta : (beta s ha hd).det.val = (a : ℝ) * d := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, val_beta, Matrix.det_fin_two_of]

theorem det_beta_pos : 0 < (beta s ha hd).det.val := by
  rw [det_beta]; exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero ha hd)

theorem σ_beta : UpperHalfPlane.σ (beta s ha hd) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_beta_pos s ha hd)]

theorem denom_beta (τ : ℍ) : UpperHalfPlane.denom (beta s ha hd) τ = d := by
  simp [UpperHalfPlane.denom, val_beta]

theorem coe_beta_smul (τ : ℍ) :
    ((beta s ha hd • τ : ℍ) : ℂ) = ((a : ℂ) * τ + (s : ℂ)) / d := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_beta_pos s ha hd)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_beta]

theorem slash_beta (kk : ℤ) (f : ℍ → ℂ) :
    f ∣[kk] beta s ha hd =
      (((a : ℂ) * d) ^ (kk - 1) * (d : ℂ) ^ (-kk)) • fun τ => f (beta s ha hd • τ) := by
  funext τ
  rw [ModularForm.slash_apply, σ_beta, det_beta, denom_beta, Pi.smul_apply, smul_eq_mul]
  have : |(a : ℝ) * d| = (a : ℝ) * d :=
    abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero ha hd))
  rw [this]
  push_cast
  simp only [ContinuousAlgEquiv.refl_apply]
  ring

end beta

theorem heckeDiag_mul_eq (g : SL(2, ℤ)) {a d : ℕ} (ha : a ≠ 0) (hd : d ≠ 0) (had : a * d = M)
    (s c' t : ℤ) (hc' : g 1 0 = a * c') (ht : g 1 1 * a - g 1 0 * s = M * t) :
    ∃ γ' : SL(2, ℤ), ModularForm.heckeDiagMatrix M * (g : GL (Fin 2) ℝ) =
      (γ' : GL (Fin 2) ℝ) * beta s ha hd := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  have hMad : (M : ℤ) = a * d := by exact_mod_cast had.symm
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha
  have h11 : g 1 1 = d * t + c' * s := by
    have h1 : (a : ℤ) * (g 1 1 - d * t - c' * s) = 0 := by
      linear_combination ht + s * hc' + t * hMad
    have h2 := (mul_eq_zero.mp h1).resolve_left ha'
    linear_combination h2
  refine ⟨slMk (g 0 0 * d) (a * g 0 1 - g 0 0 * s) c' t
    (by linear_combination hdet + g 0 1 * hc' - g 0 0 * h11), ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_slMk_GL, ModularForm.val_heckeDiagMatrix (NeZero.ne M), val_beta]
  have hM' : (M : ℝ) = a * d := by exact_mod_cast had.symm
  have hc'' : ((g 1 0 : ℤ) : ℝ) = a * c' := by exact_mod_cast hc'
  have h11' : ((g 1 1 : ℤ) : ℝ) = d * t + c' * s := by exact_mod_cast h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hM', hc'', h11'] <;> ring

theorem slash_raise_eq (F : ModularForm 𝒮ℒ k) (g : SL(2, ℤ)) {a d : ℕ} (ha : a ≠ 0) (hd : d ≠ 0)
    (had : a * d = M) (s c' t : ℤ) (hc' : g 1 0 = a * c') (ht : g 1 1 * a - g 1 0 * s = M * t) :
    ((raise F : ModularForm Γᴳ(M, H) k) : ℍ → ℂ) ∣[k] (g : GL (Fin 2) ℝ) =
      ((d : ℂ) ^ (-k)) • fun τ => F (beta s ha hd • τ) := by
  obtain ⟨γ', hγ'⟩ := heckeDiag_mul_eq g ha hd had s c' t hc' ht
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have ha'' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [coe_raise]
  have h1 : ((((M : ℂ) ^ (k - 1))⁻¹ • ((F : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix M)) ∣[k]
      (g : GL (Fin 2) ℝ)) = ((M : ℂ) ^ (k - 1))⁻¹ •
        (((F : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix M) ∣[k] (g : GL (Fin 2) ℝ)) :=
    ModularForm.SL_smul_slash k g _ _
  rw [h1, ← SlashAction.slash_mul, hγ', SlashAction.slash_mul, slash_SL_levelOne, slash_beta, smul_smul]
  congr 1
  have hM' : (M : ℂ) = a * d := by exact_mod_cast had.symm
  rw [hM', inv_mul_cancel_left₀ (zpow_ne_zero _ (mul_ne_zero ha'' hd'))]

def zetaC (M : ℕ) : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / M)) (Complex.exp_ne_zero _)

theorem coe_zetaC : ((zetaC M : ℂˣ) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) := rfl

theorem cosetTranslate (F : ModularForm 𝒮ℒ k) {a d : ℕ} [NeZero a] (hd : d ≠ 0)
    (had : a * d = M) (B : ℕ) :
    Periodic ((fun τ : ℍ => F (beta (B : ℤ) (NeZero.ne a) hd • τ)) ∘ ofComplex) M ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (beta (B : ℤ) (NeZero.ne a) hd • τ)) ∧
      IsBoundedAtImInfty (fun τ : ℍ => F (beta (B : ℤ) (NeZero.ne a) hd • τ)) ∧
      ((qExpansion M (fun τ : ℍ => F (beta (B : ℤ) (NeZero.ne a) hd • τ)) : PowerSeries ℂ) :
          LaurentSeries ℂ) =
        cosetSubst (zetaC M) a B ((qExpansion 1 (F : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst (NeZero.ne M) had (zetaC M) (coe_zetaC)
    (F : ℍ → ℂ) _ (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL)
    F.holo' (ModularFormClass.bdd_at_infty F) (fun τ τ' h => by
      congr 1
      apply UpperHalfPlane.ext
      rw [h, coe_beta_smul]; push_cast; rfl)

theorem coeff_cosetSubst_ofPowerSeries {R : Type*} [Field R] (u : Rˣ) (a B : ℕ) [NeZero a]
    (P : PowerSeries R) (n : ℕ) :
    (cosetSubst u a B (ofPowerSeries ℤ R P)).coeff (n : ℤ) =
      if a * a ∣ n then (((u ^ (a * B)) ^ (n / (a * a)) : Rˣ) : R) * PowerSeries.coeff (n / (a * a)) P
      else 0 := by
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  have e : cosetSubst u a B (ofPowerSeries ℤ R P) =
      qExpand R (a * a) (qTwist (u ^ (a * B)) (ofPowerSeries ℤ R P)) := rfl
  rw [e]
  by_cases h : a * a ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [if_pos (dvd_mul_right _ _), show (((a * a) * m : ℕ) : ℤ) = ((a * a : ℕ) : ℤ) * (m : ℤ) by push_cast; ring,
      qExpand_coeff_mul, qTwist_coeff, HahnSeries.ofPowerSeries_apply_coeff, zpow_natCast,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne (a * a)))]
  · rw [if_neg h, qExpand_coeff_of_not_dvd (a * a)]
    rintro ⟨m, hm⟩
    apply h
    rcases le_or_gt 0 m with hm0 | hm0
    · lift m to ℕ using hm0
      exact ⟨m, by exact_mod_cast hm⟩
    · exfalso
      have : ((a * a : ℕ) : ℤ) * m < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (a * a))) hm0
      omega

theorem coeff_cosetSubst_ofPowerSeries_of_neg {R : Type*} [Field R] (u : Rˣ) (a B : ℕ) [NeZero a]
    (P : PowerSeries R) {m : ℤ} (hm : m < 0) :
    (cosetSubst u a B (ofPowerSeries ℤ R P)).coeff m = 0 := by
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  have e : cosetSubst u a B (ofPowerSeries ℤ R P) =
      qExpand R (a * a) (qTwist (u ^ (a * B)) (ofPowerSeries ℤ R P)) := rfl
  rw [e]
  by_cases h : ((a * a : ℕ) : ℤ) ∣ m
  · obtain ⟨t, rfl⟩ := h
    have ht : t < 0 := by
      by_contra ht
      exact absurd hm (not_lt.mpr (mul_nonneg (by positivity) (not_lt.mp ht)))
    rw [qExpand_coeff_mul, qTwist_coeff, ofPowerSeries_coeff_of_neg _ ht, mul_zero]
  · exact qExpand_coeff_of_not_dvd (a * a) _ h

theorem coeff_qg_raise (F : ModularForm 𝒮ℒ k) (g : SL(2, ℤ)) {a d : ℕ} [NeZero a] (hd : d ≠ 0)
    (had : a * d = M) (B : ℕ) (c' t : ℤ) (hc' : g 1 0 = a * c')
    (ht : g 1 1 * a - g 1 0 * (B : ℤ) = M * t) (n : ℕ) :
    (qg g (raise F : ModularForm Γᴳ(M, H) k)).coeff n =
      (d : ℂ) ^ (-k) * (if a * a ∣ n then
        (((zetaC M ^ (a * B)) ^ (n / (a * a)) : ℂˣ) : ℂ) * (qExpansion 1 (F : ℍ → ℂ)).coeff (n / (a * a))
        else 0) := by
  obtain ⟨hper, hhol, hbdd, hexp⟩ := cosetTranslate (M := M) F hd had B
  have han : AnalyticAt ℂ (cuspFunction (M : ℝ) (fun τ : ℍ => F (beta (B : ℤ) (NeZero.ne a) hd • τ))) 0 :=
    analyticAt_cuspFunction_zero natCast_pos hper hhol hbdd
  have h1 : qg g (raise F : ModularForm Γᴳ(M, H) k) =
      (d : ℂ) ^ (-k) • qExpansion (M : ℝ) (fun τ : ℍ => F (beta (B : ℤ) (NeZero.ne a) hd • τ)) := by
    rw [qg, slash_raise_eq F g (NeZero.ne a) hd had B c' t hc' ht, qExpansion_smul han]
  rw [h1, PowerSeries.coeff_smul, smul_eq_mul]
  congr 1
  have h2 := congrArg (fun x : LaurentSeries ℂ => x.coeff (n : ℤ)) hexp
  simp only [HahnSeries.ofPowerSeries_apply_coeff] at h2
  rw [h2, coeff_cosetSubst_ofPowerSeries]

end Hermite

section Lifts

variable {M : ℕ} [NeZero M]

variable (K : Type*) [Field K] (φ : ℤ̄ →+* K)

def liftZ (p : PowerSeries ℤ) : PowerSeries ℤ̄ := p.map (Int.castRingHom _)

theorem map_liftZ {R : Type*} [CommRing R] (ψ : ℤ̄ →+* R) (p : PowerSeries ℤ) :
    (liftZ p).map ψ = p.map (Int.castRingHom R) := by
  rw [liftZ, ← RingHom.comp_apply (PowerSeries.map ψ), ← PowerSeries.map_comp,
    RingHom.ext_int (ψ.comp (Int.castRingHom _)) (Int.castRingHom R)]

theorem ofPowerSeries_map_liftZ (p : PowerSeries ℤ) :
    ofPowerSeries ℤ K ((liftZ p).map φ) = intSeriesC K p := by
  rw [map_liftZ]; rfl

variable {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem map_liftZ_spread (F : ModularForm 𝒮ℒ k) {p : PowerSeries ℤ} (hp : IsIntegralQExp (F : ℍ → ℂ) p)
    (g : SL(2, ℤ)) :
    (liftZ (spread M p)).map (algebraMap ℤ̄ ℂ) =
      (M : ℂ) ^ 0 • qExpansion M (((restrictForm (GammaH_le_SL M H) F : ModularForm Γᴳ(M, H) k) :
        ℍ → ℂ) ∣[k] g) := by
  rw [pow_zero, one_smul, map_liftZ, ← qg_eq]
  ext n
  rw [PowerSeries.coeff_map, coeff_qg_levelOne, coeff_spread]
  split_ifs with h
  · rw [eq_intCast, hp.coeff]
  · simp

def liftR (u c : ℤ̄) (a B : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ̄ :=
  PowerSeries.mk fun n => if a * a ∣ n then c * u ^ (a * B * (n / (a * a))) *
    ((PowerSeries.coeff (n / (a * a)) p : ℤ) : ℤ̄) else 0

theorem ofPowerSeries_map_liftR {R : Type*} [Field R] (ψ : ℤ̄ →+* R) (u c : ℤ̄) (a B : ℕ) [NeZero a]
    (p : PowerSeries ℤ) (w : Rˣ) (hw : (w : R) = ψ u) :
    ofPowerSeries ℤ R ((liftR u c a B p).map ψ) =
      HahnSeries.C (ψ c) * cosetSubst w a B (ofPowerSeries ℤ R (p.map (Int.castRingHom R))) := by
  ext m
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  rcases lt_or_ge m 0 with hm | hm
  · rw [ofPowerSeries_coeff_of_neg _ hm, coeff_cosetSubst_ofPowerSeries_of_neg _ _ _ _ hm, mul_zero]
  · lift m to ℕ using hm
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, coeff_cosetSubst_ofPowerSeries, liftR,
      PowerSeries.coeff_mk]
    split_ifs with h
    · rw [map_mul, map_mul, map_pow, PowerSeries.coeff_map, eq_intCast, map_intCast, ← hw,
        Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul, mul_assoc]
    · rw [map_zero, mul_zero]

def liftI (P : PowerSeries ℂ) (h : ∀ n, IsIntegral ℤ (P.coeff n)) : PowerSeries ℤ̄ :=
  PowerSeries.mk fun n => ⟨P.coeff n, h n⟩

theorem map_val_liftI (P : PowerSeries ℂ) (h : ∀ n, IsIntegral ℤ (P.coeff n)) :
    (liftI P h).map (algebraMap ℤ̄ ℂ) = P := by
  ext n; rw [PowerSeries.coeff_map, liftI, PowerSeries.coeff_mk]; rfl

theorem coeff_liftI (P : PowerSeries ℂ) (h : ∀ n, IsIntegral ℤ (P.coeff n)) (n : ℕ) :
    ((PowerSeries.coeff n (liftI P h) : ℤ̄) : ℂ) = P.coeff n := by
  rw [liftI, PowerSeries.coeff_mk]

end Lifts

section MainAux

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem natCast_ne_zero_of_dvd (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hℓM : ¬ ℓ ∣ M) {a : ℕ} (ha : a ∣ M) : (a : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K ℓ] at h
  exact hℓM (h.trans ha)

theorem map_val_liftR (F : ModularForm 𝒮ℒ k) {p : PowerSeries ℤ} (hp : IsIntegralQExp (F : ℍ → ℂ) p)
    (g : SL(2, ℤ)) {a d : ℕ} [NeZero a] (hd : d ≠ 0) (had : a * d = M) (B : ℕ) (c' t : ℤ)
    (hc' : g 1 0 = a * c') (ht : g 1 1 * a - g 1 0 * (B : ℤ) = M * t)
    (z : ℤ̄) (hz : (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M)) (hk : 0 ≤ k) :
    (liftR z ((a : ℤ̄) ^ k.toNat) a B p).map (algebraMap ℤ̄ ℂ) =
      (M : ℂ) ^ k.toNat • qExpansion M (((raise F : ModularForm Γᴳ(M, H) k) : ℍ → ℂ) ∣[k] g) := by
  have hkn : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne a
  rw [← qg_eq]
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_smul, smul_eq_mul, coeff_qg_raise F g hd had B c' t hc' ht,
    liftR, PowerSeries.coeff_mk]
  have hconst : (M : ℂ) ^ k.toNat * (d : ℂ) ^ (-k) = (a : ℂ) ^ k.toNat := by
    have hM' : (M : ℂ) = a * d := by exact_mod_cast had.symm
    rw [hM', ← zpow_natCast, ← zpow_natCast, hkn, mul_zpow, mul_assoc, ← zpow_add₀ hd', add_neg_cancel,
      zpow_zero, mul_one]
  split_ifs with h
  · rw [map_mul, map_mul, map_pow, map_pow, map_intCast, hp.coeff, ← mul_assoc, ← mul_assoc, hconst]
    congr 1
    rw [show algebraMap ℤ̄ ℂ (a : ℤ̄) = (a : ℂ) from map_natCast _ _, show algebraMap ℤ̄ ℂ z = (z : ℂ) from rfl,
      hz, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_zetaC, ← pow_mul]
  · rw [map_zero, mul_zero, mul_zero]

end MainAux

section CuspZero

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem pow_slash (A : SL(2, ℤ)) (f : ℍ → ℂ) :
    ∀ n : ℕ, (f ^ n) ∣[((n : ℤ) * k)] (A : GL (Fin 2) ℝ) = (f ∣[k] (A : GL (Fin 2) ℝ)) ^ n
  | 0 => by
    rw [pow_zero, pow_zero, Nat.cast_zero, zero_mul]
    exact ModularForm.is_invariant_one' A
  | n + 1 => by
    rw [pow_succ, pow_succ, show (((n + 1 : ℕ) : ℤ) * k) = (n : ℤ) * k + k by push_cast; ring,
      ← ModularForm.SL_slash, ModularForm.mul_slash_SL2, ModularForm.SL_slash, ModularForm.SL_slash,
      pow_slash A f n]

theorem coe_pow_slash (f : ModularForm Γᴳ(M, H) k) (A : SL(2, ℤ)) (n : ℕ) :
    ((⇑f : ℍ → ℂ) ∣[k] (A : GL (Fin 2) ℝ)) ^ n =
      (⇑(f.pow n) : ℍ → ℂ) ∣[((n : ℤ) * k)] (A : GL (Fin 2) ℝ) := by
  rw [ModularForm.coe_pow, pow_slash]

theorem qg_pow (f : ModularForm Γᴳ(M, H) k) (β : SL(2, ℤ)) (n : ℕ) :
    qg β (f.pow n) = (qg β f) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, qg, ← coe_pow_slash, pow_zero]
    exact UpperHalfPlane.qExpansion_one _
  | succ n ih =>
    rw [pow_succ, ← ih, qg, qg, qg, ← coe_pow_slash, pow_succ, coe_pow_slash]
    exact qExpansion_mul (analyticAt_cuspFunction_slash (f.pow n) β) (analyticAt_cuspFunction_slash f β)

theorem isIntegralQExp_pow (f : ModularForm Γᴳ(M, H) k) {p : PowerSeries ℤ} (hp : IsIntegralQExp (⇑f) p)
    (n : ℕ) : IsIntegralQExp (⇑(f.pow n)) (p ^ n) := by
  rw [IsIntegralQExp, map_pow, ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods M H)]
  rw [IsIntegralQExp] at hp
  rw [hp]

theorem intSeriesC_pow (K : Type*) [Field K] (p : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (p ^ n) = intSeriesC K p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, intSeriesC_one]
  | succ n ih => rw [pow_succ, pow_succ, intSeriesC_mul, ih]

theorem S_one_zero : (ModularGroup.S : SL(2, ℤ)) 1 0 = 1 := rfl

theorem S_one_one : (ModularGroup.S : SL(2, ℤ)) 1 1 = 0 := rfl

variable (K : Type*) [Field K]

theorem ofPowerSeries_map_C_mul_liftZ (φ : ℤ̄ →+* K) (c : ℤ̄) (p : PowerSeries ℤ) :
    ofPowerSeries ℤ K ((PowerSeries.C c * liftZ p).map φ) = HahnSeries.C (φ c) * intSeriesC K p := by
  rw [map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C, ofPowerSeries_map_liftZ]

theorem map_C_mul (c : ℤ̄) (P : PowerSeries ℤ̄) :
    (PowerSeries.C c * P).map (algebraMap ℤ̄ ℂ) = ((c : ℂ)) • P.map (algebraMap ℤ̄ ℂ) := by
  rw [map_mul, PowerSeries.map_C]
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_smul, smul_eq_mul]
  rfl

theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ] :
    ∃ Θ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] LaurentSeries K,
      (∀ x : qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = jqModC K → Θ x = jqNModC K M) ∧
      (∀ x : qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = jqNModC K M → Θ x = jqModC K) ∧
      ∀ (k : ℤ) (f : ModularForm Γᴳ(M, H) k) (pf : PowerSeries ℤ),
        IsIntegralQExp f pf → intSeriesC K pf ≠ 0 →
        ∃ y : LaurentSeries K, y ≠ 0 ∧
          ∀ (n : ℕ) (F : ModularForm 𝒮ℒ ((n : ℤ) * k)) (P : PowerSeries ℤ), IsIntegralQExp F P →
            ∀ x : qExpFunctionFieldC K (CohCarrier.GammaH M H),
              (x : LaurentSeries K) = intSeriesC K P / intSeriesC K pf ^ n →
              Θ x = qExpand K M (intSeriesC K P) / y ^ n := by
  classical

  have hMK : (M : K) ≠ 0 := natCast_ne_zero_of_dvd K hℓM dvd_rfl

  have hcyc : IsCyclotomicExtension {M} K K :=
    IsSepClosed.isCyclotomicExtension {M} K fun a ha _ => by
      rw [Set.mem_singleton_iff] at ha; subst ha; exact ⟨hMK⟩
  obtain ⟨ζ₀, hζ₀⟩ := hcyc.exists_isPrimitiveRoot (Set.mem_singleton M) (NeZero.ne M)
  set ζ : Kˣ := (hζ₀.isUnit (NeZero.ne M)).unit with hζdef
  have hζ : IsPrimitiveRoot (ζ : K) M := by simpa [hζdef] using hζ₀

  obtain ⟨φ, hφ⟩ :=
    Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot ℓ M hℓM K (ζ : K) hζ
  set z : ℤ̄ := ⟨Complex.exp (2 * Real.pi * Complex.I / M),
    (Complex.isPrimitiveRoot_exp M (NeZero.ne M)).isIntegral (NeZero.pos M)⟩ with hzdef
  have hz : (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) := rfl
  have hφz : (ζ : K) = φ z := (hφ z rfl).symm

  obtain ⟨Θ, hΘ⟩ :=
    exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash M H hℓM K φ
      ModularGroup.S
  refine ⟨Θ, ?_, ?_, ?_⟩
  ·
    intro x hx
    have h := hΘ 12 (e4cube M H) (delta M H) pE pD (isIntegralQExp_e4cube M H) (isIntegralQExp_delta M H)
      (intSeriesC_pD_ne_zero K) 0 (liftZ (spread M pE)) (liftZ (spread M pD))
      (map_liftZ_spread E4cube isIntegralQExp_E4cube _) (map_liftZ_spread Delta isIntegralQExp_Delta _)
      x (by rw [hx, jqModC_eq_div])
    rw [h.2, ofPowerSeries_map_liftZ, ofPowerSeries_map_liftZ, intSeriesC_spread, intSeriesC_spread,
      ← map_div₀, ← jqModC_eq_div, jqNModC]
  ·
    intro x hx
    haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
    have h := hΘ 12 (raise E4cube) (raise Delta) (spread M pE) (spread M pD)
      (isIntegralQExp_raise M H E4cube isIntegralQExp_E4cube) (isIntegralQExp_raise M H Delta isIntegralQExp_Delta)
      (intSeriesC_spread_pD_ne_zero M K) 12
      (liftR z (((1 : ℕ) : ℤ̄) ^ (12 : ℤ).toNat) 1 0 pE) (liftR z (((1 : ℕ) : ℤ̄) ^ (12 : ℤ).toNat) 1 0 pD)
      (map_val_liftR (H := H) E4cube isIntegralQExp_E4cube ModularGroup.S (a := 1) (d := M) (NeZero.ne M)
        (one_mul M) 0 1 0 (by rw [S_one_zero]; norm_num) (by rw [S_one_one, S_one_zero]; simp) z hz (by norm_num))
      (map_val_liftR (H := H) Delta isIntegralQExp_Delta ModularGroup.S (a := 1) (d := M) (NeZero.ne M)
        (one_mul M) 0 1 0 (by rw [S_one_zero]; norm_num) (by rw [S_one_one, S_one_zero]; simp) z hz (by norm_num))
      x (by rw [hx, jqNModC_eq_div])
    have hc0 : HahnSeries.C (φ ((((1 : ℕ) : ℤ̄)) ^ (12 : ℤ).toNat)) ≠ (0 : LaurentSeries K) := by
      apply HahnSeries.C_ne_zero
      rw [map_pow, map_natCast]
      simp
    rw [h.2, ofPowerSeries_map_liftR φ z _ 1 0 pE ζ hφz, ofPowerSeries_map_liftR φ z _ 1 0 pD ζ hφz,
      mul_div_mul_left _ _ hc0, ← map_div₀]
    change cosetSubst ζ 1 0 (intSeriesC K pE / intSeriesC K pD) = _
    rw [← jqModC_eq_div, cosetSubst, RingHom.comp_apply, mul_zero, pow_zero, qTwist_one_apply,
      qExpand_congr (one_mul 1), qExpand_one_apply]
  ·
    intro k f pf hpf hpf0

    obtain ⟨a₁, hint⟩ := ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_coeff M
      (restrictForm (Gamma1_le M H) f) hpf ModularGroup.S
    have hI : ∀ n, IsIntegral ℤ (((M : ℂ) ^ a₁ • qg ModularGroup.S f).coeff n) := fun n => by
      rw [PowerSeries.coeff_smul, smul_eq_mul, qg_eq]
      exact hint n
    set G₁ : PowerSeries ℤ̄ := liftI _ hI with hG₁def
    have hG₁ : G₁.map (algebraMap ℤ̄ ℂ) = (M : ℂ) ^ a₁ • qExpansion M ((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S) := by
      rw [hG₁def, map_val_liftI, qg_eq]

    have hone : ((1 : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
        intSeriesC K pf / intSeriesC K pf := by
      rw [div_self hpf0]; rfl
    have hne : ofPowerSeries ℤ K (G₁.map φ) ≠ 0 :=
      (hΘ k f f pf pf hpf hpf hpf0 a₁ G₁ G₁ hG₁ hG₁ 1 hone).1
    refine ⟨ofPowerSeries ℤ K (G₁.map φ) / HahnSeries.C ((M : K) ^ a₁), ?_, ?_⟩
    · exact div_ne_zero hne (HahnSeries.C_ne_zero (pow_ne_zero _ hMK))
    intro n F P hFP x hx

    have hFF : (PowerSeries.C ((M : ℤ̄) ^ (a₁ * n)) * liftZ (spread M P)).map (algebraMap ℤ̄ ℂ) =
        (M : ℂ) ^ (a₁ * n) • qExpansion M
          ((⇑(restrictForm (GammaH_le_SL M H) F : ModularForm Γᴳ(M, H) ((n : ℤ) * k)) : ℍ → ℂ) ∣[((n : ℤ) * k)]
            ModularGroup.S) := by
      rw [map_C_mul, map_liftZ_spread (H := H) F hFP ModularGroup.S, pow_zero, one_smul]
      simp
    have hGG : (G₁ ^ n).map (algebraMap ℤ̄ ℂ) =
        (M : ℂ) ^ (a₁ * n) • qExpansion M ((⇑(f.pow n) : ℍ → ℂ) ∣[((n : ℤ) * k)] ModularGroup.S) := by
      rw [map_pow, hG₁, smul_pow, ← pow_mul, ← qg_eq, ← qg_pow, qg_eq]
    have hpow : IsIntegralQExp (⇑(f.pow n)) (pf ^ n) := isIntegralQExp_pow f hpf n
    have h0 : intSeriesC K (pf ^ n) ≠ 0 := by
      rw [intSeriesC_pow]; exact pow_ne_zero _ hpf0
    have hFP' : IsIntegralQExp
        (⇑(restrictForm (GammaH_le_SL M H) F : ModularForm Γᴳ(M, H) ((n : ℤ) * k))) P := hFP
    have h := hΘ ((n : ℤ) * k) (restrictForm (GammaH_le_SL M H) F) (f.pow n) P (pf ^ n) hFP' hpow h0
      (a₁ * n) _ _ hFF hGG x (by rw [hx, intSeriesC_pow])
    rw [h.2, ofPowerSeries_map_C_mul_liftZ, map_pow, map_pow, intSeriesC_spread, map_pow, map_natCast,
      div_pow, map_pow (HahnSeries.C), ← pow_mul]
    have hc : (HahnSeries.C ((M : K) ^ (a₁ * n)) : LaurentSeries K) ≠ 0 :=
      HahnSeries.C_ne_zero (pow_ne_zero _ hMK)
    field_simp
    rw [map_pow]

end CuspZero

end XHCuspZero
p2m_reactivate "P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq.XHCuspZero"

open XHCuspZero in
open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ] :
    ∃ Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] LaurentSeries K,
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqModC K → Θ x = ModularCurve.jqNModC K M) ∧
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqNModC K M → Θ x = ModularCurve.jqModC K) ∧
      ∀ (k : ℤ) (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf : PowerSeries ℤ), ModularCurve.IsIntegralQExp f pf → ModularCurve.intSeriesC K pf ≠ 0 →
        ∃ y : LaurentSeries K, y ≠ 0 ∧
          ∀ (n : ℕ) (F : ModularForm 𝒮ℒ ((n : ℤ) * k)) (P : PowerSeries ℤ),
            ModularCurve.IsIntegralQExp F P →
            ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
              (x : LaurentSeries K) =
                ModularCurve.intSeriesC K P / ModularCurve.intSeriesC K pf ^ n →
              Θ x = ModularCurve.qExpand K M (ModularCurve.intSeriesC K P) / y ^ n :=
  main M H hℓM K

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq.XHCuspZero"

end S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq
end P2MW
export P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq (solution)

-- Prove2me | solution 1 for ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/60fe33fc-3328-5ce8-a04e-b12a664324ae

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_one intSeriesC_zero intSeriesC_mul qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
p2m_open "ModularCurve~Gamma1_le_GammaH"
namespace DiamondAct

local notation "Γ₁ℝ" M => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γᴴℝ" M "," H => ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Level

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem Gamma1_le_GammaH : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem M A).mp hA
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    simpa [CongruenceSubgroup.Gamma0Map] using h11
  rw [this]
  exact one_mem H

scoped instance GammaH_finiteIndex' : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem T_mem_GammaH : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  Gamma1_le_GammaH M H (by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T])

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γᴴℝ M, H).strictPeriods := by
  have h1 : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  obtain ⟨γ, hγ, hγeq⟩ := h1
  exact ⟨γ, Gamma1_le_GammaH M H hγ, hγeq⟩

variable {M H}

def liftForm {k : ℤ} (f : ModularForm (Γ₁ℝ M) k)
    (hinv : ∀ h : SL(2, ℤ), h ∈ CohCarrier.GammaH M H → (⇑f : ℍ → ℂ) ∣[k] h = ⇑f) :
    ModularForm (Γᴴℝ M, H) k where
  toFun := f
  slash_action_eq' A hA := by
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hA
    exact hinv h hh
  holo' := f.holo'
  bdd_at_cusps' {c} hc := by
    apply f.bdd_at_cusps'
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc

@[scoped simp] theorem coe_liftForm {k : ℤ} (f : ModularForm (Γ₁ℝ M) k)
    (hinv : ∀ h : SL(2, ℤ), h ∈ CohCarrier.GammaH M H → (⇑f : ℍ → ℂ) ∣[k] h = ⇑f) :
    (⇑(liftForm f hinv) : ℍ → ℂ) = ⇑f := rfl

end Level

section QExp

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem analyticAt_form (f : ModularForm (Γᴴℝ M, H) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods M H)

theorem map_intCast_injective : Function.Injective (PowerSeries.map (Int.castRingHom ℂ)) := by
  intro p r h
  ext n
  have := congrArg (PowerSeries.coeff n) h
  simp only [PowerSeries.coeff_map, eq_intCast] at this
  exact_mod_cast this

theorem isIntegralQExp_add {f g : ModularForm (Γᴴℝ M, H) k} {p r : PowerSeries ℤ}
    (hf : IsIntegralQExp (⇑f) p) (hg : IsIntegralQExp (⇑g) r) :
    IsIntegralQExp (⇑(f + g)) (p + r) := by
  unfold IsIntegralQExp at hf hg ⊢
  rw [ModularForm.coe_add, qExpansion_add (analyticAt_form f) (analyticAt_form g), map_add, hf, hg]

theorem isIntegralQExp_zero : IsIntegralQExp (⇑(0 : ModularForm (Γᴴℝ M, H) k)) 0 := by
  unfold IsIntegralQExp
  rw [ModularForm.coe_zero, qExpansion_zero, map_zero]

theorem qExpansion_intCast_smul (f : ModularForm (Γᴴℝ M, H) k) (n : ℤ) {p : PowerSeries ℤ}
    (hf : IsIntegralQExp (⇑f) p) :
    qExpansion 1 ((n : ℂ) • (⇑f : ℍ → ℂ)) = (n • p).map (Int.castRingHom ℂ) := by
  rw [qExpansion_smul (analyticAt_form f), ← hf, map_zsmul, Int.cast_smul_eq_zsmul]

theorem isIntegralQExp_intCast_smul (f : ModularForm (Γᴴℝ M, H) k) (n : ℤ) {p : PowerSeries ℤ}
    (hf : IsIntegralQExp (⇑f) p) : IsIntegralQExp (⇑((n : ℂ) • f)) (n • p) := by
  unfold IsIntegralQExp
  rw [ModularForm.IsGLPos.coe_smul]
  exact (qExpansion_intCast_smul f n hf).symm

theorem smul_eq_smul_of_coe (f₁ f₂ : ModularForm (Γᴴℝ M, H) k) {p₁ p₂ : PowerSeries ℤ}
    (h₁ : IsIntegralQExp (⇑f₁) p₁) (h₂ : IsIntegralQExp (⇑f₂) p₂) (m n : ℤ)
    (h : (m : ℂ) • (⇑f₁ : ℍ → ℂ) = (n : ℂ) • (⇑f₂ : ℍ → ℂ)) : m • p₁ = n • p₂ := by
  apply map_intCast_injective
  rw [← qExpansion_intCast_smul f₁ m h₁, ← qExpansion_intCast_smul f₂ n h₂, h]

theorem isIntegralQExp_mul {k₁ k₂ : ℤ} {f : ModularForm (Γᴴℝ M, H) k₁} {g : ModularForm (Γᴴℝ M, H) k₂}
    {p r : PowerSeries ℤ} (hf : IsIntegralQExp (⇑f) p) (hg : IsIntegralQExp (⇑g) r) :
    IsIntegralQExp (⇑(f.mul g)) (p * r) := by
  unfold IsIntegralQExp at hf hg ⊢
  rw [ModularForm.coe_mul, qExpansion_mul (analyticAt_form f) (analyticAt_form g), map_mul, hf, hg]

theorem eq_zero_of_isIntegralQExp_zero (f : ModularForm (Γᴴℝ M, H) k) (hf : IsIntegralQExp (⇑f) 0) :
    f = 0 := by
  apply ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods M H)
  intro n
  have h0 : qExpansion 1 (⇑f : ℍ → ℂ) = 0 := by rw [← hf, map_zero]
  show (qExpansion 1 ⇑f).coeff n = (qExpansion 1 ⇑(0 : ModularForm (Γᴴℝ M, H) k)).coeff n
  rw [h0, ModularForm.coe_zero, qExpansion_zero]

end QExp

section Datum

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

structure IDatum (w : ℤ) where
  f : ModularForm (Γᴴℝ M, H) w
  p : PowerSeries ℤ
  hp : IsIntegralQExp (⇑f) p

variable {M H}
variable {w w₁ w₂ : ℤ}

namespace IDatum

theorem hinv (D : IDatum M H w) (h : SL(2, ℤ)) (hh : h ∈ CohCarrier.GammaH M H) :
    (⇑D.f : ℍ → ℂ) ∣[w] h = ⇑D.f :=
  SlashInvariantForm.slash_action_eqn D.f _ (Subgroup.mem_map_of_mem _ hh)

def add (D E : IDatum M H w) : IDatum M H w :=
  ⟨D.f + E.f, D.p + E.p, isIntegralQExp_add D.hp E.hp⟩

def zsmul (n : ℤ) (D : IDatum M H w) : IDatum M H w :=
  ⟨(n : ℂ) • D.f, n • D.p, isIntegralQExp_intCast_smul D.f n D.hp⟩

def mul (D : IDatum M H w₁) (E : IDatum M H w₂) : IDatum M H (w₁ + w₂) :=
  ⟨D.f.mul E.f, D.p * E.p, isIntegralQExp_mul D.hp E.hp⟩

@[scoped simp] theorem mul_p (D : IDatum M H w₁) (E : IDatum M H w₂) : (D.mul E).p = D.p * E.p := rfl
@[scoped simp] theorem mul_f (D : IDatum M H w₁) (E : IDatum M H w₂) : ⇑(D.mul E).f = ⇑D.f * ⇑E.f :=
  ModularForm.coe_mul _ _

end IDatum
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum"

end Datum
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum"

end DiamondAct
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_one intSeriesC_zero intSeriesC_mul qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
p2m_open "ModularCurve~Gamma1_le_GammaH"
namespace DiamondAct

local notation "Γ₁ℝ" M => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γᴴℝ" M "," H => ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Translate

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {w : ℤ}

theorem smul_SL_slash (k : ℤ) (γ : SL(2, ℤ)) (F : ℍ → ℂ) (c : ℂ) :
    (c • F) ∣[k] γ = c • (F ∣[k] γ) := by
  exact ModularForm.SL_smul_slash k γ F c

theorem slash_invariant_of_invariant (F : ℍ → ℂ) (k : ℤ)
    (hinv : ∀ h : SL(2, ℤ), h ∈ CohCarrier.GammaH M H → F ∣[k] h = F)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (h : SL(2, ℤ)) (hh : h ∈ CohCarrier.GammaH M H) :
    (F ∣[k] γ) ∣[k] h = F ∣[k] γ := by
  have hconj : γ * h * γ⁻¹ ∈ CohCarrier.GammaH M H :=
    CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨h, hh⟩
  have hγh : γ * h = (γ * h * γ⁻¹) * γ := by group
  rw [← SlashAction.slash_mul, hγh, SlashAction.slash_mul, hinv _ hconj]

theorem exists_trans (D : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (a : ℕ) (E : IDatum M H w),
      (⇑E.f : ℍ → ℂ) = ((M : ℂ) ^ a) • ((⇑D.f : ℍ → ℂ) ∣[w] γ) := by
  obtain ⟨a, f₁, p₁, hp₁, hf₁⟩ :=
    exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 M
      (restrictForm (Subgroup.map_mono (Gamma1_le_GammaH M H)) D.f) D.hp γ hγ
  have hinv : ∀ h : SL(2, ℤ), h ∈ CohCarrier.GammaH M H → (⇑f₁ : ℍ → ℂ) ∣[w] h = ⇑f₁ := fun h hh => by
    rw [hf₁, smul_SL_slash, coe_restrictForm, slash_invariant_of_invariant _ _ D.hinv γ hγ h hh]
  exact ⟨a, ⟨liftForm f₁ hinv, p₁, hp₁⟩, by rw [coe_liftForm, hf₁, coe_restrictForm]⟩

def texp (D : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) : ℕ :=
  (exists_trans D γ hγ).choose

private def _root_.ModularCurve.DiamondAct.trans (D : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) : IDatum M H w :=
  (exists_trans D γ hγ).choose_spec.choose

p2m_export "ModularCurve.DiamondAct" "trans"
theorem trans_f (D : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (⇑(trans D γ hγ).f : ℍ → ℂ) = ((M : ℂ) ^ texp D γ hγ) • ((⇑D.f : ℍ → ℂ) ∣[w] γ) :=
  (exists_trans D γ hγ).choose_spec.choose_spec

theorem smul_trans_p_eq (D : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (b : ℕ) (E : IDatum M H w) (hE : (⇑E.f : ℍ → ℂ) = ((M : ℂ) ^ b) • ((⇑D.f : ℍ → ℂ) ∣[w] γ)) :
    ((M : ℤ) ^ b) • (trans D γ hγ).p = ((M : ℤ) ^ texp D γ hγ) • E.p := by
  apply smul_eq_smul_of_coe _ _ (trans D γ hγ).hp E.hp
  push_cast
  rw [trans_f, hE, smul_smul, smul_smul, mul_comm]

variable (K : Type*) [Field K]

def redHom : PowerSeries ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (Int.castRingHom K))

@[scoped simp] theorem redHom_apply (p : PowerSeries ℤ) : redHom K p = intSeriesC K p := rfl

theorem intSeriesC_zsmul (n : ℤ) (p : PowerSeries ℤ) : intSeriesC K (n • p) = (n : K) • intSeriesC K p := by
  rw [← redHom_apply, map_zsmul, redHom_apply, Int.cast_smul_eq_zsmul]

theorem intSeriesC_add (p r : PowerSeries ℤ) : intSeriesC K (p + r) = intSeriesC K p + intSeriesC K r := by
  rw [← redHom_apply, map_add, redHom_apply, redHom_apply]

theorem intSeriesC_eq_zero_iff (p : PowerSeries ℤ) :
    intSeriesC K p = 0 ↔ ∀ n : ℕ, ((PowerSeries.coeff n p : ℤ) : K) = 0 := by
  constructor
  · intro h n
    have h' : p.map (Int.castRingHom K) = 0 := by
      apply (HahnSeries.ofPowerSeries_injective : Function.Injective (HahnSeries.ofPowerSeries ℤ K))
      rw [map_zero]; exact h
    have := congrArg (PowerSeries.coeff n) h'
    simpa [PowerSeries.coeff_map] using this
  · intro h
    have h' : p.map (Int.castRingHom K) = 0 := by
      ext n; simpa [PowerSeries.coeff_map] using h n
    rw [intSeriesC, h', map_zero]

variable {K}
variable (hM : (M : K) ≠ 0)

def tRed (K : Type*) [Field K] (D : IDatum M H w) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) : LaurentSeries K :=
  (((M : K) ^ texp D γ hγ)⁻¹) • intSeriesC K (trans D γ hγ).p

include hM in

theorem tRed_eq_of (D : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (b : ℕ) (E : IDatum M H w) (hE : (⇑E.f : ℍ → ℂ) = ((M : ℂ) ^ b) • ((⇑D.f : ℍ → ℂ) ∣[w] γ)) :
    tRed K D γ hγ = (((M : K) ^ b)⁻¹) • intSeriesC K E.p := by
  have h := congrArg (intSeriesC K) (smul_trans_p_eq D γ hγ b E hE)
  rw [intSeriesC_zsmul, intSeriesC_zsmul] at h
  push_cast at h
  have hMa : ((M : K) ^ texp D γ hγ) ≠ 0 := pow_ne_zero _ hM
  have hMb : ((M : K) ^ b) ≠ 0 := pow_ne_zero _ hM
  rw [tRed]
  have h2 : intSeriesC K (trans D γ hγ).p =
      ((M : K) ^ b)⁻¹ • (((M : K) ^ texp D γ hγ) • intSeriesC K E.p) := by
    rw [← h, smul_smul, inv_mul_cancel₀ hMb, one_smul]
  rw [h2, smul_smul, smul_smul]
  congr 1
  field_simp

include hM in

theorem tRed_eq_zero_of_red_eq_zero (D : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (h0 : intSeriesC K D.p = 0) : tRed K D γ hγ = 0 := by
  obtain ⟨ℓ, hchar⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K ℓ with hℓ | hℓ
  ·
    have hℓM : ¬ (ℓ : ℤ) ∣ (M : ℤ) := by
      intro hdvd
      apply hM
      have := (CharP.intCast_eq_zero_iff K ℓ (M : ℤ)).mpr hdvd
      exact_mod_cast this
    have hcoef : ∀ n : ℕ, (ℓ : ℤ) ∣ PowerSeries.coeff n D.p := fun n =>
      (CharP.intCast_eq_zero_iff K ℓ _).mp (((intSeriesC_eq_zero_iff K D.p).mp h0) n)

    let p' : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff n D.p / ℓ
    have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

    let D' : IDatum M H w :=
      { f := ((ℓ : ℂ)⁻¹) • D.f
        p := p'
        hp := by
          unfold IsIntegralQExp
          rw [ModularForm.IsGLPos.coe_smul, qExpansion_smul (analyticAt_form D.f), ← D.hp]
          ext n
          obtain ⟨q, hq⟩ := hcoef n
          have hℓZ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
          simp only [map_smul, PowerSeries.coeff_map, eq_intCast, smul_eq_mul, p', PowerSeries.coeff_mk, hq,
            Int.mul_ediv_cancel_left _ hℓZ0]
          push_cast
          field_simp }

    have hrel : (((ℓ : ℤ) * (M : ℤ) ^ texp D γ hγ : ℤ) : ℂ) • (⇑(trans D' γ hγ).f : ℍ → ℂ) =
        (((M : ℤ) ^ texp D' γ hγ : ℤ) : ℂ) • (⇑(trans D γ hγ).f : ℍ → ℂ) := by
      push_cast
      rw [trans_f, trans_f]
      simp only [D', ModularForm.IsGLPos.coe_smul, smul_SL_slash, smul_smul]
      congr 1
      field_simp

    have hZ := smul_eq_smul_of_coe _ _ (trans D' γ hγ).hp (trans D γ hγ).hp _ _ hrel
    have hℓZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
    rw [tRed, smul_eq_zero]
    right
    rw [intSeriesC_eq_zero_iff]
    intro n
    rw [CharP.intCast_eq_zero_iff K ℓ]
    have hn := congrArg (PowerSeries.coeff n) hZ
    simp only [map_smul, smul_eq_mul] at hn

    have hdvd : (ℓ : ℤ) ∣ (M : ℤ) ^ texp D' γ hγ * PowerSeries.coeff n (trans D γ hγ).p := by
      rw [← hn, mul_assoc]; exact dvd_mul_right _ _
    rcases hℓZ.dvd_or_dvd hdvd with h1 | h2
    · exact absurd (hℓZ.dvd_of_dvd_pow h1) hℓM
    · exact h2
  ·
    subst hℓ
    haveI := CharP.charP_to_charZero K
    have hp0 : D.p = 0 := by
      ext n
      have := ((intSeriesC_eq_zero_iff K D.p).mp h0) n
      rw [map_zero]
      exact_mod_cast this
    have hf0 : D.f = 0 := eq_zero_of_isIntegralQExp_zero D.f (hp0 ▸ D.hp)
    have ht : (trans D γ hγ).p = 0 := by
      apply map_intCast_injective
      rw [(trans D γ hγ).hp, trans_f, hf0, ModularForm.coe_zero, SlashAction.zero_slash, smul_zero,
        map_zero, qExpansion_zero]
    rw [tRed, ht, intSeriesC_zero, smul_zero]

end Translate
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end DiamondAct
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_one intSeriesC_zero intSeriesC_mul qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
p2m_open "ModularCurve~Gamma1_le_GammaH"
namespace DiamondAct

local notation "Γᴴℝ" M "," H => ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Group

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {w : ℤ}

namespace IDatum

@[scoped ext] theorem ext {D E : IDatum M H w} (hf : D.f = E.f) (hp : D.p = E.p) : D = E := by
  cases D; cases E
  cases hf; cases hp
  rfl

scoped instance : Zero (IDatum M H w) := ⟨⟨0, 0, isIntegralQExp_zero⟩⟩

scoped instance : Add (IDatum M H w) := ⟨IDatum.add⟩

scoped instance : SMul ℤ (IDatum M H w) := ⟨fun n D => IDatum.zsmul n D⟩

scoped instance : SMul ℕ (IDatum M H w) := ⟨fun n D => IDatum.zsmul (n : ℤ) D⟩

scoped instance : Neg (IDatum M H w) := ⟨fun D => IDatum.zsmul (-1) D⟩

scoped instance : Sub (IDatum M H w) := ⟨fun D E => D + (-E)⟩

@[scoped simp] theorem zero_f : (0 : IDatum M H w).f = 0 := rfl
@[scoped simp] theorem zero_p : (0 : IDatum M H w).p = 0 := rfl
@[scoped simp] theorem add_f' (D E : IDatum M H w) : (D + E).f = D.f + E.f := rfl
@[scoped simp] theorem add_p' (D E : IDatum M H w) : (D + E).p = D.p + E.p := rfl
@[scoped simp] theorem zsmul_f' (n : ℤ) (D : IDatum M H w) : (n • D).f = (n : ℂ) • D.f := rfl
@[scoped simp] theorem zsmul_p' (n : ℤ) (D : IDatum M H w) : (n • D).p = n • D.p := rfl
@[scoped simp] theorem nsmul_f' (n : ℕ) (D : IDatum M H w) : (n • D).f = ((n : ℤ) : ℂ) • D.f := rfl
@[scoped simp] theorem nsmul_p' (n : ℕ) (D : IDatum M H w) : (n • D).p = (n : ℤ) • D.p := rfl
@[scoped simp] theorem neg_f' (D : IDatum M H w) : (-D).f = ((-1 : ℤ) : ℂ) • D.f := rfl
@[scoped simp] theorem neg_p' (D : IDatum M H w) : (-D).p = (-1 : ℤ) • D.p := rfl
@[scoped simp] theorem sub_f' (D E : IDatum M H w) : (D - E).f = D.f + ((-1 : ℤ) : ℂ) • E.f := rfl
@[scoped simp] theorem sub_p' (D E : IDatum M H w) : (D - E).p = D.p + (-1 : ℤ) • E.p := rfl

def toProd (D : IDatum M H w) : ModularForm (Γᴴℝ M, H) w × PowerSeries ℤ := (D.f, D.p)

theorem toProd_injective : Function.Injective (toProd (M := M) (H := H) (w := w)) := by
  intro D E h
  simp only [toProd, Prod.mk.injEq] at h
  exact ext h.1 h.2

scoped instance : AddCommGroup (IDatum M H w) :=
  toProd_injective.addCommGroup toProd rfl (fun _ _ => rfl)
    (fun D => by
      simp only [toProd, Prod.neg_mk, Prod.mk.injEq, neg_f', neg_p', neg_one_zsmul, and_true]
      ext τ; simp)
    (fun D E => by
      show (D.f + ((-1 : ℤ) : ℂ) • E.f, D.p + (-1 : ℤ) • E.p) = (D.f, D.p) - (E.f, E.p)
      rw [Prod.mk_sub_mk]
      congr 1
      · ext τ; simp [sub_eq_add_neg]
      · rw [neg_one_zsmul, sub_eq_add_neg])
    (fun D n => by
      simp only [toProd, Prod.smul_mk, Prod.mk.injEq, nsmul_f', nsmul_p', natCast_zsmul, and_true]
      ext τ; simp)
    (fun D n => by
      simp only [toProd, Prod.smul_mk, Prod.mk.injEq, zsmul_f', zsmul_p', and_true]
      ext τ; simp)

end IDatum
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

variable (K : Type*) [Field K]

def redD : IDatum M H w →+ LaurentSeries K where
  toFun D := intSeriesC K D.p
  map_zero' := by simp
  map_add' D E := by simp [intSeriesC_add]

@[scoped simp] theorem redD_apply (D : IDatum M H w) : redD K D = intSeriesC K D.p := rfl

variable {K}
variable (hM : (M : K) ≠ 0)

include hM in
theorem tRed_zero (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    tRed K (0 : IDatum M H w) γ hγ = 0 := by
  rw [tRed_eq_of hM 0 γ hγ 0 0 (by simp)]
  simp

include hM in
theorem tRed_add (D E : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    tRed K (D + E) γ hγ = tRed K D γ hγ + tRed K E γ hγ := by

  let T : IDatum M H w :=
    ((M : ℤ) ^ texp E γ hγ) • trans D γ hγ + ((M : ℤ) ^ texp D γ hγ) • trans E γ hγ
  have hT : (⇑T.f : ℍ → ℂ) =
      ((M : ℂ) ^ (texp D γ hγ + texp E γ hγ)) • ((⇑(D + E).f : ℍ → ℂ) ∣[w] γ) := by
    simp only [T, IDatum.add_f', IDatum.zsmul_f', ModularForm.coe_add, ModularForm.IsGLPos.coe_smul,
      trans_f, SlashAction.add_slash, smul_add, smul_smul]
    push_cast
    rw [← pow_add, ← pow_add, add_comm (texp E γ hγ)]
  rw [tRed_eq_of hM (D + E) γ hγ _ T hT]
  simp only [T, IDatum.add_p', IDatum.zsmul_p', intSeriesC_add, intSeriesC_zsmul, tRed, smul_add, smul_smul]
  push_cast
  have hMa : ((M : K) ^ texp D γ hγ) ≠ 0 := pow_ne_zero _ hM
  have hMb : ((M : K) ^ texp E γ hγ) ≠ 0 := pow_ne_zero _ hM
  rw [pow_add]
  congr 1
  · congr 1; field_simp
  · congr 1; field_simp

def tRedHom (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) : IDatum M H w →+ LaurentSeries K where
  toFun D := tRed K D γ hγ
  map_zero' := tRed_zero hM γ hγ
  map_add' D E := tRed_add hM D E γ hγ

@[scoped simp] theorem tRedHom_apply (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (D : IDatum M H w) :
    tRedHom hM γ hγ D = tRed K D γ hγ := rfl

end Group
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end DiamondAct
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_one intSeriesC_zero intSeriesC_mul qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
p2m_open "ModularCurve~Gamma1_le_GammaH"
namespace DiamondAct

section Descent

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {w : ℤ} {K : Type*} [Field K]
variable (hM : (M : K) ≠ 0)

theorem exists_intCast_eq_coeff_intSeriesC (p : PowerSeries ℤ) (n : ℤ) :
    ∃ z : ℤ, (intSeriesC K p).coeff n = (z : K) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨PowerSeries.coeff m p, by
      rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨PowerSeries.coeff 0 p, by
        rw [Nat.cast_zero, neg_zero, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, intSeriesC,
          HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]⟩
    · refine ⟨0, ?_⟩
      rw [Int.cast_zero, intSeriesC, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      rintro ⟨a, ha⟩
      first | omega | (simp at ha; done) | (simp at ha; omega)

include hM in

theorem sum_intCast_smul_tRed_eq_zero (s : Finset (IDatum M H w)) (m : IDatum M H w → ℤ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (h : ∑ D ∈ s, (m D : K) • intSeriesC K D.p = 0) :
    ∑ D ∈ s, (m D : K) • tRed K D γ hγ = 0 := by
  let P : IDatum M H w := ∑ D ∈ s, m D • D
  have hP : intSeriesC K P.p = 0 := by
    have : redD K P = ∑ D ∈ s, redD K (m D • D) := map_sum (redD K) _ s
    rw [redD_apply] at this
    rw [this, ← h]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [redD_apply, IDatum.zsmul_p', intSeriesC_zsmul]
  have hT := tRed_eq_zero_of_red_eq_zero hM P γ hγ hP
  rw [← tRedHom_apply hM, map_sum] at hT
  rw [← hT]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [map_zsmul, tRedHom_apply, Int.cast_smul_eq_zsmul]

theorem exists_intCast_div_of_mem_bot {x : K} (hx : x ∈ (⊥ : Subfield K)) :
    ∃ y z : ℤ, (z : K) ≠ 0 ∧ x = (y : K) / (z : K) := by
  have hx' : x ∈ Subfield.closure (∅ : Set K) := by rwa [Subfield.closure_empty]
  rw [Subfield.mem_closure_iff] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  rw [Subring.closure_empty, Subring.mem_bot] at hy hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  by_cases hb : ((b : ℤ) : K) = 0
  · exact ⟨0, 1, by simp, by simp [hb]⟩
  · exact ⟨a, b, hb, rfl⟩

include hM in

theorem sum_coe_smul_tRed_eq_zero (s : Finset (IDatum M H w)) (e : IDatum M H w → (⊥ : Subfield K))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (h : ∑ D ∈ s, ((e D : K)) • intSeriesC K D.p = 0) :
    ∑ D ∈ s, ((e D : K)) • tRed K D γ hγ = 0 := by
  classical
  choose y z hz hyz using fun D : IDatum M H w => exists_intCast_div_of_mem_bot (e D).2

  let Z : K := ∏ D ∈ s, (z D : K)
  have hZ : Z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun D _ => hz D
  let m : IDatum M H w → ℤ := fun D => y D * ∏ D' ∈ s.erase D, z D'
  have hm : ∀ D ∈ s, (m D : K) = Z * (e D : K) := by
    intro D hD
    simp only [m, Z, Int.cast_mul, Int.cast_prod]
    rw [show ((e D : K)) = (y D : K) / (z D : K) from hyz D,
      ← Finset.mul_prod_erase s (fun D' => (z D' : K)) hD]
    field_simp [hz D]
  have hrel : ∑ D ∈ s, (m D : K) • intSeriesC K D.p = 0 := by
    rw [Finset.sum_congr rfl fun D hD => by rw [hm D hD, mul_smul], ← Finset.smul_sum, h, smul_zero]
  have := sum_intCast_smul_tRed_eq_zero hM s m γ hγ hrel
  rw [Finset.sum_congr rfl fun D hD => by rw [hm D hD, mul_smul], ← Finset.smul_sum, smul_eq_zero] at this
  exact this.resolve_left hZ

omit [NeZero M] in
theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (n : ℤ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem bot_smul_eq_mul (r : (⊥ : Subfield K)) (x : K) : r • x = (r : K) * x := rfl

include hM in

theorem sum_smul_tRed_eq_zero (s : Finset (IDatum M H w)) (c : IDatum M H w → K)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (h : ∑ D ∈ s, c D • intSeriesC K D.p = 0) :
    ∑ D ∈ s, c D • tRed K D γ hγ = 0 := by
  classical
  let F : Subfield K := ⊥
  let b := Module.Basis.ofVectorSpace F K

  have hA : ∀ i, ∑ D ∈ s, ((b.repr (c D) i : F) : K) • intSeriesC K D.p = 0 := by
    intro i
    ext n
    rw [coeff_finset_sum]
    simp only [HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
    have hn : ∑ D ∈ s, c D * (intSeriesC K D.p).coeff n = 0 := by
      have := congrArg (fun x : LaurentSeries K => x.coeff n) h
      simpa only [coeff_finset_sum, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero] using this

    have hr : ∀ D : IDatum M H w, ∃ r : F, (r : K) = (intSeriesC K D.p).coeff n := fun D => by
      obtain ⟨zz, hzz⟩ := exists_intCast_eq_coeff_intSeriesC (K := K) D.p n
      exact ⟨⟨(zz : K), by simp [F]⟩, hzz.symm⟩
    choose r hr using hr

    have h1 : ∑ D ∈ s, r D • c D = 0 := by
      rw [← hn]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [bot_smul_eq_mul, hr, mul_comm]
    have h2 : ∑ D ∈ s, r D * b.repr (c D) i = 0 := by
      have := congrArg (fun x => b.repr x i) h1
      simpa only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] using this
    have h3 := congrArg (F.subtype) h2
    rw [map_sum, map_zero] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun D _ => ?_
    simp only [map_mul, Subfield.coe_subtype, hr]
    rw [mul_comm]

  have hB : ∀ i, ∑ D ∈ s, ((b.repr (c D) i : F) : K) • tRed K D γ hγ = 0 :=
    fun i => sum_coe_smul_tRed_eq_zero hM s (fun D => b.repr (c D) i) γ hγ (hA i)

  let S := s.biUnion fun D => (b.repr (c D)).support
  have hc : ∀ D ∈ s, c D = ∑ i ∈ S, ((b.repr (c D) i : F) : K) * (b i : K) := by
    intro D hD
    conv_lhs => rw [← b.linearCombination_repr (c D)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun D => (b.repr (c D)).support) hD)
        _ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bot_smul_eq_mul]
  calc ∑ D ∈ s, c D • tRed K D γ hγ
      = ∑ D ∈ s, ∑ i ∈ S, (b i : K) • (((b.repr (c D) i : F) : K) • tRed K D γ hγ) := by
        refine Finset.sum_congr rfl fun D hD => ?_
        nth_rewrite 1 [hc D hD]
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm, mul_smul]
    _ = ∑ i ∈ S, (b i : K) • ∑ D ∈ s, ((b.repr (c D) i : F) : K) • tRed K D γ hγ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.smul_sum]
    _ = 0 := by simp [hB]

end Descent
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end DiamondAct
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_one intSeriesC_zero intSeriesC_mul qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
p2m_open "ModularCurve~Gamma1_le_GammaH"
namespace DiamondAct

section Formal

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {w w₁ w₂ : ℤ} {K : Type*} [Field K]
variable (hM : (M : K) ≠ 0)

def ev (K : Type*) [Field K] (w : ℤ) : (IDatum M H w →₀ K) →ₗ[K] LaurentSeries K :=
  Finsupp.linearCombination K (fun D : IDatum M H w => intSeriesC K D.p)

def evT (K : Type*) [Field K] (w : ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (IDatum M H w →₀ K) →ₗ[K] LaurentSeries K :=
  Finsupp.linearCombination K (fun D : IDatum M H w => tRed K D γ hγ)

omit [NeZero M] in

theorem smul_mul_smul' (a b : K) (x y : LaurentSeries K) : (a • x) * (b • y) = (a * b) • (x * y) := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, map_mul]; ring

@[scoped simp] theorem ev_single (D : IDatum M H w) (c : K) : ev K w (Finsupp.single D c) = c • intSeriesC K D.p := by
  simp [ev]

@[scoped simp] theorem evT_single (D : IDatum M H w) (c : K) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    evT K w γ hγ (Finsupp.single D c) = c • tRed K D γ hγ := by
  simp [evT]

theorem ev_apply (l : IDatum M H w →₀ K) : ev K w l = ∑ D ∈ l.support, l D • intSeriesC K D.p := by
  rw [ev, Finsupp.linearCombination_apply, Finsupp.sum]

theorem evT_apply (l : IDatum M H w →₀ K) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    evT K w γ hγ l = ∑ D ∈ l.support, l D • tRed K D γ hγ := by
  rw [evT, Finsupp.linearCombination_apply, Finsupp.sum]

include hM in

theorem evT_eq_zero_of_ev_eq_zero (l : IDatum M H w →₀ K) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (h : ev K w l = 0) : evT K w γ hγ l = 0 := by
  rw [ev_apply] at h
  rw [evT_apply]
  exact sum_smul_tRed_eq_zero hM l.support l γ hγ h

include hM in
theorem evT_eq_of_ev_eq {l l' : IDatum M H w →₀ K} (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (h : ev K w l = ev K w l') : evT K w γ hγ l = evT K w γ hγ l' := by
  rw [← sub_eq_zero, ← map_sub] at h ⊢
  exact evT_eq_zero_of_ev_eq_zero hM _ γ hγ h

def fmul (l : IDatum M H w₁ →₀ K) (l' : IDatum M H w₂ →₀ K) : IDatum M H (w₁ + w₂) →₀ K :=
  l.sum fun D a => l'.sum fun E b => Finsupp.single (D.mul E) (a * b)

theorem ev_fmul (l : IDatum M H w₁ →₀ K) (l' : IDatum M H w₂ →₀ K) :
    ev K (w₁ + w₂) (fmul l l') = ev K w₁ l * ev K w₂ l' := by
  classical
  rw [fmul, map_finsuppSum, ev_apply l, ev_apply l', Finset.sum_mul_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [map_finsuppSum, Finsupp.sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [ev_single, IDatum.mul_p, intSeriesC_mul, smul_mul_smul']

include hM in

theorem tRed_mul (D : IDatum M H w₁) (E : IDatum M H w₂) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    tRed K (D.mul E) γ hγ = tRed K D γ hγ * tRed K E γ hγ := by
  have hT : (⇑((trans D γ hγ).mul (trans E γ hγ)).f : ℍ → ℂ) =
      ((M : ℂ) ^ (texp D γ hγ + texp E γ hγ)) • ((⇑(D.mul E).f : ℍ → ℂ) ∣[w₁ + w₂] γ) := by
    rw [IDatum.mul_f, trans_f, trans_f, IDatum.mul_f, ModularForm.mul_slash_SL2, pow_add]
    funext τ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [tRed_eq_of hM (D.mul E) γ hγ _ _ hT, IDatum.mul_p, intSeriesC_mul, tRed, tRed, smul_mul_smul',
    pow_add, mul_inv]

include hM in
theorem evT_fmul (l : IDatum M H w₁ →₀ K) (l' : IDatum M H w₂ →₀ K) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    evT K (w₁ + w₂) γ hγ (fmul l l') = evT K w₁ γ hγ l * evT K w₂ γ hγ l' := by
  classical
  rw [fmul, map_finsuppSum, evT_apply l, evT_apply l', Finset.sum_mul_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [map_finsuppSum, Finsupp.sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [evT_single, tRed_mul hM, smul_mul_smul']

def ftrans (l : IDatum M H w →₀ K) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    IDatum M H w →₀ K :=
  l.sum fun D a => Finsupp.single (trans D γ hγ) (a * ((M : K) ^ texp D γ hγ)⁻¹)

theorem ev_ftrans (l : IDatum M H w →₀ K) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ev K w (ftrans l γ hγ) = evT K w γ hγ l := by
  classical
  rw [ftrans, map_finsuppSum, evT_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [ev_single, tRed, smul_smul]

include hM in

theorem tRed_mul_right (D : IDatum M H w) (γ δ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 M) :
    tRed K D (γ * δ) (mul_mem hγ hδ) = ((M : K) ^ texp D γ hγ)⁻¹ • tRed K (trans D γ hγ) δ hδ := by
  have hT : (⇑(trans (trans D γ hγ) δ hδ).f : ℍ → ℂ) =
      ((M : ℂ) ^ (texp (trans D γ hγ) δ hδ + texp D γ hγ)) • ((⇑D.f : ℍ → ℂ) ∣[w] (γ * δ)) := by
    rw [trans_f, trans_f, smul_SL_slash, smul_smul, SlashAction.slash_mul, pow_add]
  rw [tRed_eq_of hM D (γ * δ) (mul_mem hγ hδ) _ _ hT, tRed, smul_smul, pow_add, mul_inv, mul_comm]

include hM in
theorem evT_mul_right (l : IDatum M H w →₀ K) (γ δ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 M) :
    evT K w (γ * δ) (mul_mem hγ hδ) l = evT K w δ hδ (ftrans l γ hγ) := by
  classical
  rw [ftrans, map_finsuppSum, evT_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [evT_single, tRed_mul_right hM, smul_smul]

include hM in

theorem tRed_of_mem_GammaH (D : IDatum M H w) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hγH : γ ∈ CohCarrier.GammaH M H) : tRed K D γ hγ = intSeriesC K D.p := by
  rw [tRed_eq_of hM D γ hγ 0 D (by rw [pow_zero, one_smul, D.hinv γ hγH])]
  simp

include hM in
theorem evT_of_mem_GammaH (l : IDatum M H w →₀ K) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hγH : γ ∈ CohCarrier.GammaH M H) : evT K w γ hγ l = ev K w l := by
  rw [evT_apply, ev_apply]
  exact Finset.sum_congr rfl fun D _ => by rw [tRed_of_mem_GammaH hM D γ hγ hγH]

include hM in

theorem evT_ne_zero (l : IDatum M H w →₀ K) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (h : ev K w l ≠ 0) : evT K w γ hγ l ≠ 0 := by
  intro h0
  apply h
  have h1 : ev K w (ftrans l γ hγ) = 0 := by rw [ev_ftrans]; exact h0
  have h2 := evT_eq_zero_of_ev_eq_zero hM _ γ⁻¹ (inv_mem hγ) h1
  rw [← evT_mul_right hM l γ γ⁻¹ hγ (inv_mem hγ)] at h2
  have h3 : evT K w (γ * γ⁻¹) (mul_mem hγ (inv_mem hγ)) l = ev K w l :=
    evT_of_mem_GammaH hM l _ _ (by rw [mul_inv_cancel]; exact one_mem _)
  rw [← h3, h2]

end Formal
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end DiamondAct
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_one intSeriesC_zero intSeriesC_mul qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
p2m_open "ModularCurve~Gamma1_le_GammaH"
namespace DiamondAct

local notation "Γᴴℝ" M "," H => ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Field

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {w w₁ w₂ : ℤ} {K : Type*} [Field K]
variable (hM : (M : K) ≠ 0)

def oneD : IDatum M H 0 :=
  ⟨1, 1, by
    show IsIntegralQExp (⇑(1 : ModularForm (Γᴴℝ M, H) 0)) 1
    rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one⟩

@[scoped simp] theorem oneD_p : (oneD : IDatum M H 0).p = 1 := rfl
@[scoped simp] theorem oneD_f : (⇑(oneD : IDatum M H 0).f : ℍ → ℂ) = 1 := ModularForm.one_coe_eq_one

omit [NeZero M] in
theorem C_eq_algebraMap' (c : K) : HahnSeries.C c = algebraMap K (LaurentSeries K) c := by
  exact (HahnSeries.ofPowerSeries_C (Γ := ℤ) (R := K) c).symm

@[scoped simp] theorem ev_single_oneD (c : K) : ev K 0 (Finsupp.single (oneD : IDatum M H 0) c) = algebraMap K _ c := by
  rw [ev_single, oneD_p, intSeriesC_one, ← HahnSeries.C_mul_eq_smul, mul_one, C_eq_algebraMap']

include hM in
theorem tRed_oneD (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    tRed K (oneD : IDatum M H 0) γ hγ = 1 := by
  rw [tRed_eq_of hM oneD γ hγ 0 oneD (by rw [pow_zero, one_smul, oneD_f, ModularForm.is_invariant_one])]
  simp [intSeriesC_one]

include hM in
@[scoped simp] theorem evT_single_oneD (c : K) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    evT K 0 γ hγ (Finsupp.single (oneD : IDatum M H 0) c) = algebraMap K _ c := by
  rw [evT_single, tRed_oneD hM, ← HahnSeries.C_mul_eq_smul, mul_one, C_eq_algebraMap']

variable (K) in

def IsRep (x : LaurentSeries K) (w : ℤ) (l l' : IDatum M H w →₀ K) : Prop :=
  ev K w l' ≠ 0 ∧ x = ev K w l / ev K w l'

def Efield (K : Type*) [Field K] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IntermediateField K (LaurentSeries K) where
  carrier := {x | ∃ (w : ℤ) (l l' : IDatum M H w →₀ K), IsRep K x w l l'}
  mul_mem' := by
    rintro x y ⟨w, l, l', hl', rfl⟩ ⟨u, m, m', hm', rfl⟩
    exact ⟨w + u, fmul l m, fmul l' m', by rw [ev_fmul]; exact mul_ne_zero hl' hm',
      by rw [ev_fmul, ev_fmul, div_mul_div_comm]⟩
  one_mem' := ⟨0, Finsupp.single oneD 1, Finsupp.single oneD 1, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨w, l, l', hl', rfl⟩ ⟨u, m, m', hm', rfl⟩
    refine ⟨w + u, fmul l m' + fmul l' m, fmul l' m', by rw [ev_fmul]; exact mul_ne_zero hl' hm', ?_⟩
    rw [map_add, ev_fmul, ev_fmul, ev_fmul, div_add_div _ _ hl' hm']
  zero_mem' := ⟨0, 0, Finsupp.single oneD 1, by simp, by simp⟩
  algebraMap_mem' c := ⟨0, Finsupp.single oneD c, Finsupp.single oneD 1, by simp,
    by rw [ev_single_oneD, ev_single_oneD, map_one, div_one]⟩
  inv_mem' := by
    rintro x ⟨w, l, l', hl', rfl⟩
    by_cases hl : ev K w l = 0
    · refine ⟨0, 0, Finsupp.single oneD 1, by simp, ?_⟩
      simp [hl]
    · exact ⟨w, l', l, hl, by rw [inv_div]⟩

theorem mem_Efield_iff {x : LaurentSeries K} :
    x ∈ Efield K M H ↔ ∃ (w : ℤ) (l l' : IDatum M H w →₀ K), IsRep K x w l l' := Iff.rfl

theorem exists_mem_support_ne_zero {l : IDatum M H w →₀ K} (h : ev K w l ≠ 0) :
    ∃ G ∈ l.support, intSeriesC K G.p ≠ 0 := by
  by_contra! hcon
  apply h
  rw [ev_apply]
  exact Finset.sum_eq_zero fun D hD => by rw [hcon D hD, smul_zero]

theorem ev_div_mem {l : IDatum M H w →₀ K} (G : IDatum M H w) (hG : intSeriesC K G.p ≠ 0) :
    ev K w l / intSeriesC K G.p ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) := by
  rw [ev_apply, Finset.sum_div]
  refine sum_mem fun D _ => ?_
  rw [← HahnSeries.C_mul_eq_smul, mul_div_assoc]
  refine mul_mem ?_ (div_mem_qExpFunctionFieldC D.f G.f D.hp G.hp hG)
  rw [C_eq_algebraMap']
  exact IntermediateField.algebraMap_mem _ _

theorem Efield_eq : Efield K M H = qExpFunctionFieldC K (CohCarrier.GammaH M H) := by
  apply le_antisymm
  · rintro x ⟨w, l, l', hl', rfl⟩
    obtain ⟨G, -, hG⟩ := exists_mem_support_ne_zero hl'
    rw [← div_div_div_cancel_right₀ hG (ev K w l) (ev K w l')]
    exact div_mem (ev_div_mem G hG) (ev_div_mem G hG)
  · rw [qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
    rintro x ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    exact ⟨k, Finsupp.single ⟨f, pf, hf⟩ 1, Finsupp.single ⟨g, pg, hg⟩ 1, by simpa using hg0, by simp⟩

theorem exists_rep {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H)) :
    ∃ (w : ℤ) (l l' : IDatum M H w →₀ K), IsRep K x w l l' := by
  rwa [← Efield_eq] at hx

def rhoVal (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (x : LaurentSeries K)
    (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K :=
  evT K _ γ hγ (exists_rep hx).choose_spec.choose / evT K _ γ hγ (exists_rep hx).choose_spec.choose_spec.choose

include hM in

theorem evT_div_eq_of_isRep {x : LaurentSeries K} {w u : ℤ} {l l' : IDatum M H w →₀ K}
    {m m' : IDatum M H u →₀ K} (h1 : IsRep K x w l l') (h2 : IsRep K x u m m')
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    evT K w γ hγ l / evT K w γ hγ l' = evT K u γ hγ m / evT K u γ hγ m' := by
  obtain ⟨hl', hx1⟩ := h1
  obtain ⟨hm', hx2⟩ := h2
  have hcross : ev K (w + u) (fmul l m') = ev K (w + u) (fmul l' m) := by
    rw [ev_fmul, ev_fmul]
    rw [hx1, div_eq_div_iff hl' hm'] at hx2
    rw [hx2, mul_comm]
  have hT := evT_eq_of_ev_eq hM γ hγ hcross
  rw [evT_fmul hM, evT_fmul hM] at hT
  rw [div_eq_div_iff (evT_ne_zero hM l' γ hγ hl') (evT_ne_zero hM m' γ hγ hm'), hT, mul_comm]

include hM in
theorem rhoVal_eq {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    {u : ℤ} {m m' : IDatum M H u →₀ K} (h : IsRep K x u m m')
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    rhoVal γ hγ x hx = evT K u γ hγ m / evT K u γ hγ m' :=
  evT_div_eq_of_isRep hM (exists_rep hx).choose_spec.choose_spec.choose_spec h γ hγ

include hM in

theorem isRep_rhoVal {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    {u : ℤ} {m m' : IDatum M H u →₀ K} (h : IsRep K x u m m')
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    IsRep K (rhoVal γ hγ x hx) u (ftrans m γ hγ) (ftrans m' γ hγ) := by
  refine ⟨by rw [ev_ftrans]; exact evT_ne_zero hM m' γ hγ h.1, ?_⟩
  rw [ev_ftrans, ev_ftrans, rhoVal_eq hM hx h γ hγ]

include hM in
theorem rhoVal_mem {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    rhoVal γ hγ x hx ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) := by
  obtain ⟨u, m, m', h⟩ := exists_rep hx
  rw [← Efield_eq]
  exact ⟨u, _, _, isRep_rhoVal hM hx h γ hγ⟩

include hM in
theorem rhoVal_add {x y : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hy : y ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    rhoVal γ hγ (x + y) (add_mem hx hy) = rhoVal γ hγ x hx + rhoVal γ hγ y hy := by
  obtain ⟨w, l, l', hl⟩ := exists_rep hx
  obtain ⟨u, m, m', hm⟩ := exists_rep hy
  have hsum : IsRep K (x + y) (w + u) (fmul l m' + fmul l' m) (fmul l' m') := by
    refine ⟨by rw [ev_fmul]; exact mul_ne_zero hl.1 hm.1, ?_⟩
    rw [hl.2, hm.2, map_add, ev_fmul, ev_fmul, ev_fmul, div_add_div _ _ hl.1 hm.1]
  rw [rhoVal_eq hM _ hsum γ hγ, rhoVal_eq hM hx hl γ hγ, rhoVal_eq hM hy hm γ hγ, map_add,
    evT_fmul hM, evT_fmul hM, evT_fmul hM,
    div_add_div _ _ (evT_ne_zero hM l' γ hγ hl.1) (evT_ne_zero hM m' γ hγ hm.1)]

include hM in
theorem rhoVal_mul {x y : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hy : y ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    rhoVal γ hγ (x * y) (mul_mem hx hy) = rhoVal γ hγ x hx * rhoVal γ hγ y hy := by
  obtain ⟨w, l, l', hl⟩ := exists_rep hx
  obtain ⟨u, m, m', hm⟩ := exists_rep hy
  have hprod : IsRep K (x * y) (w + u) (fmul l m) (fmul l' m') := by
    refine ⟨by rw [ev_fmul]; exact mul_ne_zero hl.1 hm.1, ?_⟩
    rw [hl.2, hm.2, ev_fmul, ev_fmul, div_mul_div_comm]
  rw [rhoVal_eq hM _ hprod γ hγ, rhoVal_eq hM hx hl γ hγ, rhoVal_eq hM hy hm γ hγ,
    evT_fmul hM, evT_fmul hM, div_mul_div_comm]

include hM in
theorem rhoVal_algebraMap (c : K) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    rhoVal γ hγ (algebraMap K (LaurentSeries K) c)
      (IntermediateField.algebraMap_mem (qExpFunctionFieldC K (CohCarrier.GammaH M H)) c) =
      algebraMap K (LaurentSeries K) c := by
  have h : IsRep K (algebraMap K (LaurentSeries K) c) 0 (Finsupp.single (oneD : IDatum M H 0) c)
      (Finsupp.single oneD 1) := ⟨by simp, by rw [ev_single_oneD, ev_single_oneD, map_one, div_one]⟩
  rw [rhoVal_eq hM _ h γ hγ, evT_single_oneD hM, evT_single_oneD hM, map_one, div_one]

def rhoHom (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M H) where
  toFun x := ⟨rhoVal γ hγ x x.2, rhoVal_mem hM x.2 γ hγ⟩
  map_one' := by
    apply Subtype.ext
    have h := rhoVal_algebraMap (M := M) (H := H) hM (1 : K) γ hγ
    simp only [map_one] at h
    exact h
  map_mul' x y := Subtype.ext (rhoVal_mul hM x.2 y.2 γ hγ)
  map_zero' := by
    apply Subtype.ext
    have h := rhoVal_algebraMap (M := M) (H := H) hM (0 : K) γ hγ
    simp only [map_zero] at h
    exact h
  map_add' x y := Subtype.ext (rhoVal_add hM x.2 y.2 γ hγ)
  commutes' c := Subtype.ext (rhoVal_algebraMap hM c γ hγ)

@[scoped simp] theorem coe_rhoHom (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) :
    ((rhoHom hM γ hγ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) = rhoVal γ hγ x x.2 := rfl

include hM in

theorem rhoVal_rhoVal {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (γ δ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M) :
    rhoVal δ hδ (rhoVal γ hγ x hx) (rhoVal_mem hM hx γ hγ) = rhoVal (γ * δ) (mul_mem hγ hδ) x hx := by
  obtain ⟨w, l, l', hl⟩ := exists_rep hx
  rw [rhoVal_eq hM _ (isRep_rhoVal hM hx hl γ hγ) δ hδ, rhoVal_eq hM hx hl (γ * δ) (mul_mem hγ hδ),
    evT_mul_right hM, evT_mul_right hM]

include hM in

theorem rhoVal_of_mem_GammaH {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγH : γ ∈ CohCarrier.GammaH M H) :
    rhoVal γ hγ x hx = x := by
  obtain ⟨w, l, l', hl⟩ := exists_rep hx
  rw [rhoVal_eq hM hx hl γ hγ, evT_of_mem_GammaH hM _ _ _ hγH, evT_of_mem_GammaH hM _ _ _ hγH, ← hl.2]

omit [NeZero M] in

theorem commutator_mem_GammaH (γ δ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 M) :
    γ * δ * γ⁻¹ * δ⁻¹ ∈ CohCarrier.GammaH M H := by
  let c : CongruenceSubgroup.Gamma0 M := ⟨γ, hγ⟩ * ⟨δ, hδ⟩ * ⟨γ, hγ⟩⁻¹ * ⟨δ, hδ⟩⁻¹
  have hc : (c : SL(2, ℤ)) = γ * δ * γ⁻¹ * δ⁻¹ := rfl
  have hu : CohCarrier.gamma0Units M c = 1 := by
    simp only [c, map_mul, map_inv]
    rw [mul_comm (CohCarrier.gamma0Units M ⟨γ, hγ⟩) (CohCarrier.gamma0Units M ⟨δ, hδ⟩)]
    group
  rw [← hc, CohCarrier.mem_GammaH_iff]
  exact ⟨c.2, by rw [Subtype.coe_eta, hu]; exact one_mem H⟩

include hM in

theorem rhoVal_mul_comm {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (γ δ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M) :
    rhoVal (γ * δ) (mul_mem hγ hδ) x hx = rhoVal (δ * γ) (mul_mem hδ hγ) x hx := by
  have hc := commutator_mem_GammaH (M := M) (H := H) γ δ hγ hδ
  have hc0 : γ * δ * γ⁻¹ * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H hc
  have key : rhoVal ((γ * δ * γ⁻¹ * δ⁻¹) * (δ * γ)) (mul_mem hc0 (mul_mem hδ hγ)) x hx =
      rhoVal (δ * γ) (mul_mem hδ hγ) x hx := by
    rw [← rhoVal_rhoVal hM hx _ _ hc0 (mul_mem hδ hγ)]
    congr 1
    exact rhoVal_of_mem_GammaH hM hx _ hc0 hc
  have he : (γ * δ * γ⁻¹ * δ⁻¹) * (δ * γ) = γ * δ := by group
  simp only [he] at key
  exact key

def rhoEquiv (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M H) :=
  AlgEquiv.ofAlgHom (rhoHom hM γ hγ) (rhoHom hM γ⁻¹ (inv_mem hγ))
    (by
      refine AlgHom.ext fun x => Subtype.ext ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, coe_rhoHom, AlgHom.coe_id, id_eq]
      rw [rhoVal_rhoVal hM]
      exact rhoVal_of_mem_GammaH hM x.2 (γ⁻¹ * γ) (mul_mem (inv_mem hγ) hγ)
        (by rw [inv_mul_cancel]; exact one_mem _))
    (by
      refine AlgHom.ext fun x => Subtype.ext ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, coe_rhoHom, AlgHom.coe_id, id_eq]
      rw [rhoVal_rhoVal hM]
      exact rhoVal_of_mem_GammaH hM x.2 (γ * γ⁻¹) (mul_mem hγ (inv_mem hγ))
        (by rw [mul_inv_cancel]; exact one_mem _))

@[scoped simp] theorem coe_rhoEquiv (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) :
    ((rhoEquiv hM γ hγ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
      rhoVal γ hγ x x.2 := rfl

def rho : CongruenceSubgroup.Gamma0 M →*
    (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M H)) where
  toFun γ := rhoEquiv hM γ.1 γ.2
  map_one' := by
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [coe_rhoEquiv, AlgEquiv.one_apply]
    exact rhoVal_of_mem_GammaH hM x.2 (1 : SL(2, ℤ)) (one_mem _) (one_mem _)
  map_mul' γ δ := by
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    change rhoVal (γ.1 * δ.1) (mul_mem γ.2 δ.2) (x : LaurentSeries K) x.2 =
      rhoVal γ.1 γ.2 (rhoVal δ.1 δ.2 (x : LaurentSeries K) x.2) (rhoVal_mem hM x.2 δ.1 δ.2)
    rw [rhoVal_rhoVal hM x.2 δ.1 γ.1 δ.2 γ.2]
    exact rhoVal_mul_comm hM x.2 γ.1 δ.1 γ.2 δ.2

end Field
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end DiamondAct
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_one intSeriesC_zero intSeriesC_mul qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
p2m_open "ModularCurve~Gamma1_le_GammaH"
namespace DiamondAct

local notation "Γᴴℝ" M "," H => ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Spec

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {w : ℤ} {K : Type*} [Field K]
variable (hM : (M : K) ≠ 0)

theorem slash_neg_one (F : ℍ → ℂ) (k : ℤ) : F ∣[k] (-1 : SL(2, ℤ)) = ((-1 : ℂ) ^ k) • F := by
  funext τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (-1 : SL(2, ℤ)) • τ = τ := by simp
  have h2 : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
      (-1 : SL(2, ℤ)))) (τ : ℂ) = -1 := by
    simp [denom]
  rw [h1, h2, mul_comm]
  congr 1
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

def sgn (w : ℤ) : ℤ := if Even w then 1 else -1

theorem sgn_ne_zero (w : ℤ) : sgn w ≠ 0 := by unfold sgn; split_ifs <;> decide

theorem cast_sgn (w : ℤ) : ((sgn w : ℤ) : ℂ) = (-1 : ℂ) ^ w := by
  unfold sgn
  rcases Int.even_or_odd w with hw | hw
  · rw [if_pos hw, hw.neg_one_zpow]; simp
  · rw [if_neg (Int.not_even_iff_odd.mpr hw), hw.neg_one_zpow]; simp

include hM in
theorem tRed_neg_one (D : IDatum M H w) (h1 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M) :
    tRed K D (-1) h1 = ((sgn w : ℤ) : K) • intSeriesC K D.p := by
  have hE : (⇑((sgn w) • D).f : ℍ → ℂ) = ((M : ℂ) ^ 0) • ((⇑D.f : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ))) := by
    rw [IDatum.zsmul_f', ModularForm.IsGLPos.coe_smul, pow_zero, one_smul, slash_neg_one, cast_sgn]
  rw [tRed_eq_of hM D (-1) h1 0 _ hE, IDatum.zsmul_p', intSeriesC_zsmul]
  simp

include hM in

theorem rhoVal_neg_one {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (h1 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M) : rhoVal (-1) h1 x hx = x := by
  obtain ⟨w, l, l', hl⟩ := exists_rep hx

  have hsgn : ((sgn w : ℤ) : K) ≠ 0 := by
    unfold sgn; split_ifs <;> simp
  have hev : ∀ m : IDatum M H w →₀ K,
      evT K w (-1) h1 m = HahnSeries.C ((sgn w : ℤ) : K) * ev K w m := by
    intro m
    rw [evT_apply, ev_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun D _ => by
      rw [tRed_neg_one hM, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul]
      ring
  have hC : HahnSeries.C ((sgn w : ℤ) : K) ≠ (0 : LaurentSeries K) := by
    intro h
    exact hsgn (HahnSeries.C_injective (h.trans (map_zero _).symm))
  rw [rhoVal_eq hM hx hl (-1) h1, hev, hev, hl.2, mul_div_mul_left _ _ hC]

include hM in

theorem rhoVal_eq_self_of_gamma0 {k : ℤ}
    (f g : ModularForm ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp (⇑f) pf) (hg : IsIntegralQExp (⇑g) pg)
    (hg0 : intSeriesC K pg ≠ 0) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hx : intSeriesC K pf / intSeriesC K pg ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H)) :
    rhoVal γ hγ (intSeriesC K pf / intSeriesC K pg) hx = intSeriesC K pf / intSeriesC K pg := by
  let Df : IDatum M H k := ⟨restrictForm (Subgroup.map_mono (CohCarrier.GammaH_le_Gamma0 H)) f, pf, hf⟩
  let Dg : IDatum M H k := ⟨restrictForm (Subgroup.map_mono (CohCarrier.GammaH_le_Gamma0 H)) g, pg, hg⟩
  have hrep : IsRep K (intSeriesC K pf / intSeriesC K pg) k (Finsupp.single Df 1) (Finsupp.single Dg 1) :=
    ⟨by simpa using hg0, by simp [Df, Dg]⟩
  have hinvf : tRed K Df γ hγ = intSeriesC K pf := by
    rw [tRed_eq_of hM Df γ hγ 0 Df (by
      rw [pow_zero, one_smul]
      exact (SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hγ)).symm)]
    simp [Df]
  have hinvg : tRed K Dg γ hγ = intSeriesC K pg := by
    rw [tRed_eq_of hM Dg γ hγ 0 Dg (by
      rw [pow_zero, one_smul]
      exact (SlashInvariantForm.slash_action_eqn g _ (Subgroup.mem_map_of_mem _ hγ)).symm)]
    simp [Dg]
  rw [rhoVal_eq hM hx hrep γ hγ, evT_single, evT_single, hinvf, hinvg, one_smul, one_smul]

include hM in

theorem rho_apply_eq_self_of_mem_gamma0 (γ : CongruenceSubgroup.Gamma0 M)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) ∈ qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) :
    rho hM γ x = x := by
  classical
  let Fix : IntermediateField K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) :=
    IntermediateField.fixedField (Subgroup.zpowers (rho hM γ))
  have hgen : qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) ≤ IntermediateField.lift Fix := by
    rw [qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hmem : intSeriesC K pf / intSeriesC K pg ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) :=
      qExpFunctionFieldC_mono K (CohCarrier.GammaH_le_Gamma0 H) (div_mem_qExpFunctionFieldC f g hf hg hg0)
    have hfix : rho hM γ ⟨_, hmem⟩ = ⟨_, hmem⟩ :=
      Subtype.ext (rhoVal_eq_self_of_gamma0 hM f g hf hg hg0 γ.1 γ.2 hmem)
    have hstab : Subgroup.zpowers (rho hM γ) ≤
        MulAction.stabilizer (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
          qExpFunctionFieldC K (CohCarrier.GammaH M H)) (⟨_, hmem⟩ : qExpFunctionFieldC K (CohCarrier.GammaH M H)) :=
      Subgroup.zpowers_le.mpr hfix
    exact (IntermediateField.mem_lift (⟨_, hmem⟩ : qExpFunctionFieldC K (CohCarrier.GammaH M H))).mpr
      fun m => hstab m.2
  have hx' : x ∈ Fix := (IntermediateField.mem_lift x).mp (hgen hx)
  exact hx' ⟨_, Subgroup.mem_zpowers _⟩

include hM in

theorem rho_apply_generator (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
    (f g f₁ g₁ : ModularForm (Γᴴℝ M, H) k) {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (hc : c ≠ 0)
    (hf : IsIntegralQExp (⇑f) pf) (hg : IsIntegralQExp (⇑g) pg)
    (hf₁ : IsIntegralQExp (⇑f₁) pf₁) (hg₁ : IsIntegralQExp (⇑g₁) pg₁)
    (ef : (⇑f₁ : ℍ → ℂ) = c • ((⇑f : ℍ → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
    (eg : (⇑g₁ : ℍ → ℂ) = c • ((⇑g : ℍ → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
    (hg0 : intSeriesC K pg ≠ 0) (hg₁0 : intSeriesC K pg₁ ≠ 0) :
    ((rho hM γ ⟨intSeriesC K pf / intSeriesC K pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
        qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
      intSeriesC K pf₁ / intSeriesC K pg₁ := by
  let Df : IDatum M H k := ⟨f, pf, hf⟩
  let Dg : IDatum M H k := ⟨g, pg, hg⟩
  have hrep : IsRep K (intSeriesC K pf / intSeriesC K pg) k (Finsupp.single Df 1) (Finsupp.single Dg 1) :=
    ⟨by simpa using hg0, by simp [Df, Dg]⟩
  change rhoVal γ.1 γ.2 (intSeriesC K pf / intSeriesC K pg) (div_mem_qExpFunctionFieldC f g hf hg hg0) = _
  rw [rhoVal_eq hM (div_mem_qExpFunctionFieldC f g hf hg hg0) hrep γ.1 γ.2, evT_single, evT_single,
    one_smul, one_smul]

  have hfun : (((M : ℤ) ^ texp Df γ.1 γ.2 : ℤ) : ℂ) • (⇑(f₁.mul (trans Dg γ.1 γ.2).f) : ℍ → ℂ) =
      (((M : ℤ) ^ texp Dg γ.1 γ.2 : ℤ) : ℂ) • (⇑(g₁.mul (trans Df γ.1 γ.2).f) : ℍ → ℂ) := by
    push_cast
    rw [ModularForm.coe_mul, ModularForm.coe_mul, trans_f, trans_f, ef, eg]
    funext τ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Df, Dg, ModularForm.SL_slash]
    ring
  have hZ := smul_eq_smul_of_coe _ _ (isIntegralQExp_mul hf₁ (trans Dg γ.1 γ.2).hp)
    (isIntegralQExp_mul hg₁ (trans Df γ.1 γ.2).hp) _ _ hfun
  have hK := congrArg (intSeriesC K) hZ
  rw [intSeriesC_zsmul, intSeriesC_zsmul, intSeriesC_mul, intSeriesC_mul] at hK
  push_cast at hK
  have htg : tRed K Dg γ.1 γ.2 ≠ 0 := by
    have := evT_ne_zero hM (Finsupp.single Dg (1 : K)) γ.1 γ.2 (by simpa using hg0)
    simpa using this
  rw [div_eq_div_iff htg hg₁0, tRed, tRed]
  have hMa : ((M : K) ^ texp Df γ.1 γ.2) ≠ 0 := pow_ne_zero _ hM
  have hMb : ((M : K) ^ texp Dg γ.1 γ.2) ≠ 0 := pow_ne_zero _ hM

  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul] at hK
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul]
  have ha : HahnSeries.C ((M : K) ^ texp Df γ.1 γ.2) * HahnSeries.C (((M : K) ^ texp Df γ.1 γ.2)⁻¹) =
      (1 : LaurentSeries K) := by rw [← map_mul, mul_inv_cancel₀ hMa, map_one]
  have hb : HahnSeries.C ((M : K) ^ texp Dg γ.1 γ.2) * HahnSeries.C (((M : K) ^ texp Dg γ.1 γ.2)⁻¹) =
      (1 : LaurentSeries K) := by rw [← map_mul, mul_inv_cancel₀ hMb, map_one]
  have hAB : HahnSeries.C ((M : K) ^ texp Df γ.1 γ.2) * HahnSeries.C ((M : K) ^ texp Dg γ.1 γ.2) ≠
      (0 : LaurentSeries K) := by
    rw [← map_mul]
    intro h
    exact (mul_ne_zero hMa hMb) (HahnSeries.C_injective (h.trans (map_zero _).symm))
  refine mul_left_cancel₀ hAB ?_
  linear_combination (HahnSeries.C ((M : K) ^ texp Dg γ.1 γ.2) * intSeriesC K (trans Df γ.1 γ.2).p *
      intSeriesC K pg₁) * ha -
    (HahnSeries.C ((M : K) ^ texp Df γ.1 γ.2) * intSeriesC K pf₁ * intSeriesC K (trans Dg γ.1 γ.2).p) * hb - hK

theorem main (K : Type*) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) = -1 → ρ γ = 1) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)),
        (x : LaurentSeries K) ∈ qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) → ρ γ x = x) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
        (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
        (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
        (_ : IsIntegralQExp f₁ pf₁) (_ : IsIntegralQExp g₁ pg₁)
        (_ : (⇑f₁ : ℍ → ℂ) = c • ((⇑f : ℍ → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (_ : (⇑g₁ : ℍ → ℂ) = c • ((⇑g : ℍ → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (hg0 : intSeriesC K pg ≠ 0) (_ : intSeriesC K pg₁ ≠ 0),
          ((ρ γ ⟨intSeriesC K pf / intSeriesC K pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
              qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
            intSeriesC K pf₁ / intSeriesC K pg₁) := by
  refine ⟨rho hM, fun γ hγH => ?_, fun γ hγ1 => ?_, fun γ x hx => rho_apply_eq_self_of_mem_gamma0 hM γ x hx,
    fun γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ ef eg hg0 hg₁0 =>
      rho_apply_generator hM γ f g f₁ g₁ c hc hf hg hf₁ hg₁ ef eg hg0 hg₁0⟩
  · refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [AlgEquiv.one_apply]
    exact rhoVal_of_mem_GammaH hM x.2 γ.1 γ.2 hγH
  · refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [AlgEquiv.one_apply]
    change rhoVal γ.1 γ.2 (x : LaurentSeries K) x.2 = (x : LaurentSeries K)
    have key : ∀ (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M), δ = -1 →
        rhoVal δ hδ (x : LaurentSeries K) x.2 = x := by
      rintro δ hδ rfl
      exact rhoVal_neg_one hM x.2 hδ
    exact key γ.1 γ.2 hγ1

end Spec
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end DiamondAct
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct.IDatum P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve.DiamondAct P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH.ModularCurve"

open scoped MatrixGroups ModularForm in

theorem solution
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
          ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) = -1 → ρ γ = 1) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
        (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) →
          ρ γ x = x) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
        (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
        (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
        (_ : ModularCurve.IsIntegralQExp f₁ pf₁) (_ : ModularCurve.IsIntegralQExp g₁ pg₁)
        (_ : (⇑f₁ : UpperHalfPlane → ℂ) =
          c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (_ : (⇑g₁ : UpperHalfPlane → ℂ) =
          c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (hg0 : ModularCurve.intSeriesC K pg ≠ 0) (_ : ModularCurve.intSeriesC K pg₁ ≠ 0),
          ((ρ γ ⟨ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg,
              ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
                ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
            ModularCurve.intSeriesC K pf₁ / ModularCurve.intSeriesC K pg₁) :=
  ModularCurve.DiamondAct.main K M hM H

end S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH
end P2MW
export P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH (solution)

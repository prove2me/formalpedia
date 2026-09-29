-- Prove2me | solution 1 for ModularCurve.exists_isDiamondPullbackModL_bot_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/360b99dc-33c1-5fa0-b86a-100df7bff947

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
import Theorems.Thm_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isDiamondPullbackModL_bot_of_natCast_ne_zero
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup Function HahnSeries ModularCurve IntermediateField CohCarrier

open scoped MatrixGroups ModularForm Manifold

namespace P2MKcDiaBC

universe u

section PB

variable (K : Type*) [Field K] (M : ℕ) (Γ : Subgroup SL(2, ℤ))

abbrev Aut : Type _ := qExpFunctionFieldC K Γ ≃ₐ[K] qExpFunctionFieldC K Γ

def PB (ρ : Gamma0 M →* Aut K Γ) : Prop :=
  ∀ (γ : Gamma0 M) (k : ℤ) (f g f₁ g₁ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg pf₁ pg₁ : PowerSeries ℤ),
    IsIntegralQExp f pf → IsIntegralQExp g pg → IsIntegralQExp f₁ pf₁ → IsIntegralQExp g₁ pg₁ →
    (⇑f₁ : ℍ → ℂ) = ((⇑f : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    (⇑g₁ : ℍ → ℂ) = ((⇑g : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    intSeriesC K pg ≠ 0 →
    ∀ x : qExpFunctionFieldC K Γ, (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁ →
      ((ρ γ x : qExpFunctionFieldC K Γ) : LaurentSeries K) = intSeriesC K pf / intSeriesC K pg

theorem pb_iff (ρ : Gamma0 M →* Aut K (GammaH M ⊥)) :
    PB K M (GammaH M ⊥) ρ ↔ IsDiamondPullbackModL K M ⊥ ρ := Iff.rfl

variable {K Γ} in

def ofRingEquiv' (e : qExpFunctionFieldC K Γ ≃+* qExpFunctionFieldC K Γ)
    (he : ∀ c : K, e (algebraMap K (qExpFunctionFieldC K Γ) c) = algebraMap K (qExpFunctionFieldC K Γ) c) :
    Aut K Γ :=
  AlgEquiv.ofRingEquiv (f := e) he

variable {K Γ} in
theorem ofRingEquiv'_apply (e : qExpFunctionFieldC K Γ ≃+* qExpFunctionFieldC K Γ)
    (he : ∀ c : K, e (algebraMap K (qExpFunctionFieldC K Γ) c) = algebraMap K (qExpFunctionFieldC K Γ) c)
    (x : qExpFunctionFieldC K Γ) : ofRingEquiv' e he x = e x := rfl

end PB

section Transport

variable {K₀ K : Type*} [Field K₀] [Field K]

theorem coeffMap_intSeriesC (φ : K₀ →+* K) (p : PowerSeries ℤ) : coeffMap φ (intSeriesC K₀ p) = intSeriesC K p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map φ),
    ← PowerSeries.map_comp]
  congr 3
  exact Subsingleton.elim _ _

variable {M : ℕ} (Γ : Subgroup SL(2, ℤ))

theorem transport (φ : K₀ →+* K)
    (ρ₀ : Gamma0 M →* Aut K₀ Γ) (h₀ : PB K₀ M Γ ρ₀) :
    ∃ ρ : Gamma0 M →* Aut K Γ, PB K M Γ ρ := by
  classical

  let Spec : Aut K₀ Γ → Aut K Γ → Prop := fun σ₀ σ =>
    ∀ (x₀ : qExpFunctionFieldC K₀ Γ) (x : qExpFunctionFieldC K Γ),
      (x : LaurentSeries K) = coeffMap φ (x₀ : LaurentSeries K₀) →
      ((σ x : qExpFunctionFieldC K Γ) : LaurentSeries K) =
        coeffMap φ ((σ₀ x₀ : qExpFunctionFieldC K₀ Γ) : LaurentSeries K₀)
  have hex : ∀ σ₀, ∃! σ, Spec σ₀ σ := fun σ₀ =>
    existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap φ Γ σ₀
  let lift : Aut K₀ Γ → Aut K Γ := fun σ₀ => (hex σ₀).exists.choose
  have hlift : ∀ σ₀, Spec σ₀ (lift σ₀) := fun σ₀ => (hex σ₀).exists.choose_spec
  have huniq : ∀ σ₀ σ, Spec σ₀ σ → σ = lift σ₀ := fun σ₀ σ h => (hex σ₀).unique h (hlift σ₀)
  have hmul : ∀ σ₀ τ₀, lift (σ₀ * τ₀) = lift σ₀ * lift τ₀ := by
    intro σ₀ τ₀
    symm
    apply huniq
    intro x₀ x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    exact hlift σ₀ (τ₀ x₀) (lift τ₀ x) (hlift τ₀ x₀ x hx)
  let ρ : Gamma0 M →* Aut K Γ :=
    MonoidHom.mk' (fun γ => lift (ρ₀ γ)) (fun a b => by simp only [map_mul, hmul])
  refine ⟨ρ, ?_⟩
  intro γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ ef eg hpg x hx
  have hpg₀ : intSeriesC K₀ pg ≠ 0 := fun h => hpg (by rw [← coeffMap_intSeriesC φ pg, h, map_zero])
  have hmem₀ : intSeriesC K₀ pf₁ / intSeriesC K₀ pg₁ ∈ qExpFunctionFieldC K₀ Γ := by
    by_cases h1 : intSeriesC K₀ pg₁ = 0
    · rw [h1, div_zero]; exact zero_mem _
    · exact div_mem_qExpFunctionFieldC f₁ g₁ hf₁ hg₁ h1
  set x₀ : qExpFunctionFieldC K₀ Γ := ⟨_, hmem₀⟩ with hx₀def
  have hx₀ : (x : LaurentSeries K) = coeffMap φ (x₀ : LaurentSeries K₀) := by
    rw [hx, hx₀def, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  have h1 := hlift (ρ₀ γ) x₀ x hx₀
  have h2 := h₀ γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ ef eg hpg₀ x₀ rfl
  show ((lift (ρ₀ γ) x : qExpFunctionFieldC K Γ) : LaurentSeries K) = _
  rw [h1, h2, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

end Transport

section CharL

theorem exists_zmod (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M) :
    ∃ ρ₀ : Gamma0 M →* Aut (ZMod ℓ) (GammaH M ⊥), PB (ZMod ℓ) M (GammaH M ⊥) ρ₀ := by
  obtain ⟨ρ, -, h2, -⟩ := exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod ℓ M hℓM ⊥
  exact ⟨ρ, h2⟩

end CharL

section CharZero

local notation "Γ₁ᴳ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev F1 (M : ℕ) : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gamma1 M)

theorem x1FunctionField_eq (M : ℕ) : x1FunctionField M = F1 M := rfl

variable {M : ℕ}

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ᴳ(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem conj_mem_Gamma1 {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ Gamma1 M) :
    γ * A * γ⁻¹ ∈ Gamma1 M := by
  have hA' : A ∈ GammaH M ⊥ := by rw [GammaH_bot]; exact hA
  have h : γ * A * γ⁻¹ ∈ GammaH M ⊥ := CohCarrier.conj_mem_GammaH M ⊥ ⟨γ, hγ⟩ ⟨A, hA'⟩
  rwa [GammaH_bot] at h

variable {k : ℤ}

def diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁ᴳ(M) k) :
    ModularForm Γ₁ᴳ(M) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ Gamma1 M := conj_mem_Gamma1 hγ hA
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
    have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ₁ᴳ(M)).mp hc
    have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) Γ₁ᴳ(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hcSL.smul_of_mem ⟨γ, rfl⟩
    exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

theorem coe_diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁ᴳ(M) k) :
    (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [ModularForm.SL_slash]; rfl

theorem intSeriesC_complex (p : PowerSeries ℤ) :
    intSeriesC ℂ p = coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) :=
  (coeffMap_intSeriesC (algebraMap ℚ ℂ) p).symm

theorem coeffMap_rat_injective : Function.Injective (coeffMap (algebraMap ℚ ℂ)) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact (algebraMap ℚ ℂ).injective this

theorem eq_zero_of_intSeriesC_eq_zero {L : Type*} [Field L] [CharZero L] {p : PowerSeries ℤ}
    (h : intSeriesC L p = 0) : p = 0 := by
  have h1 : p.map (Int.castRingHom L) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  ext n
  have := congrArg (PowerSeries.coeff n) h1
  rw [PowerSeries.coeff_map, map_zero, eq_intCast, Int.cast_eq_zero] at this
  rw [this, map_zero]

theorem ofPowerSeries_qExpansion_eq {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F) = intSeriesC ℂ p := by
  rw [← h]; rfl

theorem intSeriesC_ne_zero_of_slash [NeZero M] {L : Type*} [Field L] [CharZero L]
    {g g₁ : ModularForm Γ₁ᴳ(M) k} {pg pg₁ : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg₁ : IsIntegralQExp g₁ pg₁) (γ : SL(2, ℤ)) {D : ℤ} (hD : D ≠ 0)
    (eg : (⇑g₁ : ℍ → ℂ) = (D : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] γ)) (hg0 : intSeriesC L pg ≠ 0) :
    intSeriesC L pg₁ ≠ 0 := by
  intro h0
  have hp₁ : pg₁ = 0 := eq_zero_of_intSeriesC_eq_zero h0
  have hq₁ : qExpansion 1 (⇑g₁ : ℍ → ℂ) = 0 := by rw [← hg₁, hp₁, map_zero]
  have hg₁0 : g₁ = 0 := (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M) g₁).mp hq₁
  have hslash : (⇑g : ℍ → ℂ) ∣[k] γ = 0 := by
    have : (D : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] γ) = 0 := by rw [← eg, hg₁0]; rfl
    exact (smul_eq_zero.mp this).resolve_left (Int.cast_ne_zero.mpr hD)
  have hgfun : (⇑g : ℍ → ℂ) = 0 := by
    have e : (⇑g : ℍ → ℂ) = ((⇑g : ℍ → ℂ) ∣[k] γ) ∣[k] γ⁻¹ := by
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    rw [e, hslash, SlashAction.zero_slash]
  have hgz : g = 0 := DFunLike.ext' (hgfun.trans ModularForm.coe_zero.symm)
  have hq : qExpansion 1 (⇑g : ℍ → ℂ) = 0 := by rw [hgz, ModularForm.coe_zero, qExpansion_zero]
  have hp : pg = 0 := by
    have h1 : pg.map (Int.castRingHom ℂ) = 0 := hg.trans hq
    ext n
    have := congrArg (PowerSeries.coeff n) h1
    rw [PowerSeries.coeff_map, map_zero, eq_intCast, Int.cast_eq_zero] at this
    rw [this, map_zero]
  exact hg0 (by rw [hp, intSeriesC_zero])

theorem slashQExpC_eq [NeZero M] {f f₁ : ModularForm Γ₁ᴳ(M) k} {pf₁ : PowerSeries ℤ}
    (hf₁ : IsIntegralQExp f₁ pf₁) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {D : ℤ} (hD : D ≠ 0)
    (ef : (⇑f₁ : ℍ → ℂ) = (D : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] γ)) :
    slashQExpC k (⇑f) γ = HahnSeries.C ((D : ℂ)⁻¹) * intSeriesC ℂ pf₁ := by
  have hD' : (D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have e1 : ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) = (D : ℂ)⁻¹ • (⇑f₁ : ℍ → ℂ) := by
    rw [ef, smul_smul, inv_mul_cancel₀ hD', one_smul, ModularForm.SL_slash]
  rw [slashQExpC, e1, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) _ f₁, ← hf₁,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]
  rfl

theorem sigma_apply_ratio [NeZero M] {d : ℕ} {σ : F1 M ≃ₐ[ℚ] F1 M} (hσ : IsDiamondAut M d σ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M))
    {f g f₁ g₁ : ModularForm Γ₁ᴳ(M) k} {pf pg pf₁ pg₁ : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hf₁ : IsIntegralQExp f₁ pf₁) (hg₁ : IsIntegralQExp g₁ pg₁) {D : ℤ} (hD : D ≠ 0)
    (ef : (⇑f₁ : ℍ → ℂ) = (D : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] γ))
    (eg : (⇑g₁ : ℍ → ℂ) = (D : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] γ)) (hg0 : intSeriesC ℚ pg ≠ 0) :
    intSeriesC ℚ pg₁ ≠ 0 ∧
      ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : F1 M) :
          LaurentSeries ℚ) = intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁ := by
  have hg₁0 : intSeriesC ℚ pg₁ ≠ 0 := intSeriesC_ne_zero_of_slash hg hg₁ γ hD eg hg0
  have hg₁0C : intSeriesC ℂ pg₁ ≠ 0 :=
    intSeriesC_ne_zero_of_slash hg hg₁ γ hD eg (fun h => hg0 (by
      have := eq_zero_of_intSeriesC_eq_zero h; rw [this, intSeriesC_zero]))
  refine ⟨hg₁0, ?_⟩
  have hD' : (D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have key : coeffMap (algebraMap ℚ ℂ)
      ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : F1 M) :
        LaurentSeries ℚ) * slashQExpC k (⇑g) γ = slashQExpC k (⇑f) γ :=
    hσ.2 k f g pf pg hf hg hg0 γ hγ hd
  rw [slashQExpC_eq hg₁ γ hγ hD eg, slashQExpC_eq hf₁ γ hγ hD ef, mul_left_comm] at key
  have key' := mul_left_cancel₀ (HahnSeries.C_ne_zero (inv_ne_zero hD')) key
  rw [intSeriesC_complex, intSeriesC_complex, ← eq_div_iff (by rwa [← intSeriesC_complex]),
    ← map_div₀] at key'
  exact coeffMap_rat_injective key'

theorem exists_common_slash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f g : ModularForm Γ₁ᴳ(M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    ∃ (D : ℤ) (f₁ g₁ : ModularForm Γ₁ᴳ(M) k) (pf₁ pg₁ : PowerSeries ℤ), D ≠ 0 ∧
      IsIntegralQExp f₁ pf₁ ∧ IsIntegralQExp g₁ pg₁ ∧
      (⇑f₁ : ℍ → ℂ) = (D : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] γ) ∧
      (⇑g₁ : ℍ → ℂ) = (D : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] γ) := by
  obtain ⟨Df, f₁, pf₁, hDf, hf₁, ef⟩ := exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M f hf γ hγ
  obtain ⟨Dg, g₁, pg₁, hDg, hg₁, eg⟩ := exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M g hg γ hγ
  refine ⟨Df * Dg, (Dg : ℝ) • f₁, (Df : ℝ) • g₁, PowerSeries.C Dg * pf₁, PowerSeries.C Df * pg₁,
    mul_ne_zero hDf hDg, ?_, ?_, ?_, ?_⟩
  · exact isIntegralQExp_real_smul hf₁ Dg
  · exact isIntegralQExp_real_smul hg₁ Df
  · rw [coe_real_smul, ef, smul_smul]; push_cast; ring_nf
  · rw [coe_real_smul, eg, smul_smul]; push_cast; ring_nf
where
  coe_real_smul {a : ℤ} (c : ℤ) (F : ModularForm Γ₁ᴳ(M) a) :
      (⇑((c : ℝ) • F) : ℍ → ℂ) = (c : ℂ) • (⇑F : ℍ → ℂ) := by
    rw [ModularForm.coe_smul]
    funext τ
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_intCast]
  isIntegralQExp_real_smul {a : ℤ} {F : ModularForm Γ₁ᴳ(M) a} {p : PowerSeries ℤ}
      (hF : IsIntegralQExp F p) (c : ℤ) : IsIntegralQExp (⇑((c : ℝ) • F)) (PowerSeries.C c * p) := by
    rw [IsIntegralQExp, coe_real_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) _ F,
      ← hF, map_mul, PowerSeries.map_C, eq_intCast, PowerSeries.smul_eq_C_mul]

theorem algEquiv_eq_of_apply_ratio {L : Type*} [Field L] {Γ : Subgroup SL(2, ℤ)}
    (σ τ : Aut L Γ)
    (h : ∀ x : qExpFunctionFieldC L Γ, (x : LaurentSeries L) ∈ intFormRatiosC L Γ → σ x = τ x) :
    σ = τ := by
  let S : IntermediateField L (qExpFunctionFieldC L Γ) :=
    { carrier := {y | σ y = τ y}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
      one_mem' := by simp only [Set.mem_setOf_eq, map_one]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, AlgEquiv.commutes]
      inv_mem' := fun x hx => by
        simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx] }
  have hle : qExpFunctionFieldC L Γ ≤ IntermediateField.lift S := by
    change IntermediateField.adjoin L (intFormRatiosC L Γ) ≤ _
    rw [adjoin_le_iff]
    intro s hs
    exact (mem_lift (⟨s, intFormRatiosC_subset L Γ hs⟩ : qExpFunctionFieldC L Γ)).mpr (h _ hs)
  refine AlgEquiv.ext fun y => ?_
  have hy : y ∈ S := (mem_lift y).mp (hle y.2)
  exact hy

variable (M) in

def dOf (γ : Gamma0 M) : ℕ := (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val

theorem dOf_coprime (γ : Gamma0 M) : Nat.Coprime (dOf M γ) M := by
  have : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = ((gamma0Units M γ)⁻¹ : (ZMod M)ˣ) := rfl
  rw [dOf, this]
  exact ZMod.val_coe_unit_coprime _

theorem natCast_dOf [NeZero M] (γ : Gamma0 M) :
    (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = ((dOf M γ : ℕ) : ZMod M) := by
  rw [dOf, ZMod.natCast_zmod_val]

theorem entry00_mul (γ γ' : Gamma0 M) :
    ((((γ * γ' : Gamma0 M) : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) =
      (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) * (((γ' : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) := by
  have h10 : (((γ' : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ'.2
  have e : ((γ * γ' : Gamma0 M) : SL(2, ℤ)) 0 0 =
      (γ : SL(2, ℤ)) 0 0 * (γ' : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 0 1 * (γ' : SL(2, ℤ)) 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  push_cast
  rw [h10, mul_zero, add_zero]

variable (M) in

def sig [NeZero M] (γ : Gamma0 M) : F1 M ≃ₐ[ℚ] F1 M :=
  (exists_isDiamondAut M (dOf_coprime γ)).choose

theorem sig_spec [NeZero M] (γ : Gamma0 M) : IsDiamondAut M (dOf M γ) (sig M γ) :=
  (exists_isDiamondAut M (dOf_coprime γ)).choose_spec

variable (M) in

def sigA [NeZero M] (γ : Gamma0 M) : Aut ℚ (Gamma1 M) :=
  ofRingEquiv' ((sig M γ).toRingEquiv : F1 M ≃+* F1 M) fun c => by
    rw [eq_ratCast]
    exact map_ratCast _ c

theorem sigA_apply [NeZero M] (γ : Gamma0 M) (x : F1 M) : sigA M γ x = sig M γ x := rfl

theorem sig_mul [NeZero M] (γ γ' : Gamma0 M) : sigA M (γ * γ') = sigA M γ' * sigA M γ := by
  refine algEquiv_eq_of_apply_ratio _ _ fun x hx => ?_
  change sig M (γ * γ') x = sig M γ' (sig M γ x)
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hxeq⟩ := hx
  have hxx : x = ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :=
    Subtype.ext hxeq
  subst hxx

  obtain ⟨D, f₁, g₁, pf₁, pg₁, hD, hf₁, hg₁, ef, eg⟩ := exists_common_slash (γ : SL(2, ℤ)) γ.2 f g hf hg
  obtain ⟨hg₁0, h1⟩ := sigma_apply_ratio (sig_spec γ) (γ : SL(2, ℤ)) γ.2 (natCast_dOf γ)
    hf hg hf₁ hg₁ hD ef eg hg0

  obtain ⟨D', f₂, g₂, pf₂, pg₂, hD', hf₂, hg₂, ef₂, eg₂⟩ :=
    exists_common_slash (γ' : SL(2, ℤ)) γ'.2 f₁ g₁ hf₁ hg₁
  obtain ⟨hg₂0, h2⟩ := sigma_apply_ratio (sig_spec γ') (γ' : SL(2, ℤ)) γ'.2 (natCast_dOf γ')
    hf₁ hg₁ hf₂ hg₂ hD' ef₂ eg₂ hg₁0

  have ef₃ : (⇑f₂ : ℍ → ℂ) = ((D' * D : ℤ) : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] ((γ * γ' : Gamma0 M) : SL(2, ℤ))) := by
    rw [ef₂, ef, ModularForm.SL_smul_slash, smul_smul, Subgroup.coe_mul, SlashAction.slash_mul]
    push_cast; rfl
  have eg₃ : (⇑g₂ : ℍ → ℂ) = ((D' * D : ℤ) : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] ((γ * γ' : Gamma0 M) : SL(2, ℤ))) := by
    rw [eg₂, eg, ModularForm.SL_smul_slash, smul_smul, Subgroup.coe_mul, SlashAction.slash_mul]
    push_cast; rfl
  obtain ⟨-, h3⟩ := sigma_apply_ratio (sig_spec (γ * γ')) ((γ * γ' : Gamma0 M) : SL(2, ℤ)) (γ * γ').2
    (natCast_dOf (γ * γ')) hf hg hf₂ hg₂ (mul_ne_zero hD' hD) ef₃ eg₃ hg0
  apply Subtype.ext
  rw [h3]
  have e1 : sig M γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ =
      ⟨intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁, div_mem_qExpFunctionFieldC f₁ g₁ hf₁ hg₁ hg₁0⟩ :=
    Subtype.ext h1
  rw [e1, h2]

variable (M) in

def rhoQ [NeZero M] : Gamma0 M →* Aut ℚ (Gamma1 M) :=
  MonoidHom.mk' (fun γ => (sigA M γ)⁻¹) fun γ γ' => by
    beta_reduce
    rw [sig_mul, mul_inv_rev]

theorem rhoQ_apply [NeZero M] (γ : Gamma0 M) : rhoQ M γ = (sigA M γ)⁻¹ := rfl

theorem pb_rhoQ [NeZero M] : PB ℚ M (Gamma1 M) (rhoQ M) := by
  intro γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ ef eg hpg x hx
  have ef' : (⇑f₁ : ℍ → ℂ) = ((1 : ℤ) : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
    rw [Int.cast_one, one_smul]; exact ef
  have eg' : (⇑g₁ : ℍ → ℂ) = ((1 : ℤ) : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
    rw [Int.cast_one, one_smul]; exact eg
  obtain ⟨hg₁0, h1⟩ := sigma_apply_ratio (sig_spec γ) (γ : SL(2, ℤ)) γ.2 (natCast_dOf γ)
    hf hg hf₁ hg₁ one_ne_zero ef' eg' hpg
  have e1 : sigA M γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hpg⟩ = x :=
    Subtype.ext (h1.trans hx.symm)
  rw [rhoQ_apply]
  have e2 : (sigA M γ)⁻¹ x = ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hpg⟩ := by
    rw [← e1]
    exact (sig M γ).symm_apply_apply _
  rw [e2]

theorem exists_rat (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ : Γ = Gamma1 M) :
    ∃ ρ₀ : Gamma0 M →* Aut ℚ Γ, PB ℚ M Γ ρ₀ := by
  subst hΓ
  exact ⟨rhoQ M, pb_rhoQ⟩

end CharZero

end P2MKcDiaBC

open P2MKcDiaBC in
universe u in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (K : Type u) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
          qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
      IsDiamondPullbackModL K M ⊥ ρ := by
  rcases CharP.exists' K with h0 | ⟨p, hp, hchar⟩
  ·
    haveI := h0
    obtain ⟨ρ₀, h₀⟩ := exists_rat M (CohCarrier.GammaH M ⊥) (GammaH_bot M)
    obtain ⟨ρ, h⟩ := transport (CohCarrier.GammaH M ⊥) (algebraMap ℚ K) ρ₀ h₀
    exact ⟨ρ, (pb_iff K M ρ).mp h⟩
  ·
    haveI := hp
    haveI := hchar
    have hpM : ¬ p ∣ M := fun h => hM ((CharP.cast_eq_zero_iff K p M).mpr h)
    obtain ⟨ρ₀, h₀⟩ := exists_zmod p M hpM
    obtain ⟨ρ, h⟩ := transport (CohCarrier.GammaH M ⊥) (ZMod.castHom (dvd_refl p) K) ρ₀ h₀
    exact ⟨ρ, (pb_iff K M ρ).mp h⟩

end

end S_ModularCurve_exists_isDiamondPullbackModL_bot_of_natCast_ne_zero
end P2MW
export P2MW.S_ModularCurve_exists_isDiamondPullbackModL_bot_of_natCast_ne_zero (solution)

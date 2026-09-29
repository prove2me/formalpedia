-- Prove2me | solution 1 for ModularCurve.diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/55253919-e676-58ec-875e-e50167aef16b

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularForm_exists_coe_eq_slash_of_mem_gamma0_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct MatrixGroups ModularForm
p2m_open "ModularCurve P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul.ModularCurve AlgebraicCurve KaehlerDifferential HahnSeries CongruenceSubgroup"

namespace ModularCurve
p2m_export "ModularCurve" "isDiamondPullbackModL_diamondActionModL diamondDiffModLH diamondDiffModLH_apply infSubgroup IsDiamondPullbackModL restrictForm coe_restrictForm IsIntegralQExp intSeriesC intSeriesC_mul qExpFunctionFieldC div_mem_qExpFunctionFieldC coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffMap_intSeriesC coeffMap_mem_qExpFunctionFieldC_of_mem exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
namespace DiffBDia
p2m_open "ModularCurve"

section Setup
variable (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] (Γ : Subgroup SL(2, ℤ))

def iota : ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ) where
  toFun x := ⟨coeffMap (algebraMap k K) (x : LaurentSeries k),
    coeffMap_mem_qExpFunctionFieldC_of_mem (algebraMap k K) Γ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_iota (x : ↥(qExpFunctionFieldC k Γ)) :
    ((iota k K Γ x : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap (algebraMap k K) (x : LaurentSeries k) := rfl

scoped instance algebraFkFK : Algebra ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := (iota k K Γ).toAlgebra

theorem algebraMap_Fk_FK : algebraMap ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) = iota k K Γ := rfl

scoped instance algebrakFK : Algebra k ↥(qExpFunctionFieldC K Γ) :=
  ((algebraMap K ↥(qExpFunctionFieldC K Γ)).comp (algebraMap k K)).toAlgebra

theorem algebraMap_k_FK_apply (a : k) :
    algebraMap k ↥(qExpFunctionFieldC K Γ) a = algebraMap K ↥(qExpFunctionFieldC K Γ) (algebraMap k K a) := rfl

scoped instance isScalarTower_k_K_FK : IsScalarTower k K ↥(qExpFunctionFieldC K Γ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance isScalarTower_k_Fk_FK : IsScalarTower k ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := by
  refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
  apply Subtype.ext
  rw [algebraMap_k_FK_apply, algebraMap_Fk_FK, coe_iota]
  change algebraMap K (LaurentSeries K) (algebraMap k K a) = coeffMap (algebraMap k K) (algebraMap k (LaurentSeries k) a)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

scoped instance smulCommClass_K_Fk_FK : SMulCommClass K ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) :=
  ⟨fun c f x => by simp only [Algebra.smul_def]; ring⟩

scoped instance isScalarTower_Fk_FK_Omega :
    IsScalarTower ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) Ω[↥(qExpFunctionFieldC K Γ)⁄K] :=
  KaehlerDifferential.isScalarTower_of_tower K ↥(qExpFunctionFieldC K Γ)

theorem pullbackAlong_map (σk : ↥(qExpFunctionFieldC k Γ) ≃ₐ[k] ↥(qExpFunctionFieldC k Γ))
    (σK : ↥(qExpFunctionFieldC K Γ) ≃ₐ[K] ↥(qExpFunctionFieldC K Γ))
    (h : ∀ x, σK (algebraMap ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) x) =
      algebraMap ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) (σk x))
    (ω : Ω[↥(qExpFunctionFieldC k Γ)⁄k]) :
    Differential.pullbackAlong σK.toAlgHom (KaehlerDifferential.map k K ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) ω) =
      KaehlerDifferential.map k K ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) (Differential.pullbackAlong σk.toAlgHom ω) := by
  have hmem : ω ∈ Submodule.span ↥(qExpFunctionFieldC k Γ) (Set.range (D k ↥(qExpFunctionFieldC k Γ))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [KaehlerDifferential.map_D, Differential.pullbackAlong_D, Differential.pullbackAlong_D, KaehlerDifferential.map_D]
      change D K _ (σK (algebraMap _ _ g)) = _
      rw [h]
      rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul f x _ hx =>
      rw [LinearMap.map_smul, ← algebraMap_smul ↥(qExpFunctionFieldC K Γ) f, Differential.pullbackAlong_smul,
        Differential.pullbackAlong_smul, LinearMap.map_smul, ← algebraMap_smul ↥(qExpFunctionFieldC K Γ) (σk.toAlgHom f), hx]
      congr 1
      exact h f

end Setup

section Integral

theorem intSeriesC_C_mul (L : Type*) [Field L] (z : ℤ) (p : PowerSeries ℤ) :
    intSeriesC L (PowerSeries.C z * p) = (z : L) • intSeriesC L p := by
  rw [intSeriesC_mul]
  have : intSeriesC L (PowerSeries.C z) = HahnSeries.C (z : L) := by
    simp [intSeriesC]
  rw [this, HahnSeries.C_mul_eq_smul]

theorem one_mem_strictPeriods_GammaH (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    (1 : ℝ) ∈ (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH N H' := by
    have hT0 : ModularGroup.T ∈ Gamma0 N := by rw [Gamma0_mem]; simp [ModularGroup.T]
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hT0, ?_⟩
    have : CohCarrier.gamma0Units N ⟨ModularGroup.T, hT0⟩ = 1 := by
      apply Units.ext
      rw [CohCarrier.val_gamma0Units, Units.val_one]
      change ((ModularGroup.T 1 1 : ℤ) : ZMod N) = 1
      simp [ModularGroup.T]
    rw [this]; exact one_mem _
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

end Integral

section KC

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]
  (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
  (hNk : (N : k) ≠ 0) (hNK : (N : K) ≠ 0)
  {ρk : Gamma0 N →* (↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ≃ₐ[k] ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')))}
  {ρK : Gamma0 N →* (↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')))}
  (hρk : IsDiamondPullbackModL k N H' ρk) (hρK : IsDiamondPullbackModL K N H' ρK)

theorem isIntegralQExp_pow_smul' {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {w : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w) {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (c : ℕ) :
    IsIntegralQExp (((N : ℂ) ^ c) • (⇑f : UpperHalfPlane → ℂ)) (PowerSeries.C ((N : ℤ) ^ c) * pf) := by
  unfold IsIntegralQExp at hf ⊢
  have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]; exact AddSubgroup.mem_zmultiples _
  rw [ModularForm.qExpansion_smul one_pos h1 ((N : ℂ) ^ c) f, map_mul, PowerSeries.map_C, hf,
    PowerSeries.smul_eq_C_mul]
  simp

theorem T_mem_GammaH' : ModularGroup.T ∈ CohCarrier.GammaH N H' := by
  have hT0 : ModularGroup.T ∈ Gamma0 N := by rw [Gamma0_mem]; simp [ModularGroup.T]
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨ModularGroup.T, hT0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    change ((ModularGroup.T 1 1 : ℤ) : ZMod N) = 1
    simp [ModularGroup.T]
  rw [this]; exact one_mem _

theorem T_mem_Gamma1' : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]; simp [ModularGroup.T]

theorem Gamma1_le_GammaH' : Gamma1 N ≤ CohCarrier.GammaH N H' := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ Gamma0 N := by rw [Gamma0_mem]; exact h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]; exact one_mem _

include hNk hNK hρk hρK in

theorem rho_iota_gen (γ : Gamma0 N) {w : ℤ}
    (f g : ModularForm ((CohCarrier.GammaH N H') : Subgroup (GL (Fin 2) ℝ)) w) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC k pg ≠ 0) :
    ρK γ (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) ⟨intSeriesC k pf / intSeriesC k pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩) =
      algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ρk γ ⟨intSeriesC k pf / intSeriesC k pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩) := by
  set x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) := ⟨intSeriesC k pf / intSeriesC k pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ with hxdef
  set σ : Gamma0 N := γ⁻¹ with hσ
  have hle : ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ ((CohCarrier.GammaH N H') : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_GammaH' N H')

  obtain ⟨a, f₁', p₁, hf₁', hf₁'eq⟩ := ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 N
    (restrictForm hle f) (by rw [coe_restrictForm]; exact hf) (σ : SL(2, ℤ)) σ.2
  obtain ⟨b, g₁', q₁, hg₁', hg₁'eq⟩ := ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 N
    (restrictForm hle g) (by rw [coe_restrictForm]; exact hg) (σ : SL(2, ℤ)) σ.2
  rw [coe_restrictForm] at hf₁'eq hg₁'eq

  obtain ⟨Fσ, hFσ⟩ := ModularForm.exists_coe_eq_slash_of_mem_gamma0_gammaH N H' f (σ : SL(2, ℤ)) σ.2
  obtain ⟨Gσ, hGσ⟩ := ModularForm.exists_coe_eq_slash_of_mem_gamma0_gammaH N H' g (σ : SL(2, ℤ)) σ.2
  set c := a + b with hc

  have hRC : ∀ (φ : ModularForm ((CohCarrier.GammaH N H') : Subgroup (GL (Fin 2) ℝ)) w),
      (⇑(((N : ℝ) ^ c) • φ) : UpperHalfPlane → ℂ) = ((N : ℂ) ^ c) • (⇑φ : UpperHalfPlane → ℂ) := by
    intro φ
    ext τ
    rw [ModularForm.coe_smul, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    rfl
  set F : ModularForm ((CohCarrier.GammaH N H') : Subgroup (GL (Fin 2) ℝ)) w := ((N : ℝ) ^ c) • f with hFdef
  set G : ModularForm ((CohCarrier.GammaH N H') : Subgroup (GL (Fin 2) ℝ)) w := ((N : ℝ) ^ c) • g with hGdef
  set F₁ : ModularForm ((CohCarrier.GammaH N H') : Subgroup (GL (Fin 2) ℝ)) w := ((N : ℝ) ^ c) • Fσ with hF₁def
  set G₁ : ModularForm ((CohCarrier.GammaH N H') : Subgroup (GL (Fin 2) ℝ)) w := ((N : ℝ) ^ c) • Gσ with hG₁def
  have hFc : (⇑F : UpperHalfPlane → ℂ) = ((N : ℂ) ^ c) • (⇑f : UpperHalfPlane → ℂ) := hRC f
  have hGc : (⇑G : UpperHalfPlane → ℂ) = ((N : ℂ) ^ c) • (⇑g : UpperHalfPlane → ℂ) := hRC g
  have hF₁c : (⇑F₁ : UpperHalfPlane → ℂ) = ((N : ℂ) ^ c) • (⇑Fσ : UpperHalfPlane → ℂ) := hRC Fσ
  have hG₁c : (⇑G₁ : UpperHalfPlane → ℂ) = ((N : ℂ) ^ c) • (⇑Gσ : UpperHalfPlane → ℂ) := hRC Gσ
  have hF : IsIntegralQExp F (PowerSeries.C ((N : ℤ) ^ c) * pf) := by
    rw [hFc]; exact isIntegralQExp_pow_smul' N (T_mem_GammaH' N H') f hf c
  have hG : IsIntegralQExp G (PowerSeries.C ((N : ℤ) ^ c) * pg) := by
    rw [hGc]; exact isIntegralQExp_pow_smul' N (T_mem_GammaH' N H') g hg c
  have hF₁ : IsIntegralQExp F₁ (PowerSeries.C ((N : ℤ) ^ b) * p₁) := by
    have e : (⇑F₁ : UpperHalfPlane → ℂ) = ((N : ℂ) ^ b) • (⇑f₁' : UpperHalfPlane → ℂ) := by
      rw [hF₁c, hFσ, hf₁'eq, smul_smul, hc, _root_.pow_add, mul_comm]
    rw [e]; exact isIntegralQExp_pow_smul' N (T_mem_Gamma1' N) f₁' hf₁' b
  have hG₁ : IsIntegralQExp G₁ (PowerSeries.C ((N : ℤ) ^ a) * q₁) := by
    have e : (⇑G₁ : UpperHalfPlane → ℂ) = ((N : ℂ) ^ a) • (⇑g₁' : UpperHalfPlane → ℂ) := by
      rw [hG₁c, hGσ, hg₁'eq, smul_smul, hc, _root_.pow_add]
    rw [e]; exact isIntegralQExp_pow_smul' N (T_mem_Gamma1' N) g₁' hg₁' a
  have hslF : (⇑F₁ : UpperHalfPlane → ℂ) = (⇑F : UpperHalfPlane → ℂ) ∣[w] (σ : SL(2, ℤ)) := by
    rw [hF₁c, hFc, hFσ, ModularForm.SL_smul_slash]
  have hslG : (⇑G₁ : UpperHalfPlane → ℂ) = (⇑G : UpperHalfPlane → ℂ) ∣[w] (σ : SL(2, ℤ)) := by
    rw [hG₁c, hGc, hGσ, ModularForm.SL_smul_slash]

  have hNck : ((N : k) ^ c) ≠ 0 := pow_ne_zero _ hNk
  have hNcK : ((N : K) ^ c) ≠ 0 := pow_ne_zero _ hNK
  have hG0k : intSeriesC k (PowerSeries.C ((N : ℤ) ^ c) * pg) ≠ 0 := by
    rw [intSeriesC_C_mul]; push_cast; exact smul_ne_zero hNck hg0
  have hg0K : intSeriesC K pg ≠ 0 := by
    intro h; apply hg0
    ext n
    have hn := congrArg (fun s : LaurentSeries K => s.coeff n) h
    try simp only at hn
    rw [← coeffMap_intSeriesC (algebraMap k K), coeffMap_coeff, HahnSeries.coeff_zero, map_eq_zero] at hn
    rw [hn, HahnSeries.coeff_zero]
  have hG0K : intSeriesC K (PowerSeries.C ((N : ℤ) ^ c) * pg) ≠ 0 := by
    rw [intSeriesC_C_mul]; push_cast; exact smul_ne_zero hNcK hg0K

  have hratk : intSeriesC k (PowerSeries.C ((N : ℤ) ^ c) * pf) / intSeriesC k (PowerSeries.C ((N : ℤ) ^ c) * pg) =
      intSeriesC k pf / intSeriesC k pg := by
    rw [intSeriesC_C_mul, intSeriesC_C_mul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul]
    push_cast
    exact mul_div_mul_left _ _ (HahnSeries.C_ne_zero hNck)
  have hratK : intSeriesC K (PowerSeries.C ((N : ℤ) ^ c) * pf) / intSeriesC K (PowerSeries.C ((N : ℤ) ^ c) * pg) =
      intSeriesC K pf / intSeriesC K pg := by
    rw [intSeriesC_C_mul, intSeriesC_C_mul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul]
    push_cast
    exact mul_div_mul_left _ _ (HahnSeries.C_ne_zero hNcK)

  obtain ⟨Y, hY⟩ : ∃ Y : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')), (Y : LaurentSeries k) =
      intSeriesC k (PowerSeries.C ((N : ℤ) ^ b) * p₁) / intSeriesC k (PowerSeries.C ((N : ℤ) ^ a) * q₁) := by
    by_cases h0 : intSeriesC k (PowerSeries.C ((N : ℤ) ^ a) * q₁) = 0
    · exact ⟨0, by rw [h0, div_zero]; rfl⟩
    · exact ⟨⟨_, div_mem_qExpFunctionFieldC F₁ G₁ hF₁ hG₁ h0⟩, rfl⟩

  have hk := hρk σ w F G F₁ G₁ _ _ _ _ hF hG hF₁ hG₁ hslF hslG hG0k Y hY
  rw [hratk] at hk
  have hkx : ρk σ Y = x := Subtype.ext hk
  have hYx : Y = ρk γ x := by
    rw [← hkx, hσ, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]

  have hYK : ((algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) Y : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K) =
      intSeriesC K (PowerSeries.C ((N : ℤ) ^ b) * p₁) / intSeriesC K (PowerSeries.C ((N : ℤ) ^ a) * q₁) := by
    rw [algebraMap_Fk_FK, coe_iota, hY, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  have hK := hρK σ w F G F₁ G₁ _ _ _ _ hF hG hF₁ hG₁ hslF hslG hG0K (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) Y) hYK
  rw [hratK] at hK
  have hKx : ρK σ (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) Y) = algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) x := by
    apply Subtype.ext
    rw [hK, algebraMap_Fk_FK, coe_iota, hxdef]
    change _ = coeffMap (algebraMap k K) (intSeriesC k pf / intSeriesC k pg)
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  calc ρK γ (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) x) = ρK γ (ρK σ (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) Y)) := by rw [hKx]
    _ = algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) Y := by
        rw [hσ, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    _ = algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ρk γ x) := by rw [hYx]

include hNk hNK hρk hρK in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem rho_iota (γ : Gamma0 N) (x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H'))) : ρK γ (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) x) = algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ρk γ x) := by
  obtain ⟨y, hy⟩ := x
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      exact rho_iota_gen N H' hNk hNK hρk hρK γ f g hf hg hg0
  | algebraMap c =>
      have e : (⟨algebraMap k (LaurentSeries k) c, IntermediateField.algebraMap_mem _ c⟩ : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H'))) = algebraMap k ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) c := rfl
      rw [e, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply k ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) c,
        IsScalarTower.algebraMap_apply k K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) c, AlgEquiv.commutes]
  | add y z hy hz ihy ihz =>
      have e : (⟨y + z, IntermediateField.add_mem _ hy hz⟩ : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H'))) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e, (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))).map_add, map_add (ρK γ), map_add (ρk γ),
        (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))).map_add, ihy, ihz]
  | inv y hy ihy =>
      have e : (⟨y⁻¹, IntermediateField.inv_mem _ hy⟩ : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H'))) = (⟨y, hy⟩ : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')))⁻¹ := rfl
      rw [e, map_inv₀ (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))), map_inv₀ (ρK γ), map_inv₀ (ρk γ),
        map_inv₀ (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))), ihy]
  | mul y z hy hz ihy ihz =>
      have e : (⟨y * z, IntermediateField.mul_mem _ hy hz⟩ : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H'))) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [e, (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))).map_mul, map_mul (ρK γ), map_mul (ρk γ),
        (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H')) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))).map_mul, ihy, ihz]

end KC

end ModularCurve.DiffBDia
p2m_reactivate "P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul.ModularCurve P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul.ModularCurve.DiffBDia"
p2m_reactivate "P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul.ModularCurve P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul.ModularCurve.DiffBDia"

open scoped TensorProduct MatrixGroups in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul.ModularCurve ModularCurve.DiffBDia AlgebraicCurve KaehlerDifferential in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K]
    (Φ : K ⊗[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k] →ₗ[K]
        Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K])
    (hinj : Function.Injective Φ)
    (hΦ : (∀ (c : K) (f g : ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
          (f' g' : ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f' : LaurentSeries K) = coeffMap (algebraMap k K) (f : LaurentSeries k) →
          (g' : LaurentSeries K) = coeffMap (algebraMap k K) (g : LaurentSeries k) →
          Φ (c ⊗ₜ[k] (f • D k ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g)) =
            c • (f' • D K ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g')))
    (hρk : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≃ₐ[k] ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
      IsDiamondPullbackModL k (M / p) (infSubgroup p M H hpM) ρ)
    (hρK : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≃ₐ[K] ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
      IsDiamondPullbackModL K (M / p) (infSubgroup p M H hpM) ρ)
    (hN0 : NeZero (M / p)) (d : (ZMod (M / p))ˣ) :
    (diamondDiffModLH K (M / p) (infSubgroup p M H hpM) d) ∘ₗ Φ =
      Φ ∘ₗ (diamondDiffModLH k (M / p) (infSubgroup p M H hpM) d).baseChange K := by
  haveI := hN0
  have hρK' := isDiamondPullbackModL_diamondActionModL hρK
  have hρk' := isDiamondPullbackModL_diamondActionModL hρk

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨t, ht⟩ := h
    refine ⟨t, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [← this, ht]; ring
  have hNk : ((M / p : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]; exact hpN
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hNK : ((M / p : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]; exact hpN
  have hι : ∀ x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))),
      ((algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) x : ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries K) =
        coeffMap (algebraMap k K) (x : LaurentSeries k) := fun x => rfl

  have hΦ1 : ∀ ω : Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k],
      Φ (1 ⊗ₜ[k] ω) = KaehlerDifferential.map k K ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ω := by
    intro ω
    have key : ∀ η ∈ Submodule.span ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) (Set.range (D k ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))),
        ∀ f : ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))),
          Φ (1 ⊗ₜ[k] (f • η)) = KaehlerDifferential.map k K ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) (f • η) := by
      intro η hη
      induction hη using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨g, rfl⟩ := hy
          intro f
          rw [hΦ 1 f g (algebraMap _ _ f) (algebraMap _ _ g) (hι f) (hι g), one_smul, LinearMap.map_smul,
            KaehlerDifferential.map_D, algebraMap_smul]
      | zero => intro f; rw [smul_zero, TensorProduct.tmul_zero, map_zero, map_zero]
      | add y z _ _ hy hz => intro f; rw [smul_add, TensorProduct.tmul_add, map_add, map_add, hy, hz]
      | smul g y _ hy => intro f; rw [smul_smul]; exact hy (f * g)
    have := key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1
    rw [one_smul] at this
    exact this
  have hC : ∀ ω : Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k],
      diamondDiffModLH K (M / p) (infSubgroup p M H hpM) d
          (KaehlerDifferential.map k K ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ω) =
        KaehlerDifferential.map k K ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
          (diamondDiffModLH k (M / p) (infSubgroup p M H hpM) d ω) := by
    intro ω
    rw [diamondDiffModLH_apply, diamondDiffModLH_apply]
    exact pullbackAlong_map k K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) _ _
      (fun x => rho_iota (M / p) (infSubgroup p M H hpM) hNk hNK hρk' hρK' _ x) ω
  apply TensorProduct.AlgebraTensorModule.ext
  intro c ω
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  have e1 : (c ⊗ₜ[k] ω : K ⊗[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k]) = c • ((1 : K) ⊗ₜ[k] ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have e2 : (c ⊗ₜ[k] diamondDiffModLH k (M / p) (infSubgroup p M H hpM) d ω : K ⊗[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k]) =
      c • ((1 : K) ⊗ₜ[k] diamondDiffModLH k (M / p) (infSubgroup p M H hpM) d ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e1, e2, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, hΦ1, hΦ1, hC]

#print axioms solution

end S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul
end P2MW
export P2MW.S_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul (solution)

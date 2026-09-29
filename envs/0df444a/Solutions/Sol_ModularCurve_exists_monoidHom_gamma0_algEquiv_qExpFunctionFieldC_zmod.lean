-- Prove2me | solution 1 for ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2a5ec0ab-d646-57a7-96a8-8a9c2d9fc943

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup Function HahnSeries ModularCurve IntermediateField

open scoped MatrixGroups ModularForm Manifold

namespace XHDiamondModL

local notation "Γᴳ(" M ", " H ")" =>
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Groups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γᴳ(M, H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

scoped instance finiteIndex_GammaH [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

variable {M H} in

theorem conj_mem {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ CohCarrier.GammaH M H) :
    γ * A * γ⁻¹ ∈ CohCarrier.GammaH M H :=
  CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨A, hA⟩

theorem Gamma1_le : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γᴳ(M, H) :=
  Subgroup.map_mono (Gamma1_le_GammaH M H)

end Groups

section Integral

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem isIntegralQExp_mul {a b : ℤ} {f : ModularForm Γᴳ(M, H) a} {g : ModularForm Γᴳ(M, H) b}
    {p p' : PowerSeries ℤ} (hf : IsIntegralQExp f p) (hg : IsIntegralQExp g p') :
    IsIntegralQExp (⇑(f.mul g)) (p * p') := by
  rw [IsIntegralQExp, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M H) f g, map_mul, hf, hg]

theorem isIntegralQExp_add {a : ℤ} {f g : ModularForm Γᴳ(M, H) a} {p p' : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) (hg : IsIntegralQExp g p') : IsIntegralQExp (⇑(f + g)) (p + p') := by
  rw [IsIntegralQExp, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M H) f g, map_add, hf, hg]

theorem isIntegralQExp_sub {a : ℤ} {f g : ModularForm Γᴳ(M, H) a} {p p' : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) (hg : IsIntegralQExp g p') : IsIntegralQExp (⇑(f - g)) (p - p') := by
  rw [IsIntegralQExp, ModularForm.coe_sub,
    ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods M H) f g, map_sub, hf, hg]

theorem qExpansion_real_smul {a : ℤ} (r : ℝ) (f : ModularForm Γᴳ(M, H) a) :
    qExpansion 1 (⇑(r • f)) = (r : ℂ) • qExpansion 1 (⇑f) := by
  have h1 : (⇑(r • f) : ℍ → ℂ) = (r : ℂ) • (⇑f : ℍ → ℂ) := by
    rw [ModularForm.coe_smul]
    funext τ
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [h1]
  exact ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M H) (r : ℂ) f

theorem isIntegralQExp_intCast_smul {a : ℤ} {f : ModularForm Γᴳ(M, H) a} {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) (c : ℤ) :
    IsIntegralQExp (⇑((c : ℝ) • f)) (PowerSeries.C c * p) := by
  rw [IsIntegralQExp, qExpansion_real_smul, ← hf, map_mul, PowerSeries.map_C, eq_intCast,
    PowerSeries.smul_eq_C_mul, Complex.ofReal_intCast]

theorem isIntegralQExp_inv_smul {a : ℤ} {f : ModularForm Γᴳ(M, H) a} {p' : PowerSeries ℤ} {n : ℤ}
    (hn : n ≠ 0) (hf : IsIntegralQExp f (PowerSeries.C n * p')) :
    IsIntegralQExp (⇑((n : ℝ)⁻¹ • f)) p' := by
  rw [IsIntegralQExp, qExpansion_real_smul, ← hf, map_mul, PowerSeries.map_C, eq_intCast,
    PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, Complex.ofReal_inv, Complex.ofReal_intCast,
    inv_mul_cancel₀ (Int.cast_ne_zero.mpr hn), map_one, one_mul]

theorem hasSum_qExpansion' [NeZero M] {a : ℤ} (f : ModularForm Γᴳ(M, H) a) (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 (⇑f)).coeff m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods M H))
    f.holo' (ModularFormClass.bdd_at_infty f) τ

theorem coe_eq_of_isIntegralQExp [NeZero M] {a b : ℤ} {f : ModularForm Γᴳ(M, H) a} {g : ModularForm Γᴳ(M, H) b}
    {p : PowerSeries ℤ} (hf : IsIntegralQExp f p) (hg : IsIntegralQExp g p) :
    (⇑f : ℍ → ℂ) = ⇑g := by
  have h' : qExpansion 1 (⇑f) = qExpansion 1 (⇑g) := by rw [← hf, ← hg]
  funext τ
  have h1 := hasSum_qExpansion' f τ
  rw [h'] at h1
  exact h1.unique (hasSum_qExpansion' g τ)

theorem eq_of_isIntegralQExp [NeZero M] {a : ℤ} {f g : ModularForm Γᴳ(M, H) a} {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) (hg : IsIntegralQExp g p) : f = g :=
  DFunLike.ext' (coe_eq_of_isIntegralQExp hf hg)

theorem isIntegralQExp_coe_zero {a : ℤ} : IsIntegralQExp (⇑(0 : ModularForm Γᴳ(M, H) a)) 0 := by
  rw [ModularForm.coe_zero]; exact isIntegralQExp_zero

theorem isIntegralQExp_coe_one : IsIntegralQExp (⇑(1 : ModularForm Γᴳ(M, H) 0)) 1 := by
  rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one

end Integral

section Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime]

def red : PowerSeries ℤ →+* LaurentSeries (ZMod ℓ) :=
  (HahnSeries.ofPowerSeries ℤ (ZMod ℓ)).comp (PowerSeries.map (Int.castRingHom (ZMod ℓ)))

theorem red_apply (p : PowerSeries ℤ) : red ℓ p = intSeriesC (ZMod ℓ) p := rfl

theorem red_eq_zero_iff (p : PowerSeries ℤ) : red ℓ p = 0 ↔ ∃ p' : PowerSeries ℤ, p = PowerSeries.C (ℓ : ℤ) * p' := by
  constructor
  · intro h
    have h1 : PowerSeries.map (Int.castRingHom (ZMod ℓ)) p = 0 :=
      HahnSeries.ofPowerSeries_injective (by rw [← RingHom.comp_apply]; exact h.trans (map_zero _).symm)
    have hdvd : ∀ n, (ℓ : ℤ) ∣ PowerSeries.coeff n p := by
      intro n
      have := congrArg (PowerSeries.coeff n) h1
      rw [PowerSeries.coeff_map, map_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    refine ⟨PowerSeries.mk fun n => PowerSeries.coeff n p / ℓ, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (hdvd n)]
  · rintro ⟨p', rfl⟩
    rw [map_mul]
    have : red ℓ (PowerSeries.C (ℓ : ℤ)) = 0 := by
      rw [red, RingHom.comp_apply, PowerSeries.map_C, eq_intCast, Int.cast_natCast,
        ZMod.natCast_self, map_zero, map_zero]
    rw [this, zero_mul]

end Reduction

section Slash

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

def dSlash (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γᴳ(M, H) k) :
    ModularForm Γᴳ(M, H) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ CohCarrier.GammaH M H := conj_mem hγ hA
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
    have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γᴳ(M, H)).mp hc
    have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) Γᴳ(M, H) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hcSL.smul_of_mem ⟨γ, rfl⟩
    exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

theorem coe_dSlash (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γᴳ(M, H) k) :
    (⇑(dSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [ModularForm.SL_slash]; rfl

def dSlashM (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (n : ℕ) (f : ModularForm Γᴳ(M, H) k) :
    ModularForm Γᴳ(M, H) k :=
  (((M : ℤ) ^ n : ℤ) : ℝ) • dSlash γ hγ f

theorem coe_dSlashM (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (n : ℕ) (f : ModularForm Γᴳ(M, H) k) :
    (⇑(dSlashM γ hγ n f) : ℍ → ℂ) = ((M : ℂ) ^ n) • ((⇑f : ℍ → ℂ) ∣[k] γ) := by
  rw [dSlashM, ModularForm.coe_smul, coe_dSlash]
  funext τ
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem slash_inv_slash (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ⁻¹) ∣[k] γ = F := by
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

theorem slash_slash_inv (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ) ∣[k] γ⁻¹ = F := by
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem exists_pow_slash (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {f : ModularForm Γᴳ(M, H) k}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) :
    ∃ (n : ℕ) (p₁ : PowerSeries ℤ), IsIntegralQExp (⇑(dSlashM γ hγ n f)) p₁ := by
  obtain ⟨n, f₁, p₁, hp₁, hf₁⟩ :=
    exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 M (restrictForm (Gamma1_le M H) f) hp γ hγ
  refine ⟨n, p₁, ?_⟩
  rwa [coe_dSlashM, ← coe_restrictForm (Gamma1_le M H) f, ← hf₁]

theorem isIntegralQExp_intCast_smul' {a : ℤ} {f : ModularForm Γᴳ(M, H) a} {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) (c : ℤ) :
    IsIntegralQExp ((c : ℂ) • (⇑f : ℍ → ℂ)) (PowerSeries.C c * p) := by
  have h := isIntegralQExp_intCast_smul hf c
  have e : (⇑((c : ℝ) • f) : ℍ → ℂ) = (c : ℂ) • (⇑f : ℍ → ℂ) := by
    rw [ModularForm.coe_smul]; funext τ
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_intCast]
  rwa [e] at h

theorem pow_smul_coe_dSlashM (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (m n : ℕ) (f : ModularForm Γᴳ(M, H) k) :
    (((M : ℤ) ^ m : ℤ) : ℂ) • (⇑(dSlashM γ hγ n f) : ℍ → ℂ) = ⇑(dSlashM γ hγ (m + n) f) := by
  rw [coe_dSlashM, coe_dSlashM, smul_smul]
  push_cast
  rw [← _root_.pow_add]

theorem witness_eq (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {f : ModularForm Γᴳ(M, H) k} {a b : ℕ}
    {p p' : PowerSeries ℤ} (hp : IsIntegralQExp (⇑(dSlashM γ hγ a f)) p)
    (hp' : IsIntegralQExp (⇑(dSlashM γ hγ b f)) p') :
    PowerSeries.C ((M : ℤ) ^ b) * p = PowerSeries.C ((M : ℤ) ^ a) * p' := by
  have h1 := isIntegralQExp_intCast_smul' hp ((M : ℤ) ^ b)
  have h2 := isIntegralQExp_intCast_smul' hp' ((M : ℤ) ^ a)
  rw [pow_smul_coe_dSlashM] at h1 h2
  rw [add_comm] at h2
  exact h1.unique h2

theorem red_eq_zero_of_slash (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    {f : ModularForm Γᴳ(M, H) k} {p p₁ : PowerSeries ℤ} {n : ℕ} (hp : IsIntegralQExp f p)
    (hp₁ : IsIntegralQExp (⇑(dSlashM γ hγ n f)) p₁) (h0 : red ℓ p = 0) : red ℓ p₁ = 0 := by
  have hℓ : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hMb : ((M : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Int.cast_natCast]; exact fun h => hℓM ((ZMod.natCast_eq_zero_iff M ℓ).mp h)
  obtain ⟨p', rfl⟩ := (red_eq_zero_iff ℓ p).mp h0

  set f' : ModularForm Γᴳ(M, H) k := ((ℓ : ℤ) : ℝ)⁻¹ • f with hf'def
  have hf' : IsIntegralQExp (⇑f') p' := isIntegralQExp_inv_smul hℓ hp
  obtain ⟨m, p'₁, hp'₁⟩ := exists_pow_slash γ hγ hf'
  have hff' : (⇑f : ℍ → ℂ) = ((ℓ : ℤ) : ℂ) • (⇑f' : ℍ → ℂ) := by
    rw [hf'def, ModularForm.coe_smul]
    funext τ
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_intCast]
    rw [← mul_assoc, mul_inv_cancel₀ (Int.cast_ne_zero.mpr hℓ), one_mul]

  have e1 : IsIntegralQExp ((((M : ℤ) ^ m : ℤ) : ℂ) • (⇑(dSlashM γ hγ n f) : ℍ → ℂ))
      (PowerSeries.C ((M : ℤ) ^ m) * p₁) := isIntegralQExp_intCast_smul' hp₁ _
  have e2 : IsIntegralQExp ((((ℓ : ℤ) * (M : ℤ) ^ n : ℤ) : ℂ) • (⇑(dSlashM γ hγ m f') : ℍ → ℂ))
      (PowerSeries.C ((ℓ : ℤ) * (M : ℤ) ^ n) * p'₁) := isIntegralQExp_intCast_smul' hp'₁ _
  have efun : ((((M : ℤ) ^ m : ℤ) : ℂ) • (⇑(dSlashM γ hγ n f) : ℍ → ℂ))
      = ((((ℓ : ℤ) * (M : ℤ) ^ n : ℤ) : ℂ) • (⇑(dSlashM γ hγ m f') : ℍ → ℂ)) := by
    rw [coe_dSlashM, coe_dSlashM, hff', ModularForm.SL_smul_slash, smul_smul, smul_smul, smul_smul]
    push_cast; ring_nf
  rw [efun] at e1
  have heq := e1.unique e2
  have := congrArg (red ℓ) heq
  rw [map_mul, map_mul, show red ℓ (PowerSeries.C ((ℓ : ℤ) * (M : ℤ) ^ n)) = 0 by
    rw [red, RingHom.comp_apply, PowerSeries.map_C, eq_intCast, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, map_zero, map_zero], zero_mul] at this
  rw [red, RingHom.comp_apply, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C, ← red] at this
  exact (mul_eq_zero.mp this).resolve_left (HahnSeries.C_ne_zero (by rw [Int.cast_pow]; exact pow_ne_zero _ hMb))

theorem red_eq_zero_iff_of_slash (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    {f : ModularForm Γᴳ(M, H) k} {p p₁ : PowerSeries ℤ} {n : ℕ} (hp : IsIntegralQExp f p)
    (hp₁ : IsIntegralQExp (⇑(dSlashM γ hγ n f)) p₁) : red ℓ p₁ = 0 ↔ red ℓ p = 0 := by
  refine ⟨fun h => ?_, red_eq_zero_of_slash ℓ hℓM γ hγ hp hp₁⟩
  have hMb : ((M : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Int.cast_natCast]; exact fun h => hℓM ((ZMod.natCast_eq_zero_iff M ℓ).mp h)

  have hback : IsIntegralQExp (⇑(dSlashM γ⁻¹ (inv_mem hγ) 0 (dSlashM γ hγ n f))) (PowerSeries.C ((M : ℤ) ^ n) * p) := by
    have h1 := isIntegralQExp_intCast_smul' hp ((M : ℤ) ^ n)
    have e : (⇑(dSlashM γ⁻¹ (inv_mem hγ) 0 (dSlashM γ hγ n f)) : ℍ → ℂ) = (((M : ℤ) ^ n : ℤ) : ℂ) • (⇑f : ℍ → ℂ) := by
      rw [coe_dSlashM, coe_dSlashM, ModularForm.SL_smul_slash, slash_slash_inv, pow_zero, one_smul]
      push_cast; rfl
    rwa [e]
  have := red_eq_zero_of_slash ℓ hℓM γ⁻¹ (inv_mem hγ) hp₁ hback h
  rw [map_mul, red, RingHom.comp_apply, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C, ← red] at this
  exact (mul_eq_zero.mp this).resolve_left (HahnSeries.C_ne_zero (by rw [Int.cast_pow]; exact pow_ne_zero _ hMb))

end Slash

section Ratio

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

def IsRatio (z : LaurentSeries (ZMod ℓ)) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm Γᴳ(M, H) k) (pf pg : PowerSeries ℤ),
    IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ red ℓ pg ≠ 0 ∧ z = red ℓ pf / red ℓ pg

variable {ℓ M H}

theorem isRatio_iff_mem (z : LaurentSeries (ZMod ℓ)) :
    IsRatio ℓ M H z ↔ z ∈ intFormRatiosC (ZMod ℓ) (CohCarrier.GammaH M H) := Iff.rfl

theorem red_one_ne_zero : red ℓ 1 ≠ 0 := by rw [map_one]; exact one_ne_zero

theorem isRatio_zero : IsRatio ℓ M H 0 :=
  ⟨0, 0, 1, 0, 1, isIntegralQExp_coe_zero, isIntegralQExp_coe_one, red_one_ne_zero,
    by rw [map_zero, zero_div]⟩

theorem isRatio_one : IsRatio ℓ M H 1 :=
  ⟨0, 1, 1, 1, 1, isIntegralQExp_coe_one, isIntegralQExp_coe_one, red_one_ne_zero,
    by rw [map_one, div_one]⟩

theorem IsRatio.add {x y : LaurentSeries (ZMod ℓ)} (hx : IsRatio ℓ M H x) (hy : IsRatio ℓ M H y) :
    IsRatio ℓ M H (x + y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', rfl⟩ := hy
  refine ⟨k + k', f.mul g' + g.mul f', g.mul g', pf * pg' + pg * pf', pg * pg',
    isIntegralQExp_add (isIntegralQExp_mul hf hg') (isIntegralQExp_mul hg hf'),
    isIntegralQExp_mul hg hg', ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hg0 hg0'
  · rw [map_add, map_mul, map_mul, map_mul, div_add_div _ _ hg0 hg0']

theorem IsRatio.neg {x : LaurentSeries (ZMod ℓ)} (hx : IsRatio ℓ M H x) : IsRatio ℓ M H (-x) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  refine ⟨k, 0 - f, g, 0 - pf, pg, isIntegralQExp_sub isIntegralQExp_coe_zero hf, hg, hg0, ?_⟩
  rw [map_sub, map_zero, zero_sub, neg_div]

theorem IsRatio.mul {x y : LaurentSeries (ZMod ℓ)} (hx : IsRatio ℓ M H x) (hy : IsRatio ℓ M H y) :
    IsRatio ℓ M H (x * y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', rfl⟩ := hy
  refine ⟨k + k', f.mul f', g.mul g', pf * pf', pg * pg', isIntegralQExp_mul hf hf',
    isIntegralQExp_mul hg hg', ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hg0 hg0'
  · rw [map_mul, map_mul, div_mul_div_comm]

theorem IsRatio.inv {x : LaurentSeries (ZMod ℓ)} (hx : IsRatio ℓ M H x) : IsRatio ℓ M H x⁻¹ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  by_cases hf0 : red ℓ pf = 0
  · rw [hf0, zero_div, inv_zero]; exact isRatio_zero
  · exact ⟨k, g, f, pg, pf, hg, hf, hf0, by rw [inv_div]⟩

variable (ℓ M H) in

def ratioField : Subfield (LaurentSeries (ZMod ℓ)) where
  carrier := {x | IsRatio ℓ M H x}
  mul_mem' := IsRatio.mul
  one_mem' := isRatio_one
  add_mem' := IsRatio.add
  zero_mem' := isRatio_zero
  neg_mem' := IsRatio.neg
  inv_mem' _ := IsRatio.inv

theorem mem_ratioField {x : LaurentSeries (ZMod ℓ)} : x ∈ ratioField ℓ M H ↔ IsRatio ℓ M H x := Iff.rfl

theorem algebraMap_mem_ratioField (c : ZMod ℓ) :
    algebraMap (ZMod ℓ) (LaurentSeries (ZMod ℓ)) c ∈ ratioField ℓ M H := by
  have hc : (c.val : ZMod ℓ) = c := ZMod.natCast_zmod_val c
  rw [← hc, map_natCast]
  exact natCast_mem _ _

variable (ℓ M H) in

def ratioFieldIF : IntermediateField (ZMod ℓ) (LaurentSeries (ZMod ℓ)) :=
  (ratioField ℓ M H).toIntermediateField algebraMap_mem_ratioField

theorem qExpFunctionFieldC_eq :
    qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) = ratioFieldIF ℓ M H := by
  refine le_antisymm ?_ ?_
  · rw [qExpFunctionFieldC, adjoin_le_iff]
    intro x hx
    exact hx
  · intro x hx
    exact intFormRatiosC_subset (ZMod ℓ) _ hx

theorem isRatio_of_mem {x : LaurentSeries (ZMod ℓ)}
    (hx : x ∈ qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)) : IsRatio ℓ M H x := by
  rw [qExpFunctionFieldC_eq] at hx; exact hx

theorem mem_of_isRatio {x : LaurentSeries (ZMod ℓ)} (hx : IsRatio ℓ M H x) :
    x ∈ qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) := by
  rw [qExpFunctionFieldC_eq]; exact hx

variable (M) in

abbrev Mb : ZMod ℓ := (M : ZMod ℓ)

theorem Mb_ne_zero (hℓM : ¬ ℓ ∣ M) : Mb (ℓ := ℓ) M ≠ 0 :=
  fun h => hℓM ((ZMod.natCast_eq_zero_iff M ℓ).mp h)

theorem red_C_pow (n : ℕ) : red ℓ (PowerSeries.C ((M : ℤ) ^ n)) = HahnSeries.C (Mb (ℓ := ℓ) M ^ n) := by
  rw [red, RingHom.comp_apply, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C, Int.cast_pow,
    Int.cast_natCast]

def nred (n : ℕ) (p : PowerSeries ℤ) : LaurentSeries (ZMod ℓ) :=
  HahnSeries.C ((Mb (ℓ := ℓ) M ^ n)⁻¹) * red ℓ p

theorem nred_zero (p : PowerSeries ℤ) : nred (ℓ := ℓ) (M := M) 0 p = red ℓ p := by
  rw [nred, pow_zero, inv_one, map_one, one_mul]

theorem nred_eq_nred {k : ℤ} (hℓM : ¬ ℓ ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {f : ModularForm Γᴳ(M, H) k}
    {a b : ℕ} {p p' : PowerSeries ℤ} (hp : IsIntegralQExp (⇑(dSlashM γ hγ a f)) p)
    (hp' : IsIntegralQExp (⇑(dSlashM γ hγ b f)) p') :
    nred (ℓ := ℓ) (M := M) a p = nred (ℓ := ℓ) (M := M) b p' := by
  have h := congrArg (red ℓ) (witness_eq γ hγ hp hp')
  rw [map_mul, map_mul, red_C_pow, red_C_pow] at h
  have hM : Mb (ℓ := ℓ) M ≠ 0 := Mb_ne_zero hℓM
  have ha : (Mb (ℓ := ℓ) M ^ a) ≠ 0 := pow_ne_zero _ hM
  have hb : (Mb (ℓ := ℓ) M ^ b) ≠ 0 := pow_ne_zero _ hM
  rw [nred, nred]
  apply mul_left_cancel₀ (HahnSeries.C_ne_zero (mul_ne_zero ha hb))
  calc HahnSeries.C (Mb (ℓ := ℓ) M ^ a * Mb M ^ b) * (HahnSeries.C ((Mb (ℓ := ℓ) M ^ a)⁻¹) * red ℓ p)
        = HahnSeries.C (Mb (ℓ := ℓ) M ^ b) * red ℓ p := by
          rw [← mul_assoc, ← map_mul]; congr 2; field_simp
    _ = HahnSeries.C (Mb (ℓ := ℓ) M ^ a) * red ℓ p' := h
    _ = HahnSeries.C (Mb (ℓ := ℓ) M ^ a * Mb M ^ b) * (HahnSeries.C ((Mb (ℓ := ℓ) M ^ b)⁻¹) * red ℓ p') := by
          rw [← mul_assoc, ← map_mul]; congr 2; field_simp

theorem nred_eq_zero_iff (hℓM : ¬ ℓ ∣ M) (n : ℕ) (p : PowerSeries ℤ) :
    nred (ℓ := ℓ) (M := M) n p = 0 ↔ red ℓ p = 0 := by
  rw [nred, mul_eq_zero, or_iff_right]
  rw [map_inv₀, inv_eq_zero]
  exact HahnSeries.C_ne_zero (pow_ne_zero _ (Mb_ne_zero hℓM))

theorem nred_mul (a a' : ℕ) (q q' : PowerSeries ℤ) :
    nred (ℓ := ℓ) (M := M) (a + a') (q * q') = nred (ℓ := ℓ) (M := M) a q * nred (ℓ := ℓ) (M := M) a' q' := by
  simp only [nred, map_mul, _root_.pow_add, mul_inv, map_inv₀]
  ring

theorem nred_pow_mul (hℓM : ¬ ℓ ∣ M) (a m : ℕ) (q : PowerSeries ℤ) :
    nred (ℓ := ℓ) (M := M) (m + a) (PowerSeries.C ((M : ℤ) ^ m) * q) = nred (ℓ := ℓ) (M := M) a q := by
  have hM : Mb (ℓ := ℓ) M ≠ 0 := Mb_ne_zero hℓM
  simp only [nred, map_mul, red_C_pow, _root_.pow_add, mul_inv, map_inv₀]
  field_simp

theorem nred_add (a : ℕ) (q q' : PowerSeries ℤ) :
    nred (ℓ := ℓ) (M := M) a (q + q') = nred (ℓ := ℓ) (M := M) a q + nred (ℓ := ℓ) (M := M) a q' := by
  simp only [nred, map_add, mul_add]

theorem nred_exp_add (c e : ℕ) (r : PowerSeries ℤ) :
    nred (ℓ := ℓ) (M := M) (c + e) r = HahnSeries.C ((Mb (ℓ := ℓ) M ^ e)⁻¹) * nred (ℓ := ℓ) (M := M) c r := by
  simp only [nred, _root_.pow_add, mul_inv, map_mul]
  ring

section Pull

variable (hℓM : ¬ ℓ ∣ M)
include hℓM

def slashN (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) : ℕ :=
  (exists_pow_slash γ hγ hp).choose

omit hℓM in
def slashP (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) : PowerSeries ℤ :=
  (exists_pow_slash γ hγ hp).choose_spec.choose

omit hℓM in
theorem slashP_spec (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) :
    IsIntegralQExp (⇑(dSlashM γ hγ (slashN γ hγ hp) f)) (slashP γ hγ hp) :=
  (exists_pow_slash γ hγ hp).choose_spec.choose_spec

def rslash (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) : LaurentSeries (ZMod ℓ) :=
  nred (ℓ := ℓ) (M := M) (slashN γ hγ hp) (slashP γ hγ hp)

theorem rslash_eq (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) {n : ℕ} {q : PowerSeries ℤ}
    (hq : IsIntegralQExp (⇑(dSlashM γ hγ n f)) q) : rslash (ℓ := ℓ) γ hγ hp = nred (ℓ := ℓ) (M := M) n q :=
  nred_eq_nred hℓM γ hγ (slashP_spec γ hγ hp) hq

theorem rslash_ne_zero (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) (h0 : red ℓ p ≠ 0) : rslash (ℓ := ℓ) γ hγ hp ≠ 0 := by
  rw [rslash, Ne, nred_eq_zero_iff hℓM]
  exact fun h => h0 ((red_eq_zero_iff_of_slash ℓ hℓM γ hγ hp (slashP_spec γ hγ hp)).mp h)

theorem cross (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k k' : ℤ}
    {f g : ModularForm Γᴳ(M, H) k} {f' g' : ModularForm Γᴳ(M, H) k'}
    {pf pg pf' pg' : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hf' : IsIntegralQExp f' pf') (hg' : IsIntegralQExp g' pg')
    (hg0 : red ℓ pg ≠ 0) (hg0' : red ℓ pg' ≠ 0)
    (h : red ℓ pf / red ℓ pg = red ℓ pf' / red ℓ pg') :
    rslash (ℓ := ℓ) γ hγ hf / rslash (ℓ := ℓ) γ hγ hg
      = rslash (ℓ := ℓ) γ hγ hf' / rslash (ℓ := ℓ) γ hγ hg' := by
  rw [div_eq_div_iff hg0 hg0'] at h

  set a := slashN γ hγ hf; set b := slashN γ hγ hg; set a' := slashN γ hγ hf'; set b' := slashN γ hγ hg'
  set qf := slashP γ hγ hf; set qg := slashP γ hγ hg; set qf' := slashP γ hγ hf'; set qg' := slashP γ hγ hg'
  have hqf : IsIntegralQExp (⇑(dSlashM γ hγ a f)) qf := slashP_spec γ hγ hf
  have hqg : IsIntegralQExp (⇑(dSlashM γ hγ b g)) qg := slashP_spec γ hγ hg
  have hqf' : IsIntegralQExp (⇑(dSlashM γ hγ a' f')) qf' := slashP_spec γ hγ hf'
  have hqg' : IsIntegralQExp (⇑(dSlashM γ hγ b' g')) qg' := slashP_spec γ hγ hg'

  set h₁ : ModularForm Γᴳ(M, H) (k + k') := f.mul g' - (f'.mul g).mcast (add_comm k' k) with hh₁
  have hh₁int : IsIntegralQExp (⇑h₁) (pf * pg' - pf' * pg) := by
    have h2 : IsIntegralQExp (⇑((f'.mul g).mcast (add_comm k' k) : ModularForm Γᴳ(M, H) (k + k')))
        (pf' * pg) := isIntegralQExp_mul hf' hg
    exact isIntegralQExp_sub (isIntegralQExp_mul hf hg') h2
  have hred : red ℓ (pf * pg' - pf' * pg) = 0 := by rw [map_sub, map_mul, map_mul, h, sub_self]

  have hslash : IsIntegralQExp (⇑(dSlashM γ hγ ((a' + b) + (a + b')) h₁))
      (PowerSeries.C ((M : ℤ) ^ (a' + b)) * (qf * qg') - PowerSeries.C ((M : ℤ) ^ (a + b')) * (qf' * qg)) := by
    have e2 : IsIntegralQExp (⇑((dSlashM γ hγ a f).mul (dSlashM γ hγ b' g'))) (qf * qg') :=
      isIntegralQExp_mul hqf hqg'
    have e3 : IsIntegralQExp (⇑((dSlashM γ hγ a' f').mul (dSlashM γ hγ b g))) (qf' * qg) :=
      isIntegralQExp_mul hqf' hqg
    have e2' := isIntegralQExp_intCast_smul' e2 ((M : ℤ) ^ (a' + b))
    have e3' := isIntegralQExp_intCast_smul' e3 ((M : ℤ) ^ (a + b'))

    have em : ((⇑((f'.mul g).mcast (add_comm k' k) : ModularForm Γᴳ(M, H) (k + k')) : ℍ → ℂ) ∣[k + k'] γ)
        = (⇑f' : ℍ → ℂ) ∣[k'] γ * (⇑g : ℍ → ℂ) ∣[k] γ := by
      change ((⇑f' : ℍ → ℂ) * ⇑g) ∣[k + k'] γ = _
      rw [add_comm k k', ModularForm.mul_slash_SL2]
    have efun : (⇑(dSlashM γ hγ ((a' + b) + (a + b')) h₁) : ℍ → ℂ)
        = (((M : ℤ) ^ (a' + b) : ℤ) : ℂ) • (⇑((dSlashM γ hγ a f).mul (dSlashM γ hγ b' g')) : ℍ → ℂ)
          - (((M : ℤ) ^ (a + b') : ℤ) : ℂ) • (⇑((dSlashM γ hγ a' f').mul (dSlashM γ hγ b g)) : ℍ → ℂ) := by
      rw [coe_dSlashM, hh₁, ModularForm.coe_sub, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
        ← sub_eq_add_neg, ModularForm.coe_mul, ModularForm.mul_slash_SL2, em, ModularForm.coe_mul,
        ModularForm.coe_mul, coe_dSlashM, coe_dSlashM, coe_dSlashM, coe_dSlashM]
      funext τ
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
      push_cast
      ring
    rw [IsIntegralQExp, efun, map_sub]
    rw [IsIntegralQExp] at e2' e3'
    rw [e2', e3']
    have a1 : AnalyticAt ℂ (cuspFunction 1 ((((M : ℤ) ^ (a' + b) : ℤ) : ℂ) •
        (⇑((dSlashM γ hγ a f).mul (dSlashM γ hγ b' g')) : ℍ → ℂ))) 0 := by
      have := ModularFormClass.analyticAt_cuspFunction_zero
        ((((M : ℤ) ^ (a' + b) : ℤ) : ℝ) • ((dSlashM γ hγ a f).mul (dSlashM γ hγ b' g')))
        one_pos (one_mem_strictPeriods M H)
      convert this using 2
      all_goals try rfl
    have a2 : AnalyticAt ℂ (cuspFunction 1 ((((M : ℤ) ^ (a + b') : ℤ) : ℂ) •
        (⇑((dSlashM γ hγ a' f').mul (dSlashM γ hγ b g)) : ℍ → ℂ))) 0 := by
      have := ModularFormClass.analyticAt_cuspFunction_zero
        ((((M : ℤ) ^ (a + b') : ℤ) : ℝ) • ((dSlashM γ hγ a' f').mul (dSlashM γ hγ b g)))
        one_pos (one_mem_strictPeriods M H)
      convert this using 2
      all_goals try rfl
    rw [qExpansion_sub a1 a2]
  have hred' := red_eq_zero_of_slash ℓ hℓM γ hγ hh₁int hslash hred
  simp only [map_sub, map_mul, red_C_pow] at hred'
  rw [sub_eq_zero] at hred'

  have hM : Mb (ℓ := ℓ) M ≠ 0 := Mb_ne_zero hℓM
  have hqg0 : red ℓ qg ≠ 0 := fun h0 => hg0 ((red_eq_zero_iff_of_slash ℓ hℓM γ hγ hg hqg).mp h0)
  have hqg0' : red ℓ qg' ≠ 0 := fun h0 => hg0' ((red_eq_zero_iff_of_slash ℓ hℓM γ hγ hg' hqg').mp h0)
  have hz1 : rslash (ℓ := ℓ) γ hγ hg ≠ 0 := rslash_ne_zero hℓM γ hγ hg hg0
  have hz2 : rslash (ℓ := ℓ) γ hγ hg' ≠ 0 := rslash_ne_zero hℓM γ hγ hg' hg0'
  rw [div_eq_div_iff hz1 hz2]
  change nred a qf * nred b' qg' = nred a' qf' * nred b qg
  rw [← nred_mul, ← nred_mul]
  simp only [nred]
  rw [map_mul (red ℓ) qf, map_mul (red ℓ) qf']
  have hP : (Mb (ℓ := ℓ) M ^ (a + b')) ≠ 0 := pow_ne_zero _ hM
  have hQ : (Mb (ℓ := ℓ) M ^ (a' + b)) ≠ 0 := pow_ne_zero _ hM
  apply mul_left_cancel₀ (HahnSeries.C_ne_zero (mul_ne_zero hP hQ))
  calc HahnSeries.C (Mb (ℓ := ℓ) M ^ (a + b') * Mb M ^ (a' + b))
          * (HahnSeries.C ((Mb (ℓ := ℓ) M ^ (a + b'))⁻¹) * (red ℓ qf * red ℓ qg'))
        = HahnSeries.C (Mb (ℓ := ℓ) M ^ (a' + b)) * (red ℓ qf * red ℓ qg') := by
          rw [← mul_assoc, ← map_mul]; congr 2; field_simp
    _ = HahnSeries.C (Mb (ℓ := ℓ) M ^ (a + b')) * (red ℓ qf' * red ℓ qg) := hred'
    _ = HahnSeries.C (Mb (ℓ := ℓ) M ^ (a + b') * Mb M ^ (a' + b))
          * (HahnSeries.C ((Mb (ℓ := ℓ) M ^ (a' + b))⁻¹) * (red ℓ qf' * red ℓ qg)) := by
          symm
          rw [← mul_assoc, ← map_mul]; congr 2; field_simp

abbrev Fbar : Type _ := ↥(qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H))

def pull (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    LaurentSeries (ZMod ℓ) :=
  let hx := isRatio_of_mem x.2
  rslash (ℓ := ℓ) γ hγ hx.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 /
    rslash (ℓ := ℓ) γ hγ hx.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1

theorem pull_eq (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : Fbar (ℓ := ℓ) (M := M) (H := H))
    {k : ℤ} {f g : ModularForm Γᴳ(M, H) k} {pf pg qf qg : PowerSeries ℤ} {a b : ℕ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hqf : IsIntegralQExp (⇑(dSlashM γ hγ a f)) qf) (hqg : IsIntegralQExp (⇑(dSlashM γ hγ b g)) qg)
    (hg0 : red ℓ pg ≠ 0) (hx : (x : LaurentSeries (ZMod ℓ)) = red ℓ pf / red ℓ pg) :
    pull γ hγ x = nred (ℓ := ℓ) (M := M) a qf / nred (ℓ := ℓ) (M := M) b qg := by
  have hR := isRatio_of_mem x.2
  have hspec := hR.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  rw [← rslash_eq hℓM γ hγ hf hqf, ← rslash_eq hℓM γ hγ hg hqg]
  exact cross hℓM γ hγ hspec.1 hspec.2.1 hf hg hspec.2.2.1 hg0 (hspec.2.2.2.symm.trans hx)

omit hℓM in

theorem witness_of_invariant (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) (hinv : (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f) :
    IsIntegralQExp (⇑(dSlashM γ hγ 0 f)) p := by
  rw [coe_dSlashM, hinv, pow_zero, one_smul]; exact hp

theorem pull_one (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : pull (ℓ := ℓ) (M := M) (H := H) γ hγ 1 = 1 := by
  have h1 : IsIntegralQExp (⇑(dSlashM γ hγ 0 (1 : ModularForm Γᴳ(M, H) 0))) 1 :=
    witness_of_invariant γ hγ isIntegralQExp_coe_one
      (by rw [ModularForm.one_coe_eq_one, ModularForm.is_invariant_one])
  rw [pull_eq hℓM γ hγ 1 isIntegralQExp_coe_one isIntegralQExp_coe_one h1 h1 red_one_ne_zero
    (by rw [map_one, div_one]; rfl), nred_zero, map_one, div_one]

theorem pull_zero (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : pull (ℓ := ℓ) (M := M) (H := H) γ hγ 0 = 0 := by
  have h1 : IsIntegralQExp (⇑(dSlashM γ hγ 0 (1 : ModularForm Γᴳ(M, H) 0))) 1 :=
    witness_of_invariant γ hγ isIntegralQExp_coe_one
      (by rw [ModularForm.one_coe_eq_one, ModularForm.is_invariant_one])
  have h0 : IsIntegralQExp (⇑(dSlashM γ hγ 0 (0 : ModularForm Γᴳ(M, H) 0))) 0 :=
    witness_of_invariant γ hγ isIntegralQExp_coe_zero (by rw [ModularForm.coe_zero, SlashAction.zero_slash])
  rw [pull_eq hℓM γ hγ 0 isIntegralQExp_coe_zero isIntegralQExp_coe_one h0 h1 red_one_ne_zero
    (by rw [map_zero, zero_div]; rfl), nred_zero, map_zero, zero_div]

omit hℓM in

theorem witness_mul (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k k' : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {f' : ModularForm Γᴳ(M, H) k'} {a a' : ℕ} {q q' : PowerSeries ℤ}
    (hq : IsIntegralQExp (⇑(dSlashM γ hγ a f)) q) (hq' : IsIntegralQExp (⇑(dSlashM γ hγ a' f')) q') :
    IsIntegralQExp (⇑(dSlashM γ hγ (a + a') (f.mul f'))) (q * q') := by
  have h := isIntegralQExp_mul hq hq'
  have e : (⇑((dSlashM γ hγ a f).mul (dSlashM γ hγ a' f')) : ℍ → ℂ) = ⇑(dSlashM γ hγ (a + a') (f.mul f')) := by
    rw [ModularForm.coe_mul, coe_dSlashM, coe_dSlashM, coe_dSlashM, ModularForm.coe_mul,
      ModularForm.mul_slash_SL2]
    funext τ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, _root_.pow_add]
    ring
  rwa [e] at h

omit hℓM in

theorem witness_add (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f f' : ModularForm Γᴳ(M, H) k}
    {a : ℕ} {q q' : PowerSeries ℤ}
    (hq : IsIntegralQExp (⇑(dSlashM γ hγ a f)) q) (hq' : IsIntegralQExp (⇑(dSlashM γ hγ a f')) q') :
    IsIntegralQExp (⇑(dSlashM γ hγ a (f + f'))) (q + q') := by
  have h := isIntegralQExp_add hq hq'
  have e : (⇑(dSlashM γ hγ a f + dSlashM γ hγ a f') : ℍ → ℂ) = ⇑(dSlashM γ hγ a (f + f')) := by
    rw [ModularForm.coe_add, coe_dSlashM, coe_dSlashM, coe_dSlashM, ModularForm.coe_add,
      SlashAction.add_slash, smul_add]
  rwa [e] at h

omit hℓM in

theorem witness_pow_mul (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {f : ModularForm Γᴳ(M, H) k}
    {a : ℕ} {q : PowerSeries ℤ} (hq : IsIntegralQExp (⇑(dSlashM γ hγ a f)) q) (m : ℕ) :
    IsIntegralQExp (⇑(dSlashM γ hγ (m + a) f)) (PowerSeries.C ((M : ℤ) ^ m) * q) := by
  have h := isIntegralQExp_intCast_smul' hq ((M : ℤ) ^ m)
  rwa [pow_smul_coe_dSlashM] at h

theorem pull_mul (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x y : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    pull γ hγ (x * y) = pull γ hγ x * pull γ hγ y := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx⟩ := isRatio_of_mem x.2
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', hy⟩ := isRatio_of_mem y.2
  have hxy : ((x * y : Fbar) : LaurentSeries (ZMod ℓ)) = red ℓ (pf * pf') / red ℓ (pg * pg') := by
    rw [IntermediateField.coe_mul, hx, hy, map_mul, map_mul, div_mul_div_comm]
  rw [pull_eq hℓM γ hγ x hf hg (slashP_spec γ hγ hf) (slashP_spec γ hγ hg) hg0 hx,
    pull_eq hℓM γ hγ y hf' hg' (slashP_spec γ hγ hf') (slashP_spec γ hγ hg') hg0' hy,
    pull_eq hℓM γ hγ (x * y) (isIntegralQExp_mul hf hf') (isIntegralQExp_mul hg hg')
      (witness_mul γ hγ (slashP_spec γ hγ hf) (slashP_spec γ hγ hf'))
      (witness_mul γ hγ (slashP_spec γ hγ hg) (slashP_spec γ hγ hg'))
      (by rw [map_mul]; exact mul_ne_zero hg0 hg0') hxy,
    nred_mul, nred_mul, div_mul_div_comm]

theorem pull_add (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x y : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    pull γ hγ (x + y) = pull γ hγ x + pull γ hγ y := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx⟩ := isRatio_of_mem x.2
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', hy⟩ := isRatio_of_mem y.2
  have hxy : ((x + y : Fbar) : LaurentSeries (ZMod ℓ))
      = red ℓ (pf * pg' + pg * pf') / red ℓ (pg * pg') := by
    rw [IntermediateField.coe_add, hx, hy, map_add, map_mul, map_mul, map_mul, div_add_div _ _ hg0 hg0']

  set a := slashN γ hγ hf; set b := slashN γ hγ hg; set a' := slashN γ hγ hf'; set b' := slashN γ hγ hg'
  have h1 : IsIntegralQExp (⇑(dSlashM γ hγ ((b + a') + (a + b')) (f.mul g')))
      (PowerSeries.C ((M : ℤ) ^ (b + a')) * (slashP γ hγ hf * slashP γ hγ hg')) :=
    witness_pow_mul γ hγ (witness_mul γ hγ (slashP_spec γ hγ hf) (slashP_spec γ hγ hg')) _
  have h2 : IsIntegralQExp (⇑(dSlashM γ hγ ((a + b') + (b + a')) (g.mul f')))
      (PowerSeries.C ((M : ℤ) ^ (a + b')) * (slashP γ hγ hg * slashP γ hγ hf')) :=
    witness_pow_mul γ hγ (witness_mul γ hγ (slashP_spec γ hγ hg) (slashP_spec γ hγ hf')) _
  rw [add_comm (a + b') (b + a')] at h2
  have hnum := witness_add γ hγ h1 h2
  have hden := witness_mul γ hγ (slashP_spec γ hγ hg) (slashP_spec γ hγ hg')
  rw [pull_eq hℓM γ hγ x hf hg (slashP_spec γ hγ hf) (slashP_spec γ hγ hg) hg0 hx,
    pull_eq hℓM γ hγ y hf' hg' (slashP_spec γ hγ hf') (slashP_spec γ hγ hg') hg0' hy,
    pull_eq hℓM γ hγ (x + y) (isIntegralQExp_add (isIntegralQExp_mul hf hg') (isIntegralQExp_mul hg hf'))
      (isIntegralQExp_mul hg hg') hnum hden (by rw [map_mul]; exact mul_ne_zero hg0 hg0') hxy,
    nred_add, nred_pow_mul hℓM, add_comm (b + a') (a + b'), nred_pow_mul hℓM, nred_mul, nred_mul, nred_mul]
  have hz1 : nred (ℓ := ℓ) (M := M) (slashN γ hγ hg) (slashP γ hγ hg) ≠ 0 := rslash_ne_zero hℓM γ hγ hg hg0
  have hz2 : nred (ℓ := ℓ) (M := M) (slashN γ hγ hg') (slashP γ hγ hg') ≠ 0 := rslash_ne_zero hℓM γ hγ hg' hg0'
  rw [div_add_div _ _ hz1 hz2]

theorem pull_mem (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    pull γ hγ x ∈ qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx⟩ := isRatio_of_mem x.2

  set a := slashN γ hγ hf; set b := slashN γ hγ hg
  have h1 := witness_pow_mul γ hγ (slashP_spec γ hγ hf) b
  have h2 := witness_pow_mul γ hγ (slashP_spec γ hγ hg) a
  rw [add_comm a b] at h2
  rw [pull_eq hℓM γ hγ x hf hg h1 h2 hg0 hx, nred, nred, mul_div_mul_left _ _
    (HahnSeries.C_ne_zero (inv_ne_zero (pow_ne_zero _ (Mb_ne_zero hℓM))))]
  refine mem_of_isRatio ⟨k, dSlashM γ hγ (b + a) f, dSlashM γ hγ (b + a) g, _, _, h1, h2, ?_, rfl⟩
  intro h0
  have := (red_eq_zero_iff_of_slash ℓ hℓM γ hγ hg h2).mp h0
  exact hg0 this

def pullHom (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    Fbar (ℓ := ℓ) (M := M) (H := H) →+* Fbar (ℓ := ℓ) (M := M) (H := H) where
  toFun x := ⟨pull γ hγ x, pull_mem hℓM γ hγ x⟩
  map_one' := Subtype.ext (pull_one hℓM γ hγ)
  map_mul' x y := Subtype.ext (pull_mul hℓM γ hγ x y)
  map_zero' := Subtype.ext (pull_zero hℓM γ hγ)
  map_add' x y := Subtype.ext (pull_add hℓM γ hγ x y)

theorem coe_pullHom (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    ((pullHom hℓM γ hγ x : Fbar) : LaurentSeries (ZMod ℓ)) = pull γ hγ x := rfl

omit hℓM in

theorem witness_comp (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma0 M) {k : ℤ}
    {f : ModularForm Γᴳ(M, H) k} {a c : ℕ} {r : PowerSeries ℤ}
    (hr : IsIntegralQExp (⇑(dSlashM δ hδ c (dSlashM γ hγ a f))) r) :
    IsIntegralQExp (⇑(dSlashM (γ * δ) (mul_mem hγ hδ) (c + a) f)) r := by
  have e : (⇑(dSlashM δ hδ c (dSlashM γ hγ a f)) : ℍ → ℂ) = ⇑(dSlashM (γ * δ) (mul_mem hγ hδ) (c + a) f) := by
    rw [coe_dSlashM, coe_dSlashM, coe_dSlashM, ModularForm.SL_smul_slash, smul_smul, ← SlashAction.slash_mul,
      _root_.pow_add]
  rwa [e] at hr

theorem pull_pull (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma0 M)
    (x : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    pull δ hδ (pullHom hℓM γ hγ x) = pull (γ * δ) (mul_mem hγ hδ) x := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx⟩ := isRatio_of_mem x.2
  set a := slashN γ hγ hf; set b := slashN γ hγ hg
  have h1 := witness_pow_mul γ hγ (slashP_spec γ hγ hf) b
  have h2 := witness_pow_mul γ hγ (slashP_spec γ hγ hg) a
  rw [add_comm a b] at h2
  have hne : red ℓ (PowerSeries.C ((M : ℤ) ^ a) * slashP γ hγ hg) ≠ 0 := fun h0 =>
    hg0 ((red_eq_zero_iff_of_slash ℓ hℓM γ hγ hg h2).mp h0)
  have hx1 : ((pullHom hℓM γ hγ x : Fbar) : LaurentSeries (ZMod ℓ))
      = red ℓ (PowerSeries.C ((M : ℤ) ^ b) * slashP γ hγ hf) / red ℓ (PowerSeries.C ((M : ℤ) ^ a) * slashP γ hγ hg) := by
    rw [coe_pullHom, pull_eq hℓM γ hγ x hf hg h1 h2 hg0 hx, nred, nred, mul_div_mul_left _ _
      (HahnSeries.C_ne_zero (inv_ne_zero (pow_ne_zero _ (Mb_ne_zero hℓM))))]

  have hf2 := slashP_spec δ hδ h1
  have hg2 := slashP_spec δ hδ h2
  rw [pull_eq hℓM δ hδ _ h1 h2 hf2 hg2 hne hx1,
    pull_eq hℓM (γ * δ) (mul_mem hγ hδ) x hf hg (witness_comp γ δ hγ hδ hf2) (witness_comp γ δ hγ hδ hg2)
      hg0 hx,
    nred_exp_add, nred_exp_add, mul_div_mul_left _ _
      (HahnSeries.C_ne_zero (inv_ne_zero (pow_ne_zero _ (Mb_ne_zero hℓM))))]

theorem pull_one_eq (x : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    pull 1 (one_mem _) x = (x : LaurentSeries (ZMod ℓ)) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx⟩ := isRatio_of_mem x.2
  rw [pull_eq hℓM 1 (one_mem _) x hf hg
    (witness_of_invariant 1 (one_mem _) hf (SlashAction.slash_one _ _))
    (witness_of_invariant 1 (one_mem _) hg (SlashAction.slash_one _ _)) hg0 hx, nred_zero, nred_zero, hx]

def sigma (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    Fbar (ℓ := ℓ) (M := M) (H := H) ≃ₐ[ZMod ℓ] Fbar (ℓ := ℓ) (M := M) (H := H) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (pullHom hℓM γ hγ) (pullHom hℓM γ⁻¹ (inv_mem hγ))
    (RingHom.ext fun x => Subtype.ext (by
      change pull γ hγ (pullHom hℓM γ⁻¹ (inv_mem hγ) x) = (x : LaurentSeries (ZMod ℓ))
      rw [pull_pull]
      have : γ⁻¹ * γ = 1 := inv_mul_cancel γ
      simp only [this]
      exact pull_one_eq hℓM x))
    (RingHom.ext fun x => Subtype.ext (by
      change pull γ⁻¹ (inv_mem hγ) (pullHom hℓM γ hγ x) = (x : LaurentSeries (ZMod ℓ))
      rw [pull_pull]
      have : γ * γ⁻¹ = 1 := mul_inv_cancel γ
      simp only [this]
      exact pull_one_eq hℓM x)))
    (fun c => by
      have hc : (c.val : ZMod ℓ) = c := ZMod.natCast_zmod_val c
      change pullHom hℓM γ hγ (algebraMap (ZMod ℓ) Fbar c) = algebraMap (ZMod ℓ) Fbar c
      rw [← hc, map_natCast, map_natCast])

theorem coe_sigma (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    ((sigma hℓM γ hγ x : Fbar) : LaurentSeries (ZMod ℓ)) = pull γ hγ x := rfl

theorem sigma_mul (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma0 M) :
    sigma (ℓ := ℓ) (M := M) (H := H) hℓM (γ * δ) (mul_mem hγ hδ) = sigma hℓM δ hδ * sigma hℓM γ hγ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  change pull (γ * δ) (mul_mem hγ hδ) x = pull δ hδ (pullHom hℓM γ hγ x)
  rw [pull_pull]

theorem sigma_one : sigma (ℓ := ℓ) (M := M) (H := H) hℓM 1 (one_mem _) = 1 := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  exact pull_one_eq hℓM x

def rho : Gamma0 M →* (Fbar (ℓ := ℓ) (M := M) (H := H) ≃ₐ[ZMod ℓ] Fbar (ℓ := ℓ) (M := M) (H := H)) where
  toFun γ := sigma hℓM (γ⁻¹ : SL(2, ℤ)) (inv_mem γ.2)
  map_one' := by
    have : ((1 : Gamma0 M) : SL(2, ℤ))⁻¹ = 1 := by simp
    simp only [this]
    exact sigma_one hℓM
  map_mul' γ δ := by
    have h : ((γ * δ : Gamma0 M) : SL(2, ℤ))⁻¹ = (δ : SL(2, ℤ))⁻¹ * (γ : SL(2, ℤ))⁻¹ := by
      rw [Subgroup.coe_mul, mul_inv_rev]
    simp only [h]
    rw [sigma_mul hℓM _ _ (inv_mem δ.2) (inv_mem γ.2)]

theorem rho_apply (γ : Gamma0 M) : rho (H := H) hℓM γ = sigma hℓM (γ⁻¹ : SL(2, ℤ)) (inv_mem γ.2) := rfl

end Pull

end Ratio

section Clauses

open CohCarrier

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (hℓM : ¬ ℓ ∣ M)

theorem mem_sup_zpowers_neg_one_iff (u : (ZMod M)ˣ) :
    u ∈ H ⊔ Subgroup.zpowers (-1) ↔ u ∈ H ∨ -u ∈ H := by
  constructor
  · intro hu
    rw [Subgroup.mem_sup] at hu
    obtain ⟨y, hy, z, hz, rfl⟩ := hu
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    rcases Int.even_or_odd n with hn | hn
    · left; rw [hn.neg_one_zpow, mul_one]; exact hy
    · right; rw [hn.neg_one_zpow, mul_neg_one, neg_neg]; exact hy
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : u = -u * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem neg_mem_Gamma0 {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at h ⊢
  simp [h]

theorem gamma0Units_neg (γ : SL(2, ℤ)) (h : γ ∈ Gamma0 M) :
    gamma0Units M ⟨-γ, neg_mem_Gamma0 h⟩ = -gamma0Units M ⟨γ, h⟩ := by
  ext
  simp [Gamma0Map]

theorem mem_or_neg_mem_of_mem_GammaH_sup (γ : SL(2, ℤ))
    (hγ : γ ∈ GammaH M (H ⊔ Subgroup.zpowers (-1))) : γ ∈ GammaH M H ∨ -γ ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  rcases (mem_sup_zpowers_neg_one_iff _).mp hγH with h | h
  · exact Or.inl (mem_GammaH_iff.mpr ⟨hγ0, h⟩)
  · refine Or.inr (mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγ0, ?_⟩)
    rw [gamma0Units_neg]
    exact h

def sgn (k : ℤ) : ℤ := if Even k then 1 else -1

theorem sgn_ne_zero (k : ℤ) : (sgn k : ZMod ℓ) ≠ 0 := by
  unfold sgn; split_ifs <;> simp

theorem slash_neg_SL {k : ℤ} (F : ℍ → ℂ) (δ : SL(2, ℤ)) :
    F ∣[k] (-δ) = ((sgn k : ℤ) : ℂ) • (F ∣[k] δ) := by
  funext τ
  rw [Pi.smul_apply, smul_eq_mul, ModularForm.SL_slash_apply, ModularForm.SL_slash_apply]
  have h1 : (-δ) • τ = δ • τ := by simp
  have h2 : denom (-δ : SL(2, ℤ)) τ = -denom δ τ := by
    simp [denom]; ring
  rw [h1, h2]
  unfold sgn
  rcases Int.even_or_odd k with hk | hk
  · rw [if_pos hk, (Even.neg hk).neg_zpow, Int.cast_one, one_mul]
  · rw [if_neg (Int.not_even_iff_odd.mpr hk), (Odd.neg hk).neg_zpow, Int.cast_neg, Int.cast_one]
    ring

theorem witness_of_mem_sup {k : ℤ} (f : ModularForm Γᴳ(M, H) k) {p : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH M (H ⊔ Subgroup.zpowers (-1))) :
    ∃ ε : ℤ, (ε : ZMod ℓ) ≠ 0 ∧
      IsIntegralQExp (⇑(dSlashM δ (GammaH_le_Gamma0 _ hδ) 0 f)) (PowerSeries.C ε * p) := by
  rcases mem_or_neg_mem_of_mem_GammaH_sup δ hδ with h | h
  · refine ⟨1, by simp, ?_⟩
    rw [map_one, one_mul]
    refine witness_of_invariant δ _ hp ?_
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ h)
  · refine ⟨sgn k, sgn_ne_zero k, ?_⟩
    have h1 : (⇑f : ℍ → ℂ) ∣[k] (-δ) = ⇑f := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ h)
    have h2 : (⇑f : ℍ → ℂ) ∣[k] δ = ((sgn k : ℤ) : ℂ) • (⇑f : ℍ → ℂ) := by
      conv_lhs => rw [← neg_neg δ]
      rw [slash_neg_SL, h1]
    rw [coe_dSlashM, pow_zero, one_smul, IsIntegralQExp, h2,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M H) _ f, ← hp, map_mul, PowerSeries.map_C,
      eq_intCast, PowerSeries.smul_eq_C_mul]

include hℓM in
theorem pull_eq_self_of_mem_sup {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH M (H ⊔ Subgroup.zpowers (-1)))
    (x : Fbar (ℓ := ℓ) (M := M) (H := H)) :
    pull δ (GammaH_le_Gamma0 _ hδ) x = (x : LaurentSeries (ZMod ℓ)) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx⟩ := isRatio_of_mem x.2
  have hδ0 : δ ∈ Gamma0 M := GammaH_le_Gamma0 _ hδ
  obtain ⟨ε, hε, hwf⟩ := witness_of_mem_sup (ℓ := ℓ) f hf hδ
  obtain ⟨ε', hε', hwg⟩ := witness_of_mem_sup (ℓ := ℓ) g hg hδ

  rcases mem_or_neg_mem_of_mem_GammaH_sup δ hδ with h | h
  · have ef : (⇑f : ℍ → ℂ) ∣[k] δ = ⇑f := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ h)
    have eg : (⇑g : ℍ → ℂ) ∣[k] δ = ⇑g := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ h)
    rw [pull_eq hℓM δ hδ0 x hf hg (witness_of_invariant δ hδ0 hf ef) (witness_of_invariant δ hδ0 hg eg) hg0 hx,
      nred_zero, nred_zero, hx]
  · have key : ∀ (F : ModularForm Γᴳ(M, H) k) (p : PowerSeries ℤ), IsIntegralQExp F p →
        IsIntegralQExp (⇑(dSlashM δ hδ0 0 F)) (PowerSeries.C (sgn k) * p) := by
      intro F p hp
      have h1 : (⇑F : ℍ → ℂ) ∣[k] (-δ) = ⇑F := by
        rw [ModularForm.SL_slash]
        exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ h)
      have h2 : (⇑F : ℍ → ℂ) ∣[k] δ = ((sgn k : ℤ) : ℂ) • (⇑F : ℍ → ℂ) := by
        conv_lhs => rw [← neg_neg δ]
        rw [slash_neg_SL, h1]
      rw [coe_dSlashM, pow_zero, one_smul, IsIntegralQExp, h2,
        ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M H) _ F, ← hp, map_mul, PowerSeries.map_C,
        eq_intCast, PowerSeries.smul_eq_C_mul]
    rw [pull_eq hℓM δ hδ0 x hf hg (key f pf hf) (key g pg hg) hg0 hx, nred_zero, nred_zero, hx, map_mul, map_mul,
      mul_div_mul_left]
    rw [red, RingHom.comp_apply, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C]
    exact HahnSeries.C_ne_zero (sgn_ne_zero k)

include hℓM in
theorem rho_eq_one_of_mem_sup (γ : Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ GammaH M (H ⊔ Subgroup.zpowers (-1))) : rho (H := H) hℓM γ = 1 := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [rho_apply, coe_sigma]
  exact pull_eq_self_of_mem_sup hℓM (inv_mem hγ) x

theorem le_Gamma0 :
    Γᴳ(M, H) ≤ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (GammaH_le_Gamma0 H)

theorem exists_ratio_jqModCd (d : ℕ) [NeZero d] (hd : d ∣ M) :
    ∃ (k : ℤ) (f g : ModularForm ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
      (pf pg : PowerSeries ℤ), IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ red ℓ pg ≠ 0 ∧
        qExpand (ZMod ℓ) d (jqModC (ZMod ℓ)) = red ℓ pf / red ℓ pg := by
  have hsub := qExpand_image_intFormRatiosC_subset (ZMod ℓ) (Γ := ⊤) (Γ' := Gamma0 M)
    (Subgroup.mem_top _) d (by
      intro γ hγ
      have hc : (M : ℤ) ∣ γ 1 0 := by
        rw [Gamma0_mem] at hγ
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
      obtain ⟨c, hc⟩ := (Int.natCast_dvd_natCast.mpr hd |>.trans hc : (d : ℤ) ∣ γ 1 0)
      refine ⟨⟨!![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1], ?_⟩, Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        have := γ.det_coe
        rw [Matrix.det_fin_two, hc] at this
        linear_combination this
      all_goals simp [hc])
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, h⟩ :=
    hsub ⟨jqModC (ZMod ℓ), jqModC_mem_intFormRatiosC (ZMod ℓ) ⊤, rfl⟩
  exact ⟨k, f, g, pf, pg, hf, hg, hg0, h⟩

include hℓM in

theorem pull_eq_self_of_eq_jqModCd (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (d : ℕ) [NeZero d] (hd : d ∣ M)
    (x : Fbar (ℓ := ℓ) (M := M) (H := H))
    (hx : (x : LaurentSeries (ZMod ℓ)) = qExpand (ZMod ℓ) d (jqModC (ZMod ℓ))) :
    pull γ hγ x = (x : LaurentSeries (ZMod ℓ)) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, h⟩ := exists_ratio_jqModCd (ℓ := ℓ) (M := M) d hd
  set f' : ModularForm Γᴳ(M, H) k := restrictForm le_Gamma0 f
  set g' : ModularForm Γᴳ(M, H) k := restrictForm le_Gamma0 g
  have ef : (⇑f' : ℍ → ℂ) ∣[k] γ = ⇑f' := by
    rw [ModularForm.SL_slash, coe_restrictForm]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)
  have eg : (⇑g' : ℍ → ℂ) ∣[k] γ = ⇑g' := by
    rw [ModularForm.SL_slash, coe_restrictForm]
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)
  rw [pull_eq hℓM γ hγ x (f := f') (g := g') hf hg (witness_of_invariant γ hγ hf ef)
    (witness_of_invariant γ hγ hg eg) hg0 (hx.trans h), nred_zero, nred_zero, ← h, hx]

def fixedIF (e : Fbar (ℓ := ℓ) (M := M) (H := H) ≃ₐ[ZMod ℓ] Fbar (ℓ := ℓ) (M := M) (H := H)) :
    IntermediateField (ZMod ℓ) (Fbar (ℓ := ℓ) (M := M) (H := H)) where
  carrier := {y | e y = y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
  one_mem' := map_one e
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
  zero_mem' := map_zero e
  algebraMap_mem' c := e.commutes c
  inv_mem' x hx := by
    simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx]

include hℓM in
theorem full_le_lift_fixedIF (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    modularFunctionFieldFullC (ZMod ℓ) M ≤
      IntermediateField.lift (F := qExpFunctionFieldC (ZMod ℓ) (GammaH M H)) (fixedIF (sigma (H := H) hℓM γ hγ)) := by
  rw [modularFunctionFieldFullC, adjoin_le_iff]
  rintro y ⟨d, hne, hd, rfl⟩
  haveI := hne
  have hmem : qExpand (ZMod ℓ) d (jqModC (ZMod ℓ)) ∈ qExpFunctionFieldC (ZMod ℓ) (GammaH M H) := by
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, h⟩ := exists_ratio_jqModCd (ℓ := ℓ) (M := M) d hd
    rw [h]
    exact mem_of_isRatio ⟨k, restrictForm le_Gamma0 f, restrictForm le_Gamma0 g, pf, pg, hf, hg, hg0, rfl⟩
  have : (⟨_, hmem⟩ : Fbar) ∈ fixedIF (sigma (H := H) hℓM γ hγ) := by
    change sigma hℓM γ hγ ⟨_, hmem⟩ = ⟨_, hmem⟩
    exact Subtype.ext (pull_eq_self_of_eq_jqModCd hℓM γ hγ d hd _ rfl)
  exact (mem_lift (⟨_, hmem⟩ : Fbar)).mpr this

include hℓM in

theorem full_le :
    modularFunctionFieldFullC (ZMod ℓ) M ≤ qExpFunctionFieldC (ZMod ℓ) (GammaH M H) :=
  (full_le_lift_fixedIF (ℓ := ℓ) (H := H) hℓM 1 (one_mem _)).trans (lift_le _)

include hℓM in
theorem rho_apply_eq_self_of_mem_full (γ : Gamma0 M) (x : Fbar (ℓ := ℓ) (M := M) (H := H))
    (hx : (x : LaurentSeries (ZMod ℓ)) ∈ modularFunctionFieldFullC (ZMod ℓ) M) : rho (H := H) hℓM γ x = x := by
  have h := full_le_lift_fixedIF (ℓ := ℓ) (H := H) hℓM (γ⁻¹ : SL(2, ℤ)) (inv_mem γ.2) hx
  exact (mem_lift x).mp h

end Clauses

end XHDiamondModL
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod.XHDiamondModL"

open XHDiamondModL in

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M) (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) ≃ₐ[ZMod ℓ]
          ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)),
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
          (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (p : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f p →
          ∃ (n : ℕ) (f₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (p₁ : PowerSeries ℤ),
            (⇑f₁ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ n) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) ∧
            ModularCurve.IsIntegralQExp f₁ p₁ ∧
            (ModularCurve.intSeriesC (ZMod ℓ) p₁ = 0 ↔ ModularCurve.intSeriesC (ZMod ℓ) p = 0)) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
          (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg pf₁ pg₁ : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg →
          ModularCurve.IsIntegralQExp f₁ pf₁ → ModularCurve.IsIntegralQExp g₁ pg₁ →
          (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
          (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
          ModularCurve.intSeriesC (ZMod ℓ) pg ≠ 0 →
          ∀ x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H),
            (x : LaurentSeries (ZMod ℓ)) =
                ModularCurve.intSeriesC (ZMod ℓ) pf₁ / ModularCurve.intSeriesC (ZMod ℓ) pg₁ →
            ((ρ γ x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)) :
                LaurentSeries (ZMod ℓ)) =
              ModularCurve.intSeriesC (ZMod ℓ) pf / ModularCurve.intSeriesC (ZMod ℓ) pg) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M,
          (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1)) → ρ γ = 1) ∧
      ModularCurve.modularFunctionFieldFullC (ZMod ℓ) M ≤
        ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M)
          (x : ModularCurve.qExpFunctionFieldC (ZMod ℓ) (CohCarrier.GammaH M H)),
          (x : LaurentSeries (ZMod ℓ)) ∈ ModularCurve.modularFunctionFieldFullC (ZMod ℓ) M →
            ρ γ x = x) := by
  refine ⟨rho hℓM, ?_, ?_, rho_eq_one_of_mem_sup hℓM, full_le hℓM, rho_apply_eq_self_of_mem_full hℓM⟩
  · intro γ k f p hp
    obtain ⟨n, p₁, hp₁⟩ := exists_pow_slash (γ : SL(2, ℤ)) γ.2 hp
    exact ⟨n, dSlashM (γ : SL(2, ℤ)) γ.2 n f, p₁, coe_dSlashM _ _ _ _, hp₁,
      red_eq_zero_iff_of_slash ℓ hℓM (γ : SL(2, ℤ)) γ.2 hp hp₁⟩
  · intro γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ ef eg hg0 x hx
    rw [rho_apply, coe_sigma]

    have hg₁' : IsIntegralQExp (⇑(dSlashM (γ : SL(2, ℤ)) γ.2 0 g)) pg₁ := by
      rw [coe_dSlashM, pow_zero, one_smul, ← eg]; exact hg₁
    have hg₁0 : red ℓ pg₁ ≠ 0 := fun h0 =>
      hg0 ((red_eq_zero_iff_of_slash ℓ hℓM (γ : SL(2, ℤ)) γ.2 hg hg₁').mp h0)
    have qf : IsIntegralQExp (⇑(dSlashM (γ : SL(2, ℤ))⁻¹ (inv_mem γ.2) 0 f₁)) pf := by
      rw [coe_dSlashM, pow_zero, one_smul, ef, slash_slash_inv]; exact hf
    have qg : IsIntegralQExp (⇑(dSlashM (γ : SL(2, ℤ))⁻¹ (inv_mem γ.2) 0 g₁)) pg := by
      rw [coe_dSlashM, pow_zero, one_smul, eg, slash_slash_inv]; exact hg
    rw [pull_eq hℓM (γ : SL(2, ℤ))⁻¹ (inv_mem γ.2) x hf₁ hg₁ qf qg hg₁0 hx, nred_zero, nred_zero]
    rfl

end
end S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
end P2MW
export P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod (solution)

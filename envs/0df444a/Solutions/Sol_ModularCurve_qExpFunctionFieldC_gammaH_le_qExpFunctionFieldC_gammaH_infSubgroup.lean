-- Prove2me | solution 1 for ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d8c05ea5-9d2a-58e8-bbe0-8bd4f03d21fe

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
import Theorems.Thm_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime
import Theorems.Thm_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
import Theorems.Thm_ModularForm_exists_isIntegralQExp_qCoeff_congr_of_qCoeff_congr_intCast_gammaH
import Theorems.Thm_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open ModularFormClass ModularCurve
open scoped MatrixGroups ModularForm

noncomputable section

open UpperHalfPlane ModularCurve CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace RES
namespace Cuspify

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

omit [Γ.FiniteIndex] in

theorem coe_le_SL : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

def restrictSL {k : ℤ} (f : CuspForm 𝒮ℒ k) : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (coe_le_SL Γ hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)

@[scoped simp] theorem coe_restrictSL {k : ℤ} (f : CuspForm 𝒮ℒ k) : ⇑(restrictSL Γ f) = ⇑f := rfl

def deltaOn : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 := restrictSL Γ CuspForm.discriminant

@[scoped simp] theorem coe_deltaOn : ⇑(deltaOn Γ) = ModularForm.discriminant := rfl

def deltaInt : PowerSeries ℤ := PowerSeries.X * ModularCurve.dedekindEtaUnit

theorem isIntegralQExp_deltaOn : IsIntegralQExp (⇑(deltaOn Γ)) deltaInt := by
  rw [IsIntegralQExp, coe_deltaOn, deltaInt]
  exact (ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit).symm

theorem coeff_one_deltaInt : PowerSeries.coeff 1 deltaInt = 1 := by
  rw [deltaInt, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff]
  exact ModularCurve.constantCoeff_dedekindEtaUnit

theorem intSeriesC_deltaInt_ne_zero (K : Type*) [Field K] : intSeriesC K deltaInt ≠ 0 := by
  intro h
  have h1 : (intSeriesC K deltaInt).coeff 1 = 0 := by rw [h]; rfl
  rw [intSeriesC] at h1
  have : ((PowerSeries.map (Int.castRingHom K) deltaInt).coeff 1 : K) = 0 := by
    have := h1
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, HahnSeries.ofPowerSeries_apply_coeff] at this
    exact this
  rw [PowerSeries.coeff_map, coeff_one_deltaInt, map_one] at this
  exact one_ne_zero this

variable {Γ}

omit [Γ.FiniteIndex] in

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

omit [Γ.FiniteIndex] in

theorem isIntegralQExp_mul (hT : ModularGroup.T ∈ Γ) {F G : Type*} [FunLike F ℍ ℂ] [FunLike G ℍ ℂ]
    {a b : ℤ} (f : F) [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) a]
    (g : G) [ModularFormClass G (Γ : Subgroup (GL (Fin 2) ℝ)) b]
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp (⇑f) pf) (hg : IsIntegralQExp (⇑g) pg) :
    IsIntegralQExp (⇑f * ⇑g) (pf * pg) := by
  rw [IsIntegralQExp] at hf hg ⊢
  rw [map_mul, hf, hg]
  exact (ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT) f g).symm

variable (Γ)

def cuspify {k : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k + 12) :=
  CuspForm.mcast (by ring) ((deltaOn Γ).mulModularForm (f.mul g))

@[scoped simp] theorem coe_cuspify {k : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ⇑(cuspify Γ f g) = ModularForm.discriminant * (⇑f * ⇑g) := rfl

variable {Γ}

theorem isIntegralQExp_cuspify (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp (⇑f) pf) (hg : IsIntegralQExp (⇑g) pg) :
    IsIntegralQExp (⇑(cuspify Γ f g)) (pf * pg * deltaInt) := by
  have hfg : IsIntegralQExp (⇑(f.mul g)) (pf * pg) := by
    rw [ModularForm.coe_mul]; exact isIntegralQExp_mul hT f g hf hg
  have h := isIntegralQExp_mul hT (deltaOn Γ) (f.mul g) (isIntegralQExp_deltaOn Γ) hfg
  rw [coe_cuspify, show pf * pg * deltaInt = deltaInt * (pf * pg) by ring]
  rw [coe_deltaOn, ModularForm.coe_mul] at h
  exact h

theorem even_weight (k : ℤ) : Even (2 * k + 12) := ⟨k + 6, by ring⟩

end RES.Cuspify
p2m_reactivate "P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup.RES P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup.RES.Cuspify"
p2m_reactivate "P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup.RES"

namespace RES
namespace Fill

open ModularFormClass ModularCurve CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem Gamma1_le_GammaH {M : ℕ} (H : Subgroup (ZMod M)ˣ) : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨-, h11, h10⟩ := hA
  have hA0 : A ∈ Gamma0 M := Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]; exact one_mem H

scoped instance finiteIndex_GammaH {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH H)

theorem T_mem_GammaH {M : ℕ} (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  Gamma1_le_GammaH H (by rw [Gamma1_mem]; simp [ModularGroup.T])

def toMF {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (Y : CuspForm Γ k) : ModularForm Γ k where
  toSlashInvariantForm := Y.toSlashInvariantForm
  holo' := Y.holo'
  bdd_at_cusps' hc γ hγ := (Y.zero_at_cusps' hc γ hγ).boundedAtFilter

@[scoped simp] theorem coe_toMF {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (Y : CuspForm Γ k) : ⇑(toMF Y) = ⇑Y := rfl

abbrev Zbar : Type := ↥(integralClosure ℤ ℂ)

theorem coe_intCast_Zbar (m : ℤ) : ((m : Zbar) : ℂ) = (m : ℂ) := by simp

theorem hint_of_isIntegralQExp {f : UpperHalfPlane → ℂ} {P : PowerSeries ℤ} (h : IsIntegralQExp f P)
    (𝔪 : Ideal Zbar) (h𝔪 : 𝔪.IsPrime) (n : ℕ) :
    ∃ x y : Zbar, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff f n := by
  refine ⟨((PowerSeries.coeff n P : ℤ) : Zbar), 1, fun h1 => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h1), ?_⟩
  rw [OneMemClass.coe_one, one_mul, qCoeff, ← h.coeff n, coe_intCast_Zbar]

theorem intCast_mem_iff {p : ℕ} {𝔪 : Ideal Zbar}
    (hcomap : 𝔪.comap (algebraMap ℤ Zbar) = Ideal.span {(p : ℤ)}) (m : ℤ) :
    (m : Zbar) ∈ 𝔪 ↔ (p : ℤ) ∣ m := by
  rw [← Ideal.mem_span_singleton, ← hcomap, Ideal.mem_comap, eq_intCast]

theorem dvd_sub_of_congr {p : ℕ} {𝔪 : Ideal Zbar} (h𝔪 : 𝔪.IsPrime)
    (hcomap : 𝔪.comap (algebraMap ℤ Zbar) = Ideal.span {(p : ℤ)})
    {F G : UpperHalfPlane → ℂ} {PF P : PowerSeries ℤ} (hF : IsIntegralQExp F PF)
    (hGint : ∀ n : ℕ, ∃ x y : Zbar, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n)
    (hcong : ∀ (n : ℕ) (x y x' y' : Zbar), y ∉ 𝔪 → y' ∉ 𝔪 →
      (x : ℂ) = y * qCoeff F n → (x' : ℂ) = y' * qCoeff G n → x * y' - x' * y ∈ 𝔪)
    (hP : ∀ (n : ℕ) (x y : Zbar), y ∉ 𝔪 → (x : ℂ) = y * qCoeff G n →
      x - ((PowerSeries.coeff n P : ℤ) : Zbar) * y ∈ 𝔪) (n : ℕ) :
    (p : ℤ) ∣ PowerSeries.coeff n P - PowerSeries.coeff n PF := by
  obtain ⟨x, y, hy, hxy⟩ := hGint n
  have h1no : (1 : Zbar) ∉ 𝔪 := fun h1 => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hFn : ((((PowerSeries.coeff n PF : ℤ) : Zbar)) : ℂ) = (1 : Zbar) * qCoeff F n := by
    rw [OneMemClass.coe_one, one_mul, qCoeff, ← hF.coeff n, coe_intCast_Zbar]
  have h1 := hcong n _ 1 x y h1no hy hFn hxy
  have h2 := hP n x y hy hxy
  have h3 : (((PowerSeries.coeff n PF - PowerSeries.coeff n P : ℤ)) : Zbar) * y ∈ 𝔪 := by
    have := 𝔪.add_mem h1 h2
    convert this using 1
    push_cast
    ring
  rcases h𝔪.mem_or_mem h3 with h | h
  · rw [intCast_mem_iff hcomap] at h
    have : (p : ℤ) ∣ -(PowerSeries.coeff n PF - PowerSeries.coeff n P) := h.neg_right
    simpa using this
  · exact absurd h hy

theorem red_of_congr {𝔪 : Ideal Zbar} (h𝔪 : 𝔪.IsPrime)
    {F G : UpperHalfPlane → ℂ} {PF : PowerSeries ℤ} (hF : IsIntegralQExp F PF)
    (hcong : ∀ (n : ℕ) (x y x' y' : Zbar), y ∉ 𝔪 → y' ∉ 𝔪 →
      (x : ℂ) = y * qCoeff F n → (x' : ℂ) = y' * qCoeff G n → x * y' - x' * y ∈ 𝔪) (n : ℕ) :
    ∃ m : ℤ, ∀ x y : Zbar, y ∉ 𝔪 → (x : ℂ) = y * qCoeff G n → x - (m : Zbar) * y ∈ 𝔪 := by
  refine ⟨PowerSeries.coeff n PF, fun x y hy hxy => ?_⟩
  have h1no : (1 : Zbar) ∉ 𝔪 := fun h1 => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hFn : ((((PowerSeries.coeff n PF : ℤ) : Zbar)) : ℂ) = (1 : Zbar) * qCoeff F n := by
    rw [OneMemClass.coe_one, one_mul, qCoeff, ← hF.coeff n, coe_intCast_Zbar]
  have h1 := hcong n _ 1 x y h1no hy hFn hxy
  have : x - ((PowerSeries.coeff n PF : ℤ) : Zbar) * y = -((((PowerSeries.coeff n PF : ℤ) : Zbar)) * y - x * 1) := by ring
  rw [this]
  exact 𝔪.neg_mem h1

theorem intSeriesC_eq_of_dvd_sub (K : Type*) [Field K] (p : ℕ) [CharP K p] {P Q : PowerSeries ℤ}
    (h : ∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n P - PowerSeries.coeff n Q) :
    intSeriesC K P = intSeriesC K Q := by
  unfold intSeriesC
  congr 1
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast]
  exact (CharP.intCast_eq_intCast K p).mpr ((Int.modEq_iff_dvd.mpr (h n)).symm)

theorem nonneg_of_intSeriesC_ne_zero {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (K : Type*) [Field K] (g : ModularForm Γ k) {pg : PowerSeries ℤ} (hg : IsIntegralQExp (⇑g) pg)
    (hg0 : intSeriesC K pg ≠ 0) : 0 ≤ k := by
  by_contra hk
  push Not at hk
  have hz : g = 0 := ModularForm.isZero_of_neg_weight hk g
  have : pg = 0 := by
    refine hg.unique ?_
    rw [hz, ModularForm.coe_zero]
    exact isIntegralQExp_zero
  exact hg0 (by rw [this, intSeriesC_zero])

end RES.Fill
p2m_reactivate "P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup.RES P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup.RES.Cuspify P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup.RES.Fill"
p2m_reactivate "P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup.RES P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup.RES.Cuspify"

open RES.Fill in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [CharP K p] :
    ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≤
      ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨W₀⟩ := ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd hp hpM hpM2
  have hR₀ : W₀.R = M / p :=
    (Nat.div_eq_of_eq_mul_left hp.pos (W₀.hM.trans (mul_comm _ _))).symm
  have hMdiv : M = p * (M / p) := by rw [← hR₀]; exact W₀.hM
  let W : ModularForm.AtkinLehnerDatum M p :=
    ⟨M / p, hMdiv, W₀.a, W₀.b, by rw [← hR₀]; exact W₀.bezout⟩
  haveI hNZR : NeZero W.R := ⟨fun h => NeZero.ne M (by rw [hMdiv]; exact mul_eq_zero_of_right _ h)⟩
  have hpR : ¬ p ∣ W.R := ModularForm.AtkinLehnerDatum.not_dvd_R_of_prime W hp
  have hHpW : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H :=
    fun u hu => hHp u hu

  have hcop : Nat.Coprime p W.R := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpR
  set u₀ : (ZMod W.R)ˣ := ZMod.unitOfCoprime p hcop with hu₀
  obtain ⟨d, hdu⟩ := ZMod.unitsMap_surjective (Dvd.intro_left p W.hM.symm) u₀⁻¹
  have hd : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d : ZMod W.R) * (p : ZMod W.R) = 1 := by
    rw [hdu, ← ZMod.coe_unitOfCoprime p hcop, ← hu₀, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  haveI : Algebra.IsIntegral ℤ Zbar := ⟨fun x => integralClosure.isIntegral x⟩
  haveI hPp : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨𝔪, -, h𝔪, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)})
    (⊥ : Ideal Zbar) (by
      intro m hm
      rw [Ideal.mem_comap, Ideal.mem_bot] at hm
      have : (m : ℤ) = 0 := by
        have h := congrArg (fun z : Zbar => (z : ℂ)) hm
        simp only [eq_intCast] at h
        exact_mod_cast (by simpa using h : ((m : ℂ)) = 0)
      rw [this]; exact zero_mem _)
  have hp𝔪 : (p : Zbar) ∈ 𝔪 := by
    have : ((p : ℤ) : Zbar) ∈ 𝔪 := (intCast_mem_iff hcomap (p : ℤ)).mpr dvd_rfl
    exact_mod_cast this

  set a : ℕ := 4 * (p - 1) with ha_def
  have hp2 := hp.two_le
  have ha : 3 ≤ a := by omega
  have ha2 : Even a := ⟨2 * (p - 1), by omega⟩
  have hpa : p - 1 ∣ a := Dvd.intro_left 4 rfl

  change IntermediateField.adjoin K (intFormRatiosC K (CohCarrier.GammaH M H)) ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩

  have hk : 0 ≤ k := nonneg_of_intSeriesC_ne_zero K g hg hg0
  have hw : (2 : ℤ) ≤ 2 * k + 12 := by omega
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := T_mem_GammaH H

  set F := RES.Cuspify.cuspify (CohCarrier.GammaH M H) f g with hFdef
  set G := RES.Cuspify.cuspify (CohCarrier.GammaH M H) g g with hGdef
  have hFi : IsIntegralQExp (⇑F) (pf * pg * RES.Cuspify.deltaInt) := RES.Cuspify.isIntegralQExp_cuspify hT f g hf hg
  have hGi : IsIntegralQExp (⇑G) (pg * pg * RES.Cuspify.deltaInt) := RES.Cuspify.isIntegralQExp_cuspify hT g g hg hg
  have hev : Even (2 * k + 12) := RES.Cuspify.even_weight k

  have hFW := CuspForm.exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp p W H hHpW d 𝔪 h𝔪 hp𝔪 hev F _ hFi
  have hGW := CuspForm.exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp p W H hHpW d 𝔪 h𝔪 hp𝔪 hev G _ hGi

  obtain ⟨iF, hiF⟩ := CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
    p W H hHpW d hd a ha ha2 hpa 𝔪 h𝔪 hp𝔪 (2 * k + 12) hw F (hint_of_isIntegralQExp hFi 𝔪 h𝔪) hFW
  obtain ⟨iG, hiG⟩ := CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
    p W H hHpW d hd a ha ha2 hpa 𝔪 h𝔪 hp𝔪 (2 * k + 12) hw G (hint_of_isIntegralQExp hGi 𝔪 h𝔪) hGW
  obtain ⟨SF, hSFint, hSFcong⟩ := hiF (max iF iG) (le_max_left _ _)
  obtain ⟨SG, hSGint, hSGcong⟩ := hiG (max iF iG) (le_max_right _ _)

  obtain ⟨YF, PF, hYF, hPF⟩ := ModularForm.exists_isIntegralQExp_qCoeff_congr_of_qCoeff_congr_intCast_gammaH
    W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) _ p 𝔪 h𝔪 hp𝔪 (toMF SF) hSFint
    (red_of_congr h𝔪 hFi hSFcong)
  obtain ⟨YG, PG, hYG, hPG⟩ := ModularForm.exists_isIntegralQExp_qCoeff_congr_of_qCoeff_congr_intCast_gammaH
    W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) _ p 𝔪 h𝔪 hp𝔪 (toMF SG) hSGint
    (red_of_congr h𝔪 hGi hSGcong)

  have hEF : intSeriesC K PF = intSeriesC K (pf * pg * RES.Cuspify.deltaInt) :=
    intSeriesC_eq_of_dvd_sub K p (dvd_sub_of_congr h𝔪 hcomap hFi hSFint hSFcong hPF)
  have hEG : intSeriesC K PG = intSeriesC K (pg * pg * RES.Cuspify.deltaInt) :=
    intSeriesC_eq_of_dvd_sub K p (dvd_sub_of_congr h𝔪 hcomap hGi hSGint hSGcong hPG)
  have hΔ : intSeriesC K RES.Cuspify.deltaInt ≠ 0 := RES.Cuspify.intSeriesC_deltaInt_ne_zero K
  have hPG0 : intSeriesC K PG ≠ 0 := by
    rw [hEG, intSeriesC_mul, intSeriesC_mul]
    exact mul_ne_zero (mul_ne_zero hg0 hg0) hΔ
  have hx : intSeriesC K pf / intSeriesC K pg = intSeriesC K PF / intSeriesC K PG := by
    rw [hEF, hEG, intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, intSeriesC_mul,
      mul_div_mul_right _ _ hΔ, mul_div_mul_right _ _ hg0]
  rw [SetLike.mem_coe, hx]
  exact div_mem_qExpFunctionFieldC YF YG hYF hYG hPG0

end
end S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
end P2MW
export P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup (solution)

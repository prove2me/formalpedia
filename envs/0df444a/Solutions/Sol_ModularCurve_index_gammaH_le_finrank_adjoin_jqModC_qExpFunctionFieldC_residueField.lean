-- Prove2me | solution 1 for ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b979263b-73d4-54bb-86f2-8f76e21da05d

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup Function HahnSeries ModularCurve IntermediateField CohCarrier

open scoped MatrixGroups ModularForm Manifold

namespace XHIgusaDegree

local notation "Γᴳ(" M ", " H ")" =>
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ₁ᴳ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Prelim

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods_one : (1 : ℝ) ∈ (Γ₁ᴳ(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods_H : (1 : ℝ) ∈ (Γᴳ(M, H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

scoped instance finiteIndex_GammaH [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem Gamma1_le_H : Γ₁ᴳ(M) ≤ Γᴳ(M, H) := Subgroup.map_mono (Gamma1_le_GammaH M H)

variable {M H}

theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γ k) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

theorem qExpansion_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ModularForm Γ₁ᴳ(M) 4) :
    qExpansion 1 (⇑(∑ i ∈ s, F i)) = ∑ i ∈ s, qExpansion 1 (⇑(F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_one M) (F a) (∑ i ∈ s, F i), ih]

theorem finset_sum_slash {k : ℤ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ i ∈ s, F i) ∣[k] γ = ∑ i ∈ s, (F i ∣[k] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

variable (M H) in

def E4H : ModularForm Γᴳ(M, H) 4 := restrictForm (Subgroup.map_le_range _ _) E₄

theorem coe_E4H : (⇑(E4H M H) : ℍ → ℂ) = E₄ := rfl

theorem isIntegralQExp_E4H : IsIntegralQExp (⇑(E4H M H)) eisenstein4 := isIntegralQExp_E4

theorem E4H_slash (γ : SL(2, ℤ)) : (⇑(E4H M H) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(E4H M H) := by
  rw [coe_E4H, ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq E₄ _ ⟨γ, rfl⟩

theorem intSeriesC_eisenstein4_ne_zero (K : Type*) [Field K] : intSeriesC K eisenstein4 ≠ 0 := by
  intro h
  have h1 : eisenstein4.map (Int.castRingHom K) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  have := congrArg (PowerSeries.coeff 0) h1
  rw [PowerSeries.coeff_map, map_zero, eisenstein4, PowerSeries.coeff_mk, if_pos rfl, map_one] at this
  exact one_ne_zero this

end Prelim

section Witness

variable (M : ℕ) [NeZero M]

def G4 : ZMod M → ModularForm Γ₁ᴳ(M) ((4 : ℕ) : ℤ) :=
  (exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq M 4 (by norm_num)).choose

def a4 (c : ZMod M) : PowerSeries ℤ :=
  PowerSeries.mk fun n : ℕ =>
    (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (4 - 1)) +
      (-1) ^ 4 * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (4 - 1)

theorem G4_int (c : ZMod M) (hc : c ≠ 0) : IsIntegralQExp (⇑(G4 M c)) (a4 M c) :=
  (exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq M 4 (by norm_num)).choose_spec.1 c hc

theorem G4_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(G4 M c) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑(G4 M (c * ((γ 0 0 : ℤ) : ZMod M))) :=
  (exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq M 4 (by norm_num)).choose_spec.2 c γ hγ

def FS (S : Finset (ZMod M)) : ModularForm Γ₁ᴳ(M) ((4 : ℕ) : ℤ) :=
  (2 : ℝ)⁻¹ • ∑ c ∈ S, G4 M c

def bS (S : Finset (ZMod M)) : PowerSeries ℤ :=
  PowerSeries.mk fun n : ℕ => ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) ∈ S, (m : ℤ) ^ 3

theorem coe_FS (S : Finset (ZMod M)) :
    (⇑(FS M S) : ℍ → ℂ) = (2 : ℂ)⁻¹ • ∑ c ∈ S, (⇑(G4 M c) : ℍ → ℂ) := by
  rw [FS, ModularForm.coe_smul, coe_finset_sum]
  funext τ
  simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat, smul_eq_mul]

theorem FS_slash (S : Finset (ZMod M)) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(FS M S) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑(FS M (S.image (· * ((γ 0 0 : ℤ) : ZMod M)))) := by
  classical
  have hunit : IsUnit ((γ 0 0 : ℤ) : ZMod M) := by
    have h := Gamma0_d_mul_a M ⟨γ, hγ⟩
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h)
  have hinj : Function.Injective (fun c : ZMod M => c * ((γ 0 0 : ℤ) : ZMod M)) :=
    fun c c' h => hunit.mul_left_injective h
  rw [coe_FS, coe_FS, ModularForm.SL_smul_slash, finset_sum_slash,
    Finset.sum_image (fun c _ c' _ h => hinj h)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => G4_slash M c γ hγ

theorem sum_a4_eq (S : Finset (ZMod M)) (hsymm : ∀ c ∈ S, -c ∈ S) :
    ∑ c ∈ S, a4 M c = PowerSeries.C (2 : ℤ) * bS M S := by
  classical
  ext n
  rw [map_sum, PowerSeries.coeff_C_mul, bS, PowerSeries.coeff_mk]
  simp only [a4, PowerSeries.coeff_mk]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ c ∈ S, ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (4 - 1)
      = ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) ∈ S, (m : ℤ) ^ 3 :=
    Finset.sum_fiberwise_eq_sum_filter _ _ _ _
  have h2 : ∑ c ∈ S, (-1) ^ 4 * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (4 - 1)
      = ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) ∈ S, (m : ℤ) ^ 3 := by
    have e : ∀ c ∈ S, (-1 : ℤ) ^ 4 * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (4 - 1)
        = ∑ m ∈ n.divisors with -(((n / m : ℕ) : ZMod M)) = c, (m : ℤ) ^ 3 := by
      intro c _
      rw [show ((-1 : ℤ) ^ 4) = 1 by norm_num, one_mul]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext m
      simp only [Finset.mem_filter, neg_eq_iff_eq_neg]
    rw [Finset.sum_congr rfl e, Finset.sum_fiberwise_eq_sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro h; simpa using hsymm _ h
    · intro h; exact hsymm _ h
  rw [h1, h2, two_mul]

theorem FS_int (S : Finset (ZMod M)) (h0 : ∀ c ∈ S, c ≠ 0) (hsymm : ∀ c ∈ S, -c ∈ S) :
    IsIntegralQExp (⇑(FS M S)) (bS M S) := by
  classical
  have hsum : qExpansion 1 (⇑(∑ c ∈ S, G4 M c)) = (PowerSeries.C (2 : ℤ) * bS M S).map (Int.castRingHom ℂ) := by
    rw [qExpansion_finset_sum, ← sum_a4_eq M S hsymm, map_sum]
    exact Finset.sum_congr rfl fun c hc => (G4_int M c (h0 c hc)).symm
  have hcoe : (⇑(FS M S) : ℍ → ℂ) = (2 : ℂ)⁻¹ • (⇑(∑ c ∈ S, G4 M c) : ℍ → ℂ) := by
    rw [coe_FS, coe_finset_sum]
  rw [IsIntegralQExp, hcoe, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_one M) _
    (∑ c ∈ S, G4 M c), hsum, map_mul, PowerSeries.map_C, eq_intCast, PowerSeries.smul_eq_C_mul,
    ← mul_assoc, ← map_mul, Int.cast_ofNat, inv_mul_cancel₀ (two_ne_zero), map_one, one_mul]

theorem coeff_one_bS (S : Finset (ZMod M)) :
    PowerSeries.coeff 1 (bS M S) = if (1 : ZMod M) ∈ S then 1 else 0 := by
  classical
  rw [bS, PowerSeries.coeff_mk, Nat.divisors_one]
  rw [Finset.filter_singleton]
  simp only [Nat.div_self Nat.one_pos, Nat.cast_one]
  split_ifs <;> simp

end Witness

section Cosets

open Classical in

def cosetSet (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (a : (ZMod M)ˣ) : Finset (ZMod M) :=
  Finset.univ.filter fun c : ZMod M => ∃ u : (ZMod M)ˣ, (u : ZMod M) = c ∧ u * a⁻¹ ∈ H ⊔ Subgroup.zpowers (-1)

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev Hpm (H : Subgroup (ZMod M)ˣ) : Subgroup (ZMod M)ˣ := H ⊔ Subgroup.zpowers (-1)

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ Hpm H :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem le_Hpm : H ≤ Hpm H := le_sup_left

theorem mem_cosetSet {a : (ZMod M)ˣ} {c : ZMod M} :
    c ∈ cosetSet M H a ↔ ∃ u : (ZMod M)ˣ, (u : ZMod M) = c ∧ u * a⁻¹ ∈ Hpm H := by
  simp [cosetSet]

theorem coe_mem_cosetSet {a u : (ZMod M)ˣ} : (u : ZMod M) ∈ cosetSet M H a ↔ u * a⁻¹ ∈ Hpm H := by
  rw [mem_cosetSet]
  constructor
  · rintro ⟨u', hu', h⟩
    rw [Units.ext hu'] at h
    exact h
  · intro h; exact ⟨u, rfl, h⟩

theorem cosetSet_symm {a : (ZMod M)ˣ} {c : ZMod M} (hc : c ∈ cosetSet M H a) : -c ∈ cosetSet M H a := by
  rw [mem_cosetSet] at hc ⊢
  obtain ⟨u, rfl, hu⟩ := hc
  refine ⟨-u, by simp, ?_⟩
  have : -u * a⁻¹ = (u * a⁻¹) * (-1) := by simp [mul_comm]
  rw [this]
  exact mul_mem hu neg_one_mem_Hpm

theorem cosetSet_ne_zero (hM : Nontrivial (ZMod M)) {a : (ZMod M)ˣ} {c : ZMod M}
    (hc : c ∈ cosetSet M H a) : c ≠ 0 := by
  rw [mem_cosetSet] at hc
  obtain ⟨u, rfl, _⟩ := hc
  exact u.ne_zero

theorem one_mem_cosetSet_iff {a : (ZMod M)ˣ} : (1 : ZMod M) ∈ cosetSet M H a ↔ a ∈ Hpm H := by
  rw [← Units.val_one, coe_mem_cosetSet, one_mul]
  exact inv_mem_iff

theorem cosetSet_image_mul (a b : (ZMod M)ˣ) :
    (cosetSet M H a).image (· * (b : ZMod M)) = cosetSet M H (a * b) := by
  ext c
  simp only [Finset.mem_image, mem_cosetSet]
  constructor
  · rintro ⟨c', ⟨u, rfl, hu⟩, rfl⟩
    refine ⟨u * b, by simp, ?_⟩
    rwa [mul_inv_rev, ← mul_assoc, mul_assoc u, mul_inv_cancel, mul_one]
  · rintro ⟨u, rfl, hu⟩
    refine ⟨(u * b⁻¹ : (ZMod M)ˣ), ⟨u * b⁻¹, rfl, ?_⟩, by simp⟩
    rwa [mul_inv_rev, ← mul_assoc] at hu

theorem cosetSet_mul_of_mem (a : (ZMod M)ˣ) {h : (ZMod M)ˣ} (hh : h ∈ Hpm H) :
    cosetSet M H (a * h) = cosetSet M H a := by
  ext c
  simp only [mem_cosetSet]
  refine exists_congr fun u => and_congr_right fun _ => ?_
  have e : u * (a * h)⁻¹ = (u * a⁻¹) * h⁻¹ := by rw [mul_inv_rev, mul_comm h⁻¹, mul_assoc]
  rw [e]
  constructor
  · intro hmem
    have := mul_mem hmem hh
    rwa [inv_mul_cancel_right] at this
  · intro hmem
    exact mul_mem hmem (inv_mem hh)

def unitOf (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : (ZMod M)ˣ := (gamma0Units M ⟨γ, hγ⟩)⁻¹

theorem coe_unitOf (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : (unitOf γ hγ : ZMod M) = ((γ 0 0 : ℤ) : ZMod M) :=
  rfl

theorem unitOf_mem_of_mem_GammaH {γ : SL(2, ℤ)} (h : γ ∈ GammaH M H) :
    unitOf γ (GammaH_le_Gamma0 H h) ∈ Hpm H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp h
  exact inv_mem (le_Hpm hγH)

theorem mem_GammaH_of_unitOf_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (h : unitOf γ hγ ∈ Hpm H) :
    γ ∈ GammaH M (Hpm H) :=
  mem_GammaH_iff.mpr ⟨hγ, by simpa [unitOf] using inv_mem h⟩

def liftH (f : ModularForm Γ₁ᴳ(M) ((4 : ℕ) : ℤ))
    (hf : ∀ γ ∈ GammaH M H, (⇑f : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑f) : ModularForm Γᴳ(M, H) ((4 : ℕ) : ℤ) where
  toFun := f
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have := hf γ hγ
    rwa [ModularForm.SL_slash] at this
  holo' := f.holo'
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c Γ₁ᴳ(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc
    exact f.bdd_at_cusps' hc'

@[scoped simp] theorem coe_liftH (f : ModularForm Γ₁ᴳ(M) ((4 : ℕ) : ℤ))
    (hf : ∀ γ ∈ GammaH M H, (⇑f : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑f) : (⇑(liftH f hf) : ℍ → ℂ) = f := rfl

theorem FS_cosetSet_invariant (a : (ZMod M)ˣ) (γ : SL(2, ℤ)) (hγ : γ ∈ GammaH M H) :
    (⇑(FS M (cosetSet M H a)) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑(FS M (cosetSet M H a)) := by
  have hγ0 : γ ∈ Gamma0 M := GammaH_le_Gamma0 H hγ
  rw [FS_slash M _ γ hγ0, ← coe_unitOf γ hγ0, cosetSet_image_mul,
    cosetSet_mul_of_mem a (unitOf_mem_of_mem_GammaH hγ)]

variable (M H) in

def W (a : (ZMod M)ˣ) : ModularForm Γᴳ(M, H) ((4 : ℕ) : ℤ) :=
  liftH (FS M (cosetSet M H a)) (FS_cosetSet_invariant a)

theorem coe_W (a : (ZMod M)ˣ) : (⇑(W M H a) : ℍ → ℂ) = ⇑(FS M (cosetSet M H a)) := rfl

theorem W_slash (a : (ZMod M)ˣ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(W M H a) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = ⇑(W M H (a * unitOf γ hγ)) := by
  rw [coe_W, coe_W, FS_slash M _ γ hγ, ← coe_unitOf γ hγ, cosetSet_image_mul]

theorem W_int (hM : Nontrivial (ZMod M)) (a : (ZMod M)ˣ) :
    IsIntegralQExp (⇑(W M H a)) (bS M (cosetSet M H a)) := by
  rw [coe_W]
  exact FS_int M _ (fun c hc => cosetSet_ne_zero hM hc) (fun c hc => cosetSet_symm hc)

end Cosets

section Kernel

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

abbrev Fbar : IntermediateField (ZMod ℓ) (LaurentSeries (ZMod ℓ)) :=
  qExpFunctionFieldC (ZMod ℓ) (GammaH M H)

def PullBackFormula (ρ : Gamma0 M →* (Fbar ℓ M H ≃ₐ[ZMod ℓ] Fbar ℓ M H)) : Prop :=
  ∀ (γ : Gamma0 M) (k : ℤ) (f g f₁ g₁ : ModularForm Γᴳ(M, H) k) (pf pg pf₁ pg₁ : PowerSeries ℤ),
    IsIntegralQExp f pf → IsIntegralQExp g pg → IsIntegralQExp f₁ pf₁ → IsIntegralQExp g₁ pg₁ →
    (⇑f₁ : ℍ → ℂ) = ((⇑f : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    (⇑g₁ : ℍ → ℂ) = ((⇑g : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    intSeriesC (ZMod ℓ) pg ≠ 0 →
    ∀ x : Fbar ℓ M H, (x : LaurentSeries (ZMod ℓ)) = intSeriesC (ZMod ℓ) pf₁ / intSeriesC (ZMod ℓ) pg₁ →
      ((ρ γ x : Fbar ℓ M H) : LaurentSeries (ZMod ℓ)) = intSeriesC (ZMod ℓ) pf / intSeriesC (ZMod ℓ) pg

variable {ℓ M H}

theorem mem_GammaH_sup_of_eq_one (ρ : Gamma0 M →* (Fbar ℓ M H ≃ₐ[ZMod ℓ] Fbar ℓ M H))
    (h2 : PullBackFormula ℓ M H ρ) (γ : Gamma0 M) (hγ : ρ γ = 1) :
    (γ : SL(2, ℤ)) ∈ GammaH M (H ⊔ Subgroup.zpowers (-1)) := by
  classical

  by_cases htop : Hpm H = ⊤
  · exact mem_GammaH_of_unitOf_mem γ.2 (by rw [htop]; exact Subgroup.mem_top _)

  have hM : Nontrivial (ZMod M) := by
    by_contra hnt
    apply htop
    haveI : Subsingleton (ZMod M) := not_nontrivial_iff_subsingleton.mp hnt
    haveI : Subsingleton (ZMod M)ˣ := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    exact eq_top_iff.mpr fun x _ => by rw [Subsingleton.elim x 1]; exact one_mem _
  by_contra hnot
  have hd : unitOf (γ : SL(2, ℤ)) γ.2 ∉ Hpm H := fun h => hnot (mem_GammaH_of_unitOf_mem γ.2 h)

  set a : (ZMod M)ˣ := unitOf (γ : SL(2, ℤ)) γ.2 with ha
  have hf : IsIntegralQExp (⇑(W M H 1)) (bS M (cosetSet M H 1)) := W_int hM 1
  have hf₁ : IsIntegralQExp (⇑(W M H (1 * a))) (bS M (cosetSet M H (1 * a))) := W_int hM (1 * a)
  have ef : (⇑(W M H (1 * a)) : ℍ → ℂ) = (⇑(W M H 1) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] (γ : SL(2, ℤ)) :=
    (W_slash 1 (γ : SL(2, ℤ)) γ.2).symm
  have eg : (⇑(E4H M H) : ℍ → ℂ) = (⇑(E4H M H) : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] (γ : SL(2, ℤ)) :=
    (E4H_slash (γ : SL(2, ℤ))).symm
  have hg0 : intSeriesC (ZMod ℓ) eisenstein4 ≠ 0 := intSeriesC_eisenstein4_ne_zero _

  have hxmem : intSeriesC (ZMod ℓ) (bS M (cosetSet M H (1 * a))) / intSeriesC (ZMod ℓ) eisenstein4 ∈
      Fbar ℓ M H :=
    div_mem_qExpFunctionFieldC (W M H (1 * a)) (E4H M H) hf₁ isIntegralQExp_E4H hg0
  have key := h2 γ ((4 : ℕ) : ℤ) (W M H 1) (E4H M H) (W M H (1 * a)) (E4H M H)
    (bS M (cosetSet M H 1)) eisenstein4 (bS M (cosetSet M H (1 * a))) eisenstein4
    hf isIntegralQExp_E4H hf₁ isIntegralQExp_E4H ef eg hg0 ⟨_, hxmem⟩ rfl
  rw [hγ, AlgEquiv.one_apply] at key
  change intSeriesC (ZMod ℓ) (bS M (cosetSet M H (1 * a))) / intSeriesC (ZMod ℓ) eisenstein4 =
    intSeriesC (ZMod ℓ) (bS M (cosetSet M H 1)) / intSeriesC (ZMod ℓ) eisenstein4 at key
  rw [div_left_inj' hg0] at key

  have hcoeff := congrArg (fun z : LaurentSeries (ZMod ℓ) => z.coeff 1) key
  simp only [intSeriesC] at hcoeff
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map,
    coeff_one_bS, coeff_one_bS, one_mul, if_neg (mt one_mem_cosetSet_iff.mp hd),
    if_pos (one_mem_cosetSet_iff.mpr (one_mem _))] at hcoeff
  simp at hcoeff

end Kernel

section Degree

section Transport

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem adjoin_simple_eq_comap (E : IntermediateField K L) (x : E) :
    IntermediateField.adjoin K ({x} : Set E) =
      (IntermediateField.adjoin K ({(x : L)} : Set L)).comap (IntermediateField.val E) := by
  apply IntermediateField.lift_injective
  erw [IntermediateField.lift_adjoin_simple]
  change _ = ((IntermediateField.adjoin K ({(x : L)} : Set L)).comap E.val).map E.val
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left.mpr]
  exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr x.2)

theorem finrank_adjoin_simple_eq_relfinrank (E : IntermediateField K L) (x : E) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set E)) E =
      IntermediateField.relfinrank (IntermediateField.adjoin K ({(x : L)} : Set L)) E := by
  rw [adjoin_simple_eq_comap, IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

theorem finrank_eq_relfinrank_lift (E : IntermediateField K L) (A' : IntermediateField K E) :
    Module.finrank A' E = IntermediateField.relfinrank (IntermediateField.lift A') E := by
  have h : (IntermediateField.lift A').comap (IntermediateField.val E) = A' :=
    IntermediateField.comap_map _ _
  conv_lhs => rw [← h]
  rw [IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

end Transport

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem index_le_finrank_zmod (hℓM : ¬ ℓ ∣ M)
    (ρ : Gamma0 M →* (Fbar ℓ M H ≃ₐ[ZMod ℓ] Fbar ℓ M H))
    (h2 : PullBackFormula ℓ M H ρ)
    (h3 : ∀ γ : Gamma0 M, (γ : SL(2, ℤ)) ∈ GammaH M (H ⊔ Subgroup.zpowers (-1)) → ρ γ = 1)
    (h4 : modularFunctionFieldFullC (ZMod ℓ) M ≤ Fbar ℓ M H)
    (h5 : ∀ (γ : Gamma0 M) (x : Fbar ℓ M H),
      (x : LaurentSeries (ZMod ℓ)) ∈ modularFunctionFieldFullC (ZMod ℓ) M → ρ γ x = x)
    (x₀ : Fbar ℓ M H) (hx₀ : (x₀ : LaurentSeries (ZMod ℓ)) = jqModC (ZMod ℓ))
    [FiniteDimensional (IntermediateField.adjoin (ZMod ℓ) ({x₀} : Set (Fbar ℓ M H))) (Fbar ℓ M H)] :
    (GammaH M (H ⊔ Subgroup.zpowers (-1))).index ≤
      Module.finrank (IntermediateField.adjoin (ZMod ℓ) ({x₀} : Set (Fbar ℓ M H))) (Fbar ℓ M H) := by
  classical

  set Hp : Subgroup (ZMod M)ˣ := H ⊔ Subgroup.zpowers (-1) with hHp
  set K' : Subgroup (Gamma0 M) := (GammaH M Hp).subgroupOf (Gamma0 M) with hK'
  haveI : (GammaH M Hp).FiniteIndex := finiteIndex_GammaH M Hp
  haveI hK'fi : K'.FiniteIndex := inferInstance
  have hK'le : K' ≤ ρ.ker := fun γ hγ => by
    rw [MonoidHom.mem_ker]
    exact h3 γ (Subgroup.mem_subgroupOf.mp hγ)
  have hkerle : ρ.ker ≤ K' := fun γ hγ =>
    Subgroup.mem_subgroupOf.mpr (mem_GammaH_sup_of_eq_one ρ h2 γ ((MonoidHom.mem_ker).mp hγ))
  haveI : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hK'le
  set G : Subgroup (Fbar ℓ M H ≃ₐ[ZMod ℓ] Fbar ℓ M H) := ρ.range with hG
  have hcardG : Nat.card G = ρ.ker.index := (Subgroup.index_ker ρ).symm
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcardG]; exact Subgroup.FiniteIndex.index_ne_zero)
  haveI : Fintype G := Fintype.ofFinite G
  have hindex : K'.index ≤ Nat.card G := by
    rw [hcardG]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (Subgroup.index_dvd_of_le hkerle)
  have hK'index : K'.index * (Gamma0 M).index = (GammaH M Hp).index :=
    Subgroup.relIndex_mul_index (GammaH_le_Gamma0 Hp)

  have hArtin : Module.finrank (IntermediateField.fixedField G) (Fbar ℓ M H) = Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card G (Fbar ℓ M H)

  set J : IntermediateField (ZMod ℓ) (LaurentSeries (ZMod ℓ)) :=
    IntermediateField.adjoin (ZMod ℓ) ({jqModC (ZMod ℓ)} : Set (LaurentSeries (ZMod ℓ))) with hJ
  set Φ : IntermediateField (ZMod ℓ) (LaurentSeries (ZMod ℓ)) := modularFunctionFieldFullC (ZMod ℓ) M with hΦ
  set Fx : IntermediateField (ZMod ℓ) (LaurentSeries (ZMod ℓ)) :=
    IntermediateField.lift (IntermediateField.fixedField G) with hFx
  have hJΦ : J ≤ Φ := IntermediateField.adjoin_simple_le_iff.mpr (jqModC_mem_full (ZMod ℓ) M)
  have hΦFx : Φ ≤ Fx := by
    intro y hy
    have hyF : y ∈ Fbar ℓ M H := h4 hy
    have : (⟨y, hyF⟩ : Fbar ℓ M H) ∈ IntermediateField.fixedField G := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro e ⟨γ, rfl⟩
      exact h5 γ ⟨y, hyF⟩ hy
    exact (IntermediateField.mem_lift (⟨y, hyF⟩ : Fbar ℓ M H)).mpr this
  have hFxF : Fx ≤ Fbar ℓ M H := IntermediateField.lift_le _

  have hMne : ((M : ℕ) : ZMod ℓ) ≠ 0 := fun h => hℓM ((ZMod.natCast_eq_zero_iff M ℓ).mp h)
  have hψ : IntermediateField.relfinrank J Φ = dedekindPsi M := by
    have e1 := finrank_adjoin_simple_eq_relfinrank (K := ZMod ℓ) (modularFunctionFieldFullC (ZMod ℓ) M)
      ⟨jqModC (ZMod ℓ), jqModC_mem_full (ZMod ℓ) M⟩
    have e2 := finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (ZMod ℓ) M hMne
    exact e1.symm.trans e2
  have hFxdeg : IntermediateField.relfinrank Fx (Fbar ℓ M H) = Nat.card G := by
    have e := finrank_eq_relfinrank_lift (K := ZMod ℓ) (Fbar ℓ M H) (IntermediateField.fixedField G)
    exact e.symm.trans hArtin
  have htarget : Module.finrank (IntermediateField.adjoin (ZMod ℓ) ({x₀} : Set (Fbar ℓ M H))) (Fbar ℓ M H)
      = IntermediateField.relfinrank J (Fbar ℓ M H) := by
    have e := finrank_adjoin_simple_eq_relfinrank (K := ZMod ℓ) (Fbar ℓ M H) x₀
    rw [hx₀] at e
    exact e
  have htower : IntermediateField.relfinrank J (Fbar ℓ M H)
      = dedekindPsi M * (IntermediateField.relfinrank Φ Fx * Nat.card G) := by
    rw [← IntermediateField.relfinrank_mul_relfinrank hJΦ (hΦFx.trans hFxF),
      ← IntermediateField.relfinrank_mul_relfinrank hΦFx hFxF, hψ, hFxdeg]

  have hpos : 0 < Module.finrank (IntermediateField.adjoin (ZMod ℓ) ({x₀} : Set (Fbar ℓ M H))) (Fbar ℓ M H) :=
    Module.finrank_pos
  rw [htarget, htower] at hpos
  have hmid : 1 ≤ IntermediateField.relfinrank Φ Fx := by
    rcases Nat.eq_zero_or_pos (IntermediateField.relfinrank Φ Fx) with h0 | h0
    · rw [h0, zero_mul, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h0

  rw [htarget, htower, ← hK'index, Gamma0_index, mul_comm (K'.index)]
  calc dedekindPsi M * K'.index ≤ dedekindPsi M * (1 * Nat.card G) := by
        rw [one_mul]; exact Nat.mul_le_mul_left _ hindex
    _ ≤ dedekindPsi M * (IntermediateField.relfinrank Φ Fx * Nat.card G) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmid)

end Degree

section Final

theorem charP_residueField (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) : CharP (IsLocalRing.ResidueField A) ℓ := by
  have hmem : ((ℓ : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by
    have h : ((ℓ : A) : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) := by push_cast; rfl
    rw [h]
    exact hA
  have hmax : (ℓ : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.mp hmem
  have h0 : (ℓ : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hmax
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

end Final

end XHIgusaDegree
p2m_reactivate "P2MW.S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField.XHIgusaDegree"

open XHIgusaDegree in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField A)) =
      ModularCurve.jqModC (IsLocalRing.ResidueField A)) :
    (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))).index ≤
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A)
            (CohCarrier.GammaH M H))))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := by
  haveI := charP_residueField ℓ A hA

  obtain ⟨x', hx', -, hfin, -⟩ :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A
      (CohCarrier.GammaH M H) (translation_mem_GammaH M H)
  have hxx' : x' = x := Subtype.ext (hx'.trans hx.symm)
  subst hxx'
  haveI := hfin

  set φ : ZMod ℓ →+* IsLocalRing.ResidueField A := ZMod.castHom (dvd_refl ℓ) (IsLocalRing.ResidueField A)
  set x₀ : Fbar ℓ M H :=
    ⟨jqModC (ZMod ℓ), intFormRatiosC_subset (ZMod ℓ) _ (jqModC_mem_intFormRatiosC (ZMod ℓ) _)⟩ with hx₀
  have hx₀' : (x₀ : LaurentSeries (ZMod ℓ)) = jqModC (ZMod ℓ) := rfl
  have htr : Transcendental (ZMod ℓ) (x₀ : LaurentSeries (ZMod ℓ)) := transcendental_jqModC (ZMod ℓ)
  have hxφ : (x' : LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap φ (x₀ : LaurentSeries (ZMod ℓ)) := by
    rw [hx', hx₀', coeffMap_jqModC]
  obtain ⟨hfin₀, hle⟩ := finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap φ (CohCarrier.GammaH M H)
    x₀ x' htr hxφ
  haveI := hfin₀

  obtain ⟨ρ, -, h2, h3, h4, h5⟩ := exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod ℓ M hℓM H
  exact (index_le_finrank_zmod hℓM ρ h2 h3 h4 h5 x₀ hx₀').trans hle

end
p2m_reactivate "P2MW.S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField.XHIgusaDegree"

end S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
end P2MW
export P2MW.S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField (solution)

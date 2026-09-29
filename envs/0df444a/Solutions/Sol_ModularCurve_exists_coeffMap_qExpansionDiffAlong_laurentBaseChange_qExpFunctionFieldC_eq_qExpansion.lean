-- Prove2me | solution 1 for ModularCurve.exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ee863495-3351-5ef0-9bf7-87f89f7e3a64

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XH
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField
import Theorems.Thm_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane HahnSeries
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm qExpFunctionFieldC intFormRatiosC_subset jq coeff_jq_neg_one coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff qExpansionDiffAlong qEuler qEuler_coeff diffQExp diffQExp_smul_D jqModC jqModC_rat map_jqModC translation_mem_GammaH Gamma1_le_GammaH jqModC_eq_qExpansion_E4_cube_div_discriminant qExpansion_div_mem_laurentBaseChange_xHFunctionField qExpansionDiffAlong_val_eq_diffQExp jqModC_mem_intFormRatiosC"
namespace LiftDGamma
p2m_open "ModularCurve"

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

def thetaPS (p : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n : ℕ => (n : R) * PowerSeries.coeff n p

theorem thetaPS_eq (p : PowerSeries R) :
    thetaPS p = PowerSeries.mk fun n : ℕ => (n : R) * PowerSeries.coeff n p := rfl

theorem qEuler_ofPowerSeries (p : PowerSeries R) :
    qEuler R (ofPowerSeries ℤ R p) = ofPowerSeries ℤ R (thetaPS p) := by
  ext m
  rw [qEuler_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hm
  · rw [mul_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hm)
    simp [thetaPS, PowerSeries.coeff_mk]

theorem coeffMap_qEuler (f : R →+* S) (x : LaurentSeries R) :
    coeffMap f (qEuler R x) = qEuler S (coeffMap f x) := by
  ext m
  simp

theorem coeffMap_ofPowerSeries_eq (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R p) = ofPowerSeries ℤ S (p.map f) := by
  ext m
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

theorem coeffMap_C (f : R →+* S) (c : R) : coeffMap f (C c) = C (f c) :=
  HahnSeries.map_C c f

end Laurent

section Level

variable {Γ : Subgroup SL(2, ℤ)}

abbrev qL (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem qL_mul (hT : ModularGroup.T ∈ Γ) {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT), PowerSeries.coe_mul]

theorem qL_mcast {a b : ℤ} (h : a = b) (f : ModularForm Γ a) :
    qL (ModularForm.mcast h f) = qL f := by
  simp only [qL, ModularForm.coe_mcast]

theorem qL_ne_zero (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT)]
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  simpa [qL] using h

theorem ne_zero_of_qL_ne_zero {k : ℤ} (f : ModularForm Γ k) (h : qL f ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply h
  simp only [qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]

theorem coe_le_SL (Γ : Subgroup SL(2, ℤ)) : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨g, rfl⟩

end Level

section LevelOne

def E4cube : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) ((ModularForm.E₄.mul ModularForm.E₄).mul ModularForm.E₄)

theorem coe_E4cube : (E4cube : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) * ModularForm.E₄ * ModularForm.E₄ := by
  simp only [E4cube, ModularForm.coe_mcast, ModularForm.coe_mul]

theorem qL_E4cube : qL E4cube = qL ModularForm.E₄ ^ 3 := by
  rw [coe_E4cube, qL, ← ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos
    one_mem_strictPeriods_SL, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos
    one_mem_strictPeriods_SL, PowerSeries.coe_mul, PowerSeries.coe_mul]
  ring

def DeltaMF : ModularForm 𝒮ℒ 12 := ModularFormClass.modularForm CuspForm.discriminant

theorem coe_DeltaMF : (DeltaMF : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem DeltaMF_apply_ne_zero (z : ℍ) : DeltaMF z ≠ 0 := by
  rw [coe_DeltaMF]
  exact ModularForm.discriminant_ne_zero z

end LevelOne

section Descent

variable {K : Type*} [Field K] [Algebra ℚ K] (σ : K →+* ℂ) (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem exists_retraction :
    ∃ l : ℂ →+ K, (∀ a c, l (σ a * c) = a * l c) ∧ l 1 = 1 := by
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)
  refine ⟨g.toAddMonoidHom, fun a c => ?_, ?_⟩
  · have := g.map_smul a c
    rw [Algebra.smul_def] at this
    first | exact this | (simp only [smul_eq_mul, LinearMap.toAddMonoidHom_coe] at this ⊢; exact this) | simpa using this
  · have := LinearMap.congr_fun hg 1
    simpa using this

theorem linearIndependent_coeffMap {ι : Type*} [Fintype ι] {u : ι → LaurentSeries K}
    (hu : LinearIndependent K u) : LinearIndependent ℂ (fun i => coeffMap σ (u i)) := by
  classical
  obtain ⟨l, hl, hl1⟩ := exists_retraction σ
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i₀, hi₀⟩ := hne
  set g' : ι → ℂ := fun i => (g i₀)⁻¹ * g i with hg'def
  have hg'₀ : g' i₀ = 1 := by simp [hg'def, hi₀]
  have hg' : ∑ i, g' i • coeffMap σ (u i) = 0 := by
    have : ∑ i, g' i • coeffMap σ (u i) = (g i₀)⁻¹ • ∑ i, g i • coeffMap σ (u i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
    rw [this, hg, smul_zero]
  have key : ∑ i, l (g' i) • u i = 0 := by
    ext n
    have hn := congrArg (fun z : LaurentSeries ℂ => l (z.coeff n)) hg'
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul,
      HahnSeries.coeff_zero, map_zero, map_sum] at hn ⊢
    rw [← hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (g' i), hl, mul_comm]
  have := hu (fun i => l (g' i)) key i₀
  rw [hg'₀, hl1] at this
  exact one_ne_zero this

theorem coeffMap_coeffEmb' (u : LaurentSeries ℚ) : coeffMap σ (coeffEmb K u) = coeffEmb ℂ u := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) u

def bcSubmodule : Submodule K (LaurentSeries K) where
  carrier := laurentBaseChange K F₀
  add_mem' ha hb := add_mem ha hb
  zero_mem' := zero_mem _
  smul_mem' r x hx := by
    show r • x ∈ laurentBaseChange K F₀
    rw [← single_zero_mul_eq_smul, ← algebraMap_laurentSeries_eq_single]
    exact mul_mem ((laurentBaseChange K F₀).algebraMap_mem r) hx

theorem mem_bcSubmodule {x : LaurentSeries K} : x ∈ bcSubmodule F₀ ↔ x ∈ laurentBaseChange K F₀ :=
  Iff.rfl

def IsComb (a : LaurentSeries ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (γ : ι → ℂ) (w : ι → LaurentSeries K),
    (∀ i, w i ∈ laurentBaseChange K F₀) ∧ a = ∑ i, C (γ i) * coeffMap σ (w i)

variable {σ F₀}

theorem isComb_coeffMap {x : LaurentSeries K} (hx : x ∈ laurentBaseChange K F₀) :
    IsComb σ F₀ (coeffMap σ x) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => x, fun _ => hx, by
    rw [Fintype.sum_unique, map_one, one_mul]⟩

theorem isComb_C (c : ℂ) : IsComb σ F₀ (C c : LaurentSeries ℂ) :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => 1, fun _ => one_mem _, by
    rw [Fintype.sum_unique, map_one, mul_one]⟩

theorem IsComb.add {a b : LaurentSeries ℂ} (ha : IsComb σ F₀ a) (hb : IsComb σ F₀ b) :
    IsComb σ F₀ (a + b) := by
  obtain ⟨ι, _, γ, w, hw, rfl⟩ := ha
  obtain ⟨ι', _, γ', w', hw', rfl⟩ := hb
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim γ γ', Sum.elim w w', ?_, ?_⟩
  · rintro (i | i)
    · exact hw i
    · exact hw' i
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]

theorem IsComb.neg {a : LaurentSeries ℂ} (ha : IsComb σ F₀ a) : IsComb σ F₀ (-a) := by
  obtain ⟨ι, _, γ, w, hw, rfl⟩ := ha
  refine ⟨ι, inferInstance, fun i => -γ i, w, hw, ?_⟩
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_neg, neg_mul]

theorem IsComb.mul {a b : LaurentSeries ℂ} (ha : IsComb σ F₀ a) (hb : IsComb σ F₀ b) :
    IsComb σ F₀ (a * b) := by
  obtain ⟨ι, _, γ, w, hw, rfl⟩ := ha
  obtain ⟨ι', _, γ', w', hw', rfl⟩ := hb
  refine ⟨ι × ι', inferInstance, fun p => γ p.1 * γ' p.2, fun p => w p.1 * w' p.2,
    fun p => mul_mem (hw p.1) (hw' p.2), ?_⟩
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul]
  ring

def IsRat (σ : K →+* ℂ) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (y : LaurentSeries ℂ) : Prop :=
  ∃ a b : LaurentSeries ℂ, IsComb σ F₀ a ∧ IsComb σ F₀ b ∧ b ≠ 0 ∧ y = a / b

theorem isRat_of_isComb {y : LaurentSeries ℂ} (hy : IsComb σ F₀ y) : IsRat σ F₀ y :=
  ⟨y, 1, hy, by simpa using isComb_C (σ := σ) (F₀ := F₀) 1, one_ne_zero, (div_one y).symm⟩

theorem IsRat.mul {x y : LaurentSeries ℂ} (hx : IsRat σ F₀ x) (hy : IsRat σ F₀ y) :
    IsRat σ F₀ (x * y) := by
  obtain ⟨a, b, ha, hb, hb0, rfl⟩ := hx
  obtain ⟨a', b', ha', hb', hb0', rfl⟩ := hy
  exact ⟨a * a', b * b', ha.mul ha', hb.mul hb', mul_ne_zero hb0 hb0', by rw [div_mul_div_comm]⟩

theorem IsRat.add {x y : LaurentSeries ℂ} (hx : IsRat σ F₀ x) (hy : IsRat σ F₀ y) :
    IsRat σ F₀ (x + y) := by
  obtain ⟨a, b, ha, hb, hb0, rfl⟩ := hx
  obtain ⟨a', b', ha', hb', hb0', rfl⟩ := hy
  exact ⟨a * b' + b * a', b * b', (ha.mul hb').add (hb.mul ha'), hb.mul hb', mul_ne_zero hb0 hb0',
    by rw [div_add_div _ _ hb0 hb0']⟩

theorem IsRat.neg {x : LaurentSeries ℂ} (hx : IsRat σ F₀ x) : IsRat σ F₀ (-x) := by
  obtain ⟨a, b, ha, hb, hb0, rfl⟩ := hx
  exact ⟨-a, b, ha.neg, hb, hb0, (neg_div b a).symm⟩

theorem IsRat.inv {x : LaurentSeries ℂ} (hx : IsRat σ F₀ x) : IsRat σ F₀ x⁻¹ := by
  obtain ⟨a, b, ha, hb, hb0, rfl⟩ := hx
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_div, inv_zero, ← map_zero (C : ℂ →+* LaurentSeries ℂ)]
    exact isRat_of_isComb (isComb_C 0)
  · exact ⟨b, a, hb, ha, ha0, by rw [inv_div]⟩

variable (σ F₀) in

theorem isRat_of_mem {y : LaurentSeries ℂ} (hy : y ∈ laurentBaseChange ℂ F₀) : IsRat σ F₀ y := by
  rw [mem_laurentBaseChange_iff] at hy
  induction hy using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, ← C_apply]
        exact isRat_of_isComb (isComb_C c)
      · rw [← coeffMap_coeffEmb' σ]
        exact isRat_of_isComb (isComb_coeffMap (coeffEmb_mem_laurentBaseChange K hu))
  | one =>
      rw [← map_one (C : ℂ →+* LaurentSeries ℂ)]
      exact isRat_of_isComb (isComb_C 1)
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

theorem sum_C_mul_sum {ι : Type*} [Fintype ι] {n : ℕ} (γ : ι → ℂ) (ρ : ι → Fin n → ℂ)
    (e : Fin n → LaurentSeries ℂ) :
    ∑ i, C (γ i) * ∑ k, C (ρ i k) * e k = ∑ k, C (∑ i, γ i * ρ i k) * e k := by
  calc ∑ i, C (γ i) * ∑ k, C (ρ i k) * e k
      = ∑ i, ∑ k, C (γ i) * (C (ρ i k) * e k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, ∑ i, C (γ i) * (C (ρ i k) * e k) := Finset.sum_comm
    _ = ∑ k, C (∑ i, γ i * ρ i k) * e k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, mul_assoc]

variable (σ F₀) in

theorem mem_laurentBaseChange_of_coeffMap_mem {x : LaurentSeries K}
    (hx : coeffMap σ x ∈ laurentBaseChange ℂ F₀) : x ∈ laurentBaseChange K F₀ := by
  classical
  obtain ⟨a, b, ⟨ι, _, γ, w, hw, rfl⟩, ⟨ι', _, γ', w', hw', rfl⟩, hb0, hab⟩ := isRat_of_mem σ F₀ hx

  let W : ι ⊕ ι' → LaurentSeries K := Sum.elim w w'
  have hW : ∀ s, W s ∈ laurentBaseChange K F₀ := by
    rintro (i | i)
    · exact hw i
    · exact hw' i
  let V : Submodule K (LaurentSeries K) := Submodule.span K (Set.range W)
  haveI : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range W)
  have hVle : V ≤ bcSubmodule F₀ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, rfl⟩
    exact hW s
  let bV := Module.finBasis K V
  let v : Fin (Module.finrank K V) → LaurentSeries K := fun k => (bV k : LaurentSeries K)
  have hvmem : ∀ k, v k ∈ laurentBaseChange K F₀ := fun k => hVle (bV k).2
  have hli : LinearIndependent K v := bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hrep : ∀ s, ∃ ρ : Fin (Module.finrank K V) → K, ∑ k, ρ k • v k = W s := by
    intro s
    have hs : W s ∈ V := Submodule.subset_span ⟨s, rfl⟩
    refine ⟨fun k => bV.repr ⟨W s, hs⟩ k, ?_⟩
    have h := congrArg (fun z : V => (z : LaurentSeries K)) (bV.sum_repr ⟨W s, hs⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  choose ρ hρ using hrep
  have hσW : ∀ s, coeffMap σ (W s) = ∑ k, C (σ (ρ s k)) * coeffMap σ (v k) := by
    intro s
    rw [← hρ s, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← single_zero_mul_eq_smul, map_mul, coeffMap_single, C_apply]

  set α : Fin (Module.finrank K V) → ℂ := fun k => ∑ i, γ i * σ (ρ (Sum.inl i) k) with hα
  set β : Fin (Module.finrank K V) → ℂ := fun k => ∑ j, γ' j * σ (ρ (Sum.inr j) k) with hβ
  have ha : ∑ i, C (γ i) * coeffMap σ (w i) = ∑ k, C (α k) * coeffMap σ (v k) := by
    have : ∀ i, coeffMap σ (w i) = ∑ k, C (σ (ρ (Sum.inl i) k)) * coeffMap σ (v k) :=
      fun i => hσW (Sum.inl i)
    simp only [this]
    exact sum_C_mul_sum γ (fun i k => σ (ρ (Sum.inl i) k)) _
  have hb : ∑ j, C (γ' j) * coeffMap σ (w' j) = ∑ k, C (β k) * coeffMap σ (v k) := by
    have : ∀ j, coeffMap σ (w' j) = ∑ k, C (σ (ρ (Sum.inr j) k)) * coeffMap σ (v k) :=
      fun j => hσW (Sum.inr j)
    simp only [this]
    exact sum_C_mul_sum γ' (fun j k => σ (ρ (Sum.inr j) k)) _
  rw [ha, hb] at hab
  rw [hb] at hb0

  have hrel : coeffMap σ x * ∑ k, C (β k) * coeffMap σ (v k) = ∑ k, C (α k) * coeffMap σ (v k) := by
    rw [hab, div_mul_cancel₀ _ hb0]

  have hdepC : ¬ LinearIndependent ℂ
      (fun s => coeffMap σ (Sum.elim (fun k => x * v k) v s) : Fin (Module.finrank K V) ⊕
        Fin (Module.finrank K V) → LaurentSeries ℂ) := by
    rw [Fintype.not_linearIndependent_iff]
    refine ⟨Sum.elim β (fun k => -α k), ?_, ?_⟩
    · have h1 : ∀ k, β k • coeffMap σ (x * v k) = coeffMap σ x * (C (β k) * coeffMap σ (v k)) := by
        intro k
        rw [← single_zero_mul_eq_smul, ← C_apply, map_mul]
        ring
      have h2 : ∀ k, (-α k) • coeffMap σ (v k) = -(C (α k) * coeffMap σ (v k)) := by
        intro k
        rw [← single_zero_mul_eq_smul, ← C_apply, map_neg, neg_mul]
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, h1, h2]
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hrel, add_neg_cancel]
    · obtain ⟨k, hk⟩ : ∃ k, β k ≠ 0 := by
        by_contra h
        push_neg at h
        apply hb0
        exact Finset.sum_eq_zero fun k _ => by rw [h k, map_zero, zero_mul]
      exact ⟨Sum.inl k, hk⟩
  have hdepK : ¬ LinearIndependent K (Sum.elim (fun k => x * v k) v) := fun h =>
    hdepC (linearIndependent_coeffMap σ h)
  obtain ⟨g, hg, s₀, hs₀⟩ := Fintype.not_linearIndependent_iff.mp hdepK
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg

  set c : LaurentSeries K := ∑ k, g (Sum.inl k) • v k with hc
  set d : LaurentSeries K := ∑ k, g (Sum.inr k) • v k with hd
  have hxc : x * c + d = 0 := by
    rw [← hg, hc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← single_zero_mul_eq_smul, ← single_zero_mul_eq_smul, mul_left_comm]
  have hc0 : c ≠ 0 := by
    intro hc0
    have hinl : ∀ k, g (Sum.inl k) = 0 :=
      Fintype.linearIndependent_iff.mp hli _ (by rw [← hc, hc0])
    have hd0 : d = 0 := by rw [← hxc, hc0, mul_zero, zero_add]
    have hinr : ∀ k, g (Sum.inr k) = 0 :=
      Fintype.linearIndependent_iff.mp hli _ (by rw [← hd, hd0])
    rcases s₀ with k | k
    · exact hs₀ (hinl k)
    · exact hs₀ (hinr k)
  have hxeq : x = -d / c := by
    rw [eq_div_iff hc0, eq_neg_iff_add_eq_zero, hxc]
  have hcmem : c ∈ bcSubmodule F₀ :=
    (bcSubmodule F₀).sum_mem fun k _ => (bcSubmodule F₀).smul_mem _ (hvmem k)
  have hdmem : d ∈ bcSubmodule F₀ :=
    (bcSubmodule F₀).sum_mem fun k _ => (bcSubmodule F₀).smul_mem _ (hvmem k)
  rw [mem_bcSubmodule] at hcmem hdmem
  rw [hxeq]
  exact div_mem (neg_mem hdmem) hcmem

end Descent

section Main

variable (Γ : Subgroup SL(2, ℤ)) (ι₀ : AlgebraicClosure ℚ →+* ℂ)

local notation "ℚb" => AlgebraicClosure ℚ

abbrev Fbar : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)

def jBar : LaurentSeries ℚb := coeffEmb ℚb jq

theorem jBar_mem : jBar ∈ Fbar Γ := by
  refine coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ?_
  have h := intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ)
  rwa [jqModC_rat] at h

theorem coeffMap_jBar : coeffMap ι₀ jBar = jqModC ℂ := by
  rw [jBar, coeffEmb, coeffMap_coeffMap, ← jqModC_rat]
  exact map_jqModC _

theorem qEuler_jBar_ne_zero : qEuler ℚb jBar ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries ℚb => x.coeff (-1)) h
  simp only [qEuler_coeff, jBar, coeffEmb_coeff, coeff_jq_neg_one, map_one, mul_one,
    HahnSeries.coeff_zero, Int.cast_neg, Int.cast_one, neg_eq_zero, one_ne_zero] at h1

variable (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2)
  (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f : ℍ → ℂ) n ∈ ι₀.range)

def fBarPS : PowerSeries ℚb := PowerSeries.mk fun n : ℕ => Classical.choose (hf n)

theorem map_fBarPS : (fBarPS Γ ι₀ f hf).map ι₀ = qExpansion 1 f := by
  ext n
  rw [PowerSeries.coeff_map, fBarPS, PowerSeries.coeff_mk]
  exact Classical.choose_spec (hf n)

def fBar : LaurentSeries ℚb := ofPowerSeries ℤ ℚb (fBarPS Γ ι₀ f hf)

theorem coeffMap_fBar : coeffMap ι₀ (fBar Γ ι₀ f hf) = qL f := by
  rw [fBar, coeffMap_ofPowerSeries_eq, map_fBarPS]

def xBar : LaurentSeries ℚb := fBar Γ ι₀ f hf / qEuler ℚb jBar

theorem xBar_mul_qEuler_jBar : xBar Γ ι₀ f hf * qEuler ℚb jBar = fBar Γ ι₀ f hf :=
  div_mul_cancel₀ _ qEuler_jBar_ne_zero

theorem exists_coeffMap_xBar_eq_div [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    ∃ (G B : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 + 12 + 2)), B ≠ 0 ∧
      coeffMap ι₀ (C (12 : ℚb)⁻¹ * xBar Γ ι₀ f hf) = qL G / qL B := by

  let G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 := restrictForm (coe_le_SL Γ) E4cube
  let Dl : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 := restrictForm (coe_le_SL Γ) DeltaMF
  have hG : (G : ℍ → ℂ) = E4cube := rfl
  have hDl : (Dl : ℍ → ℂ) = DeltaMF := rfl

  obtain ⟨B, -, hB⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq
    (Γ := Γ) (one_mem_strictPeriods hT) Dl G
  set a : LaurentSeries ℂ := qL G with ha
  set b : LaurentSeries ℂ := qL Dl with hb
  set Da : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (thetaPS (qExpansion 1 G)) with hDa
  set Db : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (thetaPS (qExpansion 1 Dl)) with hDb
  set W : LaurentSeries ℂ := b * Da - Db * a with hW
  have hDl0 : Dl ≠ 0 := by
    intro h0
    have := congrArg (fun F : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 => (F : ℍ → ℂ) I) h0
    simp only [hDl, ModularForm.coe_zero, Pi.zero_apply] at this
    exact DeltaMF_apply_ne_zero I this
  have hb0 : b ≠ 0 := qL_ne_zero hT Dl hDl0
  have hBq : qL B = C (12 : ℂ) * W := by
    rw [qL, hB]
    simp only [map_sub, map_mul, ofPowerSeries_C, ← thetaPS_eq]
    push_cast
    ring
  have hj : coeffMap ι₀ jBar = a / b := by
    rw [coeffMap_jBar, ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, ha, hb, hG, hDl,
      qL_E4cube, coe_DeltaMF]
  have hTh : coeffMap ι₀ (qEuler ℚb jBar) = b⁻¹ ^ 2 * W := by
    rw [coeffMap_qEuler, hj, Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      ha, hb, qL, qL, qEuler_ofPowerSeries, qEuler_ofPowerSeries, ← hDa, ← hDb, hW]
    ring
  have hT0 : coeffMap ι₀ (qEuler ℚb jBar) ≠ 0 :=
    (map_ne_zero (coeffMap ι₀)).mpr qEuler_jBar_ne_zero
  have hW0 : W ≠ 0 := by
    intro hW0
    apply hT0
    rw [hTh, hW0, mul_zero]
  have hB0 : B ≠ 0 := by
    refine ne_zero_of_qL_ne_zero B ?_
    rw [hBq]
    exact mul_ne_zero (C_ne_zero (by norm_num)) hW0
  let Fm : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2 := ModularFormClass.modularForm f
  let Gnum : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 + 12 + 2) :=
    ModularForm.mcast (by norm_num) ((Fm.mul Dl).mul Dl)
  have hGnum : qL Gnum = qL f * b * b := by
    simp only [Gnum, qL_mcast, qL_mul hT, hb]
    rfl
  refine ⟨Gnum, B, hB0, ?_⟩
  have hc : (C (12 : ℂ) : LaurentSeries ℂ) ≠ 0 := C_ne_zero (by norm_num)
  rw [map_mul, coeffMap_C, map_inv₀, map_ofNat, map_inv₀, xBar, map_div₀, coeffMap_fBar, hTh, hGnum, hBq]
  field_simp
  try ring

end Main

section GammaH

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ι₀ : AlgebraicClosure ℚ →+* ℂ)

local notation "ℚb" => AlgebraicClosure ℚ

scoped instance finiteIndex_GammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

variable (f : CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2)
  (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f : ℍ → ℂ) n ∈ ι₀.range)

theorem xBar_mem : xBar (CohCarrier.GammaH M H) ι₀ f hf ∈ Fbar (CohCarrier.GammaH M H) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  obtain ⟨G, B, hB0, hx'⟩ := exists_coeffMap_xBar_eq_div (CohCarrier.GammaH M H) ι₀ f hf hT

  have hC : coeffMap ι₀ (C (12 : ℚb)⁻¹ * xBar (CohCarrier.GammaH M H) ι₀ f hf) ∈
      laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    rw [hx']
    exact ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField M H G B hB0

  have hx'mem : C (12 : ℚb)⁻¹ * xBar (CohCarrier.GammaH M H) ι₀ f hf ∈ Fbar (CohCarrier.GammaH M H) :=
    mem_laurentBaseChange_of_coeffMap_mem ι₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) hC
  have h12 : (12 : ℚb) ≠ 0 := by norm_num
  have hxx : xBar (CohCarrier.GammaH M H) ι₀ f hf =
      C (12 : ℚb) * (C (12 : ℚb)⁻¹ * xBar (CohCarrier.GammaH M H) ι₀ f hf) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h12, map_one, one_mul]
  rw [hxx]
  refine mul_mem ?_ hx'mem
  have h12mem := (Fbar (CohCarrier.GammaH M H)).algebraMap_mem (12 : ℚb)
  rwa [algebraMap_laurentSeries_eq_single, ← C_apply] at h12mem

def omega : Ω[↥(Fbar (CohCarrier.GammaH M H))⁄AlgebraicClosure ℚ] :=
  (⟨xBar (CohCarrier.GammaH M H) ι₀ f hf, xBar_mem M H ι₀ f hf⟩ : Fbar (CohCarrier.GammaH M H)) •
    KaehlerDifferential.D (AlgebraicClosure ℚ) (Fbar (CohCarrier.GammaH M H))
      (⟨jBar, jBar_mem (CohCarrier.GammaH M H)⟩ : Fbar (CohCarrier.GammaH M H))

theorem diffQExp_omega :
    diffQExp (Fbar (CohCarrier.GammaH M H)) (omega M H ι₀ f hf) = fBar (CohCarrier.GammaH M H) ι₀ f hf := by
  rw [omega, diffQExp_smul_D]
  exact xBar_mul_qEuler_jBar (CohCarrier.GammaH M H) ι₀ f hf

theorem coeffMap_qExpansionDiffAlong_omega :
    coeffMap ι₀ (qExpansionDiffAlong (Fbar (CohCarrier.GammaH M H)).val (omega M H ι₀ f hf)) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 f) := by
  rw [ModularCurve.qExpansionDiffAlong_val_eq_diffQExp, diffQExp_omega, coeffMap_fBar]

end GammaH

end ModularCurve.LiftDGamma
p2m_reactivate "P2MW.S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.ModularCurve P2MW.S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.ModularCurve.LiftDGamma"
p2m_reactivate "P2MW.S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.ModularCurve P2MW.S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.ModularCurve.LiftDGamma"

open scoped MatrixGroups in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.ModularCurve ModularCurve.LiftDGamma in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (ι₀ : AlgebraicClosure ℚ →+* ℂ) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f : UpperHalfPlane → ℂ) n ∈ ι₀.range) :
    ∃ ω : Ω[↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))⁄AlgebraicClosure ℚ],
      ModularCurve.coeffMap ι₀ (ModularCurve.qExpansionDiffAlong (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)).val ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f : UpperHalfPlane → ℂ)) := by
  obtain ⟨H, rfl⟩ := CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0 M Γ hΓ₁ hΓ₀
  exact ⟨omega M H ι₀ f hf, coeffMap_qExpansionDiffAlong_omega M H ι₀ f hf⟩

#print axioms solution

end S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
end P2MW
export P2MW.S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion (solution)

-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_tubeEquation_smul_sub_self_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/430518d9-1f3c-52d6-a47a-a0835193c59a

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Theorems.Thm_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve ModularCurve.PlaceSpecialization"
open scoped Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar arithmeticGalois_smul_coeffEmb"
namespace TubeEqAnn
p2m_open "ModularCurve"

open AlgebraicCurve IsLocalRing

section Prolongation

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

noncomputable def cO (O : RegularProlongation A F Fbar) (a : A) : O.integers :=
  ⟨algebraMap L F a, (O.algebraMap_mem_iff a).mpr a.2⟩

@[scoped simp] theorem coe_cO (O : RegularProlongation A F Fbar) (a : A) :
    ((cO O a : O.integers) : F) = algebraMap L F a := rfl

theorem residue_cO (O : RegularProlongation A F Fbar) (a : A) :
    O.residue (cO O a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  O.residue_algebraMap a

theorem residue_cO_eq_zero (O : RegularProlongation A F Fbar) {a : A} (ha : a ∈ maximalIdeal A) :
    O.residue (cO O a) = 0 := by
  rw [residue_cO, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

theorem exists_mem_mul_inv_residue_eq (O : RegularProlongation A F Fbar) (f g : O.integers)
    (hg : O.residue g ≠ 0) :
    ∃ h : (f : F) * ((g : F))⁻¹ ∈ O.integers, O.residue ⟨_, h⟩ = O.residue f * (O.residue g)⁻¹ := by
  have hunit : IsUnit g := O.isUnit_of_residue_ne_zero hg
  set v : O.integers := ((hunit.unit⁻¹ : (↥O.integers)ˣ) : O.integers) with hv
  have hgv : g * v = 1 := by rw [hv]; exact hunit.mul_val_inv
  have hvF : (v : F) = ((g : F))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have := congrArg (fun z : O.integers => (z : F)) hgv
    simpa using this
  have hresv : O.residue v = (O.residue g)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul, hgv, map_one]
  have hmem : (f : F) * ((g : F))⁻¹ ∈ O.integers := by
    rw [← hvF, ← Subring.coe_mul]; exact SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have e : (⟨(f : F) * ((g : F))⁻¹, hmem⟩ : O.integers) = f * v := Subtype.ext (by rw [Subring.coe_mul, hvF])
  rw [e, map_mul, hresv]

end Prolongation

section AnnulusLemmas

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem hasValue_sub_algebraMap
    (W : Place L F) (f : F) (b c : L) (hb : W.HasValue f b) :
    W.HasValue (f - algebraMap L F c) (b - c) := by
  obtain ⟨hmem, hres⟩ := hb
  refine ⟨sub_mem hmem (W.algebraMap_mem' c), ?_⟩
  have : (⟨f - algebraMap L F c, sub_mem hmem (W.algebraMap_mem' c)⟩ : W.toValuationSubring)
      = ⟨f, hmem⟩ - algebraMap L W.toValuationSubring c := by
    apply Subtype.ext; simp [AlgebraicCurve.Place.coe_algebraMap]
  rw [this, map_sub, hres, AlgebraicCurve.Place.residue_algebraMap, map_sub]

theorem hasValue_evalAt (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.HasValue An.param (P.evalAt An.param) := by
  obtain ⟨hrat, hmem, -⟩ := An.mem_dom P hP
  exact ⟨hmem, (P.algebraMap_evalAt hrat hmem).symm⟩

theorem evalAt_eq_of_hasValue (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) {c : L}
    (h : P.HasValue An.param c) : P.evalAt An.param = c :=
  (hasValue_evalAt An hP).unique h

theorem ord_param_sub_algebraMap_eq_single (An : Annulus A F) {V' W : Place L F}
    (hV' : V' ∈ An.dom) (hW : W ∈ An.dom) :
    W.ord (An.param - algebraMap L F (V'.evalAt An.param)) = (Finsupp.single V' (1 : ℤ)) W := by
  classical
  by_cases hWV : W = V'
  · subst hWV
    rw [Finsupp.single_eq_same]
    exact An.ord_param_sub W hW
  · rw [Finsupp.single_apply, if_neg (Ne.symm hWV)]
    obtain ⟨-, -, ⟨hcA, hc𝔪⟩, hc0, m, hm, hπ⟩ := An.mem_dom V' hV'
    have hne : W.evalAt An.param - V'.evalAt An.param ≠ 0 := by
      intro heq
      apply hWV
      obtain ⟨P₀, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨_, hcA⟩ hc𝔪 hc0 ⟨m, hm, hπ⟩
      exact (huniq W ⟨hW, sub_eq_zero.1 heq⟩).trans (huniq V' ⟨hV', rfl⟩).symm
    exact (hasValue_sub_algebraMap W _ _ _ (hasValue_evalAt An hW)).ord_eq_zero hne

end AnnulusLemmas

end ModularCurve.TubeEqAnn
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve.TubeEqAnn"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar arithmeticGalois_smul_coeffEmb"
namespace TubeEqAnn
p2m_open "ModularCurve"

open AlgebraicCurve IsLocalRing

theorem centred_smul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ((∃ x : A, red x = a ∧
            0 < (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • W).ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • W).ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) := by
  classical
  obtain ⟨hunit, htame1⟩ :=
    ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn A hσ
  set g := arithmeticGalois (modularFunctionFieldFull (1 * q)) σ with hg
  have hgjF : g • (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
    rw [hg]
    exact arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull (1 * q)) σ
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))
  have hgjqF : g • (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
    rw [hg]
    exact arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull (1 * q)) σ
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))
  have hgc : ∀ c : AlgebraicClosure ℚ, g • algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (σ c) := by
    intro c
    rw [hg, AlgebraicCurve.SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois]
    rfl
  have hred_fix : ∀ x₀ : A, ∃ y₀ : A, (y₀ : AlgebraicClosure ℚ) = σ (x₀ : AlgebraicClosure ℚ) ∧ red y₀ = red x₀ := by
    intro x₀
    by_cases hz : ((x₀ : A) : AlgebraicClosure ℚ) = 0
    · refine ⟨0, ?_, ?_⟩
      · rw [hz, map_zero]; rfl
      · rw [show x₀ = 0 from Subtype.ext hz]
    obtain ⟨u₀, hu₀, hu₀res⟩ := hunit _ hz
    refine ⟨(u₀ : A) * x₀, by rw [Subring.coe_mul]; exact hu₀, ?_⟩
    by_cases hx₀ : red x₀ = 0
    · rw [map_mul, hx₀, mul_zero]
    · have hx₀u : IsUnit x₀ := by
        by_contra hnu
        exact hx₀ ((hker x₀).2 ((IsLocalRing.mem_maximalIdeal _).2 hnu))
      have h1 : A.tameCharacter ((hx₀u.unit : (↥A)ˣ) : A) σ = 1 := htame1 hx₀u.unit
      rw [IsUnit.unit_spec] at h1
      rw [h1] at hu₀res
      have hu₀1 : red (u₀ : A) = 1 := by
        have hm : (u₀ : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
          rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hu₀res, map_one, sub_self]
        have := (hker _).2 hm
        rwa [map_sub, map_one, sub_eq_zero] at this
      rw [map_mul, hu₀1, one_mul]
  obtain ⟨⟨x₀, hx₀a, hx₀ord⟩, ⟨y₀, hy₀a, hy₀ord⟩⟩ := hW
  obtain ⟨x₁, hx₁, hx₁red⟩ := hred_fix x₀
  obtain ⟨y₁, hy₁, hy₁red⟩ := hred_fix y₀
  refine ⟨⟨x₁, hx₁red.trans hx₀a, ?_⟩, ⟨y₁, hy₁red.trans hy₀a, ?_⟩⟩
  · have := AlgebraicCurve.SemilinearAut.ord_smul g W ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x₀ : A) : AlgebraicClosure ℚ))
    rw [smul_sub, hgjF, hgc, ← hx₁] at this
    rw [this]; exact hx₀ord
  · have := AlgebraicCurve.SemilinearAut.ord_smul g W ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((y₀ : A) : AlgebraicClosure ℚ))
    rw [smul_sub, hgjqF, hgc, ← hy₁] at this
    rw [this]; exact hy₀ord

end ModularCurve.TubeEqAnn
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve.TubeEqAnn"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve.TubeEqAnn"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar arithmeticGalois_smul_coeffEmb"
namespace TubeEqAnn
p2m_open "ModularCurve"

open AlgebraicCurve IsLocalRing

section Sides

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

theorem exists_mem_integersFst_residue₁_eq_of_smul_mem
    (Z : ↥(modularFunctionFieldBar (1 * q))) (π x m : A) (u : (↥A)ˣ)
    (hm : m ∈ IsLocalRing.maximalIdeal A) (hπ : ((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) = ((π : A) : AlgebraicClosure ℚ))
    (hπ0 : ((π : A) : AlgebraicClosure ℚ) ≠ 0)
    (hZ₁ : (((((π : A) : AlgebraicClosure ℚ))⁻¹ • Z : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (t : ↥(modularFunctionFieldBar (1 * q)))
    (ht : t = (Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((((u : A) * x : A)) : AlgebraicClosure ℚ))
          * (Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x : A) : AlgebraicClosure ℚ))⁻¹) :
    ∃ h : t ∈ R.R₁.integers, (R.residue₁ ⟨t, h⟩ : ↥(modularFunctionFieldC k 1)) = algebraMap k ↥(modularFunctionFieldC k 1) (red (u : A)) := by
  classical
  obtain ⟨hY, -⟩ := R.residue₁_eq_modularRedLocHom _ hZ₁
  set Y : R.R₁.integers := ⟨_, hY⟩ with hY_def
  set N : R.R₁.integers := cO R.R₁ m * Y - cO R.R₁ (u : A) with hN_def
  set D : R.R₁.integers := cO R.R₁ m * Y - 1 with hD_def
  have hresm : R.R₁.residue (cO R.R₁ m) = 0 := residue_cO_eq_zero R.R₁ hm
  have hresN : R.R₁.residue N = - algebraMap (ResidueField A) _ (IsLocalRing.residue A (u : A)) := by
    rw [hN_def, map_sub, map_mul, hresm, zero_mul, zero_sub, residue_cO]
  have hresD : R.R₁.residue D = -1 := by
    rw [hD_def, map_sub, map_mul, hresm, zero_mul, map_one, zero_sub]
  have hresD0 : R.R₁.residue D ≠ 0 := by rw [hresD]; exact neg_ne_zero.mpr one_ne_zero

  have hx0 : ((x : A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hπ
    exact hπ0 hπ.symm
  set cx : ↥(modularFunctionFieldBar (1 * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x : A) : AlgebraicClosure ℚ) with hcx
  have hcx0 : cx ≠ 0 := by rw [hcx]; exact (map_ne_zero _).mpr hx0
  have hxmπ : ((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) * (((π : A) : AlgebraicClosure ℚ))⁻¹ = 1 := by
    rw [hπ, mul_inv_cancel₀ hπ0]

  have hDF0 : (D : ↥(modularFunctionFieldBar (1 * q))) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((m : A) : AlgebraicClosure ℚ) * ((((π : A) : AlgebraicClosure ℚ))⁻¹ • Z) - 1 := by
    rw [hD_def]; rfl
  have hNF0 : (N : ↥(modularFunctionFieldBar (1 * q))) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((m : A) : AlgebraicClosure ℚ) * ((((π : A) : AlgebraicClosure ℚ))⁻¹ • Z)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((u : A) : A) : AlgebraicClosure ℚ) := by
    rw [hN_def]; rfl
  have hDF : Z - cx = cx * (D : ↥(modularFunctionFieldBar (1 * q))) := by
    rw [hDF0, Algebra.smul_def]
    calc Z - cx = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
            (((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) * (((π : A) : AlgebraicClosure ℚ))⁻¹) * Z - cx := by
          rw [hxmπ, map_one, one_mul Z]
      _ = cx * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((m : A) : AlgebraicClosure ℚ)
            * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((((π : A) : AlgebraicClosure ℚ))⁻¹) * Z) - 1) := by
          rw [map_mul, map_mul, hcx]; ring
  have huxL : ((((u : A) * x : A)) : AlgebraicClosure ℚ) = (((u : A) : A) : AlgebraicClosure ℚ) * ((x : A) : AlgebraicClosure ℚ) := Subring.coe_mul _ _ _
  have hNF : Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((((u : A) * x : A)) : AlgebraicClosure ℚ)
      = cx * (N : ↥(modularFunctionFieldBar (1 * q))) := by
    rw [hNF0, Algebra.smul_def, huxL, map_mul]
    calc Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((u : A) : A) : AlgebraicClosure ℚ) * cx
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
            (((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) * (((π : A) : AlgebraicClosure ℚ))⁻¹) * Z
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((u : A) : A) : AlgebraicClosure ℚ) * cx := by
          rw [hxmπ, map_one, one_mul Z]
      _ = cx * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((m : A) : AlgebraicClosure ℚ)
            * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((((π : A) : AlgebraicClosure ℚ))⁻¹) * Z)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((u : A) : A) : AlgebraicClosure ℚ)) := by
          rw [map_mul, map_mul, hcx]; ring

  obtain ⟨hmem, hres⟩ := exists_mem_mul_inv_residue_eq R.R₁ N D hresD0
  have hteq : t = (N : ↥(modularFunctionFieldBar (1 * q))) * ((D : ↥(modularFunctionFieldBar (1 * q))))⁻¹ := by
    rw [ht, hNF, hDF, mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hcx0]
    exact one_mul _
  have hmem' : t ∈ R.R₁.integers := by rw [hteq]; exact hmem
  refine ⟨hmem', ?_⟩
  have hOt : (⟨t, hmem'⟩ : R.R₁.integers) = ⟨_, hmem⟩ := Subtype.ext hteq
  have hres_t : R.R₁.residue ⟨_, hmem⟩ = algebraMap (ResidueField A) _ (IsLocalRing.residue A (u : A)) := by
    rw [hres, hresN, hresD, neg_mul, inv_neg, inv_one, mul_neg, mul_one, neg_neg]
  rw [LevelOneProlongationPair.residue₁_apply, hOt, hres_t]

  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A (u : A)))
    = algebraMap k (LaurentSeries k) (red (u : A))
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single, R.redBar_residue]

theorem exists_mem_integersSnd_residue₂_eq_one_of_fricke_mem
    (Z : ↥(modularFunctionFieldBar (1 * q)))
    (hZ₂ : ((frickeInvolutionBar (1 * q) Z : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hZ₂0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hZ₂⟩ ≠ 0)
    (x s : A) (hx : x ∈ IsLocalRing.maximalIdeal A) (hs : s ∈ IsLocalRing.maximalIdeal A)
    (t : ↥(modularFunctionFieldBar (1 * q)))
    (ht : t = (Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((s : A) : AlgebraicClosure ℚ))
          * (Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x : A) : AlgebraicClosure ℚ))⁻¹) :
    ∃ h : t ∈ R.R₂.integers, (R.residue₂ ⟨t, h⟩ : ↥(modularFunctionFieldC k 1)) = 1 := by
  classical
  obtain ⟨hW₁, hW₁res⟩ := R.residue₁_eq_modularRedLocHom _ hZ₂
  have hZO : Z ∈ R.R₂.integers := (R.mem_integers₂_iff Z).mpr hW₁
  set ZO : R.R₂.integers := ⟨Z, hZO⟩ with hZO_def
  have hresZ0 : R.R₂.residue ZO ≠ 0 := by
    intro h0
    apply hZ₂0
    rw [← hW₁res]
    have e : (⟨frickeInvolutionBar (1 * q) Z, hW₁⟩ : R.R₁.integers)
        = ⟨frickeInvolutionBar (1 * q) Z, (R.mem_integers₂_iff Z).mp hZO⟩ := rfl
    rw [e, ← R.residue₂_eq Z hZO, ← hZO_def, h0, map_zero]
    rfl
  set N : R.R₂.integers := ZO - cO R.R₂ s with hN_def
  set D : R.R₂.integers := ZO - cO R.R₂ x with hD_def
  have hresN : R.R₂.residue N = R.R₂.residue ZO := by
    rw [hN_def, map_sub, residue_cO_eq_zero R.R₂ hs, sub_zero]
  have hresD : R.R₂.residue D = R.R₂.residue ZO := by
    rw [hD_def, map_sub, residue_cO_eq_zero R.R₂ hx, sub_zero]
  obtain ⟨hmem, hres⟩ := exists_mem_mul_inv_residue_eq R.R₂ N D (by rw [hresD]; exact hresZ0)
  have hteq : t = (N : ↥(modularFunctionFieldBar (1 * q))) * ((D : ↥(modularFunctionFieldBar (1 * q))))⁻¹ := by
    rw [ht, hN_def, hD_def, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, coe_cO, coe_cO, hZO_def]
  have hmem' : t ∈ R.R₂.integers := by rw [hteq]; exact hmem
  refine ⟨hmem', ?_⟩
  have hOt : (⟨t, hmem'⟩ : R.R₂.integers) = ⟨_, hmem⟩ := Subtype.ext hteq
  rw [LevelOneProlongationPair.residue₂_apply, hOt, hres, hresN, hresD, mul_inv_cancel₀ hresZ0, map_one]

end Sides
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve.TubeEqAnn"

end ModularCurve.TubeEqAnn
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve.TubeEqAnn"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus.ModularCurve.TubeEqAnn"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (An : Annulus A ↥(modularFunctionFieldBar (1 * q)))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (hmod : ((An.modulus : AlgebraicClosure ℚ) ≠ 0))
    (hσZ : arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • An.param = An.param)
    (hZ₁ : ((((An.modulus : AlgebraicClosure ℚ))⁻¹ • An.param : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hZ₂ : ((frickeInvolutionBar (1 * q) An.param : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hZ₂0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hZ₂⟩ ≠ 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV : ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ (x : A) (u : (↥A)ˣ) (t : ↥(modularFunctionFieldBar (1 * q))) (h₁ : t ∈ R.R₁.integers) (h₂ : t ∈ R.R₂.integers),
      x ∈ IsLocalRing.maximalIdeal A ∧ (∃ d ∈ IsLocalRing.maximalIdeal A, x * d = An.modulus) ∧
      σ (x : AlgebraicClosure ℚ) = ((u : A) : AlgebraicClosure ℚ) * (x : AlgebraicClosure ℚ) ∧
      V.HasValue An.param (x : AlgebraicClosure ℚ) ∧
      t = (An.param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (σ (x : AlgebraicClosure ℚ)))
          * (An.param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))⁻¹ ∧
      (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k 1)) = algebraMap k ↥(modularFunctionFieldC k 1) (red (u : A)) ∧
      (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k 1)) = 1 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
        W.ord t = ((arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) W := by
  classical

  have hVdom : V ∈ An.dom := (hdom V).mpr hV
  obtain ⟨hVrat, hZV, ⟨hxA, hx𝔪⟩, hx0, m, hm𝔪, hπ⟩ := An.mem_dom V hVdom
  set x : A := ⟨V.evalAt An.param, hxA⟩ with hx_def
  have hxL : ((x : A) : AlgebraicClosure ℚ) = V.evalAt An.param := rfl
  have hxV : V.HasValue An.param ((x : A) : AlgebraicClosure ℚ) := by
    rw [hxL]; exact ModularCurve.TubeEqAnn.hasValue_evalAt An hVdom
  have hx0' : ((x : A) : AlgebraicClosure ℚ) ≠ 0 := by rw [hxL]; exact hx0
  have hπ' : ((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) = ((An.modulus : A) : AlgebraicClosure ℚ) := by
    rw [hxL]; exact hπ.symm
  have hxq : ∃ d ∈ IsLocalRing.maximalIdeal A, x * d = An.modulus :=
    ⟨m, hm𝔪, Subtype.ext (by rw [Subring.coe_mul]; exact hπ')⟩

  obtain ⟨hunit, -⟩ :=
    ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn A hσ
  obtain ⟨u, hu, -⟩ := hunit ((x : A) : AlgebraicClosure ℚ) hx0'
  set sx : A := (u : A) * x with hsx
  have hsxL : ((sx : A) : AlgebraicClosure ℚ) = σ ((x : A) : AlgebraicClosure ℚ) := by
    rw [hsx, Subring.coe_mul]; exact hu
  have hsx𝔪 : sx ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_left _ _ hx𝔪

  set g := arithmeticGalois (modularFunctionFieldFull (1 * q)) σ with hg
  set cx : ↥(modularFunctionFieldBar (1 * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x : A) : AlgebraicClosure ℚ) with hcx
  set cσx : ↥(modularFunctionFieldBar (1 * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (σ ((x : A) : AlgebraicClosure ℚ)) with hcσx
  set t : ↥(modularFunctionFieldBar (1 * q)) := (An.param - cσx) * (An.param - cx)⁻¹ with ht

  have hσVc := ModularCurve.TubeEqAnn.centred_smul (q := q) red hker a σ hσ V hV
  have hσVdom : g • V ∈ An.dom := (hdom _).mpr hσVc
  have hσV : (g • V).HasValue An.param (σ ((x : A) : AlgebraicClosure ℚ)) := by
    have h := AlgebraicCurve.Place.HasValue.smul g hxV
    rw [hg, hσZ, baseAut_arithmeticGalois] at h
    exact h
  have hevσ : (g • V).evalAt An.param = ((sx : A) : AlgebraicClosure ℚ) := by
    rw [hsxL]; exact ModularCurve.TubeEqAnn.evalAt_eq_of_hasValue An hσVdom hσV

  have hA : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord (An.param - cx) = (Finsupp.single V (1 : ℤ)) W := by
    intro W hW
    rw [hcx, hxL]
    exact ModularCurve.TubeEqAnn.ord_param_sub_algebraMap_eq_single An hVdom ((hdom W).mpr hW)
  have hB : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord (An.param - cσx) = (Finsupp.single (g • V) (1 : ℤ)) W := by
    intro W hW
    rw [hcσx, ← hsxL, ← hevσ]
    exact ModularCurve.TubeEqAnn.ord_param_sub_algebraMap_eq_single An hσVdom ((hdom W).mpr hW)
  have hGcx_ne : An.param - cx ≠ 0 := by
    intro h0'
    have := hA V hV
    rw [h0', Finsupp.single_eq_same] at this
    simp at this
  have hGcσx_ne : An.param - cσx ≠ 0 := by
    intro h0'
    have := hB (g • V) hσVc
    rw [h0', Finsupp.single_eq_same] at this
    simp at this
  have hord : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
      W.ord t = ((arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) W := by
    intro W hW
    rw [← hg, AlgebraicCurve.SemilinearAut.smul_single, Finsupp.sub_apply, ht,
      AlgebraicCurve.Place.ord_mul _ hGcσx_ne (inv_ne_zero hGcx_ne), AlgebraicCurve.Place.ord_inv, hA W hW, hB W hW]
    ring

  have hmod0 : ((An.modulus : A) : AlgebraicClosure ℚ) ≠ 0 := hmod
  obtain ⟨h₁, hres₁⟩ := ModularCurve.TubeEqAnn.exists_mem_integersFst_residue₁_eq_of_smul_mem R An.param An.modulus x m u
    hm𝔪 hπ' hmod0 hZ₁ t (by rw [ht, hcσx, hcx, ← hsxL, hsx])
  obtain ⟨h₂, hres₂⟩ := ModularCurve.TubeEqAnn.exists_mem_integersSnd_residue₂_eq_one_of_fricke_mem R An.param hZ₂ hZ₂0
    x sx hx𝔪 hsx𝔪 t (by rw [ht, hcσx, hcx, ← hsxL])
  exact ⟨x, u, t, h₁, h₂, hx𝔪, hxq, hu.symm, hxV, rfl, hres₁, hres₂, hord⟩

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus (solution)

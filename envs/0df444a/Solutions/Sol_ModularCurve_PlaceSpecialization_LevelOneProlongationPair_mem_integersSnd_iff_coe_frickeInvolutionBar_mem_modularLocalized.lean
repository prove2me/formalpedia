-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ac8ed5bf-e1b5-5314-b5ec-9e850e2ff2c0

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve IsLocalRing ModularCurve.CharPReduction"

namespace Ws14Port

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

omit [CharP k q] in

theorem inv_mem_modularLocalized_of_modularRedLocHom_ne_zero
    {f : LaurentSeries (AlgebraicClosure ℚ)}
    (hf : f ∈ modularLocalized (1 * q) A.toSubring red)
    (hπ : modularRedLocHom (1 * q) A.toSubring red ⟨f, hf⟩ ≠ 0) :
    f⁻¹ ∈ modularLocalized (1 * q) A.toSubring red := by
  obtain ⟨r, s, hs, hfs⟩ := hf
  have hspec := redLoc_spec (A := A.toSubring) (red := red) (R := modularRing (1 * q) A.toSubring)
    (hR := modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨f, ⟨r, s, hs, hfs⟩⟩ hfs
  have hπ' : redLoc (A := A.toSubring) (red := red) (R := modularRing (1 * q) A.toSubring)
      (hR := modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨f, ⟨r, s, hs, hfs⟩⟩ ≠ 0 := hπ
  have hr : redRes A.toSubring red (modularRing (1 * q) A.toSubring)
      (modularRing_le_integralCoeffs (1 * q) A.toSubring) r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero hπ' (redRes_ne_zero_of_notMem hs)
  have hr' : r ∉ redKer A.toSubring red (modularRing (1 * q) A.toSubring)
      (modularRing_le_integralCoeffs (1 * q) A.toSubring) :=
    (notMem_redKer_iff A.toSubring red _ _).mpr hr
  have hr0 : (r : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hr (by
    have : r = 0 := Subtype.ext h
    rw [this, map_zero])
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hfs
    exact hr0 hfs.symm
  refine ⟨s, r, hr', ?_⟩
  rw [← hfs, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul]

theorem mem_integersFst_of_coe_mem {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (1 * q) A.toSubring red) :
    ∃ h : g ∈ R.R₁.integers,
      ((R.residue₁ ⟨g, h⟩ : modularFunctionFieldC k 1) : LaurentSeries k)
        = modularRedLocHom (1 * q) A.toSubring red ⟨g, hg⟩ := by
  obtain ⟨h, hh⟩ := R.residue₁_eq_modularRedLocHom g hg
  exact ⟨h, by rw [R.residue₁_apply]; exact hh⟩

theorem residueFst_ne_zero_iff {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (1 * q) A.toSubring red)
    (h : g ∈ R.R₁.integers) :
    R.R₁.residue ⟨g, h⟩ ≠ 0 ↔ modularRedLocHom (1 * q) A.toSubring red ⟨g, hg⟩ ≠ 0 := by
  obtain ⟨h', hh⟩ := mem_integersFst_of_coe_mem R hg
  have h1 : R.R₁.residue ⟨g, h⟩ ≠ 0 ↔ R.residue₁ ⟨g, h⟩ ≠ 0 := by
    rw [R.residue₁_apply]
    exact (map_ne_zero R.ι).symm
  rw [h1, ne_eq, ne_eq, ← ZeroMemClass.coe_eq_zero, hh]

theorem coe_mem_of_mem_integersFst {g : ↥(modularFunctionFieldBar (1 * q))} (h : g ∈ R.R₁.integers) :
    (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (1 * q) A.toSubring red := by
  rcases eq_or_ne g 0 with rfl | hg0
  · exact zero_mem _
  rcases ModularCurve.coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized (A := A) red g with hmem | hinv
  · exact hmem
  · obtain ⟨hinv₁, -⟩ := mem_integersFst_of_coe_mem R hinv
    have hu : IsUnit (⟨g⁻¹, hinv₁⟩ : R.R₁.integers) :=
      IsUnit.of_mul_eq_one ⟨g, h⟩ (Subtype.ext (inv_mul_cancel₀ hg0))
    have hres : R.R₁.residue ⟨g⁻¹, hinv₁⟩ ≠ 0 := R.R₁.residue_ne_zero_of_isUnit hu
    have hπ := (residueFst_ne_zero_iff R hinv hinv₁).mp hres
    simpa using inv_mem_modularLocalized_of_modularRedLocHom_ne_zero hinv hπ

end Ws14Port

theorem Ws14Port.mem_integersFst_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (g : ↥(modularFunctionFieldBar (1 * q))) :
    g ∈ R.R₁.integers ↔
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
  ⟨Ws14Port.coe_mem_of_mem_integersFst R, fun hg => (Ws14Port.mem_integersFst_of_coe_mem R hg).1⟩

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (g : ↥(modularFunctionFieldBar (1 * q))) :
    g ∈ R.R₂.integers ↔
      ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  rw [R.mem_integers₂_iff, Ws14Port.mem_integersFst_iff]

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized (solution)

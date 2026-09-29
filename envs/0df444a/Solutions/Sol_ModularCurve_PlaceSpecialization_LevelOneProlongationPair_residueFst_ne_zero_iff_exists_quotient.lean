-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residueFst_ne_zero_iff_exists_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/78518d4f-b9d4-5580-a0ba-93d21eaf9dff

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_exists_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve IsLocalRing"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData coeffMap PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence CharPReduction.integralCoeffs CharPReduction.redRes CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularRedLocHom"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom R₁ mem_integersFst_iff_coe_mem_modularLocalized mem_integersFst_iff_exists_quotient"
namespace QExp2
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"

variable {L : Type*} [CommRing L] (B : Subring L)

def liftCoeffs (x : LaurentSeries L) (hx : ∀ n : ℤ, x.coeff n ∈ B) : LaurentSeries B where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (fun _ hn h => hn (Subtype.ext h))

@[scoped simp] theorem coeffMap_subtype_liftCoeffs (x : LaurentSeries L) (hx : ∀ n : ℤ, x.coeff n ∈ B) :
    coeffMap B.subtype (liftCoeffs B x hx) = x := by
  ext n
  rfl

theorem coeffMap_subtype_injective :
    Function.Injective (coeffMap B.subtype : LaurentSeries B →+* LaurentSeries L) := by
  intro x y h
  ext n
  exact congrArg (fun z : LaurentSeries L => z.coeff n) h

@[scoped simp] theorem coeffMap_vsubtype_liftCoeffs {K : Type*} [Field K] (A : ValuationSubring K)
    (x : LaurentSeries K) (hx : ∀ n : ℤ, x.coeff n ∈ A.toSubring) :
    coeffMap A.subtype (liftCoeffs A.toSubring x hx) = x := by
  ext n
  rfl

theorem coeffMap_vsubtype_injective {K : Type*} [Field K] (A : ValuationSubring K) :
    Function.Injective (coeffMap A.subtype : LaurentSeries A →+* LaurentSeries K) := by
  intro x y h
  ext n
  exact congrArg (fun z : LaurentSeries K => z.coeff n) h

variable {k : Type*} [Field k] (red : B →+* k)
  (S : Subring (LaurentSeries L)) (hS : S ≤ CharPReduction.integralCoeffs B)

theorem redRes_eq_coeffMap_liftCoeffs (r : S) :
    CharPReduction.redRes B red S hS r = coeffMap red (liftCoeffs B (r : LaurentSeries L) (hS r.2)) := by
  ext n
  rfl

end QExp2
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2"

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2 P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization.LevelOneProlongationPair"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2 P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2 P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve"

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization.LevelOneProlongationPair in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) :
    (∃ h : f ∈ R.R₁.integers, R.residue₁ ⟨f, h⟩ ≠ 0) ↔
      ∃ x y : LaurentSeries A, coeffMap red x ≠ 0 ∧ coeffMap red y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
  classical
  set MR := CharPReduction.modularRing (1 * q) A.toSubring with hMR
  have hR : MR ≤ CharPReduction.integralCoeffs A.toSubring :=
    CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring
  constructor
  · rintro ⟨h, hres⟩
    have hfO := (R.mem_integersFst_iff_coe_mem_modularLocalized f).mp h
    obtain ⟨r, s, hs, hfs⟩ :=
      (CharPReduction.mem_localizedAtKer A.toSubring red MR hR).mp hfO
    obtain ⟨h', hdict⟩ := R.residue₁_eq_modularRedLocHom f hfO
    have hπne : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hfO⟩ ≠ 0 := by
      rw [← hdict]
      intro h0
      apply hres
      rw [residue₁_apply]
      exact_mod_cast h0
    have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := MR) (hR := hR)
      ⟨_, hfO⟩ hfs
    have hsne : CharPReduction.redRes A.toSubring red MR hR s ≠ 0 :=
      (CharPReduction.notMem_redKer_iff A.toSubring red MR hR).mp hs
    have hrne : CharPReduction.redRes A.toSubring red MR hR r ≠ 0 := by
      rw [← hspec]
      exact mul_ne_zero hπne hsne
    refine ⟨ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.liftCoeffs A.toSubring (r : LaurentSeries (AlgebraicClosure ℚ)) (hR r.2),
      ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.liftCoeffs A.toSubring (s : LaurentSeries (AlgebraicClosure ℚ)) (hR s.2), ?_, ?_, ?_⟩
    · rwa [← ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.redRes_eq_coeffMap_liftCoeffs A.toSubring red MR hR r]
    · rwa [← ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.redRes_eq_coeffMap_liftCoeffs A.toSubring red MR hR s]
    · rw [ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.coeffMap_vsubtype_liftCoeffs, ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.coeffMap_vsubtype_liftCoeffs]
      exact hfs
  · rintro ⟨x, y, hx, hy, hxy⟩
    have h : f ∈ R.R₁.integers := (mem_integersFst_iff_exists_quotient R f).mpr ⟨x, y, hy, hxy⟩
    refine ⟨h, fun hres0 => ?_⟩
    have hfO := (R.mem_integersFst_iff_coe_mem_modularLocalized f).mp h
    obtain ⟨r, s, hs, hfs⟩ :=
      (CharPReduction.mem_localizedAtKer A.toSubring red MR hR).mp hfO
    obtain ⟨h', hdict⟩ := R.residue₁_eq_modularRedLocHom f hfO
    have hπ0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hfO⟩ = 0 := by
      rw [← hdict]
      have : R.residue₁ ⟨f, h'⟩ = 0 := hres0
      rw [residue₁_apply] at this
      rw [this]
      rfl
    have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := MR) (hR := hR)
      ⟨_, hfO⟩ hfs
    have hr0 : CharPReduction.redRes A.toSubring red MR hR r = 0 := by
      rw [← hspec]
      change CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hfO⟩ * _ = 0
      rw [hπ0, zero_mul]
    have hid : coeffMap A.subtype x * (s : LaurentSeries (AlgebraicClosure ℚ))
        = (r : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y := by
      rw [← hxy, ← hfs]
      ring
    have hA : x * ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.liftCoeffs A.toSubring (s : LaurentSeries (AlgebraicClosure ℚ)) (hR s.2)
        = ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.liftCoeffs A.toSubring (r : LaurentSeries (AlgebraicClosure ℚ)) (hR r.2) * y := by
      apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.coeffMap_vsubtype_injective A
      rw [map_mul, map_mul, ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.coeffMap_vsubtype_liftCoeffs, ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.coeffMap_vsubtype_liftCoeffs]
      exact hid
    have hred := congrArg (coeffMap red) hA
    rw [map_mul, map_mul, ← ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.redRes_eq_coeffMap_liftCoeffs A.toSubring red MR hR r, hr0,
      zero_mul] at hred
    have hsne : coeffMap red (ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.liftCoeffs A.toSubring (s : LaurentSeries (AlgebraicClosure ℚ)) (hR s.2)) ≠ 0 := by
      rw [← ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2.redRes_eq_coeffMap_liftCoeffs A.toSubring red MR hR s]
      exact (CharPReduction.notMem_redKer_iff A.toSubring red MR hR).mp hs
    exact mul_ne_zero hx hsne hred

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.QExp2 P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.ModularCurve.PlaceSpecialization.LevelOneProlongationPair"

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient (solution)

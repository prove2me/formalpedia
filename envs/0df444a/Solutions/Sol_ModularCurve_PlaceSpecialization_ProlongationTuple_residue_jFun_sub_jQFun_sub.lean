-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.residue_jFun_sub_jQFun_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f2563c8d-4574-5079-a2d4-762c33eff915

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand jq ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow KroneckerCongruence jGeomGen IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC coeffMap_qExpand geomAut_atkinLehner_comp_legs exists_isAtkinLehnerAutFull_of_prime_of_not_dvd"
p2m_open "ModularCurve"

namespace DiscCoordResidue

local notation "𝕂" => AlgebraicClosure ℚ

p2m_open "ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple IsLocalRing"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring 𝕂}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral 𝕂 N q}
  {hβ : HeckeBetaBarIntegral 𝕂 N q}

noncomputable def jBarN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (modularFunctionField_le_full N (jq_mem N))⟩

theorem heckeAlphaBar_jBarN : heckeAlphaBar 𝕂 N q (jBarN N) = jFun N q :=
  Subtype.ext (coe_heckeAlphaBar N q _)

theorem heckeBetaBar_jBarN : heckeBetaBar 𝕂 N q (jBarN N) = jQFun N q := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand 𝕂 q (coeffEmb 𝕂 jq) = coeffEmb 𝕂 (qExpand ℚ q jq)
  rw [coeffEmb, ModularCurve.coeffMap_qExpand]

theorem atkinLehnerBar_jFun (hqN : ¬ q ∣ N) : atkinLehnerBar N q (jFun N q) = jQFun N q := by
  have hσ : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  have h := (geomAut_atkinLehner_comp_legs 𝕂 N q _ hσ).1
  have h' := congrArg (fun φ => φ (jBarN N)) h
  simp only [AlgHom.comp_apply] at h'
  rw [heckeAlphaBar_jBarN, heckeBetaBar_jBarN] at h'
  exact h'

theorem atkinLehnerBar_jQFun (hqN : ¬ q ∣ N) : atkinLehnerBar N q (jQFun N q) = jFun N q := by
  have hσ : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  have h := (geomAut_atkinLehner_comp_legs 𝕂 N q _ hσ).2
  have h' := congrArg (fun φ => φ (jBarN N)) h
  simp only [AlgHom.comp_apply] at h'
  rw [heckeAlphaBar_jBarN, heckeBetaBar_jBarN] at h'
  exact h'

noncomputable def constA (a : A) : LaurentSeries A := HahnSeries.single 0 a

theorem coeffMap_subtype_constA (a : A) :
    coeffMap A.subtype (constA a) = algebraMap 𝕂 (LaurentSeries 𝕂) (a : 𝕂) := by
  rw [constA, coeffMap_single, algebraMap_laurentSeries_eq_single]; rfl

theorem coeffMap_red_constA (a : A) :
    coeffMap red (constA a) = algebraMap k (LaurentSeries k) (red a) := by
  rw [constA, coeffMap_single, algebraMap_laurentSeries_eq_single]

theorem coe_jFun_sub (a : A) :
    ((jFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂) :
        modularFunctionFieldBar (N * q)) : LaurentSeries 𝕂)
      = coeffMap A.subtype (jqModC A - constA a) := by
  rw [map_sub, coeffMap_jqModC, coeffMap_subtype_constA]
  show coeffEmb 𝕂 jq - _ = _
  congr 1
  exact coeffMap_jqModC _

theorem coe_jQFun_sub (a : A) :
    ((jQFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂) :
        modularFunctionFieldBar (N * q)) : LaurentSeries 𝕂)
      = coeffMap A.subtype (qExpand A q (jqModC A) - constA a) := by
  rw [map_sub, ModularCurve.coeffMap_qExpand, coeffMap_jqModC, coeffMap_subtype_constA]
  show coeffEmb 𝕂 (qExpand ℚ q jq) - _ = _
  congr 1
  rw [coeffEmb, ModularCurve.coeffMap_qExpand]
  congr 1
  exact coeffMap_jqModC _

theorem coeffMap_redBar_residue {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (y : LaurentSeries A) :
    coeffMap R.redBar (coeffMap (IsLocalRing.residue A) y) = coeffMap red y := by
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext R.redBar_residue) y

theorem exists_mem_integers_coe_residue₁_eq {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (f : modularFunctionFieldBar (N * q)) (y : LaurentSeries A)
    (hf : (f : LaurentSeries 𝕂) = coeffMap A.subtype y) :
    ∃ h : f ∈ R.R₁.integers,
      ((R.residue₁ ⟨f, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := hf ▸ f.2
  obtain ⟨h', hr⟩ := R.residue₁_coeffMap y hy
  have e : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) = f := Subtype.ext hf.symm
  rw [e] at h'
  refine ⟨h', ?_⟩
  rw [residue₁_apply, R.ι_coe]
  have e' : (⟨f, h'⟩ : R.R₁.integers) = ⟨⟨coeffMap A.subtype y, hy⟩, e ▸ h'⟩ := Subtype.ext e.symm
  rw [e', hr, coeffMap_redBar_residue]

end DiscCoordResidue

end ModularCurve

open ModularCurve.DiscCoordResidue ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N) (a : A) :
    ∃ (h₁ : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers)
      (h₂ : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers)
      (h₃ : ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers)
      (h₄ : ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers),
      R.residue₁ ⟨_, h₁⟩ = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) ∧
      R.residue₂ ⟨_, h₂⟩ = jGeomGen k N ^ q - algebraMap k ↥(modularFunctionFieldC k N) (red a) ∧
      R.residue₁ ⟨_, h₃⟩ = jGeomGen k N ^ q - algebraMap k ↥(modularFunctionFieldC k N) (red a) ∧
      R.residue₂ ⟨_, h₄⟩ = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by

  obtain ⟨h₁, e₁⟩ := exists_mem_integers_coe_residue₁_eq R _ _ (coe_jFun_sub (N := N) (q := q) a)
  obtain ⟨h₃, e₃⟩ := exists_mem_integers_coe_residue₁_eq R _ _ (coe_jQFun_sub (N := N) (q := q) a)
  have E₁ : R.residue₁ ⟨_, h₁⟩ = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    apply Subtype.ext
    rw [e₁, map_sub, coeffMap_jqModC, coeffMap_red_constA]
    rfl
  have E₃ : R.residue₁ ⟨_, h₃⟩ = jGeomGen k N ^ q - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    apply Subtype.ext
    rw [e₃, map_sub, ModularCurve.coeffMap_qExpand, coeffMap_jqModC, coeffMap_red_constA,
      qExpand_jqModC_eq_pow k data hKr]
    rfl

  have hw₁ : atkinLehnerBar N q (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ))
      = ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    rw [map_sub, atkinLehnerBar_jFun hqN, AlgEquiv.commutes]
  have hw₃ : atkinLehnerBar N q (ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ))
      = ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    rw [map_sub, atkinLehnerBar_jQFun hqN, AlgEquiv.commutes]
  have h₂ : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hw₁]; exact h₃
  have h₄ : ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hw₃]; exact h₁
  have E₂ : R.residue₂ ⟨_, h₂⟩ = jGeomGen k N ^ q - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    rw [residue₂_apply, R.residue₂_eq, ← residue₁_apply]
    have : (⟨atkinLehnerBar N q (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)),
        (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp h₂)⟩ : R.R₁.integers) = ⟨_, h₃⟩ :=
      Subtype.ext hw₁
    rw [this, E₃]
  have E₄ : R.residue₂ ⟨_, h₄⟩ = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    rw [residue₂_apply, R.residue₂_eq, ← residue₁_apply]
    have : (⟨atkinLehnerBar N q (ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)),
        (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp h₄)⟩ : R.R₁.integers) = ⟨_, h₁⟩ :=
      Subtype.ext hw₃
    rw [this, E₁]
  exact ⟨h₁, h₂, h₃, h₄, E₁, E₂, E₃, E₄⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub (solution)

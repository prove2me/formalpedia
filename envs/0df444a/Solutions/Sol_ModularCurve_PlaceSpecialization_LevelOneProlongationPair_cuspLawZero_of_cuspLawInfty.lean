-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawZero_of_cuspLawInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/195d4376-5258-5861-a753-a5a070c8f16a

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_of_cuspLawInfty
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve

namespace Ws14Fricke

theorem hasValue_smul_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (v : Place K F) (g : F) (a : K) :
    (σ • v).HasValue (σ g) a ↔ v.HasValue g a := by

  have one : ∀ (τ : F ≃ₐ[K] F) (w : Place K F) (x : F), w.HasValue x a → (τ • w).HasValue (τ x) a := by
    intro τ w x ⟨hx, hres⟩
    let e := Place.smulRingEquiv τ w.toValuationSubring
    have hmem : τ x ∈ (τ • w).toValuationSubring := (e ⟨x, hx⟩).2
    refine ⟨hmem, ?_⟩
    have hex : (⟨τ x, hmem⟩ : (τ • w).toValuationSubring) = e ⟨x, hx⟩ := Subtype.ext rfl
    have key : (Place.smulResidueAlgEquiv τ w) (residue w.toValuationSubring ⟨x, hx⟩)
        = residue (τ • w).toValuationSubring (e ⟨x, hx⟩) := by
      show IsLocalRing.ResidueField.mapEquiv _ (residue _ _) = residue _ _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      rfl
    rw [hex, ← key, hres, AlgEquiv.commutes]
  refine ⟨fun h => ?_, one σ v g⟩
  have := one σ⁻¹ (σ • v) (σ g) h
  rwa [inv_smul_smul, show σ⁻¹ (σ g) = g from σ.symm_apply_apply g] at this

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem isFrickeAutFull_one_mul (q : ℕ) [Fact q.Prime] :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jqFun :
    frickeInvolutionBar (1 * q) (PlaceSpecialization.jqFun (q := q)) = PlaceSpecialization.jFun (q := q) :=
  (frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)).trans
    (Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq)))

theorem frickeInvolutionBar_jFun :
    frickeInvolutionBar (1 * q) (PlaceSpecialization.jFun (q := q)) = PlaceSpecialization.jqFun (q := q) := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)
  have e : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩
        : modularFunctionFieldBar (1 * q)) = PlaceSpecialization.jFun (q := q) :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [e] at h
  exact h

theorem frickeInvolutionBar_tZero :
    frickeInvolutionBar (1 * q) (PlaceSpecialization.tZero (q := q)) = PlaceSpecialization.tInfty (q := q) := by
  rw [PlaceSpecialization.tZero, PlaceSpecialization.tInfty, map_div₀, map_pow,
    frickeInvolutionBar_jFun, frickeInvolutionBar_jqFun]

theorem redFst_frickeInvolutionBar_smul (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redFst (frickeInvolutionBar (1 * q) • W) = P.redSnd W := by
  show P.sp _ = P.sp _
  rw [restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul q hα hβ]

theorem redSnd_frickeInvolutionBar_smul (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redSnd (frickeInvolutionBar (1 * q) • W) = P.redFst W := by
  show P.sp _ = P.sp _
  rw [restrictAlong_heckeBetaBar_frickeInvolutionBar_smul q hα hβ]

theorem redSnd_cuspZeroBar (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.redSnd (cuspZeroBar (1 * q)) = P.redFst (cuspInftyBar (1 * q)) := by
  rw [cuspZeroBar_def, redSnd_frickeInvolutionBar_smul]

theorem isCuspidal_frickeInvolutionBar_smul_iff (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.IsCuspidal (frickeInvolutionBar (1 * q) • W) ↔ PlaceSpecialization.IsCuspidal' P W := by
  unfold PlaceSpecialization.IsCuspidal PlaceSpecialization.IsCuspidal'
  refine forall_congr' fun a => ?_
  rw [← frickeInvolutionBar_jqFun, ← Place.ord_smul (frickeInvolutionBar (1 * q)) W, map_sub, AlgEquiv.commutes]

theorem isInftySide_frickeInvolutionBar_smul_iff (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.IsInftySide (frickeInvolutionBar (1 * q) • W) ↔ P.IsZeroSide W := by
  unfold PlaceSpecialization.IsInftySide PlaceSpecialization.IsZeroSide
  refine and_congr (isCuspidal_frickeInvolutionBar_smul_iff P W) (exists_congr fun τ => and_congr Iff.rfl ?_)
  rw [← frickeInvolutionBar_tZero, hasValue_smul_iff]

theorem mapDomain_redFst_filter_isInftySide_frickeInvolutionBar_smul (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (letI := Classical.decPred P.IsInftySide; letI := Classical.decPred P.IsZeroSide;
    Finsupp.mapDomain P.redFst ((frickeInvolutionBar (1 * q) • D).filter P.IsInftySide)
      = Finsupp.mapDomain P.redSnd (D.filter P.IsZeroSide)) := by
  classical
  have hparts : (frickeInvolutionBar (1 * q) • D).filter P.IsInftySide
      = frickeInvolutionBar (1 * q) • D.filter P.IsZeroSide := by
    ext W
    rw [Divisor.smul_apply]
    simp only [Finsupp.filter_apply, Divisor.smul_apply]
    rw [← isInftySide_frickeInvolutionBar_smul_iff P, smul_inv_smul]
  rw [hparts, Divisor.smul_def, ← Finsupp.mapDomain_comp]
  congr 1
  funext W
  exact redFst_frickeInvolutionBar_smul P W

end Ws14Fricke

open Ws14Fricke in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : PlaceSpecialization.LevelOneProlongationPair P)
    (hI : R.CuspLawInfty) : R.CuspLawZero := by
  classical
  intro f h₁ h₂ hr₁ hr₂ D hD
  have hwwf : (frickeInvolutionBar (1 * q)) ((frickeInvolutionBar (1 * q)) f) = f := frickeInvolutionBar_frickeInvolutionBar (1 * q) f
  have hg₁ : (frickeInvolutionBar (1 * q)) f ∈ R.R₁.integers := (R.mem_integers₂_iff f).mp h₂
  have hg₂ : (frickeInvolutionBar (1 * q)) f ∈ R.R₂.integers := by rw [R.mem_integers₂_iff, hwwf]; exact h₁
  have hres₁g : R.R₁.residue ⟨(frickeInvolutionBar (1 * q)) f, hg₁⟩ = R.R₂.residue ⟨f, h₂⟩ := (R.residue₂_eq f h₂).symm
  have hres₂g : R.R₂.residue ⟨(frickeInvolutionBar (1 * q)) f, hg₂⟩ = R.R₁.residue ⟨f, h₁⟩ := by
    rw [R.residue₂_eq]
    obtain ⟨h', e⟩ : ∃ h' : (frickeInvolutionBar (1 * q)) ((frickeInvolutionBar (1 * q)) f) ∈ R.R₁.integers, R.R₁.residue ⟨(frickeInvolutionBar (1 * q)) ((frickeInvolutionBar (1 * q)) f), h'⟩ = R.R₁.residue ⟨f, h₁⟩ :=
      ⟨(R.mem_integers₂_iff _).mp hg₂, by congr 1; exact Subtype.ext hwwf⟩
    exact e
  have hD' : ∀ W, ((frickeInvolutionBar (1 * q)) • D) W = W.ord ((frickeInvolutionBar (1 * q)) f) := fun W => by
    rw [AlgebraicCurve.Divisor.smul_apply, hD, ← Place.ord_smul (frickeInvolutionBar (1 * q)) ((frickeInvolutionBar (1 * q))⁻¹ • W), smul_inv_smul]
  have key := hI ((frickeInvolutionBar (1 * q)) f) hg₁ hg₂ (hres₁g ▸ hr₂) (hres₂g ▸ hr₁) ((frickeInvolutionBar (1 * q)) • D) hD'
  rw [mapDomain_redFst_filter_isInftySide_frickeInvolutionBar_smul P D, ← redSnd_cuspZeroBar P] at key
  rw [key, PlaceSpecialization.LevelOneProlongationPair.residue₁_apply, PlaceSpecialization.LevelOneProlongationPair.residue₂_apply, hres₁g]

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_of_cuspLawInfty
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_of_cuspLawInfty (solution)

-- Prove2me | solution 1 for GlobalTheory.exists_basis_kaehler_of_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:34.184887+00:00
-- url     : https://prove2.me/submissions/8c3aea55-2e14-464e-a3fd-40b7b0e4c725

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_ordTop_vw_zero
import Theorems.Thm_GlobalTheory_fracKaehlerBasis_apply
import Theorems.Thm_GlobalTheory_topFormCoeff_topFormGen
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti
attribute [local simp] GlobalTheory.dlogWedge_empty
attribute [local simp] GlobalTheory.ordTop_vw_zero
attribute [local simp] GlobalTheory.fracKaehlerBasis_apply
attribute [local simp] GlobalTheory.topFormCoeff_topFormGen

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GlobalTheory
theorem _root_.solution {K F ι : Type*} [Field K] [Field F]
    [Algebra K F] {v : ι → F} (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] :
    ∃ b : Basis ι F Ω[F⁄K], ∀ i, b i = D K F (v i) := by
  let P := MvPolynomial ι K
  let A := Algebra.adjoin K (Set.range v)
  let L := IntermediateField.adjoin K (Set.range v)
  letI : Algebra P A := hv.aevalEquiv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower K P A :=
    .of_algebraMap_eq fun r => (hv.aevalEquiv.commutes r).symm
  haveI : Algebra.FormallyEtale P A :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_isSeparable _ F
  haveI : Algebra.FormallyEtale A F := .comp A L F
  let b₁ : Basis ι A Ω[A⁄K] :=
    ((mvPolynomialBasis K ι).baseChange A).map (tensorKaehlerEquivOfFormallyEtale K P A)
  refine ⟨(b₁.baseChange F).map (tensorKaehlerEquivOfFormallyEtale K A F), fun i => ?_⟩
  simp only [b₁, Basis.map_apply, Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
    mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
  have h : algebraMap A F (algebraMap P A (MvPolynomial.X i)) = v i := by
    change algebraMap A F (hv.aevalEquiv (MvPolynomial.X i)) = v i
    rw [hv.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  rw [← h, ← map_D K K A F, ← map_D K K P A]
  exact congrArg _ ((mapBaseChange_tmul K P A 1 _).trans (one_smul _ _))
end GlobalTheory

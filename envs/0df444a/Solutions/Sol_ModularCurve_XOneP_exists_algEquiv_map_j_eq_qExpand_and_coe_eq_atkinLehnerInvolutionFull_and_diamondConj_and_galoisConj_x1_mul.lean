-- Prove2me | solution 1 for ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b34ad8f6-dec9-5892-a2f0-bdcb8d1ae4d3

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul
import Theorems.Thm_ModularCurve_XOneP_algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul
import Theorems.Thm_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    [NeZero p] :
    ∃ σ : ↥K ≃ₐ[L] ↥K,

      ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) ∧

      (∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
        (hfK : ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K),
        ((σ ⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK⟩ : ↥K) : LaurentSeries L) =
          ModularCurve.coeffEmb L ((ModularCurve.atkinLehnerInvolutionFull M p f :
            ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ)) ∧

      (∀ (d d' : ℕ), d.Coprime (M * p) → d'.Coprime (M * p) →
        ((d' : ZMod M) = (d : ZMod M)) → ((d' : ZMod p) * (d : ZMod p) = 1) →
        ∀ (θd θd' : ↥K ≃ₐ[L] ↥K),
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θd x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θd' x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L)) ∧

      (∀ (s : L ≃ₐ[ℚ] L) (b : ℕ), b.Coprime p → s ζ = ζ ^ b →
        ∀ (b' : ℕ), b'.Coprime (M * p) → ((b' : ZMod M) = 1) → ((b' : ZMod p) = (b : ZMod p)) →
        ∀ (Ss : ↥K ≃+* ↥K),
          (∀ x : ↥K, ((Ss x : ↥K) : LaurentSeries L) =
            ModularCurve.coeffMap (s.toAlgHom.toRingHom) ((x : ↥K) : LaurentSeries L)) →
        ∀ (θb' : ↥K ≃ₐ[L] ↥K),
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θb' x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) b') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          ∀ x : ↥K, ((Ss (σ (Ss.symm x)) : ↥K) : LaurentSeries L) = ((σ (θb' x) : ↥K) : LaurentSeries L)) := by
  obtain ⟨σ, h1, h4, hW⟩ :=
    ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul
      p M hpM L ζ hζ K hK j hj
  exact ⟨σ, h1, h4,
    ModularCurve.XOneP.algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul p M hpM L ζ hζ K hK j hj σ hW,
    ModularCurve.XOneP.ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul p M hpM L ζ hζ K hK j hj σ hW⟩

#print axioms solution

end S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul (solution)

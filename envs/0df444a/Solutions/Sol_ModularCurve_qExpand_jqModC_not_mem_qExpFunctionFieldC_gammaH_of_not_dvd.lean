-- Prove2me | solution 1 for ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/25fa401a-a3ce-59c3-93fa-73863789077d

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP
import Theorems.Thm_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charZero
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open scoped MatrixGroups

namespace NonmemPen14

open CongruenceSubgroup in

theorem gammaH_bot_le_of_dvd {M M' : ℕ} [NeZero M] [NeZero M'] (h : M ∣ M') :
    CohCarrier.GammaH M' ⊥ ≤ CohCarrier.GammaH M ⊥ := by
  intro A hA
  obtain ⟨hA0, h1⟩ := CohCarrier.mem_GammaH_iff.mp hA
  rw [Subgroup.mem_bot] at h1
  have h11 : (((A : SL(2, ℤ)) 1 1 : ℤ) : ZMod M') = 1 := by
    have := congrArg (fun u : (ZMod M')ˣ => (u : ZMod M')) h1
    first | exact this | simpa [Gamma0Map] using this | (simp [Gamma0Map] at this; exact this)
  have h10 : (((A : SL(2, ℤ)) 1 0 : ℤ) : ZMod M') = 0 := Gamma0_mem.mp hA0
  have hA0' : A ∈ Gamma0 M := by
    rw [Gamma0_mem]
    have := congrArg (ZMod.castHom h (ZMod M)) h10
    rwa [map_intCast, map_zero] at this
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0', ?_⟩
  rw [Subgroup.mem_bot]
  ext
  have := congrArg (ZMod.castHom h (ZMod M)) h11
  rw [map_intCast, map_one] at this
  first | exact this | simpa [Gamma0Map] using this

theorem gammaH_mono {M : ℕ} {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH M H' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

end NonmemPen14

theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (hNK : ((N : ℕ) : K) ≠ 0)
    (d : ℕ) [NeZero d] (hd : ¬ d ∣ N) (hdK : ((d : ℕ) : K) ≠ 0) :
    ModularCurve.qExpand K d (ModularCurve.jqModC K) ∉ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H') := by
  intro hmem

  have hmem1 : ModularCurve.qExpand K d (ModularCurve.jqModC K) ∈ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N ⊥) :=
    ModularCurve.qExpFunctionFieldC_mono K (NonmemPen14.gammaH_mono bot_le) hmem
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  ·
    haveI : Fact p.Prime := ⟨hprime⟩
    have hpN : ¬ p ∣ N := fun h => hNK ((CharP.cast_eq_zero_iff K p N).mpr h)
    have hpd : ¬ p ∣ d := fun h => hdK ((CharP.cast_eq_zero_iff K p d).mpr h)
    have hpNd : ¬ p ∣ N * d := fun h => (hprime.dvd_mul.mp h).elim hpN hpd
    haveI : CharP (AlgebraicClosure K) p := charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
    have hmemb : ModularCurve.coeffMap (algebraMap K (AlgebraicClosure K)) (ModularCurve.qExpand K d (ModularCurve.jqModC K)) ∈
        ModularCurve.qExpFunctionFieldC (AlgebraicClosure K) (CohCarrier.GammaH N ⊥) := by
      rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC K (AlgebraicClosure K) (CohCarrier.GammaH N ⊥)]
      exact IntermediateField.subset_adjoin _ _ ⟨_, hmem1, rfl⟩
    have hj : ModularCurve.coeffMap (algebraMap K (AlgebraicClosure K)) (ModularCurve.jqModC K) = ModularCurve.jqModC (AlgebraicClosure K) :=
      ModularCurve.map_jqModC _
    rw [ModularCurve.coeffMap_qExpand, hj] at hmemb
    exact ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP p (AlgebraicClosure K) N d hpNd hd hmemb
  ·
    haveI : CharZero K := CharP.charP_to_charZero K
    exact ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charZero K N d hd hmem1

end S_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd (solution)

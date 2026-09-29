-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_det_placeEmbed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ae145e63-a145-563c-b5f1-34ea7fec9f46

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_det_placeEmbed
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker AdelicDock NumberField.AdelicLevel NumberField.TateGlobal
open scoped NNReal

noncomputable section

namespace Ws23NormAtP

variable (p : HeightOneSpectrum (𝓞 ℚ))

def idl : (p.adicCompletion ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (Units.map (finIncl (𝓞 ℚ) ℚ)).comp (localUnit (𝓞 ℚ) ℚ p)

theorem uniformizerIdele_eq : AutomorphicForm.uniformizerIdele ℚ p = idl p (uniformizerUnit ℚ p) := rfl

theorem det_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    Matrix.GeneralLinearGroup.det (placeEmbed ℚ p x) = idl p (Matrix.GeneralLinearGroup.det x) := by
  refine Units.ext ?_
  show (finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p (x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))).det =
    ((1 : InfiniteAdeleRing ℚ),
      ((localUnit (𝓞 ℚ) ℚ p (Matrix.GeneralLinearGroup.det x) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ))
  refine Prod.ext ?_ ?_
  · show (adeleArch (𝓞 ℚ) ℚ) (finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p _)).det = 1
    rw [RingHom.map_det, mapMatrix_arch_finMat, Matrix.det_one]
  · show (adeleFin (𝓞 ℚ) ℚ) (finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p _)).det = _
    rw [RingHom.map_det, mapMatrix_fin_finMat]
    refine RestrictedProduct.ext _ _ fun w => ?_
    show (finAdeleEval (𝓞 ℚ) ℚ w) (localMat (𝓞 ℚ) ℚ p (x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).det =
      ((localUnit (𝓞 ℚ) ℚ p (Matrix.GeneralLinearGroup.det x) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) w
    rw [RingHom.map_det]
    by_cases hw : w = p
    · subst hw
      rw [mapMatrix_localMat_self, localUnit_apply_self]
      rfl
    · rw [mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ _ _ hw, Matrix.det_one, localUnit_apply_of_ne (𝓞 ℚ) ℚ _ _ hw]

def normIdl : (p.adicCompletion ℚ)ˣ →* ℝ where
  toFun t := ideleNorm ℚ (idl p t)
  map_one' := by
    rw [map_one]
    simp [ideleNorm]
  map_mul' a b := by rw [map_mul, ideleNorm_mul]

def normLoc : (p.adicCompletion ℚ)ˣ →* ℝ where
  toFun t := ‖(t : p.adicCompletion ℚ)‖
  map_one' := by rw [Units.val_one, norm_one]
  map_mul' a b := by rw [Units.val_mul, norm_mul]

theorem normIdl_apply (t : (p.adicCompletion ℚ)ˣ) : normIdl p t = ideleNorm ℚ (idl p t) := rfl
theorem normLoc_apply (t : (p.adicCompletion ℚ)ˣ) : normLoc p t = ‖(t : p.adicCompletion ℚ)‖ := rfl

theorem normIdl_of_valued_eq_one {u : (p.adicCompletion ℚ)ˣ} (hu : Valued.v (u : p.adicCompletion ℚ) = 1) :
    normIdl p u = 1 := by
  rw [normIdl_apply]
  refine ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ (idl p u) rfl ?_
  have hfin : AdeleRing.finitePartUnits (𝓞 ℚ) ℚ (idl p u) = localUnit (𝓞 ℚ) ℚ p u := Units.ext rfl
  rw [hfin, FiniteAdeleRing.mem_unitIdeles_iff]
  have hu' : Valued.v ((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have key : ∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 →
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
        ((localUnit (𝓞 ℚ) ℚ p t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w ∈
          w.adicCompletionIntegers ℚ := by
    intro t ht w
    by_cases hw : w = p
    · subst hw
      rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, ht]
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ _ _ hw]
      exact one_mem _
  refine ⟨key u hu, fun w => ?_⟩
  rw [← map_inv]
  exact key u⁻¹ hu' w

theorem normLoc_of_valued_eq_one {u : (p.adicCompletion ℚ)ˣ} (hu : Valued.v (u : p.adicCompletion ℚ) = 1) :
    normLoc p u = 1 := by
  rw [normLoc_apply, NumberField.FinitePlace.norm_def (K := ℚ) (v := p), hu, map_one, NNReal.coe_one]

theorem normIdl_uniformizerUnit :
    normIdl p (uniformizerUnit ℚ p) = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [normIdl_apply, ← uniformizerIdele_eq]
  exact ideleNorm_uniformizerIdele ℚ p

theorem normLoc_uniformizerUnit :
    normLoc p (uniformizerUnit ℚ p) = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [normLoc_apply, NumberField.FinitePlace.norm_def (K := ℚ) (v := p), valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have h1 : (WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0)).toAdd = -1 := by
    rw [show WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0) = Multiplicative.ofAdd (-1 : ℤ) from
      WithZero.unzero_coe _, toAdd_ofAdd]
  rw [h1, zpow_neg, zpow_one, NNReal.coe_inv]
  norm_cast

theorem exists_eq_mul_zpow (t : (p.adicCompletion ℚ)ˣ) :
    ∃ (u : (p.adicCompletion ℚ)ˣ) (a : ℤ), Valued.v (u : p.adicCompletion ℚ) = 1 ∧ t = u * uniformizerUnit ℚ p ^ a := by
  have ht0 : Valued.v (t : p.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 t.ne_zero
  set a : ℤ := Multiplicative.toAdd (WithZero.unzero ht0) with ha
  have hvt : Valued.v (t : p.adicCompletion ℚ) = WithZero.exp a := by
    rw [ha, WithZero.exp, ofAdd_toAdd, WithZero.coe_unzero]
  refine ⟨t * uniformizerUnit ℚ p ^ a, -a, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hvt, valued_uniformizerUnit,
      ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

theorem normIdl_eq_normLoc (t : (p.adicCompletion ℚ)ˣ) : normIdl p t = normLoc p t := by
  obtain ⟨u, a, hu, rfl⟩ := exists_eq_mul_zpow p t
  rw [map_mul, map_mul, map_zpow, map_zpow, normIdl_of_valued_eq_one p hu, normLoc_of_valued_eq_one p hu,
    normIdl_uniformizerUnit, normLoc_uniformizerUnit]

end Ws23NormAtP

end

open Ws23NormAtP IsDedekindDomain NumberField UnramifiedWhittaker NumberField.TateGlobal in

theorem solution (p : HeightOneSpectrum (𝓞 ℚ))
    (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p x)) =
      (LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det x : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) := by
  rw [det_placeEmbed, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm,
    ← normIdl_apply, ← normLoc_apply, normIdl_eq_normLoc]

end S_NumberField_TateGlobal_ideleNorm_det_placeEmbed
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_det_placeEmbed (solution)

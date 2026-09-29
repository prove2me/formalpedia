-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/5418fa12-bf06-53c1-b20a-45f24390ab0d

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

noncomputable section

set_option linter.unusedSectionVars false

p2m_open "ModularCurve~coeffMap_injective Polynomial IntermediateField"

namespace P2MKcIgusaIrr

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

abbrev FF : Type _ := ↥(modularFunctionFieldFullC K N)

def jF : FF K N := ⟨jqModC K, jqModC_mem_full K N⟩

def jNF : FF K N := ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩

@[scoped simp] theorem coe_jF : ((jF K N : FF K N) : LaurentSeries K) = jqModC K := rfl

@[scoped simp] theorem coe_jNF : ((jNF K N : FF K N) : LaurentSeries K) = jqNModC K N := rfl

abbrev Kj : IntermediateField K (FF K N) := K⟮jF K N⟯

set_option synthInstance.maxHeartbeats 1600000 in
scoped instance instAlgebraKj : Algebra K (Kj K N) := inferInstance
scoped instance instModuleKjFF : Module (Kj K N) (FF K N) := inferInstance
scoped instance instAlgebraKjFF : Algebra (Kj K N) (FF K N) := inferInstance
scoped instance instTowerKj : IsScalarTower K (Kj K N) (FF K N) := inferInstance

abbrev jKj : Kj K N := AdjoinSimple.gen K (jF K N)

abbrev PhiAt {N : ℕ} [NeZero N] (data : ModularPolynomialData N) {R : Type*} [CommRing R]
    (j₀ : R) : Polynomial R :=
  data.Φ.map (eval₂RingHom (Int.castRingHom R) j₀)

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  simpa using this

abbrev evalJ (R : Type*) [CommRing R] : Polynomial ℤ →+* LaurentSeries R :=
  eval₂RingHom (Int.castRingHom (LaurentSeries R)) (jqModC R)

theorem coeffMap_comp_evalJ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (coeffMap f).comp (evalJ R) = evalJ S := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [coeffMap_jqModC]

theorem eval₂_Phi_int (data : ModularPolynomialData N) :
    data.Φ.eval₂ (evalJ ℤ) (jqNModC ℤ N) = 0 := by
  apply coeffMap_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [Polynomial.hom_eval₂, coeffMap_comp_evalJ, coeffMap_jqNModC, map_zero]
  have hev : evalJ ℚ = evalAtJ :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [evalAtJ_X, jqModC_rat])
  rw [hev, jqNModC_rat]
  exact data.eval_eq_zero

theorem eval₂_Phi (data : ModularPolynomialData N) (R : Type*) [CommRing R] :
    data.Φ.eval₂ (evalJ R) (jqNModC R N) = 0 := by
  have h := congrArg (coeffMap (Int.castRingHom R)) (eval₂_Phi_int N data)
  rwa [Polynomial.hom_eval₂, coeffMap_comp_evalJ, coeffMap_jqNModC, map_zero] at h

theorem adjoin_pair_eq_top (hN : (N : K) ≠ 0) :
    IntermediateField.adjoin K {jF K N, jNF K N} = (⊤ : IntermediateField K (FF K N)) := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hlN : ¬ ℓ ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K ℓ N).2 h)
  have hCF := modularFunctionFieldC_eq_modularFunctionFieldFullC K ℓ N hlN
  apply IntermediateField.lift_injective
  refine (IntermediateField.lift_adjoin K _ _).trans
    (Eq.trans ?_ (IntermediateField.lift_top K _).symm)
  rw [Set.image_pair, coe_jF, coe_jNF, ← hCF]
  rfl

theorem adjoin_jNF_eq_top (hN : (N : K) ≠ 0) :
    (Kj K N)⟮jNF K N⟯ = (⊤ : IntermediateField (Kj K N) (FF K N)) := by
  apply restrictScalars_injective K
  rw [adjoin_simple_adjoin_simple, restrictScalars_top]
  exact adjoin_pair_eq_top K N hN

def adjoinEquivTop (hN : (N : K) ≠ 0) : (Kj K N)⟮jNF K N⟯ ≃ₐ[Kj K N] FF K N :=
  (equivOfEq (adjoin_jNF_eq_top K N hN)).trans topEquiv

theorem adjoinEquivTop_gen (hN : (N : K) ≠ 0) :
    adjoinEquivTop K N hN (AdjoinSimple.gen (Kj K N) (jNF K N)) = jNF K N := rfl

theorem transcendental_jF : Transcendental K (jF K N) := by
  rw [← transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (FF K N) (LaurentSeries K))]
  exact transcendental_jqModC K

abbrev PhiKj (data : ModularPolynomialData N) : Polynomial (Kj K N) := PhiAt data (jKj K N)

theorem monic_PhiKj (data : ModularPolynomialData N) : (PhiKj K N data).Monic := data.monic.map _

theorem natDegree_PhiKj (data : ModularPolynomialData N) :
    (PhiKj K N data).natDegree = dedekindPsi N := by
  rw [PhiKj, data.monic.natDegree_map, data.natDegree_eq]

theorem algebraMap_comp_eq_evalJ :
    (algebraMap (FF K N) (LaurentSeries K)).comp ((algebraMap (Kj K N) (FF K N)).comp
        (eval₂RingHom (Int.castRingHom (Kj K N)) (jKj K N))) = evalJ K := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X]
  rfl

theorem aeval_jNF_PhiKj (data : ModularPolynomialData N) : aeval (jNF K N) (PhiKj K N data) = 0 := by
  apply FaithfulSMul.algebraMap_injective (FF K N) (LaurentSeries K)
  rw [map_zero, PhiKj, aeval_def, eval₂_map, Polynomial.hom_eval₂, algebraMap_comp_eq_evalJ]
  exact eval₂_Phi N data K

theorem isIntegral_jNF (data : ModularPolynomialData N) : IsIntegral (Kj K N) (jNF K N) :=
  ⟨PhiKj K N data, monic_PhiKj K N data, by rw [← aeval_def]; exact aeval_jNF_PhiKj K N data⟩

theorem finrank_Kj_FF (hN : (N : K) ≠ 0) :
    Module.finrank (Kj K N) (FF K N) = dedekindPsi N :=
  finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN

theorem minpoly_jNF (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) :
    minpoly (Kj K N) (jNF K N) = PhiKj K N data := by
  have hint := isIntegral_jNF K N data
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
    (monic_PhiKj K N data) (minpoly.dvd _ _ (aeval_jNF_PhiKj K N data)) ?_).symm
  rw [natDegree_PhiKj, ← adjoin.finrank hint,
    (adjoinEquivTop K N hN).toLinearEquiv.finrank_eq, finrank_Kj_FF K N hN]

def phi0 : RatFunc K →ₐ[K] FF K N :=
  RatFunc.liftAlgHom (Polynomial.aeval (jF K N)) fun _ hp =>
    mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp
      (transcendental_iff_injective.1 (transcendental_jF K N) (h.trans (map_zero _).symm))

theorem phi0_algebraMap (p : K[X]) : phi0 K N (algebraMap K[X] (RatFunc K) p) = aeval (jF K N) p := by
  rw [phi0]
  exact RatFunc.liftRingHom_algebraMap _ _ p

theorem phi0_X : phi0 K N (algebraMap K[X] (RatFunc K) X) = jF K N := by
  rw [phi0_algebraMap, aeval_X]

theorem fieldRange_phi0 : (phi0 K N).fieldRange = Kj K N := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    change phi0 K N f ∈ Kj K N
    rw [phi0, RatFunc.liftAlgHom_apply]
    refine div_mem ?_ ?_ <;>
      exact algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K _)
  · rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨_, phi0_X K N⟩

def ratFuncEquiv : RatFunc K ≃ₐ[K] Kj K N :=
  (AlgEquiv.ofInjectiveField (phi0 K N)).trans (equivOfEq (fieldRange_phi0 K N))

theorem ratFuncEquiv_apply_coe (f : RatFunc K) : ((ratFuncEquiv K N f : Kj K N) : FF K N) = phi0 K N f :=
  rfl

theorem ratFuncEquiv_X : ratFuncEquiv K N (algebraMap K[X] (RatFunc K) X) = jKj K N := by
  ext1
  rw [ratFuncEquiv_apply_coe, phi0_X]
  rfl

end P2MKcIgusaIrr
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero.P2MKcIgusaIrr"

open P2MKcIgusaIrr in
theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hNK : (N : K) ≠ 0) :
    Irreducible ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))) := by
  have hirr : Irreducible (PhiKj K N data) := by
    rw [← minpoly_jNF K N hNK data]
    exact minpoly.irreducible (isIntegral_jNF K N data)
  set e := ratFuncEquiv K N
  rw [← MulEquiv.irreducible_iff (Polynomial.mapEquiv (e : RatFunc K ≃+* Kj K N))]
  convert hirr using 1
  rw [Polynomial.mapEquiv_apply, Polynomial.map_map, Polynomial.map_map]
  refine congrArg (fun f => data.Φ.map f) (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, coe_eval₂RingHom, eval₂_X]
  exact ratFuncEquiv_X K N

end
end S_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero (solution)

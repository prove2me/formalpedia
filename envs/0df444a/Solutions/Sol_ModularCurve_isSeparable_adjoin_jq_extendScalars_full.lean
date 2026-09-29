-- Prove2me | solution 1 for ModularCurve.isSeparable_adjoin_jq_extendScalars_full
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/47debe0b-19a2-55ef-a804-1d90f09652f3

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isSeparable_adjoin_jq_extendScalars_full
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve

namespace BFall

open IntermediateField Polynomial

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) =
      algebraMap L (LaurentSeries L) (algebraMap ℚ L r) := by
  rw [ModularCurve.algebraMap_apply_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
    coeffMap_single]

theorem laurentBaseChange_full_eq_adjoin (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) :
    laurentBaseChange L (modularFunctionFieldFull N) =
      IntermediateField.adjoin L (⇑(coeffEmb L) '' divisorExpansions N) := by
  apply le_antisymm
  · rw [laurentBaseChange, adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ (modularFunctionFieldFull N).toSubfield := hx
    rw [modularFunctionFieldFull, adjoin_toSubfield] at hx'
    have hmem : coeffEmb L x ∈ (Subfield.closure
        (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N)).map (coeffEmb L) :=
      ⟨x, hx', rfl⟩
    rw [RingHom.map_field_closure] at hmem
    refine (Subfield.closure_le.2 ?_) hmem
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨r, rfl⟩ | hy
    · rw [coeffEmb_algebraMap]
      exact (IntermediateField.adjoin L _).algebraMap_mem _
    · exact IntermediateField.subset_adjoin L _ ⟨y, hy, rfl⟩
  · rw [adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (IntermediateField.subset_adjoin ℚ _ hy)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in

theorem finiteDimensional_adjoin_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (hjq : jq ∈ modularFunctionFieldFull N) :
    FiniteDimensional
      (IntermediateField.adjoin L
        ({⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L hjq⟩} :
          Set (laurentBaseChange L (modularFunctionFieldFull N))))
      (laurentBaseChange L (modularFunctionFieldFull N)) := by
  classical

  let ι : Type := {d : ℕ // d ∣ N ∧ d ≠ 0}
  haveI : Finite ι := by
    refine Finite.of_injective (fun d : ι => (⟨d.1, ?_⟩ : Fin (N + 1))) ?_
    · exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) d.2.1)
    · intro d d' h
      exact Subtype.ext (by simpa using congrArg Fin.val h)

  let g : ι → laurentBaseChange L (modularFunctionFieldFull N) := fun d =>
    haveI : NeZero d.1 := ⟨d.2.2⟩
    ⟨coeffEmb L (qExpand ℚ d.1 jq), coeffEmb_mem_laurentBaseChange L (jqd_mem_full N d.2.1)⟩
  have hgval : ∀ d : ι, ((g d : laurentBaseChange L (modularFunctionFieldFull N)) : LaurentSeries L) =
      haveI : NeZero d.1 := ⟨d.2.2⟩; coeffEmb L (qExpand ℚ d.1 jq) := fun d => rfl

  let J : laurentBaseChange L (modularFunctionFieldFull N) :=
    ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L hjq⟩

  have hint : ∀ d : ι, IsIntegral
      (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N)))) (g d) := by
    rintro ⟨d, hdvd, hd0⟩
    haveI : NeZero d := ⟨hd0⟩
    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData d
    let J' : IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))) :=
      ⟨J, IntermediateField.mem_adjoin_simple_self L J⟩
    let ψ : Polynomial ℤ →+*
        IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))) :=
      Polynomial.eval₂RingHom (Int.castRingHom _) J'
    refine ⟨data.Φ.map ψ, data.monic.map ψ, ?_⟩
    have hv : Function.Injective
        (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L)) :=
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L)).injective
    apply hv
    have hcomp : ((algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L)).comp
        (algebraMap (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
          (laurentBaseChange L (modularFunctionFieldFull N)))).comp ψ =
        (coeffEmb L).comp evalAtJ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X]
      show (algebraMap _ (LaurentSeries L)) (algebraMap _ _ (Polynomial.eval₂ (Int.castRingHom _) J' X)) =
        coeffEmb L jq
      rw [Polynomial.eval₂_X]
      rfl
    rw [map_zero, Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
    show Polynomial.eval₂ ((coeffEmb L).comp evalAtJ) (coeffEmb L (qExpand ℚ d jq)) data.Φ = 0
    rw [← Polynomial.hom_eval₂]
    have h0 : Polynomial.eval₂ evalAtJ (qExpand ℚ d jq) data.Φ = 0 := data.eval_eq_zero
    rw [h0, map_zero]

  have hgen : IntermediateField.adjoin
      (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
      (Set.range g) = ⊤ := by
    apply IntermediateField.restrictScalars_injective L
    rw [IntermediateField.restrictScalars_top, IntermediateField.adjoin_adjoin_left]
    apply IntermediateField.lift_injective
    erw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    · conv_lhs => rw [laurentBaseChange_full_eq_adjoin]
      rw [adjoin_le_iff]
      rintro _ ⟨x, ⟨d, hd0, hdvd, rfl⟩, rfl⟩
      apply IntermediateField.subset_adjoin
      refine ⟨g ⟨d, hdvd, hd0.ne⟩, Or.inr ⟨⟨d, hdvd, hd0.ne⟩, rfl⟩, ?_⟩
      rfl

  have hfin : FiniteDimensional
      (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
      (IntermediateField.adjoin
        (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
        (Set.range g)) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨d, rfl⟩ := hy
      exact hint d
  rw [hgen] at hfin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv :
      (⊤ : IntermediateField
        (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
        (laurentBaseChange L (modularFunctionFieldFull N))) ≃ₐ[_]
        laurentBaseChange L (modularFunctionFieldFull N)).toLinearEquiv

end BFall

open ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N M : ℕ) [NeZero N] [NeZero M] (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull M)) : Algebra.IsSeparable (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (IntermediateField.extendScalars hle))) (IntermediateField.extendScalars hle) := by
  haveI hfd := BFall.finiteDimensional_adjoin_coeffEmb_jq L M (jq_mem_full M)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (IntermediateField.extendScalars hle))) :=
    charZero_of_injective_algebraMap (algebraMap L _).injective
  haveI : PerfectField (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (IntermediateField.extendScalars hle))) :=
    PerfectField.ofCharZero
  haveI : FiniteDimensional (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (IntermediateField.extendScalars hle))) (IntermediateField.extendScalars hle) := by
    exact hfd
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin L ({algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (IntermediateField.extendScalars hle))) (IntermediateField.extendScalars hle) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end S_ModularCurve_isSeparable_adjoin_jq_extendScalars_full
end P2MW
export P2MW.S_ModularCurve_isSeparable_adjoin_jq_extendScalars_full (solution)

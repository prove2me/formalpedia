-- Prove2me | solution 1 for ModularCurve.FullLevel.ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9a696086-80d0-5521-846a-daeb96e4702f

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup AlgebraicCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (J : ↥(fieldBar q M'))
    (hJ : ((J : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) q)
    (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))
    (hP : 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))) :
    0 ≤ P.ord (J : ↥(fieldBar q M')) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set jF : ↥(fieldBar q M') := IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) with hjF
  have hjFcoe : ((jF : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := rfl

  have hjq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
    ext k
    rw [coeffEmb_coeff, ← jqModC_rat, jqModC_eq_map_intCast (AlgebraicClosure ℚ), jqModC_eq_map_intCast ℚ,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    simp
  have hexp : ∀ f : LaurentSeries ℚ, coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q f) =
      qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) f) := by
    intro f; ext k
    by_cases hk : (q : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hk
      rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
    · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd q _ hk, qExpand_coeff_of_not_dvd q _ hk, map_zero]
  have hJcoe : ((J : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (jqN q) := by
    rw [hJ, show jqNModC (AlgebraicClosure ℚ) q = qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) from rfl,
      show jqN q = qExpand ℚ q jq from rfl, hexp, hjq]

  obtain ⟨data, -⟩ := ModularCurve.exists_modularPolynomialData_evalSymm q
  have hJ0 : (J : ↥(fieldBar q M')) ≠ 0 := by
    intro h
    have : ((J : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [h]; rfl
    rw [hJ] at this
    exact jqNModC_ne_zero (AlgebraicClosure ℚ) q this
  have hjF0 : jF ≠ 0 := by
    intro h
    have : ((jF : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [h]; rfl
    rw [hjFcoe, hjq] at this
    exact jqModC_ne_zero_def (AlgebraicClosure ℚ) this
  have hjV : jF ∈ P.toValuationSubring := P.mem_of_ord_nonneg hjF0 hP

  let φ : Polynomial ℤ →+* ↥P.toValuationSubring := (Polynomial.aeval (R := ℤ) (⟨jF, hjV⟩ : ↥P.toValuationSubring)).toRingHom

  let ι : ↥(fieldBar q M') →+* LaurentSeries (AlgebraicClosure ℚ) := (fieldBar q M').toSubalgebra.val.toRingHom
  have hι : ∀ f : ↥(fieldBar q M'), ι f = (f : LaurentSeries (AlgebraicClosure ℚ)) := fun f => rfl
  have hcomp : (ι.comp ((algebraMap ↥P.toValuationSubring ↥(fieldBar q M')).comp φ)) =
      (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro n; simp
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X]
      simp [φ, hι, hjFcoe]
  have key : ι (Polynomial.eval₂ ((algebraMap ↥P.toValuationSubring ↥(fieldBar q M')).comp φ) (J : ↥(fieldBar q M')) data.Φ) = 0 := by
    rw [Polynomial.hom_eval₂, hcomp, hι, hJcoe, ← Polynomial.hom_eval₂, data.eval_eq_zero, map_zero]
  have heval : Polynomial.eval₂ (algebraMap ↥P.toValuationSubring ↥(fieldBar q M')) (J : ↥(fieldBar q M')) (data.Φ.map φ) = 0 := by
    rw [Polynomial.eval₂_map]
    exact Subtype.ext (by rw [← hι]; exact key)
  have hint : IsIntegral ↥P.toValuationSubring (J : ↥(fieldBar q M')) := ⟨data.Φ.map φ, data.monic.map φ, heval⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥P.toValuationSubring) (K := ↥(fieldBar q M'))).mp hint
  have hJV : (J : ↥(fieldBar q M')) ∈ P.toValuationSubring := by rw [← hy]; exact y.2
  exact P.ord_nonneg_of_mem hJV

end S_ModularCurve_FullLevel_ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
end P2MW
export P2MW.S_ModularCurve_FullLevel_ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC (solution)

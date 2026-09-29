-- Prove2me | solution 1 for ModularCurve.mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/60d52e3b-60fa-500e-b7f0-2162aaed7404

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqModC_rat map_jqModC qExpand qExpand_one_apply jq jqN ModularPolynomialData coeffEmb nonempty_modularPolynomialData ModularPolynomialData.evalSymm_of_one_lt coeffEmb_qExpand"
namespace JInt
p2m_open "ModularCurve"

open Polynomial

theorem aeval_toRingHom_comp {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T) (s : S) :
    g.comp (Polynomial.aeval (R := ℤ) s).toRingHom = (Polynomial.aeval (R := ℤ) (g s)).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => by simp) ?_
  simp

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ L)

theorem main (L : Type*) [Field L] [Algebra ℚ L] (ℓ : ℕ) [NeZero ℓ]
    (F : IntermediateField L (LaurentSeries L)) (P : AlgebraicCurve.Place L F) (x y : F)
    (hx : (x : LaurentSeries L) = jqModC L)
    (hy : (y : LaurentSeries L) = qExpand L ℓ (jqModC L))
    (hyP : y ∈ P.toValuationSubring) : x ∈ P.toValuationSubring := by
  classical
  by_cases h1 : ℓ = 1
  · subst h1
    have : x = y := by
      apply Subtype.ext
      change (x : LaurentSeries L) = (y : LaurentSeries L)
      rw [hx, hy, qExpand_one_apply]
    rw [this]; exact hyP
  have hℓ : 1 < ℓ := lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne ℓ)) (Ne.symm h1)
  obtain ⟨data⟩ := nonempty_modularPolynomialData ℓ
  have hsym := ModularPolynomialData.evalSymm_of_one_lt ℓ hℓ data

  have h0 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN ℓ)).toRingHom jq = 0 := by
    rw [← hsym jq (jqN ℓ)]
    exact data.eval_eq_zero

  have e1 : (coeffEmb L).comp (Polynomial.aeval (R := ℤ) (jqN ℓ)).toRingHom =
      (Polynomial.aeval (R := ℤ) (y : LaurentSeries L)).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => by simp) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X]
    rw [jqN, coeffEmb_qExpand L ℓ jq, coeffEmb_jq, hy]
  have hL : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (y : LaurentSeries L)).toRingHom
      (x : LaurentSeries L) = 0 := by
    have := congrArg (coeffEmb L) h0
    rw [map_zero, Polynomial.hom_eval₂, e1, coeffEmb_jq, ← hx] at this
    exact this

  have e2 : (algebraMap F (LaurentSeries L)).comp (Polynomial.aeval (R := ℤ) y).toRingHom =
      (Polynomial.aeval (R := ℤ) (y : LaurentSeries L)).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => by simp) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X]
    rfl
  have hF : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x = 0 := by
    have hinj : Function.Injective (algebraMap F (LaurentSeries L)) :=
      (algebraMap F (LaurentSeries L)).injective
    apply hinj
    rw [map_zero, Polynomial.hom_eval₂, e2]
    exact hL

  set O : Subring F := P.toValuationSubring.valuation.integer with hO
  have hyO : y ∈ O := by rw [hO, ValuationSubring.integer_valuation]; exact hyP
  have e3 : (algebraMap O F).comp (Polynomial.aeval (R := ℤ) (⟨y, hyO⟩ : O)).toRingHom =
      (Polynomial.aeval (R := ℤ) y).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => by simp) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X]
    rfl
  have hint : IsIntegral O x := by
    refine ⟨data.Φ.map (Polynomial.aeval (R := ℤ) (⟨y, hyO⟩ : O)).toRingHom, data.monic.map _, ?_⟩
    rw [Polynomial.eval₂_map, e3]
    exact hF
  have hmem := (Valuation.integer.integers P.toValuationSubring.valuation).mem_of_integral hint
  rw [ValuationSubring.integer_valuation] at hmem
  exact hmem

end ModularCurve.JInt

end

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (ℓ : ℕ) [NeZero ℓ]
    (F : IntermediateField L (LaurentSeries L)) (P : AlgebraicCurve.Place L F) (x y : F)
    (hx : (x : LaurentSeries L) = ModularCurve.jqModC L)
    (hy : (y : LaurentSeries L) = ModularCurve.qExpand L ℓ (ModularCurve.jqModC L))
    (hyP : y ∈ P.toValuationSubring) : x ∈ P.toValuationSubring :=
  ModularCurve.JInt.main L ℓ F P x y hx hy hyP

end S_ModularCurve_mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem
end P2MW
export P2MW.S_ModularCurve_mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem (solution)

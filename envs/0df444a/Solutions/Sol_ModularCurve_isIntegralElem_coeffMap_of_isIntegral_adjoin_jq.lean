-- Prove2me | solution 1 for ModularCurve.isIntegralElem_coeffMap_of_isIntegral_adjoin_jq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bc13d8af-37a4-55c9-b7bc-03693bf49a5c

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegralElem_coeffMap_of_isIntegral_adjoin_jq

open ModularCurve

private lemma coeffMap_intCast_injective_s18 :
    Function.Injective (ModularCurve.coeffMap (Int.castRingHom ℚ) : LaurentSeries ℤ →+* LaurentSeries ℚ) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries ℚ => z.coeff k) h
  simp only [ModularCurve.coeffMap_coeff, eq_intCast] at this
  exact_mod_cast this

private lemma jq_eq_coeffMap_s18 :
    ModularCurve.jq = ModularCurve.coeffMap (Int.castRingHom ℚ) (ModularCurve.jqModC ℤ) := by
  rw [← ModularCurve.jqModC_rat, ModularCurve.jqModC_eq_map_intCast]
  rfl

theorem solution (y : LaurentSeries ℚ)
    (hy : IsIntegral (Algebra.adjoin ℤ ({ModularCurve.jq} : Set (LaurentSeries ℚ))) y) :
    (ModularCurve.coeffMap (Int.castRingHom ℚ)).IsIntegralElem y := by
  set φ : LaurentSeries ℤ →+* LaurentSeries ℚ := ModularCurve.coeffMap (Int.castRingHom ℚ) with hφ
  set A : Subalgebra ℤ (LaurentSeries ℚ) := Algebra.adjoin ℤ ({ModularCurve.jq} : Set (LaurentSeries ℚ)) with hA

  let B : Subalgebra ℤ (LaurentSeries ℚ) :=
    { φ.range with
      algebraMap_mem' := fun r => by
        refine ⟨(r : LaurentSeries ℤ), ?_⟩
        rw [eq_intCast (algebraMap ℤ (LaurentSeries ℚ)) r, map_intCast] }
  have hAB : A ≤ B := by
    refine Algebra.adjoin_le ?_
    rintro _ rfl
    exact ⟨ModularCurve.jqModC ℤ, jq_eq_coeffMap_s18.symm⟩
  have hle : A.toSubring ≤ φ.range := fun x hx => hAB hx

  have hbij : Function.Bijective φ.rangeRestrict :=
    ⟨fun a b h => coeffMap_intCast_injective_s18 (by simpa using congrArg Subtype.val h),
      φ.rangeRestrict_surjective⟩
  let e : LaurentSeries ℤ ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict hbij
  let h : A →+* LaurentSeries ℤ := e.symm.toRingHom.comp (Subring.inclusion hle)
  have h3 : ∀ z : φ.range, φ (e.symm z) = (z : LaurentSeries ℚ) := fun z =>
    calc φ (e.symm z) = ((e (e.symm z) : φ.range) : LaurentSeries ℚ) := rfl
      _ = (z : LaurentSeries ℚ) := by rw [e.apply_symm_apply]
  have hcomp : φ.comp h = (algebraMap A (LaurentSeries ℚ) : A →+* LaurentSeries ℚ) :=
    RingHom.ext fun a => by
      simp only [h, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      exact h3 _
  obtain ⟨p, hpm, hp⟩ := hy
  refine ⟨p.map h, hpm.map h, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact hp

end S_ModularCurve_isIntegralElem_coeffMap_of_isIntegral_adjoin_jq
end P2MW
export P2MW.S_ModularCurve_isIntegralElem_coeffMap_of_isIntegral_adjoin_jq (solution)

-- Prove2me | solution 1 for N25.U25_complex_ord_eq_zero_of_j_mem
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:59.703256+00:00
-- url     : https://prove2.me/submissions/74b66bd5-6ac4-407e-8aa8-94dba14d1abf

import Mathlib
import Theorems.Thm_N25_coe_U25C
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_N25_GammaH25_finiteIndex
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Theorems.Thm_N25_unitAnalytic25_realizeOf
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_N25_unitAnalytic25_mdifferentiable
import Theorems.Thm_N25_unitAnalytic25_ne_zero
import Theorems.Thm_N25_U25C_ne_zero
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

open UpperHalfPlane ModularCurve AlgebraicCurve

open scoped MatrixGroups Manifold

namespace N25

/-- Every place where j is regular has zero order on the literal unpowered unit. -/
theorem _root_.solution (i : Fin 5)
    (x : laurentBaseChange ℂ (xHFunctionField 25 N25.H25))
    (hx : (x : LaurentSeries ℂ) = unitSeries25 ℂ i)
    (P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)))
    (j : laurentBaseChange ℂ (xHFunctionField 25 N25.H25))
    (hj : (j : LaurentSeries ℂ) = jqModC ℂ) (hP : j ∈ P.toValuationSubring) :
    P.ord x = 0 := by
  let Γ := CohCarrier.GammaH 25 N25.H25
  letI : Γ.FiniteIndex := GammaH25_finiteIndex
  obtain ⟨D⟩ := exists_complexPlaceDictionaryOf Γ (translation_mem_GammaH 25 N25.H25)
    (xHFunctionField 25 N25.H25) rfl
  obtain ⟨τ, rfl⟩ := ComplexPlaceDictionaryOf.exists_pt_eq_of_mem Γ
    (translation_mem_GammaH 25 N25.H25) (xHFunctionField 25 N25.H25) rfl D P j hj hP
  have hx0 : x ≠ 0 := by
    intro h
    have hz : unitSeries25 ℂ i = 0 := by simpa [h] using hx.symm
    exact U25C_ne_zero ℂ i (Subtype.ext ((coe_U25C ℂ i).trans hz))
  have he : (fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z)) =
      unitAnalytic25 i ∘ ofComplex := by
    funext z
    rw [hx]
    exact unitAnalytic25_realizeOf i (ofComplex z)
  have ha : AnalyticAt ℂ (unitAnalytic25 i ∘ ofComplex) (τ : ℂ) :=
    (UpperHalfPlane.mdifferentiable_iff.mp (unitAnalytic25_mdifferentiable i)).analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have ho : meromorphicOrderAt (unitAnalytic25 i ∘ ofComplex) (τ : ℂ) = 0 :=
    by
      rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr
        (by simpa using unitAnalytic25_ne_zero i τ)]
      rfl
  have hm := D.meromorphicOrderAt_realizeOf τ x hx0
  rw [he, ho] at hm
  have hmul : (D.ramification τ : ℤ) * (D.pt τ).ord x = 0 := by
    exact_mod_cast hm.symm
  exact (mul_eq_zero.mp hmul).resolve_left
    (by exact_mod_cast (Nat.ne_of_gt (D.ramification_pos τ)))

end N25

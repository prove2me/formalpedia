-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:31:53.442176+00:00
-- url     : https://prove2.me/submissions/6ecf7094-b493-4f1d-931f-fabb6fdce913
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_arbitrary_power_euler_quadratic
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_power_H2_linear_bound
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H0_finite

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

private lemma surface_euler_expansion_aux (S : Surface) (M : S.scheme.Modules) :
    eulerCharacteristic S.structureMap 2 M =
      (cohomologyDimension S.structureMap M 0 : ℤ) -
      (cohomologyDimension S.structureMap M 1 : ℤ) +
      (cohomologyDimension S.structureMap M 2 : ℤ) := by
  simp [eulerCharacteristic, Finset.sum_range_succ, sub_eq_add_neg]

private lemma quadratic_lower_eventually_pos_aux (q l c : ℤ) (hq : 0 < q) (B : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      0 < (n : ℤ)*((n : ℤ)-1)*q + 2*(n : ℤ)*l + 2*c - 2*B := by
  let N := (2*|l|+2*|c|+2*(B : ℤ)+3).toNat
  have hN : (N : ℤ) = 2*|l|+2*|c|+2*(B : ℤ)+3 := Int.toNat_of_nonneg (by positivity)
  refine ⟨N,?_,fun n hn => ?_⟩
  · have : (0 : ℤ) < N := by rw [hN]; positivity
    exact_mod_cast this
  · have hn' : (N : ℤ) ≤ n := by exact_mod_cast hn
    rw [hN] at hn'
    have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    have hB : (0 : ℤ) ≤ B := Nat.cast_nonneg B
    have hq' : 1 ≤ q := hq
    have hbase : 0 ≤ (n : ℤ)*((n : ℤ)-1) := mul_nonneg hn0 (by omega)
    have hmul := mul_le_mul_of_nonneg_left hq' hbase
    have hl := neg_abs_le l
    have hc := neg_abs_le c
    have hlmul := mul_le_mul_of_nonneg_left hl
      (show (0 : ℤ) ≤ 2 * (n : ℤ) by positivity)
    have habsl := abs_nonneg l
    have habsc := abs_nonneg c
    nlinarith

end
end MaximalSeshadri.Geometry
end
end OAI

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open OAI.MaximalSeshadri.Frames OAI.MaximalSeshadri.Projective
open OAI.MaximalSeshadri.Geometry

theorem solution (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hq : 0 < selfIntersection S M) (hm : 0 ≤ mixedEuler S L M) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ s : O S.scheme ⟶ (M.pow n).sheaf, s ≠ 0 := by
  obtain ⟨B,C,hB⟩ := S.power_H2_linear_bound L hL M hm
  obtain ⟨N,hN,hpos⟩ := quadratic_lower_eventually_pos_aux (selfIntersection S M)
    (eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (O S.scheme) - C)
    (eulerCharacteristic S.structureMap 2 (O S.scheme)) hq B
  refine ⟨N,hN,fun n hn => ?_⟩
  have hd : 0 < cohomologyDimension S.structureMap (M.pow n).sheaf 0 := by
    have hp := hpos n hn
    have he := S.arbitrary_power_euler_quadratic L hL M n
    rw [surface_euler_expansion_aux] at he
    have hb : (cohomologyDimension S.structureMap (M.pow n).sheaf 2 : ℤ) ≤
        B+(C:ℤ)*n := by exact_mod_cast hB n
    have hi : (0 : ℤ) ≤ cohomologyDimension S.structureMap (M.pow n).sheaf 1 := Nat.cast_nonneg _
    have H : (0 : ℤ) < 2*(cohomologyDimension S.structureMap (M.pow n).sheaf 0 : ℤ) := by
      nlinarith
    exact_mod_cast (by omega : (0 : ℤ) < cohomologyDimension S.structureMap (M.pow n).sheaf 0)
  let := Module.compHom (cohomology (M.pow n).sheaf 0) (baseScalars S.structureMap)
  let := S.H0_finite L hL (M.pow n)
  let : Nontrivial (cohomology (M.pow n).sheaf 0) := Module.finrank_pos_iff.mp hd
  obtain ⟨x,hx⟩ := exists_ne (0 : cohomology (M.pow n).sheaf 0)
  refine ⟨Ext.homEquiv₀ x,?_⟩
  intro hs
  apply hx
  have he := congrArg Ext.mk₀ hs
  exact (Ext.mk₀_homEquiv₀_apply x).symm.trans (he.trans (Ext.mk₀_zero _ _))

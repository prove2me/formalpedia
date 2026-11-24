-- Prove2me | solution 1 for GlobalTheory.TorusConst.exists_elim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:05.888939+00:00
-- url     : https://prove2.me/submissions/c3924f7f-e494-46a2-92ce-f6b404ecf695

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
namespace GlobalTheory.TorusConst
theorem _root_.solution {R L : Type} [CommRing R] [Field L] (e : R →+* L) (a b : R[X])
    (ha : a.map e = 1) (hb : b.map e = 1) :
    ∃ g : R, e g ≠ 0 ∧ ∀ (A : Type) [Field A] (c : R →+* A) (x : A), eval₂ c x a = 0 →
      (x ≠ 0 → eval₂ c x⁻¹ b = 0) → c g = 0 := by
  let n := b.natDegree
  let h : R[X] := X * reflect n b
  have hh : h.natDegree ≤ n + 1 := by
    refine natDegree_mul_le.trans ?_
    have h1 : (reflect n b).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
    have h2 : (X : R[X]).natDegree ≤ 1 := natDegree_X_le
    omega
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant a h (m := a.natDegree) (n := n + 1)
    le_rfl hh (Or.inr (by omega))
  refine ⟨resultant a h a.natDegree (n + 1), ?_, fun A _ c x h1 h2 => ?_⟩
  · rw [← resultant_map_map, ha, resultant_one_left]
    have : h.map e = X ^ (n + 1) := by
      rw [Polynomial.map_mul, ← reflect_map, hb, reflect_one, map_X, pow_succ']
    simp [this]
  · have h3 : eval₂ c x h = 0 := by
      rw [eval₂_mul, eval₂_X]
      by_cases hx : x = 0
      · simp [hx]
      · letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
        have := (eval₂_reflect_eq_zero_iff c x⁻¹ n b le_rfl).2 (h2 hx)
        rw [invOf_eq_inv, inv_inv] at this
        rw [this, mul_zero]
    have := congrArg (eval₂ c x) hpq
    rw [eval₂_add, eval₂_mul, eval₂_mul, h1, h3, eval₂_C] at this
    simpa using this.symm
end GlobalTheory.TorusConst

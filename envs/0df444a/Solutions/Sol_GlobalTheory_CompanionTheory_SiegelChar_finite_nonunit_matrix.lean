-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelChar.finite_nonunit_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:34.684396+00:00
-- url     : https://prove2.me/submissions/1e66f18e-08f8-4c96-9d75-3e37f23f90bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelChar
namespace GlobalTheory.CompanionTheory.SiegelChar
theorem _root_.solution {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    {β : Type} [Fintype β] [DecidableEq β] (A B D : Matrix β β E) (τ : E) (h : IsUnit (A + τ • B + (τ * τ) • D)) :
    {t : F | ¬ IsUnit (A + algebraMap F E t • B + (algebraMap F E t * algebraMap F E t) • D)}.Finite := by
  classical
  set P : Matrix β β (Polynomial E) := A.map Polynomial.C + (Polynomial.X : Polynomial E) • B.map Polynomial.C
      + ((Polynomial.X : Polynomial E) * Polynomial.X) • D.map Polynomial.C with hP
  have hev : ∀ z : E, P.det.eval z = (A + z • B + (z * z) • D).det := by
    intro z
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [hP, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply] <;> ring
  refine (finite_nonunit (F := F) P.det τ ?_).subset ?_
  · rw [hev]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h
  · intro t ht
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [hev]
    exact fun hu => ht ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
end GlobalTheory.CompanionTheory.SiegelChar

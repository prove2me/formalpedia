-- Prove2me | solution 1 for GlobalTheory.IntegralTrace.exists_monic_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:52:08.521601+00:00
-- url     : https://prove2.me/submissions/09727772-b706-4e93-9751-a198bd4d6eba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicAevalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.IntegralTrace
open Polynomial
namespace GlobalTheory.IntegralTrace
theorem _root_.solution {R E : Type*} [CommRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hL : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) :
    ∃ p : R[X], p.Monic ∧ aeval M (p.map (algebraMap R E)) = 0 := by
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  let g : Module.End R (Fin n → E) := (Matrix.toLin' M).restrictScalars R
  have hg : ∀ x ∈ L, g x ∈ L := fun x hx => by simpa [g] using hM x hx
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero R (g.restrict hg)
  refine ⟨p, hp, ?_⟩
  have key : ∀ (q : R[X]) (x : L), ((aeval (g.restrict hg) q x : L) : Fin n → E)
      = (aeval M (q.map (algebraMap R E))).mulVec x := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    | add a b ha hb =>
      intro x
      simp only [map_add, Polynomial.map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb,
        Matrix.add_mulVec]
    | monomial k a ih =>
      intro x
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.map_mul, map_mul (aeval M), Module.End.mul_apply,
        ih,
        Polynomial.map_X, aeval_X, aeval_X, ← Matrix.mulVec_mulVec]
      rfl
  apply Matrix.toLin'.injective
  rw [map_zero]
  apply LinearMap.ext_on hspan
  intro x hx
  have := key p ⟨x, hx⟩
  rw [hp0] at this
  simpa using this.symm
end GlobalTheory.IntegralTrace

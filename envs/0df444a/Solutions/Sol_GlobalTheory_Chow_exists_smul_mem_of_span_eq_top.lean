-- Prove2me | solution 1 for GlobalTheory.Chow.exists_smul_mem_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:48.965993+00:00
-- url     : https://prove2.me/submissions/aa53df1a-2e0e-4ce8-90dd-810274c24699

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.Chow
theorem _root_.solution {R Ω n : Type*} [CommRing R] [Field Ω] [Finite n]
    (φ : R →+* Ω) (S : Submodule R (n → R))
    (h : Submodule.span Ω ((fun v : n → R => φ ∘ v) '' S) = ⊤) :
    ∃ r, φ r ≠ 0 ∧ ∀ w, r • w ∈ S := by
  classical
  cases nonempty_fintype n
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent Ω ((fun v : n → R => φ ∘ v) '' S)
  let B : Module.Basis b Ω (n → Ω) := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, h])
  let e : n ≃ b := (Pi.basisFun Ω n).indexEquiv B
  choose v hv hv' using fun k : n => hb (e k).2
  let A : Matrix n n R := Matrix.of v
  have hA : IsUnit (φ.mapMatrix A) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    have : (φ.mapMatrix A).row = Subtype.val ∘ e := funext fun k => hv' k
    rw [this]
    exact hli.comp _ e.injective
  refine ⟨A.det, ?_, fun w => ?_⟩
  · rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hA).ne_zero
  · have : A.det • w = Matrix.vecMul (Matrix.vecMul w A.adjugate) A := by
      rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [this, Matrix.vecMul_eq_sum]
    exact S.sum_mem fun k _ => S.smul_mem _ (hv k)
end GlobalTheory.Chow

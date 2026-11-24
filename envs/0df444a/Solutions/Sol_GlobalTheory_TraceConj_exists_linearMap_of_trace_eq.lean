-- Prove2me | solution 1 for GlobalTheory.TraceConj.exists_linearMap_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:15.808961+00:00
-- url     : https://prove2.me/submissions/fda5258b-f064-41d0-8e8d-73e38123b2d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlIntertwinerOfResidualSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLinearMapOfTraceEq
import Theorems.Thm_GlobalTheory_TraceConj_ker_le_ker_of_trace_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceConj
open IsLocalRing
namespace GlobalTheory.TraceConj
theorem _root_.solution {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hM : Submodule.span R (Set.range M) = ⊤) (hN : Submodule.span R (Set.range N) = ⊤) :
    ∃ φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R, φ 1 = 1 ∧ ∀ g X, φ (M g * X) = N g * φ X := by
  classical
  let a := Finsupp.linearCombination R (fun g => M g)
  let b := Finsupp.linearCombination R (fun g => N g)
  have hker : LinearMap.ker a ≤ LinearMap.ker b := ker_le_ker_of_trace_eq M N h hN
  have ha : Function.Surjective a := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]; exact hM
  let φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R :=
    ((LinearMap.ker a).liftQ b hker).comp (a.quotKerEquivOfSurjective ha).symm.toLinearMap
  have hφ : ∀ c, φ (a c) = b c := fun c => by
    have : a c = a.quotKerEquivOfSurjective ha (Submodule.Quotient.mk c) := rfl
    rw [this]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hφg : ∀ g, φ (M g) = N g := fun g => by
    simpa [a, b] using hφ (Finsupp.single g 1)
  refine ⟨φ, by simpa using hφg 1, fun g X => ?_⟩
  have hX : X ∈ Submodule.span R (Set.range M) := hM ▸ Submodule.mem_top
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨g', rfl⟩ := hX; rw [← map_mul, hφg, hφg, map_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, map_add, mul_add, hx, hy]
  | smul t x _ hx => rw [Matrix.mul_smul, map_smul, map_smul, Matrix.mul_smul, hx]
end GlobalTheory.TraceConj

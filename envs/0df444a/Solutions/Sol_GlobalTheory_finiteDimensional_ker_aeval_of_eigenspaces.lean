-- Prove2me | solution 1 for GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:48:55.091248+00:00
-- url     : https://prove2.me/submissions/d2793683-c3dd-4bfa-8f01-fd9b25e8d274

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalKerAevalOfEigenspaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (hT : ∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) (p : Polynomial ℂ) (hp : p ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  by_cases h0 : p.degree = 0
  · have hu : IsUnit p := Polynomial.isUnit_iff_degree_eq_zero.mpr h0
    have hu' : IsUnit (Polynomial.aeval T p) := hu.map _
    have hk : LinearMap.ker (Polynomial.aeval T p) = ⊥ :=
      LinearMap.ker_eq_bot.mpr ((Module.End.isUnit_iff _).mp hu').1
    rw [hk]
    infer_instance
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p h0
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr ha
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
      exact hp hq
    have hdeg : q.natDegree < n := by
      rw [← hn, hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0,
        Polynomial.natDegree_X_sub_C]
      omega
    have ihq := ih _ hdeg q hq0 rfl
    have hfg : (LinearMap.ker (Polynomial.aeval T p)).FG := by
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (Polynomial.aeval T q)
      · have hle : (LinearMap.ker (Polynomial.aeval T p)).map (Polynomial.aeval T q)
            ≤ T.eigenspace a := by
          rintro _ ⟨x, hx, rfl⟩
          rw [Module.End.mem_eigenspace_iff]
          have hx' : Polynomial.aeval T p x = 0 := hx
          rw [hq, map_mul, Module.End.mul_apply] at hx'
          simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
            Module.algebraMap_end_apply] at hx'
          exact sub_eq_zero.mp hx'
        haveI := hT a
        exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le hle)
      · exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le
          (inf_le_right : _ ≤ LinearMap.ker (Polynomial.aeval T q)))
    exact (Module.Finite.iff_fg).mpr hfg
end GlobalTheory

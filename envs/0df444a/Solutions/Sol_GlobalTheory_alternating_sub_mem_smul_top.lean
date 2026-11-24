-- Prove2me | solution 1 for GlobalTheory.alternating_sub_mem_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:16.73454+00:00
-- url     : https://prove2.me/submissions/037c30c9-ccfe-4d66-8374-d37891ae3b73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}
namespace GlobalTheory
theorem _root_.solution (ω : M [⋀^Fin D]→ₗ[A] N) (I : Ideal A) (v w : Fin D → M)
    (hvw : ∀ k, v k - w k ∈ I • (⊤ : Submodule A M)) :
    ω v - ω w ∈ I • (⊤ : Submodule A N) := by
  classical
  have key : ∀ s : Finset (Fin D), ω (s.piecewise v w) - ω w ∈ I • (⊤ : Submodule A N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have h1 : s.piecewise v w = Function.update (s.piecewise v w) i (w i) := by
        rw [eq_comm, Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hi]
      have h2 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          = ω.toMultilinearMap.toLinearMap (s.piecewise v w) i (v i - w i) := by
        rw [map_sub, Finset.piecewise_insert]
        conv_lhs => rw [h1]
        simp
      have h3 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          ∈ I • (⊤ : Submodule A N) := by
        rw [h2]
        have := Submodule.mem_map_of_mem
          (f := ω.toMultilinearMap.toLinearMap (s.piecewise v w) i) (hvw i)
        rw [Submodule.map_smul''] at this
        exact Submodule.smul_mono le_rfl le_top this
      simpa using add_mem h3 ih
  simpa using key Finset.univ
end GlobalTheory

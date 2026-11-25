-- Prove2me | solution 1 for GlobalTheory.PDivGroup.exists_comp_res_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:28:36.614473+00:00
-- url     : https://prove2.me/submissions/6b0a1c19-60e3-4c0f-bdf3-806e6252705e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable (G : PDivGroup p O)
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) {B : Type*} [CommRing B] [Algebra O B]
    (x : G.A (n + 1) →ₐ[O] B) :
    (∃ y : G.A n →ₐ[O] B, y.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) = x) ↔
      toConv x ^ p ^ n = 1 := by
  rw [← torsionIdeal_le_ker_iff, ← G.ker_res]
  constructor
  · rintro ⟨y, rfl⟩ a ha
    have ha' : G.res n a = 0 := ha
    change y (G.res n a) = 0
    rw [ha', map_zero]
  · intro h
    exact ⟨AlgHom.liftOfSurjective _ (G.res_surjective n) x h, AlgHom.liftOfSurjective_comp ..⟩
end GlobalTheory.PDivGroup

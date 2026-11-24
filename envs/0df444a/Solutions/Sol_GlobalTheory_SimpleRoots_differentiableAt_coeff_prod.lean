-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.differentiableAt_coeff_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:16.012734+00:00
-- url     : https://prove2.me/submissions/6e358a74-3078-4c7a-bfc8-57bb53436e43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : Multiset ι) (ψ : ι → E → ℂ) {x₀ : E} (h : ∀ y ∈ T, DifferentiableAt ℂ (ψ y) x₀) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (T.map fun y => X - C (ψ y x)).prod.coeff k) x₀ := by
  induction T using Multiset.induction_on generalizing k with
  | empty => simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine DifferentiableAt.sub ?_ (ha.mul (ih' k))
    cases k with
    | zero => simp
    | succ k => simpa only [coeff_X_mul] using ih' k
end GlobalTheory.SimpleRoots

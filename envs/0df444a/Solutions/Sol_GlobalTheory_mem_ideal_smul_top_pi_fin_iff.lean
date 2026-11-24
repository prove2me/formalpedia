-- Prove2me | solution 1 for GlobalTheory.mem_ideal_smul_top_pi_fin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:21.057931+00:00
-- url     : https://prove2.me/submissions/d81835ce-7772-40b0-88e9-ee698c0d5655

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChainLeIInfSupPowSmulTopOfPrecomplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Λ : Type} [CommRing Λ] (J : Ideal Λ) {a : ℕ}
    (y : Fin a → Λ) : y ∈ J • (⊤ : Submodule Λ (Fin a → Λ)) ↔ ∀ i, y i ∈ J := by
  constructor
  · intro h
    refine Submodule.smul_induction_on h ?_ ?_
    · intro r hr m _ i
      exact J.mul_mem_right _ hr
    · intro x z hx hz i
      exact J.add_mem (hx i) (hz i)
  · intro h
    rw [pi_eq_sum_univ y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top
end GlobalTheory

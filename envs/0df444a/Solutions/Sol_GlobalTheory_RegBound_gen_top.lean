-- Prove2me | solution 1 for GlobalTheory.RegBound.gen_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:35.453825+00:00
-- url     : https://prove2.me/submissions/a0ce482e-c7f9-4473-b078-8dedd5230cc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution {e : ℕ} {F : MvPolynomial σ K} (hFe : F.IsHomogeneous (e + 1)) :
    F ∈ genIn (⊤ : Ideal (MvPolynomial σ K)) e := by
  have : F ∈ homogeneousSubmodule σ K e * homogeneousSubmodule σ K 1 := by
    have h1 : F ∈ homogeneousSubmodule σ K 1 ^ (e + 1) := by
      rw [homogeneousSubmodule_one_pow]; exact hFe
    rwa [pow_succ, homogeneousSubmodule_one_pow] at h1
  refine Submodule.mul_induction_on this (fun a ha b _ => ?_) (fun a b => Ideal.add_mem _)
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨trivial, ha⟩)
end GlobalTheory.RegBound

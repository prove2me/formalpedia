-- Prove2me | solution 1 for GlobalTheory.exists_sum_eigen_split_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:20:21.391749+00:00
-- url     : https://prove2.me/submissions/2e899a26-19cb-4260-8614-9681988e6041

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AevalNegEqZeroOfResolventIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumEigenvectorsOfAevalProdLinearEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEigenSplitOfResolventIdentity
import Theorems.Thm_GlobalTheory_T_aeval_neg_eq_zero_of_resolvent_identity
import Theorems.Thm_GlobalTheory_T_exists_eigen_decomp_of_aeval_prod_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  intro N _ _ n Ω X d c ν hν hX hres w
  have key := GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity N Ω X d c (∏ s, (Polynomial.X + Polynomial.C (ν s))) hX (by
    intro u w
    rw [hres u w, Polynomial.eval_prod]
    simp)
  obtain ⟨v, hv, hw⟩ := GlobalTheory.T.exists_eigen_decomp_of_aeval_prod_eq_zero N n Ω ν hν key.1 w
  refine ⟨v, hw, fun s u => ?_⟩
  have h := key.2 (ν s) (v s) (hv s)
    (∏ t ∈ Finset.univ.erase s, (Polynomial.X + Polynomial.C (ν t)))
    (Finset.mul_prod_erase Finset.univ (fun t => Polynomial.X + Polynomial.C (ν t))
      (Finset.mem_univ s)).symm u
  rw [h, Polynomial.eval_prod]
  simp
end GlobalTheory

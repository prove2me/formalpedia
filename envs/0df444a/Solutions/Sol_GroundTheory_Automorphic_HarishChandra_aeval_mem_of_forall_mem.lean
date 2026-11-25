-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.aeval_mem_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:45.232249+00:00
-- url     : https://prove2.me/submissions/7b99c4df-873a-4d39-b824-f92906f55230

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {A : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)}
    (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ i, f i ∈ A) (F : MvPolynomial (Fin n) ℂ) :
    aeval f F ∈ A := by
  induction F using MvPolynomial.induction_on with
  | C r => rw [aeval_C]; exact A.algebraMap_mem r
  | add p q hp hq => rw [map_add]; exact A.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact A.mul_mem hp (hf i)
end GroundTheory.Automorphic.HarishChandra

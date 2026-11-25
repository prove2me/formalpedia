-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.TopClose.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:44.307978+00:00
-- url     : https://prove2.me/submissions/26a6e043-f76b-4ef0-92f7-9cb2bba43021

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_one
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_mul

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
namespace TopClose
theorem _root_.solution {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a b : ι → MvPolynomial (Fin n) ℂ)
    (h : ∀ i ∈ s, TopClose (k i) (a i) (b i)) :
    TopClose (∑ i ∈ s, k i) (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TopClose.one
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    exact (h i (mem_insert_self _ _)).mul (ih fun j hj => h j (mem_insert_of_mem hj))
end TopClose
end GroundTheory.Automorphic.HarishChandra

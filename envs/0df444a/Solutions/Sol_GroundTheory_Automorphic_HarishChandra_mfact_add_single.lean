-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mfact_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:37.817216+00:00
-- url     : https://prove2.me/submissions/dcaf0d43-aa23-430d-96e4-e676dbd21628

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {σ : Type*}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution [DecidableEq σ] (s : σ →₀ ℕ) (a : σ) :
    mfact (s + Finsupp.single a 1) = mfact s * (s a + 1) := by
  unfold mfact
  have h1 := Finsupp.mul_prod_erase' (s + Finsupp.single a 1) a (fun _ k => k.factorial)
    (fun _ => Nat.factorial_zero)
  have h2 := Finsupp.mul_prod_erase' s a (fun _ k => k.factorial) (fun _ => Nat.factorial_zero)
  have he : Finsupp.erase a (s + Finsupp.single a 1) = Finsupp.erase a s := by
    ext v
    by_cases hv : v = a
    · subst hv; simp
    · simp [Finsupp.erase_ne hv]
  rw [← h1, ← h2, he]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring
end GroundTheory.Automorphic.HarishChandra

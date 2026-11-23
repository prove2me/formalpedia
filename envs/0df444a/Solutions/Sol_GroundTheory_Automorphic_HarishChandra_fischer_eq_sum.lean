-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:36.039801+00:00
-- url     : https://prove2.me/submissions/ce48c4f7-4490-4005-918f-6d34a8c1f913

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
theorem _root_.solution (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hg : g.support ⊆ s) :
    fischer f g = ∑ m ∈ s, (mfact m : ℂ) * star (coeff m f) * coeff m g :=
  Finset.sum_subset hg fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]
end GroundTheory.Automorphic.HarishChandra

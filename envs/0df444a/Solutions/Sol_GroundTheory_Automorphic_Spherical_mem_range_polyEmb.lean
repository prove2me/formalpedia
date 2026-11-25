-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.mem_range_polyEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:32.772323+00:00
-- url     : https://prove2.me/submissions/2e5ec053-3ea4-4fe2-bb7a-e487005827bf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_natToInt_apply
import Theorems.Thm_GroundTheory_Automorphic_Spherical_polyEmb_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open AddMonoidAlgebra MvPolynomial
open GroundTheory.Automorphic.Spherical
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {q : LaurentRing n} (hq : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i) :
    q ∈ (polyEmb n).range := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single q]
  refine Subalgebra.sum_mem _ fun l hl => ?_
  refine ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (l i).toNat) (q.coeff l), ?_⟩
  change polyEmb n _ = _
  rw [polyEmb_monomial]
  congr 1
  funext i
  simp [natToInt_apply, Int.toNat_of_nonneg (hq l hl i)]
end GroundTheory.Automorphic.Spherical

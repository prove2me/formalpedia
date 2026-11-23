-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.coeff_orbitSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:55.421417+00:00
-- url     : https://prove2.me/submissions/904bb637-8559-4d48-82d6-2a4ad089d372

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric

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
theorem _root_.solution (ν l : Fin n → ℤ) :
    (orbitSum ν).coeff l = ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      ν ∘ σ.symm = l).card : ℂ) := by
  classical
  rw [orbitSum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.card_filter,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp
end GroundTheory.Automorphic.Spherical

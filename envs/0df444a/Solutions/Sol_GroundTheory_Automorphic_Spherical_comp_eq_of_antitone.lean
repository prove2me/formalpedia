-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.comp_eq_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:28.963176+00:00
-- url     : https://prove2.me/submissions/16970b1f-f6bd-4f7d-9743-91c5d1c22da8

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
theorem _root_.solution {ν : Fin n → ℤ} (hν : Antitone ν) (σ : Equiv.Perm (Fin n))
    (hσ : Antitone (ν ∘ σ)) : ν ∘ σ = ν := by
  set f : Fin n → ℤ := fun i => -ν i
  have hf : Monotone (f ∘ σ) := fun i j hij => neg_le_neg (hσ hij)
  have hf1 : Monotone (f ∘ (1 : Equiv.Perm (Fin n))) := fun i j hij => neg_le_neg (hν hij)
  have e1 := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := σ)).2 hf
  have e2 := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := 1)).2 hf1
  have : f ∘ σ = f := by
    rw [e1, ← e2]
    rfl
  funext i
  have := congrFun this i
  simpa [f] using this
end GroundTheory.Automorphic.Spherical

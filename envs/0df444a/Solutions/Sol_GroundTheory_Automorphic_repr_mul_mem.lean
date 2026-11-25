-- Prove2me | solution 1 for GroundTheory.Automorphic.repr_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:54.64814+00:00
-- url     : https://prove2.me/submissions/187d5508-e55f-4590-b07b-1ba259757881

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Theorems.Thm_GroundTheory_Automorphic_repr_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {R : Type*} [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable {H b}
namespace GroundTheory.Automorphic
theorem _root_.solution {O : Subring R} (hO : IsAdapted b O) {z w : R ⊗[K] E}
    (hz : ∀ k, (Algebra.TensorProduct.basis R b).repr z k ∈ O)
    (hw : ∀ k, (Algebra.TensorProduct.basis R b).repr w k ∈ O) (m : κ) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m ∈ O := by
  rw [repr_mul]
  exact O.sum_mem fun k _ => O.sum_mem fun l _ =>
    O.mul_mem (O.mul_mem (hz k) (hw l)) (hO.2 k l m)
end GroundTheory.Automorphic

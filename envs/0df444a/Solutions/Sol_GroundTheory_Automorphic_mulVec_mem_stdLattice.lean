-- Prove2me | solution 1 for GroundTheory.Automorphic.mulVec_mem_stdLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:23.822449+00:00
-- url     : https://prove2.me/submissions/3a8bbd4f-aee9-4b8d-8869-685f83861b6e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Theorems.Thm_GroundTheory_Automorphic_repr_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply



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
theorem _root_.solution {O : Subring R} (hO : IsAdapted b O) {M : Matrix ι ι (R ⊗[K] E)}
    (hM : ∀ i j k, (Algebra.TensorProduct.basis R b).repr (M i j) k ∈ O) {x : ι → R ⊗[K] E}
    (hx : x ∈ stdLattice ι R b O) : M *ᵥ x ∈ stdLattice ι R b O := by
  intro i k
  simp only [Matrix.mulVec, dotProduct, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact O.sum_mem fun j _ => repr_mul_mem hO (hM i j) (hx j) k
end GroundTheory.Automorphic

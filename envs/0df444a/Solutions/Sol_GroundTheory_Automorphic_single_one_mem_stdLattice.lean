-- Prove2me | solution 1 for GroundTheory.Automorphic.single_one_mem_stdLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:18.65105+00:00
-- url     : https://prove2.me/submissions/fefcb65c-b27d-4869-807c-0bb952a8d41f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Theorems.Thm_GroundTheory_Automorphic_repr_one_tmul

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
theorem _root_.solution {O : Subring R} (hO : IsAdapted b O) (j : ι) :
    (Pi.single j 1 : ι → R ⊗[K] E) ∈ stdLattice ι R b O := by
  intro i k
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, Algebra.TensorProduct.one_def, repr_one_tmul]
    exact hO.1 k
  · rw [Pi.single_eq_of_ne h, map_zero]
    exact O.zero_mem
end GroundTheory.Automorphic

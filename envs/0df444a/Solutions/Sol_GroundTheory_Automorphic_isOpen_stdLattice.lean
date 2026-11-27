-- Prove2me | solution 1 for GroundTheory.Automorphic.isOpen_stdLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:51.739126+00:00
-- url     : https://prove2.me/submissions/8d9938a0-6970-4a02-824e-2043f999e112

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_LatticeCompact
import Theorems.Thm_GroundTheory_Automorphic_stdLattice_eq_preimage

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
open Module Matrix TensorProduct Topology
noncomputable section
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
namespace GroundTheory.Automorphic
theorem _root_.solution {O : Subring R} (hO : IsOpen (O : Set R)) :
    IsOpen (stdLattice ι R b O) := by
  rw [stdLattice_eq_preimage]
  exact (vecCoordsHomeomorph R b).continuous.isOpen_preimage _
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hO)
end GroundTheory.Automorphic

-- Prove2me | solution 1 for GroundTheory.Automorphic.matrixCoords_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:02.559714+00:00
-- url     : https://prove2.me/submissions/0200fe0e-3281-493f-aa38-120953673bfd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)
variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]
omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution : matrixCoords b R (0 : Matrix ι ι (R ⊗[F] E)) = 0 := by
  funext ⟨i, j, k⟩
  rw [matrixCoords_apply]
  simp
end GroundTheory.Automorphic

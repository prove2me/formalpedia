-- Prove2me | solution 1 for GroundTheory.Automorphic.conjBase_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:36.981712+00:00
-- url     : https://prove2.me/submissions/7d0302e1-bd06-47c9-8982-945c8060d3d3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic

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
open Module Matrix TensorProduct Topology Metric
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E) (R : Type*) [CommRing R] [Algebra K R]
variable {K H R}
namespace GroundTheory.Automorphic
theorem _root_.solution (c : R) (z : R ⊗[K] E) :
    conjBase K E R (c • z) = c • conjBase K E R z :=
  map_smul (show R ⊗[K] E →ₐ[R] R ⊗[K] E from
    Algebra.TensorProduct.map (AlgHom.id R R) (conj K E).toAlgHom) c z
end GroundTheory.Automorphic

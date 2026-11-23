-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.expG_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:33.919883+00:00
-- url     : https://prove2.me/submissions/0e449a8e-5e2c-4e84-b1c2-a708950e938e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (X : 𝔤) (s t : ℝ) :
    h.expG ((s + t) • X) = h.expG (s • X) * h.expG (t • X) := by
  apply Subtype.ext; apply Units.ext
  simp only [coe_expG, Submodule.coe_smul, Subgroup.coe_mul, Units.val_mul, add_smul]
  exact exp_add_of_commute' ℝ ((Commute.refl (X : 𝔸)).smul_left s |>.smul_right t)
end GroundTheory.Automorphic.IsExpLieAlgebra

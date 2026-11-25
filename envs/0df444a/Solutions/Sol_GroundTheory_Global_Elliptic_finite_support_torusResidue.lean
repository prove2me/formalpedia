-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.finite_support_torusResidue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:36.311912+00:00
-- url     : https://prove2.me/submissions/f55ec839-38cd-448d-98c9-4ce8fc5fc63c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_image_singularSet
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_zero_of_analyticAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusResidue L f)).Finite := by
  refine (finite_image_singularSet L hf.1 hf.2).subset ?_
  intro x hx
  refine ⟨x.out, fun ha ↦ hx (residue_eq_zero_of_analyticAt ha), QuotientAddGroup.out_eq' x⟩
end GroundTheory.Global.Elliptic

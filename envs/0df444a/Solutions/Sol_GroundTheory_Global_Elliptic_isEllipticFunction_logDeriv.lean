-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.isEllipticFunction_logDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.18751+00:00
-- url     : https://prove2.me/submissions/96ae0f9a-2f25-49e5-9b92-af7b03a71d0b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_comp_add


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
    IsEllipticFunction L (logDeriv f) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ ?_⟩
  · have : logDeriv f = fun w ↦ deriv f w / f w := rfl
    rw [this]
    exact (hf.1 z).deriv.div (hf.1 z)
  · simp only [logDeriv_apply]
    rw [hf.2 z l hl]
    congr 1
    rw [← deriv_comp_add_const, hf.2.comp_add hl]
end GroundTheory.Global.Elliptic

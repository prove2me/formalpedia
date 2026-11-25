-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.finite_support_torusOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:00:55.508845+00:00
-- url     : https://prove2.me/submissions/0a2efc1c-5b3b-4359-8212-349e8b3b37a3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_isEllipticFunction_logDeriv
import Theorems.Thm_GroundTheory_Global_Elliptic_torusResidue_logDeriv
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_support_torusResidue

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
    (Function.support (torusOrder L f)).Finite := by
  refine (finite_support_torusResidue (isEllipticFunction_logDeriv hf)).subset ?_
  intro x hx
  simp only [Function.mem_support, torusResidue_logDeriv hf] at hx ⊢
  exact_mod_cast hx
end GroundTheory.Global.Elliptic

-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.finsum_torusOrder_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:25.972988+00:00
-- url     : https://prove2.me/submissions/b094c4f9-93d3-483c-b851-460eeea7adb2

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
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_support_torusOrder
import Theorems.Thm_GroundTheory_Global_Elliptic_finsum_torusResidue_eq_zero


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
    ∑ᶠ x : Torus L, torusOrder L f x = 0 := by
  have h := finsum_torusResidue_eq_zero (isEllipticFunction_logDeriv hf)
  simp_rw [torusResidue_logDeriv hf] at h
  have hc := (Int.castAddHom ℂ).map_finsum (finite_support_torusOrder hf)
  simp only [Int.coe_castAddHom] at hc
  rw [← hc] at h
  exact_mod_cast h
end GroundTheory.Global.Elliptic

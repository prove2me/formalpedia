-- Prove2me | solution 1 for GlobalTheory.SW.HAct.skew
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:07.750749+00:00
-- url     : https://prove2.me/submissions/e9568350-ae0f-443d-9d43-a51302e3cd54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (Z Y : Matrix (Fin N) (Fin N) ℂ) :
    (Y * Cᴴ + Dᴴ) * (A * Z + B) - (Y * Aᴴ + Bᴴ) * (C * Z + D) = Z - Y := by
  have e : (Y * Cᴴ + Dᴴ) * (A * Z + B) - (Y * Aᴴ + Bᴴ) * (C * Z + D) =
      Y * (Cᴴ * A) * Z + Y * (Cᴴ * B) + (Dᴴ * A) * Z + Dᴴ * B -
        (Y * (Aᴴ * C) * Z + Y * (Aᴴ * D) + (Bᴴ * C) * Z + Bᴴ * D) := by noncomm_ring
  rw [e, h1, h2, h3, h4]
  noncomm_ring
end GlobalTheory.SW.HAct

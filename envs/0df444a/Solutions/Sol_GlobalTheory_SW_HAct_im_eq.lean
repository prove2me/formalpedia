-- Prove2me | solution 1 for GlobalTheory.SW.HAct.im_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:06.786376+00:00
-- url     : https://prove2.me/submissions/2fe7e8a0-c5b6-43b4-9d16-7facb96965a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_skew

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
    (h4 : Bᴴ * D = Dᴴ * B) (Z : Matrix (Fin N) (Fin N) ℂ) :
    (2 * I)⁻¹ • ((C * Z + D)ᴴ * (A * Z + B) - (A * Z + B)ᴴ * (C * Z + D)) = imH Z := by
  rw [imH, ← skew h1 h2 h3 h4 Z Zᴴ]
  simp only [conjTranspose_add, conjTranspose_mul]
end GlobalTheory.SW.HAct

-- Prove2me | solution 1 for GlobalTheory.SW.HAct.det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:37.58727+00:00
-- url     : https://prove2.me/submissions/297623de-31c6-44a7-9da0-08057c30de7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_im_eq

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
    (h4 : Bᴴ * D = Dᴴ * B) (hZ : (imH Z).PosDef) : (C * Z + D).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hq⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hp := hZ.dotProduct_mulVec_pos hv
  rw [← im_eq h1 h2 h3 h4 Z, smul_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hq,
    mulVec_zero, sub_zero, dotProduct_smul, dotProduct_mulVec, ← star_mulVec, hq] at hp
  simp at hp
end GlobalTheory.SW.HAct

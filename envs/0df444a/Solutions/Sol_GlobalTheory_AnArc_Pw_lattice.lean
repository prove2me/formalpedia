-- Prove2me | solution 1 for GlobalTheory.AnArc.Pw_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:21.786072+00:00
-- url     : https://prove2.me/submissions/1379a651-4fe0-4657-8a42-7c9c4d0e9623

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_PolarisedLattice_lattice_of_im
import Theorems.Thm_GlobalTheory_AnArc_EF_bijective
import Theorems.Thm_GlobalTheory_AnArc_finrank_La
import Theorems.Thm_GlobalTheory_AnArc_im_Hw_Pw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {w : ℂ} (hw : (A.BwMat w).PosDef) : Function.Injective (A.Pw w) ∧
    DiscreteTopology (A.Pw w).range ∧ Submodule.span ℝ (Set.range (A.Pw w)) = ⊤ :=
  PolarisedLattice.lattice_of_im A.EF A.EF_bijective.1 (A.Pw w) (fun v => (A.Hw w).flip v)
    (fun a b => A.im_Hw_Pw hw a b) A.finrank_La
end GlobalTheory.AnArc

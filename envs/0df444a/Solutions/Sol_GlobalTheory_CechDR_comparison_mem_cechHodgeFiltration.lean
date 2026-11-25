-- Prove2me | solution 1 for GlobalTheory.CechDR.comparison_mem_cechHodgeFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:40:00.123821+00:00
-- url     : https://prove2.me/submissions/0f29e81d-392e-417d-b58d-d90958bef60c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Theorems.Thm_GlobalTheory_CechDR_structureSheaf_comparison_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.CechDR
theorem _root_.solution (s : X ⟶ Sp R) {c : FirstDeRham s} (hc : c ∈ F1 s) : cmp1 s c ∈ CechHodgeFiltration s := by
  change toHO1 s (cmp1 s c) = 0
  rw [structureSheaf_comparison_comm, show toH1O s c = 0 from hc, map_zero]
end GlobalTheory.CechDR

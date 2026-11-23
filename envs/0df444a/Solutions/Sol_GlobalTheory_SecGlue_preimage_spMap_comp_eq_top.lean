-- Prove2me | solution 1 for GlobalTheory.SecGlue.preimage_spMap_comp_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:35.62849+00:00
-- url     : https://prove2.me/submissions/fc463b87-4488-4d6b-ad5b-1ebcb02cca35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue
namespace GlobalTheory.SecGlue
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') {u : Sp S ⟶ Y} (h : u ⁻¹ᵁ V = ⊤) : (spMap g ≫ u) ⁻¹ᵁ V = ⊤ := by
  rw [Scheme.Hom.comp_preimage, h, Scheme.Hom.preimage_top]
end GlobalTheory.SecGlue

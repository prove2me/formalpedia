-- Prove2me | solution 1 for GlobalTheory.ThetaShiftProofs.j_mem_abLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:58.012163+00:00
-- url     : https://prove2.me/submissions/60b8f714-ad1e-4cee-9413-8387c729e08a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsOpenImmersionJKPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaShiftProofs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
namespace GlobalTheory.ThetaShiftProofs
theorem _root_.solution {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (p : Xo.XF c) :
    Y.j p ∈ abLocus Y.t.G := by
  have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using hz
end GlobalTheory.ThetaShiftProofs

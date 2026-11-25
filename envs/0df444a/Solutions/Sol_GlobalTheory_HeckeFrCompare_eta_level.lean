-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.eta_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:48:11.72055+00:00
-- url     : https://prove2.me/submissions/665e783c-3fc7-41fe-927f-1a8a72c7076c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution (a : Dw.La) : Xo.univ.eta (l.M' • a) = 1 := by
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  refine Xo.univ.eta_ker _ ?_
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := by
    exact Ideal.mul_le.2 fun r hr s _ => Ideal.mul_mem_right _ _ hr
  have h' : (l.M : 𝓞 E) ∈ l.Mb := hle h
  have e : l.M' • a = (l.M : 𝓞 E) • (k • a) := by rw [hk, mul_smul, Nat.cast_smul_eq_nsmul]
  rw [e]
  exact Submodule.smul_mem_smul h' Submodule.mem_top
end GlobalTheory.HeckeFrCompare

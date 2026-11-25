-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.VanOrd.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:10.191132+00:00
-- url     : https://prove2.me/submissions/569f9719-84aa-4f03-b95e-8266deceacfa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_SpanSubtraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology Asymptotics
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
namespace VanOrd
theorem _root_.solution {X : Data E r} {Xa : ArchInM X} {Fl : FlatM X Xa} {a : ℕ} (ha : a ≠ 0)
    {f : Frame X.Ψ r → ℂ} (hf : VanOrd Fl a f) (j : Fin Fl.δ)
    (hs : ∀ k, Fl.s k (cpt X (Fl.xs j) 0) = 0) : f (cpt X (Fl.xs j) 0) = 0 := by
  obtain ⟨C, hC⟩ := (hf j).bound
  have h := hC.self_of_nhds
  have hz : zAt Fl j 0 = 0 := by
    ext k
    simp [zAt, hs k]
  simp only [hz, norm_zero, zero_pow ha, mul_zero] at h
  exact norm_le_zero_iff.mp h
end VanOrd
end GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction

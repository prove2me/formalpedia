-- Prove2me | solution 1 for GlobalTheory.AffGlue.Cech.span_small_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:51:18.933797+00:00
-- url     : https://prove2.me/submissions/5198d3f3-f58c-4fe8-980a-eb6839751a0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineCoverSectionsGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
open GlobalTheory GlobalTheory.AffGlue GlobalTheory.AffGlue.Cech
variable {T : Scheme.{0}}
namespace GlobalTheory.AffGlue.Cech
theorem _root_.solution {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens)
    (hc : V ≤ ⨆ i, W i) :
    Ideal.span {f : Γ(T, V) | ∃ i, T.basicOpen f ≤ W i} = ⊤ := by
  rw [← hV.self_le_iSup_basicOpen_iff]
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hx)
  obtain ⟨f, hf, hxf⟩ := hV.exists_basicOpen_le (V := W i) ⟨x, hi⟩ hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩
end GlobalTheory.AffGlue.Cech

-- Prove2me | solution 1 for GlobalTheory.LatPair.inX_mem_gluedLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:51.893214+00:00
-- url     : https://prove2.me/submissions/8c60c985-ae23-44e3-9930-615cc4bbb036

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {c : ℕ}
namespace GlobalTheory.LatPair
theorem _root_.solution {q : Unif k} {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) {L : Submodule 𝒪[k] (n → k)} {f x : n → k} :
    inX k n c x ∈ gluedLat q c p L f ↔ x ∈ L := by
  rw [mem_gluedLat]
  constructor
  · rintro ⟨s, hs, h⟩
    have h0 := (h ⟨p - 1, by omega⟩).2.1 (by simp; omega)
    have : s = 0 := by simpa [inX, Unif.inv, q.ne_zero] using h0
    simpa [this, inX] using hs
  · exact fun hx => ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩
end GlobalTheory.LatPair

-- Prove2me | solution 1 for N25.GlobalKummer.kernel_comp_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:46.405502+00:00
-- url     : https://prove2.me/submissions/edb30597-de25-4be1-843a-c9ad689d65e2

import Definitions.Def_N25_GlobalKummerSequence

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace N25.GlobalKummer

/-- The two literal K2 maps form a complex. -/
theorem _root_.solution (hPhi : PhiFiveZero) (K2 : K2Rows) :
    kernelInclusion hPhi K2 ≫ kernelQuotient hPhi K2 = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  change K2.q (K2.i a) = 0
  have h : K2.i a ∈ K2.i.range := ⟨a, rfl⟩
  rw [← K2.exact_at_V] at h
  exact h

end N25.GlobalKummer

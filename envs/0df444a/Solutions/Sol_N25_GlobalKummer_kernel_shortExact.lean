-- Prove2me | solution 1 for N25.GlobalKummer.kernel_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:36.653235+00:00
-- url     : https://prove2.me/submissions/34b0a062-159c-4813-89ad-4f20e1010077

import Theorems.Thm_N25_GlobalKummer_kernel_comp_zero
import Definitions.Def_N25_GlobalKummerSequence

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace N25.GlobalKummer

/-- The frozen character filtration is short exact in the representation category. -/
theorem _root_.solution (hPhi : PhiFiveZero) (K2 : K2Rows) :
    (ShortComplex.mk (kernelInclusion hPhi K2) (kernelQuotient hPhi K2)
      (kernel_comp_zero hPhi K2)).ShortExact := by
  have hi : Function.Injective (kernelInclusion hPhi K2).hom := K2.i_injective
  have hq : Function.Surjective (kernelQuotient hPhi K2).hom := K2.q_surjective
  haveI : Mono (kernelInclusion hPhi K2) := (Rep.mono_iff_injective _).mpr hi
  haveI : Epi (kernelQuotient hPhi K2) := (Rep.epi_iff_surjective _).mpr hq
  refine ⟨?_⟩
  let C := ShortComplex.mk (kernelInclusion hPhi K2) (kernelQuotient hPhi K2)
    (kernel_comp_zero hPhi K2)
  apply (C.exact_map_iff_of_faithful
    (forget₂ (Rep (ZMod 71) Gal) (ModuleCat (ZMod 71)))).mp
  apply (ShortComplex.exact_iff_of_hasForget _).mpr
  intro v hv
  change ↥V at v
  have h : v ∈ K2.q.ker := hv
  rw [K2.exact_at_V] at h
  exact h

end N25.GlobalKummer

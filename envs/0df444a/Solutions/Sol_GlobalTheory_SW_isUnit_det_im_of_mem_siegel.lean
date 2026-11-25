-- Prove2me | solution 1 for GlobalTheory.SW.isUnit_det_im_of_mem_siegel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:55.018239+00:00
-- url     : https://prove2.me/submissions/a1bd80d1-7391-4c2f-97d8-1366e3292d5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CanonicalThetaExponentSymplecticInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ}
    (hτ : τ ∈ Siegel ι) : IsUnit (τ.map fun z => (z.im : ℂ)).det := by
  have h : (τ.map fun z => (z.im : ℂ)) = Complex.ofRealHom.mapMatrix (τ.map Complex.im) := by
    ext i j; simp
  rw [h, ← RingHom.map_det]
  exact (hτ.2.det_pos.ne'.isUnit).map _
end GlobalTheory.SW

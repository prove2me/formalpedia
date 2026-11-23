-- Prove2me | solution 1 for GlobalTheory.Mem.FewPrimes.finite_absNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:00.821831+00:00
-- url     : https://prove2.me/submissions/87170be0-d1f4-4af6-ab94-625f1de016db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.FewPrimes
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.FewPrimes
theorem _root_.solution (X : ℝ) :
    {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.Finite := by
  have h := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊
  have h2 := h.preimage (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)
  refine h2.subset ?_
  intro v hv
  exact Nat.le_floor hv
end GlobalTheory.Mem.FewPrimes

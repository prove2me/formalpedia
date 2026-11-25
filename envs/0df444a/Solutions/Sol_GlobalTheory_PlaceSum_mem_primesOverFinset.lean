-- Prove2me | solution 1 for GlobalTheory.PlaceSum.mem_primesOverFinset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:32.619675+00:00
-- url     : https://prove2.me/submissions/1a125183-2097-4b97-b601-aa25304191b5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes
import Theorems.Thm_GlobalTheory_PlaceSum_liesOver_resChar
import Theorems.Thm_GlobalTheory_PlaceSum_span_ne_bot
import Theorems.Thm_GlobalTheory_PlaceSum_span_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.PlaceSum
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.PlaceSum
theorem _root_.solution {p : ℕ} (hp : p.Prime) (la : HeightOneSpectrum (𝓞 K)) (h : resCharOf la = p) :
    la.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) := by
  haveI := span_isMaximal hp
  refine (IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) _).mpr ⟨la.isPrime, ?_⟩
  rw [← h]
  exact liesOver_resChar la
end GlobalTheory.PlaceSum

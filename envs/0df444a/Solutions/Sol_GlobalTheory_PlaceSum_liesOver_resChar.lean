-- Prove2me | solution 1 for GlobalTheory.PlaceSum.liesOver_resChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:04.629983+00:00
-- url     : https://prove2.me/submissions/dedb1edc-debf-4fb3-97fb-52dccea7d2b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes

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
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) :
    la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  refine ⟨?_⟩
  ext n
  rw [Ideal.mem_span_singleton, Ideal.under_def, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  have h : (Ideal.Quotient.mk la.asIdeal) (algebraMap ℤ (𝓞 K) n) = (n : 𝓞 K ⧸ la.asIdeal) := by simp
  rw [h]
  exact (CharP.intCast_eq_zero_iff (𝓞 K ⧸ la.asIdeal) (ringChar (𝓞 K ⧸ la.asIdeal)) n).symm
end GlobalTheory.PlaceSum

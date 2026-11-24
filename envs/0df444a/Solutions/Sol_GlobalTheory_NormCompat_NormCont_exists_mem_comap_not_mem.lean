-- Prove2me | solution 1 for GlobalTheory.NormCompat.NormCont.exists_mem_comap_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:34.099153+00:00
-- url     : https://prove2.me/submissions/e4c2d976-99be-4b48-80c2-0ffbd1233854

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.NormCont
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
namespace GlobalTheory.NormCompat.NormCont
theorem _root_.solution (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K))
    (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) :
    ∃ e : 𝓞 E, algebraMap (𝓞 E) (𝓞 K) e ∈ w.asIdeal ∧ e ∉ v.asIdeal := by
  by_contra h
  push_neg at h
  have hmax : (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).IsMaximal :=
    haveI := w.isMaximal; Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w.asIdeal
  exact hw (hmax.eq_of_le v.isPrime.ne_top fun e he => h e he)
end GlobalTheory.NormCompat.NormCont

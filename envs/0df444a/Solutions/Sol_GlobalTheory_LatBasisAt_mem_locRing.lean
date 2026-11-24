-- Prove2me | solution 1 for GlobalTheory.LatBasisAt.mem_locRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:55.556297+00:00
-- url     : https://prove2.me/submissions/a886e9a5-0485-4658-ba24-2b1733cc1e5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LatticeHasBasisAtEveryFinitePlace
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.LatBasisAt
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.LatBasisAt
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∉ w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl
end GlobalTheory.LatBasisAt

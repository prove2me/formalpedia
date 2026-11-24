-- Prove2me | solution 1 for GlobalTheory.valued_absNorm_lt_one_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:22.180845+00:00
-- url     : https://prove2.me/submissions/d06c9699-90fd-4b9b-afbb-c8c38e792feb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNatCongruenceLeOpenSubgroupGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  convert h using 2
  have : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) := by simp
  rw [this]
  rfl
end GlobalTheory

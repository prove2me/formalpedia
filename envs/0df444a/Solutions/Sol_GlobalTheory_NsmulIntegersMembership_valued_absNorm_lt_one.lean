-- Prove2me | solution 1 for GlobalTheory.NsmulIntegersMembership.valued_absNorm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:02:28.480439+00:00
-- url     : https://prove2.me/submissions/2b7d09fe-6676-4d59-ae03-3f3428b9686f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNsmulIntegersMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.NsmulIntegersMembership
namespace GlobalTheory.NsmulIntegersMembership
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by
  have h1 : v.valuation F (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) < 1 :=
    (v.valuation_lt_one_iff_mem (K := F) _).2 (Ideal.absNorm_mem v.asIdeal)
  have h2 := v.valuedAdicCompletion_eq_valuation' (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : F)
  have h3 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((Ideal.absNorm v.asIdeal : ℕ) : F) := by
    rw [map_natCast]
  rw [h3]
  refine lt_of_eq_of_lt h2 ?_
  simpa using h1
end GlobalTheory.NsmulIntegersMembership

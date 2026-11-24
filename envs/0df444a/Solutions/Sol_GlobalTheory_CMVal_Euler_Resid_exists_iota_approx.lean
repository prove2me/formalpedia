-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.Resid.exists_iota_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:04:00.452071+00:00
-- url     : https://prove2.me/submissions/8501a784-db82-42a9-b0d7-a6ec369b78e7

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitRepresentativesSplitPrime
import Theorems.Thm_ReciprocityTheory_Aut_adic_algebraMap_R
import Theorems.Thm_ReciprocityTheory_Aut_adic_exists_approx
import Theorems.Thm_ReciprocityTheory_Aut_adic_valued_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.Resid
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler.Resid
theorem _root_.solution {P : HeightOneSpectrum (𝓞 E)}
    (h : ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal) (x : P.adicCompletion E)
    (hx : Valued.v x ≤ 1) : ∃ a : OF E, Valued.v (x - iota a P) < 1 := by
  obtain ⟨b, hb⟩ := ReciprocityTheory.Aut.adic_exists_approx (R := 𝓞 E) (K := E) P x hx
  obtain ⟨a, ha⟩ := h b
  refine ⟨a, ?_⟩
  rw [ReciprocityTheory.Aut.adic_algebraMap_R] at hb
  have h1 : iota a P = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a)) := rfl
  have h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (b - algebraMap (OF E) (𝓞 E) a))) < 1 := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_lt_one_iff_mem _).2 ha
  have := Valuation.map_add_lt _ hb h2
  rwa [map_sub, map_sub, sub_add_sub_cancel, ← h1] at this
end GlobalTheory.CMVal.Euler.Resid

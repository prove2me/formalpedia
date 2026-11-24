-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.notMem_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:45:03.609835+00:00
-- url     : https://prove2.me/submissions/074ef9f1-56cb-4fc5-afb2-9f720bf802c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution {t N : ℕ} (ht : t.Coprime N) {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∈ v.asIdeal) : (t : 𝓞 F) ∉ v.asIdeal := fun h => by
  obtain ⟨p, q, hpq⟩ : IsCoprime (t : 𝓞 F) (N : 𝓞 F) := Nat.Coprime.cast ht
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hpq ▸ add_mem (v.asIdeal.mul_mem_left _ h) (v.asIdeal.mul_mem_left _ hv)))
end GlobalTheory.UnRep.Compare

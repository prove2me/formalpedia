-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.congAtA_iff_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:51.821107+00:00
-- url     : https://prove2.me/submissions/54d30515-de74-43c8-a31e-422adaf88c9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_congOneAt_of_congAtA
import Theorems.Thm_GlobalTheory_UnRep_Compare_exists_coprime_dvd
import Theorems.Thm_GlobalTheory_UnRep_Compare_congAtA_of_congOneAt

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
theorem _root_.solution {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {N D d : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (hd : d ≠ 0) (k : Matrix (Fin n) (Fin n) (RA F E))
    (hk : ∀ z ∈ hat F (L : Set (Fin n → E)), d • k *ᵥ z ∈ hat F (L : Set (Fin n → E))) :
    CongAtA F L N D k ↔ CongOneAt N D (L : Set (Fin n → E)) k := by
  refine ⟨congOneAt_of_congAtA L N D k, fun h => ?_⟩
  obtain ⟨t, j, ht, hdvd⟩ := exists_coprime_dvd N (D * d) (mul_ne_zero hD hd)
  exact ⟨t, ht, congAtA_of_congOneAt L hN hD hd k hk h hdvd⟩
end GlobalTheory.UnRep.Compare

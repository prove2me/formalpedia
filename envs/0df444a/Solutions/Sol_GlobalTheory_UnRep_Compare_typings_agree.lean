-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.typings_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:15.555165+00:00
-- url     : https://prove2.me/submissions/7541712b-642c-4f45-aab6-bdeb2d805c64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnA_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_splitPl_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_suppSplit_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_congAtA_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_repStatement_iff

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
theorem _root_.solution :
    (∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ)
      (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)), IsUnA c G g ↔ IsUnitaryA c G g) ∧
    (∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E),
      Module.finrank F E = 2 → c ≠ 1 →
      (∀ v : HeightOneSpectrum (𝓞 F), SplitPl c v ↔ IsSplitPlace E v) ∧
      ∀ (n N : ℕ) (h : Matrix (Fin n) (Fin n) (RA F E)), SuppSplit c N h ↔ SupportedAtSplit N h) ∧
    (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      ∀ N D : ℕ, N ≠ 0 → D ≠ 0 → ∀ k : Matrix (Fin n) (Fin n) (RA F E),
      CongAtA F L N D k ↔ CongOneAt N D (L : Set (Fin n → E)) k) ∧
    (RepStatement 2 ↔ SplitRepresentatives) :=
  ⟨fun _ _ _ _ _ _ c _ G g => isUnA_iff c G g,
    fun _ _ _ _ _ _ c h2 hc => ⟨splitPl_iff c h2 hc, fun _ N h => suppSplit_iff c h2 hc N h⟩,
    fun _ _ _ _ _ _ _ _ L hfg hsp _ _ hN hD k => congAtA_iff L hfg hsp hN hD k, repStatement_iff⟩
end GlobalTheory.UnRep.Compare

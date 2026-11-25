-- Prove2me | solution 1 for GlobalTheory.HL.RatPat.pt_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:23.404301+00:00
-- url     : https://prove2.me/submissions/58c04615-2a32-413d-8913-41b64e3d6e27

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliser
import Theorems.Thm_GlobalTheory_HL_RatPat_rhoL_lt
import Theorems.Thm_GlobalTheory_HL_RatPat_rhoL_rhoL
import Theorems.Thm_GlobalTheory_HL_RatPat_entry_ne_zero_iff
import Theorems.Thm_GlobalTheory_HL_RatPat_rhoL_rev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatPat
namespace GlobalTheory.HL.RatPat
theorem _root_.solution {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : Pt R n) :
    ∃ ρ : Fin n → Fin n, Function.Involutive ρ ∧ (∀ a b, w.mat a b ≠ 0 ↔ b = ρ a) ∧
      ∀ x y : Fin n, x < y → (∀ l : ℕ, (x : ℕ) < l → l ≤ (y : ℕ) →
        ¬ ∀ a : Fin n, (a : ℕ) < l → ((ρ a : Fin n) : ℕ) < l) → ρ y < ρ x := by
  have hn : ∀ a : Fin n, (a : ℕ) < (w.blocks.map (fun b => (b.2 : ℕ))).sum := fun a => by rw [w.size]; exact a.2
  let ρ : Fin n → Fin n := fun a => ⟨rhoL w.blocks a, by have := rhoL_lt _ _ (hn a); rwa [w.size] at this⟩
  refine ⟨ρ, fun a => Fin.ext (rhoL_rhoL _ _ (hn a)), fun a b => ?_, fun x y hxy hB => ?_⟩
  · show ptEntryL w.blocks a b ≠ 0 ↔ b = ρ a
    rw [entry_ne_zero_iff _ _ _ (hn a), Fin.ext_iff]
  · show rhoL w.blocks y < rhoL w.blocks x
    refine rhoL_rev _ _ _ hxy (hn y) fun l h1 h2 hcl => hB l h1 h2 fun a ha => hcl a ha
end GlobalTheory.HL.RatPat

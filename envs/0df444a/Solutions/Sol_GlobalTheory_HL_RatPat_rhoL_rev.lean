-- Prove2me | solution 1 for GlobalTheory.HL.RatPat.rhoL_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:55.430005+00:00
-- url     : https://prove2.me/submissions/8a1e6c7c-2987-4f45-a24b-67ba8f5dd5fb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliser
import Theorems.Thm_P2M_GlobalTheory_HL_RatPat_sum_cons__0b43592650e5
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatPat
namespace GlobalTheory.HL.RatPat
theorem _root_.solution {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (x y : ℕ) (hxy : x < y)
    (hy : y < (bs.map (fun b => (b.2 : ℕ))).sum)
    (hB : ∀ l : ℕ, x < l → l ≤ y → ¬ ∀ a, a < l → rhoL bs a < l) : rhoL bs y < rhoL bs x := by
  induction bs generalizing x y with
  | nil => simp at hy
  | cons c bs ih =>
    obtain ⟨t, s⟩ := c
    rw [sum_cons'] at hy
    simp only [rhoL] at hB ⊢
    by_cases h1 : y < (s : ℕ)
    · rw [if_pos h1, if_pos (by omega)]; omega
    · by_cases h2 : x < (s : ℕ)
      · exfalso
        refine hB s h2 (by omega) fun a ha => ?_
        rw [if_pos ha]; omega
      · rw [if_neg h1, if_neg h2]
        have := ih (x - s) (y - s) (by omega) (by omega) fun l hl1 hl2 hcl => by
          refine hB (s + l) (by omega) (by omega) fun a ha => ?_
          by_cases h : a < (s : ℕ)
          · rw [if_pos h]; omega
          · rw [if_neg h]; have := hcl (a - s) (by omega); omega
        omega
end GlobalTheory.HL.RatPat

-- Prove2me | solution 1 for GlobalTheory.HL.TermBasic.inner_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:01.38525+00:00
-- url     : https://prove2.me/submissions/c3da6a99-2e64-4194-ba48-a7346d94575d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Theorems.Thm_GlobalTheory_HL_TermBasic_mem_smul
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TermBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.TermBasic
theorem _root_.solution {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (x : S.V) :
    (∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) ↔
      ∃ y ∈ n • Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  obtain ⟨h1, h2⟩ := hn.2
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨n y, (mem_smul S n Λ _).2 ⟨y, hy, rfl⟩, (h1 y).2 hp, ?_⟩
    have := (S.spanTo g r).add_mem (h2 y hp) hx
    rwa [sub_add_sub_cancel] at this
  · rintro ⟨_, hy, hp, hx⟩
    obtain ⟨y, hy0, rfl⟩ := (mem_smul S n Λ _).1 hy
    refine ⟨y, hy0, (h1 y).1 hp, ?_⟩
    have := (S.spanTo g r).sub_mem hx (h2 y ((h1 y).1 hp))
    rwa [sub_sub_sub_cancel_left] at this
end GlobalTheory.HL.TermBasic

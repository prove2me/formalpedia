-- Prove2me | solution 1 for GlobalTheory.HL.TermBasic.trace_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:22.426414+00:00
-- url     : https://prove2.me/submissions/2acdbe4a-356a-48c9-8072-2b6818ab7c47

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Theorems.Thm_GlobalTheory_HL_TermBasic_mem_smul
import Theorems.Thm_GlobalTheory_HL_TermBasic_smul_eq_map
import Theorems.Thm_GlobalTheory_HL_TermBasic_map_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_map_mem_iff

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
variable {S} {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
include hg
namespace GlobalTheory.HL.TermBasic
theorem _root_.solution {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V} {j : ℕ}
    (h : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔ x ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) (x : S.V) :
    (x ∈ n • Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) := by
  have e : Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) =
      n • Submodule.span L.O (g '' {i | (i : ℕ) < j}) := by
    rw [smul_eq_map, Submodule.map_span, Set.image_image]; rfl
  rw [e, mem_smul, mem_smul]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h2⟩
    exact ⟨y, (h y).1 ⟨hy, (map_mem_iff hg hn j y).1 h2⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, ((h y).2 hy).1, rfl⟩, map_mem hg hn j ((h y).2 hy).2⟩
end GlobalTheory.HL.TermBasic

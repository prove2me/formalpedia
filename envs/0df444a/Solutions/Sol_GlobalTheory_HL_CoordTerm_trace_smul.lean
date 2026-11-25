-- Prove2me | solution 1 for GlobalTheory.HL.CoordTerm.trace_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:26:04.238583+00:00
-- url     : https://prove2.me/submissions/f096a036-2514-4198-b195-61e1b5af1628

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordTerm
theorem _root_.solution {A B : Submodule E S.V} {n : S.GLV} (hn : n ∈ unipOn A B)
    (Λ : Submodule M.L.O S.V) (x : S.V) :
    (∃ y ∈ n • Λ, y ∈ A ∧ y - x ∈ B) ↔ ∃ y ∈ Λ, y ∈ A ∧ y - x ∈ B := by
  obtain ⟨h1, h2⟩ := hn
  constructor
  · rintro ⟨y, hy, hA, hB⟩
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have hzA : z ∈ A := (h1 z).1 hA
    refine ⟨z, hz, hzA, ?_⟩
    have := B.sub_mem hB (h2 z hzA)
    have e : n • z - x - (n z - z) = z - x := by
      change n z - x - (n z - z) = z - x
      abel
    rwa [e] at this
  · rintro ⟨z, hz, hA, hB⟩
    refine ⟨n • z, Submodule.smul_mem_pointwise_smul _ _ _ hz, (h1 z).2 hA, ?_⟩
    have := B.add_mem hB (h2 z hA)
    have e : z - x + (n z - z) = n • z - x := by
      change _ = n z - x
      abel
    rwa [e] at this
end GlobalTheory.HL.CoordTerm

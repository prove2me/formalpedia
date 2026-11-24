-- Prove2me | solution 1 for GlobalTheory.HL.CoordInnerSnd.mem_perp_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:43.230957+00:00
-- url     : https://prove2.me/submissions/280401fb-b637-40a7-87c7-2b297a9e71cc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordInnerSnd
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable (Fr : LocNG.FrameD H r)
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
namespace GlobalTheory.HL.CoordInnerSnd
theorem _root_.solution (hgs : ∀ a, gs a = c.e (Fr.es a)) (v : V) :
    c.e v ∈ perp M.L S.Hm (Submodule.span E (Set.range gs)) ↔ ∀ a, H.h v (Fr.es a) = 0 := by
  constructor
  · intro h a
    rw [← c.h_eq, ← hgs]
    exact h _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h y hy
    obtain ⟨y, rfl⟩ := c.e.surjective y
    have : Submodule.span E (Set.range gs) ≤ (LinearMap.ker (hl H v)).map (c.e : V →ₗ[E] S.V) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact ⟨_, h_swap_zero (h a), (hgs a).symm⟩
    obtain ⟨y', hy', he⟩ := this hy
    rw [← c.e.injective he]
    exact (c.h_eq v y').trans (h_swap_zero hy')
end GlobalTheory.HL.CoordInnerSnd

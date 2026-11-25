-- Prove2me | solution 1 for GlobalTheory.HL.WitIndep.coords_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:32:25.061844+00:00
-- url     : https://prove2.me/submissions/0e9b2fcc-e466-4404-826e-759ed9e63e4f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_dual
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_sum_l
import Theorems.Thm_GlobalTheory_HL_StdLat_stdLat_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.WitIndep
theorem _root_.solution (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V)
    (hA : S.IsInner g gs A) (n : S.GLV) (c : Fin (r + 1) → E) :
    ∑ i, c i • n (g i) ∈ n • S.stdLat g gs A ↔ ∀ i, c i ∈ L.O := by
  have h1 : ∑ i, c i • n (g i) = n • ∑ i, c i • g i := by
    change _ = n (∑ i, c i • g i)
    simp
  have h2 := (StdLat.stdLat_spec L r k S g gs hg A hA).2.1 (r + 1) le_rfl (∑ i, c i • g i)
  have h3 : ∑ i, c i • g i ∈ S.spanTo g (r + 1) := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (FrameOnto.mem_spanTo S g i.2)
  have h4 : g '' {i | (i : ℕ) < r + 1} = Set.range g := by
    ext x; simp [Fin.is_le]
  have h5 : ∀ j, ∃ u : S.V, ∀ i, hf L S.Hm (g i) u = if i = j then 1 else 0 := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact FrameOnto.exists_dual S _ _ S.T S.gram S.dual
    · exact FrameOnto.exists_dual S _ _ S.T' S.gram' S.dual'
  have h6 : ∀ x : S.V, n • x ∈ n • S.stdLat g gs A ↔ x ∈ S.stdLat g gs A := fun x => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, hy, e⟩ => MulAction.injective n e ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  rw [h1, h6, ((and_iff_left h3).symm.trans h2), h4,
    Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨d, hd⟩ j
    obtain ⟨u, hu⟩ := h5 j
    have := congrArg (fun x => hf L S.Hm x u) hd
    have e : ∀ i, d i • g i = (d i : E) • g i := fun _ => rfl
    simp [e, StdLat.hf_sum_l, hf_smul_l, hu] at this
    rw [← this]
    exact (d j).2
  · exact fun h => ⟨fun i => ⟨c i, h i⟩, rfl⟩
end GlobalTheory.HL.WitIndep

-- Prove2me | solution 1 for GlobalTheory.HL.FrameStab.mem_Nof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:02.113198+00:00
-- url     : https://prove2.me/submissions/a8d689da-956a-4a1a-b6bd-8a2ca65c4484

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Theorems.Thm_P2M_GlobalTheory_HL_FrameStab_mem_unipOn__694350c57e4c
import Theorems.Thm_GlobalTheory_HL_FrameStab_step_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_r
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_le_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameStab
theorem _root_.solution [IsArtinianRing E] (g g' : Fin (r + 1) → S.V) (T : Fˣ)
    (gram : ∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
    (W : Submodule E S.V) (hW : ∀ w ∈ W, ∀ y ∈ S.spanTo g (r + 1), hf L S.Hm w y = 0)
    (htop : (S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) ⊔ W = ⊤)
    (hnd : ∀ u ∈ S.spanTo g' (r + 1), (∀ y ∈ S.spanTo g (r + 1), hf L S.Hm u y = 0) → u = 0)
    (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (hs' : (∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1))
    (h : S.GLV) (hi : h ∈ isomG L S.Hm) (hg : ∀ j, h (g j) = ∑ i, s i j • g i)
    (hg' : ∀ j, h (g' j) = ∑ i, s' i j • g' i) (hw : ∀ w ∈ W, h w = w) : h ∈ S.Nof g := by
  have hu : ∀ l, h ∈ unipOn (S.spanTo g (l + 1)) (S.spanTo g l) := fun l =>
    mem_unipOn' (spanTo_mono S g (Nat.le_succ _)) h (step_mem S g s hs h hg l)
  refine ⟨⟨hi, Subgroup.mem_iInf.2 fun l => hu l⟩, mem_unipOn' (spanTo_le_perp S g T gram) h ?_⟩
  intro v hv
  have hv' : v ∈ (S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) ⊔ W := htop ▸ Submodule.mem_top
  obtain ⟨m, hm, w, hw', rfl⟩ := Submodule.mem_sup.1 hv'
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hm
  have hxp : x ∈ perp L S.Hm (S.spanTo g r) := by
    have : S.spanTo g (r + 1) ≤ perp L S.Hm (S.spanTo g r) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, -, rfl⟩
      exact mem_perp S g T gram i
    exact this hx
  have hwp : w ∈ perp L S.Hm (S.spanTo g r) := fun z hz => hW w hw' z (spanTo_mono S g (Nat.le_succ _) hz)
  have hyp : y ∈ perp L S.Hm (S.spanTo g r) := by
    have := sub_mem (sub_mem hv hwp) hxp
    simpa using this
  have hy0 : h y - y = 0 := by
    refine hnd _ (spanTo_mono S g' (Nat.le_succ _) (step_mem S g' s' hs' h hg' r y hy)) fun z hz => ?_
    have hz1 : h.symm z ∈ S.spanTo g (r + 1) := ((hu r).1 _).1 (by simpa using hz)
    have hz2 := hyp _ ((hu r).2 _ hz1)
    have hz3 := hi y (h.symm z)
    rw [LinearEquiv.apply_symm_apply] at hz2 hz3
    rw [hf_sub_r] at hz2
    rw [hf_sub_l, hz3]
    linear_combination -hz2
  have : h (x + y + w) - (x + y + w) = h x - x := by
    rw [map_add, map_add, hw w hw', sub_eq_zero.1 hy0]; abel
  rw [this]
  exact (hu r).2 x hx
end GlobalTheory.HL.FrameStab

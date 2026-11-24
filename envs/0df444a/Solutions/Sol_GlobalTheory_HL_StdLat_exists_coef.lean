-- Prove2me | solution 1 for GlobalTheory.HL.StdLat.exists_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:12:47.605397+00:00
-- url     : https://prove2.me/submissions/1a13386c-60fe-4d70-a5fc-6ddf9bec33a6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StdLat
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.StdLat
theorem _root_.solution {m : ℕ} {V : Type} [AddCommGroup V] [Module E V] (g : Fin m → V) (s : Set (Fin m))
    {x : V} (hx : x ∈ Submodule.span E (g '' s)) :
    ∃ c : Fin m → E, (∀ i, i ∉ s → c i = 0) ∧ x = ∑ i, c i • g i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (by rintro rfl; exact hj hi) _, ?_⟩
    simp [Pi.single_apply]
  | zero => exact ⟨0, by simp, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, rfl⟩ := ha
    obtain ⟨d, hd, rfl⟩ := hb
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t a _ ha =>
    obtain ⟨c, hc, rfl⟩ := ha
    exact ⟨t • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, mul_smul]⟩
end GlobalTheory.HL.StdLat

-- Prove2me | solution 1 for GlobalTheory.HL.DatumStab.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:02.32089+00:00
-- url     : https://prove2.me/submissions/40b484ae-91d2-4237-b279-f734778357b2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DatumStabilizerBetweenLatticeStabilizers
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_StdLat_exists_mul_mem
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.DatumStab
theorem _root_.solution {n : ℕ} {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (w : Fin n → E) :
    ∃ c : F, c ≠ 0 ∧ c ∈ 𝒪[F] ∧ algebraMap F E c • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  have hO : ∀ c : F, c ∈ 𝒪[F] → ∀ v ∈ Λ, algebraMap F E c • v ∈ Λ := fun c hc v hv =>
    Λ.smul_mem (⟨_, (UnramOrder.algebraMap_mem_iff L c).2 hc⟩ : L.O) hv
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, hc', h⟩ := ha
    obtain ⟨d, hd, hd', h'⟩ := hb
    refine ⟨c * d, mul_ne_zero hc hd, Subring.mul_mem _ hc' hd', ?_⟩
    have := Λ.add_mem (hO d hd' _ h) (hO c hc' _ h')
    rwa [smul_smul, smul_smul, mul_comm (algebraMap F E d), ← smul_add, ← map_mul] at this
  | smul e a _ ha =>
    obtain ⟨c, hc, hc', h⟩ := ha
    obtain ⟨d, hd, hd', h'⟩ := StdLat.exists_mul_mem L {e}
    refine ⟨c * d, mul_ne_zero hc hd, Subring.mul_mem _ hc' hd', ?_⟩
    have := Λ.smul_mem (⟨_, h' e (by simp)⟩ : L.O) h
    have e1 : algebraMap F E (c * d) • e • a = (algebraMap F E d * e) • algebraMap F E c • a := by
      rw [smul_smul, smul_smul, map_mul]; congr 1; ring
    rw [e1]; exact this
end GlobalTheory.HL.DatumStab

-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:41.259383+00:00
-- url     : https://prove2.me/submissions/236a6dac-e1dd-405d-bd5a-2314ebe74caf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) {n : ℕ} (x : Fin n → E) : x ∈ stdLat L n ↔ ∀ i, x i ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      show (Pi.single j 1 : Fin n → E) i ∈ L.O
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => intro i; exact zero_mem _
    | add u v _ _ hu hv => intro i; exact add_mem (hu i) (hv i)
    | smul c u _ hu =>
      intro i
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hu i)
  · intro hx
    have hsum : x = ∑ i, (⟨x i, hx i⟩ : L.O) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.HL.Inhab

-- Prove2me | solution 1 for GlobalTheory.HL.SAN.mem_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:11.704051+00:00
-- url     : https://prove2.me/submissions/e6bf4e9f-783b-49fd-917f-4fc1004ca1bb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SAN
namespace _root_.GlobalTheory.HL.SAN
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} (x : Fin N → E) :
    x ∈ Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin N → E)) ↔ ∀ j, x j ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro j
      by_cases h : j = i
      · subst h; simp [L.O.one_mem]
      · simp [Pi.single_apply, h, L.O.zero_mem]
    | zero => intro j; exact L.O.zero_mem
    | add y z _ _ hy hz => intro j; exact add_mem (hy j) (hz j)
    | smul c y _ hy =>
      intro j
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hy j)
  · intro hx
    have hsum : x = ∑ j, (⟨x j, hx j⟩ : L.O) • (Pi.single j 1 : Fin N → E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end _root_.GlobalTheory.HL.SAN
end GlobalTheory.HL.SAN

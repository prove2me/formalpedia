-- Prove2me | solution 1 for GlobalTheory.HL.span_pointwise_le_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:50.338982+00:00
-- url     : https://prove2.me/submissions/f9ae3809-0c9e-4df5-80bb-e22c52c0a416

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemStabilizerSpanIffUnitriangularIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E)
    (h : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E) (hM : IsIntM L M)
    (hv : ∀ b, h (v b) = ∑ a, M a b • v a) :
    h • Submodule.span L.O (Set.range v) ≤ Submodule.span L.O (Set.range v) := by
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  show h (v b) ∈ _
  rw [hv b]
  refine Submodule.sum_mem _ fun a _ => ?_
  have : M a b • v a = (⟨M a b, hM a b⟩ : L.O) • v a := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
end GlobalTheory.HL

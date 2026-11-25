-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.frame_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:12.352688+00:00
-- url     : https://prove2.me/submissions/3c923864-5929-4ec5-8405-3821c3d25796

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_span_le
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution {m : ℕ} (f : Fin m → V) (hf : LinearIndependent E f) (N : Subgroup (V ≃ₗ[E] V))
    (hN : ∀ n ∈ N, ∃ s : Matrix (Fin m) (Fin m) E, IsUni s ∧ ∀ j, n (f j) = ∑ i, s i j • f i)
    (n : V ≃ₗ[E] V) (hn : n ∈ N) :
    LinearIndependent E (fun b => n (f b)) ∧
      Submodule.span E (Set.range fun b => n (f b)) = Submodule.span E (Set.range f) ∧
      ∀ h ∈ N, ∃ s : Matrix (Fin m) (Fin m) E, IsUni s ∧ ∀ j, h (n (f j)) = ∑ i, s i j • n (f i) := by
  have key : ∀ h ∈ N, ∃ s : Matrix (Fin m) (Fin m) E, IsUni s ∧
      ∀ j, h (n (f j)) = ∑ i, s i j • n (f i) := by
    intro h hh
    obtain ⟨s, hs, e⟩ := hN (n⁻¹ * h * n) (N.mul_mem (N.mul_mem (N.inv_mem hn) hh) hn)
    refine ⟨s, hs, fun j => ?_⟩
    have h1 : h (n (f j)) = n ((n⁻¹ * h * n) (f j)) := (n.apply_symm_apply _).symm
    rw [h1, e]; simp
  refine ⟨hf.map' n.toLinearMap n.ker, le_antisymm ?_ ?_, key⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s, -, e⟩ := hN n hn
    show n (f j) ∈ Submodule.span E (Set.range f)
    rw [e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s, -, e⟩ := key n⁻¹ (N.inv_mem hn)
    have h1 : f j = n⁻¹ (n (f j)) := (n.symm_apply_apply _).symm
    show f j ∈ Submodule.span E (Set.range fun b => n (f b))
    rw [h1, e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
end GlobalTheory.HL.FrameStabLat

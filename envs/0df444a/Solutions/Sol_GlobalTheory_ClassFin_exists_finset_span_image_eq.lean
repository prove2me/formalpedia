-- Prove2me | solution 1 for GlobalTheory.ClassFin.exists_finset_span_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:09.519487+00:00
-- url     : https://prove2.me/submissions/6298a32c-1bb9-4117-bee4-4cda1dc3debd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsometryMatrixRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsLogKronecker
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsConjHarmOfSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SsTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsCompletelyReducibleKroneckerOfSpanEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution {G V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : G → V) : ∃ T : Finset G, ∀ S : Set G, (T : Set G) ⊆ S →
      Submodule.span ℂ (f '' S) = Submodule.span ℂ (Set.range f) := by
  classical
  have h : (Submodule.span ℂ (Set.range f)).FG := Submodule.FG.of_finite
  obtain ⟨s, hs, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 h
  have hs' : (s : Set V) ⊆ f '' Set.univ := by simpa using hs
  obtain ⟨T, -, hT⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨T, fun S hS => le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩
  rw [hsp, ← hT, Finset.coe_image]
  exact Submodule.span_mono (Set.image_mono hS)
end GlobalTheory.ClassFin

-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:12.233562+00:00
-- url     : https://prove2.me/submissions/3fa44925-1313-4cd6-b1da-ae035899543e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_VolumeFlatSection
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
open scoped NNReal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
variable {k A D D'}
namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
theorem _root_.solution {g : GL (A ⊕ D) k} : g ∈ parahoric k A D ↔
    g ∈ KO k (A ⊕ D) ∧ ∀ i j, valuation k (g.1 (.inr i) (.inl j)) < 1 := by
  have hl : ∀ x : A, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D))) (Sum.inl x) = false := by
    intro x
    have e : (Sum.inl x : A ⊕ D) = GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D)) ⟨false, x⟩ := by simp
    rw [e, GlobalTheory.SmGL.blk_apply]
  have hr : ∀ x : D, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D))) (Sum.inr x) = true := by
    intro x
    have e : (Sum.inr x : A ⊕ D) = GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D)) ⟨true, x⟩ := by simp
    rw [e, GlobalTheory.SmGL.blk_apply]
  have hval : ∀ z : 𝒪[k], IsLocalRing.residue 𝒪[k] z = 0 ↔ valuation k (z : k) < 1 := by
    intro z
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨h, rfl⟩, fun i j => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_parab] at hh
    have h0 := hh (Sum.inr i) (Sum.inl j) (by rw [hl, hr]; decide)
    simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply] at h0 ⊢
    exact (hval _).mp h0
  · rintro ⟨⟨h, rfl⟩, hv⟩
    refine ⟨h, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_parab]
    intro i j hij
    rcases i with i | i <;> rcases j with j | j <;> simp only [hl, hr, lt_self_iff_false] at hij
    · exact absurd hij (by decide)
    · have h0 := hv i j
      simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply] at h0 ⊢
      exact (hval _).mpr h0
end GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection

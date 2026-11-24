-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.Fnf.exists_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:33:50.379956+00:00
-- url     : https://prove2.me/submissions/dbc65b93-6e7a-4b83-adbf-41d1c206868a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_isCompact_sup
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_isCompact_finset_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.Fnf
namespace GlobalTheory.JR.WeilQuad.Fnf
theorem _root_.solution {F V : Type} [NontriviallyNormedField F] [AddCommGroup V] [Module F V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul F V]
    (Λ₀ : AddSubgroup V) (ho : IsOpen (Λ₀ : Set V)) (hc : IsCompact (Λ₀ : Set V)) (C : Set V)
    (hC : IsCompact C) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ₀ ≤ Λ ∧ C ⊆ Λ := by
  obtain ⟨c, hc1⟩ := NormedField.exists_one_lt_norm F
  have hc0 : c ≠ 0 := norm_pos_iff.1 (one_pos.trans hc1)
  let S : ℕ → AddSubgroup V := fun n => (c ^ n) • Λ₀
  have hS : ∀ n, (S n : Set V) = (c ^ n) • (Λ₀ : Set V) := fun n => AddSubgroup.coe_pointwise_smul _ _
  have hSo : ∀ n, IsOpen (S n : Set V) := fun n => by rw [hS]; exact ho.smul₀ (pow_ne_zero _ hc0)
  have hSc : ∀ n, IsCompact (S n : Set V) := fun n => by rw [hS]; exact hc.smul _
  have hcov : C ⊆ ⋃ n, (S n : Set V) := by
    intro y _
    have ht : Tendsto (fun n : ℕ => (c⁻¹) ^ n • y) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (c⁻¹) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc1)
      simpa using h1.smul_const y
    obtain ⟨n, hn⟩ := (ht.eventually (ho.mem_nhds Λ₀.zero_mem)).exists
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rw [hS]
    refine ⟨(c⁻¹) ^ n • y, hn, ?_⟩
    simp [smul_smul, mul_inv_cancel₀ (pow_ne_zero n hc0)]
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun n => (S n : Set V)) hSo hcov
  refine ⟨Λ₀ ⊔ t.sup S, AddSubgroup.isOpen_mono le_sup_left ho,
    isCompact_sup _ _ hc (isCompact_finset_sup t S hSc), le_sup_left, ?_⟩
  intro y hy
  obtain ⟨n, hn, hy'⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact (le_sup_right : t.sup S ≤ Λ₀ ⊔ t.sup S) (Finset.le_sup (f := S) hn hy')
end GlobalTheory.JR.WeilQuad.Fnf

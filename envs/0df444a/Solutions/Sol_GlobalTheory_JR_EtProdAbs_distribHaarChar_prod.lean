-- Prove2me | solution 1 for GlobalTheory.JR.EtProdAbs.distribHaarChar_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:34.386393+00:00
-- url     : https://prove2.me/submissions/e7d7ed31-f585-44fe-aa27-14553581595d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtProdAbs
namespace GlobalTheory.JR.EtProdAbs
theorem _root_.solution {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [LocallyCompactSpace R₁] [T2Space R₁] [SecondCountableTopology R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    [LocallyCompactSpace R₂] [T2Space R₂] [SecondCountableTopology R₂] (v : (R₁ × R₂)ˣ) :
    distribHaarChar (R₁ × R₂) v =
      distribHaarChar R₁ (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v) *
        distribHaarChar R₂ (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v) := by
  borelize R₁ R₂
  let μ₁ : Measure R₁ := Measure.addHaar
  let μ₂ : Measure R₂ := Measure.addHaar
  obtain ⟨S₁⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₁) := inferInstance
  obtain ⟨S₂⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₂) := inferInstance
  have h0₁ : μ₁ (S₁ : Set R₁) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₁ S₁.interior_nonempty).ne'
  have h0₂ : μ₂ (S₂ : Set R₂) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₂ S₂.interior_nonempty).ne'
  have h1₁ : μ₁ (S₁ : Set R₁) ≠ ⊤ := S₁.isCompact.measure_lt_top.ne
  have h1₂ : μ₂ (S₂ : Set R₂) ≠ ⊤ := S₂.isCompact.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ₁.prod μ₂) (s := (S₁ : Set R₁) ×ˢ (S₂ : Set R₂))
    (by rw [Measure.prod_prod]; exact mul_ne_zero h0₁ h0₂)
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top h1₁ h1₂) ?_
  have hs : v • ((S₁ : Set R₁) ×ˢ (S₂ : Set R₂)) =
      (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v • (S₁ : Set R₁)) ×ˢ
        (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v • (S₂ : Set R₂)) := by
    ext ⟨x, y⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_prod, Set.mem_prod, Set.mem_smul_set_iff_inv_smul_mem,
      Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, ← map_inv]
    exact Iff.rfl
  rw [hs, Measure.prod_prod, Measure.prod_prod, ← distribHaarChar_mul μ₁, ← distribHaarChar_mul μ₂]
  push_cast
  ring
end GlobalTheory.JR.EtProdAbs

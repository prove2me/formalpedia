-- Prove2me | solution 1 for GlobalTheory.JR.ModuleNorm.distribHaarChar_transport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:34.633528+00:00
-- url     : https://prove2.me/submissions/c6c4d2d5-72a9-499c-9e72-c646de544ecb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ModuleNorm
namespace GlobalTheory.JR.ModuleNorm
theorem _root_.solution {G H A B : Type} [Group G] [Group H]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
    [T2Space B] [SecondCountableTopology B] [DistribMulAction H B] [ContinuousConstSMul H B]
    (e : A ≃ₜ+ B) (g : G) (h : H) (he : ∀ x, e (g • x) = h • e x) :
    distribHaarChar B h = distribHaarChar A g := by
  borelize A B
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hmap : ∀ s : Set B, ((Measure.addHaar : Measure A).map e) s = (Measure.addHaar : Measure A) (e ⁻¹' s) :=
    fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  have key : ∀ x, h⁻¹ • e x = e (g⁻¹ • x) := fun x => by
    rw [inv_smul_eq_iff, ← he, smul_inv_smul]
  have hpre : e ⁻¹' (e.symm ⁻¹' K) = K := by
    ext x; simp
  have hpre2 : e ⁻¹' (h • e.symm ⁻¹' K) = g • K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, key]
    simp
  have h0' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ 0 := by rw [hmap, hpre]; exact h0
  have hT' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ ⊤ := by rw [hmap, hpre]; exact hT
  apply ENNReal.coe_injective
  rw [distribHaarChar_eq_div h0' hT', distribHaarChar_eq_div h0 hT, hmap, hmap, hpre, hpre2]
end GlobalTheory.JR.ModuleNorm

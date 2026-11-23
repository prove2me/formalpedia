-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.FieldIdem.map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:01.791256+00:00
-- url     : https://prove2.me/submissions/5c4f3809-74b4-49c4-a607-3d15b0a9e3df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open Classical
variable {R : Type} [CommRing R]
namespace GlobalTheory.UnitLemma.Desc
namespace FieldIdem
theorem _root_.solution {u : R} (hu : FieldIdem u) (σ : R ≃+* R) : FieldIdem (σ u) := by
  refine ⟨?_, ?_, ?_⟩
  · show σ u * σ u = σ u
    rw [← map_mul, hu.1.eq]
  · intro h0
    exact hu.2.1 (σ.injective (by rw [h0, map_zero]))
  · intro y hy
    have hy' : u * σ.symm y ≠ 0 := by
      intro h0
      apply hy
      have h1 := congrArg σ h0
      rwa [map_mul, RingEquiv.apply_symm_apply, map_zero] at h1
    obtain ⟨z, hz⟩ := hu.2.2 _ hy'
    refine ⟨σ z, ?_⟩
    have h1 := congrArg σ hz
    rwa [map_mul, map_mul, RingEquiv.apply_symm_apply] at h1
end FieldIdem
end GlobalTheory.UnitLemma.Desc

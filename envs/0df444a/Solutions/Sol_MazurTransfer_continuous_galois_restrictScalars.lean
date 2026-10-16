-- Prove2me | solution 1 for MazurTransfer.continuous_galois_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T07:48:58.933729+00:00
-- url     : https://prove2.me/submissions/03a550a8-3e39-4933-909c-17c4c002fa14

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: standalone exact public Krull-continuity proof at default limits.
Named downstream consumer: actual thirteenth-cyclotomic pi-character extensions. -/
import Mathlib
open scoped Topology

noncomputable section
theorem solution (R K Ω : Type) [Field R] [Field K] [Field Ω]
    [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsAlgebraic K Ω] :
    Continuous (AlgEquiv.restrictScalarsHom R : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[R] Ω)) := by
  classical
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hE, hN⟩ := hN
  letI : FiniteDimensional R E := hE
  let b := Module.finBasis R E
  let B : Finset Ω := Finset.univ.image (fun i => (b i : Ω))
  let J : IntermediateField K Ω := IntermediateField.adjoin K (B : Set Ω)
  have hJ : FiniteDimensional K J :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral)
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨J, hJ, ?_⟩
  intro σ hσ
  apply hN
  change σ.restrictScalars R ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ ∈ J.fixingSubgroup at hσ
  have hs : ∀ y ∈ J, σ y = y := by
    rw [← IntermediateField.mem_fixingSubgroup_iff]
    exact hσ
  have he : (σ.restrictScalars R).toLinearMap.comp E.val.toLinearMap = E.val.toLinearMap := by
    apply b.ext
    intro i
    exact hs (b i) (IntermediateField.subset_adjoin K (B : Set Ω)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  exact LinearMap.congr_fun he ⟨x, hx⟩

#print axioms solution

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitProdAlg.map_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:47.901472+00:00
-- url     : https://prove2.me/submissions/f2b541f7-60a6-4d58-b6c6-713986740933

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_mulSupport_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitProdAlg
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg
theorem _root_.solution (f : ℝ≥0 →* ℝ≥0) {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) : IsUnitProd (f a) (fun v => f (c v)) := by
  have hfin := mulSupport_finite h
  refine ⟨h.1.mono fun v hv => by simp [hv], ?_⟩
  have hsub : Function.mulSupport (fun v => f (c v)) ⊆ (hfin.toFinset : Set _) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    exact hv (by simp [h1])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← map_prod, ← map_mul,
    ← finprod_eq_prod_of_mulSupport_subset c (by simp), h.2, map_one]
end GlobalTheory.CompanionTheory.SW.UnitProdAlg

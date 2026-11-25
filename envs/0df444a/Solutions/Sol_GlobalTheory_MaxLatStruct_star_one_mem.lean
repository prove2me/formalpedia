-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.star_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:23:42.790877+00:00
-- url     : https://prove2.me/submissions/4a0707e8-a7df-4525-8477-ac6f6aabb020

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_alg_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule R V} {σ : R →+* R}
omit [IsDedekindDomain R] [IsFractionRing R K]
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) {a : K}
    (ha : a ∈ (1 : Submodule R K)) : star a ∈ (1 : Submodule R K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
  rw [← hσ]; exact locDual_alg_mem _
end GlobalTheory.MaxLatStruct

-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:51.782571+00:00
-- url     : https://prove2.me/submissions/bdc94f32-5dfa-43e7-82ec-10291eb8c897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_conj_eq
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_sigma_spec


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
omit [IsDedekindDomain R]
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (P : Ideal R) (r : R) :
    r ∈ conjIdeal (K := K) P ↔ σ r ∈ P := by
  have hinj := IsFractionRing.injective R K
  have hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K) := fun r => ⟨σ r, hσ r⟩
  rw [locBasic_conj_eq hinj hstar, Ideal.mem_comap]
  have : locBasic_sigma hinj hstar r = σ r := hinj (by rw [locBasic_sigma_spec, hσ])
  rw [this]
end GlobalTheory.MaxLatStruct

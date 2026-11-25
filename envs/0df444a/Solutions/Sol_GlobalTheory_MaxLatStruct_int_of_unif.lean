-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.int_of_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:22:43.848905+00:00
-- url     : https://prove2.me/submissions/245df200-d4f0-4832-a8c9-120d7c87c5d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_alg_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_one_mul


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
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution {P : Ideal R} (hP : P.IsMaximal) {π b : R} (h1 : π ∈ P) (h2 : π ∉ P ^ 2) {α : K}
    (hα : ∀ p ∈ P, algebraMap R K p * α ∈ (1 : Submodule R K)) (hb : b ∈ P)
    (e : algebraMap R K π * α = algebraMap R K b) : α ∈ (1 : Submodule R K) := by
  have hπ0 : π ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
  obtain ⟨I, hI⟩ : P ∣ Ideal.span {π} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact h1
  have hIP : ¬ I ≤ P := by
    intro hle
    apply h2
    have : Ideal.span {π} ≤ P ^ 2 := by rw [hI, sq]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨i, hi, hiP⟩ := Set.not_subset.1 hIP
  obtain ⟨r, p, hp, hrp⟩ := hP.exists_inv hiP
  have hbi : b * i ∈ Ideal.span {π} := by rw [hI]; exact Ideal.mul_mem_mul hb hi
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hbi
  have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0
  have hiα : algebraMap R K i * α = algebraMap R K c := by
    apply mul_left_cancel₀ hπK
    rw [mul_left_comm, e, ← map_mul, ← map_mul, mul_comm i b, ← hc, mul_comm]
  have : α = algebraMap R K r * (algebraMap R K i * α) + algebraMap R K p * α := by
    rw [← mul_assoc, ← add_mul, ← map_mul, ← map_add, hrp, map_one, one_mul]
  rw [this, hiα]
  exact Submodule.add_mem _ (locDual_one_mul (locDual_alg_mem r) (locDual_alg_mem c)) (hα p hp)
end GlobalTheory.MaxLatStruct

-- Prove2me | solution 1 for GlobalTheory.JR.Et.quadratic_structure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:10.718807+00:00
-- url     : https://prove2.me/submissions/59204b3a-6325-46e0-abd8-19dd4544dead

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Theorems.Thm_GlobalTheory_JR_Unram_exists_basis_antifixed
import Theorems.Thm_GlobalTheory_JR_quadratic_star_structure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
namespace Et
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nonempty (Module.Basis (Fin 2) A.K A.L) ∧ Function.Injective (algebraMap A.K A.L) ∧ (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (∀ y' : A.L, (∀ y : A.L, Algebra.trace A.K A.L (star y' * y) = 0) → y' = 0) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  let B : Module.Basis (Fin 2) A.K A.L := A.push.symm.out.basis b
  have hB : ∀ i, B i = algebraMap E A.L (b i) := fun i => by
    simp [B, IsBaseChange.basis_apply]
  have key := quadratic_star_structure B (algebraMap F A.K d) (by rw [hB, hb0, map_one])
    (by rw [hB, A.star_E, hs, map_neg])
    (by
      rw [hB, ← map_mul, hd, ← IsScalarTower.algebraMap_apply F E A.L,
        ← IsScalarTower.algebraMap_apply F A.K A.L])
    A.star_K ((isUnit_iff_ne_zero.mpr hd0).map _)
    (by
      have h2F := (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : F) ≠ 0)).map (algebraMap F A.K)
      rwa [map_ofNat] at h2F)
  exact ⟨⟨B⟩, key.1, key.2.1, key.2.2.1, key.2.2.2⟩
end Et
end GlobalTheory.JR

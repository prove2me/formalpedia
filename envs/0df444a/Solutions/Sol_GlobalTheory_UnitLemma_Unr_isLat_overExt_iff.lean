-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.isLat_overExt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:50.22489+00:00
-- url     : https://prove2.me/submissions/10c044a4-ddac-4e00-81ba-67b99bf43842

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIff
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_isLat_iff_of_coe_eq
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_eq_base_mul_int
import Theorems.Thm_GlobalTheory_T_exists_integer_spanning_family_of_unramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by
  intro K K' d φ hU B ψ hψ hσ L M h
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt K K' d φ hU
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  have hO' : ∀ b : K'.O, algebraMap K'.O B.A b = ψ (algebraMap K'.O K'.E b) := fun _ => rfl
  have hE' : ∀ b : K'.E, algebraMap K'.E B.A b = ψ b := fun _ => rfl
  have hO : ∀ a : K.O, algebraMap K.O B.A a = ψ (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hψ, ← IsScalarTower.algebraMap_apply]
  have key := isLat_iff_of_coe_eq (O := K.O) (O' := K'.O) (E := K.E) (E' := K'.E) (A := B.A) u ?_ ?_ ?_ ?_
  · exact key L M h
  · intro a
    obtain ⟨b, hb⟩ := exists_int_image hU a
    exact ⟨b, by rw [hO', hO, hb]⟩
  · intro y
    obtain ⟨a, ha⟩ := hu y
    refine ⟨a, ?_⟩
    rw [hO', ha, map_sum]
    simp only [map_mul, hO, hO']
  · intro e
    exact ⟨φ e, by rw [hE', hψ]⟩
  · intro z
    obtain ⟨e, b, hb⟩ := exists_eq_base_mul_int hU z
    exact ⟨e, b, by rw [hE', hO', ← hψ, ← map_mul, ← hb]⟩
end GlobalTheory.UnitLemma.Unr

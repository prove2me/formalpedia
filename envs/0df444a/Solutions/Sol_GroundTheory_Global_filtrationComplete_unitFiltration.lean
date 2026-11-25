-- Prove2me | solution 1 for GroundTheory.Global.filtrationComplete_unitFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:16.822183+00:00
-- url     : https://prove2.me/submissions/6e4c994c-e735-4b65-b373-cfc71eb158cd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_div_mem_unitFiltration_iff
import Theorems.Thm_GroundTheory_Global_isAdicComplete_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.Global
theorem _root_.solution : FiltrationComplete (unitFiltration K) := by
  have hc := (isAdicComplete_integer (K := K)).toIsPrecomplete
  intro x hx
  choose M hM using hx

  let M' : ℕ → ℕ := fun N ↦ (Finset.range (N + 1)).sup M
  have hM'ge : ∀ N, M N ≤ M' N := fun N ↦ Finset.le_sup (Finset.self_mem_range_succ N)
  have hM'mono : Monotone M' := fun a b hab ↦
    Finset.sup_mono (Finset.range_subset_range.2 (by omega))
  have hy : ∀ {a b : ℕ}, a ≤ b →
      ((x (M' a) : 𝒪[K]) ≡ x (M' b) [SMOD (𝓂[K] ^ a • ⊤ : Submodule 𝒪[K] 𝒪[K])]) := by
    intro a b hab
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact div_mem_unitFiltration_iff.mp
      (hM a (M' b) ((hM'ge a).trans (hM'mono hab)) (M' a) (hM'ge a))
  obtain ⟨L, hL⟩ := hc.prec' (fun N ↦ (x (M' N) : 𝒪[K])) hy
  have hL' : ∀ N, (x (M' N) : 𝒪[K]) - L ∈ 𝓂[K] ^ N := fun N ↦ by
    have := hL N
    rwa [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at this
  have hLu : IsUnit L := by
    by_contra hL0
    have h1 : L ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal L).mpr hL0
    have h2 := hL' 1
    rw [pow_one] at h2
    have : (x (M' 1) : 𝒪[K]) ∈ 𝓂[K] := by
      simpa using Ideal.add_mem _ h2 h1
    exact (IsLocalRing.mem_maximalIdeal _).mp this (x (M' 1)).isUnit
  refine ⟨hLu.unit, fun N ↦ ⟨M' N, fun n hn ↦ ?_⟩⟩
  rw [div_mem_unitFiltration_iff, IsUnit.unit_spec]
  have h1 : (x n : 𝒪[K]) - x (M' N) ∈ 𝓂[K] ^ N :=
    div_mem_unitFiltration_iff.mp (hM N (M' N) (hM'ge N) n ((hM'ge N).trans hn))
  have := Ideal.add_mem _ h1 (hL' N)
  rwa [sub_add_sub_cancel] at this
end GroundTheory.Global

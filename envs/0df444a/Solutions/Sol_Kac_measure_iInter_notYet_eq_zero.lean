-- Prove2me | solution 1 for Kac.measure_iInter_notYet_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:49:34.700984+00:00
-- url     : https://prove2.me/submissions/fb2605ee-d0ed-4e60-ad5e-fc3f30fbda79

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_mem_notYet_iff
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
variable [IsFiniteMeasure μ]
namespace Kac
theorem _root_.solution (hf : Ergodic f μ) (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    μ (⋂ n, notYet f A n) = 0 := by
  have hfm := hf.toMeasurePreserving.measurable
  -- the points meeting `A` infinitely often form a strictly invariant set
  set V : Set α := ⋂ m : ℕ, ⋃ n ∈ {n : ℕ | m ≤ n}, f^[n] ⁻¹' A with hV
  have hVmeas : MeasurableSet V :=
    MeasurableSet.iInter fun m => MeasurableSet.biUnion (to_countable _)
      fun n _ => (hfm.iterate n) hA
  have hVmem : ∀ x, x ∈ V ↔ ∃ᶠ n in atTop, f^[n] x ∈ A := by
    intro x
    simp only [hV, mem_iInter, mem_iUnion, mem_ofPred_eq, mem_preimage, frequently_atTop,
      exists_prop]
  have hVinv : f ⁻¹' V = V := by
    ext x
    simp only [mem_preimage, hVmem, frequently_atTop]
    constructor
    · intro h m
      obtain ⟨n, hn, hmem⟩ := h m
      exact ⟨n + 1, by omega, by rwa [Function.iterate_succ_apply]⟩
    · intro h m
      obtain ⟨n, hn, hmem⟩ := h (m + 1)
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact ⟨n', by omega, by rwa [Function.iterate_succ_apply] at hmem⟩
  -- Poincaré recurrence puts almost all of `A` inside `V`, so `V` is not null
  have hAV : A ≤ᵐ[μ] V := by
    filter_upwards [hf.toMeasurePreserving.conservative.ae_mem_imp_frequently_image_mem
      hA.nullMeasurableSet] with x hx hxA
    exact (hVmem x).mpr (hx hxA)
  have hVne : μ V ≠ 0 := fun hzero => hA0 (measure_mono_null_ae hAV hzero)
  -- ergodicity then makes it conull
  have hVc : μ Vᶜ = 0 :=
    (hf.toPreErgodic.measure_self_or_compl_eq_zero hVmeas
      (by rw [hVinv])).resolve_left hVne
  refine measure_mono_null (fun x hx => ?_) hVc
  simp only [mem_iInter] at hx
  simp only [mem_compl_iff, hVmem, frequently_atTop, not_forall, not_exists, not_and]
  exact ⟨0, fun n _ hmem => (mem_notYet_iff (n + 1) x).mp (hx (n + 1)) n (by omega) hmem⟩
end Kac

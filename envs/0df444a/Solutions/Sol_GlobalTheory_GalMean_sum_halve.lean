-- Prove2me | solution 1 for GlobalTheory.GalMean.sum_halve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:24:34.734271+00:00
-- url     : https://prove2.me/submissions/a77c925b-9343-44fb-a0ee-eb3185e9d968

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses
import Theorems.Thm_GlobalTheory_GalMean_emb_two
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open Classical
namespace GlobalTheory.GalMean
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (hK2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (L : IntermediateField ℚ ℂ) [NumberField L] (hK : ∀ x : K, φK x ∈ L)
    (f : (L →+* ℂ) → ℝ) (hf : ∀ τ, f ((starRingEnd ℂ).comp τ) = f τ) :
    ∑ τ : L →+* ℂ, f τ =
      2 * ∑ τ ∈ Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x), f τ := by
  classical
  set P : (L →+* ℂ) → Prop := fun τ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x with hPdef
  set c : (L →+* ℂ) → (L →+* ℂ) := fun τ => (starRingEnd ℂ).comp τ with hcdef
  have hcc : ∀ τ, c (c τ) = τ := fun τ => RingHom.ext fun x => by simp [c]
  have key : ∀ τ, ¬ P τ ↔ P (c τ) := by
    intro τ
    let g : K →+* ℂ := τ.comp (φK.codRestrict L hK)
    have hP : P τ ↔ g = φK := ⟨fun h => RingHom.ext fun x => h x, fun h x => RingHom.congr_fun h x⟩
    have hPc : P (c τ) ↔ (starRingEnd ℂ).comp g = φK :=
      ⟨fun h => RingHom.ext fun x => h x, fun h x => RingHom.congr_fun h x⟩
    rw [hP, hPc]
    rcases emb_two φK hK2 hc g with h | h
    · rw [h]; exact iff_of_false (not_not.2 rfl) hc
    · rw [h]; exact iff_of_true hc (RingHom.ext fun x => by simp)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P f, two_mul]
  congr 1
  refine Finset.sum_nbij' c c ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (key a).1 ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (key (c a)).2 (by rw [hcc]; exact ha)
  · intro a _; exact hcc a
  · intro a _; exact hcc a
  · intro a _; exact (hf a).symm
end GlobalTheory.GalMean

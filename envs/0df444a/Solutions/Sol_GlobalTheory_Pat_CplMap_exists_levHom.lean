-- Prove2me | solution 1 for GlobalTheory.Pat.CplMap.exists_levHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:27.514581+00:00
-- url     : https://prove2.me/submissions/b13537a0-eac9-4344-bc29-c39d506ef8aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom
import Theorems.Thm_GlobalTheory_Pat_CplMap_exists_val
import Theorems.Thm_GlobalTheory_Pat_CplMap_val_unique_of_pair
import Theorems.Thm_GlobalTheory_Pat_CplMap_one_notMem
import Theorems.Thm_GlobalTheory_Pat_isCplAt_approx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat GlobalTheory.Pat.CplMap
variable {R S S' : Type} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
  {q : Ideal R} {φ : R →+* S} {ψ : R →+* S'}
variable [hq : q.IsPrime]
namespace GlobalTheory.Pat.CplMap
theorem _root_.solution (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) :
    ∃ f : S →+* S' ⧸ maximalIdeal S' ^ n, ∀ s, IsVal q φ ψ n s (f s) := by
  choose f hf using exists_val hφ hψ n
  have ap := (isCplAt_approx R S q φ hφ n).1
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · exact val_unique_of_pair hψ (hf 1) (a := 1) (b := 1) one_notMem (by simp) (by simp)
  · intro x y
    obtain ⟨a1, b1, hb1, h1⟩ := ap x
    obtain ⟨a2, b2, hb2, h2⟩ := ap y
    have hb : b1 * b2 ∉ q := fun h => (hq.mem_or_mem h).elim hb1 hb2
    refine val_unique_of_pair hψ (hf (x * y)) (a := a1 * a2) hb ?_ ?_
    · have : φ (b1 * b2) * (x * y) - φ (a1 * a2) =
          (φ b1 * x - φ a1) * (φ b2 * y) + φ a1 * (φ b2 * y - φ a2) := by
        simp only [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · simp only [map_mul]
      rw [← hf x a1 b1 hb1 h1, ← hf y a2 b2 hb2 h2]; ring
  · exact val_unique_of_pair hψ (hf 0) (a := 0) (b := 1) one_notMem (by simp) (by simp)
  · intro x y
    obtain ⟨a1, b1, hb1, h1⟩ := ap x
    obtain ⟨a2, b2, hb2, h2⟩ := ap y
    have hb : b1 * b2 ∉ q := fun h => (hq.mem_or_mem h).elim hb1 hb2
    refine val_unique_of_pair hψ (hf (x + y)) (a := a1 * b2 + a2 * b1) hb ?_ ?_
    · have : φ (b1 * b2) * (x + y) - φ (a1 * b2 + a2 * b1) =
          φ b2 * (φ b1 * x - φ a1) + φ b1 * (φ b2 * y - φ a2) := by
        simp only [map_mul, map_add]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · simp only [map_mul, map_add]
      rw [← hf x a1 b1 hb1 h1, ← hf y a2 b2 hb2 h2]; ring
end GlobalTheory.Pat.CplMap

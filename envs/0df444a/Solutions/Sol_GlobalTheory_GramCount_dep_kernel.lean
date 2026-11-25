-- Prove2me | solution 1 for GlobalTheory.GramCount.dep_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:34.926594+00:00
-- url     : https://prove2.me/submissions/a33efa72-0c32-46b4-906e-19a59cb2b74c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
import Theorems.Thm_GlobalTheory_GramCount_cj_ip
import Theorems.Thm_GlobalTheory_GramCount_ip_add_left
import Theorems.Thm_GlobalTheory_GramCount_ip_smul_left
import Theorems.Thm_GlobalTheory_GramCount_ip_sum_left
import Theorems.Thm_GlobalTheory_GramCount_ip_zero_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B]
namespace GlobalTheory.GramCount
theorem _root_.solution (c : B →+* B) (hc : ∀ u, c (c u) = u) {k n : ℕ} (x d : Fin k → Fin n → B)
    (hd : ∀ a b, ip c (x a) (d b) = if a = b then 1 else 0) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) (z : Fin n → B) (ρ s : Fin k → B) (hz : ∀ i, ip c z (x i) = 0)
    (hs : ε • z = ∑ i, s i • x i) (hA : ∀ i, c (ε * ip c z (d i)) + ε * ρ i = 0)
    (hB : ∀ l, (c ε • z + ∑ j, (c ε * ρ j) • d j) l +
      c ((c ε • z + ∑ j, (c ε * ρ j) • d j) l) = 0) : z = 0 ∧ ρ = 0 := by
  have hw : c ε • z + ∑ j, (c ε * ρ j) • d j = c ε • (z + ∑ j, ρ j • d j) := by
    simp only [smul_add, Finset.smul_sum, mul_smul]
  have hw0 : c ε • z + ∑ j, (c ε * ρ j) • d j = 0 := by
    funext l
    have := hB l
    rw [hw] at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hc, Pi.zero_apply] at this ⊢
    set u := (z + ∑ j, ρ j • d j) l
    linear_combination c ε * this - c u * h2 + u * h2 - c ε * u * h1
  have hd' : ∀ a b, ip c (d b) (x a) = if a = b then 1 else 0 := fun a b => by
    rw [← cj_ip c hc, hd]; split_ifs <;> simp
  have hη : ∀ i, c ε * ρ i = 0 := fun i => by
    have := congrArg (fun v => ip c v (x i)) hw0
    simpa [ip_add_left, ip_sum_left, ip_smul_left, hd', hz, ip_zero_left] using this
  have hε : ∀ i, ε * ρ i = 0 := fun i => by
    have := hA i
    rw [map_mul] at this
    linear_combination ε * this - c (ip c z (d i)) * h2 + ρ i * h2 - ε * ρ i * h1
  have hs0 : ∀ i, s i = 0 := fun i => by
    have h3 := hA i
    rw [hε, add_zero] at h3
    have h4 := congrArg c h3
    rw [hc, map_zero] at h4
    have := congrArg (fun v => ip c v (d i)) hs
    simpa [ip_sum_left, ip_smul_left, hd, h4] using this.symm
  refine ⟨?_, funext fun i => ?_⟩
  · simp only [hη, zero_smul, Finset.sum_const_zero, add_zero] at hw0
    simp only [hs0, zero_smul, Finset.sum_const_zero] at hs
    rw [← one_smul B z, ← h1, add_smul, hs, hw0, add_zero]
  · have := hε i
    have := hη i
    simp only [Pi.zero_apply]
    linear_combination hε i + hη i - ρ i * h1
end GlobalTheory.GramCount

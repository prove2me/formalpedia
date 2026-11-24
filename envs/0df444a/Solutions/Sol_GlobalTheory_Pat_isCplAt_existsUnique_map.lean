-- Prove2me | solution 1 for GlobalTheory.Pat.isCplAt_existsUnique_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:34.613466+00:00
-- url     : https://prove2.me/submissions/fa110a23-b4fc-4641-b3a7-adc62610ad11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom
import Theorems.Thm_GlobalTheory_Pat_CplMap_ext_mem_pow
import Theorems.Thm_GlobalTheory_Pat_CplMap_val_unique_of_pair
import Theorems.Thm_GlobalTheory_Pat_CplMap_one_notMem
import Theorems.Thm_GlobalTheory_Pat_CplMap_exists_levHom
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
open GlobalTheory GlobalTheory.Pat
open CplMap
namespace GlobalTheory.Pat
theorem _root_.solution : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing S'] [IsLocalRing S'] [IsAdicComplete (maximalIdeal S') S'] (q : Ideal R) [q.IsPrime]
    (φ : R →+* S) (ψ : R →+* S'), IsCplAt q φ → (maximalIdeal S').comap ψ = q →
    ∃! θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = ψ := by
  intro R S S' _ _ _ _ _ _ q _ φ ψ hφ hψ
  choose f hf using exists_levHom hφ hψ
  have hc : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal S') hle).comp (f n) = f m := by
    intro m n hle
    ext s
    obtain ⟨a, b, hb, h⟩ := (isCplAt_approx R S q φ hφ n).1 s
    refine (val_unique_of_pair hψ (hf m s) hb (Ideal.pow_le_pow_right hle h) ?_).symm
    have e := congrArg (Ideal.Quotient.factorPow (maximalIdeal S') hle) (hf n s a b hb h)
    rw [map_mul] at e
    exact e
  have hcomp : (IsAdicComplete.liftRingHom (maximalIdeal S') f hc).comp φ = ψ := by
    ext r
    refine congrFun (IsHausdorff.funext' (maximalIdeal S')
      (f := fun r => IsAdicComplete.liftRingHom (maximalIdeal S') f hc (φ r)) (g := fun r => ψ r)
      (fun n r => ?_)) r
    rw [IsAdicComplete.mk_liftRingHom]
    exact val_unique_of_pair hψ (hf n (φ r)) (a := r) (b := 1) one_notMem (by simp) (by simp)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal S') f hc, ⟨⟨fun s hs => ?_⟩, hcomp⟩, ?_⟩
  · by_contra hn
    have h1 := ext_mem_pow hφ hψ hcomp 1 (x := s) (by
      rw [pow_one]; exact (mem_maximalIdeal _).mpr hn)
    rw [pow_one] at h1
    exact (mem_maximalIdeal _).mp h1 hs
  · rintro F ⟨-, hF⟩
    refine IsAdicComplete.eq_liftRingHom _ f hc F (fun n => ?_)
    ext s
    obtain ⟨a, b, hb, h⟩ := (isCplAt_approx R S q φ hφ n).1 s
    refine (val_unique_of_pair hψ (hf n s) hb h ?_).symm
    have h1 := ext_mem_pow hφ hψ hF n h
    rw [RingHom.comp_apply, ← map_mul, Ideal.Quotient.eq, ← hF]
    simpa using h1
end GlobalTheory.Pat

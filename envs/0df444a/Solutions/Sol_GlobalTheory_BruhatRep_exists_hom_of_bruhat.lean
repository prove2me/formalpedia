-- Prove2me | solution 1 for GlobalTheory.BruhatRep.exists_hom_of_bruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:39.247898+00:00
-- url     : https://prove2.me/submissions/01b45c9c-e483-414a-9b6d-74d733755e86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_rho_n
import Theorems.Thm_GlobalTheory_BruhatRep_rho_m
import Theorems.Thm_GlobalTheory_BruhatRep_rho_w
import Theorems.Thm_GlobalTheory_BruhatRep_rho_one
import Theorems.Thm_GlobalTheory_BruhatRep_rho_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
namespace GlobalTheory.BruhatRep
theorem _root_.solution : ∀ (K : Type) [CommRing K], IsField K → ∀ (M : Type) [Monoid M] (n : K → M)
    (m : Kˣ → M) (t : M), n 0 = 1 → (∀ a b, n (a + b) = n a * n b) → m 1 = 1 →
    (∀ a b, m (a * b) = m a * m b) → (∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) → t * t = m (-1) →
    (∀ s, t * m s = m s⁻¹ * t) →
    (∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K))) →
    ∃ ρ : SpecialLinearGroup (Fin 2) K →* M, (∀ z, ρ (nS z) = n z) ∧ (∀ s, ρ (mS s) = m s) ∧ ρ (wS K) = t := by
  intro K _ hK M _ n m t hn0 hn hm1 hm hmn htt htm htnt
  letI := hK.toField
  let ρ : SpecialLinearGroup (Fin 2) K →* M :=
    { toFun := rho n m t
      map_one' := rho_one n m t hn0 hm1
      map_mul' := rho_mul n m t hn0 hn hm hmn htt htm htnt }
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro z
    have := rho_n n m t hn 1 z
    rw [one_mul, rho_one n m t hn0 hm1, one_mul] at this
    exact this
  · intro s
    have := rho_m n m t hm hmn htm 1 s
    rw [one_mul, rho_one n m t hn0 hm1, one_mul] at this
    exact this
  · have := rho_w n m t hn0 hn hm hmn htt htnt 1
    rw [one_mul, rho_one n m t hn0 hm1, one_mul] at this
    exact this
end GlobalTheory.BruhatRep

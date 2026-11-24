-- Prove2me | solution 1 for GlobalTheory.exists_root_lift_of_residue_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:38:49.684503+00:00
-- url     : https://prove2.me/submissions/ff662873-08dd-4f4f-8669-7f742fdaeeb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHenselRootResidue
import Theorems.Thm_GlobalTheory_residue_eval_map_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V]
      [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V)
      (σ : ResidueField R →+* ResidueField V),
      (∀ a, σ (residue R (φ a)) = residue V (α a)) → ∀ (θ : R) (q : Polynomial A), q.Monic →
      (q.map φ).eval θ = 0 → IsUnit ((q.derivative.map φ).eval θ) →
      ∃ η : V, (q.map α).eval η = 0 ∧ residue V η = σ (residue R θ) := by
  intro A R V _ _ _ _ _ _ _ φ α σ hσ θ q hq h0 hu
  obtain ⟨η₀, hη₀⟩ := residue_surjective (σ (residue R θ))
  have hcomp : (residue V).comp α = σ.comp ((residue R).comp φ) := by
    ext a; simp [hσ]
  have key : ∀ p : A[X], residue V ((p.map α).eval η₀) = σ (residue R ((p.map φ).eval θ)) := by
    intro p
    rw [residue_eval_map_comm, hcomp, hη₀, residue_eval_map_comm p φ (residue R),
      residue_eval_map_comm _ _ σ]
  have hm : (q.map α).Monic := hq.map α
  have h1 : (q.map α).eval η₀ ∈ maximalIdeal V := by
    rw [← residue_eq_zero_iff, key, h0, map_zero, map_zero]
  have h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal V) ((q.map α).derivative.eval η₀)) := by
    have : (Ideal.Quotient.mk (maximalIdeal V) ((q.map α).derivative.eval η₀)) =
        σ (residue R ((q.derivative.map φ).eval θ)) := by
      rw [derivative_map]; exact key _
    rw [this]
    exact (hu.map (residue R)).map σ
  obtain ⟨η, hη, hηm⟩ := HenselianRing.is_henselian (I := maximalIdeal V) _ hm η₀ h1 h2
  refine ⟨η, hη, ?_⟩
  rw [← hη₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hηm
end GlobalTheory

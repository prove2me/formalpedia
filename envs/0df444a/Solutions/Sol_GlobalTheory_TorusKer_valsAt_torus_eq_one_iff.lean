-- Prove2me | solution 1 for GlobalTheory.TorusKer.valsAt_torus_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:10.749896+00:00
-- url     : https://prove2.me/submissions/c8bc2a69-f14b-4846-8732-746e3f6e3e26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ZValuationsAtIndicesTorusEqOneIff
import Theorems.Thm_GlobalTheory_UnitLemma_valsAt_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma
open GlobalTheory GlobalTheory.TorusKer
namespace GlobalTheory.TorusKer
theorem _root_.solution (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G)
    (hT : ∀ t, t ∈ T ↔ t * τ t = 1) (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ)
    (hs : ∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x)))
    (r : ℕ) (e : Fin r → ι) (hcov : ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) (t : T) :
    (valsAt w e).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  have hinv : ∀ i (x : G), Multiplicative.toAdd (w i x⁻¹) = - Multiplicative.toAdd (w i x) := by
    intro i x; rw [map_inv, toAdd_inv]
  have hτ : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT t).1 t.2)
  have hτ' : τ ((t : G)⁻¹) = (t : G) := by rw [map_inv, hτ, inv_inv]
  constructor
  · intro h
    have he : ∀ j, Multiplicative.toAdd (w (e j) (t : G)) = 0 := by
      intro j
      have := congrArg (fun y : Multiplicative (Fin r → ℤ) => Multiplicative.toAdd y j) h
      simpa [valsAt_apply] using this
    intro i
    rcases hcov i with hi | ⟨j, hj | hj⟩
    · have h1 := hs i (t : G)
      rw [hi, hτ, hinv] at h1
      omega
    · subst hj; exact he j
    · subst hj
      have h1 := hs (e j) (t : G)
      have h2 := hs (e j) ((t : G)⁻¹)
      rw [hτ, hinv, he j] at h1
      rw [hτ', he j, hinv] at h2
      omega
  · intro h
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [valsAt_apply, h]
    rfl
end GlobalTheory.TorusKer

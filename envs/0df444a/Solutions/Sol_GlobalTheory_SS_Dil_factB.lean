-- Prove2me | solution 1 for GlobalTheory.SS.Dil.factB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:53:36.980132+00:00
-- url     : https://prove2.me/submissions/c822bc81-4ae5-4f45-97b5-f6e9e913b071

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
import Theorems.Thm_GlobalTheory_SS_Dil_span_d
import Theorems.Thm_GlobalTheory_SS_Dil_dd_add
import Theorems.Thm_GlobalTheory_SS_Dil_dd_mul
import Theorems.Thm_GlobalTheory_SS_Dil_dd_algebraMap
import Theorems.Thm_GlobalTheory_SS_Dil_dd_zero
import Theorems.Thm_GlobalTheory_SS_Dil_chain
import Theorems.Thm_GlobalTheory_SS_Dil_gr_add
import Theorems.Thm_GlobalTheory_SS_Dil_gr_sub
import Theorems.Thm_GlobalTheory_SS_Dil_gr_mul
import Theorems.Thm_GlobalTheory_SS_Dil_gr_zero
import Theorems.Thm_GlobalTheory_SS_Dil_gr_sum
import Theorems.Thm_GlobalTheory_SS_Dil_ker_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution {R B S : Type} {n : ℕ} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    (q : MvPolynomial (Fin n) R →ₐ[R] B) (hq : Function.Surjective q) (σ : MvPolynomial (Fin n) R →+* S)
    (hσ : ∀ p, σ p = algebraMap B S (q p)) (hs : Function.Surjective σ)
    [Module.Projective S (S ⊗[B] KaehlerDifferential R B)] :
    ∃ h : Fin n → MvPolynomial (Fin n) R, (∀ j, q (h j) = 0) ∧
      ∀ f, q f = 0 → gr σ (f - ∑ j, pderiv j f * h j) = 0 := by
  let τ : (Fin n → S) →ₗ[S] S ⊗[B] KaehlerDifferential R B := Fintype.linearCombination S (fun i => dd R B S (q (X i)))
  have hτ : ∀ u, τ u = ∑ i, u i • dd R B S (q (X i)) := fun u => Fintype.linearCombination_apply _ _ _
  have hτg : ∀ p, τ (gr σ p) = dd R B S (q p) := fun p => by
    rw [hτ]
    exact (chain σ (fun p => dd R B S (q p)) (fun x y => by rw [map_add, dd_add])
      (fun x y => by rw [map_mul, dd_mul, hσ, hσ]) (fun r => by rw [← algebraMap_eq, q.commutes, dd_algebraMap]) p).symm
  have hsur : Function.Surjective τ := fun x => span_d R B S (LinearMap.range τ) (fun b => by
    obtain ⟨p, rfl⟩ := hq b
    exact ⟨_, hτg p⟩) x
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property τ LinearMap.id hsur
  let N : Submodule S (Fin n → S) :=
    { carrier := {u | ∃ f, q f = 0 ∧ gr σ f = u}
      zero_mem' := ⟨0, map_zero _, gr_zero σ⟩
      add_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        exact ⟨f + g, by rw [map_add, hf, hg, add_zero], gr_add σ _ _⟩
      smul_mem' := by
        rintro c _ ⟨f, hf, rfl⟩
        obtain ⟨p, rfl⟩ := hs c
        exact ⟨p * f, by rw [map_mul, hf, mul_zero], by rw [gr_mul, hσ f, hf, map_zero, zero_smul, add_zero]⟩ }
  let r : (Fin n → S) →ₗ[S] (Fin n → S) := LinearMap.id - s ∘ₗ τ
  have hr : ∀ u, r u ∈ N := fun u => ker_le q hq σ hσ N (fun f hf => ⟨f, hf, rfl⟩) _ (by
    rw [← hτ]
    have := LinearMap.congr_fun hs' (τ u)
    simp only [r, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub] at this ⊢
    rw [this, sub_self])
  choose h hh1 hh2 using fun j => hr (Pi.single j 1)
  refine ⟨h, hh1, fun f hf => ?_⟩
  have h1 : r (gr σ f) = gr σ f := by
    simp only [r, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hτg, hf, dd_zero, map_zero, sub_zero]
  have h2 : ∑ i, gr σ f i • (Pi.single i 1 : Fin n → S) = gr σ f := by
    funext j; simp [Pi.single_apply]
  rw [gr_sub, gr_sum, sub_eq_zero, ← h1]
  conv_lhs => rw [← h2, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gr_mul, hσ (h j), hh1, map_zero, zero_smul, add_zero, hh2, map_smul]; rfl
end GlobalTheory.SS.Dil

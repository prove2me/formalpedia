-- Prove2me | solution 1 for GlobalTheory.CubeFace.face
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:59.316096+00:00
-- url     : https://prove2.me/submissions/d08027b1-025c-4a55-a55c-7d59affebed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
import Theorems.Thm_GlobalTheory_CubeFace_glue_const
import Theorems.Thm_GlobalTheory_CubeFace_span_triples
import Theorems.Thm_GlobalTheory_CubeFace_prod_alt_erase
import Theorems.Thm_GlobalTheory_CubeFace_isOpen_sums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
variable {g : ℕ} {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ)
  (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
  (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
  (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
  (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ)
  (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
  (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
  (hTT : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
    (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
    T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
      T j' x)
  (Λ : Submodule ℤ (Fin g → ℂ)) (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
  (hWp : ∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i)
  (hTp : ∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x)
  (i₀ : ι) (h0 : (0 : Fin g → ℂ) ∈ W i₀)
include hW hcov hc0 hT hTT hΛ hWp hTp h0
namespace GlobalTheory.CubeFace
theorem _root_.solution (a : Fin 3) (x : Fin 3 → Fin g → ℂ)
    (hx : ∀ I : Finset (Fin 3), ∑ b ∈ I, x b ∈ W i₀) (hxa : x a = 0) :
    T (fun _ => i₀) x = T (fun _ => i₀) 0 := by
  have hsum : ∀ (y : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)),
      ∑ b ∈ I, Function.update y a 0 b = ∑ b ∈ I.erase a, Function.update y a 0 b :=
    fun y I => (Finset.sum_erase I (by simp)).symm
  have hPd : Differentiable ℂ (fun y : Fin 3 → Fin g → ℂ => Function.update y a 0) := by
    refine differentiable_pi.2 fun b => ?_
    by_cases hb : b = a
    · subst hb; simp
    · simp only [Function.update_of_ne hb]; fun_prop
  have hadd : ∀ y l : Fin 3 → Fin g → ℂ, Function.update (y + l) a 0 =
      Function.update y a 0 + Function.update l a 0 := by
    intro y l
    rw [← Function.update_add, add_zero]
  have hl : ∀ l : Fin 3 → Fin g → ℂ, (∀ b, l b ∈ Λ) → ∀ b, Function.update l a 0 b ∈ Λ := by
    intro l hl b
    by_cases hb : b = a
    · subst hb; simp
    · simpa [Function.update_of_ne hb] using hl b
  have key := glue_const (κ := Finset (Fin 3) → ι)
    (fun j => (fun y : Fin 3 → Fin g → ℂ => Function.update y a 0) ⁻¹'
      {x | ∀ I : Finset (Fin 3), ∑ b ∈ I, x b ∈ W (j (I.erase a))})
    (fun j y => T (fun I => j (I.erase a)) (Function.update y a 0))
    (fun j => (isOpen_sums W hW _).preimage hPd.continuous)
    (fun y => by
      choose s hs using hcov
      refine ⟨fun I => s (∑ b ∈ I, Function.update y a 0 b), fun I => ?_⟩
      rw [hsum]
      exact hs _)
    (fun j => (hT _).comp hPd.differentiableOn (fun y hy => hy))
    (fun j j' y hy hy' => by
      beta_reduce
      rw [hTT _ _ _ hy hy']
      have := prod_alt_erase a (fun I => c (j (I.erase a)) (j' (I.erase a))
        (∑ b ∈ I, Function.update y a 0 b)) (fun I => hc0 _ _ _ (hy I) (hy' I))
      simp only [Finset.erase_idem, ← hsum] at this
      rw [this, one_mul])
    (span_triples Λ hΛ)
    (fun j y l hlm hy => by
      refine ⟨fun I => ?_, ?_⟩
      · simp only [hadd, Pi.add_apply, Finset.sum_add_distrib]
        exact (hWp _ _ _ (Λ.sum_mem fun b _ => hl l hlm b)).2 (hy I)
      · simp only [hadd]
        exact hTp _ _ _ (hl l hlm))
    (fun _ => i₀) (fun _ => i₀) x 0
    (by
      have : Function.update x a 0 = x := by rw [← hxa]; simp
      rw [Set.mem_preimage, this]
      exact hx)
    (by intro I; simpa using h0)
  have : Function.update x a 0 = x := by rw [← hxa]; simp
  simpa [this] using key
end GlobalTheory.CubeFace

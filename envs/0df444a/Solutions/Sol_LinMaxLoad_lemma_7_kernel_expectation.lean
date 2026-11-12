-- Prove2me | solution 1 for LinMaxLoad.lemma_7_kernel_expectation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:40.537839+00:00
-- url     : https://prove2.me/submissions/8e46e91d-9060-4bd4-8f2b-16fb0e7e8622

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_probLin
import Theorems.Thm_LinMaxLoad_lemma_1

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace LinMaxLoad.Dev.KerExp

open Classical

variable {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]

theorem pow_eq_card (l : ℕ) (V : Submodule K E) (h : E →ₗ[K] (Fin l → K)) :
    (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker (h.domRestrict V)) =
      (Nat.card (LinearMap.ker (h.domRestrict V)) : ℝ) := by
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype (LinearMap.ker (h.domRestrict V)) := Fintype.ofFinite _
  have := Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker (h.domRestrict V))
  rw [Nat.card_eq_fintype_card, this]
  push_cast; rfl

theorem ker_card (l : ℕ) (V : Submodule K E) [Fintype V] (h : E →ₗ[K] (Fin l → K)) :
    (Nat.card (LinearMap.ker (h.domRestrict V)) : ℝ) =
      ∑ v : V, (if h v = 0 then (1 : ℝ) else 0) := by
  haveI : Fintype E := Fintype.ofFinite E
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

theorem swap (l : ℕ) (V : Submodule K E) [Fintype V] :
    avgLin K E l (fun h => (Nat.card (LinearMap.ker (h.domRestrict V)) : ℝ)) =
      ∑ v : V, probLin K E l (fun h => h v = 0) := by
  haveI : Fintype E := Fintype.ofFinite E
  letI : Fintype (E →ₗ[K] (Fin l → K)) := Fintype.ofFinite _
  unfold probLin avgLin
  simp only [ker_card, ← Finset.sum_div]
  rw [Finset.sum_comm]
  congr!

theorem prob_term (l : ℕ) (v : E) :
    probLin K E l (fun h => h v = 0) =
      if v = 0 then 1 else ((Fintype.card K : ℝ) ^ l)⁻¹ := by
  have hfun : (fun h : E →ₗ[K] (Fin l → K) => h v = 0) =
      (fun h => ∀ i : Fin 1, h ((fun _ : Fin 1 => v) i) = 0) := by
    funext h; simp
  rw [hfun, (LinMaxLoad.lemma_1 (K := K) l 1 (fun _ : Fin 1 => v) 0).2]
  by_cases hv : v = 0
  · subst hv; rw [Set.range_const, Submodule.span_zero_singleton, finrank_bot]; simp
  · rw [if_neg hv, Set.range_const, finrank_span_singleton hv]
    simp

theorem sum_terms (l : ℕ) (V : Submodule K E) [Fintype V] :
    ∑ v : V, probLin K E l (fun h => h v = 0) =
      1 + ((Nat.card V : ℝ) - 1) / (Fintype.card K : ℝ) ^ l := by
  simp only [prob_term]
  have hc : (Nat.card V : ℝ) = Fintype.card V := by rw [Nat.card_eq_fintype_card]
  rw [hc]
  have : ∀ v : V, (if (v : E) = 0 then (1 : ℝ) else ((Fintype.card K : ℝ) ^ l)⁻¹) =
      ((Fintype.card K : ℝ) ^ l)⁻¹ + (if v = 0 then (1 - ((Fintype.card K : ℝ) ^ l)⁻¹) else 0) := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · have : (v : E) ≠ 0 := fun h => hv (Subtype.ext h)
      simp [this, hv]
  simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem le_two (l : ℕ) (V : Submodule K E) (hd : Module.finrank K V ≤ l) :
    1 + ((Nat.card V : ℝ) - 1) / (Fintype.card K : ℝ) ^ l ≤ 2 := by
  haveI : Fintype V := Fintype.ofFinite V
  have hq := Fintype.card_pos (α := K)
  have h1 : (Nat.card V : ℝ) = (Fintype.card K : ℝ) ^ Module.finrank K V := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := V)]; push_cast; rfl
  have h2 : (Fintype.card K : ℝ) ^ Module.finrank K V ≤ (Fintype.card K : ℝ) ^ l :=
    pow_le_pow_right₀ (by exact_mod_cast hq) hd
  have h3 : (0 : ℝ) < (Fintype.card K : ℝ) ^ l := by positivity
  have : ((Nat.card V : ℝ) - 1) / (Fintype.card K : ℝ) ^ l ≤ 1 := by
    rw [div_le_one h3]; linarith
  linarith

end LinMaxLoad.Dev.KerExp

namespace LinMaxLoad
open LinMaxLoad.Dev.KerExp in
theorem chk_lemma_7_kernel_expectation {K E : Type*} [Field K] [Fintype K] [AddCommGroup E]
    [Module K E] [Finite E] (ℓ : ℕ) (V : Submodule K E) :
    avgLin K E ℓ (fun h => (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker (h.domRestrict V))) =
        avgLin K E ℓ (fun h => (Nat.card (LinearMap.ker (h.domRestrict V)) : ℝ)) ∧
      avgLin K E ℓ (fun h => (Nat.card (LinearMap.ker (h.domRestrict V)) : ℝ)) =
        ∑ᶠ v ∈ (V : Set E), probLin K E ℓ (fun h => h v = 0) ∧
      ∑ᶠ v ∈ (V : Set E), probLin K E ℓ (fun h => h v = 0) =
        1 + ((Nat.card V : ℝ) - 1) / (Fintype.card K : ℝ) ^ ℓ ∧
      (Module.finrank K V ≤ ℓ → 1 + ((Nat.card V : ℝ) - 1) / (Fintype.card K : ℝ) ^ ℓ ≤ 2) := by
  haveI : Fintype V := Fintype.ofFinite V
  have hfs : ∑ᶠ v ∈ (V : Set E), probLin K E ℓ (fun h => h v = 0) =
      ∑ v : V, probLin K E ℓ (fun h => h v = 0) := by
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
    rfl
  refine ⟨?_, ?_, ?_, le_two ℓ V⟩
  · congr 1; funext h; exact pow_eq_card ℓ V h
  · rw [hfs]; exact swap ℓ V
  · rw [hfs]; exact sum_terms ℓ V
end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_lemma_7_kernel_expectation := @LinMaxLoad.chk_lemma_7_kernel_expectation

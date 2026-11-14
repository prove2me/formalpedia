-- Prove2me | solution 1 for LatticePrepro.eq_zero_of_moment_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:09.279191+00:00
-- url     : https://prove2.me/submissions/306bd575-a18a-4c09-992a-98d532935565

import Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

open Finsupp

section Moment

variable {F Ω : Type*} [CommRing F] [CommRing Ω] [Algebra F Ω]

lemma moment_eq_sum (f : Ω →₀ F) (k : ℕ) :
    moment f k = ∑ α ∈ f.support, f α • α ^ k := rfl

end Moment

section Identification

variable {Ω : Type*} [Field Ω]

/-- **Vandermonde identification** (Lemma 4.3). A finitely supported `g : Ω →₀ Ω` supported on
at most `t` points whose moments of order `< t` all vanish is identically zero. -/
private theorem eq_zero_of_moment_eq_zero (g : Ω →₀ Ω) {t : ℕ} (hs : g.support.card ≤ t)
    (h : ∀ k < t, moment g k = 0) : g = 0 := by
  classical
  set s := g.support with hs_def
  set e : Fin s.card ≃ s := s.equivFin.symm
  let v : Fin s.card → Ω := fun j => (e j : Ω)
  have hv : Function.Injective v := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  let w : Fin s.card → Ω := fun j => g (e j)
  have hw : Matrix.vecMul w (Matrix.vandermonde v) = 0 := by
    funext k
    have hk : (k : ℕ) < t := lt_of_lt_of_le k.isLt hs
    have hmom := h k hk
    rw [moment_eq_sum] at hmom
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rw [← hmom, ← Finset.sum_coe_sort s, ← e.sum_comp]
    simp [w, v, smul_eq_mul]
  have hdet : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hw0 : w = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hw
  ext α
  by_cases hα : α ∈ g.support
  · have := congrFun hw0 (e.symm ⟨α, hα⟩)
    simpa [w] using this
  · simpa using Finsupp.notMem_support_iff.mp hα

end Identification

end LatticePrepro

open LatticePrepro
open Finsupp
variable {Ω : Type*} [Field Ω]
theorem solution (g : Ω →₀ Ω) {t : ℕ} (hs : g.support.card ≤ t)
    (h : ∀ k < t, moment g k = 0) : g = 0 :=
  @LatticePrepro.eq_zero_of_moment_eq_zero Ω _ g t hs h

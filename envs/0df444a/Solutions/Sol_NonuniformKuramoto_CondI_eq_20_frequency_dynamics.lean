-- Prove2me | solution 1 for NonuniformKuramoto.CondI.eq_20_frequency_dynamics
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:01:06.762426+00:00
-- url     : https://prove2.me/submissions/0c6ba091-4d02-46c8-a4a4-05b686a7860f

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

open NonuniformKuramoto.CondI


theorem solution {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 ≤ P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (θ : ℝ → Fin n → ℝ) (hθ : IsSolution D ω P ϕ θ) (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => D i * field D ω P ϕ (θ s) i)
      (-∑ j, P i j * Real.cos (θ t i - θ t j + ϕ i j)
          * (field D ω P ϕ (θ t) i - field D ω P ϕ (θ t) j))
      (Set.Ici 0) t := by
  have hcomp : ∀ k, HasDerivWithinAt (fun s => θ s k) (field D ω P ϕ (θ t) k) (Set.Ici 0) t :=
    fun k => hasDerivWithinAt_pi.mp (hθ t ht) k
  have heq : (fun s => D i * field D ω P ϕ (θ s) i) =
      fun s => ω i - ∑ j, P i j * Real.sin (θ s i - θ s j + ϕ i j) := by
    funext s
    unfold field
    field_simp [(hD i).ne']
  rw [heq]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasDerivWithinAt (fun s => P i j * Real.sin (θ s i - θ s j + ϕ i j))
        (P i j * (Real.cos (θ t i - θ t j + ϕ i j) *
          (field D ω P ϕ (θ t) i - field D ω P ϕ (θ t) j))) (Set.Ici 0) t := by
    intro j _
    exact ((((hcomp i).sub (hcomp j)).add_const (ϕ i j)).sin).const_mul (P i j)
  have hs := HasDerivWithinAt.fun_sum hterm
  have hfin := (hasDerivWithinAt_const t (Set.Ici (0:ℝ)) (ω i)).sub hs
  refine hfin.congr_deriv ?_
  rw [zero_sub, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

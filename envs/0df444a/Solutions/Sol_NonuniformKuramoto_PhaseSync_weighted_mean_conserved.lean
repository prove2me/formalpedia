-- Prove2me | solution 1 for NonuniformKuramoto.PhaseSync.weighted_mean_conserved
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:02:14.089599+00:00
-- url     : https://prove2.me/submissions/ff822c0c-31ab-48f8-8da9-25fdfb904324

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_NonuniformKuramoto_CondI_Constants
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
import Definitions.Def_NonuniformKuramoto_PhaseSync_Rate

namespace Aux_NKPSwmc

lemma sinc_mul (x : ℝ) : Real.sinc x * x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]; field_simp

end Aux_NKPSwmc

open Aux_NKPSwmc in
theorem solution {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (ωbar : ℝ)
    (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 ≤ P i j)
    (hPii : ∀ i, P i i = 0) (hϕ : ∀ i j, ϕ i j = 0) (hω : ∀ i, ω i / D i = ωbar)
    (hreach : NonuniformKuramoto.CondI.HasGloballyReachableNode P) (hsymm : ∀ i j, P i j = P j i)
    (θ : ℝ → Fin n → ℝ) (hsol : NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ) :
    (∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (fun s : ℝ => fun i => D i * (θ s i - ωbar * s))
        (-((NonuniformKuramoto.CondI.lap (fun i j => P i j * Real.sinc (θ t i - θ t j))).mulVec
          (fun i => θ t i - ωbar * t)))
        (Set.Ici 0) t) ∧
    (∀ t : ℝ, 0 ≤ t →
      ∑ i, D i * θ t i = ∑ i, D i * θ 0 i + ωbar * t * ∑ i, D i) := by
  have hωi : ∀ i, ω i = ωbar * D i := by
    intro i
    have := hω i
    rw [div_eq_iff (hD i).ne'] at this
    exact this
  -- component derivatives
  have hcomp : ∀ t : ℝ, 0 ≤ t → ∀ i, HasDerivWithinAt (fun s : ℝ => D i * (θ s i - ωbar * s))
      (-(∑ j, P i j * Real.sin (θ t i - θ t j))) (Set.Ici 0) t := by
    intro t ht i
    have h1 := hasDerivWithinAt_pi.1 (hsol t ht) i
    have h2 : HasDerivWithinAt (fun s : ℝ => ωbar * s) ωbar (Set.Ici 0) t := by
      simpa using (hasDerivWithinAt_id t (Set.Ici 0)).const_mul ωbar
    have h3 := (h1.sub h2).const_mul (D i)
    refine h3.congr_deriv ?_
    simp only [NonuniformKuramoto.CondI.field, hϕ, add_zero, hωi]
    have := (hD i).ne'
    field_simp
    ring
  have hlap : ∀ t : ℝ, ∀ i,
      ((NonuniformKuramoto.CondI.lap (fun i j => P i j * Real.sinc (θ t i - θ t j))).mulVec
        (fun i => θ t i - ωbar * t)) i = ∑ j, P i j * Real.sin (θ t i - θ t j) := by
    intro t i
    rw [NonuniformKuramoto.CondI.lap, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← sinc_mul (θ t i - θ t j)]
    ring
  have hanti : ∀ t : ℝ, ∑ i, ∑ j, P i j * Real.sin (θ t i - θ t j) = 0 := by
    intro t
    have h : ∑ i, ∑ j, P i j * Real.sin (θ t i - θ t j) =
        -(∑ i, ∑ j, P i j * Real.sin (θ t i - θ t j)) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [hsymm j i, ← neg_sub, Real.sin_neg]
      ring
    linarith
  refine ⟨?_, ?_⟩
  · intro t ht
    apply hasDerivWithinAt_pi.2
    intro i
    have := hcomp t ht i
    rw [Pi.neg_apply, hlap t i]
    exact this
  · intro t ht
    set g : ℝ → ℝ := fun s => ∑ i, D i * (θ s i - ωbar * s) with hg
    have hgd : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt g 0 (Set.Ici 0) s := by
      intro s hs
      have := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hcomp s hs i)
      refine this.congr_deriv ?_
      rw [Finset.sum_neg_distrib, hanti s, neg_zero]
    have hcont : ContinuousOn g (Set.Icc 0 t) := by
      intro s hs
      exact ((hgd s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
    have hconst := constant_of_has_deriv_right_zero hcont (fun s hs =>
      (hgd s hs.1).mono (Set.Ici_subset_Ici.2 hs.1)) t ⟨ht, le_rfl⟩
    simp only [hg, mul_zero, sub_zero] at hconst
    have e : ∑ i, D i * (θ t i - ωbar * t) = ∑ i, D i * θ t i - ωbar * t * ∑ i, D i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e] at hconst
    linarith

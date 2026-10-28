-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_sum_eq_column_sum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:56:41.374967+00:00
-- url     : https://prove2.me/submissions/c24d729a-fc5d-4f83-8e29-a87619e54cb8

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

set_option maxHeartbeats 800000

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (F : (Fin (m + 1) →₀ Nat) → Complex)
    (hcols : ∀ e ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = e) :
      ∑ e ∈ P.support, P.coeff e * F e =
        ∑ c : InterpolationMatrix.Column w0 w H,
          P.coeff (InterpolationMatrix.exponentVector c.1) *
            F (InterpolationMatrix.exponentVector c.1) := by
  classical
  let expV : InterpolationMatrix.Column w0 w H → (Fin (m + 1) →₀ Nat) :=
    fun c => InterpolationMatrix.exponentVector c.1
  have hexp_inj : Function.Injective expV := by
    intro c₁ c₂ h
    exact Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h)
  by_cases hne : P.support.Nonempty
  · obtain ⟨e0, he0⟩ := hne
    let σ : (Fin (m + 1) →₀ Nat) → InterpolationMatrix.Column w0 w H := fun e =>
      if h : e ∈ P.support then Classical.choose (hcols e h)
      else Classical.choose (hcols e0 he0)
    have hσ : ∀ e ∈ P.support, expV (σ e) = e := by
      intro e he
      dsimp [σ]
      rw [dif_pos he]
      exact Classical.choose_spec (hcols e he)
    have hσ_inj : ∀ {e₁ e₂}, e₁ ∈ P.support → e₂ ∈ P.support → σ e₁ = σ e₂ → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂ h
      have := congrArg expV h
      simpa [hσ e₁ he₁, hσ e₂ he₂] using this
    have hLHS :
        ∑ e ∈ P.support, P.coeff e * F e =
          ∑ c ∈ P.support.image σ, P.coeff (expV c) * F (expV c) := by
      rw [Finset.sum_image (fun _ he₁ _ he₂ h => hσ_inj he₁ he₂ h)]
      refine Finset.sum_congr rfl ?_
      intro e he
      simp [hσ e he]
    have hRHS :
        ∑ c : InterpolationMatrix.Column w0 w H,
            P.coeff (expV c) * F (expV c) =
          ∑ c ∈ P.support.image σ, P.coeff (expV c) * F (expV c) := by
      refine (Finset.sum_subset (Finset.subset_univ (P.support.image σ)) ?_).symm
      intro c _ hc
      have : expV c ∉ P.support := by
        intro hin
        apply hc
        refine Finset.mem_image.mpr ⟨expV c, hin, ?_⟩
        exact hexp_inj ((hσ _ hin).trans rfl)
      have hz : P.coeff (expV c) = 0 := MvPolynomial.notMem_support_iff.mp this
      simp [hz]
    rw [hLHS, hRHS]
  · have hs : P.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hL : ∑ e ∈ P.support, P.coeff e * F e = 0 := by simp [hs]
    have hR :
        ∑ c : InterpolationMatrix.Column w0 w H,
            P.coeff (expV c) * F (expV c) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro c _
      have : expV c ∉ P.support := by simp [hs]
      have hz : P.coeff (expV c) = 0 := MvPolynomial.notMem_support_iff.mp this
      simp [hz]
    rw [hL, hR]

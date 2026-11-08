-- Prove2me | solution 1 for NondualOpt.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:31:23.574995+00:00
-- url     : https://prove2.me/submissions/8fffb7fd-7169-4e20-95cf-87c1572df435

import Mathlib
import Definitions.Def_NondualOpt_maxRegret

open NondualOpt in
theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] (X U : Set E) (hX : Convex ℝ X)
    (hU : U ⊆ X) (T : ℕ) (hT : 1 ≤ T) (x : Fin T → E) (hx : ∀ t, x t ∈ X) (f : E → ℝ)
    (ℓ : Fin T → E → ℝ) (hℓU : ∀ t, ∀ u ∈ U, ℓ t u ≤ f u) (hℓx : ∀ t, ℓ t (x t) = f (x t)) :
    ∃ t₀ : Fin T, (∀ t, f (x t₀) ≤ f (x t)) ∧
      ∀ u ∈ U, (((T : ℝ) * (f (x t₀) - f u) : ℝ) : EReal) ≤ maxRegret X x ℓ := by
  haveI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  obtain ⟨t₀, ht₀⟩ := Finite.exists_min (fun t => f (x t))
  refine ⟨t₀, ht₀, fun u hu => ?_⟩
  unfold maxRegret
  have hI : (⨅ u' : X, ((T : ℝ) : EReal) * ⨆ t, ((ℓ t u' : ℝ) : EReal)) ≤
      ((T : ℝ) : EReal) * ((f u : ℝ) : EReal) := by
    refine le_trans (iInf_le _ ⟨u, hU hu⟩) ?_
    apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.mpr (Nat.cast_nonneg T))
    exact iSup_le fun t => EReal.coe_le_coe_iff.mpr (hℓU t u hu)
  have hsum : (T : ℝ) * f (x t₀) ≤ ∑ t, ℓ t (x t) := by
    simp_rw [hℓx]
    have := Finset.card_nsmul_le_sum Finset.univ (fun t => f (x t)) (f (x t₀))
      (fun t _ => ht₀ t)
    simpa using this
  calc ((((T : ℝ) * (f (x t₀) - f u)) : ℝ) : EReal)
      ≤ ((∑ t, ℓ t (x t) - (T : ℝ) * f u : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (by rw [mul_sub]; linarith)
    _ = ((∑ t, ℓ t (x t) : ℝ) : EReal) - (((T : ℝ) * f u : ℝ) : EReal) := EReal.coe_sub _ _
    _ ≤ _ := EReal.sub_le_sub le_rfl (by rw [EReal.coe_mul]; exact hI)

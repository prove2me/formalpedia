-- Prove2me | solution 1 for GlobalTheory.CurvMargin.curv_and_margin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:59.743319+00:00
-- url     : https://prove2.me/submissions/4c2f3203-2713-4fb2-8a60-cadb1a8a7c7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PhlaBlockWtCpt
import Theorems.Thm_GlobalTheory_CurvMargin_leviRh_eq
import Theorems.Thm_GlobalTheory_CurvMargin_coeff_cases
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.CurvMargin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CurvMargin
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → ∀ ξ : Fin (nd X) → ℂ, leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 * ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2) →
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom → ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧ Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ), leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 (D ξ)) →
    ((CurvGGStatement (E := E)) ∧ (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℝ), (∀ τ (i j : Fin r), i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → m ≤ (la τ j : ℝ) - (la τ i : ℝ)) → ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ)) := by
  intro hdiag htr
  refine ⟨fun r X la x0 z hz => ⟨fun hd ξ => ?_, fun hd ξ hξ => ?_⟩, ?_⟩
  · obtain ⟨x1, D, ho, -, hD⟩ := htr r X x0 z hz
    show 0 ≤ leviM X (phla X la) x0 z ξ
    rw [hD, hdiag r X la x1 ho]
    refine Finset.sum_nonneg fun e _ => mul_nonneg ?_ (by positivity)
    obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
    obtain ⟨h1, h2, h3⟩ := hd τ
    have hab' : (b : ℕ) < a := hab
    rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h1 b a (le_of_lt hab) h))
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h2 b a h (le_of_lt hab)))
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h3 b a h h'))
  · obtain ⟨x1, D, ho, hinj, hD⟩ := htr r X x0 z hz
    show 0 < leviM X (phla X la) x0 z ξ
    rw [hD, hdiag r X la x1 ho]
    have hpos : ∀ e : Ent X, 0 < sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 *
        ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) := by
      intro e
      obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
      obtain ⟨h1, h2, h3⟩ := hd τ
      have hab' : (b : ℕ) < a := hab
      rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h1 b a hab h))
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h2 b a h hab))
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h3 b a h h'))
    have hne : D ξ ≠ 0 := fun h => hξ (hinj (h.trans (map_zero D).symm))
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    refine Finset.sum_pos' (fun e _ => mul_nonneg (hpos e).le (by positivity))
      ⟨(Fintype.equivFin (Ent X)).symm k, Finset.mem_univ _, mul_pos (hpos _) ?_⟩
    have hkk : (Fintype.equivFin (Ent X)) ((Fintype.equivFin (Ent X)).symm k) = k :=
      Equiv.apply_symm_apply (Fintype.equivFin (Ent X)) k
    refine pow_pos (norm_pos_iff.2 fun h => hk ?_) 2
    exact (congrArg (D ξ) hkk).symm.trans h
  · intro r X la m h1 h2 h3 x0 ho z hz ξ
    obtain ⟨x1, D, ho1, -, hD⟩ := htr r X x0 z hz
    rw [leviRh_eq X x0 ho hz, leviO, hD, hD, hdiag r X la x1 ho1, hdiag r X _ x1 ho1,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
    have hab' : (b : ℕ) < a := hab
    show m * (sgn X.p0 a * sgn X.p0 b * ((blockWt X τ b : ℝ) - (blockWt X τ a : ℝ))) ≤
      sgn X.p0 a * sgn X.p0 b * ((la τ b : ℝ) - (la τ a : ℝ))
    rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
    · rw [e]
      have := sub_nonneg.2 (Int.cast_le (R := ℝ).2 (h1 τ b a (le_of_lt hab) h))
      simpa [blockWt, h, hab'.trans h] using this
    · rw [e]
      have := sub_nonneg.2 (Int.cast_le (R := ℝ).2 (h2 τ b a h (le_of_lt hab)))
      simpa [blockWt, not_lt.2 h, not_lt.2 (h.trans hab'.le)] using this
    · rw [e]
      have := h3 τ b a h h'
      simpa [blockWt, sgn, h, not_lt.2 h'] using this
end GlobalTheory.CurvMargin

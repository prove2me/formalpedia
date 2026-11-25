-- Prove2me | solution 1 for GlobalTheory.FlagSecProbe.weight_eq_zero_of_one_isSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:25.866628+00:00
-- url     : https://prove2.me/submissions/6d7645e7-f57c-44d2-9dba-8e4dcb7c864f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_WeightEqZeroOfOneIsSec
import Theorems.Thm_GlobalTheory_FlagSecProbe_dom_nonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open GlobalTheory GlobalTheory.FlagSecProbe
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlagSecProbe
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r)
    (h : X.IsSec la (fun _ => 1)) : la = 0 := by
  classical
  obtain ⟨x, hx⟩ := dom_nonempty X
  funext τ i
  let b : Frame X.Ψ r := fun σ => Matrix.diagonal fun a => if σ = τ ∧ a = i then (2 : ℂ) else 1
  have hb : b ∈ Bor X.Ψ r := fun σ => ⟨by
      have : mat b σ = Matrix.diagonal fun a => if σ = τ ∧ a = i then (2 : ℂ) else 1 := rfl
      rw [this, Matrix.det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
      split_ifs <;> norm_num,
    fun a c hca => Matrix.diagonal_apply_ne _ hca.ne'⟩
  have h1 := h.2.1 x hx b hb
  have h2 : bchar la b = (2 : ℂ) ^ la τ i := by
    unfold bchar
    rw [Finset.prod_eq_single τ, Finset.prod_eq_single i]
    · simp [b]
    · intro a _ ha; simp [b, ha]
    · simp
    · intro σ _ hσ; simp [b, hσ]
    · simp
  rw [h2, mul_one] at h1
  have h3 : ((2 : ℝ)) ^ la τ i = 1 := by
    have := congrArg norm h1
    simpa [norm_zpow] using this.symm
  exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 h3
end GlobalTheory.FlagSecProbe

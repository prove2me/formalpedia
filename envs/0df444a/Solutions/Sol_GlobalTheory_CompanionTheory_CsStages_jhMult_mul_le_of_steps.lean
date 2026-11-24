-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CsStages.jhMult_mul_le_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:33.497802+00:00
-- url     : https://prove2.me/submissions/c9fc23a2-f600-4ca5-ad6f-87c330db525b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JhMultMulLeOfSteps
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CsStages
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
namespace GlobalTheory.CompanionTheory.CsStages
theorem _root_.solution (σ : Representation F G W) (ρ : Representation F G V)
    (A : Subrepresentation ρ → ℕ∞) (m : ℕ∞) (hmono : ∀ S T : Subrepresentation ρ, T ≤ S → A T ≤ A S)
    (hstep : ∀ S T : Subrepresentation ρ, T ≤ S → Nonempty ((subQuot S T).Equiv σ) → A T + m ≤ A S) :
    jhMult σ ρ * m ≤ A ⊤ := by
  have key : ∀ r, OccursTimes σ ρ r → (r : ℕ∞) * m ≤ A ⊤ := by
    rintro r ⟨S, T, h1, h2, h3⟩
    have hi : ∀ (i : ℕ) (hi : i < r), ((i + 1 : ℕ) : ℕ∞) * m ≤ A (S ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero =>
        intro hi
        have := hstep _ _ (h1 ⟨0, hi⟩) (h3 ⟨0, hi⟩)
        simpa using le_trans le_add_self this
      | succ i ih =>
        intro hi
        have h4 := ih (by omega)
        have h5 := hmono _ _ (h2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))
        have h6 := hstep _ _ (h1 ⟨i + 1, hi⟩) (h3 ⟨i + 1, hi⟩)
        refine le_trans ?_ h6
        have : (((i + 1 + 1 : ℕ)) : ℕ∞) * m = ((i + 1 : ℕ) : ℕ∞) * m + m := by
          push_cast; ring
        rw [this]
        exact add_le_add (h4.trans h5) le_rfl
    rcases r with _ | r
    · simp
    · exact (hi r (by omega)).trans (hmono _ _ le_top)
  unfold jhMult
  rw [ENat.iSup_mul]
  refine iSup_le fun r => ?_
  rw [ENat.iSup_mul]
  exact iSup_le fun hr => key r hr
end GlobalTheory.CompanionTheory.CsStages

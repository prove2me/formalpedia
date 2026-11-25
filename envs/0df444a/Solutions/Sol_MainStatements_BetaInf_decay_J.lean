-- Prove2me | solution 1 for MainStatements.BetaInf.decay_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:18.385437+00:00
-- url     : https://prove2.me/submissions/bc5a79c8-eba3-4c62-b881-1ec17f1ecef6

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_CompanionTheory_AutomorphicTheory_KFiniteVectors_KDecay
import Theorems.Thm_MainStatements_BetaInf_sN_nonneg
import Theorems.Thm_MainStatements_BetaInf_gap_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MainStatements MainStatements.BetaInf
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace
noncomputable section
namespace MainStatements.BetaInf
theorem _root_.solution {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) {n : ℕ} (ε : Fin n → Bool) :
    ∀ (m : ℕ) (h : ℝ) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam μ → IsDS ε μ σ → PI.ZuckTensor.GapAtLeast ε μ h →
      t n ε + m < h → ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
      ∃ C : ℝ, ∀ g ∈ UJset ε, sN g ^ m * ‖⟪w, σ g v⟫_ℂ‖ ≤ C := by
  intro m
  induction m with
  | zero =>
    intro h μ H _ _ _ σ _ hσ _ _ v w _ _
    refine ⟨‖w‖ * ‖v‖, fun g hg => ?_⟩
    rw [pow_zero, one_mul, ← hσ.2.2.1.2.1 g hg v]
    exact norm_inner_le_norm _ _
  | succ m ih =>
    intro h μ H _ _ _ σ hμ hσ hgap hlt v w hv hw
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hlt
    obtain ⟨X⟩ := hZ n ε μ H σ hμ hσ h hgap (by linarith)
    have key : ∀ i j : Fin n, ∃ C : ℝ, ∀ g ∈ UJset ε, sN g ^ m * (‖⟪w, σ g v⟫_ℂ‖ * ‖g i j‖) ≤ C := by
      intro i j
      obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (Pi.single j 1) (Pi.single i 1) hv hw
      choose C hC using fun a : ι => ih (h - 1) _ (X.Hs (sI a)) (X.σs (sI a)) (X.ds _ (hI a).1).1
        (X.ds _ (hI a).1).2 (gap_step hgap _) (by linarith) (vI a) (wI a) (hI a).2.1 (hI a).2.2
      refine ⟨∑ a, C a, fun g hg => ?_⟩
      have e : star (Pi.single i 1 : Fin n → ℂ) ⬝ᵥ (g *ᵥ Pi.single j 1) = g i j := by
        have : star (Pi.single i 1 : Fin n → ℂ) = Pi.single i 1 := by
          funext a
          simp only [Pi.star_apply, Pi.single_apply]
          split_ifs <;> simp
        rw [this, single_one_dotProduct, Matrix.mulVec_single_one]
        rfl
      have h1 := hsum g hg
      rw [e] at h1
      rw [← norm_mul, h1]
      calc sN g ^ m * ‖∑ a, ⟪wI a, X.σs (sI a) g (vI a)⟫_ℂ‖
          ≤ sN g ^ m * ∑ a, ‖⟪wI a, X.σs (sI a) g (vI a)⟫_ℂ‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (sN_nonneg g) _)
        _ = ∑ a, sN g ^ m * ‖⟪wI a, X.σs (sI a) g (vI a)⟫_ℂ‖ := Finset.mul_sum _ _ _
        _ ≤ ∑ a, C a := Finset.sum_le_sum fun a _ => hC a g hg
    choose C hC using key
    refine ⟨∑ i, ∑ j, C i j, fun g hg => ?_⟩
    have e : sN g ^ (m + 1) * ‖⟪w, σ g v⟫_ℂ‖ = ∑ i, ∑ j, sN g ^ m * (‖⟪w, σ g v⟫_ℂ‖ * ‖g i j‖) := by
      simp only [← Finset.mul_sum]
      rw [pow_succ]
      unfold sN
      ring
    rw [e]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hC i j g hg
end MainStatements.BetaInf

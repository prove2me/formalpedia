-- Prove2me | solution 1 for GlobalTheory.IntBallMinorOne.mat_nFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:18.191193+00:00
-- url     : https://prove2.me/submissions/cc08ed19-f296-4d12-ac5b-1817609b3798

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst
import Theorems.Thm_GlobalTheory_IntBall_nmat_eq_lowMat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBallMinorOne
open Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IntBallMinorOne
theorem _root_.solution (X : Data E r) (hp : X.p0 = 1) (z : V (nd X)) (τ : X.Ψ) :
    mat (nFrame X z) τ = lowMat (zOf X z τ) := by
  rw [← nmat_eq_lowMat]
  ext a b
  show ∑ c, zFrame X z τ a c * leviFrame X z τ c b = nmat X z τ a b
  simp only [zFrame, leviFrame, hp]
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have n00 : ∀ c : Fin r, nmat X z τ c c = 1 := fun c => by simp [nmat]
  have nup : ∀ c d : Fin r, c < d → nmat X z τ c d = 0 := fun c d h => by
    have h1 : ¬ d < c := fun h' => lt_asymm h h'
    have h2 : c ≠ d := ne_of_lt h
    simp [nmat, h1, h2]
  by_cases hb : (b : ℕ) < 1
  · have hb0 : b = ⟨0, hr⟩ := Fin.ext (by simp; omega)
    subst hb0
    rw [Finset.sum_eq_single ⟨0, hr⟩]
    · by_cases ha : 1 ≤ (a : ℕ)
      · simp [ha, n00]
      · have ha0 : a = ⟨0, hr⟩ := Fin.ext (by simp; omega)
        subst ha0; simp [n00]
    · intro c _ hc
      have hc1 : 1 ≤ (c : ℕ) := by
        by_contra h; apply hc; exact Fin.ext (by simp; omega)
      simp [hc1]
    · simp
  · rw [Finset.sum_eq_single a]
    · have : ¬ (1 ≤ (a : ℕ) ∧ (a : ℕ) < 1) := by omega
      simp [this, hb]
      intro h1 h2; omega
    · intro c _ hca
      by_cases hc : (c : ℕ) < 1
      · have h1 : c < b := Fin.lt_def.2 (by omega)
        simp [hb, nup c b h1]
      · have : ¬ (1 ≤ (a : ℕ) ∧ (c : ℕ) < 1) := by omega
        simp [this, Ne.symm hca]
        intro _ _ h3; omega
    · simp
end GlobalTheory.IntBallMinorOne

-- Prove2me | solution 1 for GlobalTheory.exists_half_char_of_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:07.665864+00:00
-- url     : https://prove2.me/submissions/771fe892-2667-4849-b20b-6b19096c04f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_neg_half_int
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply
attribute [local simp] GlobalTheory.thetaLevelBasis_apply

set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution {α : (ι → ℤ) → (ι → ℤ) → ℂ}
    (hα : ∀ n n' m m', α (n + m) (n' + m') = α n n' * α m m')
    (hs : ∀ n n', α n n' = 1 ∨ α n n' = -1) :
    ∃ p q : ι → ℤ, ∀ n n', α n n' = eC (ofRealVec (fun i => (p i : ℝ) / 2) ⬝ᵥ ofIntVec n' -
      ofRealVec (fun i => (q i : ℝ) / 2) ⬝ᵥ ofIntVec n) := by
  classical
  have key : ∀ β : (ι → ℤ) → ℂ, (∀ n m, β (n + m) = β n * β m) → (∀ n, β n = 1 ∨ β n = -1) →
      ∃ p : ι → ℤ, ∀ n, β n = eC (ofRealVec (fun i => (p i : ℝ) / 2) ⬝ᵥ ofIntVec n) := by
    intro β hβ hs
    have h0 : β 0 = 1 := by
      have := hβ 0 0
      rw [add_zero] at this
      rcases hs 0 with h | h
      · exact h
      · rw [h] at this; norm_num at this
    have hne : ∀ n, β n ≠ 0 := fun n => by rcases hs n with h | h <;> simp [h]
    have hp : ∀ i, ∃ k : ℤ, β (Pi.single i 1) = eC ((k : ℂ) / 2) := fun i => by
      rcases hs (Pi.single i 1) with h | h
      · exact ⟨0, by simp [h, eC_zero]⟩
      · exact ⟨-1, by simpa [h] using (eC_neg_half_int 1).symm⟩
    choose p hp using hp
    refine ⟨p, fun n => ?_⟩
    have hsingle : ∀ i (k : ℤ), β (Pi.single i k) = eC ((p i : ℂ) / 2 * k) := fun i k => by
      induction k using Int.induction_on with
      | zero => simp [h0, eC_zero]
      | succ k ih => rw [Pi.single_add, hβ, ih, hp, ← eC_add]; congr 1; push_cast; ring
      | pred k ih =>
        refine mul_right_cancel₀ (hne (Pi.single i 1)) ?_
        rw [← hβ, ← Pi.single_add, sub_add_cancel, ih, hp, ← eC_add]; congr 1; push_cast; ring
    induction n using Pi.single_induction with
    | zero => simp [h0, ofIntVec_zero, eC_zero]
    | add n m hn hm => rw [hβ, hn, hm, ofIntVec_add, dotProduct_add, eC_add]
    | single i k =>
      rw [hsingle]
      congr 1
      simp [dotProduct, ofIntVec, ofRealVec, Pi.single_apply]
  obtain ⟨p, hp⟩ := key (α 0) (fun n m => by simpa using hα 0 n 0 m) (hs 0)
  obtain ⟨q, hq⟩ := key (α · 0) (fun n m => by simpa using hα n 0 m 0) (hs · 0)
  refine ⟨p, -q, fun n n' => ?_⟩
  have h := hα n 0 0 n'
  rw [add_zero, zero_add, hp, hq, ← eC_add] at h
  rw [h]
  congr 1
  have : ofRealVec (fun i => (((-q) i : ℤ) : ℝ) / 2) = -ofRealVec (fun i => (q i : ℝ) / 2) := by
    funext i; simp [ofRealVec, neg_div]
  rw [this, neg_dotProduct]; ring
end GlobalTheory

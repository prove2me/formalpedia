-- Prove2me | solution 1 for GlobalTheory.HCXi.LineStabiliser.acts_through_level_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:02.258512+00:00
-- url     : https://prove2.me/submissions/053b470a-f9bf-44fb-9ef2-8aff18bec03e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_pair_e0_left
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_lift_lst
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_decomp
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_pair_unitary
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_pair_lift
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_pair_shift
import Theorems.Thm_GlobalTheory_LevelStabiliser_liftVec_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.LineStabiliser
open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser
variable (k r' : ℕ)
namespace GlobalTheory.HCXi.LineStabiliser
theorem _root_.solution : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  intro k r' a p hp he
  have hp' : pᴴ * Hpk k (1 + r') * p = Hpk k (1 + r') := hp
  have ha : a ≠ 0 := by
    rintro rfl
    have h := pair_unitary _ p hp' (Pi.single (lst k r') 1) (e0 k r')
    rw [he, zero_smul, star_zero, zero_dotProduct, pair_e0_left] at h
    simp at h
  have hl : ∀ w, (p *ᵥ liftVec k 1 r' w) (lst k r') = 0 := by
    intro w
    have h := pair_unitary _ p hp' (liftVec k 1 r' w) (e0 k r')
    rw [he, star_smul, smul_dotProduct, pair_e0_left, pair_e0_left, lift_lst, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (star_ne_zero.2 ha)
  have hd : ∀ w, p *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (((incl k 1 r')ᴴ * p * incl k 1 r') *ᵥ w) +
        (p *ᵥ liftVec k 1 r' w) (fst k r') • e0 k r' := by
    intro w
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← liftVec_eq k 1 r' w]
    exact decomp k r' _ (hl w)
  refine ⟨ha, (incl k 1 r')ᴴ * p * incl k 1 r', ?_, fun w => ⟨_, hd w⟩⟩
  generalize (incl k 1 r')ᴴ * p * incl k 1 r' = g at hd
  show gᴴ * Hpk k r' * g = Hpk k r'
  ext i j
  have h := pair_unitary _ p hp' (liftVec k 1 r' (Pi.single j 1)) (liftVec k 1 r' (Pi.single i 1))
  rw [hd (Pi.single j 1), hd (Pi.single i 1), pair_shift, pair_lift, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec, ← Pi.single_star, star_one, single_one_dotProduct,
    single_one_dotProduct, mulVec_single_one, mulVec_single_one] at h
  exact h
end GlobalTheory.HCXi.LineStabiliser

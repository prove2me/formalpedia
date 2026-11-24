-- Prove2me | solution 1 for GlobalTheory.FormalInv.exists_substInv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:11:52.012798+00:00
-- url     : https://prove2.me/submissions/98ac055f-ebc3-4f65-9cca-d86bc65e24ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}
namespace GlobalTheory.FormalInv
theorem _root_.solution (hu : ∀ i, constantCoeff (u i) = 0) :
    (∃ v : σ → MvPowerSeries σ R, (∀ i, constantCoeff (v i) = 0) ∧
      (∀ i, (u i).subst v = X i) ∧ ∀ i, (v i).subst u = X i) ↔ IsUnit (linearPart u) :=
  ⟨fun ⟨_, hv, h, _⟩ => IsUnit.of_mul_eq_one _ (linearPart_mul_eq_one hu hv h), fun hA =>
    ⟨substInv u, constantCoeff_substInv hu, subst_substInv_right hu hA,
      subst_substInv_left hu hA⟩⟩
end GlobalTheory.FormalInv

-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.nabla_liftX_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:09:37.024677+00:00
-- url     : https://prove2.me/submissions/3f12eb18-5271-4a1c-b1ed-213e121a869f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_NablaExpConj_pderiv_inr_liftX
import Theorems.Thm_GlobalTheory_NablaExpConj_Dx_liftX
import Theorems.Thm_GlobalTheory_NablaExpConj_Dx_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.NablaExpConj
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
omit [Algebra ℚ k]
namespace GlobalTheory.NablaExpConj
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (f : PS k 1 d)
    (G : AA k d) :
    nabla k B h m u φ (liftX k f * G) =
      liftX k f * nabla k B h m u φ G + liftX k (Dof (B.FK k) u f) * G := by
  have e : ∀ c : Fin d → AA k d, ∑ i : Fin d, c i * pderiv k (Sum.inr i) (liftX k f * G) =
      liftX k f * ∑ i : Fin d, c i * pderiv k (Sum.inr i) G := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, pderiv_inr_liftX, smul_zero, add_zero, smul_eq_mul]
    ring
  unfold nabla
  rw [Dx_mul, Dx_liftX, e, e]
  ring
end GlobalTheory.NablaExpConj

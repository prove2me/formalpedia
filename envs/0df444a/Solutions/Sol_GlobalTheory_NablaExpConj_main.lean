-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:45.517929+00:00
-- url     : https://prove2.me/submissions/9066c0fa-dcb6-4ea5-b705-171bad598002

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_NablaExpConj_liftX_one
import Theorems.Thm_GlobalTheory_NablaExpConj_liftX_mul
import Theorems.Thm_GlobalTheory_NablaExpConj_nabla_liftX_mul
import Theorems.Thm_GlobalTheory_NablaExpConj_Dof_expS
import Theorems.Thm_GlobalTheory_NablaExpConj_expS_neg_mul_expS

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
namespace GlobalTheory.NablaExpConj
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (g : PS k 1 d), constantCoeff g = 0 → ∀ G : AA k d, liftX k (FB.expS k (-g)) * nabla k B h m u φ (liftX k (FB.expS k g) * G) = nabla k B h m u φ G + liftX k (Dof (B.FK k) u g) * G := by
  intro R _ d O _ _ k _ _ _ B h m u φ g hg G
  have e : liftX k (FB.expS k (-g)) * liftX k (FB.expS k g) = 1 := by
    rw [← liftX_mul, expS_neg_mul_expS k hg, liftX_one]
  rw [nabla_liftX_mul, Dof_expS k _ u hg, liftX_mul]
  linear_combination (nabla k B h m u φ G + liftX k (Dof (B.FK k) u g) * G) * e
end GlobalTheory.NablaExpConj

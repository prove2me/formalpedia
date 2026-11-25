-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.pderiv_inl_liftX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:06.104269+00:00
-- url     : https://prove2.me/submissions/1e31eaa3-943d-4689-a11b-3450ddbdf2f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_NablaExpConj_liftX_hasSubst
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst


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
variable (k : Type) [CommRing k]
namespace GlobalTheory.NablaExpConj
theorem _root_.solution (f : PS k 1 d) (j : Fin d) :
    pderiv k (Sum.inl j) (liftX k f) = liftX k (pderiv k ((0 : Fin 1), j) f) := by
  unfold liftX
  rw [FormalCalc.pderiv_subst (liftX_hasSubst k), Finset.sum_eq_single ((0 : Fin 1), j)]
  · rw [pderiv_X_self, mul_one]
  · rintro ⟨a, b⟩ _ hne
    have hb : b ≠ j := fun h => hne (by subst h; rw [Subsingleton.elim a 0])
    rw [pderiv_X_of_ne (fun h => hb (Sum.inl_injective h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
end GlobalTheory.NablaExpConj

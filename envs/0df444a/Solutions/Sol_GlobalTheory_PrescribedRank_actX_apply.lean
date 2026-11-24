-- Prove2me | solution 1 for GlobalTheory.PrescribedRank.actX_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:35.932956+00:00
-- url     : https://prove2.me/submissions/06900077-fe6b-4a98-9c06-7f81c5f24fe0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
namespace GlobalTheory.PrescribedRank
theorem _root_.solution (γ : (trivLevel p O Kf).Γ) (x : (noPlaces p O Kf).Xsp) :
    (trivLevel p O Kf).actX γ x = x := by
  have h : ∀ G, (noPlaces p O Kf).subst G = AlgHom.id Kf _ := fun G =>
    MvPolynomial.algHom_ext fun i => isEmptyElim i.1
  unfold Level.actX Places.natAct
  rw [h, Fintype.prod_empty]
  simp
end GlobalTheory.PrescribedRank

-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.quotSum_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:19.57669+00:00
-- url     : https://prove2.me/submissions/c9730808-993e-42b2-9f79-adcf56052f5f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_out_mk
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function
open scoped Pointwise
variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]
variable {H}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {Φ : G → M} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (x : G) :
    quotSum H (fun g => Φ (x * g)) = quotSum H Φ := by
  unfold quotSum
  calc ∑ᶠ q : G ⧸ H, Φ (x * q.out)
      = ∑ᶠ q : G ⧸ H, (fun q' : G ⧸ H => Φ q'.out) (MulAction.toPerm x q) := by
        refine finsum_congr fun q => ?_
        have hq : (MulAction.toPerm x q : G ⧸ H) = QuotientGroup.mk (x * q.out) := by
          rw [MulAction.toPerm_apply]
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        simp only [hq, apply_out_mk hΦ]
    _ = ∑ᶠ q : G ⧸ H, Φ q.out := finsum_comp_equiv (MulAction.toPerm x) (f := fun q' : G ⧸ H => Φ q'.out)
end GroundTheory.Automorphic.Parabolic

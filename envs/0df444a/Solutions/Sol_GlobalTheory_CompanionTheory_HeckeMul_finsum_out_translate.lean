-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.finsum_out_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:52:09.118302+00:00
-- url     : https://prove2.me/submissions/bee3851e-9f8a-4b10-b5c4-c06574835876

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_out_mk_of_right_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.HeckeMul
theorem _root_.solution {M : Type} [AddCommMonoid M] (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (a : G) :
    ∑ᶠ q : G ⧸ K, φ (a * q.out) = ∑ᶠ q : G ⧸ K, φ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) (f := fun q : G ⧸ K => φ q.out)]
  refine finsum_congr fun q => ?_
  have h : (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) q = (QuotientGroup.mk (a * q.out) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h, out_mk_of_right_inv K φ hφ]
end GlobalTheory.CompanionTheory.HeckeMul

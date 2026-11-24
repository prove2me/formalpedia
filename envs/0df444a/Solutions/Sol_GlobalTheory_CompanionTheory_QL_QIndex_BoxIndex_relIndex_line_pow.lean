-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.relIndex_line_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:00:04.63802+00:00
-- url     : https://prove2.me/submissions/b628f1ef-0ee4-4dd7-b2ef-ee82ebd5e851

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_map_line
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_ball_eq_line
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_irreducible_pi
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitRow_IdxV_relIndex_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
theorem _root_.solution (h : LF O ϖ nrm q) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (line O (c * ϖ ^ k)).relIndex (line O c) = q ^ k := by
  have hϖ0 : ϖ ^ k ≠ 0 := pow_ne_zero _ h.ne
  have hp : ∃ p : 𝒪[F], Irreducible p ∧ (p : F) = (Units.mk0 ϖ h.ne : Fˣ) :=
    ⟨_, irreducible_pi h, rfl⟩
  have h1 := relIndex_ball (Units.mk0 ϖ h.ne) hp (k : ℤ)
  have hu : (((Units.mk0 ϖ h.ne : Fˣ) ^ (k : ℤ) : Fˣ) : F) = ϖ ^ k := by simp
  rw [hu, ball_eq_line h one_ne_zero, ball_eq_line h hϖ0, Int.toNat_natCast, inv_one] at h1
  have hinj : Function.Injective (AddMonoidHom.mulLeft (c * ϖ ^ k)) :=
    mul_right_injective₀ (mul_ne_zero hc hϖ0)
  have h2 := AddSubgroup.relIndex_map_map_of_injective (line O 1) (line O (ϖ ^ k)⁻¹) hinj
  rw [map_line, map_line, mul_one, mul_assoc, mul_inv_cancel₀ hϖ0, mul_one] at h2
  rw [h2, h1, h.card]
  rfl
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex

-- Prove2me | solution 1 for GlobalTheory.OrbitUnfold.aedisjoint_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:17:29.907901+00:00
-- url     : https://prove2.me/submissions/b6b2e64e-0a43-42a5-ace7-2bf6b8aa4f54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
open GlobalTheory.OrbitUnfold
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
namespace GlobalTheory.OrbitUnfold
namespace _root_.GlobalTheory.OrbitUnfold
theorem _root_.solution (hF : IsFundamentalDomain Γ 𝓕 ν) {a b : Γ}
    (hab : a ≠ b) :
    AEDisjoint ν (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (a : H)) (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (b : H)) := by
  have key : ∀ c : Γ, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (c : H) = c⁻¹ • 𝓕 := fun c => by
    ext x
    simp [_root_.GlobalTheory.OrbitUnfold.pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  rw [key, key]
  exact hF.aedisjoint (inv_injective.ne hab)
end _root_.GlobalTheory.OrbitUnfold
end GlobalTheory.OrbitUnfold

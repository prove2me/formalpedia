-- Prove2me | solution 1 for GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:17:31.589648+00:00
-- url     : https://prove2.me/submissions/6f832cfb-edb2-49af-99ec-ce69a09f0a51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbits
import Theorems.Thm_GlobalTheory_OrbitUnfold_nullMeasurableSet_pull

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
theorem _root_.solution (hF : IsFundamentalDomain Γ 𝓕 ν)
    (y₀ : Y) {O : Set Y}
    [Countable O] (hO : ∀ γ : Γ, γ • y₀ ∈ O) (σ : O → Γ) (hσ : ∀ a : O, σ a • y₀ = a) :
    IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype)
      (⋃ a : O, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν where
  nullMeasurableSet := .iUnion fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _
  ae_covers := by
    filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
    let a : O := ⟨γ • y₀, hO γ⟩
    have hs : (σ a)⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ a]
    refine ⟨⟨Γ.subtype ((σ a)⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩, Set.mem_iUnion.2 ⟨a, ?_⟩⟩
    simpa [_root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def, mul_assoc] using hγ
  aedisjoint := by
    rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
    have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : O),
        (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ :
            (MulAction.stabilizer Γ y₀).map Γ.subtype) •
          _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H) = (σ a * u⁻¹)⁻¹ • 𝓕 := by
      intro u hu a
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem, _root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def,
        mul_assoc]
    simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
    refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
    refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
    have hab : a = b := by
      apply Subtype.ext
      have h1 := congrArg (· • y₀) h
      simp only [mul_smul] at h1
      rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
    subst hab
    have : s = t := inv_injective (mul_left_cancel h)
    subst this
    rfl
end _root_.GlobalTheory.OrbitUnfold
end GlobalTheory.OrbitUnfold

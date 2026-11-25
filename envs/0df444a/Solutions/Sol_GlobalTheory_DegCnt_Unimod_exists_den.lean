-- Prove2me | solution 1 for GlobalTheory.DegCnt.Unimod.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:49.314152+00:00
-- url     : https://prove2.me/submissions/13d080d4-e304-47f5-ba4b-7494f9a57926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexNeZero
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_exists_mul_le
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Unimod
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.Unimod
theorem _root_.solution {s : V ≃ₗ[K] V} {n : ℕ} (hs : ((s : V →ₗ[K] V) - 1) ^ n = 0)
    {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ m : ℕ, ∀ x ∈ Λ, N • (s ^ m) x ∈ Λ := by
  let u : V →ₗ[K] V := (s : V →ₗ[K] V) - 1
  let B : Submodule (𝓞 K) V := ⨆ i : Fin (n + 1), Λ.map ((u ^ (i : ℕ)).restrictScalars (𝓞 K))
  have hB : B.FG := Submodule.fg_iSup _ fun i => hΛ.fg.map _
  have hm : ∀ i : ℕ, ∀ x ∈ Λ, (u ^ i) x ∈ B := by
    intro i x hx
    by_cases hi : i < n + 1
    · exact Submodule.mem_iSup_of_mem (⟨i, hi⟩ : Fin (n + 1)) ⟨x, hx, rfl⟩
    · rw [pow_eq_zero_of_le (by omega : n ≤ i) hs]
      exact B.zero_mem
  have hu : B ≤ B.comap (u.restrictScalars (𝓞 K)) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨x, hx, rfl⟩
    have := hm (i + 1) x hx
    rw [pow_succ'] at this
    exact this
  have hsB : ∀ x ∈ B, s x ∈ B := by
    intro x hx
    have h1 : u x ∈ B := hu hx
    have : s x = u x + x := by simp [u]
    rw [this]
    exact B.add_mem h1 hx
  have hp : ∀ m : ℕ, ∀ x ∈ Λ, (s ^ m) x ∈ B := by
    intro m x hx
    induction m with
    | zero => simpa using hm 0 x hx
    | succ m ih => rw [pow_succ']; exact hsB _ ih
  obtain ⟨N, hN, h⟩ := exists_mul_le hΛ.span_eq_top hB
  exact ⟨N, hN, fun m x hx => h _ (hp m x hx)⟩
end GlobalTheory.DegCnt.Unimod

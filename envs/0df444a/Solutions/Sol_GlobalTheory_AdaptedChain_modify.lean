-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.modify
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:33.850087+00:00
-- url     : https://prove2.me/submissions/278df84b-9276-44a2-a56d-e9134fa3fcec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_pure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}
namespace GlobalTheory.AdaptedChain
theorem _root_.solution (S : Sys X) (Q : Finset I) (h : ∀ c ∈ Q, ∀ k, V.Ge 0 (S.cur c 1 (Sum.inl k))) :
    ∃ S' : Sys X, (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ S'.tan = S.tan ∧
      ∀ c ∈ Q, ∀ k, S'.cur c 1 (Sum.inl k) = 0 := by
  have : ∀ c, ∃ y, X.IsCurve (X.ty (Sum.inl c)) (S.tan c) y ∧ (c ∉ Q → y = S.cur c) ∧
      (c ∈ Q → ∀ k, y 1 (Sum.inl k) = 0) := by
    intro c
    by_cases hc : c ∈ Q
    · obtain ⟨z, hz, hz0, hzp⟩ := X.t4 (X.ty (Sum.inl c) + 1) (fun k => S.cur c 1 (Sum.inl k)) (h c hc)
        (fun k hk => S.pure c 1 _ (by simpa using hk))
      refine ⟨S.cur c - Vpow 1 z, ⟨X.Ty.sub_mem (S.mem c) (X.V_mem _ hz), ?_, ?_⟩, fun hh => absurd hc hh,
        fun _ k => ?_⟩
      · funext n
        simp [Vpow, (S.curve c).2.1]
      · intro i n hn
        simp only [Pi.sub_apply, S.pure c i n hn, Vpow]
        split_ifs with hi
        · simp
        · rw [hzp (i - 1) n, sub_zero]
          rw [Nat.cast_sub (by omega)]
          intro hh; apply hn; rw [hh]; push_cast; ring
      · simp [Vpow, hz0]
    · exact ⟨S.cur c, S.curve c, fun _ => rfl, fun hh => absurd hh hc⟩
  choose y h1 h2 h3 using this
  exact ⟨⟨S.tan, y, h1, S.unimod⟩, h2, rfl, h3⟩
end GlobalTheory.AdaptedChain

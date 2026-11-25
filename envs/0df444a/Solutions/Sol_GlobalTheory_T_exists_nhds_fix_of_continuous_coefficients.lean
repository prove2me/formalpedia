-- Prove2me | solution 1 for GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:17.862437+00:00
-- url     : https://prove2.me/submissions/ffc3f1bf-df73-41b1-9891-945fb741d067

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNhdsFixOfContinuousCoefficients
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNhdsFixOfContinuousCoefficientsStatement
import Theorems.Thm_GlobalTheory_SmoothFix_exists_nhds_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  first | exact @GlobalTheory.SmoothFix.exists_nhds_fix | exact GlobalTheory.SmoothFix.exists_nhds_fix | (intros; apply GlobalTheory.SmoothFix.exists_nhds_fix <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GlobalTheory.LeviRank.exists_select_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:29.235368+00:00
-- url     : https://prove2.me/submissions/828f630b-464c-40d8-aa20-c5eb7dc772dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSelectForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff Matrix
open GlobalTheory GlobalTheory.LeviRank
namespace GlobalTheory.LeviRank
theorem _root_.solution {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n N : ℕ} (hn : Module.finrank K M = n)
    (φ : Fin N → Module.Dual K M) (hφ : ∀ x, (∀ k, φ k x = 0) → x = 0) :
    ∃ jj : Fin n → Fin N, ∀ x, (∀ k, φ (jj k) x = 0) → x = 0 := by
  classical
  have hspan : Submodule.span K (Set.range φ) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    have : x = 0 := hφ x (fun k => by simpa using (Submodule.mem_iInf _).1 hx k)
    simp [this]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K φ
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = n := by
    have h := finrank_span_eq_card hli
    rw [hsp, hspan, finrank_top, Subspace.dual_finrank_eq, hn] at h
    exact h.symm
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k => a (e.symm k), fun x hx => hφ x fun k => ?_⟩
  have hk : φ k ∈ Submodule.span K (Set.range (φ ∘ a)) := by rw [hsp, hspan]; trivial
  refine Submodule.span_induction (p := fun f _ => f x = 0) ?_ ?_ ?_ ?_ hk
  · rintro _ ⟨i, rfl⟩
    simpa using hx (e i)
  · simp
  · intro f g _ _ hf hg; simp [hf, hg]
  · intro c f _ hf; simp [hf]
end GlobalTheory.LeviRank

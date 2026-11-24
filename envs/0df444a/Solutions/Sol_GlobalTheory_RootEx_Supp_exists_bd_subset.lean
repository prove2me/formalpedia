-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.exists_bd_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:16.292219+00:00
-- url     : https://prove2.me/submissions/6d7e778c-bde4-4952-9bb3-022cb7fba979

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
variable {k : Type} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.Supp
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] (Λ : AddSubgroup (Matrix ι κ k))
    (hΛ : IsOpen (Λ : Set (Matrix ι κ k))) :
    ∃ u : kˣ, ∀ x, Bd (valuation k (u : k)) x → x ∈ Λ := by
  classical
  have h : ∀ᶠ t in 𝓝 (0 : k), ∀ r s, Matrix.single r s t ∈ Λ := by
    refine Filter.eventually_all.2 fun r => Filter.eventually_all.2 fun s => ?_
    have hc : Continuous fun t : k => Matrix.single r s t := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.single, Matrix.of_apply]
      split_ifs
      exacts [continuous_id, continuous_const]
    refine hc.continuousAt.eventually_mem (hΛ.mem_nhds ?_)
    simp
  obtain ⟨u, hu⟩ := exists_cball_subset h
  refine ⟨u, fun x hx => ?_⟩
  rw [Matrix.matrix_eq_sum_single x]
  exact sum_mem fun r _ => sum_mem fun s _ => hu (hx r s) r s
end GlobalTheory.RootEx.Supp

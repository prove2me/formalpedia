-- Prove2me | solution 1 for GlobalTheory.RootEx.integrable_opE_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:15.820941+00:00
-- url     : https://prove2.me/submissions/ec5bcf43-ee70-4295-8459-5f9f6835fe35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Theorems.Thm_GlobalTheory_RootEx_continuous_affPt_uncurry
import Theorems.Thm_GlobalTheory_RootEx_comp_affPt_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c : ℕ}
open Classical
namespace GlobalTheory.RootEx
theorem _root_.solution (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x₀ : Matrix n n' k) :
    Integrable (fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc : Continuous fun e => affPt (c := c) p x₀ e :=
    (continuous_affPt_uncurry p).comp (Continuous.prodMk_right x₀)
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · refine (hΦ.1.continuous.comp hc).mul (continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_)))
    exact continuous_finset_sum _ fun i _ => hc.matrix_elem _ _
  · refine HasCompactSupport.mul_right ?_
    have h2 := (comp_affPt_mem_SB p hΦ).2
    refine HasCompactSupport.intro (h2.isCompact.image continuous_snd) fun e he => ?_
    exact image_eq_zero_of_notMem_tsupport
      (f := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) (x := (x₀, e)) fun h' => he ⟨_, h', rfl⟩
end GlobalTheory.RootEx

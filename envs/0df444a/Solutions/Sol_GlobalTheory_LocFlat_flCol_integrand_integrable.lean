-- Prove2me | solution 1 for GlobalTheory.LocFlat.flCol_integrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:51:40.851894+00:00
-- url     : https://prove2.me/submissions/ba2508e4-d487-421f-8e11-26907d9a227a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumn
import Theorems.Thm_GlobalTheory_LocFlat_affPt_eq_basePt_add_freeMat
import Theorems.Thm_GlobalTheory_LocFlat_isClosedEmbedding_freeMat
import Theorems.Thm_GlobalTheory_RootEx_continuous_affPt_uncurry
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open Classical
namespace GlobalTheory.LocFlat
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) (ν : Measure k)
    (hν : ν.IsAddHaarMeasure) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x : Matrix n (n' ⊕ Unit) k) :
    Integrable (fun e => Φ (ptCol p x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))
      (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := hν
  have hemb : Topology.IsClosedEmbedding (fun e => ptCol (c := c) p x e) := by
    have h : (fun e => ptCol (c := c) p x e) =
        (fun z => z + (basePt c x.toCols₁ + colAt n' c p fun r => x r (Sum.inr ()))) ∘ freeMat p := by
      funext e
      simp only [ptCol, affPt_eq_basePt_add_freeMat, Function.comp_apply]
      abel
    rw [h]
    exact (Homeomorph.addRight _).isClosedEmbedding.comp (isClosedEmbedding_freeMat p)
  have hch : Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k =>
      ((ψ (-ch (affPt p (0 : Matrix n n' k) e)) : Circle) : ℂ) := by
    refine continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_))
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_affPt_uncurry p).comp (Continuous.prodMk_right (0 : Matrix n n' k))).matrix_elem _ _
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hΦ.1.continuous.comp hemb.continuous).mul hch
  · exact (hΦ.2.comp_isClosedEmbedding hemb).mul_right
end GlobalTheory.LocFlat

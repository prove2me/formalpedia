-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.hk_cosetFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:06.157254+00:00
-- url     : https://prove2.me/submissions/48efa7eb-e4bf-4ed0-9af9-c49f985d5cfa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_fix_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution {K L : Subgroup (GL ι F)} [Fintype (K ⧸ L.subgroupOf K)] (g : GL ι F)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {v : V} (hv : v ∈ fixed ρ K) :
    hk ρ K (cosetFn K L g) v = avg ρ K L (ρ g v) := by
  classical
  have step : ∀ p : GL ι F ⧸ K, cosetFn K L g p.out • ρ p.out v =
      ∑ q : K ⧸ L.subgroupOf K, if p = QuotientGroup.mk (((q.out : K) : GL ι F) * g)
        then ρ (((q.out : K) : GL ι F) * g) v else 0 := by
    intro p
    unfold cosetFn
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [QuotientGroup.out_eq']
    split_ifs with h
    · obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (((q.out : K) : GL ι F) * g)
      rw [one_smul, h, hc, map_mul, Module.End.mul_apply, fix_of_mem hv c.2]
    · rw [zero_smul]
  unfold hk
  rw [finsum_congr step, finsum_sum_comm]
  · simp only [avg, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [finsum_eq_single _ (QuotientGroup.mk (((q.out : K) : GL ι F) * g))]
    · simp [map_mul, Module.End.mul_apply]
    · intro p hp
      exact if_neg hp
  · intro q _
    refine (Set.finite_singleton (QuotientGroup.mk (((q.out : K) : GL ι F) * g) : GL ι F ⧸ K)).subset ?_
    intro p hp
    by_contra h
    exact (Function.mem_support.1 hp) (if_neg h)
end GlobalTheory.CompanionTheory.HeckeInj

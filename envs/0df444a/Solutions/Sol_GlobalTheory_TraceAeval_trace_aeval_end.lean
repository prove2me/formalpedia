-- Prove2me | solution 1 for GlobalTheory.TraceAeval.trace_aeval_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:59.114527+00:00
-- url     : https://prove2.me/submissions/5fad60ef-6055-43ad-a38d-6d421c33b002

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
import Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_of_isNilpotent
import Theorems.Thm_GlobalTheory_TraceAeval_coe_aeval_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceAeval
open Module
namespace GlobalTheory.TraceAeval
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (f : Module.End ℂ V) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval f p) = (f.charpoly.roots.map fun z => p.eval z).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hf : ∀ μ, ∀ x ∈ f.maxGenEigenspace μ, f x ∈ f.maxGenEigenspace μ :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hp : ∀ μ, Set.MapsTo (aeval f p) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) := by
    intro μ x hx
    rw [show aeval f p x = _ from (coe_aeval_restrict f _ (hf μ) p ⟨x, hx⟩).symm]
    exact Subtype.mem _
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hp]
  have h1 : ∀ μ, LinearMap.trace ℂ _ ((aeval f p).restrict (hp μ))
      = (f.charpoly.rootMultiplicity μ : ℂ) * p.eval μ := by
    intro μ
    have e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p := by
      ext x
      rw [coe_aeval_restrict]; rfl
    have hn := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    have e2 : f.restrict (hf μ) - algebraMap ℂ _ μ = (f - algebraMap ℂ _ μ).restrict
        (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) := by
      ext x
      rfl
    rw [e, trace_aeval_of_isNilpotent _ μ (e2 ▸ hn), LinearMap.finrank_maxGenEigenspace_eq]
  simp_rw [h1]
  rw [Finset.sum_multiset_map_count]
  have hs : h_fin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Multiset.mem_toFinset, Set.mem_setOf_eq,
      ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq,
      Ne, Ne, Submodule.finrank_eq_zero]
  rw [hs]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, nsmul_eq_mul]
end GlobalTheory.TraceAeval

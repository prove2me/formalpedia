-- Prove2me | solution 1 for GlobalTheory.WachFree.mem_X_smul_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:23:28.107831+00:00
-- url     : https://prove2.me/submissions/13194dee-3f2f-4069-8048-a28fd5c68f93

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemXSmulOfProjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open GlobalTheory GlobalTheory.WachFree
namespace GlobalTheory.WachFree
theorem _root_.solution {D M : Type} [CommRing D] [IsDomain D] [AddCommGroup M]
    [Module D⟦X⟧ M] [Module.Projective D⟦X⟧ M] (c : D) (hc : c ≠ 0) (x y : M)
    (h : (C c : D⟦X⟧) • x = (X : D⟦X⟧) • y) : ∃ z : M, x = (X : D⟦X⟧) • z := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective D⟦X⟧ M›
  have hs' : ∀ m, Finsupp.linearCombination D⟦X⟧ id (s m) = m := fun m => LinearMap.congr_fun hs m
  have hd : ∀ m, (X : D⟦X⟧) ∣ s x m := by
    intro m
    have h1 := congrArg (fun w => constantCoeff (s w m)) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, constantCoeff_C,
      constantCoeff_X, zero_mul] at h1
    exact X_dvd_iff.mpr ((mul_eq_zero.mp h1).resolve_left hc)
  have : x ∈ LinearMap.range ((X : D⟦X⟧) • (LinearMap.id : M →ₗ[D⟦X⟧] M)) := by
    rw [← hs' x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    obtain ⟨d, hd⟩ := hd m
    exact ⟨d • m, by rw [hd, mul_smul]; rfl⟩
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by simpa using hz.symm⟩
end GlobalTheory.WachFree

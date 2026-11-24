-- Prove2me | solution 1 for GlobalTheory.rank_le_rank_map_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:38.784801+00:00
-- url     : https://prove2.me/submissions/962a155d-fef0-4154-ab70-b17d09cead42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k K : Type) [Field k] [Field K] [Algebra k K] (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) k) : Φ.rank ≤ (Φ.map (algebraMap k K)).rank := by
  classical
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := k)
    (M := LinearMap.range Φ.mulVecLin) (n := Φ.rank) le_rfl
  have hv : LinearIndependent k (fun i => ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k)) :=
    hf.map' _ (Submodule.ker_subtype _)

  have hw : LinearIndependent K
      (fun i => algebraMap k K ∘ ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k)) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hmem : ∀ i, algebraMap k K ∘ ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k) ∈
      LinearMap.range (Φ.map (algebraMap k K)).mulVecLin := by
    intro i
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (f i).2
    refine ⟨algebraMap k K ∘ y, ?_⟩
    rw [← hy]
    funext j
    simp only [Matrix.mulVecLin_apply, Function.comp_apply]
    exact (RingHom.map_mulVec _ _ _ j).symm
  let g : Fin Φ.rank → LinearMap.range (Φ.map (algebraMap k K)).mulVecLin := fun i => ⟨_, hmem i⟩
  have hg : LinearIndependent K g := LinearIndependent.of_comp (LinearMap.range _).subtype hw
  have hc := hg.fintype_card_le_finrank
  rw [Fintype.card_fin] at hc
  exact hc
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.isLattice_stdLat_and_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:34.704899+00:00
-- url     : https://prove2.me/submissions/9d9bedee-4ef3-4173-ba24-ee2b7a7d872f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLatticeStdLatAndAct
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_act
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι], Submodule.IsLattice k (stdLat k ι) ∧ ∀ (g : GL ι k) (L : Submodule 𝒪[k] (ι → k)), Submodule.IsLattice k L → Submodule.IsLattice k (act g L) := by
  intro k _ _ _ _ ι _ _
  refine ⟨⟨?_, ?_⟩, fun g L hL => ⟨?_, ?_⟩⟩
  · unfold stdLat
    refine Submodule.fg_pi fun _ => ?_
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : k) : ι → k) := by
      ext j
      simp [Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine mem_stdLat.2 fun j => ?_
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact hL.fg.map _
  · have himg : ((act g L : Submodule 𝒪[k] (ι → k)) : Set (ι → k))
        = (g : Matrix ι ι k).mulVecLin '' (L : Set (ι → k)) := by
      ext v
      exact mem_act
    rw [himg, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    intro w
    refine ⟨((g⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ w, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
end GlobalTheory.RootEx.UnfoldShape

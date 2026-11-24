-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.isHk_cosetFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:12.794955+00:00
-- url     : https://prove2.me/submissions/2f72e326-87e1-49c2-a6e7-db2a68844382

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_cosetFn_right
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_cosetFn_left
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


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
theorem _root_.solution {K L : Subgroup (GL ι F)} [Fintype (K ⧸ L.subgroupOf K)]
    (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) (g : GL ι F)
    (hL : ∀ l ∈ L, g⁻¹ * l * g ∈ K) : IsHk K (cosetFn K L g) := by
  classical
  refine ⟨hKo, hKc, ?_, fun k₁ h₁ k₂ h₂ x => ?_⟩
  · let C : Set (GL ι F) := ⋃ q : K ⧸ L.subgroupOf K, (fun y => (((q.out : K) : GL ι F) * g) * y) '' (K : Set (GL ι F))
    have hC : IsCompact C := isCompact_iUnion fun q => hKc.image (continuous_const.mul continuous_id)
    refine HasCompactSupport.of_support_subset_isCompact hC fun x hx => ?_
    obtain ⟨q, hq⟩ : ∃ q : K ⧸ L.subgroupOf K,
        (QuotientGroup.mk x : GL ι F ⧸ K) = QuotientGroup.mk (((q.out : K) : GL ι F) * g) := by
      by_contra h
      push_neg at h
      refine (Function.mem_support.1 hx) ?_
      unfold cosetFn
      exact Finset.sum_eq_zero fun q _ => if_neg (h q)
    refine Set.mem_iUnion.2 ⟨q, _, QuotientGroup.eq.1 hq.symm, ?_⟩
    group
  · rw [cosetFn_right K L g _ h₂, cosetFn_left K L g hL _ h₁]
end GlobalTheory.CompanionTheory.HeckeInj

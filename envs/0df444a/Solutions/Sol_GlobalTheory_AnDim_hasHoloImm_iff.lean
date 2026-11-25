-- Prove2me | solution 1 for GlobalTheory.AnDim.hasHoloImm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:45.088089+00:00
-- url     : https://prove2.me/submissions/df71246d-a4e8-41e0-965f-587675bd41f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_GlobalTheory_AnDim_le_analyticDim_iff
import Theorems.Thm_GlobalTheory_AnDim_hasHoloImm_of_regularLocus
import Theorems.Thm_GlobalTheory_AnDim_le_of_mem_regularLocus
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution (h : Published.AnalyticSetDimension) [CompactSpace X] [T2Space X]
    {A : FinHolAtlas d X} {T : Set X} (hT : A.IsAnalyticSubset T) {k : ℕ} :
    HasHoloImm A T k ↔ (k : WithBot ℕ∞) ≤ analyticDim A T := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · induction hm : analyticDim A T using WellFoundedLT.induction generalizing T with
    | ind m ih =>
      subst hm
      obtain ⟨U, g, j, hU, hne, hmaps, han, hinj⟩ := hk
      by_cases hreg : ∃ z ∈ U, ∃ n, g z ∈ regularLocus A T n
      · obtain ⟨z, hz, n, hn⟩ := hreg
        exact le_analyticDim_iff.2
          ⟨n, le_of_mem_regularLocus hU hmaps han hz (hinj z hz) hn, _, hn⟩
      · push_neg at hreg
        obtain ⟨hs, hlt⟩ := (h d X A).1 T hT
        obtain ⟨z, hz⟩ := hne
        have hlt' := hlt ⟨g z, (hmaps hz).1⟩
        refine (ih _ hlt' hs ⟨U, g, j, hU, ⟨z, hz⟩, fun w hw => ⟨⟨(hmaps hw).1, ?_⟩, (hmaps hw).2⟩,
          han, hinj⟩ rfl).trans hlt'.le
        simpa using hreg w hw
  · obtain ⟨n, hkn, hn⟩ := le_analyticDim_iff.1 hk
    exact hasHoloImm_of_regularLocus hkn hn
end GlobalTheory.AnDim

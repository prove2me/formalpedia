-- Prove2me | solution 1 for GlobalTheory.SBInduced.isQuotientMap_sweep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:43.384443+00:00
-- url     : https://prove2.me/submissions/8e632219-6a4b-4906-95ea-6068af616e9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatEventuallyInvariantOfContinuousAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInduced
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter
open GlobalTheory GlobalTheory.SBInduced
variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]
namespace GlobalTheory.SBInduced
theorem _root_.solution (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) :
    IsQuotientMap fun p : Y × K => r (j p.1) p.2 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : X × K ≃ₜ X × K :=
    { toFun := fun p => (r p.1 p.2, p.2)
      invFun := fun p => (r p.1 (p.2 : G)⁻¹, p.2)
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk
        continuous_snd
      continuous_invFun := (hc.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd).inv)).prodMk continuous_snd }
  have hcl : IsClosedMap fun p : Y × K => r (j p.1) p.2 :=
    (isClosedMap_fst_of_compactSpace (X := X) (Y := K)).comp
      (e.isClosedMap.comp (hj.prodMap (IsClosedEmbedding.id (X := K))).isClosedMap)
  refine hcl.isQuotientMap (hc.comp ((hj.continuous.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))) fun x => ?_
  obtain ⟨y, c, hc, rfl⟩ := hs x
  exact ⟨(y, ⟨c, hc⟩), rfl⟩
end GlobalTheory.SBInduced

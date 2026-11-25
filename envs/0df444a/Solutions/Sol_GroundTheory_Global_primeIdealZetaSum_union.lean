-- Prove2me | solution 1 for GroundTheory.Global.primeIdealZetaSum_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:10.842638+00:00
-- url     : https://prove2.me/submissions/084398dc-03b3-420a-8675-7d206e654705

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg_subtype
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {A B : Set (HeightOneSpectrum (𝓞 K))} (hd : Disjoint A B)
    {s : ℝ} (hs : 1 < s) :
    (A ∪ B).primeIdealZetaSum s = A.primeIdealZetaSum s + B.primeIdealZetaSum s := by
  simp only [Set.primeIdealZetaSum_def]
  exact Summable.tsum_union_disjoint
    (f := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s)) hd
    (summable_absNorm_rpow_neg_subtype A hs) (summable_absNorm_rpow_neg_subtype B hs)
end GroundTheory.Global

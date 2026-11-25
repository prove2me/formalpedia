-- Prove2me | solution 1 for GlobalTheory.HasLogGrowth.comp_of_logWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:26.425147+00:00
-- url     : https://prove2.me/submissions/5bb8c507-ea0d-4839-8dbc-687d53b8267b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_HasLogGrowth_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
open GlobalTheory.HasLogGrowth
namespace GlobalTheory.HasLogGrowth
theorem _root_.solution {f : X → E} (hf : HasLogGrowth S w U f) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hB : ∀ x ∈ U', x ∉ coordDivisor S' w' → π x ∉ coordDivisor S w)
    (hw : HasLogGrowth S' w' U' fun x => GlobalTheory.lwP₂ S (w (π x))) :
    HasLogGrowth S' w' U' fun x => f (π x) := by
  intro K hKU hK
  obtain ⟨C, N, h⟩ := hf (π '' K) (hU.mono_left hKU).image_subset
    (hK.image_of_continuousOn (hπ.mono hKU))
  exact HasLogGrowth.of_le (U := K) ((const C).mul ((hw.mono hKU).pow N))
    (fun x hx hx' => h _ (mem_image_of_mem π hx) (hB x (hKU hx) hx')) K Subset.rfl hK
end GlobalTheory.HasLogGrowth

-- Prove2me | solution 1 for GroundTheory.Automorphic.sub_hsTruncation_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:19.353827+00:00
-- url     : https://prove2.me/submissions/505b1612-b754-4ab1-9202-9f4f464b7f95

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap Filter Topology
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
omit [CompleteSpace H] [CompleteSpace K]
namespace GroundTheory.Automorphic
theorem _root_.solution {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι 𝕜 H)
    (T : H →L[𝕜] K) (F : Finset ι) (j : ι) :
    (T - hsTruncation b T F) (b j) = if j ∈ F then 0 else T (b j) := by
  have hb : ∀ i, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := fun i =>
    orthonormal_iff_ite.mp b.orthonormal i j
  simp only [sub_apply, hsTruncation, FunLike.coe_sum, Finset.sum_apply, smulRight_apply,
    innerSL_apply_apply, hb, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq']
  split_ifs <;> simp
end GroundTheory.Automorphic

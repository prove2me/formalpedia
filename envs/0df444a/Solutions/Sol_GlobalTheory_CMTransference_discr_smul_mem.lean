-- Prove2me | solution 1 for GlobalTheory.CMTransference.discr_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:48.389167+00:00
-- url     : https://prove2.me/submissions/c64729cf-ded1-4492-a611-1b4f5c42276c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
import Theorems.Thm_GlobalTheory_CMTransference_traceForm_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
variable {K : Type} [Field K] [NumberField K] {r : ℕ}
namespace GlobalTheory.CMTransference
theorem _root_.solution [IsCMField K] {S : HermForm K r} {L : Submodule (𝓞 K) (Fin r → K)}
    (hL : IsSelfDual S L) {z : Fin r → K} (hz : ∀ y ∈ L, ∃ k : ℤ, traceForm S z y = k) :
    (discr K : K) • z ∈ L := by
  refine hL.2 _ fun y hy => ?_
  have h := ReciprocityTheory.ChartRestriction.G.FD.d4l2_dual_int (S.h z y) fun γ => by
    obtain ⟨k, hk⟩ := hz _ (L.smul_mem γ hy)
    refine ⟨k, ?_⟩
    rw [← hk, traceForm_apply, mul_comm, ← h_smul_right]
    rfl
  refine ⟨⟨_, h⟩, ?_⟩
  rw [h_smul_left, map_intCast]
  rfl
end GlobalTheory.CMTransference

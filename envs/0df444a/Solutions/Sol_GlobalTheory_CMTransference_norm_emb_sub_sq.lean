-- Prove2me | solution 1 for GlobalTheory.CMTransference.norm_emb_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:55.734614+00:00
-- url     : https://prove2.me/submissions/bedb5245-e6c2-44de-8cac-54f245e17e2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference

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
variable {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
variable (p : ℕ) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
namespace GlobalTheory.CMTransference
theorem _root_.solution (x : Fin r → K) (w : ι → Fin r → ℂ) :
    ‖(WithLp.toLp 2 fun ik : ι × Fin r => w ik.1 ik.2 : EuclideanSpace ℂ (ι × Fin r)) -
      emb σ Q x‖ ^ 2 = ∑ i, normSq (Q i *ᵥ embVec (σ i) x - w i) := by
  rw [norm_sub_rev, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl
end GlobalTheory.CMTransference

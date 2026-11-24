-- Prove2me | solution 1 for GlobalTheory.CMTransference.norm_embDual_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:54.895235+00:00
-- url     : https://prove2.me/submissions/cbebf63f-2405-4820-8af6-dec8792b2181

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
theorem _root_.solution (x : Fin r → K) : ‖embDual p σ Q x‖ ^ 2 = 4 * majSq σ Q x := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, majSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [normSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  change ‖2 * sgn p k * (Q i *ᵥ embVec (σ i) x) k‖ ^ 2 = _
  have : ‖sgn p k‖ = 1 := by unfold sgn; split_ifs <;> simp
  rw [norm_mul, norm_mul, this]
  simp only [Complex.norm_ofNat]
  ring
end GlobalTheory.CMTransference

-- Prove2me | solution 1 for GlobalTheory.CoverPlaces.isIntegral_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:22.343496+00:00
-- url     : https://prove2.me/submissions/ac36d624-2cf5-415c-920a-934b3eda7679

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsPtOrdEqAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEquivCoverPointsPlacesBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.CoverPlaces
variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}
namespace GlobalTheory.CoverPlaces
theorem _root_.solution {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Finite ι]
    {S : ι → Type} [∀ c, CommRing (S c)] [∀ c, Algebra R (S c)] (Ψ : ∀ c, A →ₐ[R] S c)
    (hΨ : ∀ a, (∀ c, Ψ c a = 0) → a = 0) (x : A) (hx : ∀ c, IsIntegral R (Ψ c x)) :
    IsIntegral R x := by
  classical
  cases nonempty_fintype ι
  choose p hp hp0 using hx
  refine ⟨∏ c, p c, Polynomial.monic_prod_of_monic _ _ fun c _ => hp c, hΨ _ fun c => ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_algHom_apply, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.aeval_def]; exact hp0 c)
end GlobalTheory.CoverPlaces

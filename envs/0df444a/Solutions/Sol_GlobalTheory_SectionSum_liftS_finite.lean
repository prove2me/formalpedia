-- Prove2me | solution 1 for GlobalTheory.SectionSum.liftS_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:48.749069+00:00
-- url     : https://prove2.me/submissions/2c46ecc6-c473-405a-acfc-733c507336e8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection
import Theorems.Thm_GlobalTheory_SectionSum_liftS_fieldRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.SectionSum
open MvPolynomial MeasureTheory
namespace GlobalTheory.SectionSum
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x))
    (hfin : FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
        (OmS Ω D N)) :
    letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS h).toAlgebra
    FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := by
  letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS h).toAlgebra
  let i : FractionRing (MvPolynomial (TVar D N) K) ≃+*
      (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))) :=
    (liftS h).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (liftS_fieldRange h))
  have hc : (algebraMap (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
      (OmS Ω D N)).comp i.toRingHom =
      (RingEquiv.refl (OmS Ω D N)).toRingHom.comp
        (algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)) := by
    refine RingHom.ext fun y => ?_
    show ((i y : IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))) : OmS Ω D N) =
      liftS h y
    rfl
  have hrk := Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) hc
  apply FiniteDimensional.of_finrank_pos
  rw [hrk]
  exact Module.finrank_pos
end GlobalTheory.SectionSum

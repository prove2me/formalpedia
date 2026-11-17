-- Prove2me | solution 1 for N25.LocalFive.exists_finite_quotient_surjective_71_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:25.802289+00:00
-- url     : https://prove2.me/submissions/959668d9-bf4e-4cba-bc84-7605072a3f1f

import Mathlib
import Definitions.Def_N25_LocalFiveIntegralPoints
import Theorems.Thm_N25_LocalFive_exists_integralPointCover
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
import Theorems.Thm_N25_LocalFive_finite_quotient_reductionKernel
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_N25_LocalFive_surjective_nsmul_reductionKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_N25_LocalFive_isUnit_seventyOne
import Theorems.Thm_N25_LocalFive_finite_quotient_and_surjective_nsmul_map

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open GoodReductionJacobian NeronModelInfra

noncomputable section

local instance instL_N25_LocalFive_exists_finite_quotient_sur_bfd51b_s0cb624 : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace N25.LocalFive

/-- The represented local points have a finite-index subgroup admitting division by 71. -/
theorem _root_.solution
    {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of ℚ)}
    (L : RelativeGroupLaw ℚ f) (hB : AbelianSchemePropertyBundle ℚ f)
    (hc : L.IsCommutative) :
    ∃ U : AddSubgroup (L.AlgPoints hc ℚ_[5]),
      Finite ((L.AlgPoints hc ℚ_[5]) ⧸ U) ∧
        Function.Surjective (fun u : U => (71 : ℕ) • u) := by
  obtain ⟨D⟩ := exists_integralPointCover L hB hc
  letI : LocallyOfFiniteType D.g := D.model.locallyOfFiniteType
  letI : QuasiCompact D.g := D.model.quasiCompact
  refine ⟨(reductionKernel D.law D.comm).map D.toLocal, ?_⟩
  exact finite_quotient_and_surjective_nsmul_map D.toLocal D.onto 71
    (reductionKernel D.law D.comm) (finite_quotient_reductionKernel D.law D.comm)
    (surjective_nsmul_reductionKernel D.law D.comm D.model.smooth 71 isUnit_seventyOne)

end N25.LocalFive

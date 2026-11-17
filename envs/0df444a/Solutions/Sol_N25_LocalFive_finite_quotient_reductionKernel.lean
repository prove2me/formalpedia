-- Prove2me | solution 1 for N25.LocalFive.finite_quotient_reductionKernel
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:22.277309+00:00
-- url     : https://prove2.me/submissions/5fd24610-ea69-4e2f-b174-d6048f4ecf57

import Mathlib
import Definitions.Def_N25_LocalFiveIntegralPoints
import Theorems.Thm_N25_LocalFive_finite_k5
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_N25_LocalFive_finite_schemeHomOver_of_finite_field
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open GoodReductionJacobian NeronModelInfra GoodReductionJacobian.RelativeGroupLaw

noncomputable section

local instance instL_N25_LocalFive_finite_quotient_reductionK_bfd51b_s2fa1dd : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace N25.LocalFive

/-- The reduction kernel has finite quotient because residue-field points are finite. -/
theorem _root_.solution
    {N : Scheme.{0}} {g : N ⟶ Spec (CommRingCat.of R5)}
    (L : RelativeGroupLaw R5 g) (hc : L.IsCommutative)
    [LocallyOfFiniteType g] [QuasiCompact g] :
    Finite (L.AlgPoints hc R5 ⧸ reductionKernel L hc) := by
  letI : Finite k5 := finite_k5
  letI : Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R5 k5))) g) :=
    finite_schemeHomOver_of_finite_field g
  letI : Finite (L.AlgPoints hc k5) := inferInstanceAs
    (Finite (Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R5 k5))) g)))
  exact Finite.of_equiv ((reductionHom L hc).range) (QuotientAddGroup.quotientKerEquivRange (reductionHom L hc)).symm.toEquiv

end N25.LocalFive

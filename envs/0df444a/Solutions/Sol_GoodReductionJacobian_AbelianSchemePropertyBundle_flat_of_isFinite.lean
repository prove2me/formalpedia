-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.flat_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3500d391-7d85-5f78-a4e5-e800d34e3848

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism
import Theorems.Thm_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero
import Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mIsogFlat

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

private theorem _root_.P2mIsogFlat.isLocallyNoetherian (hA : AbelianSchemePropertyBundle K f) : IsLocallyNoetherian A := by
  haveI : Smooth f := hA.smooth
  exact LocallyOfFiniteType.isLocallyNoetherian f

p2m_export "P2mIsogFlat" "isLocallyNoetherian"

theorem flat_stalkMap (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f)
    [IsFinite β.1] (x : A) : (β.1.stalkMap x).hom.Flat := by
  haveI : Smooth f := hA.smooth
  haveI : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA
  haveI : IsLocallyNoetherian A := isLocallyNoetherian hA

  haveI hx : IsRegularLocalRing (A.presheaf.stalk x) := Smooth.isRegularLocalRing_stalk (f := f) x
  haveI hy : IsRegularLocalRing (A.presheaf.stalk (β.1.base x)) :=
    Smooth.isRegularLocalRing_stalk (f := f) (β.1.base x)

  letI alg : Algebra (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) :=
    (β.1.stalkMap x).hom.toAlgebra
  haveI : IsLocalHom (algebraMap (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (β.1.stalkMap x).hom)

  have hfib : ringKrullDim ((A.presheaf.stalk x) ⧸
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (β.1.base x))).map
        (algebraMap (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero β.1 x

  have hdim : ringKrullDim (A.presheaf.stalk x) =
      ringKrullDim (A.presheaf.stalk (β.1.base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism (f := f) β.1 β.2 x

  have hflat : Module.Flat (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) :=
    Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) hfib hdim
  exact hflat

theorem main (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f) [IsFinite β.1] :
    Flat β.1 :=
  Flat.of_stalkMap β.1 (flat_stalkMap hA β)

end P2mIsogFlat

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f) [IsFinite β.1] :
    Flat β.1 :=
  P2mIsogFlat.main hA β

end

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite (solution)

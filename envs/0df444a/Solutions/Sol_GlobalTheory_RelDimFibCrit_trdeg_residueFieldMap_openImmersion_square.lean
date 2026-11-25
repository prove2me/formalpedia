-- Prove2me | solution 1 for GlobalTheory.RelDimFibCrit.trdeg_residueFieldMap_openImmersion_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:10.096465+00:00
-- url     : https://prove2.me/submissions/2f6f02c6-3ce0-4edb-92d3-efc898600560

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothRelativeDimOfTrdeg
import Theorems.Thm_GlobalTheory_trdeg_eq_of_ringEquiv_square


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.RelDimFibCrit
namespace GlobalTheory.RelDimFibCrit
theorem _root_.solution :
    ∀ {X Y X' Y' : Scheme.{0}} (g : X' ⟶ Y') (f : X ⟶ Y) (jX : X' ⟶ X) (jY : Y' ⟶ Y)
    [IsOpenImmersion jX] [IsOpenImmersion jY], g ≫ jY = jX ≫ f → ∀ x : X',
    @Algebra.trdeg (Y.residueField (f (jX x))) (X.residueField (jX x)) _ _
      (f.residueFieldMap (jX x)).hom.toAlgebra =
    @Algebra.trdeg (Y'.residueField (g x)) (X'.residueField x) _ _
      (g.residueFieldMap x).hom.toAlgebra := by
  intro X Y X' Y' g f jX jY _ _ e x
  have hpt : jY (g x) = f (jX x) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  have hc := Scheme.Hom.residueFieldMap_congr e x
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hc
  let C : Y.residueField (jY (g x)) ≅ Y.residueField (f (jX x)) := Y.residueFieldCongr hpt
  have hc' : jY.residueFieldMap (g x) ≫ g.residueFieldMap x =
      C.hom ≫ f.residueFieldMap (jX x) ≫ jX.residueFieldMap x := hc
  let eU : Y.residueField (f (jX x)) ≅ Y'.residueField (g x) :=
    C.symm ≪≫ asIso (jY.residueFieldMap (g x))
  let eV : X.residueField (jX x) ≅ X'.residueField x := asIso (jX.residueFieldMap x)
  refine GlobalTheory.trdeg_eq_of_ringEquiv_square _ _ eU.commRingCatIsoToRingEquiv
    eV.commRingCatIsoToRingEquiv ?_
  have key : C.inv ≫ jY.residueFieldMap (g x) ≫ g.residueFieldMap x =
      f.residueFieldMap (jX x) ≫ jX.residueFieldMap x := by
    rw [hc']; simp
  have key2 := congrArg CommRingCat.Hom.hom key
  simp only [CommRingCat.hom_comp] at key2
  ext y
  have key3 := congrArg (fun φ => φ y) key2
  simpa [eU, eV] using key3
end GlobalTheory.RelDimFibCrit

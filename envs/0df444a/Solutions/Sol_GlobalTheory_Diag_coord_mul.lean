-- Prove2me | solution 1 for GlobalTheory.Diag.coord_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:46:56.537948+00:00
-- url     : https://prove2.me/submissions/d6d665a7-383e-4819-92df-467e59a90daa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_GlobalTheory_Diag_coord_ofChar
import Theorems.Thm_GlobalTheory_Diag_coord_single_zero
import Theorems.Thm_GlobalTheory_Diag_coord_single_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory GlobalTheory.Diag
variable (S : Scheme.{u}) {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable {S}
namespace GlobalTheory.Diag
theorem _root_.solution {T : Over S} (s t : T ⟶ splitTorus S X) (x : X) :
    (coord (s * t)).hom (AddMonoidAlgebra.single x 1) =
      (coord s).hom (AddMonoidAlgebra.single x 1) * (coord t).hom (AddMonoidAlgebra.single x 1) := by
  let g : Multiplicative (X × X) →* Γ(T.left, ⊤) :=
    { toFun := fun z => (coord s).hom (AddMonoidAlgebra.single z.toAdd.1 1) *
        (coord t).hom (AddMonoidAlgebra.single z.toAdd.2 1)
      map_one' := by
        change (coord s).hom (AddMonoidAlgebra.single 0 1) *
          (coord t).hom (AddMonoidAlgebra.single 0 1) = 1
        rw [coord_single_zero, coord_single_zero, _root_.one_mul]
      map_mul' := fun a b => by
        rw [toAdd_mul, Prod.fst_add, Prod.snd_add, coord_single_add, coord_single_add]
        ring }
  have hs : ofChar T g ≫ diagMap S (AddMonoidHom.inl X X) = s := hom_ext fun y => by
    rw [coord_comp_diagMap_single, coord_ofChar]
    change _ * (coord t).hom (AddMonoidAlgebra.single 0 1) = _
    rw [coord_single_zero, _root_.mul_one]; rfl
  have ht : ofChar T g ≫ diagMap S (AddMonoidHom.inr X X) = t := hom_ext fun y => by
    rw [coord_comp_diagMap_single, coord_ofChar]
    change (coord s).hom (AddMonoidAlgebra.single 0 1) * _ = _
    rw [coord_single_zero, _root_.one_mul]; rfl
  have : s * t = ofChar T g ≫ diagMap S (AddMonoidHom.inl X X + AddMonoidHom.inr X X) := by
    rw [diagMap_add, MonObj.comp_mul, hs, ht]
  rw [this, coord_comp_diagMap_single, coord_ofChar]
  simp [g]
end GlobalTheory.Diag

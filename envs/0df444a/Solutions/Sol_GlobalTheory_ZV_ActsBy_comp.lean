-- Prove2me | solution 1 for GlobalTheory.ZV.ActsBy.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:20.317579+00:00
-- url     : https://prove2.me/submissions/36489ea7-9477-4072-a268-edd5462f0ad9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Theorems.Thm_GlobalTheory_ZV_ActsBy_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
variable {A : Over (Sp K)} [GrpObj A] {k m : ℕ} {pt : Fin m → (Out.baseOver (Sp K) ⟶ A)}
namespace GlobalTheory.ZV
namespace ActsBy
theorem _root_.solution [IsCommMonObj A] (hp : ∀ i, pt i ^ k = 1) {f g : A ⟶ A} [IsMonHom g]
    {F G : Matrix (Fin m) (Fin m) (ZMod k)} (hf : ActsBy pt f F) (hg : ActsBy pt g G) :
    ActsBy pt (f ≫ g) (G * F) := by
  refine ⟨hf.pos, fun i => ?_⟩
  haveI : NeZero k := ⟨hf.pos.ne'⟩
  have hl : ∀ a : Fin m → ℕ, Out.linComb pt a = ∏ j, pt j ^ a j := fun a => List.prod_ofFn
  let φ : (Out.baseOver (Sp K) ⟶ A) →* (Out.baseOver (Sp K) ⟶ A) :=
    { toFun := (· ≫ g), map_one' := MonObj.one_comp _, map_mul' := fun a b => MonObj.mul_comp a b g }
  have hg' : ∀ j, φ (pt j) = ∏ l, pt l ^ (G l j).val := fun j => (hg.comp_eq j).trans (hl _)
  rw [← Category.assoc, hf.comp_eq i, hl, hl]
  change φ _ = _
  simp_rw [map_prod, map_pow, hg', ← Finset.prod_pow, ← pow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Finset.prod_pow_eq_pow_sum, pow_eq_pow_mod _ (hp l), Matrix.mul_apply, ← ZMod.val_natCast]
  simp
end ActsBy
end GlobalTheory.ZV

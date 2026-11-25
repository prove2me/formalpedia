-- Prove2me | solution 1 for GlobalTheory.BXOf.val_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:18:09.273237+00:00
-- url     : https://prove2.me/submissions/ed81fd5d-cb40-4d1d-ac09-d43e593efc9e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue
import Theorems.Thm_GlobalTheory_BXOf_sig_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BXOf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {X Y : Scheme.{0}}
namespace GlobalTheory.BXOf
theorem _root_.solution {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (f : R →+* S)
    {JR : (Spec (CommRingCat.of R) ⟶ X) → L.ι} (hR : Good L (closedPoint R) JR)
    {JS : (Spec (CommRingCat.of S) ⟶ X) → L.ι} (hS : Good L (closedPoint S) JS) (r : Spec (CommRingCat.of R) ⟶ Y) :
    sig S (val t (Spec.map (CommRingCat.ofHom f) ≫ r) (closedPoint S) JS) =
      (∏ k, del L f JR JS (r ≫ φ k) ^ ε k) * Units.map f.toMonoidHom (sig R (val t r (closedPoint R) JR)) := by
  have m := hR.mem φ r
  have g := gen_trans ht (Spec.map (CommRingCat.ofHom f) ≫ r) (closedPoint S) (hS.mem φ _) (top_le_of_mem r m trivial)
  refine (congrArg (sig S) g).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (sig_nat f r m _).symm))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact congrArg (fun q => sig S (gm q (closedPoint S) (L.U (JS q) ⊓ L.U (JR (r ≫ φ k))) (L.g (JS q) (JR (r ≫ φ k)))))
    (Category.assoc _ _ _)
end GlobalTheory.BXOf

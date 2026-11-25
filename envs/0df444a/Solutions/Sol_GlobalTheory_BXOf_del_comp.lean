-- Prove2me | solution 1 for GlobalTheory.BXOf.del_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:18:06.47988+00:00
-- url     : https://prove2.me/submissions/c9f2934e-e19e-459f-a9a2-761d5f22efce

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle


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
theorem _root_.solution {Q : Type} [CommRing Q] [IsLocalRing Q] {L : LB X} (hL : L.IsLB) (f : Q →+* R) (h : R →+* S)
    {JQ : (Spec (CommRingCat.of Q) ⟶ X) → L.ι} (hQ : Good L (closedPoint Q) JQ)
    {JR : (Spec (CommRingCat.of R) ⟶ X) → L.ι} (hR : Good L (closedPoint R) JR)
    {JS : (Spec (CommRingCat.of S) ⟶ X) → L.ι} (hS : Good L (closedPoint S) JS)
    (ψ : Spec (CommRingCat.of Q) ⟶ X) :
    del L (h.comp f) JQ JS ψ =
      Units.map h.toMonoidHom (del L f JQ JR ψ) * del L h JR JS (Spec.map (CommRingCat.ofHom f) ≫ ψ) := by
  have mQ : (Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint R) ∈ L.U (JQ ψ) := top_le_of_mem ψ (hQ ψ) trivial
  have mQ' : (Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint S) ∈ L.U (JQ ψ) :=
    top_le_of_mem ψ (hQ ψ) trivial
  have mR : (Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint S) ∈
      L.U (JR (Spec.map (CommRingCat.ofHom f) ≫ ψ)) := top_le_of_mem _ (hR _) trivial
  have mm : (Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint R) ∈
      L.U (JR (Spec.map (CommRingCat.ofHom f) ≫ ψ)) ⊓ L.U (JQ ψ) := ⟨hR _, mQ⟩
  have c := gm_cocycle hL _ _ (hS (Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom f) ≫ ψ)) mR mQ'
  rw [del, del, del, sig_nat h _ mm, ← map_mul, mul_comm, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  exact congrArg (sig S) c.symm
end GlobalTheory.BXOf

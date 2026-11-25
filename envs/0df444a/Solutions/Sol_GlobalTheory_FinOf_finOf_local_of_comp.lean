-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_local_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:47:04.958972+00:00
-- url     : https://prove2.me/submissions/6b9ad9b0-2f04-430a-acbe-426c5081ab1c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
namespace GlobalTheory.FinOf
theorem _root_.solution {O Q S : Type} [CommRing O] [CommRing Q] [CommRing S] [IsLocalRing O]
    [IsLocalRing Q] [IsLocalRing S] [Algebra O Q] [Algebra.IsIntegral O Q] (g : Q →+* S)
    (h : IsLocalHom (g.comp (algebraMap O Q))) : IsLocalHom g := by
  have h1 : (maximalIdeal S).comap (g.comp (algebraMap O Q)) = maximalIdeal O :=
    ((local_hom_TFAE (g.comp (algebraMap O Q))).out 0 4).1 h
  have h2 : (((maximalIdeal S).comap g).comap (algebraMap O Q)).IsMaximal := by
    rw [Ideal.comap_comap, h1]; infer_instance
  have h3 := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h2
  exact ((local_hom_TFAE g).out 4 0).1 (eq_maximalIdeal h3)
end GlobalTheory.FinOf

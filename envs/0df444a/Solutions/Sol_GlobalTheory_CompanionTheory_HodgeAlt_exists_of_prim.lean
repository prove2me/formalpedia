-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.exists_of_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:58.200745+00:00
-- url     : https://prove2.me/submissions/1ac14d88-ad4f-460c-a4ba-98e31b60165e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_pullHyp2_mk
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (m p q : CoefMap (RingHom.id R) F G) (z : cechDeRhamTotalCocyclesTwo F) (hz : z.1.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    ∃ e : Tot1 G, dTot1 G e = ((0 : C2 G),
      (pullTot2 m z.1 - pullTot2 p z.1 - pullTot2 q z.1).2.1,
      (pullTot2 m z.1 - pullTot2 p z.1 - pullTot2 q z.1).2.2) := by
  have h0 : Hyp2.mk G (pullZZ2 m z - pullZZ2 p z - pullZZ2 q z) = 0 := by
    rw [map_sub, map_sub, ← pullHyp2_mk, ← pullHyp2_mk, ← pullHyp2_mk, h]
    abel
  obtain ⟨e, he⟩ := Hyp2.mk_eq_zero.1 h0
  refine ⟨e, he.trans (Prod.ext ?_ rfl)⟩
  funext T T' T'' φ ψ
  change (pullTot2 m z.1).1 T T' T'' φ ψ - (pullTot2 p z.1).1 T T' T'' φ ψ -
    (pullTot2 q z.1).1 T T' T'' φ ψ = 0
  simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, hz, Pi.zero_apply, map_zero, sub_zero]
end GlobalTheory.CompanionTheory.HodgeAlt

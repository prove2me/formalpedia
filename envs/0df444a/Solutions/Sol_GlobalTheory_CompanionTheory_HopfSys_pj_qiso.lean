-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.pj_qiso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:02:03.520931+00:00
-- url     : https://prove2.me/submissions/0c4ec63f-daaa-437d-b6e1-84b3947b41fc

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_kap_bijective
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_pjAlg_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_Wop_inf
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_Wop_iSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
variable [IsSeparated A.hom]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution [Finite P] (hF : FubiniSt) (hA : AffAcycSt) : AllQIso (pj A S).coef := by
  haveI : Quiver.IsThin (Pᵒᵖ × Pᵒᵖ) := fun _ _ ↦ ⟨fun f g ↦ Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  refine hF R (Pᵒᵖ × Pᵒᵖ) (box (OSys A.hom S)) Pᵒᵖ (GG A S) (pj A S) fun T ↦ ?_
  let u : P →o (A ⊗ A).left.affineOpens := ⟨fun c ↦ ⟨Wop A S T.1.unop T.2.unop c, Wop_aff A S _ _ _⟩,
    fun c c' h ↦ Wop_mono A S le_rfl le_rfl h⟩
  obtain ⟨h1, h2, h3⟩ := hA R (A ⊗ A).left (A ⊗ A).hom ⟨Vop A S T.1.unop T.2.unop, Vop_aff A S _ _⟩ P u
    (fun c ↦ inf_le_left) (fun c c' ↦ Wop_inf A S _ _ c c') (Wop_iSup A S _ _)
  let aug : Sec (A ⊗ A).hom (Vop A S T.1.unop T.2.unop) →ₗ[R] Cn (u.monotone.functor.op ⋙ OAff (A ⊗ A).hom) 0 :=
    LinearMap.pi fun c ↦ (Sec.res (A ⊗ A).hom (show (u (c.obj (Fin.last 0)).unop).1 ≤ Vop A S T.1.unop T.2.unop from inf_le_left)).toLinearMap
  have hf : ∀ z c, ((pj A S).fib T z) c = aug (kap A S T.1.unop T.2.unop z) c := fun z c ↦
    pjAlg_apply A S (T, c.obj (Fin.last 0)) z
  have hb := kap_bijective A S T.1.unop T.2.unop
  refine ⟨fun x y e ↦ hb.1 (h1 (funext fun c ↦ ?_)), fun y ↦ (h2 y).trans ?_, h3⟩
  · exact ((hf x c).symm.trans (congrFun e c)).trans (hf y c)
  · constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, rfl⟩ := hb.2 w
      exact ⟨z, funext fun c ↦ hf z c⟩
    · rintro ⟨z, rfl⟩
      exact ⟨kap A S T.1.unop T.2.unop z, funext fun c ↦ (hf z c).symm⟩
end GlobalTheory.CompanionTheory.HopfSys

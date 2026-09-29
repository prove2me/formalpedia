-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.finPts_le_finPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d4983252-a7ab-55de-aef1-b7485648f279

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_finPts_le_finPts

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_finPts_le_finPts.ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_finPts_le_finPts.ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.NeronExtension JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP JZero"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "LevelData.shLift LevelData.shGenLift NeronExtension genPt barPt ExtendsToPlace LevelData finPts g pts"
namespace NeronExtension
p2m_export "ModularCurve.JZeroNeronObjectAtP.NeronExtension" "ExtN finPts openImm"
namespace S17EXTG
p2m_open "ModularCurve.JZeroNeronObjectAtP.NeronExtension ModularCurve.JZeroNeronObjectAtP ModularCurve"

open CategoryTheory.Limits

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
  {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension)

theorem res_comp {B T' T X Y : Scheme.{0}} {t : T ⟶ B} {t' : T' ⟶ B} {f : X ⟶ B} {g : Y ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (a : SchemeHomOver t f) (φ : SchemeHomOver f g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp a φ) =
      NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ a) φ :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem shGenLift_fst (q : SchemeHomOver (genPt p) O.g) :
    (Λ.shGenLift q).1 ≫ pullback.fst O.g Λ.shStr = q.1 := by
  unfold LevelData.shGenLift
  rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  rfl

theorem shLift_fst (s₀ : SchemeHomOver Λ.σA O.g) :
    (Λ.shLift s₀).1 ≫ pullback.fst O.g Λ.shStr = s₀.1 := by
  unfold LevelData.shLift
  rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  rfl

theorem shGenLift_eq_res_shLift (q : SchemeHomOver (genPt p) O.g) (s₀ : SchemeHomOver Λ.σA O.g)
    (h : q.1 = barPt A ≫ s₀.1) :
    Λ.shGenLift q = GoodReductionJacobian.schemeHomOverComp (barPt A) rfl (Λ.shLift s₀) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [shGenLift_fst, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, shLift_fst, h]
  · rw [(Λ.shGenLift q).2, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, (Λ.shLift s₀).2]

set_option maxHeartbeats 3200000 in
theorem extN_of_extendsToPlace' (x : JZero (N₀ * p)) (hx : ExtendsToPlace A Λ.σA (O.pts x)) : F.ExtN x := by
  obtain ⟨s₀, hs₀⟩ := hx
  refine ⟨NeronModelInfra.schemeHomOverComp (Λ.shLift s₀) F.openImm, ?_⟩
  show (NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) F.openImm).1 = _
  rw [shGenLift_eq_res_shLift (O.pts x) s₀ hs₀, ← res_comp (barPt A) rfl (Λ.shLift s₀) F.openImm]
  rfl

end ModularCurve.JZeroNeronObjectAtP.NeronExtension.S17EXTG

theorem solution
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
    {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension) (m : ℕ) :
    O.finPts m ≤ F.finPts m := by
  apply AddSubgroup.closure_le _ |>.mpr
  rintro x ⟨hxm, hx⟩
  exact AddSubgroup.subset_closure ⟨hxm,
    ModularCurve.JZeroNeronObjectAtP.NeronExtension.S17EXTG.extN_of_extendsToPlace' F x hx⟩

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_finPts_le_finPts
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_finPts_le_finPts (solution)

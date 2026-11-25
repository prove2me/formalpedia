-- Prove2me | solution 1 for GlobalTheory.thetaGrp_acts_linearly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:50:39.460424+00:00
-- url     : https://prove2.me/submissions/6c7d2191-fe3d-4e31-ae14-c1757d550906

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Theorems.Thm_GlobalTheory_ThetaAct_sv_ext
import Theorems.Thm_GlobalTheory_ThetaAct_sv_smul
import Theorems.Thm_GlobalTheory_ThetaAct_translT_translT
import Theorems.Thm_GlobalTheory_ThetaAct_isActOf_iff
import Theorems.Thm_GlobalTheory_ThetaAct_exists_mul
import Theorems.Thm_GlobalTheory_ThetaAct_exists_equiv
import Theorems.Thm_GlobalTheory_ThetaAct_exists_ratio
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ThetaAct CommPairing
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v) := by
  intro hG S P k T
  have hL := P.isLB
  have := P.isAb.comm
  have cm : ∀ x y : T ⟶ P.A, x * y = y * x := fun x y => _root_.mul_comm x y
  choose ρ hρ using fun θ : ThetaGrp P.A P.L k T => exists_equiv hL θ
  refine ⟨ρ, fun θ s s' => ?_, fun θx θy c H v => sv_ext hL fun y J hJ => ?_, fun θ θ' h => ?_, fun θx θy => ?_⟩
  · rw [isActOf_iff hL]
    exact ⟨fun H => sv_ext hL fun y J hJ => (hρ _ _ _ _ _ _ hJ).trans (H y J hJ).symm,
      fun H y J hJ => H ▸ hρ _ _ _ _ _ _ hJ⟩
  · have e := congrArg Units.val ((commIsOf_iff hL θx θy c).1 H _ (𝟙 _) y J hJ)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ _ ⊤ trivial] at e
    rw [sv_smul _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ,
      Category.assoc, Category.assoc, translT_translT, translT_translT, cm θy.pt, ← _root_.mul_assoc, e]
    ring
  · obtain ⟨c, hc⟩ := exists_ratio hG P.isAb hL θ θ' h
    refine ⟨c, fun v => sv_ext hL fun y J hJ => ?_⟩
    rw [sv_smul _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hc _ _ _ _ hJ, h, _root_.mul_assoc]
  · obtain ⟨θ, hp, hv⟩ := exists_mul hL θx θy
    refine ⟨θ, hp.trans (cm _ _), fun v => sv_ext hL fun y J hJ => ?_⟩
    rw [hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hv _ _ _ _ hJ, hp, Category.assoc,
      translT_translT, Units.val_mul, _root_.mul_assoc]
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.twist_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:43:37.149644+00:00
-- url     : https://prove2.me/submissions/650a460b-5bbe-483a-bfc9-c99f0131dc38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_GlobalTheory_TorsionFixedAut_sval_isActOf
import Theorems.Thm_GlobalTheory_TorsionFixedAut_secM_ext
import Theorems.Thm_GlobalTheory_TorsionFixedAut_whisker_translT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (σ : A ⟶ A)
  (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ.left, 𝟙 A.left] ![1, -1]))
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution [IsMonHom σ] (hL : L.IsLB) {k : ℤ} {T : Over S} (F : SecM A L k T → SecM A L k T)
    (hF : ∀ (v) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      secVal (SecM.toSec A (F v)) r z J =
        secVal (SecM.toSec A v) (r ≫ (T ◁ σ).left) z J * ((val c (r ≫ (snd T A).left) z J ^ k)⁻¹).val)
    (θ : ThetaGrp A L k T) (hx : θ.pt ≫ σ = θ.pt)
    (hθ : ∀ y J, Good L y J → thetaVal θ.φ (𝟙 _) y J = thetaVal θ.φ (𝟙 _ ≫ (T ◁ σ).left) y J *
      (val c (𝟙 _ ≫ (snd T A).left) y J ^ k * val c (𝟙 _ ≫ (translPt A θ.pt).left) y J ^ (-k))⁻¹)
    {v v' w' : SecM A L k T} (a₁ : IsActOf A L k θ (SecM.toSec A v) (SecM.toSec A v'))
    (a₂ : IsActOf A L k θ (SecM.toSec A (F v)) (SecM.toSec A w')) : F v' = w' := by
  refine secM_ext hL fun y J hJ => ?_
  have e₁ : translT A θ.pt ≫ snd T A = translPt A θ.pt := lift_snd _ _
  rw [hF _ _ _ _ _ hJ, sval_isActOf a₁ _ y hJ, sval_isActOf a₂ _ y hJ, hF _ _ _ _ _ hJ, hθ y J hJ]
  simp only [Category.id_comp, ← Over.comp_left]
  rw [whisker_translT σ hx, e₁, zpow_neg, mul_inv, inv_inv, Units.val_mul, Units.val_mul]
  generalize val c (translPt A θ.pt).left y J ^ k = p
  have := p.mul_inv
  linear_combination (-(thetaVal θ.φ (T ◁ σ).left y J).val * secVal (SecM.toSec A v) (T ◁ σ ≫ translT A θ.pt).left y J *
    ((val c (snd T A).left y J ^ k)⁻¹).val) * this
end GlobalTheory.TorsionFixedAut

-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.exists_linear_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:26.326743+00:00
-- url     : https://prove2.me/submissions/38c2a9db-949f-472d-88d3-88f6bbfd1f72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_GlobalTheory_ThetaScalar_exists_actVal
import Theorems.Thm_GlobalTheory_ThetaScalar_secVal_add
import Theorems.Thm_GlobalTheory_ThetaScalar_secVal_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaScalar
theorem _root_.solution (hL : L.IsLB) (θ : ThetaGrp A L k T) :
    ∃ Φ : SecM A L k T →ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ f, ActVal θ (SecM.toSec A f) (SecM.toSec A (Φ f)) := by
  choose a ha using exists_actVal hL θ
  have ext : ∀ f g : SecM A L k T, (∀ y J, Good L y J → secVal (SecM.toSec A f) (𝟙 _) y J =
      secVal (SecM.toSec A g) (𝟙 _) y J) → f = g := fun f g h => Subtype.ext (funext fun j =>
    sec_ext_val (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL
      (s := SecM.toSec A f) (s' := SecM.toSec A g) h j)
  have hb : ∀ f : SecM A L k T, ActVal θ (SecM.toSec A f) (SecM.toSec A (SecM.ofSec A (a (SecM.toSec A f)))) :=
    fun f => ha _
  refine ⟨⟨⟨fun f => SecM.ofSec A (a (SecM.toSec A f)), fun f g => ext _ _ fun y J hJ => ?_⟩,
    fun c f => ext _ _ fun y J hJ => ?_⟩, hb⟩
  · rw [secVal_add _ _ _ y hJ, hb _ _ _ y J hJ, hb _ _ _ y J hJ, hb _ _ _ y J hJ, secVal_add _ _ _ y hJ, mul_add]
  · have e : (𝟙 _ ≫ (translT A θ.pt).left) ≫ (fst T A).left = 𝟙 _ ≫ (fst T A).left := by
      rw [Category.assoc, ← Over.comp_left, translT, lift_fst]
    refine (hb (c • f) _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul c _ _ y hJ).symm)
    rw [hb f _ _ y J hJ, secVal_smul c f _ y hJ, e, mul_left_comm]
end GlobalTheory.ThetaScalar

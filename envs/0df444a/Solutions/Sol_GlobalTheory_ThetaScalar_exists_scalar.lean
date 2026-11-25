-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.exists_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:32:57.254855+00:00
-- url     : https://prove2.me/submissions/5d7e2409-34e5-47cc-93de-a151f0ca9e1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_GlobalTheory_ThetaScalar_eq_zero_of_germ
import Theorems.Thm_GlobalTheory_ThetaScalar_secVal_smul
import Theorems.Thm_GlobalTheory_ThetaScalar_exists_linear_act
import Theorems.Thm_GlobalTheory_ThetaScalar_exists_eigenvector
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
theorem _root_.solution (hL : L.IsLB) [IsIntegral (T ⊗ A).left] {F : Type} [Field F] [IsAlgClosed F]
    (e : Γ(T.left, ⊤) ≃+* F) (h0 : 0 < Module.finrank Γ(T.left, ⊤) (SecM A L k T)) (θ : ThetaGrp A L k T)
    (h : ∀ s s' t t', ActVal θ s s' → ActVal θ t t' → ∀ y J, Good L y J →
      secVal s' (𝟙 _) y J * secVal t (𝟙 _) y J = secVal t' (𝟙 _) y J * secVal s (𝟙 _) y J) :
    ∃ a : Γ(T.left, ⊤), ∀ s s', ActVal θ s s' → ∀ j, s'.f j = liftFun A _ a * s.f j := by
  obtain ⟨Φ, hΦ⟩ := exists_linear_act hL θ
  obtain ⟨a, v, hv, hav⟩ := exists_eigenvector e h0 Φ
  refine ⟨a, fun s s' hs j => sec_ext_val (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL
    (s := s') (s' := SecM.toSec A (a • SecM.ofSec A s)) (fun y J hJ => ?_) j⟩
  have hne : secVal (SecM.toSec A v) (𝟙 _) y J ≠ 0 := fun e0 => hv (Subtype.ext (funext fun i =>
    eq_zero_of_germ (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (SecM.toSec A v) y hJ e0 i))
  have H := h s s' _ _ hs (hΦ v) y J hJ
  rw [hav, secVal_smul a v _ y hJ] at H
  refine (mul_right_cancel₀ hne ?_ : secVal s' (𝟙 _) y J = _).trans (secVal_smul a (SecM.ofSec A s) _ y hJ).symm
  rw [H, mul_right_comm]
  rfl
end GlobalTheory.ThetaScalar

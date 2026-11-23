-- Prove2me | solution 1 for GlobalTheory.IntegralCoord.lin_of_sval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:36.398867+00:00
-- url     : https://prove2.me/submissions/11596920-bc17-4d9b-a2b5-b66e426c8745

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_gs_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_trans


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IntegralCoord
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
namespace GlobalTheory.IntegralCoord
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (y : Y) (J : (Y ⟶ X) → L.ι), Good L y J →
      sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y J) (j : K → L.ι) :
    s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j) := by
  refine fn_ext fun x hx => ?_
  obtain ⟨J, hJ, -⟩ := sval_trans hL s x j hx
  have hx₀ : (𝟙 Y : Y ⟶ Y) x ∈ LB.wchart L φ j := hx
  have hx' := hJ.mem φ (𝟙 Y)
  change gs (𝟙 Y) x (LB.wchart L φ j) (s.f j) =
    gs (𝟙 Y) x (LB.wchart L φ j) (∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j))
  have key : ∀ u : LB.Sec (LB.LinComb L φ ε), gs (𝟙 Y) x (LB.wchart L φ j) (u.f j) =
      (trF φ ε (𝟙 Y) x j (fun k => J (𝟙 Y ≫ φ k))).val * sval u (𝟙 Y) x J :=
    fun u => sec_trans u (𝟙 Y) x hx₀ hx'
  rw [key s, H x J hJ, SectionScalarValuation.gs_sum (𝟙 Y) x _ hx₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold resTop
  rw [gs_mul (𝟙 Y) x _ hx₀, key (t i), gs_res (𝟙 Y) x le_top hx₀]
  ring
end GlobalTheory.IntegralCoord

-- Prove2me | solution 1 for GlobalTheory.IndivisibleSection.secIsMul_of_sval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:59.13216+00:00
-- url     : https://prove2.me/submissions/9d3f2a31-f4e9-4bce-8529-964ef813770b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
import Theorems.Thm_GlobalTheory_IndivisibleSection_gs_scal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndivisibleSection
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.IndivisibleSection
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {p : Y ⟶ Sp R} {a : R}
    {s t : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = cst p y a * sval t (𝟙 Y) y J) : SecIsMul p a s t := by
  unfold SecIsMul
  intro j
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, -⟩ := exists_good L hL y (Empty.elim : Empty → (Y ⟶ X)) Empty.elim (fun a => a.elim) (fun a => a.elim)
  have hy' := hJ.mem φ (𝟙 Y)
  have e1 : gs (𝟙 Y) y ((LB.LinComb L φ ε).U j) (s.f j) = _ := sec_trans s (𝟙 Y) y hy hy'
  have e2 : gs (𝟙 Y) y ((LB.LinComb L φ ε).U j) (t.f j) = _ := sec_trans t (𝟙 Y) y hy hy'
  have e3 := h y J hJ
  unfold sval at e3
  rw [gs_mul _ _ _ hy, gs_scal p (𝟙 Y) y _ hy, e1, e2, e3]
  simp only [Category.id_comp]
  ring
end GlobalTheory.IndivisibleSection

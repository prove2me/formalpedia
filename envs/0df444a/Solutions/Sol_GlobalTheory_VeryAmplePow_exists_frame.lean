-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:11:53.325887+00:00
-- url     : https://prove2.me/submissions/7df454e1-243d-4860-b938-f6e7778add5d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_GlobalTheory_VeryAmplePow_isUnit_sval
import Theorems.Thm_GlobalTheory_VeryAmplePow_formEq_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_isUnit_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec


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
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (w : Y ⟶ X) (n : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin n) (fun _ => w) (fun _ => 1))) (x : Z ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s)
    (x' : Z ⟶ X) (e : x' = x ≫ w) :
    ∃ τ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => x') (fun _ => (n : ℤ))), τ.IsGen ∧
      ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z) (z : Z') J, Good L z J → (val τ r z J).val = sval s (r ≫ x) z J := by
  obtain ⟨t, ht⟩ := exists_sec hL (fun U _ h => (formEq_pow x' (x ≫ w) e n U h).symm) (H1.SectionArithmetic.pullSec s x)
  have ht' : ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z) (z : Z') J, Good L z J → sval t r z J = sval s (r ≫ x) z J :=
    fun Z' r z J hJ => (ht Z' r z J hJ).trans (H1.SectionArithmetic.sval_pullSec s x r z hJ)
  have hu : ∀ j, IsUnit (t.f j) := fun j => Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL t y j hy
    rw [ht' _ _ y J hJ] at e
    refine (congrArg IsUnit ((gs_eq (𝟙 Z) y _ hy _).symm.trans e)).mpr ((Units.isUnit _).mul ?_)
    exact (isUnit_sval s _ y hJ).2 (hx trivial)
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (t.compat i j), fun Z' r z J hJ =>
    (gs_unit r z _ (hJ.mem _ r) _).symm.trans (ht' Z' r z J hJ)⟩
end GlobalTheory.VeryAmplePow

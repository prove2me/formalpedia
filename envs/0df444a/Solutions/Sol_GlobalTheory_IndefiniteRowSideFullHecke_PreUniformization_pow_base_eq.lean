-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization.pow_base_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:05.056465+00:00
-- url     : https://prove2.me/submissions/90e93563-e64f-423c-af25-4fb074f8299c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PreUniformization
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
variable {R : Type} [CommRing R] [IsDomain R]
variable (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
theorem _root_.solution {k : ℕ} (p : QkPt D F k) : p.g.b ^ k = toUnit _ ≫ D.c p.y := by
  obtain ⟨h, ⟨gs, h0, hs, hl⟩, hi⟩ := p.eq
  have key : ∀ i : Fin (k + 1), (gs i).b = p.g.b ^ (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero => exact h0.1
    | succ i ih =>
      have e : (gs i.succ).b = (gs i.castSucc).b * p.g.b := (hs i).1
      rw [e, ih, Fin.val_succ, pow_succ]; rfl
  have := key (Fin.last k)
  rw [hl, Fin.val_last] at this
  exact this.symm.trans hi.1
end GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization

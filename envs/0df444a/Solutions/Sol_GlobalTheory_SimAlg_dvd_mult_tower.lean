-- Prove2me | solution 1 for GlobalTheory.SimAlg.dvd_mult_tower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:59.444024+00:00
-- url     : https://prove2.me/submissions/9a47dfa3-e3b6-4e04-8cdd-d44a9f4799e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFormEqOne
import Theorems.Thm_GlobalTheory_SimAlg_dvd_form_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SimAlg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.SimAlg
theorem _root_.solution (g : Sim D) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {a b : D.La} (hab : D.EF a b = 1) :
    (n : ℤ) ∣ g.ν (n * m) - g.ν n := by
  have h1 := g.mult n hn a b
  have h2 : (n : ℤ) ∣ _ := Dvd.dvd.trans (by push_cast; exact Dvd.intro _ rfl) (g.mult (n * m) (Nat.mul_pos hn hm) a b)
  have h3 := dvd_form_sub (g.tower n m hn hm a) (g.tower n m hn hm b)
  rw [hab] at h1 h2
  obtain ⟨c, hc⟩ := dvd_add (dvd_sub h3 h2) h1
  exact ⟨c, by linear_combination hc⟩
end GlobalTheory.SimAlg

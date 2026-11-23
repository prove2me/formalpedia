-- Prove2me | solution 1 for GlobalTheory.SimAlg.dvd_mult_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:10.682153+00:00
-- url     : https://prove2.me/submissions/3a1149bc-1a69-4f5a-98b5-70e25f1a1ba4

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
theorem _root_.solution (g : Sim D) {n : ℕ} (hn : 0 < n) {a b : D.La} (hab : D.EF a b = 1)
    (h : D.La →ₗ[𝓞 E] D.La) (hh : ∀ x, D.ModN n (g.f n (h x) - x)) :
    (n : ℤ) ∣ g.ν n * D.EF (h a) (h b) - 1 := by
  have h1 := g.mult n hn (h a) (h b)
  have h2 := dvd_form_sub (hh a) (hh b)
  rw [hab] at h2
  obtain ⟨c, hc⟩ := dvd_sub h2 h1
  exact ⟨c, by linear_combination hc⟩
end GlobalTheory.SimAlg

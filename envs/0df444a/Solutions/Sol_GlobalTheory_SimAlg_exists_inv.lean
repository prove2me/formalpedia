-- Prove2me | solution 1 for GlobalTheory.SimAlg.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:23:35.73781+00:00
-- url     : https://prove2.me/submissions/d12c1203-afaa-4504-abc6-b90bd0e7f8ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFormEqOne
import Theorems.Thm_GlobalTheory_SimAlg_modN_neg
import Theorems.Thm_GlobalTheory_SimAlg_modN_of_mul
import Theorems.Thm_GlobalTheory_SimAlg_dvd_form_sub
import Theorems.Thm_GlobalTheory_SimAlg_dvd_mult_inv

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
theorem _root_.solution (g : Sim D) {a b : D.La} (hab : D.EF a b = 1) :
    ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧
      (n : ℤ) ∣ g.ν n * g'.ν n - 1 := by
  have hex : ∀ n : ℕ, ∃ h : D.La →ₗ[𝓞 E] D.La, 0 < n →
      ∀ a, D.ModN n (h (g.f n a) - a) ∧ D.ModN n (g.f n (h a) - a) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨h, hh⟩ := g.inv n hn
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose h hh using hex
  have hν : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n * D.EF (h n a) (h n b) - 1 := fun n hn =>
    dvd_mult_inv g hn hab (h n) fun x => (hh n hn x).2
  refine ⟨⟨h, fun n => D.EF (h n a) (h n b), ?_, ?_, ?_⟩, fun n hn => ⟨hh n hn, hν n hn⟩⟩
  · intro n m hn hm x
    have h1 := modN_neg (hh n hn (h (n * m) x)).1
    have h2 := modN_neg (modN_map (h n) (g.tower n m hn hm (h (n * m) x)))
    have h3 := modN_map (h n) (modN_of_mul (hh (n * m) (Nat.mul_pos hn hm) x).2)
    convert modN_add (modN_add h1 h2) h3 using 1
    simp only [map_sub]
    abel
  · intro n hn
    exact ⟨g.f n, fun x => ⟨(hh n hn x).2, (hh n hn x).1⟩⟩
  · intro n hn x y
    have h1 := Dvd.dvd.mul_left (g.mult n hn (h n x) (h n y)) (D.EF (h n a) (h n b))
    have h2 := Dvd.dvd.mul_left (dvd_form_sub (hh n hn x).2 (hh n hn y).2) (D.EF (h n a) (h n b))
    have h3 := Dvd.dvd.mul_right (hν n hn) (D.EF (h n x) (h n y))
    obtain ⟨c, hc⟩ := dvd_sub (dvd_sub h2 h1) h3
    exact ⟨c, by linear_combination hc⟩
end GlobalTheory.SimAlg

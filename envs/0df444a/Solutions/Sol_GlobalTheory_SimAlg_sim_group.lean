-- Prove2me | solution 1 for GlobalTheory.SimAlg.sim_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:26:43.218727+00:00
-- url     : https://prove2.me/submissions/ad482fa5-9c7b-4eba-b7d5-5ee4f8ece953

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFormEqOne
import Theorems.Thm_GlobalTheory_SimAlg_exists_form_eq_one
import Theorems.Thm_GlobalTheory_SimAlg_dvd_mult_inv
import Theorems.Thm_GlobalTheory_SimAlg_dvd_mult_tower
import Theorems.Thm_GlobalTheory_SimAlg_exists_inv

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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1) := by
  intro E _ _ _ H D hpq
  obtain ⟨a, b, hab⟩ := exists_form_eq_one hpq
  refine ⟨fun g n m hn hm => ⟨dvd_mult_tower g hn hm hab, ?_⟩, ⟨one D, fun _ => ⟨rfl, rfl⟩⟩,
    fun g g' => ⟨mul g g', fun _ => ⟨rfl, rfl⟩⟩, fun g => exists_inv g hab⟩
  obtain ⟨h, hh⟩ := g.inv n hn
  obtain ⟨c, hc⟩ := dvd_mult_inv g hn hab h fun x => (hh x).2
  exact ⟨D.EF (h a) (h b), -c, by linear_combination hc⟩
end GlobalTheory.SimAlg

-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation.Presents.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:16.786945+00:00
-- url     : https://prove2.me/submissions/03c0588d-ff36-41a5-871f-26f468a8be6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PeriodMapPresentation_IsPeriodMap_map_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
namespace Presents
theorem _root_.solution {D : Datum H} {g : ℕ} {ty ty' : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J J' : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h : Presents D ty P J) (h' : Presents D ty' P J') : J = J' := by
  obtain ⟨φ, h1, h2, -⟩ := h
  obtain ⟨φ', h1', h2', -⟩ := h'
  have e : ∀ v, φ v = φ' v := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have : r ⊗ₜ[ℤ] x = r • ((1 : ℝ) ⊗ₜ[ℤ] x) := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, h1, h1']
    | add u v hu hv => simp [hu, hv]
  refine LinearMap.ext fun v => ?_
  apply φ.injective
  rw [h2, e (J' v), h2', e]
end Presents
end GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation

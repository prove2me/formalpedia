-- Prove2me | solution 1 for GlobalTheory.psWeight_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:28.713944+00:00
-- url     : https://prove2.me/submissions/65a116b3-e053-466e-8b43-eda2b8cc26eb

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    [DecidableEq σ] (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g * g')) := by
  intro α
  rw [MvPowerSeries.coeff_mul]
  refine AddValuation.map_le_sum v ?_
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [AddValuation.map_mul]
  have hs : α.sum (fun j e => ρ j * (e : ℝ)) =
      p.1.sum (fun j e => ρ j * (e : ℝ)) + p.2.sum (fun j e => ρ j * (e : ℝ)) := by
    rw [← hp]
    exact Finsupp.sum_add_index' (fun j => by simp) (fun j a b => by push_cast; ring)
  calc (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      = (((r - p.1.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
        + ((r' - p.2.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)) := by
        rw [← WithTop.coe_add, hs]
        congr 1
        ring
    _ ≤ v (MvPowerSeries.coeff p.1 g) + v (MvPowerSeries.coeff p.2 g') :=
        add_le_add (h p.1) (h' p.2)
end GlobalTheory

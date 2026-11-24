-- Prove2me | solution 1 for GlobalTheory.ZH.WtPart.eq_sum_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:47.567194+00:00
-- url     : https://prove2.me/submissions/55d6dbd0-074a-4629-b2c1-39cec95f57f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Theorems.Thm_GlobalTheory_ZH_WtPart_cf_sum
import Theorems.Thm_GlobalTheory_ZH_WtPart_cf_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}
namespace GlobalTheory.ZH.WtPart
theorem _root_.solution (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec)
    (hA : Φ.supp φ ⊆ A) (hψ : ∀ α ∈ A, Φ.IsPart α φ (ψ α)) (l : Φ.N₀.ι) :
    φ.f l = ∑ α ∈ A, (ψ α).f l := by
  refine cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun β => Eq.symm ?_
  refine (cf_sum (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β A _).trans ?_
  change ∑ α ∈ A, Φ.wt (ψ α) β l = Φ.wt φ β l
  have h0 : ∀ α ∈ A, α ≠ β → Φ.wt (ψ α) β l = 0 := fun α hα hne => by
    by_contra h
    exact hne ((hψ α hα).1 ⟨l, h⟩).symm
  by_cases hβ : β ∈ A
  · rw [Finset.sum_eq_single_of_mem β hβ h0, (hψ β hβ).2 l]
  · rw [Finset.sum_eq_zero fun α hα => h0 α hα fun e => hβ (e ▸ hα)]
    by_contra h
    exact hβ (hA ⟨l, fun e => h e.symm⟩)
end GlobalTheory.ZH.WtPart

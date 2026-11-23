-- Prove2me | solution 1 for GlobalTheory.FramePeriod.hermForm_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:26.304855+00:00
-- url     : https://prove2.me/submissions/fc49b240-e0f1-4177-80f8-7cf283d6413a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {g : ℕ} (idx : Fin g ≃ ι × Fin r)
    (s : ι → ℝ) (Hl : ι → Matrix (Fin r) (Fin r) ℂ) (z w : Fin g → ℂ) :
    hermForm (Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      (s (idx k).1 : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0) z w =
      ∑ τ, (s τ : ℂ) * hermForm (Hl τ) (fun a => z (idx.symm (τ, a))) (fun a => w (idx.symm (τ, a))) := by
  simp only [hermForm, dotProduct, mulVec, of_apply, Finset.mul_sum]
  rw [← idx.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => ?_
  rw [← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Equiv.apply_symm_apply, if_true, Pi.star_apply]
    ring
  · intro σ _ hσ
    simp [hσ.symm]
  · simp
end GlobalTheory.FramePeriod

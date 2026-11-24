-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.r_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:36.265842+00:00
-- url     : https://prove2.me/submissions/7dbc32ad-a8e6-4025-a450-92c367ddd263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution {k : ℕ} {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (a : ℕ) (ha : a ≠ 0) : μ.r k (p ^ a) (p' ^ a) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  induction a with
  | zero => simpa using h
  | succ a ih => rw [Nat.succ_eq_add_one, pow_succ, pow_succ p']; exact μ.mul _ _ _ _ _ (ih (Nat.succ_ne_zero _)) h
end GlobalTheory.Ex.RecPeriods

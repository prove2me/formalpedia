-- Prove2me | solution 1 for GlobalTheory.RootEx.ConjVol.conj_mem_of_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:47.8187+00:00
-- url     : https://prove2.me/submissions/f37a6aa6-0223-49c1-a4bc-6d431b18a64a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ConjVol
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.ConjVol
theorem _root_.solution {p : ℕ} {g u : GL (n ⊕ Fin c) k} (hg : g.val.BlockTriangular (lev p))
    (hg' : (g⁻¹).val.BlockTriangular (lev p)) (hu : u ∈ N k n c p) : g * u * g⁻¹ ∈ N k n c p := by
  rw [Model.mem_N_iff] at hu ⊢
  intro r s hrs
  have e : (g * u * g⁻¹).val = 1 + g.val * (u.val - 1) * (g⁻¹).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
    abel
  rw [e, Matrix.add_apply, add_eq_left, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : lev p s < lev p t
  · rw [hg' ht, mul_zero]
  rw [Matrix.mul_apply]
  refine mul_eq_zero_of_left (Finset.sum_eq_zero fun v _ => ?_) _
  by_cases hv : lev p v < lev p r
  · rw [hg hv, zero_mul]
  rw [Matrix.sub_apply, hu v t (by omega), sub_self, mul_zero]
end GlobalTheory.RootEx.ConjVol

-- Prove2me | solution 1 for GlobalTheory.LatticePair.ord_det_torusElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:46.602311+00:00
-- url     : https://prove2.me/submissions/3e5884dc-d3ed-4c8d-8955-49da81d15353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSum
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_GLDoubling_val_torusElt
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.LatticePair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.LatticePair
theorem _root_.solution {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) :
    ord k (Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e)) = ∑ i, e i := by
  have h1 : Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e) = ϖ ^ ∑ i, e i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_torusElt, Matrix.det_diagonal, Units.val_zpow_eq_zpow_val]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have := map_zpow o ϖ (∑ i, e i)
  rw [show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
    smul_eq_mul, mul_one, ← h1] at this
  exact this
end GlobalTheory.LatticePair

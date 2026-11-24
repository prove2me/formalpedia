-- Prove2me | solution 1 for GlobalTheory.DoublingLength.pairTerm_pairEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:33.545934+00:00
-- url     : https://prove2.me/submissions/6cf225ca-9708-4079-b230-be3ea1865fd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Theorems.Thm_GlobalTheory_DoublingLength_int_mul_of_mem_KO
import Theorems.Thm_GlobalTheory_DoublingLength_ord_det_of_mem_KO
import Theorems.Thm_GlobalTheory_DoublingLength_pairEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_HeckeSeries_ord_det_of_mem_KO
import Theorems.Thm_GlobalTheory_HeckeShift_ord_det_of_mem_KO
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LatticePair_ord_det_of_mem_KO
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
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
open scoped Classical
namespace GlobalTheory.DoublingLength
theorem _root_.solution {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (X : ℂ)
    (g h : GL (Fin n) k ⧸ KO k (Fin n)) :
    pairTerm X φ (pairEquiv k n (g, h)) =
      if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
          (∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat +
          (ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out))).toNat) * φ g.out
      else 0 := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (h.out⁻¹ * g.out)
  have hiff : (∀ i j, (h.out⁻¹ * g.out * x : GL (Fin n) k).1 i j ∈ 𝒪[k]) ↔
      ∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k] :=
    ⟨fun H => by
      have := int_mul_of_mem_KO H (inv_mem x.2)
      rwa [mul_inv_cancel_right] at this, fun H => int_mul_of_mem_KO H x.2⟩
  have hord : ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out * x : GL (Fin n) k)) =
      ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out)) := by
    rw [map_mul, ord_mul, ord_det_of_mem_KO x.2, add_zero]
  have hval : φ (h.out * (h.out⁻¹ * g.out * x)) = φ g.out := by
    rw [mul_assoc, mul_inv_cancel_left, hφ.1 _ _ x.2]
  rw [pairEquiv_apply, pairTerm]
  dsimp only
  rw [hx, hord, hval]
  exact if_congr (and_congr Iff.rfl hiff) rfl rfl
end GlobalTheory.DoublingLength

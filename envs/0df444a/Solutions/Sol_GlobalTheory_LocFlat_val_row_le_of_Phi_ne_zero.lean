-- Prove2me | solution 1 for GlobalTheory.LocFlat.val_row_le_of_Phi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:36.606832+00:00
-- url     : https://prove2.me/submissions/7feca724-da88-4ab2-a57a-fcf25b7816ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapRowEqZeroUnlessRowMemDualLattice
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_intM_of_Phi_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + 1 + c = s) (r : ℕ)
    (hc : c = 2 * r) (w : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hw : (S.T t).Phi j (c + 1) (by omega) w ≠ 0) (y : XIx (Fin κ) t j) :
    valuation k (w (Sum.inr ⟨r, by omega⟩) (Sum.inl y)) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : (S.T t).Phi j (c + 1) (by omega) w = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') w).submatrix (ixSucc _ t j) id) := rfl
  rw [hΦ] at hw
  have hI := TypeDatum.intM_of_Phi_ne_zero _ _ hw ((ixSucc _ t j).symm (o.symm (Sum.inr ⟨r, by omega⟩)))
    (o'.symm (Sum.inl y))
  have hw' : w = fromBlocks w.toBlocks₁₁ w.toBlocks₁₂ w.toBlocks₂₁ w.toBlocks₂₂ := (fromBlocks_toBlocks w).symm
  rw [hw'] at hI
  simp [LatFrame.coords, typeFrame, embA, GlobalTheory.SplitFlip.diagGL, fromBlocks_multiply] at hI
  rw [Valuation.mem_integer_iff, map_mul, map_inv₀] at hI
  have hv : 0 < valuation k ((S.ϖ : k) ^ (r + 1)) := by
    rw [zero_lt_iff]; simp
  rw [Units.val_pow_eq_pow_val]
  change valuation k (w.toBlocks₂₁ ⟨r, by omega⟩ y) ≤ _
  rwa [inv_mul_le_iff₀ hv, mul_one] at hI
end GlobalTheory.LocFlat

-- Prove2me | solution 1 for GlobalTheory.LatticePair.isInt_and_mul_torus_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:44.191711+00:00
-- url     : https://prove2.me/submissions/f5458cb9-bfa5-4fc7-b579-d3525b75ec17

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
theorem _root_.solution {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (A : GL (Fin n) k)
    (e : Fin n → ℤ) : IsInt A ∧ IsInt (A * torusElt k (Fin n) ϖ e) ↔
      IsInt (A * torusElt k (Fin n) ϖ fun i => min (e i) 0) := by
  have hle : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have hpow : ∀ m : ℤ, 0 ≤ m → (ϖ : k) ^ m ∈ 𝒪[k] := fun m hm => by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [zpow_natCast]
    exact pow_mem hle m
  have hent : ∀ (f : Fin n → ℤ) i j, (A * torusElt k (Fin n) ϖ f).1 i j = A.1 i j * (ϖ : k) ^ f j :=
    fun f i j => by rw [Units.val_mul, val_torusElt, Matrix.mul_diagonal]
  have key : ∀ (x : k) (m : ℤ), (x ∈ 𝒪[k] ∧ x * (ϖ : k) ^ m ∈ 𝒪[k]) ↔ x * (ϖ : k) ^ min m 0 ∈ 𝒪[k] := by
    intro x m
    have hz : (ϖ : k) ≠ 0 := ϖ.ne_zero
    rcases le_total m 0 with h | h
    · rw [min_eq_left h]
      refine ⟨And.right, fun h2 => ⟨?_, h2⟩⟩
      have : x = x * (ϖ : k) ^ m * (ϖ : k) ^ (-m) := by
        rw [mul_assoc, ← zpow_add₀ hz, add_neg_cancel, zpow_zero, mul_one]
      rw [this]
      exact mul_mem h2 (hpow _ (by omega))
    · rw [min_eq_right h, zpow_zero, mul_one]
      exact ⟨And.left, fun h2 => ⟨h2, mul_mem h2 (hpow _ h)⟩⟩
  simp only [IsInt, hent]
  constructor
  · rintro ⟨h1, h2⟩ i j
    exact (key _ _).1 ⟨h1 i j, h2 i j⟩
  · intro h
    exact ⟨fun i j => ((key _ _).2 (h i j)).1, fun i j => ((key _ _).2 (h i j)).2⟩
end GlobalTheory.LatticePair

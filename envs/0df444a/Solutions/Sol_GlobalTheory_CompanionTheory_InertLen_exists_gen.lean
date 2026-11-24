-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLen.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:05:52.949878+00:00
-- url     : https://prove2.me/submissions/54053176-02be-41ce-bedd-cff910d96882

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLen
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertLen
theorem _root_.solution {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {N : ℕ} (A : ℕ) (f₁ f₂ : Fin N → L) :
    ∃ y : L, WithZero.exp (A : ℤ) ≤ Valued.v y ∧ (∀ i, Valued.v (f₁ i) ≤ Valued.v y) ∧
      (∀ i, Valued.v (f₂ i) ≤ Valued.v y) ∧
      (Valued.v y = WithZero.exp (A : ℤ) ∨ (∃ i, Valued.v y = Valued.v (f₁ i)) ∨ ∃ i, Valued.v y = Valued.v (f₂ i)) := by
  classical
  let g : Option (Fin N ⊕ Fin N) → L := fun o => o.elim (ϖ ^ (-(A : ℤ))) (Sum.elim f₁ f₂)
  have hg0 : Valued.v (g none) = WithZero.exp (A : ℤ) := by
    show Valued.v (ϖ ^ (-(A : ℤ))) = _
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
    congr 1
    simp
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun o => Valued.v (g o)) Finset.univ_nonempty
  refine ⟨g k, hg0.ge.trans (hk none (Finset.mem_univ _)), fun i => hk (some (Sum.inl i)) (Finset.mem_univ _),
    fun i => hk (some (Sum.inr i)) (Finset.mem_univ _), ?_⟩
  rcases k with _ | (i | i)
  · exact Or.inl hg0
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)
end GlobalTheory.CompanionTheory.InertLen

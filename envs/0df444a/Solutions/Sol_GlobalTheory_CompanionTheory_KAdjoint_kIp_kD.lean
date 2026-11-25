-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KAdjoint.kIp_kD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:14.013245+00:00
-- url     : https://prove2.me/submissions/11449d68-9449-484c-9398-e08fcc9f026f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Theorems.Thm_GlobalTheory_CompanionTheory_KAdjoint_position_sum
import Theorems.Thm_PositivityTheory_Rg_Cz_kD_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KAdjoint
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]
namespace GlobalTheory.CompanionTheory.KAdjoint
theorem _root_.solution (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) :
    kIp B b (kD T η) θ = ((m : ℂ) + 1) * kIp B b η (kDel T' b θ) := by
  have hs : ∀ s : Fin (m + 1), ∑ I : Fin (m + 1) → β,
      B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
        = kIp B b η (kDel T' b θ) := fun s => position_sum B b T T' h η θ s
  simp only [kIp, kD_apply, Function.comp_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  simp only [kIp] at hs
  rw [Finset.sum_congr rfl fun s _ => hs s]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
end GlobalTheory.CompanionTheory.KAdjoint

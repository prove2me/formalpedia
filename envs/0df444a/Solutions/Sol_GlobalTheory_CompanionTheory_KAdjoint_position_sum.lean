-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KAdjoint.position_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:20.580607+00:00
-- url     : https://prove2.me/submissions/16866c84-eb71-4a08-85f0-70c94848ec6c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Theorems.Thm_GlobalTheory_CompanionTheory_KAdjoint_comp_insertNth_eq
import Theorems.Thm_PositivityTheory_Rg_Cz_kDel_apply


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
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) (s : Fin (m + 1)) :
    ∑ I : Fin (m + 1) → β,
        B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
      = kIp B b η (kDel T' b θ) := by
  rw [← (Fin.insertNthEquiv (fun _ => β) s).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [kIp, kDel_apply, map_sum]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, comp_insertNth_eq, Fin.insertNth_apply_same,
    Fin.removeNth_insertNth]
  rw [← h, θ.map_insertNth]
  simp only [map_zsmul, LinearMap.smul_apply, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]
end GlobalTheory.CompanionTheory.KAdjoint

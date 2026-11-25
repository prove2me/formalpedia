-- Prove2me | solution 1 for GlobalTheory.PMonE.LangOnto.exists_sol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:43:49.55452+00:00
-- url     : https://prove2.me/submissions/8736bba7-2ae7-4175-b88f-f5f07f264cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq
import Theorems.Thm_GlobalTheory_PMonE_LangOnto_exists_sub_eq_inv
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_two_le_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangOnto
open Polynomial Finset GlobalTheory.PMonE
namespace GlobalTheory.PMonE.LangOnto
theorem _root_.solution {F : Type*} [Field F] [IsAlgClosed F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] {m : Type*}
    [Fintype m] {e : ℕ} (he : 0 < e) (A : Matrix m m F) (b : m → F) :
    ∃ x : m → F, ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  have : ExpChar F p := ExpChar.prime hp.out
  have hq : 2 ≤ p ^ e := GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he
  let r : F ≃+* F := (iterateFrobeniusEquiv F p e).symm
  have hr : ∀ a : F, r a ^ p ^ e = a := fun a => by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p e).apply_symm_apply a
  have hr' : ∀ a : F, r (a ^ p ^ e) = a := fun a => by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p e).symm_apply_apply a
  let ψ : (m → F) →+ (m → F) := AddMonoidHom.mk' (fun y => A.mulVec (fun i => r (y i))) (fun y y' => by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp)
  have hψ : ∀ (c : F) (x : m → F), ψ (c ^ p ^ e • x) = c • ψ x := by
    intro c x
    change A.mulVec _ = c • A.mulVec _
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hr']
  obtain ⟨y, hy⟩ := exists_sub_eq_inv hq ψ hψ b
  refine ⟨fun i => r (y i), fun i => ?_⟩
  rw [hr, ← hy]
  rfl
end GlobalTheory.PMonE.LangOnto

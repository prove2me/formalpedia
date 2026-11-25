-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kabs.kD_kDel_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:22.851793+00:00
-- url     : https://prove2.me/submissions/c5f0a031-ca63-46ae-8f27-1e0a5b03324b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KDKDelApply
import Theorems.Thm_PositivityTheory_Rg_Cz_kD_apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kabs
namespace GlobalTheory.CompanionTheory.Kabs
theorem _root_.solution {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (Y : Fin (n + 1) → P) :
    kD T (kDel T' b θ) Y = ∑ s, ∑ i, T (Y s) (T' (b i) (θ (Function.update Y s (b i)))) := by
  rw [kD_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [kDel_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.insertNth_removeNth, θ.map_insertNth, map_zsmul, map_zsmul]
end GlobalTheory.CompanionTheory.Kabs

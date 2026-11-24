-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.mem_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:51:52.478612+00:00
-- url     : https://prove2.me/submissions/b995816d-5fa7-4488-a119-a7f3981356b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_al_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution {a : K.O} (ha : K.Small a) [Fintype ι] {e : ι → B.A} {N : ℕ} {M : Submodule K.O B.A}
    {p : ι → ℤ} (hP : Pos B a e N M p) (i : ι) {c : ℕ} {y : B.A}
    (hy : ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y)) (k : ℕ) (hk : p i + N + c ≤ 2 * k) :
    e i * (al K a ^ ((2 * k : ℕ) : ℤ) • y) ∈ M := by
  have hr := hy (2 * k - p i - N) (by omega)
  have h := (hP i).1 _ hr
  convert h using 1
  rw [mul_smul_comm, mul_smul_comm, smul_smul, ← zpow_add₀ (al_ne_zero ha)]
  congr 2; push_cast; ring
end GlobalTheory.UnitLemma.Desc.Window

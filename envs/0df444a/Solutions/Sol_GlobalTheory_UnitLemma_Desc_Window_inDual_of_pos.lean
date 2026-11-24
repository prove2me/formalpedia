-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.inDual_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:36.774332+00:00
-- url     : https://prove2.me/submissions/782be5eb-66bd-40be-adc7-82f4f9b95fb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_al_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_isIntegral_zpow_smul
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_trace_mem_of_isIntegral

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
    (hy : ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y)) (hp : (c : ℤ) ≤ p i) :
    InDual B (e i * y) M := by
  intro z hz
  have h2 := (hP i).2 z hz
  have h1 := hy c le_rfl
  have hα := al_ne_zero ha
  have heq : e i * y * z = al K a ^ (p i - c) • ((al K a ^ (c : ℤ) • y) * (al K a ^ (-p i) • (e i * z))) := by
    rw [smul_mul_smul_comm, smul_smul, ← zpow_add₀ hα, ← zpow_add₀ hα]
    have : p i - c + (c + -p i) = 0 := by ring
    rw [this, zpow_zero, one_smul]; ring
  rw [heq]
  exact trace_mem_of_isIntegral B (isIntegral_zpow_smul B a (by omega) (h1.mul h2))
end GlobalTheory.UnitLemma.Desc.Window

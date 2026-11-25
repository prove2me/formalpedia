-- Prove2me | solution 1 for GlobalTheory.GoodCorank.exists_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:27.57141+00:00
-- url     : https://prove2.me/submissions/58b6ba7e-40f3-4548-8b9b-08d88b606174

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
import Theorems.Thm_GlobalTheory_GoodCorank_div_int
import Theorems.Thm_GlobalTheory_GoodCorank_ge_ite
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GoodCorank
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.GoodCorank
theorem _root_.solution {N : ℕ} (φ : Fin (N + 1) → C) :
    ∃ A : Fin N → Fin (N + 1) → C, IsSat V A ∧ ∀ ν, ∑ k, A ν k * φ k = 0 := by
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ (fun k => V.v (φ k)) Finset.univ_nonempty
  refine ⟨fun ν k => (if k = k0.succAbove ν then 1 else 0) -
      (φ (k0.succAbove ν) / φ k0) * (if k = k0 then 1 else 0), ⟨fun ν k => ?_,
      fun k c => if k = k0.succAbove c then 1 else 0, fun k c => ge_ite _, fun c c' => ?_⟩, fun ν => ?_⟩
  · exact (ge_ite _).sub ((div_int (hk0 _ (Finset.mem_univ _))).mul_int (ge_ite _))
  · simp [Fin.succAbove_ne, eq_comm]
  · simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h0 : φ k0 = 0
    · have h1 := hk0 (k0.succAbove ν) (Finset.mem_univ _)
      rw [h0, V.v.map_zero, top_le_iff] at h1
      have h2 : φ (k0.succAbove ν) = 0 := by
        by_contra hy
        have h3 : V.v (φ (k0.succAbove ν) * (φ (k0.succAbove ν))⁻¹) = 0 := by
          rw [mul_inv_cancel₀ hy, V.v.map_one]
        rw [V.v.map_mul, h1, top_add] at h3
        exact WithTop.top_ne_zero h3
      simp [h0, h2]
    · rw [div_mul_cancel₀ _ h0, sub_self]
end GlobalTheory.GoodCorank

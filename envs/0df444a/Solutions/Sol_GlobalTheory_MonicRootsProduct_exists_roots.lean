-- Prove2me | solution 1 for GlobalTheory.MonicRootsProduct.exists_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:49.435545+00:00
-- url     : https://prove2.me/submissions/3db543ea-160f-4e17-be9c-44963abfd98b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsProdXSubCOfMonic
import Theorems.Thm_GlobalTheory_MonicRootsProduct_exists_prod_X_sub_C_of_monic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.MonicRootsProduct
namespace GlobalTheory.MonicRootsProduct
theorem _root_.solution {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ, ∏ j : Fin δ, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  have hdeg := Polynomial.degree_sum_fin_lt c
  have hmon : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).Monic := Polynomial.monic_X_pow_add hdeg
  have hd : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).natDegree = δ := by
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_of_monic _ hmon
  exact ⟨fun j => r (Fin.cast hd.symm j),
    (Fintype.prod_equiv (finCongr hd.symm) _ _ (fun j => rfl)).trans hr⟩
end GlobalTheory.MonicRootsProduct

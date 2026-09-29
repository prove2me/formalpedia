-- Prove2me | solution 1 for KummerTheory.algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0dbfbbfa-b38f-5fe8-a30a-465d47af21b8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField

set_option autoImplicit false

theorem solution (K L : Type*) [Field K] [Field L]
    [Algebra K L] {n : ℕ} (S : Finset Kˣ)
    [Polynomial.IsSplittingField K L (∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)))]
    (σ : L ≃ₐ[K] L) (hσ : ∀ α : L, ∀ u ∈ S, α ^ n = algebraMap K L (u : K) → σ α = α) : σ = 1 := by
  classical
  set f : Polynomial K := ∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)) with hf
  have hadj := Polynomial.IsSplittingField.adjoin_rootSet L f
  have key : (σ : L →ₐ[K] L) = AlgHom.id K L := by
    apply AlgHom.ext_of_adjoin_eq_top hadj
    intro α hα
    rw [Polynomial.mem_rootSet] at hα
    obtain ⟨-, hα⟩ := hα
    rw [hf, map_prod, Finset.prod_eq_zero_iff] at hα
    obtain ⟨u, hu, hαu⟩ := hα
    have hαn : α ^ n = algebraMap K L (u : K) := by
      rw [← sub_eq_zero]
      simpa using hαu
    change σ α = α
    exact hσ α u hu hαn
  ext x
  exact DFunLike.congr_fun key x

end S_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField
end P2MW
export P2MW.S_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField (solution)

-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.eq_of_exp_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:17.380473+00:00
-- url     : https://prove2.me/submissions/4a0ece3a-f020-4138-9b23-1858db6e2ab6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
open IsNilpotent
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {N N' : Matrix n n K} (hN : IsNilpotent N) (hN' : IsNilpotent N')
    {c : K} (hc : c ≠ 0) (H : ∀ k : ℕ, exp (((k : K) * c) • N) = exp (((k : K) * c) • N')) :
    N = N' := by
  obtain ⟨m, hm⟩ := hN
  obtain ⟨m', hm'⟩ := hN'
  ext i j
  let P : Matrix n n K → K[X] := fun M =>
    ∑ d ∈ Finset.range (m + m' + 2), monomial d ((d.factorial : K)⁻¹ * (M ^ d) i j)
  have hP : ∀ M : Matrix n n K, M ^ (m + m' + 2) = 0 → ∀ s : K,
      (P M).eval s = (exp (s • M)) i j := by
    intro M hM s
    rw [exp_eq_sum (k := m + m' + 2) (by rw [_root_.smul_pow, hM, smul_zero]), eval_finsetSum,
      Matrix.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eval_monomial, _root_.smul_pow, Matrix.smul_apply, Matrix.smul_apply, Rat.smul_def]
    simp only [smul_eq_mul]
    push_cast; ring
  have hPP : P N = P N' := by
    refine eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => (k : K) * c) (fun a b hab => by simpa [hc] using hab) fun k => ?_)
    show _ = _
    rw [hP N (pow_eq_zero_of_le (by omega) hm), hP N' (pow_eq_zero_of_le (by omega) hm'), H]
  have := congrArg (fun p => coeff p 1) hPP
  simpa [P, finsetSum_coeff, coeff_monomial] using this
end GlobalTheory.WeilDeligne

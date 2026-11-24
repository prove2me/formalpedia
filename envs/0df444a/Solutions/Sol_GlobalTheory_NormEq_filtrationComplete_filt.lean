-- Prove2me | solution 1 for GlobalTheory.NormEq.filtrationComplete_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:58:49.522808+00:00
-- url     : https://prove2.me/submissions/1c1ed48d-1c44-4679-a3e4-8e0dceab668a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete
import Theorems.Thm_GlobalTheory_NormEq_Cmpl_eq_zero_of_forall_mem_piPow
import Theorems.Thm_GlobalTheory_NormEq_Cmpl_exists_lim_alg
import Theorems.Thm_GlobalTheory_NormEq_mem_filt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.NormEq
open Cmpl
namespace GlobalTheory.NormEq
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)),
    GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  intro L _ _ _ σ ϖ q h P x hx
  have ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, ((x n : GlobalTheory.UTr.Alg P) - x m) ∈ piPow h P N := by
    intro N
    obtain ⟨M, hM⟩ := hx N
    refine ⟨M, fun m hm n hn => ?_⟩
    have h1 : ((x n / x m : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - 1 ∈ piPow h P N := hM m hm n hn
    have e : (x n : GlobalTheory.UTr.Alg P) - x m = (x m : GlobalTheory.UTr.Alg P) * (((x n / x m : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - 1) := by
      rw [div_eq_mul_inv, Units.val_mul]
      linear_combination (-(x n : GlobalTheory.UTr.Alg P)) * (x m).mul_inv
    rw [e]; exact Ideal.mul_mem_left _ _ h1
  have hb : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M,
      (((x n)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - ((x m)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) ∈ piPow h P N := by
    intro N
    obtain ⟨M, hM⟩ := hx N
    refine ⟨M, fun m hm n hn => ?_⟩
    have h1 : ((x n / x m : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - 1 ∈ piPow h P N := hM m hm n hn
    have e : (((x n)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - ((x m)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) =
        -(((x n)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) * (((x n / x m : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - 1) := by
      rw [div_eq_mul_inv, Units.val_mul]
      linear_combination (((x m)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) * (x n).inv_mul
    rw [e]; exact Ideal.mul_mem_left _ _ h1
  obtain ⟨y, hy⟩ := exists_lim_alg h P _ ha
  obtain ⟨y', hy'⟩ := exists_lim_alg h P _ hb
  have hyy : y * y' = 1 := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mem_piPow h P fun N => ?_
    obtain ⟨n, hn1, hn2⟩ := ((hy N).and (hy' N)).exists
    have e : y * y' - 1 = -((x n : GlobalTheory.UTr.Alg P) - y) * y' -
        (x n : GlobalTheory.UTr.Alg P) * ((((x n)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - y') := by
      linear_combination (x n).mul_inv
    rw [e]
    exact (piPow h P N).sub_mem ((piPow h P N).mul_mem_right _ ((piPow h P N).neg_mem hn1))
      ((piPow h P N).mul_mem_left _ hn2)
  refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, fun N => ?_⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hy N)
  refine ⟨M, fun n hn => ?_⟩
  rw [mem_filt, div_eq_mul_inv, Units.val_mul, Units.inv_mk, Units.val_mk]
  have e : (x n : GlobalTheory.UTr.Alg P) * y' - 1 = ((x n : GlobalTheory.UTr.Alg P) - y) * y' := by
    linear_combination hyy
  rw [e]
  exact (piPow h P N).mul_mem_right _ (hM n hn)
end GlobalTheory.NormEq

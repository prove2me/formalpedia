-- Prove2me | solution 1 for GlobalTheory.SW.Vac.exists_den_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:02.669519+00:00
-- url     : https://prove2.me/submissions/8e2fade7-1996-4d96-89af-c280ff73c721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_intM_smul
import Theorems.Thm_GlobalTheory_SW_Vac_exists_den

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (M : AddSubgroup (Matrix κ ι ℚ)) (hM : M.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, IntM ((N : ℚ) • x) := by
  classical
  obtain ⟨S, rfl⟩ := hM
  choose d hd hd' using fun x : Matrix κ ι ℚ => exists_den x
  refine ⟨∏ x ∈ S, d x, Finset.prod_pos fun x _ => hd x, fun x hx => ?_⟩
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_coe.1 hx)
    rw [hc, mul_comm, Nat.cast_mul, mul_smul]
    exact intM_smul c (hd' x)
  | zero => intro k i; simpa using isIntegral_zero
  | add x y _ _ hx hy => intro k i; rw [smul_add]; exact (hx k i).add (hy k i)
  | neg x _ hx => intro k i; rw [smul_neg]; exact (hx k i).neg
end GlobalTheory.SW.Vac

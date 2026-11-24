-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.ContractProof.contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:49:15.452315+00:00
-- url     : https://prove2.me/submissions/5da0c20e-4869-46db-8460-0393c9bd9cb9

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContracts
import Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_mat_inv_diag
import Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_mat_pow_diag
import Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_conj_mem_root
import Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_conj_mem_K
import Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_zpow_mul_int
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mem_KU_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
noncomputable section
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.ContractProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
namespace GlobalTheory.SatakeWeyl.ContractProof
theorem _root_.solution : GlobalTheory.SatakeWeyl.Contract := by
  intro L _ _ ϖ σ q r γ b s g hU hb hs hg
  obtain ⟨-, hσ, -, hv, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  refine ⟨conj_mem_root h0 γ b s g hs hg, ?_, fun hK => ?_, ?_⟩
  · have := conj_mem_root h0 γ _ s⁻¹ g (mat_inv_diag h0 b s hs) hg
    rwa [inv_inv] at this
  · refine conj_mem_K h0 hσ γ b s g hs hg fun i l h1 h2 => ?_
    refine mul_mem ?_ ((mem_KU_iff hσ g).1 hK i l)
    show Valued.v (ϖ ^ (b i - b l)) ≤ (1 : WithZero (Multiplicative ℤ))
    have := hb i l h1 h2
    rw [map_zpow₀, hv', ← WithZero.exp_zsmul, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    omega
  · choose N hN using fun p : Fin r × Fin r => zpow_mul_int hv' (mat g p.1 p.2)
    refine ⟨Finset.univ.sup N, conj_mem_K h0 hσ γ _ _ g (mat_pow_diag h0 b s hs _) hg fun i l h1 h2 => ?_⟩
    refine hN (i, l) _ ?_
    have h3 := hb i l h1 h2
    have h4 : (N (i, l) : ℤ) ≤ (Finset.univ.sup N : ℕ) := by
      exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ _)
    have h5 : (0 : ℤ) ≤ (Finset.univ.sup N : ℕ) := Int.natCast_nonneg _
    nlinarith
end GlobalTheory.SatakeWeyl.ContractProof

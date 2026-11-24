-- Prove2me | solution 1 for GlobalTheory.NormEq.Cmpl.exists_lim_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:44.0672+00:00
-- url     : https://prove2.me/submissions/bf16c54f-1c9d-494c-a467-3474d55956d3

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete
import Theorems.Thm_GlobalTheory_NormEq_Cmpl_exists_lim_of_cauchy
import Theorems.Thm_GlobalTheory_NormEq_Cmpl_mem_piPow_iff

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
open GlobalTheory GlobalTheory.NormEq GlobalTheory.NormEq.Cmpl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1))
namespace GlobalTheory.NormEq.Cmpl
theorem _root_.solution [CompleteSpace L] (a : ℕ → GlobalTheory.UTr.Alg P)
    (ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, a n - a m ∈ piPow h P N) :
    ∃ y, ∀ N, ∀ᶠ n in atTop, a n - y ∈ piPow h P N := by
  have hco : ∀ i, ∃ ℓ : L, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop,
      Valued.v ((((GlobalTheory.UTr.powBasis P).repr (a n) i : intL L) : L) - ℓ) ≤ Valued.v ϖ ^ N := by
    intro i
    refine exists_lim_of_cauchy h.2.2.2.1 _ (fun n => ((GlobalTheory.UTr.powBasis P).repr (a n) i).2) fun N => ?_
    obtain ⟨M, hM⟩ := ha N
    refine ⟨M, fun m hm n hn => ?_⟩
    have := (mem_piPow_iff h P).mp (hM m hm n hn) i
    rwa [map_sub, Finsupp.sub_apply, AddSubgroupClass.coe_sub] at this
  choose ℓ hℓO hℓ using hco
  refine ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩), fun N => ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => hℓ i N)] with n hn
  rw [mem_piPow_iff]
  intro i
  have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩)) i =
      ⟨ℓ i, hℓO i⟩ := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [map_sub, Finsupp.sub_apply, hd, AddSubgroupClass.coe_sub]
  exact hn i
end GlobalTheory.NormEq.Cmpl

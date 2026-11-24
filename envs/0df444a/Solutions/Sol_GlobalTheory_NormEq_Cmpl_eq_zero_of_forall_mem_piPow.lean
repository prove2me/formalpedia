-- Prove2me | solution 1 for GlobalTheory.NormEq.Cmpl.eq_zero_of_forall_mem_piPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:50.006997+00:00
-- url     : https://prove2.me/submissions/c35b782a-4c0e-46f6-afc0-0ca4daa75c76

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete
import Theorems.Thm_GlobalTheory_NormEq_Cmpl_exists_pow_lt
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
theorem _root_.solution {z : GlobalTheory.UTr.Alg P} (hz : ∀ N, z ∈ piPow h P N) : z = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  by_contra hne
  have hne' : (((GlobalTheory.UTr.powBasis P).repr z i : intL L) : L) ≠ 0 := fun h0 => hne (Subtype.ext h0)
  obtain ⟨N, hN⟩ := exists_pow_lt h.2.2.2.1 ((Valued.v).ne_zero_iff.mpr hne')
  exact absurd ((mem_piPow_iff h P).mp (hz N) i) (not_le.mpr hN)
end GlobalTheory.NormEq.Cmpl

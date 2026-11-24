-- Prove2me | solution 1 for GlobalTheory.NormEq.Cmpl.exists_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:26.59099+00:00
-- url     : https://prove2.me/submissions/9fab42c4-bec0-459f-9745-046e08c780c5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete

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
namespace GlobalTheory.NormEq.Cmpl
theorem _root_.solution {w γ : WithZero (Multiplicative ℤ)}
    (hw : w = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (hγ : γ ≠ 0) :
    ∃ N : ℕ, w ^ N < γ := by
  subst hw
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hγ
  refine ⟨(-Multiplicative.toAdd g).toNat + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe, ← ofAdd_toAdd g, ← ofAdd_nsmul, Multiplicative.ofAdd_lt]
  simp only [toAdd_ofAdd, smul_neg, nsmul_eq_mul, mul_one]
  omega
end GlobalTheory.NormEq.Cmpl

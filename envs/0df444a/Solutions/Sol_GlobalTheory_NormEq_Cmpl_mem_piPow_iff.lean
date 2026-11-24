-- Prove2me | solution 1 for GlobalTheory.NormEq.Cmpl.mem_piPow_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:26.623977+00:00
-- url     : https://prove2.me/submissions/07d20146-6ec9-4b8f-af4e-50ce4d381f7b

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
variable {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1))
namespace GlobalTheory.NormEq.Cmpl
theorem _root_.solution {N : ℕ} {a : GlobalTheory.UTr.Alg P} :
    a ∈ piPow h P N ↔ ∀ i, Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : intL L) : L) ≤ Valued.v ϖ ^ N := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by
    have := h.2.2.2.1; rw [h0, map_zero] at this; exact WithZero.zero_ne_coe this
  constructor
  · intro ha i
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Subring.coe_mul,
      SubmonoidClass.coe_pow, coe_piO, map_mul, map_pow]
    calc _ ≤ Valued.v ϖ ^ N * 1 := mul_le_mul' le_rfl (((GlobalTheory.UTr.powBasis P).repr c i).2)
      _ = _ := mul_one _
  · intro ha
    have hϖN : ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ0
    let d : Fin P.1.natDegree → intL L := fun i => ⟨((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N, by
      change Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N) ≤ 1
      rw [map_div₀, map_pow]
      exact (div_le_one₀ (zero_lt_iff.mpr (pow_ne_zero _ ((Valued.v).ne_zero_iff.mpr hϖ0)))).mpr (ha i)⟩
    refine Ideal.mem_span_singleton'.mpr ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm d, ?_⟩
    refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
    have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm d) i = d i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hd]
    apply Subtype.ext
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, coe_piO]
    exact mul_div_cancel₀ _ hϖN
end GlobalTheory.NormEq.Cmpl

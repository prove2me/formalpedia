-- Prove2me | solution 1 for GlobalTheory.NormEq.isUnit_one_add_piO_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:29.184298+00:00
-- url     : https://prove2.me/submissions/2970c4e0-3e64-4820-b70c-65fb9291ae23

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Theorems.Thm_GlobalTheory_NormEq_piO_mem_of_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P) :
    IsUnit (1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a) := by
  by_contra hn
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := intL L) M
  have hϖ : algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) ∈ M := piO_mem_of_isMaximal h hmax
  have h1 : 1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a ∈ M := hxM (Ideal.mem_span_singleton_self _)
  have : (1 : GlobalTheory.UTr.Alg P) ∈ M := by
    have := M.sub_mem h1 (M.mul_mem_right a hϖ)
    simpa using this
  exact hM.ne_top ((Ideal.eq_top_iff_one M).2 this)
end GlobalTheory.NormEq

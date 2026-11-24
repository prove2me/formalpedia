-- Prove2me | solution 1 for GlobalTheory.locFld
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:00:05.249005+00:00
-- url     : https://prove2.me/submissions/605c1f3e-8a7c-4597-aab7-5bf5e085285e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
import Theorems.Thm_GlobalTheory_AdicCompl_isAdicComplete
import Theorems.Thm_GlobalTheory_AdicCompl_finite_res
import Theorems.Thm_GlobalTheory_AdicCompl_exists_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open Formalism.L2.Pj Formalism.L2.PjFree
open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology
open AdicCompl
namespace GlobalTheory
theorem _root_.solution : Formalism.L2.PjFree.LocFld := by
  intro K L _ _ _ _ j la
  let : Algebra K L := j.toAlgebra
  have := la.isMaximal
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) la.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot la.ne_bot Q
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ.isPrime, hQ0⟩
  have : w.asIdeal.LiesOver la.asIdeal := hQl
  have : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  have : CharZero (adicCompletionIntegers L w) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (𝓞 L) (adicCompletionIntegers L w))
  obtain ⟨e1, he1, h1⟩ := exists_e (L := L) w
  let T : CDVR := { V := adicCompletionIntegers L w, cpl := isAdicComplete w }
  have he2 : la.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot
  refine ⟨T, kMap w, la.asIdeal.ramificationIdx' w.asIdeal * e1,
    ⟨Nat.mul_pos (Nat.pos_of_ne_zero he2) he1, fun a => ?_⟩, finite_res w⟩
  show vV (adicCompletionIntegers L w) (kMap w (j a)) = _
  simp only [vV, vLa]
  rw [h1, show j a = algebraMap K L a from rfl, ← valuation_liesOver L la w a, ← pow_mul,
    WithZero.log_pow]
  push_cast
  simp
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.CosetFn.deltaR_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:22:14.712154+00:00
-- url     : https://prove2.me/submissions/289d1df0-9a5b-4042-91d8-ac0d1ca2e54c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsParabolicDoubleCosetFunctionEqOne
import Theorems.Thm_GlobalTheory_CosetFn_deltaR_mul
import Theorems.Thm_GlobalTheory_CosetFn_mul_embX_mem_R
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.CosetFn
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.CosetFn
theorem _root_.solution {J : Subgroup (GL (n ⊕ Fin c) k)} {h : GL (n ⊕ Fin c) k}
    (H : ∀ g ∈ prX (Cgrp J h), deltaR c g = 1) {u u' j j' : GL (n ⊕ Fin c) k} {g g' : GL n k}
    (hu : u ∈ N k n c 1) (hu' : u' ∈ N k n c 1) (hj : j ∈ J) (hj' : j' ∈ J)
    (e : u * embX c g * h * j = u' * embX c g' * h * j') : deltaR c g = deltaR c g' := by
  have h1 : g'⁻¹ * g ∈ prX (Cgrp J h) := by
    refine ⟨embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹,
      Radical.conj_mem _ (mul_mem (inv_mem hu') hu), ?_⟩
    have e2 : embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹ * embX c (g'⁻¹ * g)
        = (u' * embX c g')⁻¹ * (u * embX c g) := by
      simp only [map_mul, map_inv]; group
    rw [e2]
    refine Subgroup.mem_inf.2
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (mul_embX_mem_R hu' g')) (mul_embX_mem_R hu g), ?_⟩
    have e3 : u * embX c g = u' * embX c g' * h * j' * j⁻¹ * h⁻¹ := by
      rw [← e]; group
    have e4 : h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ = j' * j⁻¹ := by
      rw [e3]; group
    show h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ ∈ J
    rw [e4]
    exact mul_mem hj' (inv_mem hj)
  have h2 := deltaR_mul (c := c) g' (g'⁻¹ * g)
  rw [H _ h1, mul_inv_cancel_left, mul_one] at h2
  exact h2
end GlobalTheory.CosetFn

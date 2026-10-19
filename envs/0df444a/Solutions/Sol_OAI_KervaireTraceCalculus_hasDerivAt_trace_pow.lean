-- Prove2me | solution 1 for OAI.KervaireTraceCalculus.hasDerivAt_trace_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:19:34.291316+00:00
-- url     : https://prove2.me/submissions/7eb4ff93-af70-4a69-8219-7df14d48edb5

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus

open OAI OAI.KervaireTraceCalculus
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped Topology
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
theorem solution (τ : E →L[𝕜] F)
    (hτ : ∀ a b : E, τ (a * b) = τ (b * a))
    {f : 𝕜 → E} {f' : E} {x : 𝕜} (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun y => τ (f y ^ n)) (n • τ (f x ^ (n - 1) * f')) x := by
  have key : ∀ n : ℕ, HasDerivAt (fun y => f y ^ n)
      (∑ k ∈ Finset.range n, f x ^ k * f' * f x ^ (n - 1 - k)) x := by
    intro n
    induction n with
    | zero => simpa using hasDerivAt_const x (1 : E)
    | succ n ih =>
      have := ih.fun_mul hf
      simp only [← pow_succ] at this
      convert this using 1
      rw [Finset.sum_range_succ, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk' := Finset.mem_range.1 hk
        rw [mul_assoc (f x ^ k * f') _ (f x), ← pow_succ]
        congr 2; omega
      · simp
  have h1 := τ.hasFDerivAt.comp_hasDerivAt x (key n)
  refine HasDerivAt.congr_deriv (h1 : HasDerivAt (fun y => τ (f y ^ n)) _ x) ?_
  rw [map_sum]
  have hterm : ∀ k ∈ Finset.range n, τ (f x ^ k * f' * f x ^ (n - 1 - k)) = τ (f x ^ (n - 1) * f') := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [hτ, ← mul_assoc, ← pow_add]
    congr 3; omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]

-- Prove2me | solution 1 for GlobalTheory.BK.derivative_mem_away
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:02.639874+00:00
-- url     : https://prove2.me/submissions/20796c16-ea94-47a8-adc7-8ab46fe94434

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution {B : Subalgebra O K⟦X⟧} (s : B)
    (hB : ∀ f ∈ B, PowerSeries.derivative K f ∈ B) {f : K⟦X⟧} (hf : f ∈ away B s) :
    PowerSeries.derivative K f ∈ away B s := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n + 1, ?_⟩
  have h1 := B.mul_mem s.2 (hB _ hn)
  have h2 := B.mul_mem (B.mul_mem (natCast_mem B n) (hB _ s.2)) hn
  convert B.sub_mem h1 h2 using 1
  rw [Derivation.leibniz, derivative_pow]
  cases n with
  | zero => simp
  | succ n => simp only [smul_eq_mul, Nat.add_sub_cancel]; ring
end GlobalTheory.BK

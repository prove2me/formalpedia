-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.companionMatrixOfCoeffs_pow_mulVec_first_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:32.129329+00:00
-- url     : https://prove2.me/submissions/65ae75e4-55c6-47ee-abd4-a5322d6eaa0c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbitProper
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.OrbitProper
theorem _root_.solution (p : Fin r → k) (n : ℕ) (hn : n < r) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = Pi.single (⟨n, hn⟩ : Fin r) 1 := by
  induction n with
  | zero =>
    rw [pow_zero, one_mulVec]
    funext i
    simp [Pi.single_apply, Fin.ext_iff]
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), mulVec_single_one]
    funext i
    simp only [companion, transpose_apply, of_apply, Pi.single_apply, Fin.ext_iff]
    have : ¬ (n + 1 = r) := by omega
    simp [this]
end GlobalTheory.JR.OrbitProper

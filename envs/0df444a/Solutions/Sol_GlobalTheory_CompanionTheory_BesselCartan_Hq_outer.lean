-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.Hq_outer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:10.33269+00:00
-- url     : https://prove2.me/submissions/43ac8221-b7a2-46f1-9ddf-d6cde8dded69

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCartan
open scoped ComplexOrder
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCartan
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) (hi : outer k r i) (hij : i.val + j.val = 2 * r + k) :
    Hq k r *ᵥ bvec j = bvec i := by
  have hHq : ∀ i j : Fin (2 * r + k + 1), Hq k r i j =
      if outer k r i then (if (i : ℕ) + (j : ℕ) = 2 * r + k then 1 else 0) else if i = j then 1 else 0 :=
    fun _ _ => rfl
  have hout : ∀ i : Fin (2 * r + k + 1), outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := fun _ => Iff.rfl
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  funext m
  have hm := m.isLt
  have hjl := j.isLt
  simp only [Matrix.mulVec, dotProduct, hbv, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hout] at hi
  simp only [hHq, hout, Fin.ext_iff]
  split_ifs <;> (try simp) <;> omega
end GlobalTheory.CompanionTheory.BesselCartan

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuTorConj.uw_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:48.808422+00:00
-- url     : https://prove2.me/submissions/9598a774-969b-4ff0-adfb-c09c1f9ed997

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugacy
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorConj_hpk_row
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorConj_uw_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuTorConj
namespace GlobalTheory.CompanionTheory.BmuTorConj
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (q : Fin (2 * r + k + 1)) (hq : q.val < r ∨ r + k < q.val)
    (j : Fin (2 * r + k + 1)) : h q j = if j = q then 1 else 0 := by
  have hqlt := q.isLt
  obtain ⟨p, hpd⟩ : ∃ p : Fin (2 * r + k + 1), p.val = 2 * r + k - q.val := ⟨⟨2 * r + k - q.val, by omega⟩, rfl⟩
  have hp : p.val < r ∨ r + k < p.val := by omega
  have hpq : p.val + q.val = 2 * r + k := by omega
  have hor : p.val < r ∨ q.val < r := by omega
  have hc : ∀ i, h i p = if i = p then 1 else 0 := uw_col k r z h hh p hp
  have hr : ∀ j', Hpk k r p j' = if j' = q then 1 else 0 := hpk_row k r p q hpq hor
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hx := congrFun (congrFun hU p) j
  simp only [mul_apply, conjTranspose_apply, hc, hr] at hx
  simpa [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, hr] using hx
end GlobalTheory.CompanionTheory.BmuTorConj

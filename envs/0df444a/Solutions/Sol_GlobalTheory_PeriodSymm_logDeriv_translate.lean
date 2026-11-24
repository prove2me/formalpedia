-- Prove2me | solution 1 for GlobalTheory.PeriodSymm.logDeriv_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:32.496802+00:00
-- url     : https://prove2.me/submissions/01545ebd-076e-483c-9711-75ff83a8332d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
open GlobalTheory GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PeriodSymm
theorem _root_.solution {g : ℕ} {U : Set (Fin g → ℂ)} (hU : IsOpen U) {a : (Fin g → ℂ) → ℂ}
    (ha : DifferentiableOn ℂ a U) (ha0 : ∀ z ∈ U, a z ≠ 0) (l w : Fin g → ℂ) (e : ℂ)
    (hinv : ∀ z ∈ U, z + l ∈ U)
    (hf : ∀ z ∈ U, a z = e * cexp (π * (z ⬝ᵥ w)) * a (z + l)) (m : Fin g) {z : Fin g → ℂ}
    (hz : z ∈ U) :
    fderiv ℂ a (z + l) (Pi.single m 1) / a (z + l)
      = fderiv ℂ a z (Pi.single m 1) / a z - π * w m := by
  have hz' : z + l ∈ U := hinv z hz
  have ha1 : a (z + l) ≠ 0 := ha0 _ hz'
  let L : (Fin g → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun x => x ⬝ᵥ w
      map_add' := fun x y => add_dotProduct x y w
      map_smul' := fun c x => smul_dotProduct c x w }
  have hL : ∀ x, L x = x ⬝ᵥ w := fun x => rfl
  have hE : HasFDerivAt (fun x => e * cexp (π * (x ⬝ᵥ w)))
      (e • (cexp (π * (z ⬝ᵥ w)) • ((π : ℂ) • L))) z := by
    have h0 : HasFDerivAt (fun x => (π : ℂ) * L x) ((π : ℂ) • L) z := L.hasFDerivAt.const_mul _
    exact h0.cexp.const_mul e
  have hA0 : HasFDerivAt a (fderiv ℂ a (z + l)) (z + l) :=
    (ha.differentiableAt (hU.mem_nhds hz')).hasFDerivAt
  have hA : HasFDerivAt (fun x => a (x + l)) (fderiv ℂ a (z + l)) z := by
    have h3 := hA0.comp z ((hasFDerivAt_id z).add_const l)
    simp only [ContinuousLinearMap.comp_id] at h3
    exact h3
  have hev : a =ᶠ[𝓝 z] fun x => e * cexp (π * (x ⬝ᵥ w)) * a (x + l) := by
    filter_upwards [hU.mem_nhds hz] with x hx using hf x hx
  have hP : HasFDerivAt (fun x => e * cexp (π * (x ⬝ᵥ w)) * a (x + l))
      ((e * cexp (π * (z ⬝ᵥ w))) • fderiv ℂ a (z + l)
        + a (z + l) • (e • (cexp (π * (z ⬝ᵥ w)) • ((π : ℂ) • L)))) z := hE.mul hA
  have hD := (hP.congr_of_eventuallyEq hev).fderiv
  have hD' : fderiv ℂ a z (Pi.single m 1)
      = e * cexp (π * (z ⬝ᵥ w)) * fderiv ℂ a (z + l) (Pi.single m 1)
        + a (z + l) * (e * (cexp (π * (z ⬝ᵥ w)) * (π * w m))) := by
    rw [hD]
    simp [hL]
  have hEz : e * cexp (π * (z ⬝ᵥ w)) ≠ 0 := by
    intro h0
    exact ha0 z hz (by rw [hf z hz, h0, zero_mul])
  have he : e ≠ 0 := left_ne_zero_of_mul hEz
  have hX : cexp (π * (z ⬝ᵥ w)) ≠ 0 := Complex.exp_ne_zero _
  rw [hD', hf z hz]
  field_simp
  ring
end GlobalTheory.PeriodSymm

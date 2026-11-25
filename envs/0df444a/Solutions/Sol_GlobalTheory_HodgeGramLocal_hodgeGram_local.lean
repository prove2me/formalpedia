-- Prove2me | solution 1 for GlobalTheory.HodgeGramLocal.hodgeGram_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:37.261898+00:00
-- url     : https://prove2.me/submissions/7618d279-1284-43dc-8729-269c6ee4c50b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
import Theorems.Thm_GlobalTheory_HodgeGramLocal_del_im_of_differentiableAt
import Theorems.Thm_GlobalTheory_HodgeGramLocal_ddbar_im_of_contDiffAt
import Theorems.Thm_GlobalTheory_HodgeGramLocal_contDiffAt_im_of_analyticAt
import Theorems.Thm_GlobalTheory_HodgeGramLocal_exp_locLog
import Theorems.Thm_GlobalTheory_HodgeGramLocal_hasDerivAt_locLog
import Theorems.Thm_GlobalTheory_HodgeGramLocal_isOpen_polydisc
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HodgePeriodGram_im_period
import Theorems.Thm_GlobalTheory_IsPshC2On_add
import Theorems.Thm_GlobalTheory_ddbar_congr
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeGramLocal
variable {n a g : ℕ}
namespace GlobalTheory.HodgeGramLocal
theorem _root_.solution (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (hP : IsPeriodChart rk τ₀ B) :
    ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧
      (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) •
        ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) +
          ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) •
            ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧
      ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  intro z hz
  let V : Set (Fin n → ℂ) := {x | x ∈ polydisc n 1 ∧
    ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane}
  have hVo : IsOpen V := by
    have h2 : IsOpen {x : Fin n → ℂ |
        ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_slitPlane.preimage (by fun_prop)
    exact (isOpen_polydisc n).inter h2
  have hzV : z ∈ V := ⟨hz.1, fun i => by rw [div_self (hz.2 i)]; exact one_mem_slitPlane⟩
  have hV : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]

  have hterm : ∀ (j k : Fin g) (i : Fin a) (x : Fin n → ℂ), x ∈ V →
      HasFDerivAt (fun y : Fin n → ℂ => locLog (z (Fin.castLE ha i)) (y (Fin.castLE ha i)) /
        (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ))
        ((1 / z (Fin.castLE ha i) / (x (Fin.castLE ha i) / z (Fin.castLE ha i)) /
          (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k i x hx => by
      have h1 := ((hasDerivAt_locLog (hx.2 i)).div_const (2 * (Real.pi : ℂ) * I)).mul_const
        ((B i j k : ℤ) : ℂ)
      have h2 : HasFDerivAt (fun y : Fin n → ℂ => y (Fin.castLE ha i))
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
        hasFDerivAt_apply _ _
      exact h1.comp_hasFDerivAt x h2
  have hτ : ∀ j k, ∀ x ∈ V, HasFDerivAt (fun y => τ₀ y j k) (fderiv ℂ (fun y => τ₀ y j k) x) x :=
    fun j k x hx => ((hP.holo j k).differentiableAt ((isOpen_polydisc n).mem_nhds hx.1)).hasFDerivAt
  have hloc : ∀ j k, ∀ x ∈ V, HasFDerivAt (locEntry ha τ₀ B z j k)
      (fderiv ℂ (fun y => τ₀ y j k) x + ∑ i, (1 / z (Fin.castLE ha i) /
        (x (Fin.castLE ha i) / z (Fin.castLE ha i)) / (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k x hx => (hτ j k x hx).add (HasFDerivAt.fun_sum fun i _ => hterm j k i x hx)
  have hdiff : ∀ j k, DifferentiableOn ℂ (locEntry ha τ₀ B z j k) V := fun j k x hx =>
    (hloc j k x hx).differentiableAt.differentiableWithinAt
  have hF : ∀ j k, AnalyticAt ℂ (locEntry ha τ₀ B z j k) z := fun j k =>
    ReciprocityTheory.AnForm.Osgood.osgood n V _ hVo (hdiff j k) z hzV
  have heq : ∀ x ∈ V, hodgeGram ha τ₀ B x = of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) := by
    intro x hx
    have hL : ∀ i, exp ((fun i => locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i))) i) =
        x (Fin.castLE ha i) := fun i => exp_locLog (hz.2 i) (hx.2 i)
    rw [hodgeGram, ← im_period ha τ₀ B x _ hL]
    ext j k
    simp [period, locEntry, Matrix.sum_apply]
  have hev : hodgeGram ha τ₀ B =ᶠ[𝓝 z] fun x => of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) :=
    Filter.eventually_of_mem hV heq
  have hev' : ∀ j k, (fun x => hodgeGram ha τ₀ B x j k) =ᶠ[𝓝 z]
      fun x => ((locEntry ha τ₀ B z j k x).im : ℂ) := fun j k =>
    Filter.eventually_of_mem hV fun x hx => by
      show hodgeGram ha τ₀ B x j k = _
      rw [heq x hx]; rfl
  refine ⟨fun j k => (contDiffAt_im_of_analyticAt (hF j k)).congr_of_eventuallyEq (hev' j k),
    fun ξ => ?_, fun ξ η => ?_⟩
  · rw [mdel_congr hev]
    ext j k
    simp only [mdel_apply, of_apply]
    rw [del_im_of_differentiableAt (hF j k).differentiableAt, (hloc j k z hzV).fderiv]
    simp [Matrix.sum_apply, div_self (hz.2 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · ext j k
    rw [mddbar_apply, ddbar_congr (hev' j k),
      ddbar_im_of_contDiffAt ((hF j k).contDiffAt)]
    rfl
end GlobalTheory.HodgeGramLocal

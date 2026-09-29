-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisReparamJet5.qdata5_eq_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:24:59.601162+00:00
-- url     : https://prove2.me/submissions/9b40c23f-80ef-4e5b-a2a7-78d36a0caef6

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_derivative_semantics
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_Certificates_E8InverseJet5Bridge_e8QCanonicalJet5_soundAt_unconditional

section
namespace GeneralCK.Certificates
namespace Jet5



theorem SoundAt.comp {f g : Jet5} {a : ℝ}
    (hf : f.SoundAt (g.d0 a)) (hg : g.SoundAt a) :
    (f.comp g).SoundAt a := by
  have f0 := hf.1.comp a hg.1
  have f1 := hf.2.1.comp a hg.1
  have f2 := hf.2.2.1.comp a hg.1
  have f3 := hf.2.2.2.1.comp a hg.1
  have f4 := hf.2.2.2.2.comp a hg.1
  refine ⟨f0, ?_, ?_, ?_, ?_⟩
  · convert! f1.mul hg.2.1 using 1 <;>
      simp only [Jet5.comp, Function.comp_def, Pi.mul_apply] <;>
      first | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring) | ring
  · have h := (f2.mul (hg.2.1.pow 2)).add (f1.mul hg.2.2.1)
    convert! h using 1 <;>
      simp only [Jet5.comp, Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
      first | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring) | ring
  · have h := ((f3.mul (hg.2.1.pow 3)).add
      (((f2.mul hg.2.1).mul hg.2.2.1).const_mul 3)).add (f1.mul hg.2.2.2.1)
    convert! h using 1 <;>
      simp only [Jet5.comp, Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
      first | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring) | ring
  · have h := ((((f4.mul (hg.2.1.pow 4)).add
      (((f3.mul (hg.2.1.pow 2)).mul hg.2.2.1).const_mul 6)).add
      ((f2.mul (hg.2.2.1.pow 2)).const_mul 3)).add
      (((f2.mul hg.2.1).mul hg.2.2.2.1).const_mul 4)).add (f1.mul hg.2.2.2.2)
    convert! h using 1 <;>
      simp only [Jet5.comp, Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
      first | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring) | ring



theorem eqAt_of_soundOn {f g : Jet5} {U : Set ℝ} (hU : IsOpen U)
    (hf : f.SoundOn U) (hg : g.SoundOn U)
    (h0 : Set.EqOn f.d0 g.d0 U) {a : ℝ} (ha : a ∈ U) : f.EqAt g a := by
  have step {u v du dv : ℝ → ℝ}
      (hu : ∀ x ∈ U, HasDerivAt u (du x) x)
      (hv : ∀ x ∈ U, HasDerivAt v (dv x) x)
      (he : Set.EqOn u v U) : Set.EqOn du dv U := by
    intro x hx
    have hevent : u =ᶠ[nhds x] v := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) he
    exact (hu x hx).unique ((hv x hx).congr_of_eventuallyEq hevent)
  have h1 := step (fun x hx => (hf x hx).1) (fun x hx => (hg x hx).1) h0
  have h2 := step (fun x hx => (hf x hx).2.1) (fun x hx => (hg x hx).2.1) h1
  have h3 := step (fun x hx => (hf x hx).2.2.1) (fun x hx => (hg x hx).2.2.1) h2
  have h4 := step (fun x hx => (hf x hx).2.2.2.1) (fun x hx => (hg x hx).2.2.2.1) h3
  have h5 := step (fun x hx => (hf x hx).2.2.2.2) (fun x hx => (hg x hx).2.2.2.2) h4
  exact ⟨h0 ha, h1 ha, h2 ha, h3 ha, h4 ha, h5 ha⟩

end Jet5

namespace E8TAxisReparamJet5

open E8InverseJet5Bridge





theorem qdata5_eq_of_comp {x y f : Jet5} {a : ℝ}
    (heq : x.EqAt (f.comp y) a) (hp : y.d1 a ≠ 0) :
    (qdata5 x y).EqAt (atParam f y) a := by
  rcases heq with ⟨h0, h1, h2, h3, h4, h5⟩
  dsimp only [Jet5.comp] at h0 h1 h2 h3 h4 h5
  dsimp only [Jet5.EqAt, qdata5, atParam, Function.comp_def]
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]
    field_simp [hp]
  · rw [h1, h2]
    field_simp [hp]
    <;> ring
  · rw [h1, h2, h3]
    field_simp [hp]
    <;> ring
  · rw [h1, h2, h3, h4]
    field_simp [hp]
    <;> ring
  · rw [h1, h2, h3, h4, h5]
    field_simp [hp]
    <;> ring






end E8TAxisReparamJet5
end GeneralCK.Certificates
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisReparamJet5
open E8InverseJet5Bridge
theorem solution {x y : Jet5} {U : Set ℝ}
    (hU : IsOpen U) (hx : x.SoundOn U) (hy : y.SoundOn U)
    (hrange : ∀ a ∈ U, y.d0 a ∈ GeneralCK.e8SlopeRange)
    (hvalue : ∀ a ∈ U, x.d0 a = GeneralCK.e8Q (y.d0 a))
    {a : ℝ} (ha : a ∈ U) (hp : y.d1 a ≠ 0) :
    (qdata5 x y).EqAt (atParam (e8QJet5 e8ThetaCanonicalJet5) y) a := by
  apply qdata5_eq_of_comp (hp := hp)
  apply Jet5.eqAt_of_soundOn hU hx
  · intro b hb
    exact (e8QCanonicalJet5_soundAt_unconditional (hrange b hb)).comp (hy b hb)
  · exact hvalue
  · exact ha

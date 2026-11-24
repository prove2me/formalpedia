-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KrullLocal.exists_ringHom_of_fractions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:34.437202+00:00
-- url     : https://prove2.me/submissions/ed428b53-eb24-4b2e-a0d3-b33516a5d9b6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KrullLocal
namespace GlobalTheory.CompanionTheory.KrullLocal
theorem _root_.solution {B C D : Type} [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime] (φ : B →+* D)
    (hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ t))
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ q ∧ v * algebraMap B C b = 0) → φ b = 0) :
    ∃ g : C →+* D, (∀ b, g (algebraMap B C b) = φ b) ∧ ∀ v, v ∉ q → IsUnit (g v) := by
  classical
  choose bb tt ht vv hv hvt using h1
  have hmul : ∀ {x y : C}, x ∉ q → y ∉ q → x * y ∉ q := fun hx hy hm =>
    (hq.mem_or_mem hm).elim hx hy
  have hone : (1 : C) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
  have hone' : algebraMap B C 1 ∉ q := by simpa using hone
  let f : C → D := fun c => φ (bb c) * Ring.inverse (φ (tt c))
  have hft : ∀ c, f c * φ (tt c) = φ (bb c) := by
    intro c
    simp only [f]
    rw [mul_assoc, Ring.inverse_mul_cancel _ (hu _ (ht c)), mul_one]
  have key : ∀ (c : C) (b t : B) (v : C), algebraMap B C t ∉ q → v ∉ q →
      v * (algebraMap B C t * c) = v * algebraMap B C b → f c * φ t = φ b := by
    intro c b t v htq hvq h
    have hz : φ (tt c * b - t * bb c) = 0 := by
      apply h2
      refine ⟨vv c * v, hmul (hv c) hvq, ?_⟩
      have h' := hvt c
      simp only [map_sub, map_mul]
      linear_combination (-(vv c * algebraMap B C (tt c))) * h + (v * algebraMap B C t) * h'
    have hz' : φ (tt c) * φ b = φ (tt c) * (f c * φ t) := by
      have e : φ (tt c) * φ b - φ t * φ (bb c) = 0 := by simpa using hz
      rw [← hft c] at e
      linear_combination e
    exact ((hu _ (ht c)).mul_left_cancel hz').symm
  have hhom1 : f 1 = 1 := by
    have := key 1 1 1 1 hone' hone (by simp)
    simpa using this
  have hhom0 : f 0 = 0 := by
    have := key 0 0 1 1 hone' hone (by simp)
    simpa using this
  have hhommul : ∀ c c', f (c * c') = f c * f c' := by
    intro c c'
    have e := key (c * c') (bb c * bb c') (tt c * tt c') (vv c * vv c')
      (by rw [map_mul]; exact hmul (ht c) (ht c')) (hmul (hv c) (hv c'))
      (by
        have h := hvt c
        have h' := hvt c'
        simp only [map_mul]
        linear_combination (vv c' * algebraMap B C (tt c') * c') * h +
          (vv c * algebraMap B C (bb c)) * h')
    have hU : IsUnit (φ (tt c * tt c')) := by
      rw [map_mul]; exact (hu _ (ht c)).mul (hu _ (ht c'))
    apply hU.mul_right_cancel
    rw [e, map_mul, map_mul, ← hft c, ← hft c']
    ring
  have hhomadd : ∀ c c', f (c + c') = f c + f c' := by
    intro c c'
    have e := key (c + c') (tt c' * bb c + tt c * bb c') (tt c * tt c') (vv c * vv c')
      (by rw [map_mul]; exact hmul (ht c) (ht c')) (hmul (hv c) (hv c'))
      (by
        have h := hvt c
        have h' := hvt c'
        simp only [map_mul, map_add]
        linear_combination (vv c' * algebraMap B C (tt c')) * h +
          (vv c * algebraMap B C (tt c)) * h')
    have hU : IsUnit (φ (tt c * tt c')) := by
      rw [map_mul]; exact (hu _ (ht c)).mul (hu _ (ht c'))
    apply hU.mul_right_cancel
    rw [e, map_add, map_mul, map_mul, map_mul, ← hft c, ← hft c']
    ring
  refine ⟨{ toFun := f, map_one' := hhom1, map_mul' := hhommul, map_zero' := hhom0,
            map_add' := hhomadd }, ?_, ?_⟩
  · intro b
    have := key (algebraMap B C b) b 1 1 hone' hone (by simp [mul_comm])
    simpa using this
  · intro v hvq
    have hb : algebraMap B C (bb v) ∉ q := by
      intro hm
      have h := hvt v
      have : vv v * (algebraMap B C (tt v) * v) ∈ q := by
        rw [h]; exact q.mul_mem_left _ hm
      exact hmul (hv v) (hmul (ht v) hvq) this
    have hU := hu _ hb
    rw [← hft v] at hU
    exact isUnit_of_mul_isUnit_left hU
end GlobalTheory.CompanionTheory.KrullLocal

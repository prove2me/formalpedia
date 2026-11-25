-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzFiniteTruncationIdentityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:56:44.302267+00:00
-- url     : https://prove2.me/submissions/7e541ff3-2856-42d5-b1a8-a25bf83d8f20

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineRightCoercionV1
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineLeftCoercionV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpTelescopingV2
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpFderivIntegrableV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

set_option maxHeartbeats 800000 in
/-- Transfer the finite-jump identity from real to nonnegative real time. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (omega : Omega) (c : ℝ)
    (U : NNReal → ℝ) (K : NNReal) (hULip : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (t : NNReal) :
    let j : Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    ∀ S : Finset (Ioc (0 : NNReal) t),
      f (U t,P S t) = f (U 0,X 0 omega) + c *
        (∫ u in Icc (0 : ℝ) (t : ℝ),
          fderiv ℝ f (U u.toNNReal,P S u.toNNReal) (0,1) ∂volume) +
        (∫ u in Icc (0 : ℝ) (t : ℝ),
          fderiv ℝ f (U u.toNNReal,P S u.toNNReal) (1,0) *
            deriv (fun z : ℝ => U z.toNNReal) u ∂volume) +
        ∑ s ∈ S, (f (U s,P S s) - f (U s,Q S s)) := by
  classical
  intro j P Q S
  let I := Ioc (0 : NNReal) t
  let τ : I → ℝ := fun s => ((s : NNReal) : ℝ)
  have hτ : StrictMono τ := fun i j hij => hij
  let R (S : Finset I) (u : ℝ) :=
    X 0 omega + c * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
  let B (S : Finset I) (u : ℝ) :=
    X 0 omega + c * u + ∑ s ∈ S, if τ s < u then j s else 0
  let V : ℝ → ℝ := fun u => U u.toNNReal
  have hV : LipschitzWith K V := by
    simpa only [V, Function.comp_def, mul_one] using
      hULip.comp Real.lipschitzWith_toNNReal
  have hn (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (t : ℝ)) : 0 ≤ V u := by
    by_cases hz : u = 0
    · simpa [hz,V] using hU0
    · have hpos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hz)
      exact (hUp u.toNNReal (by
        rw [← NNReal.coe_pos, Real.coe_toNNReal u hpos.le]; exact hpos)).le
  have hp (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) (t : ℝ)) : 0 < V u :=
    hUp u.toNNReal (by
      rw [← NNReal.coe_pos, Real.coe_toNNReal u hu.1.le]; exact hu.1)
  have ht := t.coe_nonneg
  have hR (u : ℝ) (hu : 0 ≤ u) : R S u = P S u.toNNReal :=
    Kyprianou.Ch04.bvNNRealFiniteAffineRightCoercionV1
      (fun s : I => (s : NNReal)) j (X 0 omega) c S u hu
  have hpost (u : NNReal) : R S (u : ℝ) = P S u := by
    simpa only [Real.toNNReal_coe] using hR (u : ℝ) u.coe_nonneg
  have hpre (u : NNReal) : B S (u : ℝ) = Q S u :=
    Kyprianou.Ch04.bvNNRealFiniteAffineLeftCoercionV1
      (fun s : I => (s : NNReal)) j (X 0 omega) c S u
  let F (v : ℝ × ℝ) (u : ℝ) := fderiv ℝ f (V u,R S u) v
  have hi (v : ℝ × ℝ) : IntervalIntegrable (F v) volume 0 (t : ℝ) :=
    Kyprianou.Ch04.exercise42LipschitzFiniteJumpFderivIntegrableV1
      τ hτ j (X 0 omega) c V K hV f hf v S (t : ℝ) ht
      (fun s _ => s.property.1) (fun s _ => s.property.2) hn hp
  have hiW : IntervalIntegrable (fun u => F (1,0) u * deriv V u)
      volume 0 (t : ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
    exact (hi (1,0)).1.mul_bdd (aestronglyMeasurable_deriv _ _)
      (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hV))
  have h := Kyprianou.Ch04.exercise42LipschitzFiniteJumpTelescopingV2
    τ hτ j (X 0 omega) c V K hV f hf S (t : ℝ) ht
    (fun s _ => s.property.1) (fun s _ => s.property.2) hn hp
  change f (V t,R S t) = f (V 0,X 0 omega) +
    (∫ u in 0..(t : ℝ), F (1,0) u * deriv V u + c * F (0,1) u) +
      ∑ s ∈ S, (f (V (τ s),R S (τ s)) - f (V (τ s),B S (τ s))) at h
  rw [intervalIntegral.integral_add hiW ((hi (0,1)).const_mul c),
    intervalIntegral.integral_const_mul] at h
  have hI (v : ℝ × ℝ) (w : ℝ → ℝ) :
      (∫ u in 0..(t : ℝ), F v u * w u) =
      ∫ u in Icc (0 : ℝ) (t : ℝ),
        fderiv ℝ f (U u.toNNReal,P S u.toNNReal) v * w u ∂volume := by
    rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only [F,V,hR u hu.1]
  have hIw := hI (1,0) (deriv V)
  have hId := hI (0,1) (fun _ => 1)
  simp only [mul_one] at hId
  rw [hIw,hId,hpost t] at h
  simpa only [V, τ, Real.toNNReal_coe, Real.toNNReal_zero, hpost, hpre,
    add_assoc, add_left_comm, add_comm] using h

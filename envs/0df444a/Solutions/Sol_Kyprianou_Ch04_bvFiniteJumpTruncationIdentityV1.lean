-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteJumpTruncationIdentityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:36:10.812463+00:00
-- url     : https://prove2.me/submissions/8c9062da-0cb5-48c6-80f2-d21e2c441095

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineRightCoercionV1
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineLeftCoercionV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpTelescopingV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpDerivativeIntervalIntegrableV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : forall t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (t : NNReal) :
    let jump : Set.Ioc (0 : NNReal) t → Real :=
      fun s => X s omega - Xleft s omega
    let approx : Finset (Set.Ioc (0 : NNReal) t) → NNReal → Real :=
      fun S u => X 0 omega + c * (u : Real) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then jump s else 0
    let before : Finset (Set.Ioc (0 : NNReal) t) → NNReal → Real :=
      fun S u => X 0 omega + c * (u : Real) +
        ∑ s ∈ S, if (s : NNReal) < u then jump s else 0
    let A : Finset (Set.Ioc (0 : NNReal) t) → Real :=
      fun S => f (0, X 0 omega) +
        (∫ u in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (u, approx S (Real.toNNReal u)) (1, 0) ∂volume) +
        c * (∫ u in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (u, approx S (Real.toNNReal u)) (0, 1) ∂volume) +
        ∑ s ∈ S, (f (((s : NNReal) : Real), approx S s) -
          f (((s : NNReal) : Real), before S s))
    ∀ S : Finset (Set.Ioc (0 : NNReal) t),
      f ((t : Real), approx S t) = A S := by
  classical
  intro jump approx before A S
  let I := Set.Ioc (0 : NNReal) t
  let τ : I → ℝ := fun s => ((s : NNReal) : ℝ)
  have hτ : StrictMono τ := by
    intro i j hij
    exact hij
  let P : Finset I → ℝ → ℝ :=
    fun R u => X 0 omega + c * u + ∑ s ∈ R, if τ s ≤ u then jump s else 0
  let Q : Finset I → ℝ → ℝ :=
    fun R u => X 0 omega + c * u + ∑ s ∈ R, if τ s < u then jump s else 0
  have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
  have hp : ∀ s ∈ S, 0 < τ s := fun s _ => s.property.1
  have hb : ∀ s ∈ S, τ s ≤ (t : ℝ) := fun s _ => s.property.2
  have hP (u : ℝ) (hu : 0 ≤ u) : P S u = approx S (Real.toNNReal u) :=
    Kyprianou.Ch04.bvNNRealFiniteAffineRightCoercionV1
      (fun s : I => (s : NNReal)) jump (X 0 omega) c S u hu
  have hpost (u : NNReal) : P S (u : ℝ) = approx S u := by
    simpa only [Real.toNNReal_coe] using hP (u : ℝ) u.coe_nonneg
  have hpre (u : NNReal) : Q S (u : ℝ) = before S u :=
    Kyprianou.Ch04.bvNNRealFiniteAffineLeftCoercionV1
      (fun s : I => (s : NNReal)) jump (X 0 omega) c S u
  have hi (v : ℝ × ℝ) : IntervalIntegrable
      (fun u => fderiv ℝ f (u,P S u) v) volume 0 (t : ℝ) :=
    Kyprianou.Ch04.bvFiniteJumpDerivativeIntervalIntegrableV1
      τ hτ jump (X 0 omega) c f hf v S (t : ℝ) ht hp hb
  have hI (v : ℝ × ℝ) :
      (∫ u in 0..(t : ℝ), fderiv ℝ f (u,P S u) v) =
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          fderiv ℝ f (u,approx S (Real.toNNReal u)) v ∂volume := by
    rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    change fderiv ℝ f (u,P S u) v = fderiv ℝ f (u,approx S (Real.toNNReal u)) v
    rw [hP u hu.1]
  have hvec : ((1 : ℝ),c) = (1,0) + c • ((0 : ℝ),1) := by
    ext <;> simp
  have hsplit :
      (∫ u in 0..(t : ℝ), fderiv ℝ f (u,P S u) (1,c)) =
        (∫ u in 0..(t : ℝ), fderiv ℝ f (u,P S u) (1,0)) +
        c * (∫ u in 0..(t : ℝ), fderiv ℝ f (u,P S u) (0,1)) := by
    rw [hvec]
    simp only [map_add, map_smul, smul_eq_mul]
    rw [intervalIntegral.integral_add (hi (1,0)) ((hi (0,1)).const_mul c),
      intervalIntegral.integral_const_mul]
  have h := Kyprianou.Ch04.bvFiniteJumpTelescopingV1
    τ hτ jump (X 0 omega) c f hf S (t : ℝ) ht hp hb
  change f ((t : ℝ),P S t) = f (0,X 0 omega) +
    (∫ u in 0..(t : ℝ), fderiv ℝ f (u,P S u) (1,c)) +
    ∑ s ∈ S, (f (τ s,P S (τ s)) - f (τ s,Q S (τ s))) at h
  rw [hsplit, hI (1,0), hI (0,1), hpost t] at h
  simpa only [A, τ, hpost, hpre, ← add_assoc] using h

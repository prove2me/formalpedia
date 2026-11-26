-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_record_phase_level_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:46:16.258913+00:00
-- url     : https://prove2.me/submissions/80853da9-751e-47a7-ab1c-7605e6483c87

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_complex_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw48_level_grid_mesh
import Theorems.Thm_Kyprianou_Ch04_kw48_level_primitive_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The time grid mapped by the running record is a vanishing-mesh
level grid, whose phase quadrature converges to the primitive increment. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) (w : Ω)
    (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n)
    (right : Bool) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
      Complex.exp (Complex.I * (beta:Complex) *
        (runningSup L (if right then u n (i+1) else u n i) w:Complex)))
      atTop (nhds (S L beta b w-S L beta a w)) := by
  let U : Real → Real := fun r => runningSup L r.toNNReal w
  let f : Real → Complex := fun y => Complex.exp (Complex.I*(beta:Complex)*(y:Complex))
  have hU : Monotone U := fun x y hxy =>
    (runningSup_monotone_and_path_le L w).1 (Real.toNNReal_le_toNNReal hxy)
  have hUc : Continuous U := (runningSup_continuous_actual L w).comp
    continuous_real_toNNReal
  have hmono (n : Nat) : Monotone (fun i => (u n i:Real)) :=
    fun i j hij => by exact_mod_cast hu n hij
  obtain ⟨d,hd,hmesh⟩ := Kyprianou.Ch04.kw48_level_grid_mesh
    (a:Real) (b:Real) U hUc.continuousOn hU
    (fun n i => (u n i:Real)) N hmono
    (fun n => by rw [h0 n]) (fun n => by rw [hN n]) delta hDelta hMesh
  have hf : Continuous f := by unfold f; fun_prop
  have hB (y : Real) : ‖f y‖ ≤ 1 := by
    simp [f, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have h := Kyprianou.Ch04.kw48_complex_quadrature volume
    (U a) (U b) f 1 hf.measurable hB (fun n i => U (u n i)) N
    (fun n => hU.comp (hmono n))
    (fun n => by rw [h0 n]) (fun n => by rw [hN n]) d hd hmesh right
    (Eventually.of_forall (fun x => hf.continuousAt.continuousWithinAt))
  have habU := (runningSup_monotone_and_path_le L w).1 hab
  have hcell (n i : Nat) :
      (volume (Ioc (U (u n i)) (U (u n (i+1))))).toReal =
        runningSup L (u n (i+1)) w-runningSup L (u n i) w := by
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal]
    · simp [U]
    · exact sub_nonneg.mpr (hU (hmono n (Nat.le_succ i)))
  have htarget := Kyprianou.Ch04.kw48_level_primitive_increment L beta w a b hab
  simp only [U,Real.toNNReal_coe] at h
  -- Convert the volume cells and the primitive endpoint integral.
  have hcell' (n i : Nat) := hcell n i
  simp only [U,Real.toNNReal_coe] at hcell'
  simp only [hcell',f] at h
  rw [htarget] at h
  convert h using 1
  funext n
  apply Finset.sum_congr rfl
  intro i hi
  cases right <;> rfl

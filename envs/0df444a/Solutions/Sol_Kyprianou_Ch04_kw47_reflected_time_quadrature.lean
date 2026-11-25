-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_reflected_time_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:19:23.730397+00:00
-- url     : https://prove2.me/submissions/435bfa3e-4eb6-4ce5-9ec6-3cf080e5f397

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_real_path
import Theorems.Thm_Kyprianou_Ch04_kw47_right_grid_integral_convergence
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact right-endpoint time quadrature on any vanishing-mesh grid. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1) : Real) - (u n i : Real) ≤ delta n) :
    let Z : NNReal → Real := fun r =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((u n (i+1) : Real)-(u n i : Real)) * Z (u n (i+1)))
      atTop (nhds ((∫ x in Icc (0:Real) (b:Real), Z x.toNNReal ∂volume) -
        (∫ x in Icc (0:Real) (a:Real), Z x.toNNReal ∂volume))) := by
  dsimp only
  let Z : NNReal → Real := fun r =>
    Real.exp (-alpha * (runningSup L r w - L.X r w))
  let f : Real → Real := fun r => Z r.toNNReal
  obtain ⟨hf,hB,hRight⟩ :=
    Kyprianou.Ch04.kw47_reflected_exp_real_path L alpha hAlpha w
  have hmono (n : Nat) : Monotone (fun i => (u n i : Real)) :=
    fun i j hij => by exact_mod_cast hu n hij
  have h0r (n : Nat) : (u n 0 : Real) = (a : Real) := by rw [h0 n]
  have hNr (n : Nat) : (u n (N n) : Real) = (b : Real) := by rw [hN n]
  letI : IsFiniteMeasure (volume.restrict (Ioc (a:Real) (b:Real))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  have hconv := Kyprianou.Ch04.kw47_right_grid_integral_convergence
    volume (a:Real) (b:Real) f 1 hf hB hRight
    (fun n i => (u n i : Real)) N hmono h0r hNr delta hDelta hMesh
  have hmass (n i : Nat) :
      (volume (Ioc (u n i : Real) (u n (i+1) : Real))).toReal =
        (u n (i+1) : Real)-(u n i : Real) := by
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr (hmono n (Nat.le_succ i))
  have hIntA : IntegrableOn f (Icc (0:Real) (a:Real)) volume := by
    letI : IsFiniteMeasure (volume.restrict (Icc (0:Real) (a:Real))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
          exact ENNReal.ofReal_lt_top⟩
    exact (integrable_const (1:Real)).mono' hf.aestronglyMeasurable
      (Eventually.of_forall hB)
  have hIntAB : IntegrableOn f (Ioc (a:Real) (b:Real)) volume :=
    (integrable_const (1:Real)).mono' hf.aestronglyMeasurable
      (Eventually.of_forall hB)
  have habR : (a:Real) ≤ (b:Real) := by exact_mod_cast hab
  have hdis : Disjoint (Icc (0:Real) (a:Real)) (Ioc (a:Real) (b:Real)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  have hUnion : Icc (0:Real) (a:Real) ∪ Ioc (a:Real) (b:Real) =
      Icc (0:Real) (b:Real) := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans habR⟩
      · exact ⟨(NNReal.coe_nonneg a).trans hx.1.le, hx.2⟩
    · intro hx
      by_cases h : x ≤ (a:Real)
      · exact Or.inl ⟨hx.1,h⟩
      · exact Or.inr ⟨lt_of_not_ge h,hx.2⟩
  have hSplit := setIntegral_union hdis measurableSet_Ioc hIntA hIntAB
  rw [hUnion] at hSplit
  have hTarget : (∫ x in Ioc (a:Real) (b:Real), f x ∂volume) =
      (∫ x in Icc (0:Real) (b:Real), f x ∂volume) -
      (∫ x in Icc (0:Real) (a:Real), f x ∂volume) := by linarith
  simpa only [hmass, f, Z, Real.toNNReal_coe, hTarget] using hconv

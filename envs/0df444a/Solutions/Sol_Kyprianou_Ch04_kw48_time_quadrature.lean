-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_time_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:47:32.540004+00:00
-- url     : https://prove2.me/submissions/c067bdbf-37cb-4b7c-91c1-9ee9b5d12c77

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_complex_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_right_path
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Right-point time sums converge to the actual complex time integral increment. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((u n (i+1):Real)-(u n i:Real)) • Z L alpha beta (u n (i+1)) w)
      atTop (nhds (J L alpha beta b w-J L alpha beta a w)) := by
  let f : Real → Complex := fun r => Z L alpha beta r.toNNReal w
  obtain ⟨hf,hRight⟩ := Kyprianou.Ch04.kw48_Z_right_path L alpha beta w
  have hB (r : Real) : ‖f r‖ ≤ 1 :=
    le_of_eq (Kyprianou.Ch04.kw48_norm_Z L alpha beta r.toNNReal w)
  have hmono (n : Nat) : Monotone (fun i => (u n i:Real)) :=
    fun i j hij => by exact_mod_cast hu n hij
  letI : IsFiniteMeasure (volume.restrict (Ioc (a:Real) (b:Real))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  have hconv := Kyprianou.Ch04.kw48_complex_quadrature
    volume (a:Real) (b:Real) f 1 hf hB
    (fun n i => (u n i:Real)) N hmono (fun n => by rw [h0 n])
    (fun n => by rw [hN n]) delta hDelta hMesh true
    (Eventually.of_forall fun r => hRight r)
  have hmass (n i : Nat) :
      (volume (Ioc (u n i:Real) (u n (i+1):Real))).toReal =
        (u n (i+1):Real)-(u n i:Real) := by
    rw [Real.volume_Ioc,ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr (hmono n (Nat.le_succ i))
  have hIntA : IntegrableOn f (Icc (0:Real) (a:Real)) volume := by
    letI : IsFiniteMeasure (volume.restrict (Icc (0:Real) (a:Real))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Icc]
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
      · exact ⟨hx.1,hx.2.trans habR⟩
      · exact ⟨(NNReal.coe_nonneg a).trans hx.1.le,hx.2⟩
    · intro hx
      by_cases h : x ≤ (a:Real)
      · exact Or.inl ⟨hx.1,h⟩
      · exact Or.inr ⟨lt_of_not_ge h,hx.2⟩
  have hSplit := setIntegral_union hdis measurableSet_Ioc hIntA hIntAB
  rw [hUnion] at hSplit
  have hTarget : (∫ x in Ioc (a:Real) (b:Real), f x ∂volume) =
      J L alpha beta b w-J L alpha beta a w := by
    unfold J
    change (∫ x in Ioc (a:Real) (b:Real), f x ∂volume) =
      (∫ x in Icc (0:Real) (b:Real), f x ∂volume) -
        (∫ x in Icc (0:Real) (a:Real), f x ∂volume)
    linear_combination -hSplit
  simpa only [hmass,f,Real.toNNReal_coe,if_true,hTarget] using hconv

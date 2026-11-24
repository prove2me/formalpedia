-- Prove2me | solution 2 for Kyprianou.Ch02.bvLevyJordanJumpsEqSignedProcessJumpsV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T23:03:32.3148+00:00
-- url     : https://prove2.me/submissions/716df190-4f65-4c7d-862a-40b879c3a9f0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

private lemma max_eq_half_add_abs (a : ℝ) : max a 0 = (a + |a|) / 2 := by
  have h := congrArg (fun x : ℝ => x / 2) (add_abs_eq_two_nsmul_posPart a)
  simp only [two_nsmul, ← two_mul] at h
  have h2 : (2 * (a⁺ : ℝ)) / 2 = a⁺ := by ring
  rw [h2] at h
  simpa [posPart] using h.symm

private lemma max_max_zero (a : ℝ) : max (max a 0) 0 = max a 0 :=
  max_eq_left (le_max_right a 0)

/-- Pathwise: jumps of Jordan components equal signed jumps of a BV càdlàg path. -/
private theorem bvCadlagJordanJumpIdentity
    (f : ℝ≥0 → ℝ)
    (hBV : LocallyBoundedVariationOn f Set.univ)
    (hCad : ProbabilityTheory.IsCadlag f)
    (s : ℝ≥0) (hs : 0 < s) :
    let V : ℝ≥0 → ℝ := fun t => variationOnFromTo f Set.univ 0 t
    let Spos : ℝ≥0 → ℝ := fun t => (V t + f t) / 2
    let Sneg : ℝ≥0 → ℝ := fun t => (V t - f t) / 2
    max (Spos s - limUnder (nhdsWithin s (Set.Iio s)) Spos) 0 =
      max (f s - limUnder (nhdsWithin s (Set.Iio s)) f) 0 ∧
    max (Sneg s - limUnder (nhdsWithin s (Set.Iio s)) Sneg) 0 =
      max (limUnder (nhdsWithin s (Set.Iio s)) f - f s) 0 := by
  have : (nhdsWithin s (Set.Iio s)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs⟩
  let V : ℝ≥0 → ℝ := fun t => variationOnFromTo f Set.univ 0 t
  let Spos : ℝ≥0 → ℝ := fun t => (V t + f t) / 2
  let Sneg : ℝ≥0 → ℝ := fun t => (V t - f t) / 2
  obtain ⟨_hr, l, hl⟩ := hCad s
  have hlim_f : limUnder (nhdsWithin s (Set.Iio s)) f = l := hl.limUnder_eq
  have hVtend :
      Tendsto V (nhdsWithin s (Set.Iio s))
        (nhds (V s - dist (f s) l)) := by
    have h := variationOnFromTo.tendsto_left (f := f) (l := l) (a := (0 : ℝ≥0)) (b := s)
      (mem_univ _) (mem_univ _) hBV
    simpa [V, nhdsWithin, Set.univ_inter] using
      h (by simpa [nhdsWithin, Set.univ_inter] using hl)
  have hSpos_eq : Spos = fun x => (V x + f x) / 2 := rfl
  have hSneg_eq : Sneg = fun x => (V x - f x) / 2 := rfl
  have hlim_Spos :
      limUnder (nhdsWithin s (Set.Iio s)) Spos =
        (V s - dist (f s) l + l) / 2 := by
    rw [hSpos_eq]
    exact ((hVtend.add hl).div_const (2 : ℝ)).limUnder_eq
  have hlim_Sneg :
      limUnder (nhdsWithin s (Set.Iio s)) Sneg =
        (V s - dist (f s) l - l) / 2 := by
    rw [hSneg_eq]
    exact ((hVtend.sub hl).div_const (2 : ℝ)).limUnder_eq
  have hdist : dist (f s) l = |f s - l| := Real.dist_eq (f s) l
  constructor
  · have hjump :
        Spos s - limUnder (nhdsWithin s (Set.Iio s)) Spos =
          max (f s - l) 0 := by
      rw [hlim_Spos, hdist, max_eq_half_add_abs]
      change (V s + f s) / 2 - (V s - |f s - l| + l) / 2 = (f s - l + |f s - l|) / 2
      ring
    rw [hjump, hlim_f, max_max_zero]
  · have hjump :
        Sneg s - limUnder (nhdsWithin s (Set.Iio s)) Sneg =
          max (l - f s) 0 := by
      rw [hlim_Sneg, hdist]
      change (V s - f s) / 2 - (V s - |f s - l| - l) / 2 = max (l - f s) 0
      calc
        (V s - f s) / 2 - (V s - |f s - l| - l) / 2
            = ((l - f s) + |f s - l|) / 2 := by ring
        _ = ((l - f s) + |l - f s|) / 2 := by rw [abs_sub_comm]
        _ = max (l - f s) 0 := (max_eq_half_add_abs _).symm
    rw [hjump, hlim_f, max_max_zero]

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
          X s.1 ω) 0
    let JSpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Spos s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Spos u ω)) 0
    let JSneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Sneg s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Sneg u ω)) 0
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, JSpos t ω = Jpos t ω) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, JSneg t ω = Jneg t ω) := by
  dsimp only
  let V : ℝ≥0 → Ω → ℝ := fun t ω =>
    variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
  let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
  let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
  let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (X s.1 ω -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
  let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
        X s.1 ω) 0
  let JSpos : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (Spos s.1 ω -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Spos u ω)) 0
  let JSneg : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (Sneg s.1 ω -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Sneg u ω)) 0
  -- Pathwise identity on the AE set where X is BV and càdlàg
  have hboth : ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, JSpos t ω = Jpos t ω) ∧
      (∀ t : ℝ≥0, JSneg t ω = Jneg t ω) := by
    filter_upwards [hBV, hX.cadlag_ae] with ω hBVω hCadω
    constructor
    · intro t
      refine tsum_congr fun s => ?_
      have hs : 0 < s.1 := s.2.1
      have hid := bvCadlagJordanJumpIdentity (fun u => X u ω) hBVω hCadω s.1 hs
      simpa [Spos, Sneg, V] using hid.1
    · intro t
      refine tsum_congr fun s => ?_
      have hs : 0 < s.1 := s.2.1
      have hid := bvCadlagJordanJumpIdentity (fun u => X u ω) hBVω hCadω s.1 hs
      simpa [Spos, Sneg, V] using hid.2
  exact ⟨hboth.mono fun _ h => h.1, hboth.mono fun _ h => h.2⟩

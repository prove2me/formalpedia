-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_restart_payoff_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:33:03.822086+00:00
-- url     : https://prove2.me/submissions/93eb4371-ddf0-4148-b7a2-b7006105e4b0

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_geometry
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_lower_clock_shift
open Set Filter Topology MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem discountedAt_add_finite
    (q : ℝ) (t : ℝ≥0) (r : WithTop ℝ≥0) :
    discountedAt q ((t : WithTop ℝ≥0) + r) =
      discountedAt q (t : WithTop ℝ≥0) * discountedAt q r := by
  induction r using WithTop.recTopCoe with
  | top =>
    rw [show (t : WithTop ℝ≥0) + (⊤ : WithTop ℝ≥0) = ⊤ from WithTop.add_top _]
    change (0 : ℝ) = discountedAt q (t : WithTop ℝ≥0) * 0
    rw [mul_zero]
  | coe s =>
    rw [← WithTop.coe_add]
    change Real.exp (-q * ((t + s : ℝ≥0) : ℝ)) =
      Real.exp (-q * (t : ℝ)) * Real.exp (-q * (s : ℝ))
    rw [NNReal.coe_add, mul_add, Real.exp_add]

private theorem cadlag_shifted_no_positive_jump
    (g : ℝ≥0 → ℝ) (x : ℝ) (hcad : IsCadlag g)
    (hjump : ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto g (nhdsWithin t (Iio t)) (nhds l) → g t ≤ l) :
    let f : ℝ≥0 → ℝ := fun s => x + g s
    IsCadlag f ∧
      (∀ (t : ℝ≥0) (l : ℝ), 0 < t →
        Tendsto f (nhdsWithin t (Iio t)) (nhds l) → f t ≤ l) := by
  intro f
  refine ⟨?_, ?_⟩
  · intro t
    obtain ⟨l, hl⟩ := (hcad t).2
    exact ⟨continuous_const.continuousWithinAt.add (hcad t).1, x + l, hl.const_add x⟩
  · intro t l ht hl
    have hrel : (fun s => f s - x) = g := by
      funext s
      dsimp [f]
      ring
    have hlim := hl.sub_const x
    rw [hrel] at hlim
    dsimp [f]
    linarith [hjump t (l - x) ht hlim]

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (hneg : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => D.X s ω) (nhdsWithin t (Iio t)) (nhds l) → D.X t ω ≤ l)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    let L := tauMinus (shifted D.X x) 0
    let U := tauPlus (shifted D.X x) a
    let low := fun ω => if L ω < U ω then discountedAt q (L ω) else 0
    let restart := fun ω =>
      if U ω < L ω then
        WithTop.recTopCoe 0 (fun t =>
          discountedAt q (t : WithTop ℝ≥0) *
            discountedAt q (tauMinus
              (fun s (_ : Unit) => a + (D.X (t + s) ω - D.X t ω)) 0 ())) (U ω)
      else 0
    ∀ᵐ ω ∂P, discountedAt q (L ω) = low ω + restart ω := by
  intro L U low restart
  filter_upwards [D.levy.cadlag_ae, hneg] with ω hcad hjumps
  let f : ℝ≥0 → ℝ := fun s => x + D.X s ω
  have hL : tauMinus (fun s (_ : Unit) => f s) 0 () = L ω := rfl
  have hstart : f 0 ≤ a := by
    dsimp [f]
    rw [congrFun D.levy.start_zero ω, add_zero]
    exact hxa
  obtain ⟨hcadf, hjumpsf⟩ := cadlag_shifted_no_positive_jump (fun t => D.X t ω) x hcad hjumps
  have hgeom := source_result81_strict_exit_geometry f a ha hstart hcadf hjumpsf
  rcases lt_trichotomy (L ω) (U ω) with hlo | heq | hup
  · simp only [low, restart, if_pos hlo, if_neg hlo.not_gt, add_zero]
  · have htop : L ω = ⊤ := hgeom.2 heq
    simp only [low, restart, ← heq, htop, lt_irrefl, if_false, discountedAt, add_zero]
  · obtain ⟨t, htU⟩ := WithTop.ne_top_iff_exists.mp
      (ne_of_lt (hup.trans_le le_top))
    have hlevel : x + D.X t ω = a := hgeom.1 t htU.symm
    have hbefore : (t : WithTop ℝ≥0) < tauMinus (fun s (_ : Unit) => f s) 0 () := by
      rw [htU, hL]
      exact hup
    have hshift := source_result81_strict_lower_clock_shift f t hbefore
    have hf :
        (fun s (_ : Unit) => f (t + s)) =
          (fun s (_ : Unit) => a + (D.X (t + s) ω - D.X t ω)) := by
      funext s u
      dsimp [f]
      linarith
    rw [hL, hf] at hshift
    simp only [low, restart, if_neg hup.not_gt, if_pos hup, zero_add]
    rw [← htU, hshift, discountedAt_add_finite] <;> rfl

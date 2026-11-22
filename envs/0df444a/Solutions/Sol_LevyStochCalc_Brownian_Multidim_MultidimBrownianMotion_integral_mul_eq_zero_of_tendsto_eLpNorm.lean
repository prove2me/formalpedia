-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_eq_zero_of_tendsto_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T14:25:00.607978+00:00
-- url     : https://prove2.me/submissions/384b9c5b-f85a-414a-9aca-f1f101fcc37b

import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

private theorem product_limit {α ι : Type*} [MeasurableSpace α]
    {m : Measure α} {l : Filter ι} {X Y : ι → α → ℝ} {X' Y' : α → ℝ}
    (hX : ∀ i, MemLp (X i) 2 m) (hY : ∀ i, MemLp (Y i) 2 m)
    (hX' : MemLp X' 2 m) (hY' : MemLp Y' 2 m)
    (hXc : Tendsto (fun i => eLpNorm (fun x => X i x - X' x) 2 m) l (𝓝 0))
    (hYc : Tendsto (fun i => eLpNorm (fun x => Y i x - Y' x) 2 m) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, X i x * Y i x ∂m) l (𝓝 (∫ x, X' x * Y' x ∂m)) := by
  let A := fun i => eLpNorm (X i - X') 2 m
  let B := fun i => eLpNorm (Y i - Y') 2 m
  let C := eLpNorm X' 2 m
  let D := eLpNorm Y' 2 m
  have ha : Tendsto A l (𝓝 0) := hXc
  have hb : Tendsto B l (𝓝 0) := hYc
  have hbound : Tendsto (fun i => A i * (B i + D) + C * B i) l (𝓝 0) := by
    have hbd : Tendsto (fun i => B i + D) l (𝓝 D) := by simpa using hb.add tendsto_const_nhds
    have h1 := ENNReal.Tendsto.mul ha (Or.inr hY'.eLpNorm_ne_top) hbd (Or.inr ENNReal.zero_ne_top)
    have h2 := ENNReal.Tendsto.mul (tendsto_const_nhds : Tendsto (fun _ : ι => C) l (𝓝 C))
      (Or.inr ENNReal.zero_ne_top) hb (Or.inr hX'.eLpNorm_ne_top)
    simpa using h1.add h2
  have hL1 : Tendsto (fun i => eLpNorm (X i * Y i - X' * Y') 1 m) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun _ => bot_le)
    intro i
    have hYbound : eLpNorm (Y i) 2 m ≤ B i + D := by
      simpa only [sub_add_cancel, B, D] using
        (eLpNorm_add_le ((hY i).sub hY').aestronglyMeasurable hY'.aestronglyMeasurable (p := 2) (by norm_num))
    have heq : X i * Y i - X' * Y' = (X i - X') • Y i + X' • (Y i - Y') := by
      funext x
      change X i x * Y i x - X' x * Y' x = (X i x - X' x) * Y i x + X' x * (Y i x - Y' x)
      ring
    change eLpNorm (X i * Y i - X' * Y') 1 m ≤ A i * (B i + D) + C * B i
    rw [heq]
    have hleft : AEStronglyMeasurable ((X i - X') • Y i) m :=
      ((hX i).sub hX').aestronglyMeasurable.smul (hY i).aestronglyMeasurable
    have hright : AEStronglyMeasurable (X' • (Y i - Y')) m :=
      hX'.aestronglyMeasurable.smul ((hY i).sub hY').aestronglyMeasurable
    calc
      _ ≤ eLpNorm ((X i - X') • Y i) 1 m + eLpNorm (X' • (Y i - Y')) 1 m :=
        eLpNorm_add_le hleft hright (p := 1) (by norm_num)
      _ ≤ A i * eLpNorm (Y i) 2 m + C * B i :=
        add_le_add (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) (hY i).aestronglyMeasurable ((hX i).sub hX').aestronglyMeasurable)
          (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) ((hY i).sub hY').aestronglyMeasurable hX'.aestronglyMeasurable)
      _ ≤ _ := by
        gcongr
  have h := tendsto_integral_of_L1' (X' * Y') (hX'.integrable_mul hY').aestronglyMeasurable
    (Eventually.of_forall (fun i => (hX i).integrable_mul (hY i))) hL1
  exact h



variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem solution {u v : Ω → ℝ} {un vn : ℕ → Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hun : ∀ n, MemLp (un n) 2 P) (hvn : ∀ n, MemLp (vn n) 2 P)
    (h0 : ∀ n, ∫ ω, un n ω * vn n ω ∂P = 0)
    (hcu : Filter.Tendsto (fun n => eLpNorm (fun ω => un n ω - u ω) 2 P) Filter.atTop (nhds 0))
    (hcv : Filter.Tendsto (fun n => eLpNorm (fun ω => vn n ω - v ω) 2 P) Filter.atTop (nhds 0)) :
    ∫ ω, u ω * v ω ∂P = 0 := by
  have h := product_limit hun hvn hu hv hcu hcv
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (∫ ω, u ω * v ω ∂P)) := by
    simpa only [h0] using h
  exact tendsto_nhds_unique hzero tendsto_const_nhds

#print axioms solution

-- Prove2me | solution 1 for MathematicsOfWater.poiseuille_law
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-09-24T19:13:15.852395+00:00
-- url     : https://prove2.me/submissions/47bce662-caa8-4525-a430-96e1065150ca

import Definitions.Def_MathematicsOfWater_PipeFlow
open Real
namespace MathematicsOfWater

theorem poiseuille_law (η L Δp d : ℝ) (v : ℝ → ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d)
    (hv : IsPipeFlow η L Δp d v) :
    flowRate d v = π * Δp * d ^ 4 / (128 * η * L) := by
  obtain ⟨hode, ⟨M, hbound⟩, hcont, hlast⟩ := hv
  have hRpos : (0:ℝ) < d / 2 := by positivity
  set R : ℝ := d / 2 with hR_def
  set s : Set ℝ := Set.Ioo (0:ℝ) R with hs_def
  have hsOpen : IsOpen s := isOpen_Ioo
  have hsConv : Convex ℝ s := convex_Ioo 0 R
  have hsPre : IsPreconnected s := hsConv.isPreconnected
  -- w r = r * v'(r)
  set w : ℝ → ℝ := fun r => r * deriv v r with hw_def
  -- Step A: deriv w r = -(Δp/(ηL)) * r on s
  have hwdiffAt : ∀ r ∈ s, DifferentiableAt ℝ w r := by
    intro r hr; exact (hode r hr).2.1
  have hwdiff : DifferentiableOn ℝ w s := fun r hr => (hwdiffAt r hr).differentiableWithinAt
  have hwderiv : ∀ r ∈ s, deriv w r = -(Δp / (η * L)) * r := by
    intro r hr
    obtain ⟨hv1, hv2, hv3⟩ := hode r hr
    have hrpos : 0 < r := hr.1
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hv3' : r * ((1 / r) * deriv w r) = r * (-(Δp / (η * L))) := by rw [hv3]
    rw [← mul_assoc, mul_one_div, div_self hrne, one_mul] at hv3'
    rw [hv3']; ring
  set k1 : ℝ := -(Δp / (2 * η * L)) with hk1_def
  set g1 : ℝ → ℝ := fun r => k1 * r ^ 2 with hg1_def
  have hg1diff : DifferentiableOn ℝ g1 s := by
    intro r _
    exact ((differentiable_pow 2).const_mul k1).differentiableAt.differentiableWithinAt
  have hg1deriv : ∀ r : ℝ, deriv g1 r = -(Δp / (η * L)) * r := by
    intro r
    have hd1 : HasDerivAt g1 (k1 * ((2:ℝ) * r ^ (2 - 1))) r := (hasDerivAt_pow 2 r).const_mul k1
    rw [hd1.deriv, hk1_def]; ring
  have heqderiv1 : s.EqOn (deriv w) (deriv g1) := by
    intro r hr; rw [hwderiv r hr, hg1deriv r]
  obtain ⟨a, ha⟩ := hsOpen.exists_eq_add_of_deriv_eq hsPre hwdiff hg1diff heqderiv1
  -- ha : s.EqOn w (fun r => g1 r + a), i.e. r * v'(r) = k1*r^2 + a for r ∈ s
  set c2 : ℝ := -(Δp / (4 * η * L)) with hc2_def
  have hk1c2 : k1 = 2 * c2 := by rw [hk1_def, hc2_def]; ring
  set h2 : ℝ → ℝ := fun r => c2 * r ^ 2 + a * Real.log r with hh2_def
  have hvdiff : DifferentiableOn ℝ v s := fun r hr => ((hode r hr).1).differentiableWithinAt
  have hh2diff : DifferentiableOn ℝ h2 s := by
    intro r hr
    have hrpos : 0 < r := hr.1
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hp : DifferentiableAt ℝ (fun r : ℝ => c2 * r ^ 2) r :=
      ((differentiable_pow 2).const_mul c2).differentiableAt
    have hl : DifferentiableAt ℝ (fun r : ℝ => a * Real.log r) r :=
      (differentiableAt_log hrne).const_mul a
    exact (hp.add hl).differentiableWithinAt
  have hh2deriv : ∀ r ∈ s, deriv h2 r = k1 * r + a / r := by
    intro r hr
    have hrpos : 0 < r := hr.1
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hp : HasDerivAt (fun r : ℝ => c2 * r ^ 2) (c2 * ((2:ℝ) * r ^ (2 - 1))) r :=
      (hasDerivAt_pow 2 r).const_mul c2
    have hl : HasDerivAt (fun r : ℝ => a * Real.log r) (a * r⁻¹) r :=
      (hasDerivAt_log hrne).const_mul a
    have hsum : HasDerivAt h2 (c2 * ((2:ℝ) * r ^ (2 - 1)) + a * r⁻¹) r := hp.add hl
    rw [hsum.deriv, hk1c2]
    field_simp
    try ring
  have hvderiv : ∀ r ∈ s, deriv v r = deriv h2 r := by
    intro r hr
    have hrpos : 0 < r := hr.1
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hwr : w r = g1 r + a := ha hr
    have heq1 : r * deriv v r = k1 * r ^ 2 + a := by
      rw [hw_def] at hwr; rw [hg1_def] at hwr; exact hwr
    have hdv : deriv v r = (k1 * r ^ 2 + a) / r := by
      rw [eq_div_iff hrne]; linarith [heq1]
    rw [hdv, hh2deriv r hr]
    field_simp
    try ring
  have heqderiv2 : s.EqOn (deriv v) (deriv h2) := hvderiv
  obtain ⟨b, hb⟩ := hsOpen.exists_eq_add_of_deriv_eq hsPre hvdiff hh2diff heqderiv2
  -- hb : s.EqOn v (fun r => h2 r + b), i.e. v r = c2*r^2 + a*log r + b for r ∈ s
  have hIooMem : s ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
    have h1 : Set.Iio R ∈ nhds (0:ℝ) := IsOpen.mem_nhds isOpen_Iio hRpos
    have h2 : Set.Iio R ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := mem_nhdsWithin_of_mem_nhds h1
    have h3 : Set.Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
    have h4 := Filter.inter_mem h2 h3
    have heq : Set.Iio R ∩ Set.Ioi (0:ℝ) = s := by
      rw [hs_def]; ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
      exact and_comm
    rwa [heq] at h4
  have hveq : ∀ᶠ r in nhdsWithin (0:ℝ) (Set.Ioi 0), v r = c2 * r ^ 2 + a * Real.log r + b :=
    Filter.eventually_of_mem hIooMem (fun r hr => by
      have hthis := hb hr; simpa [hh2_def] using hthis)
  haveI : Filter.NeBot (nhdsWithin (0:ℝ) (Set.Ioi 0)) := nhdsWithin_Ioi_neBot (le_refl (0:ℝ))
  have hMev : ∀ᶠ r in nhdsWithin (0:ℝ) (Set.Ioi 0), |v r| ≤ M :=
    Filter.eventually_of_mem hIooMem (fun r hr => hbound r hr)
  -- Step C: a = 0, using boundedness
  have ha0 : a = 0 := by
    by_contra hane
    have hpoly : Filter.Tendsto (fun r : ℝ => c2 * r ^ 2 + b) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds b) := by
      have hcont0 : Filter.Tendsto (fun r : ℝ => c2 * r ^ 2 + b) (nhds (0:ℝ))
          (nhds (c2 * (0:ℝ) ^ 2 + b)) :=
        (((continuous_pow 2).const_mul c2).add continuous_const).tendsto 0
      simpa using hcont0.mono_left nhdsWithin_le_nhds
    have hlog : Filter.Tendsto Real.log (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atBot :=
      Real.tendsto_log_nhdsGT_zero
    rcases lt_or_gt_of_ne hane with hneg | hpos
    · -- a < 0 : a * log r → atTop, so v r → atTop
      have halog : Filter.Tendsto (fun r => a * Real.log r) (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atTop :=
        hlog.const_mul_atBot_of_neg hneg
      have htot : Filter.Tendsto (fun r => a * Real.log r + (c2 * r ^ 2 + b))
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atTop :=
        halog.atTop_add hpoly
      have hveqtot : v =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] (fun r => a * Real.log r + (c2 * r ^ 2 + b)) := by
        filter_upwards [hveq] with r hr; rw [hr]; ring
      have hvtend : Filter.Tendsto v (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atTop :=
        htot.congr' hveqtot.symm
      have hev : ∀ᶠ r in nhdsWithin (0:ℝ) (Set.Ioi 0), M + 1 ≤ v r :=
        Filter.tendsto_atTop.mp hvtend (M + 1)
      have hcontra : ∀ᶠ r in nhdsWithin (0:ℝ) (Set.Ioi 0), False := by
        filter_upwards [hev, hMev] with r hr1 hr2
        linarith [(abs_le.mp hr2).2]
      obtain ⟨r0, hfalse⟩ := hcontra.exists
      exact hfalse
    · -- a > 0 : a * log r → atBot, so v r → atBot
      have halog : Filter.Tendsto (fun r => a * Real.log r) (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atBot :=
        hlog.const_mul_atBot hpos
      have htot : Filter.Tendsto (fun r => a * Real.log r + (c2 * r ^ 2 + b))
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atBot :=
        halog.atBot_add hpoly
      have hveqtot : v =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] (fun r => a * Real.log r + (c2 * r ^ 2 + b)) := by
        filter_upwards [hveq] with r hr; rw [hr]; ring
      have hvtend : Filter.Tendsto v (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atBot :=
        htot.congr' hveqtot.symm
      have hev : ∀ᶠ r in nhdsWithin (0:ℝ) (Set.Ioi 0), v r ≤ -(M + 1) :=
        Filter.tendsto_atBot.mp hvtend (-(M + 1))
      have hcontra : ∀ᶠ r in nhdsWithin (0:ℝ) (Set.Ioi 0), False := by
        filter_upwards [hev, hMev] with r hr1 hr2
        linarith [(abs_le.mp hr2).1]
      obtain ⟨r0, hfalse⟩ := hcontra.exists
      exact hfalse
  -- v r = c2*r^2 + b for r ∈ s
  have hvform : ∀ r ∈ s, v r = c2 * r ^ 2 + b := by
    intro r hr
    have hthis := hb hr
    simp only [hh2_def, ha0, zero_mul, add_zero] at hthis
    exact hthis
  -- Step D: determine b from continuity at R and v R = 0
  haveI : Filter.NeBot (nhdsWithin R (Set.Iio R)) := nhdsWithin_Iio_neBot (le_refl R)
  have hIooMemR : s ∈ nhdsWithin R (Set.Iio R) := by
    have h1 : Set.Ioi (0:ℝ) ∈ nhds R := IsOpen.mem_nhds isOpen_Ioi hRpos
    have h2 : Set.Ioi (0:ℝ) ∈ nhdsWithin R (Set.Iio R) := mem_nhdsWithin_of_mem_nhds h1
    have h3 : Set.Iio R ∈ nhdsWithin R (Set.Iio R) := self_mem_nhdsWithin
    have h4 := Filter.inter_mem h3 h2
    have heq : Set.Iio R ∩ Set.Ioi (0:ℝ) = s := by
      rw [hs_def]; ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
      exact and_comm
    rwa [heq] at h4
  have hveq2 : v =ᶠ[nhdsWithin R (Set.Iio R)] (fun r => c2 * r ^ 2 + b) :=
    Filter.eventually_of_mem hIooMemR hvform
  have hpoly2 : Filter.Tendsto (fun r : ℝ => c2 * r ^ 2 + b) (nhdsWithin R (Set.Iio R))
      (nhds (c2 * R ^ 2 + b)) :=
    (((continuous_pow 2).const_mul c2).add continuous_const).tendsto R |>.mono_left nhdsWithin_le_nhds
  have hvtend2 : Filter.Tendsto v (nhdsWithin R (Set.Iio R)) (nhds (c2 * R ^ 2 + b)) :=
    hpoly2.congr' hveq2.symm
  have hcont2 : Filter.Tendsto v (nhdsWithin R (Set.Iio R)) (nhds (v R)) := hcont
  rw [hlast] at hcont2
  have hbeq : c2 * R ^ 2 + b = 0 := tendsto_nhds_unique hvtend2 hcont2
  -- v r = c2*r^2 + b for r ∈ Ioc 0 R
  have hvformIoc : ∀ r ∈ Set.Ioc (0:ℝ) R, v r = c2 * r ^ 2 + b := by
    intro r hr
    rcases eq_or_lt_of_le hr.2 with heq | hlt
    · rw [heq, hlast]; linarith [hbeq]
    · exact hvform r ⟨hr.1, hlt⟩
  -- Step E: compute the integral
  have hcongr : ∀ᵐ r ∂ (MeasureTheory.volume), r ∈ Set.uIoc (0:ℝ) R →
      v r * (2 * π * r) = (c2 * r ^ 2 + b) * (2 * π * r) := by
    apply MeasureTheory.ae_of_all
    intro r hr
    rw [Set.uIoc_of_le hRpos.le] at hr
    rw [hvformIoc r hr]
  have hflow : flowRate d v = ∫ r in (0:ℝ)..R, (c2 * r ^ 2 + b) * (2 * π * r) := by
    show (∫ r in (0:ℝ)..(d/2), v r * (2 * π * r)) = _
    rw [← hR_def]
    exact intervalIntegral.integral_congr_ae hcongr
  rw [hflow]
  have step1 : (∫ r in (0:ℝ)..R, (c2 * r ^ 2 + b) * (2 * π * r))
      = ∫ r in (0:ℝ)..R, (2 * π * c2 * r ^ 3 + 2 * π * b * r) := by
    apply intervalIntegral.integral_congr
    intro r _; ring
  have hcont3 : Continuous (fun r : ℝ => 2 * π * c2 * r ^ 3) :=
    continuous_const.mul (continuous_pow 3)
  have hcont1 : Continuous (fun r : ℝ => 2 * π * b * r) :=
    continuous_const.mul continuous_id
  have hIsum : (∫ r in (0:ℝ)..R, (2 * π * c2 * r ^ 3 + 2 * π * b * r))
      = (∫ r in (0:ℝ)..R, 2 * π * c2 * r ^ 3) + (∫ r in (0:ℝ)..R, 2 * π * b * r) :=
    intervalIntegral.integral_add (hcont3.intervalIntegrable 0 R) (hcont1.intervalIntegrable 0 R)
  have hI3 : (∫ r in (0:ℝ)..R, 2 * π * c2 * r ^ 3) = 2 * π * c2 * (R ^ 4 / 4) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num
  have hI1 : (∫ r in (0:ℝ)..R, 2 * π * b * r) = 2 * π * b * (R ^ 2 / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]; norm_num
  rw [step1, hIsum, hI3, hI1]
  have hb_val : b = -(c2 * R ^ 2) := by linarith [hbeq]
  rw [hb_val, hc2_def, hR_def]
  field_simp
  ring

end MathematicsOfWater


-- Platform entry point: restates the target verbatim.
namespace MathematicsOfWater
theorem _root_.solution (η L Δp d : ℝ) (v : ℝ → ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d)
    (hv : IsPipeFlow η L Δp d v) :
    flowRate d v = π * Δp * d ^ 4 / (128 * η * L) := by
  apply @MathematicsOfWater.poiseuille_law <;> assumption
end MathematicsOfWater

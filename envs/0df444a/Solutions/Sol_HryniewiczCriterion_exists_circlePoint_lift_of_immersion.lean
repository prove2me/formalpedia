-- Prove2me | solution 1 for HryniewiczCriterion.exists_circlePoint_lift_of_immersion
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T22:28:54.781985+00:00
-- url     : https://prove2.me/submissions/d8a8cda1-19c7-41fe-95f3-1fe37bde42fe

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

open HryniewiczCriterion
open Complex MeasureTheory Set

/-!
# Winding numbers of `C¹` loops in `ℂ \ {0}` via the logarithmic derivative
-/


noncomputable section

namespace WindA

/-- The log-derivative primitive recovers the loop: `c t = c 0 · exp (∫₀ᵗ c'/c)`. -/
lemma eq_mul_exp_integral {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (t : ℝ) :
    c t = c 0 * exp (∫ s in (0 : ℝ)..t, c' s / c s) := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hq : Continuous fun s => c' s / c s := hc'.div hcc hne
  set L : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, c' s / c s
  have hL : ∀ t, HasDerivAt L (c' t / c t) t := fun t =>
    (hq.integral_hasStrictDerivAt 0 t).hasDerivAt
  set g : ℝ → ℂ := fun t => c t * exp (-L t)
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h1 : HasDerivAt g (c' t * exp (-L t) + c t * (exp (-L t) * -(c' t / c t))) t :=
      (hc t).mul (HasDerivAt.cexp (f := fun t => -L t) (hL t).neg)
    convert h1 using 1
    field_simp [hne t]
    ring
  have hconst : ∀ t, g t = g 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
  have hL0 : L 0 = 0 := by simp [L]
  have := hconst t
  simp only [g, hL0, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- The log-derivative integral of a closed `C¹` loop lies in `2πi ℤ`. -/
lemma integral_mem_two_pi_I {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0) :
    ∃ k : ℤ, ∫ s in (0 : ℝ)..1, c' s / c s = k * (2 * Real.pi * I) := by
  have h := eq_mul_exp_integral hc hc' hne 1
  rw [hper] at h
  have h1 : exp (∫ s in (0 : ℝ)..1, c' s / c s) = 1 := by
    have h0 := hne 0
    exact mul_left_cancel₀ h0 (h.symm.trans (mul_one _).symm)
  exact Complex.exp_eq_one_iff.1 h1

lemma im_integral {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) :
    (∫ s in a..b, f s).im = ∫ s in a..b, (f s).im :=
  (Complex.imCLM.intervalIntegral_comp_comm (hf.intervalIntegrable a b)).symm

/-- Homotopy invariance of the log-derivative integral. -/
lemma integral_eq_of_homotopy {F F' : ℝ → ℝ → ℂ}
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, HasDerivAt (F r) (F' r s) s)
    (hcF : ContinuousOn (Function.uncurry F) (Icc 0 1 ×ˢ univ))
    (hcF' : ContinuousOn (Function.uncurry F') (Icc 0 1 ×ˢ univ))
    (hne : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, F r s ≠ 0)
    (hper : ∀ r ∈ Icc (0 : ℝ) 1, F r 1 = F r 0) :
    ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by
  set p : ℝ → ℝ := fun r => (projIcc (0 : ℝ) 1 zero_le_one r : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpI : ∀ r, p r ∈ Icc (0 : ℝ) 1 := fun r => (projIcc (0 : ℝ) 1 zero_le_one r).2
  have hpid : ∀ r ∈ Icc (0 : ℝ) 1, p r = r := fun r hr => by simp [p, projIcc_of_mem _ hr]
  set G : ℝ → ℝ → ℂ := fun r s => F' (p r) s / F (p r) s
  have hmap : Continuous fun q : ℝ × ℝ => (p q.1, q.2) := (hp.comp continuous_fst).prodMk continuous_snd
  have hmapI : ∀ q : ℝ × ℝ, (p q.1, q.2) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) :=
    fun q => ⟨hpI q.1, trivial⟩
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous fun q : ℝ × ℝ => Function.uncurry F' (p q.1, q.2) :=
      hcF'.comp_continuous hmap hmapI
    have h2 : Continuous fun q : ℝ × ℝ => Function.uncurry F (p q.1, q.2) :=
      hcF.comp_continuous hmap hmapI
    exact h1.div h2 fun q => hne _ (hpI q.1) q.2
  set W : ℝ → ℂ := fun r => ∫ s in (0 : ℝ)..1, G r s
  have hW : Continuous W := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hGc 0 1
  -- `W r ∈ 2πiℤ`
  have hk : ∀ r, ∃ k : ℤ, W r = k * (2 * Real.pi * I) := by
    intro r
    have hr := hpI r
    have hcont : Continuous (F' (p r)) := by
      have := hGc.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (r, s))
      have h1 : Continuous fun s : ℝ => Function.uncurry F' (p r, s) :=
        hcF'.comp_continuous (continuous_const.prodMk continuous_id) fun s => ⟨hr, trivial⟩
      exact h1
    exact integral_mem_two_pi_I (hF _ hr) hcont (hne _ hr) (hper _ hr)
  set f : ℝ → ℝ := fun r => (W r).im / (2 * Real.pi)
  have hf : Continuous f := (Complex.continuous_im.comp hW).div_const _
  have hfint : ∀ r, ∃ k : ℤ, f r = k := by
    intro r; obtain ⟨k, hk⟩ := hk r
    refine ⟨k, ?_⟩
    simp only [f, hk]
    simp [Complex.mul_im]
  have hWre : ∀ r, W r = (f r : ℂ) * (2 * Real.pi * I) := by
    intro r; obtain ⟨k, hk'⟩ := hk r
    have : f r = k := by
      simp only [f, hk']; simp [Complex.mul_im]
    rw [this, hk']; push_cast; ring
  -- `f` is constant on `[0, 1]`
  obtain ⟨k0, hk0⟩ := hfint 0
  obtain ⟨k1, hk1⟩ := hfint 1
  have hk01 : k0 = k1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · have hmem : (k0 : ℝ) + 1 / 2 ∈ Icc (f 0) (f 1) := by
        rw [hk0, hk1]
        have : (k0 : ℝ) + 1 ≤ k1 := by exact_mod_cast h
        constructor <;> linarith
      obtain ⟨r, -, hr⟩ := intermediate_value_Icc zero_le_one hf.continuousOn hmem
      obtain ⟨k, hk⟩ := hfint r
      rw [hk] at hr
      have h1 : (k : ℝ) - k0 = 1 / 2 := by linarith
      have h2 : ((k - k0 : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
      have h3 : (2 : ℝ) * ((k - k0 : ℤ) : ℝ) = 1 := by rw [h2]; norm_num
      have h4 : (2 * (k - k0) : ℤ) = 1 := by exact_mod_cast h3
      omega
    · have hmem : (k1 : ℝ) + 1 / 2 ∈ Icc (f 1) (f 0) := by
        rw [hk0, hk1]
        have : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast h
        constructor <;> linarith
      obtain ⟨r, -, hr⟩ := intermediate_value_Icc' zero_le_one hf.continuousOn hmem
      obtain ⟨k, hk⟩ := hfint r
      rw [hk] at hr
      have h1 : (k : ℝ) - k1 = 1 / 2 := by linarith
      have h2 : ((k - k1 : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
      have h3 : (2 : ℝ) * ((k - k1 : ℤ) : ℝ) = 1 := by rw [h2]; norm_num
      have h4 : (2 * (k - k1) : ℤ) = 1 := by exact_mod_cast h3
      omega
  have hW1 : W 1 = W 0 := by rw [hWre 1, hWre 0, hk0, hk1, hk01]
  have e1 : W 1 = ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s := by
    simp only [W, G, hpid 1 ⟨zero_le_one, le_rfl⟩]
  have e0 : W 0 = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by
    simp only [W, G, hpid 0 ⟨le_rfl, zero_le_one⟩]
  rw [← e1, ← e0, hW1]

/-- A closed loop whose argument strictly increases and which returns to the ray of
`c 0` only at the ends winds exactly once. -/
lemma integral_eq_two_pi_I_of_im_pos {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0)
    (hpos : ∀ t, 0 < (c' t / c t).im)
    (hray : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ l : ℝ, 0 < l → c t ≠ (l : ℂ) * c 0) :
    ∫ s in (0 : ℝ)..1, c' s / c s = 2 * Real.pi * I := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hq : Continuous fun s => c' s / c s := hc'.div hcc hne
  obtain ⟨k, hk⟩ := integral_mem_two_pi_I hc hc' hne hper
  set θ : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, c' s / c s).im
  have hθ : ∀ t, θ t = ∫ s in (0 : ℝ)..t, (c' s / c s).im := fun t => im_integral hq 0 t
  have hθc : Continuous θ := by
    have : θ = fun t => ∫ s in (0 : ℝ)..t, (c' s / c s).im := funext hθ
    rw [this]
    exact continuous_iff_continuousAt.2 fun t =>
      ((Complex.continuous_im.comp hq).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  have hθ1 : θ 1 = 2 * Real.pi * k := by
    simp only [θ, hk]; simp [Complex.mul_im]; ring
  have hθ1pos : 0 < θ 1 := by
    rw [hθ]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Complex.continuous_im.comp hq).intervalIntegrable 0 1) (fun t _ => hpos t) zero_lt_one
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by
      rw [hθ1] at hθ1pos
      have := Real.pi_pos
      nlinarith
    exact_mod_cast this
  have hk1 : k = 1 := by
    by_contra hk1
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show (2 : ℤ) ≤ k by omega)
    have hθ0 : θ 0 = 0 := by simp [θ]
    have hmem : 2 * Real.pi ∈ Icc (θ 0) (θ 1) := by
      rw [hθ0, hθ1]
      have := Real.pi_pos
      constructor <;> nlinarith
    obtain ⟨t, ht, hθt⟩ := intermediate_value_Icc zero_le_one hθc.continuousOn hmem
    have ht0 : t ≠ 0 := by
      rintro rfl; rw [hθ0] at hθt; have := Real.pi_pos; linarith
    have ht1 : t ≠ 1 := by
      rintro rfl; rw [hθ1] at hθt; have := Real.pi_pos; nlinarith
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    set L := ∫ s in (0 : ℝ)..t, c' s / c s
    have hL : L = (L.re : ℂ) + (2 * Real.pi : ℝ) * I := by
      apply Complex.ext <;> simp [θ] at hθt ⊢
      first | exact hθt | exact hθt.symm
    have hct := eq_mul_exp_integral hc hc' hne t
    apply hray t htI (Real.exp L.re) (Real.exp_pos _)
    have h2 : exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
      push_cast; exact Complex.exp_two_pi_mul_I
    have hE : exp L = (Real.exp L.re : ℂ) := by
      conv_lhs => rw [hL]
      rw [Complex.exp_add, h2, mul_one, Complex.ofReal_exp]
    rw [hct, hE]; ring
  rw [hk, hk1]; simp

end WindA

/-!
# Lifting a periodic immersion `ℝ → S¹` through `circlePoint`

`u = circlePoint ∘ θ` with `θ' = (u₀u₁' - u₁u₀')/2π ≠ 0` and `θ(s+1) = θ(s) + k`, `k ≠ 0`;
in particular `u` is onto the unit circle.
-/


noncomputable section

namespace HryniewiczCriterion

/-- A continuous real function without zeros has non-zero integral over `[0,1]`. -/
lemma td_integral_ne_zero_of_ne_zero {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) :
    ∫ x in (0 : ℝ)..1, f x ≠ 0 := by
  have key : ∀ g : ℝ → ℝ, Continuous g → (∀ x, g x ≠ 0) → 0 < g 0 →
      0 < ∫ x in (0 : ℝ)..1, g x := by
    intro g hg hg0 hpos
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hg.intervalIntegrable 0 1) ?_
      zero_lt_one
    intro x _
    by_contra hx
    push_neg at hx
    have hsub := intermediate_value_uIcc (a := 0) (b := x) hg.continuousOn
    obtain ⟨y, _, hy⟩ := hsub (show (0 : ℝ) ∈ uIcc (g 0) (g x) from
      mem_uIcc.2 (Or.inr ⟨hx, hpos.le⟩))
    exact hg0 y hy
  rcases (h0 0).lt_or_gt with hneg | hpos
  · have h := key (fun x => -f x) hf.neg (fun x => neg_ne_zero.2 (h0 x)) (by linarith)
    rw [intervalIntegral.integral_neg] at h
    linarith
  · exact (key f hf h0 hpos).ne'

theorem td_circle_lift (u : ℝ → Plane) (hu : ContDiff ℝ 2 u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hu' : ∀ s, deriv u s ≠ 0) :
    ∃ (θ θ' : ℝ → ℝ) (k : ℤ), k ≠ 0 ∧ Continuous θ' ∧ (∀ s, HasDerivAt θ (θ' s) s) ∧
      (∀ s, θ (s + 1) = θ s + k) ∧ ∀ s, u s = circlePoint (θ s) := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu'c : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have huc : Continuous u := hud.continuous
  set c : ℝ → ℂ := fun s => (u s 0 : ℂ) + (u s 1 : ℂ) * I with hcdef
  set c' : ℝ → ℂ := fun s => (deriv u s 0 : ℂ) + (deriv u s 1 : ℂ) * I with hc'def
  have hcomp : ∀ (i : Fin 2) s, HasDerivAt (fun s => u s i) (deriv u s i) s := fun i s =>
    hasDerivAt_pi.1 (hud s).hasDerivAt i
  have hc : ∀ s, HasDerivAt c (c' s) s := fun s =>
    ((hcomp 0 s).ofReal_comp).add (((hcomp 1 s).ofReal_comp).mul_const I)
  have hd0 : Continuous fun s => deriv u s 0 := (continuous_apply 0).comp hu'c
  have hd1 : Continuous fun s => deriv u s 1 := (continuous_apply 1).comp hu'c
  have hu0 : Continuous fun s => u s 0 := (continuous_apply 0).comp huc
  have hu1 : Continuous fun s => u s 1 := (continuous_apply 1).comp huc
  have hc'c : Continuous c' :=
    (continuous_ofReal.comp hd0).add ((continuous_ofReal.comp hd1).mul continuous_const)
  have hnorm : ∀ s, u s 0 ^ 2 + u s 1 ^ 2 = 1 := hucirc
  have hcre : ∀ s, (c s).re = u s 0 := by intro s; simp [c]
  have hcim : ∀ s, (c s).im = u s 1 := by intro s; simp [c]
  have hcn : ∀ s, normSq (c s) = 1 := by
    intro s; rw [normSq_apply, hcre, hcim]; nlinarith [hnorm s]
  have hne : ∀ s, c s ≠ 0 := fun s h => by
    have := hcn s; rw [h, map_zero] at this; norm_num at this
  have horth : ∀ s, u s 0 * deriv u s 0 + u s 1 * deriv u s 1 = 0 := by
    intro s
    have hd : HasDerivAt (fun s => u s 0 * u s 0 + u s 1 * u s 1)
        (deriv u s 0 * u s 0 + u s 0 * deriv u s 0 +
          (deriv u s 1 * u s 1 + u s 1 * deriv u s 1)) s :=
      ((hcomp 0 s).mul (hcomp 0 s)).add ((hcomp 1 s).mul (hcomp 1 s))
    have hconst : (fun s => u s 0 * u s 0 + u s 1 * u s 1) = fun _ => (1 : ℝ) :=
      funext fun s => by nlinarith [hnorm s]
    rw [hconst] at hd
    have := hd.unique (hasDerivAt_const s 1)
    linarith
  set wd : ℝ → ℝ := fun s => u s 0 * deriv u s 1 - u s 1 * deriv u s 0 with hwddef
  have hwdc : Continuous wd := (hu0.mul hd1).sub (hu1.mul hd0)
  have hc'eq : ∀ s, c' s = (wd s : ℂ) * I * c s := by
    intro s
    have hn' : ((u s 0 : ℝ) : ℂ) ^ 2 + ((u s 1 : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast hnorm s
    have ho' : ((u s 0 : ℝ) : ℂ) * (deriv u s 0 : ℂ) + (u s 1 : ℂ) * (deriv u s 1 : ℂ) = 0 := by
      exact_mod_cast horth s
    simp only [c, c', wd]
    push_cast
    linear_combination (-(deriv u s 0 : ℂ) - (deriv u s 1 : ℂ) * I) * hn' +
      ((u s 0 : ℂ) + (u s 1 : ℂ) * I) * ho' +
      (-((u s 0 : ℂ) * (deriv u s 1 : ℂ) - (u s 1 : ℂ) * (deriv u s 0 : ℂ)) * (u s 1 : ℂ)) *
        Complex.I_sq
  have hquot : ∀ s, c' s / c s = (wd s : ℂ) * I := fun s => by
    rw [hc'eq s, mul_div_assoc, div_self (hne s), mul_one]
  have hwdne : ∀ s, wd s ≠ 0 := by
    intro s hwd
    have h0 : c' s = 0 := by rw [hc'eq s, hwd]; simp
    have hr : (c' s).re = 0 := by rw [h0]; simp
    have hi : (c' s).im = 0 := by rw [h0]; simp
    simp [c'] at hr hi
    apply hu' s
    ext i; fin_cases i
    · exact hr
    · exact hi
  -- the lift
  have hL : ∀ t, (∫ s in (0 : ℝ)..t, c' s / c s) = ((∫ s in (0 : ℝ)..t, wd s : ℝ) : ℂ) * I := by
    intro t
    simp_rw [hquot]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  set a : ℝ := arg (c 0)
  have hc0n : ‖c 0‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq (c 0)
    rw [hcn 0] at h
    nlinarith [norm_nonneg (c 0)]
  have hc0 : c 0 = exp ((a : ℂ) * I) := by
    have := norm_mul_exp_arg_mul_I (c 0)
    rw [hc0n, ofReal_one, one_mul] at this
    exact this.symm
  set Φ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, wd s
  have hcexp : ∀ t, c t = exp (((a + Φ t : ℝ) : ℂ) * I) := by
    intro t
    rw [WindA.eq_mul_exp_integral hc hc'c hne t, hL t, hc0, ← Complex.exp_add]
    congr 1
    push_cast; ring
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  refine ⟨fun t => (a + Φ t) / (2 * Real.pi), fun t => wd t / (2 * Real.pi), ?_⟩
  -- the degree
  have hc10 : c 1 = c 0 := by
    have := huper 0; rw [zero_add] at this; simp only [c, this]
  obtain ⟨k, hk⟩ := WindA.integral_mem_two_pi_I hc hc'c hne hc10
  rw [hL 1] at hk
  have hwd1 : ∫ s in (0 : ℝ)..1, wd s = k * (2 * Real.pi) := by
    have h2 : ((∫ s in (0 : ℝ)..1, wd s : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi) := by
      have hI : (I : ℂ) ≠ 0 := I_ne_zero
      apply mul_right_cancel₀ hI
      rw [hk]; ring
    exact_mod_cast h2
  have hdper : ∀ s, deriv u (s + 1) = deriv u s := fun s => by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f => deriv f s) (funext huper)
  have hwdper : Function.Periodic wd 1 := fun s => by
    simp only [wd, huper s, hdper s]
  refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
  · intro hk0
    rw [hk0, Int.cast_zero, zero_mul] at hwd1
    exact td_integral_ne_zero_of_ne_zero hwdc hwdne hwd1
  · exact hwdc.div_const _
  · intro s
    have hΦ : HasDerivAt Φ (wd s) s := (hwdc.integral_hasStrictDerivAt 0 s).hasDerivAt
    exact ((hasDerivAt_const s a).add hΦ).div_const _ |>.congr_deriv (by ring)
  · intro s
    have hsub : Φ (s + 1) - Φ s = ∫ x in s..s + 1, wd x :=
      intervalIntegral.integral_interval_sub_left (hwdc.intervalIntegrable _ _)
        (hwdc.intervalIntegrable _ _)
    have hshift : ∫ x in s..s + 1, wd x = ∫ x in (0 : ℝ)..0 + 1, wd x :=
      hwdper.intervalIntegral_add_eq s 0
    rw [zero_add, hwd1] at hshift
    field_simp
    linarith
  · intro s
    have h := hcexp s
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    rw [exp_ofReal_mul_I_re, hcre] at hre
    rw [exp_ofReal_mul_I_im, hcim] at him
    have h2 : 2 * Real.pi * ((a + Φ s) / (2 * Real.pi)) = a + Φ s := by field_simp
    ext i; fin_cases i
    · simp [circlePoint, h2, hre]
    · simp [circlePoint, h2, him]

/-- A periodic immersion into the circle is onto. -/
theorem td_circle_surj (u : ℝ → Plane) (θ θ' : ℝ → ℝ) (k : ℤ) (hk : k ≠ 0)
    (hθ : ∀ s, HasDerivAt θ (θ' s) s) (hθper : ∀ s, θ (s + 1) = θ s + k)
    (hθu : ∀ s, u s = circlePoint (θ s)) :
    ∀ w ∈ unitCircle, ∃ s, u s = w := by
  intro w hw
  have hw' : w 0 ^ 2 + w 1 ^ 2 = 1 := hw
  set z : ℂ := (w 0 : ℂ) + (w 1 : ℂ) * I
  have hzre : z.re = w 0 := by simp [z]
  have hzim : z.im = w 1 := by simp [z]
  have hzn : ‖z‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [normSq_apply, hzre, hzim] at h
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hzn; norm_num at hzn
  set b : ℝ := arg z / (2 * Real.pi)
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcp : ∀ m : ℤ, circlePoint (b + m) = w := by
    intro m
    have h2 : 2 * Real.pi * (b + m) = arg z + m * (2 * Real.pi) := by
      simp only [b]; field_simp
    ext i; fin_cases i
    · simp only [circlePoint, h2]
      simp [Real.cos_add_int_mul_two_pi, Complex.cos_arg hz0, hzn, hzre]
    · simp only [circlePoint, h2]
      simp [Real.sin_add_int_mul_two_pi, Complex.sin_arg, hzn, hzim]
  have hθc : Continuous θ := continuous_iff_continuousAt.2 fun s => (hθ s).continuousAt
  have h1 : θ 1 = θ 0 + k := by simpa using hθper 0
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  -- a target value `b + m` between `θ 0` and `θ 1`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, b + m ∈ uIcc (θ 0) (θ 1) := by
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
      refine ⟨⌊θ 0 - b⌋, mem_uIcc.2 (Or.inr ⟨?_, ?_⟩)⟩
      · have := Int.sub_one_lt_floor (θ 0 - b); rw [h1]; linarith
      · have := Int.floor_le (θ 0 - b); linarith
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hpos
      refine ⟨⌈θ 0 - b⌉, mem_uIcc.2 (Or.inl ⟨?_, ?_⟩)⟩
      · have := Int.le_ceil (θ 0 - b); linarith
      · have := Int.ceil_lt_add_one (θ 0 - b); rw [h1]; linarith
  obtain ⟨s, _, hs⟩ := intermediate_value_uIcc (a := 0) (b := 1) hθc.continuousOn hm
  exact ⟨s, by rw [hθu s, hs, hcp m]⟩

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (u : ℝ → Plane) (hu : ContDiff ℝ 2 u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hu' : ∀ s, deriv u s ≠ 0) :
    ∃ (θ θ' : ℝ → ℝ) (k : ℤ), k ≠ 0 ∧ Continuous θ' ∧ (∀ s, HasDerivAt θ (θ' s) s) ∧
      (∀ s, θ (s + 1) = θ s + k) ∧ ∀ s, u s = circlePoint (θ s) :=
  HryniewiczCriterion.td_circle_lift u hu huper hucirc hu'

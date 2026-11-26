-- Prove2me | solution 1 for Kyprianou.Ch04.discountedBVResidualIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:52:36.041309+00:00
-- url     : https://prove2.me/submissions/b517062b-2182-44c9-bd23-2ffb058cff4e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedVariationChangeOfVariables
import Theorems.Thm_Kyprianou_Ch04_discountedTestFunctionDerivatives
import Theorems.Thm_Kyprianou_Ch04_continuousStatePathCompactIntegrable
import Theorems.Thm_Kyprianou_Ch04_cadlagLeftPathClockAE
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Discounted bounded-variation change of variables minus physical compensation. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hLevy : IsLevyProcess X P)
    (T : LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : ℝ), charFun (P.map (X t)) theta =
      Complex.exp (((t:ℝ):ℂ)*Kyprianou.Ch01.levyTripleExponent T theta))
    (hBV : T.gaussianVariance = 0 ∧
      (∫⁻ x in Ioo (-1:ℝ) 1, ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (hLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hXm : ∀ᵐ w ∂P, Measurable (fun r : ℝ => X r.toNNReal w))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (l : ℝ)
    (G : ℝ → ℝ) (hG : G = fun y => ∫ x, (f (y+x)-f y) ∂T.levyMeasure)
    (hGc : Continuous G) :
    let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
    let J := fun (t : NNReal) w => Real.exp (-l*(t:ℝ))*f (X t w)
    let k := fun (s x : ℝ) w => Real.exp (-l*s)*(f (L s.toNNReal w+x)-f (L s.toNNReal w))
    ∀ᵐ w ∂P, ∀ t : NNReal,
      (∫ s in Icc (0:ℝ) (t:ℝ), Real.exp (-l*s) *
        (d * deriv f (X s.toNNReal w)+G (X s.toNNReal w)-l*f (X s.toNNReal w)) ∂volume)
      = J t w-J 0 w -
        ((∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ univ, k z.1 z.2 w ∂(pathJumpMeasure X L w)) -
          ∫ s in Icc (0:ℝ) (t:ℝ), ∫ x, k s x w ∂T.levyMeasure ∂volume) := by
  let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
  let q := fun p : ℝ × ℝ => Real.exp (-l*p.1)*f p.2
  have hq : ContDiff ℝ 1 q := (discountedTestFunctionDerivatives f hf l 0 0).1
  have hCV := boundedVariationChangeOfVariables P X hLevy T hTriplet hBV L hLeft q hq.contDiffOn
  filter_upwards [hCV,hLevy.cadlag_ae,hLeft,hXm] with w hw hcad hleft hm
  intro t
  let a := fun s : ℝ => -l*Real.exp (-l*s)*f (X s.toNNReal w)
  let b := fun s : ℝ => Real.exp (-l*s)*deriv f (X s.toNNReal w)
  let e := fun s : ℝ => Real.exp (-l*s)*G (X s.toNNReal w)
  have ha : IntegrableOn a (Icc (0:ℝ) (t:ℝ)) volume :=
    continuousStatePathCompactIntegrable _ hcad hm
      (fun p => -l*Real.exp (-l*p.1)*f p.2) (by fun_prop) t
  have hb : IntegrableOn b (Icc (0:ℝ) (t:ℝ)) volume :=
    continuousStatePathCompactIntegrable _ hcad hm
      (fun p => Real.exp (-l*p.1)*deriv f p.2)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
        (hf.continuous_deriv_one.comp continuous_snd)) t
  have he : IntegrableOn e (Icc (0:ℝ) (t:ℝ)) volume :=
    continuousStatePathCompactIntegrable _ hcad hm
      (fun p => Real.exp (-l*p.1)*G p.2) (by fun_prop) t
  have hD1 (s : ℝ) : fderiv ℝ q (s,X s.toNNReal w) (1,0) = a s :=
    (discountedTestFunctionDerivatives f hf l s (X s.toNNReal w)).2.1
  have hD2 (s : ℝ) : fderiv ℝ q (s,X s.toNNReal w) (0,1) = b s :=
    (discountedTestFunctionDerivatives f hf l s (X s.toNNReal w)).2.2
  have hEq := hw t
  simp only [hD1,hD2] at hEq
  have hLeftAE := cadlagLeftPathClockAE (fun u => X u w) (fun u => L u w)
    (fun u => (hcad u).1) hleft
  have hComp : (∫ s in Icc (0:ℝ) (t:ℝ), ∫ x,
      Real.exp (-l*s)*(f (L s.toNNReal w+x)-f (L s.toNNReal w)) ∂T.levyMeasure ∂volume)
      = ∫ s in Icc (0:ℝ) (t:ℝ), e s ∂volume := by
    apply integral_congr_ae
    have hSub : Icc (0:ℝ) (t:ℝ) ⊆ Ici (0:ℝ) := fun _ hs => hs.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub hLeftAE] with s hs
    rw [integral_const_mul,← hs]
    simp only [e,hG]
  have hInt : (∫ s in Icc (0:ℝ) (t:ℝ), Real.exp (-l*s) *
      (d*deriv f (X s.toNNReal w)+G (X s.toNNReal w)-l*f (X s.toNNReal w)) ∂volume)
      = (∫ s in Icc (0:ℝ) (t:ℝ), a s ∂volume) +
        d*(∫ s in Icc (0:ℝ) (t:ℝ), b s ∂volume) +
        ∫ s in Icc (0:ℝ) (t:ℝ), e s ∂volume := by
    calc
      _ = ∫ s in Icc (0:ℝ) (t:ℝ), (a s+d*b s)+e s ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with s
        dsimp only [a,b,e]
        ring
      _ = _ := by
        have hh := integral_add (ha.add (hb.const_mul d)) he
        change (∫ s in Icc (0:ℝ) (t:ℝ), (a s+d*b s)+e s ∂volume) =
          (∫ s in Icc (0:ℝ) (t:ℝ), a s+d*b s ∂volume) +
          ∫ s in Icc (0:ℝ) (t:ℝ), e s ∂volume at hh
        rw [hh,integral_add ha (hb.const_mul d),integral_const_mul]
  rw [hInt,hComp]
  dsimp only [q] at hEq
  -- factor the discount inside the physical jump difference
  have hRaw : (∫ z in (Icc (0:ℝ) (t:ℝ)).prod (univ : Set ℝ),
      (Real.exp (-l*z.1)*f (L z.1.toNNReal w+z.2) -
        Real.exp (-l*z.1)*f (L z.1.toNNReal w)) ∂(pathJumpMeasure X L w)) =
      ∫ z in (Icc (0:ℝ) (t:ℝ)).prod (univ : Set ℝ),
        Real.exp (-l*z.1)*(f (L z.1.toNNReal w+z.2)-f (L z.1.toNNReal w))
        ∂(pathJumpMeasure X L w) := by
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  rw [hRaw] at hEq
  change _ = _ at hEq
  change _ = _
  simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul] at hEq ⊢
  change Real.exp (-l*(t:ℝ))*f (X t w) = f (X 0 w) +
      (∫ s in Icc (0:ℝ) (t:ℝ), a s ∂volume) +
      d*(∫ s in Icc (0:ℝ) (t:ℝ), b s ∂volume) +
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ univ,
        Real.exp (-l*z.1)*(f (L z.1.toNNReal w+z.2)-f (L z.1.toNNReal w))
        ∂(pathJumpMeasure X L w)) at hEq
  linarith only [hEq]

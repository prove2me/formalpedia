-- Prove2me | solution 1 for LearnNoConc.ERM.noise_correlation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T07:57:38.650982+00:00
-- url     : https://prove2.me/submissions/5fc9ce9f-8868-441b-844d-af0de983896b

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting
open MeasureTheory
namespace Queelius.SmallBall
lemma quadratic_first_order (A B : ℝ) (hA : 0 ≤ A)
    (h : ∀ t : ℝ,0 ≤ t → t ≤ 1 → 0 ≤ 2*t*B+t^2*A) : 0 ≤ B := by
  by_contra hb
  have hB : B < 0 := lt_of_not_ge hb
  let d := A-B+1
  have hd : 0 < d := by dsimp [d];linarith
  let t := -B/d
  have ht : 0 < t := div_pos (by linarith) hd
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by dsimp [d];linarith)
  have he : t*d = -B := div_mul_cancel₀ (-B) hd.ne'
  have hn : 2*B+t*A < 0 := by dsimp [d] at he;nlinarith
  have hh := h t ht.le ht1
  nlinarith
lemma integral_quadratic {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (u v : Z → ℝ) (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) (t : ℝ) :
    (∫ z,(u z+t*v z)^2 ∂ν) = (∫ z,u z^2 ∂ν)+
      (2*t)*(∫ z,u z*v z ∂ν)+t^2*(∫ z,v z^2 ∂ν) := by
  have hu2 := hu.integrable_sq
  have hv2 := hv.integrable_sq
  have huv := hu.integrable_mul hv
  have he : (fun z => (u z+t*v z)^2) =
      (fun z => u z^2+(2*t)*(u z*v z)+t^2*v z^2) := by funext z;ring
  have h1 : (∫ z,u z^2+(2*t)*(u z*v z) ∂ν)=
      (∫ z,u z^2 ∂ν)+(∫ z,(2*t)*(u z*v z) ∂ν) := by
    simpa only [Pi.add_apply,Pi.mul_apply] using integral_add hu2 (huv.const_mul (2*t))
  have h2 : (∫ z,u z^2+(2*t)*(u z*v z)+t^2*v z^2 ∂ν)=
      (∫ z,u z^2+(2*t)*(u z*v z) ∂ν)+(∫ z,t^2*v z^2 ∂ν) := by
    simpa only [Pi.add_apply,Pi.mul_apply] using
      integral_add (hu2.add (huv.const_mul (2*t))) (hv2.const_mul (t^2))
  rw [he,h2,h1,integral_const_mul,integral_const_mul]
lemma first_order_integral {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (u v : Z → ℝ) (hu : MemLp u 2 ν) (hv : MemLp v 2 ν)
    (h : ∀ t : ℝ,0 ≤ t → t ≤ 1 → (∫ z,u z^2 ∂ν) ≤ ∫ z,(u z+t*v z)^2 ∂ν) :
    0 ≤ ∫ z,u z*v z ∂ν := by
  apply quadratic_first_order (∫ z,v z^2 ∂ν) (∫ z,u z*v z ∂ν)
    (integral_nonneg (fun _ => sq_nonneg _))
  intro t ht ht1
  have hh := h t ht ht1
  rw [integral_quadratic ν u v hu hv t] at hh
  linarith
lemma correlation {Ω : Type*} [MeasurableSpace Ω] (ν : Measure (Ω × ℝ))
    (F : Set (Ω → ℝ)) (hF2 : ∀ f ∈ F, MemLp f 2 (ν.map Prod.fst))
    (hFconv : Convex ℝ F) (hY : MemLp (fun z : Ω × ℝ => z.2) 2 ν)
    (fstar : Ω → ℝ) (hfstar : fstar ∈ F)
    (hmin : ∀ f ∈ F, ∫ z,(fstar z.1-z.2)^2 ∂ν ≤ ∫ z,(f z.1-z.2)^2 ∂ν)
    (f : Ω → ℝ) (hf : f ∈ F) :
    0 ≤ ∫ z,(fstar z.1-z.2)*(f z.1-fstar z.1) ∂ν := by
  have hs : MemLp (fun z : Ω × ℝ => fstar z.1) 2 ν :=
    (hF2 fstar hfstar).comp_of_map measurable_fst.aemeasurable
  have hf2 : MemLp (fun z : Ω × ℝ => f z.1) 2 ν :=
    (hF2 f hf).comp_of_map measurable_fst.aemeasurable
  apply first_order_integral ν (fun z => fstar z.1-z.2) (fun z => f z.1-fstar z.1)
    (hs.sub hY) (hf2.sub hs)
  intro t ht ht1
  have hm := hmin ((1-t) • fstar+t • f)
    (hFconv hfstar hf (by linarith) ht (by ring))
  have he (z : Ω × ℝ) : (((1-t) • fstar+t • f) z.1-z.2)^2=
      (fstar z.1-z.2+t*(f z.1-fstar z.1))^2 := by simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
  simpa only [he] using hm
lemma quadratic_boundary_control :
    (∀ t ∈ Set.Icc (0:ℝ) 1,0 ≤ (1+t)^2-1) ∧
    (2*(-1:ℝ)*(1/2)+(1/2)^2*1 < 0) := by
  constructor
  · intro t ht;have ht0 := ht.1;nlinarith [sq_nonneg t]
  · norm_num
end Queelius.SmallBall

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- §5, p. 23: since `f*` minimizes `‖Y − f(X)‖_{L₂}` over the convex class `F`, the
metric-projection characterization gives `E ξ (f − f*)(X) ≥ 0` for every `f ∈ F`,
where `ξ = f*(X) − Y`. -/
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (ν : Measure (Ω × ℝ))
    [IsProbabilityMeasure ν] (F : Set (Ω → ℝ)) (hF2 : ∀ f ∈ F, MemLp f 2 (ν.map Prod.fst))
    (hFconv : Convex ℝ F) (hY : MemLp (fun z : Ω × ℝ => z.2) 2 ν)
    (fstar : Ω → ℝ) (hfstar : fstar ∈ F)
    (hmin : ∀ f ∈ F, ∫ z, (fstar z.1 - z.2) ^ 2 ∂ν ≤ ∫ z, (f z.1 - z.2) ^ 2 ∂ν) :
    ∀ f ∈ F, 0 ≤ ∫ z, (fstar z.1 - z.2) * (f z.1 - fstar z.1) ∂ν := by
  exact Queelius.SmallBall.correlation ν F hF2 hFconv hY fstar hfstar hmin

end LearnNoConc.ERM

-- Prove2me | solution 1 for OAI.CKSMixedGeometry.cks_sourceCollarData_bounded
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:20:10.625169+00:00
-- url     : https://prove2.me/submissions/bf878c7d-0964-4c80-b51e-65435dc84d25

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_congr {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (e : E) : D e f x = D e g x := by
  unfold D
  rw [h.fderiv_eq]

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]
lemma D_add (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y + g y) x = D e f x + D e g x := by
  simp [D, fderiv_fun_add hf hg]

lemma D_const_mul (e : E) {f : E → ℝ} {x : E} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) : D e (fun y => c * f y) x = c * D e f x := by
  rw [D_mul e (differentiableAt_const c) hf, D_const]
  ring

lemma contDiffAt_D {f : E → ℝ} {x : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f x)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) (e : E) : ContDiffAt ℝ m (D e f) x :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

lemma D_D_mul (e w : E) {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    D w (D e (fun y => f y * g y)) x =
      f x * D w (D e g) x + g x * D w (D e f) x +
        D w f x * D e g x + D w g x * D e f x := by
  have heq : D e (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => f y * D e g y + g y * D e f y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact D_mul e (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  have hf1 := hf.differentiableAt (by norm_num)
  have hg1 := hg.differentiableAt (by norm_num)
  have hfe := (contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  have hge := (contDiffAt_D hg (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  rw [D_congr heq w, D_add w (hf1.fun_mul hge) (hg1.fun_mul hfe),
    D_mul w hf1 hge, D_mul w hg1 hfe]
  ring

lemma D_inv (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    D e (fun y => (f y)⁻¹) x = -(D e f x) / (f x) ^ 2 := by
  unfold D
  change fderiv ℝ ((fun z : ℝ => z⁻¹) ∘ f) x e = _
  rw [((hasDerivAt_inv h0).comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp
  ring

lemma D_div (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h0 : g x ≠ 0) :
    D e (fun y => f y / g y) x =
      (D e f x * g x - f x * D e g x) / (g x) ^ 2 := by
  simp only [div_eq_mul_inv]
  rw [D_mul (g := fun y => (g y)⁻¹) e hf (hg.inv h0), D_inv e hg h0]
  field_simp
  ring

lemma D_pow (e : E) {f : E → ℝ} {x : E} (n : ℕ)
    (hf : DifferentiableAt ℝ f x) :
    D e (fun y => f y ^ n) x = n * f x ^ (n - 1) * D e f x := by
  unfold D
  rw [fderiv_fun_pow n hf]
  simp

lemma D_D_const (e w x : E) (c : ℝ) : D w (D e (fun _ => c)) x = 0 := by
  have h : D e (fun _ : E => c) = fun _ => 0 := funext (fun y => D_const e y c)
  rw [h, D_const]

lemma D_comp_real (e : E) {f : ℝ → ℝ} {g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f (g y)) x = deriv f (g x) * D e g x := by
  unfold D
  change fderiv ℝ (f ∘ g) x e = _
  rw [(hf.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt).fderiv]
  simp

lemma D_inv_inv (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    D e (fun y => 1 / f y) x = - D e f x / f x ^ 2 := by
  simpa only [one_div] using D_inv e hf h0

lemma D_D_inv (e w : E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (h0 : f x ≠ 0) :
    D w (D e (fun y => 1 / f y)) x =
      2 * D e f x * D w f x / f x ^ 3 - D w (D e f) x / f x ^ 2 := by
  have heq : D e (fun y => 1 / f y) =ᶠ[𝓝 x]
      (fun y => (-1) * D e f y / f y ^ 2) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually_ne h0]
      with y hyf hy0
    simpa using D_inv_inv e (hyf.differentiableAt (by norm_num)) hy0
  have hf1 := hf.differentiableAt (by norm_num)
  have hfe := (contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  rw [D_congr heq w,
    D_div (f := fun y => (-1) * D e f y) (g := fun y => f y ^ 2) w
      (hfe.const_mul (-1)) (hf1.pow 2) (pow_ne_zero _ h0),
    D_const_mul w (-1) hfe, D_pow w 2 hf1]
  norm_num
  field_simp
  ring

lemma D_sqrt (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : 0 < f x) :
    D e (fun y => Real.sqrt (f y)) x = D e f x / (2 * Real.sqrt (f x)) := by
  unfold D
  change fderiv ℝ (Real.sqrt ∘ f) x e = _
  rw [((Real.hasDerivAt_sqrt h0.ne').comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp
  ring

lemma D_D_sqrt (e w : E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (h0 : 0 < f x) :
    D w (D e (fun y => Real.sqrt (f y))) x =
      D w (D e f) x / (2 * Real.sqrt (f x)) -
      D e f x * D w f x / (4 * Real.sqrt (f x) ^ 3) := by
  have heq : D e (fun y => Real.sqrt (f y)) =ᶠ[𝓝 x]
      (fun y => D e f y / (2 * Real.sqrt (f y))) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually (eventually_gt_nhds h0)]
      with y hyf hy0
    exact D_sqrt e (hyf.differentiableAt (by norm_num)) hy0
  have hf1 := hf.differentiableAt (by norm_num)
  have hfe := (contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  have hsq := hf1.sqrt h0.ne'
  have hs0 : Real.sqrt (f x) ≠ 0 := (Real.sqrt_pos.2 h0).ne'
  rw [D_congr heq w, D_div (f := D e f) (g := fun y => 2 * Real.sqrt (f y)) w
    hfe (hsq.const_mul 2) (mul_ne_zero (by norm_num) hs0),
    D_const_mul w 2 hsq, D_sqrt w hf1 h0]
  field_simp
  ring

end
end CKSCalculus

end









end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem exact_mass_cancellation {z D T V : ℝ} (hz : z ≠ 0) (hv : 1+z^3*V ≠ 0) :
    (z^2+(1+z^3*T)^2-(1+z^2)*(1+z^3*D)^2/(1+z^3*V))/(2*z^3) =
      ((1+z^2)*V+2*T-2*(1+z^2)*D+
        z^3*(T^2+2*T*V-(1+z^2)*D^2)+z^6*T^2*V)/(2*(1+z^3*V)) := by
  field_simp
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actual_reciprocal {z : Point → ℝ} {x : Point} (hz : ContDiffAt ℝ 2 z x) (h0 : z x ≠ 0) :
    actualScalarJet (fun y => 1/z y) x = reciprocalJet (actualScalarJet z x) := by
  dsimp only [actualScalarJet, reciprocalJet]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a
    exact D_inv_inv (basis a) (hz.differentiableAt (by norm_num)) h0
  · ext a b
    dsimp [actualScalarJet,reciprocalJet]
    rw [D_D_inv (basis b) (basis a) hz h0]
    ring

lemma actualScalarJet_const (c : ℝ) (x : Point) : actualScalarJet (fun _ => c) x = constantJet c := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a; exact D_const _ _ _
  · ext a b; exact D_D_const _ _ _ _

lemma actualScalarJet_add {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => f y+g y) x = actualScalarJet f x+actualScalarJet g x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_add _ (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))
  · ext a b
    have heq : D (basis b) (fun y => f y+g y) =ᶠ[𝓝 x]
        (fun y => D (basis b) f y+D (basis b) g y) := by
      filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
      exact D_add _ (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
    change D (basis a) (D (basis b) (fun y => f y+g y)) x = _
    rw [D_congr heq]
    exact D_add _ ((contDiffAt_D hf (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))
      ((contDiffAt_D hg (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))

lemma actualScalarJet_smul (c : ℝ) {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    actualScalarJet (fun y => c*f y) x = c • actualScalarJet f x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_const_mul _ c (hf.differentiableAt (by norm_num))
  · ext a b
    have heq : D (basis b) (fun y => c*f y) =ᶠ[𝓝 x]
        (fun y => c*D (basis b) f y) := by
      filter_upwards [hf.eventually (by norm_num)] with y hyf
      exact D_const_mul _ c (hyf.differentiableAt (by norm_num))
    change D (basis a) (D (basis b) (fun y => c*f y)) x = _
    rw [D_congr heq]
    exact D_const_mul _ c ((contDiffAt_D hf (m := 1) (by norm_num) (basis b)).differentiableAt (by norm_num))

lemma actualScalarJet_sub {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => f y-g y) x = actualScalarJet f x-actualScalarJet g x := by
  have hh : (fun y => f y-g y) = (fun y => f y+(-1)*g y) := by funext y; ring
  have hn : ContDiffAt ℝ 2 (fun y => (-1:ℝ)*g y) x := hg.const_smul (-1:ℝ)
  rw [hh,actualScalarJet_add hf hn,actualScalarJet_smul (-1) hg]
  simp [sub_eq_add_neg]

lemma actualScalarJet_mul {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => f y*g y) x = productJet (actualScalarJet f x) (actualScalarJet g x) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_mul _ (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))
  · ext a b
    exact D_D_mul (basis b) (basis a) hf hg

lemma reciprocalJet_smooth {j : ScalarJet} (h0 : j.1 ≠ 0) : ContDiffAt ℝ ∞ reciprocalJet j := by
  unfold reciprocalJet
  apply ContDiffAt.prodMk
  · exact contDiffAt_const.div (by fun_prop) h0
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => -j.2.1 a) j).div
      (by fun_prop) (pow_ne_zero 2 h0)
  · apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    exact ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => 2*j.2.1 a*j.2.1 b) j).div
      (by fun_prop) (pow_ne_zero 3 h0)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.2 a b) j).div (by fun_prop) (pow_ne_zero 2 h0))

lemma actualScalarJet_congr {f g : Point → ℝ} {x : Point} (h : f =ᶠ[𝓝 x] g) :
    actualScalarJet f x = actualScalarJet g x := by
  apply Prod.ext
  · exact h.eq_of_nhds
  apply Prod.ext
  · ext a
    exact D_congr h (basis a)
  · ext a b
    have hd : D (basis b) f =ᶠ[𝓝 x] D (basis b) g := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : Point →L[ℝ] ℝ => L (basis b)) hy
    exact D_congr hd (basis a)

lemma actualScalarJet_linear (c d : ℝ) {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => c*f y+d*g y) x = c • actualScalarJet f x+d • actualScalarJet g x := by
  have hcf : ContDiffAt ℝ 2 (fun y => c*f y) x := by simpa only [smul_eq_mul] using hf.const_smul c
  have hdg : ContDiffAt ℝ 2 (fun y => d*g y) x := by simpa only [smul_eq_mul] using hg.const_smul d
  rw [actualScalarJet_add hcf hdg,
    actualScalarJet_smul c hf,actualScalarJet_smul d hg]

lemma actualScalarJet_D_linear (c d : ℝ) {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) (a : I) :
    actualScalarJet (D (basis a) (fun y => c*f y+d*g y)) x =
      c • actualScalarJet (D (basis a) f) x+d • actualScalarJet (D (basis a) g) x := by
  have heq : D (basis a) (fun y => c*f y+d*g y) =ᶠ[𝓝 x]
      (fun y => c*D (basis a) f y+d*D (basis a) g y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
    have hfd := hyf.differentiableAt (by norm_num)
    have hgd := hyg.differentiableAt (by norm_num)
    rw [D_add _ (hfd.const_mul c) (hgd.const_mul d),D_const_mul _ c hfd,D_const_mul _ d hgd]
  rw [actualScalarJet_congr heq]
  exact actualScalarJet_linear c d (contDiffAt_D hf (by norm_num) (basis a))
    (contDiffAt_D hg (by norm_num) (basis a))

lemma actualScalarJet_neg {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    actualScalarJet (fun y => -(f y)) x = -actualScalarJet f x := by
  simpa using actualScalarJet_smul (-1) hf

lemma actualScalarJet_sum {α : Type*} (s : Finset α) {f : α → Point → ℝ} {x : Point}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    actualScalarJet (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, actualScalarJet (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change actualScalarJet (fun _ => 0) x = constantJet 0
    exact actualScalarJet_const 0 x
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [actualScalarJet_add (hf a (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actualThreeJet_const (c : ℝ) (x : Point) :
    actualThreeJet (fun _ => c) x = constantThreeJet c := by
  apply Prod.ext
  · exact actualScalarJet_const c x
  · funext a
    change actualScalarJet (D (basis a) (fun _ : Point => c)) x = 0
    have hz : D (basis a) (fun _ : Point => c) = (fun _ => 0) := by
      funext y
      exact D_const _ _ _
    rw [hz]
    exact actualScalarJet_const 0 x

lemma actualThreeJet_linear (c d : ℝ) {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    actualThreeJet (fun y => c*f y+d*g y) x = c • actualThreeJet f x+d • actualThreeJet g x := by
  apply Prod.ext
  · exact actualScalarJet_linear c d (hf.of_le (by norm_num)) (hg.of_le (by norm_num))
  · funext a
    exact actualScalarJet_D_linear c d hf hg a

lemma actualThreeJet_smul (c : ℝ) {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    actualThreeJet (fun y => c*f y) x = c • actualThreeJet f x := by
  simpa using actualThreeJet_linear c 0 hf (contDiffAt_const (c := (0:ℝ)))

lemma actualThreeJet_add {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    actualThreeJet (fun y => f y+g y) x = actualThreeJet f x+actualThreeJet g x := by
  simpa using actualThreeJet_linear 1 1 hf hg

lemma actualThreeJet_neg {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    actualThreeJet (fun y => -f y) x = -actualThreeJet f x := by
  simpa using actualThreeJet_smul (-1) hf

lemma actualThreeJet_sub {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    actualThreeJet (fun y => f y-g y) x = actualThreeJet f x-actualThreeJet g x := by
  simpa [sub_eq_add_neg] using actualThreeJet_linear 1 (-1) hf hg

theorem actualThreeJet_mul {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    actualThreeJet (fun y => f y*g y) x = productThreeJet (actualThreeJet f x) (actualThreeJet g x) := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hg2 : ContDiffAt ℝ 2 g x := hg.of_le (by norm_num)
  apply Prod.ext
  · exact actualScalarJet_mul hf2 hg2
  · funext a
    have heq : D (basis a) (fun y => f y*g y) =ᶠ[𝓝 x]
        (fun y => f y*D (basis a) g y+g y*D (basis a) f y) := by
      filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
      exact D_mul _ (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
    change actualScalarJet (D (basis a) (fun y => f y*g y)) x = _
    rw [actualScalarJet_congr heq]
    have hfd : ContDiffAt ℝ 2 (D (basis a) f) x := contDiffAt_D hf (by norm_num) _
    have hgd : ContDiffAt ℝ 2 (D (basis a) g) x := contDiffAt_D hg (by norm_num) _
    rw [actualScalarJet_add (hf2.mul hgd) (hg2.mul hfd),
      actualScalarJet_mul hf2 hgd,actualScalarJet_mul hg2 hfd]
    rfl

theorem actualThreeJet_reciprocal {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (h0 : f x ≠ 0) :
    actualThreeJet (fun y => 1/f y) x = reciprocalThreeJet (actualThreeJet f x) := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hi : ContDiffAt ℝ 2 (fun y => 1/f y) x := contDiffAt_const.div hf2 h0
  apply Prod.ext
  · exact actual_reciprocal hf2 h0
  · funext a
    have heq : D (basis a) (fun y => 1/f y) =ᶠ[𝓝 x]
        (fun y => -((1/f y)*(1/f y)*D (basis a) f y)) := by
      filter_upwards [hf.eventually (by norm_num),hf.continuousAt.eventually_ne h0] with y hyf hy0
      rw [D_inv_inv _ (hyf.differentiableAt (by norm_num)) hy0]
      field_simp
    change actualScalarJet (D (basis a) (fun y => 1/f y)) x = _
    rw [actualScalarJet_congr heq]
    have hfd : ContDiffAt ℝ 2 (D (basis a) f) x := contDiffAt_D hf (by norm_num) _
    rw [actualScalarJet_neg ((hi.mul hi).mul hfd),actualScalarJet_mul (hi.mul hi) hfd,
      actualScalarJet_mul hi hi,actual_reciprocal hf2 h0]
    rfl

lemma reciprocalThreeJet_smooth {f : ScalarThreeJet} (h0 : f.1.1 ≠ 0) :
    ContDiffAt ℝ ∞ reciprocalThreeJet f := by
  have hi : ContDiffAt ℝ ∞ (fun j : ScalarThreeJet => reciprocalJet j.1) f :=
    (reciprocalJet_smooth h0).comp f (by fun_prop)
  have hp : ContDiffAt ℝ ∞ (fun j : ScalarThreeJet => productJet (reciprocalJet j.1) (reciprocalJet j.1)) f :=
    productJet_smooth.contDiffAt.comp f (hi.prodMk hi)
  apply ContDiffAt.prodMk hi
  apply contDiffAt_pi.mpr
  intro a
  exact (productJet_smooth.contDiffAt.comp f
    (hp.prodMk (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarThreeJet => j.2 a) f))).neg

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff

lemma actualScalarJet_sqrt {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (h0 : 0 < f x) :
    actualScalarJet (fun y => Real.sqrt (f y)) x = sqrtJet (actualScalarJet f x) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_sqrt _ (hf.differentiableAt (by norm_num)) h0
  · ext a b
    dsimp [actualScalarJet,sqrtJet]
    rw [D_D_sqrt (basis b) (basis a) hf h0]
    ring

lemma sqrtJet_smooth {j : ScalarJet} (h0 : 0 < j.1) : ContDiffAt ℝ ∞ sqrtJet j := by
  have hs : ContDiffAt ℝ ∞ (fun j : ScalarJet => Real.sqrt j.1) j :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.1) j).sqrt h0.ne'
  unfold sqrtJet
  apply ContDiffAt.prodMk hs
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.1 a) j).div (hs.const_smul (2:ℝ)) (by positivity)
  · apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    exact ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.2 a b) j).div (hs.const_smul (2:ℝ)) (by positivity)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.1 a*j.2.1 b) j).div ((hs.pow 3).const_smul (4:ℝ)) (by positivity))

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma component_diff {n : ℕ∞ω} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (i k : A) : ContDiffAt ℝ n (fun y => q y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k
lemma component_three {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (i k : A) : ContDiffAt ℝ 3 (fun y => q y i k) x :=
  component_diff hq i k

lemma actual_determinantJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) :
    actualScalarJet (fun y => determinant (q y)) x = determinantJet (matrixScalarJets q x) := by
  unfold determinant determinantJet matrixScalarJets
  rw [actualScalarJet_sub ((component_diff hq 0 0).mul (component_diff hq 1 1))
    ((component_diff hq 0 1).mul (component_diff hq 1 0)),
    actualScalarJet_mul (component_diff hq 0 0) (component_diff hq 1 1),
    actualScalarJet_mul (component_diff hq 0 1) (component_diff hq 1 0)]

lemma actual_inverseMatrixJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (i k : A) :
    actualScalarJet (fun y => inverse (q y) i k) x = inverseMatrixJet (matrixScalarJets q x) i k := by
  have hd : ContDiffAt ℝ 2 (fun y => determinant (q y)) x :=
    (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
  have hg : ContDiffAt ℝ 2 (fun y => 1/determinant (q y)) x := contDiffAt_const.div hd h0
  have hi (a b : A) := component_diff hq a b
  have hh : (fun y => inverse (q y) i k) =
      (fun y => (!![q y 1 1, -q y 0 1; -q y 1 0, q y 0 0] : Mat) i k * (1/determinant (q y))) := by
    funext y
    simp [inverse,div_eq_mul_inv]
  rw [hh]
  have hc : ContDiffAt ℝ 2 (fun y => (!![q y 1 1, -q y 0 1; -q y 1 0, q y 0 0] : Mat) i k) x := by
    fin_cases i <;> fin_cases k <;> dsimp <;> first | exact hi _ _ | exact (hi _ _).neg
  rw [actualScalarJet_mul hc hg,actual_reciprocal hd h0,actual_determinantJet hq]
  unfold inverseMatrixJet
  congr 1
  fin_cases i <;> fin_cases k <;> dsimp [matrixScalarJets] <;>
    first | rfl | exact actualScalarJet_neg (hi _ _)

lemma determinantJet_smooth : ContDiff ℝ ∞ determinantJet := by
  unfold determinantJet
  exact (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixScalarJet => (q 0 0,q 1 1)))).sub
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixScalarJet => (q 0 1,q 1 0))))

lemma inverseMatrixJet_smooth {q : MatrixScalarJet}
    (h0 : determinant (fun i k => (q i k).1) ≠ 0) (i k : A) :
    ContDiffAt ℝ ∞ (fun p : MatrixScalarJet => inverseMatrixJet p i k) q := by
  have hc : ContDiffAt ℝ ∞ (fun p : MatrixScalarJet =>
      (!![p 1 1, -p 0 1; -p 1 0, p 0 0] : MatrixScalarJet) i k) q := by
    fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  exact productJet_smooth.contDiffAt.comp q
    (hc.prodMk ((reciprocalJet_smooth h0).comp q determinantJet_smooth.contDiffAt))

lemma actualThreeJet_sum {α : Type*} (s : Finset α) {f : α → Point → ℝ} {x : Point}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 3 (f i) x) :
    actualThreeJet (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, actualThreeJet (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change actualThreeJet (fun _ => 0) x = constantThreeJet 0
    exact actualThreeJet_const 0 x
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [actualThreeJet_add (hf a (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma actual_determinantThreeJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 3 q x) :
    actualThreeJet (fun y => determinant (q y)) x = determinantThreeJet (matrixThreeJets q x) := by
  unfold determinant determinantThreeJet matrixThreeJets
  rw [actualThreeJet_sub ((component_three hq 0 0).mul (component_three hq 1 1))
    ((component_three hq 0 1).mul (component_three hq 1 0)),
    actualThreeJet_mul (component_three hq 0 0) (component_three hq 1 1),
    actualThreeJet_mul (component_three hq 0 1) (component_three hq 1 0)]

lemma actual_inverseMatrixThreeJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 3 q x)
    (h0 : determinant (q x) ≠ 0) (i k : A) :
    actualThreeJet (fun y => inverse (q y) i k) x = inverseMatrixThreeJet (matrixThreeJets q x) i k := by
  have hd : ContDiffAt ℝ 3 (fun y => determinant (q y)) x :=
    (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt.comp x hq
  have hg : ContDiffAt ℝ 3 (fun y => 1/determinant (q y)) x := contDiffAt_const.div hd h0
  have hi (a b : A) := component_three hq a b
  have hh : (fun y => inverse (q y) i k) =
      (fun y => (!![q y 1 1, -q y 0 1; -q y 1 0, q y 0 0] : Mat) i k * (1/determinant (q y))) := by
    funext y
    simp [inverse,div_eq_mul_inv]
  rw [hh]
  have hc : ContDiffAt ℝ 3 (fun y => (!![q y 1 1, -q y 0 1; -q y 1 0, q y 0 0] : Mat) i k) x := by
    fin_cases i <;> fin_cases k <;> dsimp <;> first | exact hi _ _ | exact (hi _ _).neg
  rw [actualThreeJet_mul hc hg,actualThreeJet_reciprocal hd h0,actual_determinantThreeJet hq]
  unfold inverseMatrixThreeJet
  congr 1
  fin_cases i <;> fin_cases k <;> dsimp [matrixThreeJets] <;>
    first | rfl | exact actualThreeJet_neg (hi _ _)

lemma determinantThreeJet_smooth : ContDiff ℝ ∞ determinantThreeJet := by
  unfold determinantThreeJet
  exact (productThreeJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixThreeJet => (q 0 0,q 1 1)))).sub
    (productThreeJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixThreeJet => (q 0 1,q 1 0))))

lemma inverseMatrixThreeJet_smooth {q : MatrixThreeJet}
    (h0 : determinant (fun i k => (q i k).1.1) ≠ 0) (i k : A) :
    ContDiffAt ℝ ∞ (fun p : MatrixThreeJet => inverseMatrixThreeJet p i k) q := by
  have hc : ContDiffAt ℝ ∞ (fun p : MatrixThreeJet =>
      (!![p 1 1, -p 0 1; -p 1 0, p 0 0] : MatrixThreeJet) i k) q := by
    fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  exact productThreeJet_smooth.contDiffAt.comp q
    (hc.prodMk ((reciprocalThreeJet_smooth h0).comp q determinantThreeJet_smooth.contDiffAt))

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_pos (n : ℝ) (x : Point) : 0 < radiusPower n x := Real.exp_pos _
lemma radiusPower_smooth (n : ℝ) : ContDiff ℝ ∞ (radiusPower n) := by unfold radiusPower; fun_prop
lemma radiusPower_diff (n : ℝ) (m : ℕ) (x : Point) : ContDiffAt ℝ m (radiusPower n) x :=
  ((radiusPower_smooth n).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt
lemma basis_rad_abs (a : I) : |basis a 0| ≤ 1 := by
  simp only [basis,Pi.single_apply]
  split_ifs <;> norm_num
lemma D_radiusPower (n : ℝ) (a : I) :
    D (basis a) (radiusPower n) = fun x => (n*basis a 0)*radiusPower n x := by
  funext x
  have hc : DifferentiableAt ℝ (fun y : Point => y 0) x := by fun_prop
  unfold radiusPower
  rw [D_comp_real (basis a) (Real.differentiableAt_exp) (hc.const_mul n),
    Real.deriv_exp,D_const_mul (basis a) n hc]
  change Real.exp (n*x 0) * (n*D (basis a) (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ) x) = _
  rw [D_clm]
  simp only [ContinuousLinearMap.proj_apply]
  ring

lemma actual_radiusPower (n : ℝ) (x : Point) :
    actualScalarJet (radiusPower n) x =
    (radiusPower n x, (fun a => (n*basis a 0)*radiusPower n x),
      fun a b => (n*basis b 0)*((n*basis a 0)*radiusPower n x)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a
    exact congrFun (D_radiusPower n a) x
  · funext a b
    change D (basis a) (D (basis b) (radiusPower n)) x = _
    rw [D_radiusPower,D_const_mul (basis a) _ ((radiusPower_diff n 2 x).differentiableAt (by norm_num)),D_radiusPower]

lemma radiusPower_two_norm (n : ℝ) (x : Point) :
    ‖actualScalarJet (radiusPower n) x‖ ≤ (max 1 |n|)^2*radiusPower n x := by
  let N : ℝ := max 1 |n|
  have hN : 1 ≤ N := le_max_left _ _
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hn : |n| ≤ N := le_max_right _ _
  have hR : 0 ≤ radiusPower n x := (radiusPower_pos n x).le
  have hc (a : I) : |n*basis a 0| ≤ N := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (basis_rad_abs a) (abs_nonneg n)).trans (by simpa using hn)
  have hN2 : N ≤ N^2 := by nlinarith
  rw [actual_radiusPower]
  apply norm_prod_le_iff.mpr
  constructor
  · change |radiusPower n x| ≤ _
    rw [abs_of_nonneg hR]
    nlinarith [mul_nonneg (sq_nonneg N) hR]
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_right ((hc a).trans hN2) hR
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro b
    rw [Real.norm_eq_abs,abs_mul,abs_mul (n*basis a 0),abs_of_nonneg hR]
    calc
      _ ≤ N*(N*radiusPower n x) := mul_le_mul (hc b) (mul_le_mul_of_nonneg_right (hc a) hR) (by positivity) hN0
      _ = N^2*radiusPower n x := by ring

lemma radiusPower_three_norm (n : ℝ) (x : Point) :
    ‖actualThreeJet (radiusPower n) x‖ ≤ (max 1 |n|)^3*radiusPower n x := by
  let N : ℝ := max 1 |n|
  have hN : 1 ≤ N := le_max_left _ _
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hR : 0 ≤ radiusPower n x := (radiusPower_pos n x).le
  have hn : |n| ≤ N := le_max_right _ _
  have hN23 : N^2 ≤ N^3 := by nlinarith [sq_nonneg (N-1)]
  apply norm_prod_le_iff.mpr
  constructor
  · exact (radiusPower_two_norm n x).trans (mul_le_mul_of_nonneg_right hN23 hR)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  change ‖actualScalarJet (D (basis a) (radiusPower n)) x‖ ≤ _
  rw [D_radiusPower,actualScalarJet_smul _ (radiusPower_diff n 2 x),norm_smul,Real.norm_eq_abs]
  have hc : |n*basis a 0| ≤ N := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (basis_rad_abs a) (abs_nonneg n)).trans (by simpa using hn)
  calc
    _ ≤ N*(N^2*radiusPower n x) := mul_le_mul hc (radiusPower_two_norm n x) (norm_nonneg _) hN0
    _ = N^3*radiusPower n x := by ring

lemma inverse_radius_three_norm (x : Point) :
    ‖actualThreeJet (radiusPower (-1)) x‖ ≤ 1/Real.exp (x 0) := by
  simpa only [abs_neg,abs_one,max_self,one_pow,one_mul,radiusPower,neg_one_mul,Real.exp_neg,one_div]
    using radiusPower_three_norm (-1) x

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma scalarJet_norm_components {u : ScalarJet} {B : ℝ} (h : ‖u‖ ≤ B) :
    |u.1| ≤ B ∧ (∀ a, |u.2.1 a| ≤ B) ∧ (∀ a b, |u.2.2 a b| ≤ B) := by
  obtain ⟨h0,h12⟩ := norm_prod_le_iff.mp h
  obtain ⟨h1,h2⟩ := norm_prod_le_iff.mp h12
  refine ⟨h0,?_,?_⟩
  · intro a; exact (norm_le_pi_norm _ a).trans h1
  · intro a b; exact (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans h2)

lemma scalarJet_norm_of_components {u : ScalarJet} {B : ℝ} (hB : 0 ≤ B)
    (h0 : |u.1| ≤ B) (h1 : ∀ a, |u.2.1 a| ≤ B) (h2 : ∀ a b, |u.2.2 a b| ≤ B) :
    ‖u‖ ≤ B := by
  exact norm_prod_le_iff.mpr ⟨h0,norm_prod_le_iff.mpr
    ⟨(pi_norm_le_iff_of_nonneg hB).mpr h1,(pi_norm_le_iff_of_nonneg hB).mpr
    (fun a => (pi_norm_le_iff_of_nonneg hB).mpr (h2 a))⟩⟩

lemma productJet_norm {u v : ScalarJet} {U V : ℝ}
    (hU : ‖u‖ ≤ U) (hV : ‖v‖ ≤ V) : ‖productJet u v‖ ≤ 4*U*V := by
  have hU0 := (norm_nonneg u).trans hU
  have hV0 := (norm_nonneg v).trans hV
  obtain ⟨hu0,hu1,hu2⟩ := scalarJet_norm_components hU
  obtain ⟨hv0,hv1,hv2⟩ := scalarJet_norm_components hV
  have hb {a b : ℝ} (ha : |a| ≤ U) (hb : |b| ≤ V) : |a*b| ≤ U*V := by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hU0
  have hUV : 0 ≤ U*V := mul_nonneg hU0 hV0
  apply scalarJet_norm_of_components (by positivity)
  · exact (hb hu0 hv0).trans (by nlinarith)
  · intro a
    change |u.1*v.2.1 a+v.1*u.2.1 a| ≤ _
    have hs := abs_add_le (u.1*v.2.1 a) (v.1*u.2.1 a)
    have h := hb (hu1 a) hv0
    rw [mul_comm (u.2.1 a)] at h
    linarith [hb hu0 (hv1 a)]
  · intro a b
    change |u.1*v.2.2 a b+v.1*u.2.2 a b+u.2.1 a*v.2.1 b+v.2.1 a*u.2.1 b| ≤ _
    have h := hb (hu2 a b) hv0
    rw [mul_comm (u.2.2 a b)] at h
    have hh := hb (hu1 b) (hv1 a)
    rw [mul_comm (u.2.1 b)] at hh
    calc
      _ ≤ |u.1*v.2.2 a b|+|v.1*u.2.2 a b|+|u.2.1 a*v.2.1 b|+|v.2.1 a*u.2.1 b| := by
        exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ U*V+U*V+U*V+U*V := add_le_add (add_le_add (add_le_add (hb hu0 (hv2 a b)) h) (hb (hu1 a) (hv1 b))) hh
      _ = 4*U*V := by ring

lemma productThreeJet_norm {u v : ScalarThreeJet} {U V : ℝ}
    (hU : ‖u‖ ≤ U) (hV : ‖v‖ ≤ V) : ‖productThreeJet u v‖ ≤ 8*U*V := by
  have hU0 := (norm_nonneg u).trans hU
  have hV0 := (norm_nonneg v).trans hV
  obtain ⟨hu0,hu1⟩ := norm_prod_le_iff.mp hU
  obtain ⟨hv0,hv1⟩ := norm_prod_le_iff.mp hV
  apply norm_prod_le_iff.mpr
  constructor
  · exact (productJet_norm hu0 hv0).trans (by nlinarith [mul_nonneg hU0 hV0])
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    have hua : ‖u.2 a‖ ≤ U := (norm_le_pi_norm _ a).trans hu1
    have hva : ‖v.2 a‖ ≤ V := (norm_le_pi_norm _ a).trans hv1
    calc
      _ ≤ ‖productJet u.1 (v.2 a)‖+‖productJet v.1 (u.2 a)‖ := norm_add_le _ _
      _ ≤ 4*U*V+4*V*U := add_le_add (productJet_norm hu0 hva) (productJet_norm hv0 hua)
      _ = 8*U*V := by ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma productJet_smul_right (c : ℝ) (f g : ScalarJet) : productJet f (c • g) = c • productJet f g := by
  apply Prod.ext
  · change f.1*(c*g.1) = c*(f.1*g.1)
    ring
  apply Prod.ext
  · funext a
    change f.1*(c*g.2.1 a)+(c*g.1)*f.2.1 a = c*(f.1*g.2.1 a+g.1*f.2.1 a)
    ring
  · funext a b
    change f.1*(c*g.2.2 a b)+(c*g.1)*f.2.2 a b+f.2.1 a*(c*g.2.1 b)+(c*g.2.1 a)*f.2.1 b = c*(f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)
    ring

lemma productJet_sub_right (f g h : ScalarJet) : productJet f (g-h) = productJet f g-productJet f h := by
  apply Prod.ext
  · change f.1*(g.1-h.1) = (f.1*g.1)-(f.1*h.1)
    ring
  apply Prod.ext
  · funext a
    change f.1*(g.2.1 a-h.2.1 a)+(g.1-h.1)*f.2.1 a = (f.1*g.2.1 a+g.1*f.2.1 a)-(f.1*h.2.1 a+h.1*f.2.1 a)
    ring
  · funext a b
    change f.1*(g.2.2 a b-h.2.2 a b)+(g.1-h.1)*f.2.2 a b+f.2.1 a*(g.2.1 b-h.2.1 b)+(g.2.1 a-h.2.1 a)*f.2.1 b = (f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)-(f.1*h.2.2 a b+h.1*f.2.2 a b+f.2.1 a*h.2.1 b+h.2.1 a*f.2.1 b)
    ring
lemma productJet_constant_right (f : ScalarJet) (c : ℝ) : productJet f (constantJet c) = c • f := by
  ext a b <;> simp [productJet,constantJet,mul_comm]
lemma productJet_constant_left (f : ScalarJet) (c : ℝ) : productJet (constantJet c) f = c • f := by
  ext a b <;> simp [productJet,constantJet]

lemma reciprocalJet_one : reciprocalJet (constantJet 1) = constantJet 1 := by
  ext a b <;> simp [reciprocalJet,constantJet]

lemma powJet_fst (j : ScalarJet) (n : ℕ) : (powJet j n).1 = j.1^n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [powJet,productJet,pow_succ] using congrArg (fun x : ℝ => x*j.1) ih

lemma actualScalarJet_pow {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) (n : ℕ) :
    actualScalarJet (fun y => f y^n) x = powJet (actualScalarJet f x) n := by
  induction n with
  | zero => exact actualScalarJet_const 1 x
  | succ n ih => simp only [pow_succ,powJet,actualScalarJet_mul (hf.pow n) hf,ih]
lemma actualThreeJet_pow {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 3 f x) (n : ℕ) :
    actualThreeJet (fun y => f y^n) x = powThreeJet (actualThreeJet f x) n := by
  induction n with
  | zero => exact actualThreeJet_const 1 x
  | succ n ih => simp only [pow_succ,powThreeJet,actualThreeJet_mul (hf.pow n) hf,ih]


lemma massNumeratorJet_smooth : ContDiff ℝ ∞
    (fun j : ScalarJet × ScalarJet × ScalarJet × ScalarJet => massNumeratorJet j.1 j.2.1 j.2.2.1 j.2.2.2) := by
  unfold massNumeratorJet
  fun_prop
lemma normalizedMassJet_smooth {j : ScalarJet × ScalarJet × ScalarJet × ScalarJet}
    (h0 : (constantJet 1+productJet (powJet j.1 3) j.2.2.2).1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun k : ScalarJet × ScalarJet × ScalarJet × ScalarJet =>
      normalizedMassJet k.1 k.2.1 k.2.2.1 k.2.2.2) j := by
  have hi := (reciprocalJet_smooth h0).comp j
    (by fun_prop : ContDiffAt ℝ ∞ (fun k : ScalarJet × ScalarJet × ScalarJet × ScalarJet =>
      constantJet 1+productJet (powJet k.1 3) k.2.2.2) j)
  exact (productJet_smooth.contDiffAt.comp j (massNumeratorJet_smooth.contDiffAt.prodMk hi)).const_smul _
lemma normalizedMassJet_zero (D T V : ScalarJet) :
    normalizedMassJet 0 D T V = (1/2:ℝ) • (V+(2:ℝ) • T-(2:ℝ) • D) := by
  simp [normalizedMassJet,massNumeratorJet,productJet_constant_left,productJet_constant_right,reciprocalJet_one]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProductJet_sub (q p s : MatrixScalarJet) :
    traceProductJet q (p-s) = traceProductJet q p-traceProductJet q s := by
  simp [traceProductJet,productJet_sub_right,Finset.sum_sub_distrib]
lemma traceProductJet_smul (c : ℝ) (q p : MatrixScalarJet) :
    traceProductJet q (c • p) = c • traceProductJet q p := by
  simp [traceProductJet,productJet_smul_right]

lemma cksMassJet_zero (j : MassInput) : cksMassJet 0 j = leadingMassJet j := by
  simp only [cksMassJet,normalizedMassJet_zero,coefficientD,coefficientT,coefficientV,
    coefficientMetric_zero,Prod.fst_zero,mulMatrixJet_zero,powJet_zero_succ,
    productJet_zero_left,add_zero,sub_zero,leadingMassJet]
  erw [traceProductJet_sub,traceProductJet_smul]
  module

lemma traceProductJet_smooth : ContDiff ℝ ∞
    (fun j : MatrixScalarJet × MatrixScalarJet => traceProductJet j.1 j.2) := by
  unfold traceProductJet
  fun_prop


lemma coefficientMetric_smooth : ContDiff ℝ ∞ (fun p : MassParameter => coefficientMetric p.1 p.2) := by
  unfold coefficientMetric
  fun_prop
attribute [local irreducible] coefficientMetric

lemma coefficientShift_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientShift t.1 t.2) p := by
  unfold coefficientShift
  apply contDiffAt_pi.mpr
  intro a
  apply ContDiffAt.sum
  intro b _
  apply productThreeJet_contDiffAt
  · exact (inverseMatrixThreeJet_smooth (q := coefficientMetric p.1 p.2) hp a b).comp p coefficientMetric_smooth.contDiffAt
  · fun_prop
attribute [local irreducible] coefficientShift

lemma lieJet_smooth : ContDiff ℝ ∞ (fun p : MatrixThreeJet × (A → ScalarThreeJet) => lieJet p.1 p.2) := by
  unfold lieJet
  fun_prop
attribute [local irreducible] lieJet
lemma coefficientLie_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientLie t.1 t.2) p := by
  unfold coefficientLie
  exact lieJet_smooth.contDiffAt.comp p
    (coefficientMetric_smooth.contDiffAt.prodMk (coefficientShift_smooth (p := p) hp))
attribute [local irreducible] coefficientLie
lemma coefficientInverse_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => inverseMatrixJet (lowerMatrixJet (coefficientMetric t.1 t.2))) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact (inverseMatrixJet_smooth (q := lowerMatrixJet (coefficientMetric p.1 p.2)) hp i k).comp p
    (lowerMatrixJet_smooth.contDiffAt.comp p coefficientMetric_smooth.contDiffAt)
lemma coefficientD_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientD t.1 t.2) p := by
  have hl := coefficientLie_smooth (p := p) hp
  have hlower (order : Fin 3) : ContDiffAt ℝ ∞
      (fun t : MassParameter => lowerMatrixJet (t.2.1 order)) p := by
    fun_prop
  have harg : ContDiffAt ℝ ∞ (fun t : MassParameter =>
      (-3:ℝ) • lowerMatrixJet (t.2.1 1)+mulMatrixJet t.1.1
        (t.2.2.1 0-(2:ℝ) • lowerMatrixJet (t.2.1 2)-coefficientLie t.1 t.2)) p := by
    apply ContDiffAt.add
    · exact (contDiffAt_const (c := (-3 : ℝ))).smul (hlower 1)
    · apply mulMatrixJet_contDiffAt
      · fun_prop
      · exact ((by fun_prop : ContDiffAt ℝ ∞ (fun t : MassParameter => t.2.2.1 0) p).sub
          ((contDiffAt_const (c := (2 : ℝ))).smul (hlower 2))).sub hl
  unfold coefficientD
  exact (traceProductJet_smooth.contDiffAt.comp p
    ((coefficientInverse_smooth (p := p) hp).prodMk harg)).const_smul _
attribute [local irreducible] coefficientD
lemma coefficientT_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientT t.1 t.2) p := by
  have harg : ContDiff ℝ ∞ (fun t : MassParameter =>
      t.2.2.1 1-lowerMatrixJet (t.2.1 1)+mulMatrixJet t.1.1
        (t.2.2.1 2-lowerMatrixJet (t.2.1 2))) := by fun_prop
  unfold coefficientT
  exact (traceProductJet_smooth.contDiffAt.comp p
    ((coefficientInverse_smooth (p := p) hp).prodMk harg.contDiffAt)).const_smul _
attribute [local irreducible] coefficientT
lemma coefficientBB_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientBB t.1 t.2) p := by
  unfold coefficientBB
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro k _
  apply productJet_contDiffAt
  · exact contDiffAt_pi.mp (contDiffAt_pi.mp (coefficientInverse_smooth (p := p) hp) i) k
  · fun_prop
attribute [local irreducible] coefficientBB
lemma coefficientV_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => coefficientV t.1 t.2) p := by
  have hbb := coefficientBB_smooth (p := p) hp
  unfold coefficientV
  fun_prop
attribute [local irreducible] coefficientV
lemma cksMassJet_smooth {p : MassParameter}
    (hp : determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0)
    (hv : (constantJet 1+productJet (powJet p.1.1 3) (coefficientV p.1 p.2)).1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : MassParameter => cksMassJet t.1 t.2) p := by
  have hz : ContDiffAt ℝ ∞ (fun t : MassParameter => t.1.1) p := by fun_prop
  have hinner := hz.prodMk ((coefficientD_smooth (p := p) hp).prodMk
    ((coefficientT_smooth (p := p) hp).prodMk (coefficientV_smooth (p := p) hp)))
  have hh := (normalizedMassJet_smooth
    (j := (p.1.1,coefficientD p.1 p.2,coefficientT p.1 p.2,coefficientV p.1 p.2)) hv).comp p hinner
  exact hh

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def traceProduct (q p : Mat) : ℝ := ∑ i, ∑ k, q i k*p k i

theorem physical_mass_normalized {r D T V : ℝ} (hr : r ≠ 0)
    (h0 : 1+(1/r)^3*V ≠ 0) :
    r/2*(1+(r*(1+(1/r)^3*T))^2-
      (1+r^2)/(1+(1/r)^3*V)*(1+(1/r)^3*D)^2) =
      (1/2:ℝ)*(((1+(1/r)^2)*V+2*T-(2*(1+(1/r)^2))*D+
        (1/r)^3*(T*T+2*(T*V)-(1+(1/r)^2)*(D*D))+(1/r)^6*((T*T)*V))*
          (1+(1/r)^3*V)⁻¹) := by
  have hh := exact_mass_cancellation (D := D) (T := T) (V := V) (one_div_ne_zero hr) h0
  convert! hh using 1 <;> field_simp
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def massMetricRegion : Set (MassParameter) :=
  {p | determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0}

def massDenominator (p : MassParameter) : ℝ :=
  (constantJet 1+productJet (powJet p.1.1 3) (coefficientV p.1 p.2)).1

def massRegion : Set (MassParameter) := massMetricRegion ∩ massDenominator ⁻¹' ({0}ᶜ)

lemma massMetricRegion_open : IsOpen massMetricRegion := by
  have hf : Continuous (fun q : MatrixThreeJet => determinant (fun i k => (q i k).1.1)) :=
    determinant_smooth.continuous.comp (by fun_prop)
  exact isOpen_ne_fun (hf.comp coefficientMetric_smooth.continuous) continuous_const

lemma massDenominator_continuousOn : ContinuousOn massDenominator massMetricRegion := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hV := (coefficientV_smooth hp).continuousAt
  unfold massDenominator
  have hp : ContinuousAt (fun t : MassParameter => powJet t.1.1 3) p :=
    (powJet_smooth 3).continuous.continuousAt.comp ((continuousAt_fst).fst)
  exact (continuousAt_const.add (productJet_smooth.continuous.continuousAt.comp (hp.prodMk hV))).fst

lemma massRegion_open : IsOpen massRegion :=
  massDenominator_continuousOn.isOpen_inter_preimage massMetricRegion_open isOpen_compl_singleton

lemma massRegion_zero {j : MassInput}
    (hj : determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) : (0,j) ∈ massRegion := by
  refine ⟨?_,?_⟩
  · simpa [massMetricRegion,coefficientMetric_zero] using hj
  · simp [massDenominator,constantJet]

lemma massRegion_locallyLipschitz : LocallyLipschitzOn massRegion
    (fun p : MassParameter => cksMassJet p.1 p.2) := by
  intro p hp
  have hdiff := (cksMassJet_smooth hp.1 hp.2).of_le (by simp : (1:ℕ∞ω) ≤ ∞)
  obtain ⟨C,u,hu,hC⟩ := hdiff.exists_lipschitzOnWith
  exact ⟨C,u,mem_nhdsWithin_of_mem_nhds hu,hC⟩

lemma mass_uniform_lipschitz {K : Set MassInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0, LipschitzOnWith C
      (fun p : MassParameter => cksMassJet p.1 p.2)
      (Metric.cthickening δ ((fun j : MassInput => ((0:ScalarThreeJet),j)) '' K)) := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : ProperSpace (MassParameter) := FiniteDimensional.proper ℝ (MassParameter)
  let K₀ : Set (MassParameter) := (fun j : MassInput => ((0:ScalarThreeJet),j)) '' K
  have hK₀ : IsCompact K₀ := hK.image (by fun_prop)
  have hsub : K₀ ⊆ massRegion := by
    rintro p ⟨j,hj,rfl⟩
    exact massRegion_zero (hreg j hj)
  obtain ⟨δ,hδ,hδsub⟩ := hK₀.exists_cthickening_subset_open massRegion_open hsub
  exact ⟨δ,hδ,(massRegion_locallyLipschitz.mono hδsub).exists_lipschitzOnWith_of_compact
    (hK₀.cthickening (r := δ))⟩

lemma parameter_lipschitz_zero_estimate {Z E F : Type*} [NormedAddCommGroup Z]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : Z × E → F} {K : Set E} {δ : ℝ} {C : ℝ≥0}
    (hC : LipschitzOnWith C f (Metric.cthickening δ ((fun j : E => ((0:Z),j)) '' K)))
    {z : Z} {j : E} (hj : j ∈ K) (hz : ‖z‖ ≤ δ) :
    ‖f (z,j)-f (0,j)‖ ≤ (C:ℝ)*‖z‖ := by
  let K₀ : Set (Z × E) := (fun j : E => ((0:Z),j)) '' K
  have hj₀ : (0,j) ∈ K₀ := ⟨j,hj,rfl⟩
  have hzero : ((0:Z),j) ∈ Metric.cthickening δ K₀ := (Metric.self_subset_cthickening K₀) hj₀
  have hzj : (z,j) ∈ Metric.cthickening δ K₀ := by
    apply Metric.mem_cthickening_of_dist_le (z,j) (0,j) δ K₀ hj₀
    simpa only [Prod.dist_eq,dist_zero_right,dist_self,max_eq_left (norm_nonneg z)] using hz
  have hh := hC.norm_sub_le hzj hzero
  have heq : ‖(z,j)-((0:Z),j)‖ = ‖z‖ := by
    change max ‖z-0‖ ‖j-j‖ = ‖z‖
    rw [sub_zero,sub_self,norm_zero,max_eq_left (norm_nonneg z)]
  rwa [heq] at hh

attribute [local irreducible] cksMassJet leadingMassJet

theorem cks_mass_uniform {K : Set MassInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ScalarThreeJet, ∀ j ∈ K, ‖z‖ ≤ δ →
      ‖cksMassJet z j-leadingMassJet j‖ ≤ C*‖z‖ := by
  obtain ⟨δ,hδ,C,hC⟩ := mass_uniform_lipschitz hK hreg
  refine ⟨δ,hδ,C,C.coe_nonneg,?_⟩
  intro z j hj hz
  have hh : ‖cksMassJet z j-cksMassJet 0 j‖ ≤ (C:ℝ)*‖z‖ :=
    parameter_lipschitz_zero_estimate (E := MassInput) (F := ScalarJet)
      (f := fun p : MassParameter => cksMassJet p.1 p.2) (K := K) (δ := δ) (C := C)
      (z := z) (j := j) hC hj hz
  exact (congrArg (fun v : ScalarJet => ‖cksMassJet z j-v‖) (cksMassJet_zero j).symm).trans_le hh

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_diff {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    ContDiffAt ℝ 2 (fun y => traceProduct (q y) (p y)) x := by
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hq i k).mul (component_diff hp k i)

lemma actual_traceProductJet {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    actualScalarJet (fun y => traceProduct (q y) (p y)) x =
      traceProductJet (matrixScalarJets q x) (matrixScalarJets p x) := by
  unfold traceProduct traceProductJet
  rw [actualScalarJet_sum _ (fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hq i k).mul (component_diff hp k i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [actualScalarJet_sum _ (fun k _ => (component_diff hq i k).mul (component_diff hp k i))]
  apply Finset.sum_congr rfl
  intro k _
  exact actualScalarJet_mul (component_diff hq i k) (component_diff hp k i)

lemma inverse_diff_at {n : ℕ} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ n (fun y => inverse (q y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> first
      | exact contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
      | exact (contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _).neg
  · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt.comp x hq
  · exact h0

lemma actual_inverseJets {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (h0 : determinant (q x) ≠ 0) :
    matrixScalarJets (fun y => inverse (q y)) x = inverseMatrixJet (matrixScalarJets q x) := by
  funext i k
  exact actual_inverseMatrixJet hq h0 i k

def massNumeratorField (z D T V : Point → ℝ) : Point → ℝ := fun y =>
  (1+z y^2)*V y+2*T y-2*((1+z y^2)*D y)+
    z y^3*(T y*T y+2*(T y*V y)-(1+z y^2)*(D y*D y))+
    z y^6*((T y*T y)*V y)

def normalizedMassField (z D T V : Point → ℝ) : Point → ℝ := fun y =>
  (1/2:ℝ)*(massNumeratorField z D T V y*(1+z y^3*V y)⁻¹)

lemma massNumeratorField_diff {z D T V : Point → ℝ} {x : Point}
    (hz : ContDiffAt ℝ 2 z x) (hD : ContDiffAt ℝ 2 D x) (hT : ContDiffAt ℝ 2 T x) (hV : ContDiffAt ℝ 2 V x) :
    ContDiffAt ℝ 2 (massNumeratorField z D T V) x := by
  unfold massNumeratorField
  fun_prop

lemma actual_massNumeratorJet {z D T V : Point → ℝ} {x : Point}
    (hz : ContDiffAt ℝ 2 z x) (hD : ContDiffAt ℝ 2 D x) (hT : ContDiffAt ℝ 2 T x) (hV : ContDiffAt ℝ 2 V x) :
    actualScalarJet (massNumeratorField z D T V) x =
      massNumeratorJet (actualScalarJet z x) (actualScalarJet D x) (actualScalarJet T x) (actualScalarJet V x) := by
  unfold massNumeratorField massNumeratorJet
  simp (disch := fun_prop) only [actualScalarJet_add,actualScalarJet_sub,actualScalarJet_smul,
    actualScalarJet_mul,actualScalarJet_pow,actualScalarJet_const]

lemma actual_normalizedMassJet {z D T V : Point → ℝ} {x : Point}
    (hz : ContDiffAt ℝ 2 z x) (hD : ContDiffAt ℝ 2 D x) (hT : ContDiffAt ℝ 2 T x) (hV : ContDiffAt ℝ 2 V x)
    (h0 : 1+z x^3*V x ≠ 0) :
    actualScalarJet (normalizedMassField z D T V) x =
      normalizedMassJet (actualScalarJet z x) (actualScalarJet D x) (actualScalarJet T x) (actualScalarJet V x) := by
  have hm : ContDiffAt ℝ 2 (fun y => z y^3*V y) x := by fun_prop
  have hd : ContDiffAt ℝ 2 (fun y => 1+z y^3*V y) x := by fun_prop
  have hi : ContDiffAt ℝ 2 (fun y => (1+z y^3*V y)⁻¹) x := hd.inv h0
  have hrec : actualScalarJet (fun y => (1+z y^3*V y)⁻¹) x =
      reciprocalJet (actualScalarJet (fun y => 1+z y^3*V y) x) := by
    simpa only [one_div] using actual_reciprocal hd h0
  unfold normalizedMassField normalizedMassJet
  rw [actualScalarJet_smul (1/2:ℝ) ((massNumeratorField_diff hz hD hT hV).mul hi),
    actualScalarJet_mul (massNumeratorField_diff hz hD hT hV) hi,
    actual_massNumeratorJet hz hD hT hV,hrec,
    actualScalarJet_add (f := fun _ : Point => (1:ℝ)) contDiffAt_const hm,
    actualScalarJet_const,actualScalarJet_mul (hz.pow 3) hV,actualScalarJet_pow hz]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixThreeJets_add {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hp : ContDiffAt ℝ 3 p x) :
    matrixThreeJets (fun y => q y+p y) x = matrixThreeJets q x+matrixThreeJets p x := by
  funext i k
  exact actualThreeJet_add (component_three hq i k) (component_three hp i k)
lemma matrixThreeJets_mul {f : Point → ℝ} {q : Point → Mat} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hq : ContDiffAt ℝ 3 q x) :
    matrixThreeJets (fun y => f y • q y) x = mulMatrixThreeJet (actualThreeJet f x) (matrixThreeJets q x) := by
  funext i k
  exact actualThreeJet_mul hf (component_three hq i k)
lemma matrixScalarJets_smul (c : ℝ) {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) :
    matrixScalarJets (fun y => c • q y) x = c • matrixScalarJets q x := by
  funext i k
  exact actualScalarJet_smul c (component_diff hq i k)
lemma matrixScalarJets_add {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => q y+p y) x = matrixScalarJets q x+matrixScalarJets p x := by
  funext i k
  exact actualScalarJet_add (component_diff hq i k) (component_diff hp i k)
lemma matrixScalarJets_sub {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => q y-p y) x = matrixScalarJets q x-matrixScalarJets p x := by
  funext i k
  exact actualScalarJet_sub (component_diff hq i k) (component_diff hp i k)
lemma matrixScalarJets_mul {f : Point → ℝ} {q : Point → Mat} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hq : ContDiffAt ℝ 2 q x) :
    matrixScalarJets (fun y => f y • q y) x = mulMatrixJet (actualScalarJet f x) (matrixScalarJets q x) := by
  funext i k
  exact actualScalarJet_mul hf (component_diff hq i k)

lemma normalizedLie_diff {q : Point → Mat} {S : Point → A → ℝ} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : A) :
    ContDiffAt ℝ 2 (fun y => normalizedLie q S y i k) x := by
  have hSa (a : A) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  apply ContDiffAt.sum
  intro a ha
  exact ((((hSa a).of_le h23).mul (contDiffAt_D (hqa i k) (by norm_num) (basis a.succ))).add
      (((hqa a k).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis i.succ)))).add
      (((hqa i a).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis k.succ)))

lemma actual_normalizedLieJet {q : Point → Mat} {S : Point → A → ℝ} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : A) :
    actualScalarJet (fun y => normalizedLie q S y i k) x =
      lieJet (matrixThreeJets q x) (fun a => actualThreeJet (fun y => S y a) x) i k := by
  have hSa (a : A) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  have hdS (a b : A) : ContDiffAt ℝ 2 (D (basis a.succ) (fun y => S y b)) x :=
    contDiffAt_D (hSa b) (by norm_num) (basis a.succ)
  have hdq (a i k : A) : ContDiffAt ℝ 2 (D (basis a.succ) (fun y => q y i k)) x :=
    contDiffAt_D (hqa i k) (by norm_num) (basis a.succ)
  have hterm (a : A) : ContDiffAt ℝ 2 (fun y =>
      S y a*D (basis a.succ) (fun z => q z i k) y+
      q y a k*D (basis i.succ) (fun z => S z a) y+q y i a*D (basis k.succ) (fun z => S z a) y) x :=
    ((((hSa a).of_le h23).mul (hdq a i k)).add
      (((hqa a k).of_le h23).mul (hdS i a))).add
      (((hqa i a).of_le h23).mul (hdS k a))
  unfold normalizedLie lieJet
  rw [actualScalarJet_sum _ (fun a _ => hterm a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [actualScalarJet_add ((((hSa a).of_le h23).mul (hdq a i k)).add
      (((hqa a k).of_le h23).mul (hdS i a))) (((hqa i a).of_le h23).mul (hdS k a)),
    actualScalarJet_add (((hSa a).of_le h23).mul (hdq a i k)) (((hqa a k).of_le h23).mul (hdS i a)),
    actualScalarJet_mul ((hSa a).of_le h23) (hdq a i k),
    actualScalarJet_mul ((hqa a k).of_le h23) (hdS i a),
    actualScalarJet_mul ((hqa i a).of_le h23) (hdS k a)]
  rfl

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def tensorBase (p : TensorParameter) : MassParameter := (p.1,p.2.1)

def tensorCoefficients (p : TensorParameter) : ScalarJet × (A → ScalarJet) × MatrixScalarJet :=
  (tensorLCoeff p,tensorEtaCoeff p,tensorTauCoeff p)

def tensorRegion : Set TensorParameter :=
  {p | determinant (fun i k => (coefficientMetric p.1 p.2.1 i k).1.1) ≠ 0 ∧ 0 < (tensorDen p).1}

lemma tensorBase_smooth : ContDiff ℝ ∞ tensorBase := by unfold tensorBase; fun_prop
lemma tensorQ_smooth : ContDiff ℝ ∞ tensorQ :=
  lowerMatrixJet_smooth.comp (coefficientMetric_smooth.comp tensorBase_smooth)
lemma tensorK_smooth : ContDiff ℝ ∞ tensorK := by unfold tensorK; fun_prop
attribute [local irreducible] tensorK tensorQ
lemma tensorH_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) (a : A) :
    ContDiffAt ℝ ∞ (fun t => tensorH t a) p := by
  have hbase : determinant (fun i k => (coefficientMetric (tensorBase p).1 (tensorBase p).2 i k).1.1) ≠ 0 := by
    simpa only [tensorBase] using hp.1
  have hh := (coefficientShift_smooth hbase).comp p tensorBase_smooth.contDiffAt
  have ha := (contDiffAt_pi.mp hh a).fst
  simpa only [Function.comp_def,tensorBase,tensorH] using ha
attribute [local irreducible] tensorH
lemma tensorDen_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorDen p := by
  have hV := (coefficientV_smooth (p := (p.1,p.2.1)) hp.1).comp p tensorBase_smooth.contDiffAt
  dsimp only [Function.comp_def,tensorBase] at hV
  unfold tensorDen
  fun_prop
attribute [local irreducible] tensorDen
lemma tensorLapseSq_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorLapseSq p := by
  unfold tensorLapseSq
  exact productJet_contDiffAt (by fun_prop)
    ((reciprocalJet_smooth hp.2.ne').comp p (tensorDen_smooth hp))
attribute [local irreducible] tensorLapseSq
lemma tensorLapse_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorLapse p := by
  have hpos : 0 < (constantJet 1+powJet p.1.1 2).1 := by
    change 0 < 1+(powJet p.1.1 2).1
    rw [powJet_fst]; positivity
  have hs := (sqrtJet_smooth hp.2).comp p (tensorDen_smooth hp)
  unfold tensorLapse
  have ha : ContDiffAt ℝ ∞ (fun t : TensorParameter => constantJet 1+powJet t.1.1 2) p := by fun_prop
  have hs0 := sqrtJet_smooth (j := constantJet 1+powJet p.1.1 2) hpos
  have hs1 := hs0.comp p ha
  have hi0 := reciprocalJet_smooth (j := sqrtJet (tensorDen p)) (Real.sqrt_pos.mpr hp.2).ne'
  have hi1 := hi0.comp p hs
  exact productJet_contDiffAt hs1 hi1
attribute [local irreducible] tensorLapse
lemma tensorCross_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorCross p := by
  unfold tensorCross
  apply ContDiffAt.sum
  intro a _
  exact productJet_contDiffAt (tensorH_smooth hp a) (by fun_prop)
attribute [local irreducible] tensorCross
lemma tensorNormalQuad_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorNormalQuad p := by
  unfold tensorNormalQuad
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact productJet_contDiffAt (contDiffAt_pi.mp (contDiffAt_pi.mp tensorK_smooth.contDiffAt a) b)
    (productJet_contDiffAt (tensorH_smooth hp a) (tensorH_smooth hp b))
attribute [local irreducible] tensorNormalQuad
lemma tensorLCoeff_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorLCoeff p := by
  have hBB := (coefficientBB_smooth (p := (p.1,p.2.1)) hp.1).comp p tensorBase_smooth.contDiffAt
  dsimp only [Function.comp_def,tensorBase] at hBB
  have hC := tensorCross_smooth hp
  have hQ := tensorNormalQuad_smooth hp
  unfold tensorLCoeff
  apply productJet_contDiffAt (tensorLapseSq_smooth hp)
  fun_prop
attribute [local irreducible] tensorLCoeff
lemma tensorEtaCoeff_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorEtaCoeff p := by
  apply contDiffAt_pi.mpr
  intro a
  unfold tensorEtaCoeff
  apply productJet_contDiffAt (tensorLapse_smooth hp)
  apply ContDiffAt.sub (by fun_prop)
  apply ContDiffAt.sum
  intro b _
  exact productJet_contDiffAt (tensorH_smooth hp b)
    (contDiffAt_pi.mp (contDiffAt_pi.mp tensorK_smooth.contDiffAt b) a)
attribute [local irreducible] tensorEtaCoeff
lemma tensorTauCoeff_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorTauCoeff p := by
  have hT := (coefficientT_smooth (p := (p.1,p.2.1)) hp.1).comp p tensorBase_smooth.contDiffAt
  dsimp only [Function.comp_def,tensorBase] at hT
  have hQ := tensorQ_smooth.contDiffAt (x := p)
  unfold tensorTauCoeff
  fun_prop
attribute [local irreducible] tensorTauCoeff
lemma tensorCoefficients_smooth {p : TensorParameter} (hp : p ∈ tensorRegion) :
    ContDiffAt ℝ ∞ tensorCoefficients p :=
  (tensorLCoeff_smooth hp).prodMk ((tensorEtaCoeff_smooth hp).prodMk (tensorTauCoeff_smooth hp))

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def boundedMassFamily (K : Set MatrixThreeJet) (B : ℝ) : Set MassInput :=
  {j | j.1 0 ∈ K} ∩ Metric.closedBall 0 B

lemma boundedMassFamily_compact {K : Set MatrixThreeJet} (hK : IsCompact K) (B : ℝ) :
    IsCompact (boundedMassFamily K B) := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : ProperSpace MassInput := FiniteDimensional.proper ℝ MassInput
  exact (isCompact_closedBall (0:MassInput) B).inter_left (hK.isClosed.preimage (by fun_prop))

lemma boundedMassFamily_mem {K : Set MatrixThreeJet} {B : ℝ} {j : MassInput}
    (hj : j.1 0 ∈ K) (hB : ‖j‖ ≤ B) : j ∈ boundedMassFamily K B :=
  ⟨hj,by simpa only [Metric.mem_closedBall,dist_zero_right] using hB⟩

attribute [local irreducible] cksMassJet leadingMassJet

theorem cks_mass_uniform_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ∀ z : ScalarThreeJet, ∀ j : MassInput,
      R₀ ≤ r → ‖z‖ ≤ 1/r → j.1 0 ∈ K → ‖j‖ ≤ B →
      ‖cksMassJet z j-leadingMassJet j‖ ≤ C/r := by
  obtain ⟨δ,hδ,C,hC,hh⟩ := cks_mass_uniform (boundedMassFamily_compact hK B)
    (fun j hj => hreg _ hj.1)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,hC,?_⟩
  intro r z j hr hz hj hB
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hd : 1/r ≤ δ := by
    apply (div_le_iff₀ hr0).mpr
    simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))
  exact (hh z j (boundedMassFamily_mem hj hB) (hz.trans hd)).trans
    (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hz hC)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def massInputOf (f : MassFields) (x : Point) : MassInput :=
  (![matrixThreeJets f.sigma x,matrixThreeJets f.mg x,matrixThreeJets f.eg x],
    ![matrixScalarJets f.er x,matrixScalarJets f.mK x,matrixScalarJets f.ek x],
    (fun a => actualThreeJet (fun y => f.b y a) x),
    ![actualScalarJet f.mr x,actualScalarJet f.err x])

def cksQField (z : Point → ℝ) (f : MassFields) : Point → Mat :=
  fun y => f.sigma y+z y^3 • f.mg y+z y^4 • f.eg y

def cksHField (z : Point → ℝ) (f : MassFields) : Point → A → ℝ :=
  fun y a => ∑ b, inverse (cksQField z f y) a b*f.b y b

def cksLieField (z : Point → ℝ) (f : MassFields) : Point → Mat :=
  normalizedLie (cksQField z f) (cksHField z f)

def cksDField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  fun y => (1/4:ℝ)*traceProduct (inverse (cksQField z f y))
    ((-3:ℝ) • f.mg y+z y • (f.er y-(2:ℝ) • f.eg y-cksLieField z f y))

def cksTField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  fun y => (1/2:ℝ)*traceProduct (inverse (cksQField z f y))
    (f.mK y-f.mg y+z y • (f.ek y-f.eg y))

def cksBBField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  fun y => ∑ i, ∑ k, inverse (cksQField z f y) i k*(f.b y i*f.b y k)

def cksVField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  fun y => f.mr y+z y*f.err y+z y^2*f.mr y+z y^3*f.err y-
    (z y^3*(1+z y^2))*cksBBField z f y

def cksFField (z : Point → ℝ) (f : MassFields) : Point → ℝ :=
  normalizedMassField z (cksDField z f) (cksTField z f) (cksVField z f)

lemma cksQField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (cksQField z f) x := (hf.sigma.add ((hz.pow 3).smul hf.mg)).add ((hz.pow 4).smul hf.eg)

lemma cksHField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 3 (cksHField z f) x := by
  have hi := inverse_diff_at (cksQField_diff hz hf) h0
  apply contDiffAt_pi.mpr
  intro a
  exact ContDiffAt.sum fun b _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul
    (contDiffAt_pi.mp hf.b b)

lemma cksLieField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksLieField z f) x := by
  exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun k =>
    normalizedLie_diff (cksQField_diff hz hf) (cksHField_diff hz hf h0) i k

lemma cksDField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksDField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at ((cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have hp := (hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).const_smul (-3:ℝ)
  have he := (hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).const_smul (2:ℝ)
  exact (traceProduct_diff hi (hp.add (hz2.smul ((hf.er.sub he).sub (cksLieField_diff hz hf h0))))).const_smul (1/4:ℝ)

lemma cksTField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksTField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at ((cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  exact (traceProduct_diff hi ((hf.mK.sub (hf.mg.of_le (by norm_num))).add
    (hz2.smul (hf.ek.sub (hf.eg.of_le (by norm_num)))))).const_smul (1/2:ℝ)

lemma cksBBField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksBBField z f) x := by
  have hi := inverse_diff_at ((cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have hb (i : A) := (contDiffAt_pi.mp hf.b i).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hi i k).mul ((hb i).mul (hb k))

lemma cksVField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (cksVField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (((hf.mr.add (hz2.mul hf.err)).add ((hz2.pow 2).mul hf.mr)).add
    ((hz2.pow 3).mul hf.err)).sub (((hz2.pow 3).mul (contDiffAt_const.add (hz2.pow 2))).mul (cksBBField_diff hz hf h0))

lemma cksQField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    matrixThreeJets (cksQField z f) x = coefficientMetric (actualThreeJet z x) (massInputOf f x) := by
  unfold cksQField coefficientMetric
  erw [matrixThreeJets_add (hf.sigma.add ((hz.pow 3).smul hf.mg)) ((hz.pow 4).smul hf.eg),
    matrixThreeJets_add hf.sigma ((hz.pow 3).smul hf.mg),
    matrixThreeJets_mul (hz.pow 3) hf.mg,matrixThreeJets_mul (hz.pow 4) hf.eg,
    actualThreeJet_pow hz,actualThreeJet_pow hz]
  rfl

lemma cksHField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    (fun a => actualThreeJet (fun y => cksHField z f y a) x) =
      coefficientShift (actualThreeJet z x) (massInputOf f x) := by
  have hq := cksQField_diff hz hf
  have hi := inverse_diff_at hq h0
  funext a
  unfold cksHField coefficientShift
  rw [actualThreeJet_sum _ (fun b _ => (component_diff hi a b).mul (contDiffAt_pi.mp hf.b b))]
  apply Finset.sum_congr rfl
  intro b _
  rw [actualThreeJet_mul (component_diff hi a b) (contDiffAt_pi.mp hf.b b),
    actual_inverseMatrixThreeJet hq h0,cksQField_realized hz hf]
  rfl

lemma cksLieField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    matrixScalarJets (cksLieField z f) x =
      coefficientLie (actualThreeJet z x) (massInputOf f x) := by
  funext i k
  change actualScalarJet (fun y => normalizedLie (cksQField z f) (cksHField z f) y i k) x = _
  rw [actual_normalizedLieJet (cksQField_diff hz hf) (cksHField_diff hz hf h0),
    cksQField_realized hz hf,cksHField_realized hz hf h0]
  rfl

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def foliationCoefficients (p : MassParameter) :
    ScalarJet × ScalarJet × (A → ScalarThreeJet) × ScalarJet × ScalarJet :=
  (coefficientD p.1 p.2,coefficientT p.1 p.2,coefficientShift p.1 p.2,lapseCorrection p,uCorrection p)
def foliationRegion : Set MassParameter := massMetricRegion ∩ {p | 0 < massDenominator p}

lemma foliationRegion_open : IsOpen foliationRegion :=
  massDenominator_continuousOn.isOpen_inter_preimage massMetricRegion_open (isOpen_Ioi (a := (0:ℝ)))
lemma foliationRegion_zero {j : MassInput}
    (hj : determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) : (0,j) ∈ foliationRegion := by
  constructor
  · simpa only [massMetricRegion,mem_ofPred_eq,coefficientMetric_zero] using hj
  · simp [massDenominator,constantJet]
lemma foliationDen_smooth {p : MassParameter} (hp : p ∈ foliationRegion) :
    ContDiffAt ℝ ∞ foliationDen p := by
  have hV := coefficientV_smooth hp.1
  unfold foliationDen
  fun_prop
lemma lapseCorrection_smooth {p : MassParameter} (hp : p ∈ foliationRegion) :
    ContDiffAt ℝ ∞ lapseCorrection p := by
  have hd : 0 < (foliationDen p).1 := hp.2
  have hs := (sqrtJet_smooth hd).comp p (foliationDen_smooth hp)
  have hs1 : ContDiffAt ℝ ∞ (fun t : MassParameter => constantJet 1+sqrtJet (foliationDen t)) p := contDiffAt_const.add hs
  have hmul := productJet_contDiffAt hs hs1
  have hpos : 0 < (productJet (sqrtJet (foliationDen p)) (constantJet 1+sqrtJet (foliationDen p))).1 := by
    change 0 < Real.sqrt (foliationDen p).1*(1+Real.sqrt (foliationDen p).1)
    positivity
  have hi := (reciprocalJet_smooth hpos.ne').comp p hmul
  exact (productJet_contDiffAt (coefficientV_smooth hp.1) hi).neg
attribute [local irreducible] lapseCorrection
lemma uCorrection_smooth {p : MassParameter} (hp : p ∈ foliationRegion) :
    ContDiffAt ℝ ∞ uCorrection p := by
  have hd := coefficientD_smooth hp.1
  have hl := lapseCorrection_smooth hp
  unfold uCorrection
  fun_prop
lemma foliationCoefficients_smooth {p : MassParameter} (hp : p ∈ foliationRegion) :
    ContDiffAt ℝ ∞ foliationCoefficients p :=
  (coefficientD_smooth hp.1).prodMk ((coefficientT_smooth hp.1).prodMk
    ((coefficientShift_smooth hp.1).prodMk ((lapseCorrection_smooth hp).prodMk (uCorrection_smooth hp))))

lemma foliation_family_bound {K : Set MassInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ScalarThreeJet,
      ∀ j ∈ K, ‖z‖ ≤ δ → ‖foliationCoefficients (z,j)‖ ≤ C := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : ProperSpace MassParameter := FiniteDimensional.proper ℝ MassParameter
  let K₀ : Set MassParameter := (fun j : MassInput => ((0:ScalarThreeJet),j)) '' K
  have hK₀ : IsCompact K₀ := hK.image (by fun_prop)
  have hs : K₀ ⊆ foliationRegion := by
    rintro p ⟨j,hj,rfl⟩
    exact foliationRegion_zero (hreg j hj)
  obtain ⟨δ,hδ,hδs⟩ := hK₀.exists_cthickening_subset_open foliationRegion_open hs
  obtain ⟨C,hC⟩ := (hK₀.cthickening (r := δ)).exists_bound_of_continuousOn
    (fun p hp => (foliationCoefficients_smooth (hδs hp)).continuousAt.continuousWithinAt)
  refine ⟨δ,hδ,max C 0,le_max_right _ _,?_⟩
  intro z j hj hz
  apply (hC (z,j) ?_).trans (le_max_left _ _)
  apply Metric.mem_cthickening_of_dist_le (z,j) (0,j) δ K₀ ⟨j,hj,rfl⟩
  simpa only [Prod.dist_eq,dist_zero_right,dist_self,max_eq_left (norm_nonneg z)] using hz

theorem cks_foliation_coefficients_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ∀ z : ScalarThreeJet, ∀ j : MassInput, R₀ ≤ r → ‖z‖ ≤ 1/r →
      j.1 0 ∈ K → ‖j‖ ≤ B → ‖foliationCoefficients (z,j)‖ ≤ C := by
  obtain ⟨δ,hδ,C,hC,hh⟩ := foliation_family_bound (boundedMassFamily_compact hK B)
    (fun j hj => hreg _ hj.1)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,hC,?_⟩
  intro r z j hr hz hq hj
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)
  have hd : 1/r ≤ δ := by
    apply (div_le_iff₀ hr0).mpr
    simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))
  exact hh z j (boundedMassFamily_mem hq hj) (hz.trans hd)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma cksQField_two_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    matrixScalarJets (cksQField z f) x = lowerMatrixJet (coefficientMetric (actualThreeJet z x) (massInputOf f x)) :=
  congrArg lowerMatrixJet (cksQField_realized hz hf)

lemma cksDField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksDField z f) x = coefficientD (actualThreeJet z x) (massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hmg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hlie := cksLieField_diff hz hf h0
  have hp := (hmg.const_smul (-3:ℝ)).add (hz2.smul ((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie))
  unfold cksDField coefficientD
  erw [actualScalarJet_smul (1/4:ℝ) (traceProduct_diff hi hp),actual_traceProductJet hi hp,
    actual_inverseJets hq h0,cksQField_two_realized hz hf,
    matrixScalarJets_add (hmg.const_smul (-3:ℝ)) (hz2.smul ((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie)),
    matrixScalarJets_smul (-3) hmg,matrixScalarJets_mul hz2 ((hf.er.sub (heg.const_smul (2:ℝ))).sub hlie),
    matrixScalarJets_sub (hf.er.sub (heg.const_smul (2:ℝ))) hlie,
    matrixScalarJets_sub hf.er (heg.const_smul (2:ℝ)),matrixScalarJets_smul (2:ℝ) heg,
    cksLieField_realized hz hf h0]
  rfl

lemma cksTField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksTField z f) x = coefficientT (actualThreeJet z x) (massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hmg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hp := (hf.mK.sub hmg).add (hz2.smul (hf.ek.sub heg))
  unfold cksTField coefficientT
  erw [actualScalarJet_smul (1/2:ℝ) (traceProduct_diff hi hp),actual_traceProductJet hi hp,
    actual_inverseJets hq h0,cksQField_two_realized hz hf,
    matrixScalarJets_add (hf.mK.sub hmg) (hz2.smul (hf.ek.sub heg)),
    matrixScalarJets_sub hf.mK hmg,matrixScalarJets_mul hz2 (hf.ek.sub heg),
    matrixScalarJets_sub hf.ek heg]
  rfl

lemma cksBBField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksBBField z f) x = coefficientBB (actualThreeJet z x) (massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hq h0
  have hb (i : A) := (contDiffAt_pi.mp hf.b i).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  unfold cksBBField coefficientBB
  rw [actualScalarJet_sum _ (fun i _ => ContDiffAt.sum fun k _ => (component_diff hi i k).mul ((hb i).mul (hb k)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [actualScalarJet_sum _ (fun k _ => (component_diff hi i k).mul ((hb i).mul (hb k)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [actualScalarJet_mul (component_diff hi i k) ((hb i).mul (hb k)),
    actualScalarJet_mul (hb i) (hb k),actual_inverseMatrixJet hq h0]
  have heq := cksQField_two_realized hz hf
  change productJet (inverseMatrixJet (matrixScalarJets (cksQField z f) x) i k)
      (productJet (actualScalarJet (fun y => f.b y i) x) (actualScalarJet (fun y => f.b y k) x)) = _
  rw [heq]
  rfl

lemma cksVField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (cksVField z f) x = coefficientV (actualThreeJet z x) (massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hmr := hf.mr
  have herr := hf.err
  have hbb := cksBBField_diff hz hf h0
  unfold cksVField coefficientV
  simp (disch := fun_prop) only [actualScalarJet_add,actualScalarJet_sub,actualScalarJet_mul,actualScalarJet_pow,actualScalarJet_const]
  rw [cksBBField_realized hz hf h0]
  rfl

lemma cksFField_realized {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hV : 1+z x^3*cksVField z f x ≠ 0) :
    actualScalarJet (cksFField z f) x = cksMassJet (actualThreeJet z x) (massInputOf f x) := by
  unfold cksFField cksMassJet
  rw [actual_normalizedMassJet (hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) (cksDField_diff hz hf h0) (cksTField_diff hz hf h0) (cksVField_diff hz hf h0) hV,
    cksDField_realized hz hf h0,cksTField_realized hz hf h0,cksVField_realized hz hf h0]
  rfl

lemma cksLeadingField_realized {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (f.sigma x) ≠ 0) :
    actualScalarJet (cksLeadingField f) x = leadingMassJet (massInputOf f x) := by
  have hs := hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hs h0
  have hmg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have htg := traceProduct_diff hi hmg
  have htk := traceProduct_diff hi hf.mK
  have hmr := hf.mr
  unfold cksLeadingField leadingMassJet
  simp (disch := fun_prop) only [actualScalarJet_add,actualScalarJet_smul]
  rw [actual_traceProductJet hi hmg,actual_traceProductJet hi hf.mK,actual_inverseJets hs h0]
  rfl

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t := by
  simp [traceProduct,mul_add,Finset.sum_add_distrib]
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p := by
  simp [traceProduct]
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma tensorRegion_open : IsOpen tensorRegion := by
  have h := massDenominator_continuousOn.isOpen_inter_preimage massMetricRegion_open (isOpen_Ioi (a := (0:ℝ)))
  exact h.preimage tensorBase_smooth.continuous

lemma tensorRegion_zero {j : TensorInput}
    (hj : determinant (fun i k => (j.1.1 0 i k).1.1) ≠ 0) : (0,j) ∈ tensorRegion := by
  constructor
  · simpa only [coefficientMetric_zero] using hj
  · simp [tensorDen,constantJet]

lemma tensor_family_bound {K : Set TensorInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ScalarThreeJet,
      ∀ j ∈ K, ‖z‖ ≤ δ → ‖tensorCoefficients (z,j)‖ ≤ C := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : FiniteDimensional ℝ TensorInput := inferInstance
  let : ProperSpace TensorParameter := FiniteDimensional.proper ℝ TensorParameter
  let K₀ : Set TensorParameter := (fun j : TensorInput => ((0:ScalarThreeJet),j)) '' K
  have hK₀ : IsCompact K₀ := hK.image (by fun_prop)
  have hs : K₀ ⊆ tensorRegion := by
    rintro p ⟨j,hj,rfl⟩
    exact tensorRegion_zero (hreg j hj)
  obtain ⟨δ,hδ,hδs⟩ := hK₀.exists_cthickening_subset_open tensorRegion_open hs
  obtain ⟨C,hC⟩ := (hK₀.cthickening (r := δ)).exists_bound_of_continuousOn
    (fun p hp => (tensorCoefficients_smooth (hδs hp)).continuousAt.continuousWithinAt)
  refine ⟨δ,hδ,max C 0,le_max_right _ _,?_⟩
  intro z j hj hz
  apply (hC (z,j) ?_).trans (le_max_left _ _)
  apply Metric.mem_cthickening_of_dist_le (z,j) (0,j) δ K₀ ⟨j,hj,rfl⟩
  simpa only [Prod.dist_eq,dist_zero_right,dist_self,max_eq_left (norm_nonneg z)] using hz

def boundedTensorFamily (K : Set MatrixThreeJet) (B : ℝ) : Set TensorInput :=
  boundedMassFamily K B ×ˢ (Metric.closedBall (0:ScalarJet) B ×ˢ Metric.closedBall (0:A → ScalarJet) B)

lemma boundedTensorFamily_compact {K : Set MatrixThreeJet} (hK : IsCompact K) (B : ℝ) :
    IsCompact (boundedTensorFamily K B) := by
  let : ProperSpace ScalarJet := FiniteDimensional.proper ℝ ScalarJet
  let : ProperSpace (A → ScalarJet) := FiniteDimensional.proper ℝ (A → ScalarJet)
  exact (boundedMassFamily_compact hK B).prod ((isCompact_closedBall _ B).prod (isCompact_closedBall _ B))

theorem cks_tensor_coefficients_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ∀ z : ScalarThreeJet, ∀ j : TensorInput, R₀ ≤ r → ‖z‖ ≤ 1/r →
      j.1.1 0 ∈ K → ‖j.1‖ ≤ B → ‖j.2.1‖ ≤ B → ‖j.2.2‖ ≤ B →
      ‖tensorCoefficients (z,j)‖ ≤ C := by
  obtain ⟨δ,hδ,C,hC,hh⟩ := tensor_family_bound (boundedTensorFamily_compact hK B)
    (fun j hj => hreg _ hj.1.1)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,hC,?_⟩
  intro r z j hr hz hq hj hkr hkb
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)
  have hd : 1/r ≤ δ := by
    apply (div_le_iff₀ hr0).mpr
    simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))
  apply hh z j
  · exact ⟨boundedMassFamily_mem hq hj,by simpa only [Metric.mem_closedBall,dist_zero_right] using hkr,
      by simpa only [Metric.mem_closedBall,dist_zero_right] using hkb⟩
  · exact hz.trans hd

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def foliationDenField (z : Point → ℝ) (f : MassFields) : Point → ℝ := fun y =>
  1+z y^3*cksVField z f y
def lapseCorrectionField (z : Point → ℝ) (f : MassFields) : Point → ℝ := fun y =>
  -(cksVField z f y*(Real.sqrt (foliationDenField z f y)*(1+Real.sqrt (foliationDenField z f y)))⁻¹)
def uCorrectionField (z : Point → ℝ) (f : MassFields) : Point → ℝ := fun y =>
  cksDField z f y+lapseCorrectionField z f y+z y^3*(cksDField z f y*lapseCorrectionField z f y)

lemma foliationDenField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (foliationDenField z f) x :=
  contDiffAt_const.add (((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 3).mul (cksVField_diff hz hf h0))
lemma actual_foliationDen {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (foliationDenField z f) x = foliationDen (actualThreeJet z x,massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hv := cksVField_diff hz hf h0
  unfold foliationDenField foliationDen
  rw [actualScalarJet_add contDiffAt_const ((hz2.pow 3).mul hv),actualScalarJet_const,
    actualScalarJet_mul (hz2.pow 3) hv,actualScalarJet_pow hz2,cksVField_realized hz hf h0]
  rfl
lemma lapseCorrectionField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hp : 0 < foliationDenField z f x) :
    ContDiffAt ℝ 2 (lapseCorrectionField z f) x := by
  have hs := (foliationDenField_diff hz hf h0).sqrt hp.ne'
  have hp' : Real.sqrt (foliationDenField z f x)*(1+Real.sqrt (foliationDenField z f x)) ≠ 0 := by positivity
  exact ((cksVField_diff hz hf h0).mul ((hs.mul (contDiffAt_const.add hs)).inv hp')).neg
lemma uCorrectionField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hp : 0 < foliationDenField z f x) :
    ContDiffAt ℝ 2 (uCorrectionField z f) x := by
  have hd := cksDField_diff hz hf h0
  have hl := lapseCorrectionField_diff hz hf h0 hp
  exact (hd.add hl).add (((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 3).mul (hd.mul hl))

lemma actual_lapseCorrection {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hp : 0 < foliationDenField z f x) :
    actualScalarJet (lapseCorrectionField z f) x = lapseCorrection (actualThreeJet z x,massInputOf f x) := by
  have hs := (foliationDenField_diff hz hf h0).sqrt hp.ne'
  have hv := cksVField_diff hz hf h0
  have hp' : Real.sqrt (foliationDenField z f x)*(1+Real.sqrt (foliationDenField z f x)) ≠ 0 := by positivity
  have hi := actual_reciprocal (hs.mul (contDiffAt_const.add hs)) hp'
  simp only [one_div] at hi
  unfold lapseCorrectionField lapseCorrection
  erw [actualScalarJet_neg (hv.mul ((hs.mul (contDiffAt_const.add hs)).inv hp')),
    actualScalarJet_mul hv ((hs.mul (contDiffAt_const.add hs)).inv hp'),
    hi,
    actualScalarJet_mul hs (contDiffAt_const.add hs),actualScalarJet_add contDiffAt_const hs,
    actualScalarJet_const,actualScalarJet_sqrt (foliationDenField_diff hz hf h0) hp,
    actual_foliationDen hz hf h0,cksVField_realized hz hf h0]

lemma actual_uCorrection {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hp : 0 < foliationDenField z f x) :
    actualScalarJet (uCorrectionField z f) x = uCorrection (actualThreeJet z x,massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hd := cksDField_diff hz hf h0
  have hl := lapseCorrectionField_diff hz hf h0 hp
  unfold uCorrectionField uCorrection
  rw [actualScalarJet_add (hd.add hl) ((hz2.pow 3).mul (hd.mul hl))]
  rw [actualScalarJet_add hd hl]
  rw [actualScalarJet_mul (hz2.pow 3) (hd.mul hl)]
  rw [actualScalarJet_pow hz2,actualScalarJet_mul hd hl]
  rw [cksDField_realized hz hf h0,actual_lapseCorrection hz hf h0 hp]
  simp only [actualThreeJet]

lemma reciprocal_sqrt_factor {z V : ℝ} (hp : 0 < 1+z^3*V) :
    (Real.sqrt (1+z^3*V))⁻¹-1 = z^3*(-(V*(Real.sqrt (1+z^3*V)*(1+Real.sqrt (1+z^3*V)))⁻¹)) := by
  have hs := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  have hh : 1+Real.sqrt (1+z^3*V) ≠ 0 := by positivity
  field_simp
  nlinarith

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def tensorInputOf (f : TensorFields) (x : Point) : TensorInput :=
  (massInputOf f.base x,actualScalarJet f.kr x,fun a => actualScalarJet (fun y => f.kb y a) x)

def tensorKField (z : Point → ℝ) (f : TensorFields) : Point → Mat := fun y =>
  f.base.sigma y+z y^3 • f.base.mK y+z y^4 • f.base.ek y

def tensorDenField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  1+z y^3*cksVField z f.base y

def tensorLapseSqField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  (1+z y^2)*(tensorDenField z f y)⁻¹

def tensorLapseField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  Real.sqrt (1+z y^2)*(Real.sqrt (tensorDenField z f y))⁻¹

def tensorCrossField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  ∑ a, cksHField z f.base y a*f.kb y a

def tensorQuadField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  ∑ a, ∑ b, tensorKField z f y a b*(cksHField z f.base y a*cksHField z f.base y b)

def tensorLField (z : Point → ℝ) (f : TensorFields) : Point → ℝ := fun y =>
  tensorLapseSqField z f y*(f.kr y-f.base.mr y-z y*f.base.err y+
    z y^3*(cksBBField z f.base y-2*tensorCrossField z f y+tensorQuadField z f y))

def tensorEtaField (z : Point → ℝ) (f : TensorFields) : Point → A → ℝ := fun y a =>
  tensorLapseField z f y*(f.kb y a-∑ b, cksHField z f.base y b*tensorKField z f y b a)

def tensorTauField (z : Point → ℝ) (f : TensorFields) : Point → Mat := fun y =>
  f.base.mK y-f.base.mg y+z y • (f.base.ek y-f.base.eg y)-
    cksTField z f.base y • cksQField z f.base y

lemma tensorKField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (tensorKField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact ((hf.base.sigma.of_le (by norm_num)).add ((hz2.pow 3).smul hf.base.mK)).add
    ((hz2.pow 4).smul hf.base.ek)

lemma tensorDenField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    ContDiffAt ℝ 2 (tensorDenField z f) x :=
  contDiffAt_const.add (((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 3).mul
    (cksVField_diff hz hf.base h0))

lemma actual_tensorK {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x) :
    matrixScalarJets (tensorKField z f) x = tensorK (actualThreeJet z x,tensorInputOf f x) := by
  have hs := hf.base.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  unfold tensorKField tensorK tensorInputOf massInputOf
  dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
  erw [matrixScalarJets_add (hs.add ((hz2.pow 3).smul hf.base.mK)) ((hz2.pow 4).smul hf.base.ek),
    matrixScalarJets_add hs ((hz2.pow 3).smul hf.base.mK),
    matrixScalarJets_mul (hz2.pow 3) hf.base.mK,matrixScalarJets_mul (hz2.pow 4) hf.base.ek,
    actualScalarJet_pow hz2,actualScalarJet_pow hz2]
  rfl

lemma actual_tensorDen {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    actualScalarJet (tensorDenField z f) x = tensorDen (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hv := cksVField_diff hz hf.base h0
  unfold tensorDenField tensorDen tensorInputOf
  simp only [actualScalarJet_add contDiffAt_const ((hz2.pow 3).mul hv),actualScalarJet_const,
    actualScalarJet_mul (hz2.pow 3) hv,actualScalarJet_pow hz2,cksVField_realized hz hf.base h0]
  rfl

lemma actual_tensorLapseSq {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    actualScalarJet (tensorLapseSqField z f) x = tensorLapseSq (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have ht : ContDiffAt ℝ 2 (fun y => 1+z y^2) x := contDiffAt_const.add (hz2.pow 2)
  have hden := tensorDenField_diff hz hf h0
  unfold tensorLapseSqField tensorLapseSq
  erw [actualScalarJet_mul ht (hden.inv hd.ne')]
  have hi := actual_reciprocal hden hd.ne'
  simp only [one_div] at hi
  erw [hi,actual_tensorDen hz hf h0,actualScalarJet_add contDiffAt_const (hz2.pow 2),
    actualScalarJet_const,actualScalarJet_pow hz2]
  rfl

lemma actual_tensorLapse {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    actualScalarJet (tensorLapseField z f) x = tensorLapse (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have ht : ContDiffAt ℝ 2 (fun y => 1+z y^2) x := contDiffAt_const.add (hz2.pow 2)
  have hpos : 0 < 1+z x^2 := by positivity
  have hden := tensorDenField_diff hz hf h0
  have hsd := hden.sqrt hd.ne'
  unfold tensorLapseField tensorLapse
  erw [actualScalarJet_mul (ht.sqrt hpos.ne') (hsd.inv (Real.sqrt_pos.mpr hd).ne')]
  have hi := actual_reciprocal hsd (Real.sqrt_pos.mpr hd).ne'
  simp only [one_div] at hi
  erw [hi,actualScalarJet_sqrt ht hpos,actualScalarJet_sqrt hden hd,actual_tensorDen hz hf h0,
    actualScalarJet_add contDiffAt_const (hz2.pow 2),actualScalarJet_const,actualScalarJet_pow hz2]
  rfl

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma metricBlock_submatrix (a : ℝ) (b : Point) (q : Mat) :
    (metricBlock a b q).submatrix Fin.succ Fin.succ = q := by
  ext i k
  fin_cases i <;> fin_cases k <;> rfl

lemma metricBlock_leaf_posDef {a : ℝ} {b : Point} {q : Mat} (h : (metricBlock a b q).PosDef) :
    q.PosDef := by
  have hi : Function.Injective (Fin.succ : I → Fin 3) := Fin.succ_injective 2
  simpa only [metricBlock_submatrix] using h.submatrix hi

lemma inverse_mul_vector (q : Mat) (hq : determinant q ≠ 0) (b : Point) (i : I) :
    ∑ k, q i k*(∑ a, inverse q k a*b a) = b i := by
  fin_cases i <;> simp only [Fin.sum_univ_two,inverse] <;>
    field_simp <;> dsimp [determinant] at * <;> ring

lemma metricBlock_schur_positive {a : ℝ} {b : Point} {q : Mat}
    (h : (metricBlock a b q).PosDef) :
    0 < a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
  have hq : determinant q ≠ 0 := by rw [determinant_eq]; exact (metricBlock_leaf_posDef h).det_pos.ne'
  let s : Point := fun i => ∑ k, inverse q i k*b k
  let v : Fin 3 → ℝ := ![1,-s 0,-s 1]
  have hv : v ≠ 0 := by
    intro hh
    have hh' := congrFun hh 0
    norm_num [v] at hh'
  have hp := h.dotProduct_mulVec_pos hv
  have hquad : (star v) ⬝ᵥ (metricBlock a b q *ᵥ v) = a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
    have hmul0 : q 0 0*s 0+q 0 1*s 1=b 0 := by simpa [s,Fin.sum_univ_two] using inverse_mul_vector q hq b 0
    have hmul1 : q 1 0*s 0+q 1 1*s 1=b 1 := by simpa [s,Fin.sum_univ_two] using inverse_mul_vector q hq b 1
    have hbb : (∑ i, ∑ k, inverse q i k*(b i*b k)) = b 0*s 0+b 1*s 1 := by
      simp [s,Fin.sum_univ_two]
      ring
    rw [hbb]
    simp only [v,metricBlock,Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      star_trivial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      one_mul,neg_mul,mul_neg]
    simp only [Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      mul_one]
    nlinarith [congrArg (fun t : ℝ => t * s 0) hmul0, congrArg (fun t : ℝ => t * s 1) hmul1]
  rwa [hquad] at hp

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_nat (n : ℕ) (x : Point) : radiusPower n x = Real.exp (x 0)^n := by
  exact Real.exp_nat_mul (x 0) n

lemma normalize_two_bound {n : ℕ} {f : Point → ℝ} {x : Point} {B : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hb : ‖actualScalarJet f x‖ ≤ B/Real.exp (x 0)^n) :
    ‖actualScalarJet (fun y => radiusPower n y*f y) x‖ ≤ 4*(max 1 |(n:ℝ)|)^2*B := by
  rw [actualScalarJet_mul (radiusPower_diff n 2 x) hf]
  have h := productJet_norm (radiusPower_two_norm n x) hb
  have hr : Real.exp (x 0)^n ≠ 0 := ne_of_gt (pow_pos (Real.exp_pos _) _)
  calc
    _ ≤ 4*((max 1 |(n:ℝ)|)^2*radiusPower n x)*(B/Real.exp (x 0)^n) := h
    _ = 4*(max 1 |(n:ℝ)|)^2*B := by rw [radiusPower_nat]; field_simp

lemma normalize_three_bound {n : ℕ} {f : Point → ℝ} {x : Point} {B : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hb : ‖actualThreeJet f x‖ ≤ B/Real.exp (x 0)^n) :
    ‖actualThreeJet (fun y => radiusPower n y*f y) x‖ ≤ 8*(max 1 |(n:ℝ)|)^3*B := by
  rw [actualThreeJet_mul (radiusPower_diff n 3 x) hf]
  have h := productThreeJet_norm (radiusPower_three_norm n x) hb
  have hr : Real.exp (x 0)^n ≠ 0 := ne_of_gt (pow_pos (Real.exp_pos _) _)
  calc
    _ ≤ 8*((max 1 |(n:ℝ)|)^3*radiusPower n x)*(B/Real.exp (x 0)^n) := h
    _ = 8*(max 1 |(n:ℝ)|)^3*B := by rw [radiusPower_nat]; field_simp

lemma normalize_matrix_three {n : ℕ} {f : Point → Mat} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 3 f x) (hb : ‖matrixThreeJets f x‖ ≤ B/Real.exp (x 0)^n) :
    ‖matrixThreeJets (fun y => radiusPower n y • f y) x‖ ≤ 8*(max 1 |(n:ℝ)|)^3*B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  exact normalize_three_bound (component_diff hf i k)
    ((norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ i).trans hb))

lemma normalize_matrix_two {n : ℕ} {f : Point → Mat} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 2 f x) (hb : ‖matrixScalarJets f x‖ ≤ B/Real.exp (x 0)^n) :
    ‖matrixScalarJets (fun y => radiusPower n y • f y) x‖ ≤ 4*(max 1 |(n:ℝ)|)^2*B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  exact normalize_two_bound (component_diff hf i k)
    ((norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ i).trans hb))

lemma radialMatrixD_regular {f : Point → Mat} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    ContDiffAt ℝ 2 (radialMatrixD f) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact contDiffAt_D (component_diff hf i k) (by norm_num) (basis 0)

lemma radialMatrixD_bound {f : Point → Mat} {x : Point} {B : ℝ}
    (hb : ‖matrixThreeJets f x‖ ≤ B) : ‖matrixScalarJets (radialMatrixD f) x‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro k
  have hh : ‖actualThreeJet (fun y => f y i k) x‖ ≤ B :=
    (norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ i).trans hb)
  exact (norm_le_pi_norm _ 0).trans (norm_prod_le_iff.mp hh).2

def normalizeMassLogFields (f : MassFields) : MassFields where
  sigma := f.sigma
  mg := f.mg
  eg := fun y => radiusPower 2 y • f.eg y
  er := fun y => radiusPower 2 y • radialMatrixD f.eg y
  mK := f.mK
  ek := fun y => radiusPower 2 y • f.ek y
  b := fun y => radiusPower 3 y • f.b y
  mr := f.mr
  err := fun y => radiusPower 6 y*f.err y

lemma normalizeMassLogFields_regular {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    (normalizeMassLogFields f).RegularAt x := by
  exact ⟨hf.sigma,hf.mg,(radiusPower_diff 2 3 x).smul hf.eg,
    (radiusPower_diff 2 2 x).smul (radialMatrixD_regular hf.eg),hf.mK,
    (radiusPower_diff 2 2 x).smul hf.ek,(radiusPower_diff 3 3 x).smul hf.b,
    hf.mr,(radiusPower_diff 6 2 x).mul hf.err⟩

lemma massInputOf_norm {f : MassFields} {x : Point} {B : ℝ} (hB : 0 ≤ B)
    (hs : ‖matrixThreeJets f.sigma x‖ ≤ B) (hmg : ‖matrixThreeJets f.mg x‖ ≤ B)
    (heg : ‖matrixThreeJets f.eg x‖ ≤ B) (her : ‖matrixScalarJets f.er x‖ ≤ B)
    (hmk : ‖matrixScalarJets f.mK x‖ ≤ B) (hek : ‖matrixScalarJets f.ek x‖ ≤ B)
    (hb : ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B)
    (hmr : ‖actualScalarJet f.mr x‖ ≤ B) (herr : ‖actualScalarJet f.err x‖ ≤ B) :
    ‖massInputOf f x‖ ≤ B := by
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    fin_cases i <;> first | exact hs | exact hmg | exact heg
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    fin_cases i <;> first | exact her | exact hmk | exact hek
  apply norm_prod_le_iff.mpr
  refine ⟨hb,?_⟩
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  fin_cases i <;> first | exact hmr | exact herr

theorem normalized_log_mass_input_bound {B : ℝ} (hB : 0 ≤ B)
    {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hs : ‖matrixThreeJets f.sigma x‖ ≤ B) (hmg : ‖matrixThreeJets f.mg x‖ ≤ B)
    (heg : ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2)
    (hmk : ‖matrixScalarJets f.mK x‖ ≤ B) (hek : ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2)
    (hb : ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3)
    (hmr : ‖actualScalarJet f.mr x‖ ≤ B) (herr : ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6) :
    ‖massInputOf (normalizeMassLogFields f) x‖ ≤ 216*B := by
  have hB216 : B ≤ 216*B := by linarith
  refine massInputOf_norm (f := normalizeMassLogFields f) (x := x) (by positivity)
    (hs.trans hB216) (hmg.trans hB216) ?_ ?_ (hmk.trans hB216) ?_ ?_ (hmr.trans hB216) ?_
  · exact (normalize_matrix_three hB hf.eg heg).trans (by norm_num; linarith)
  · exact (normalize_matrix_two hB (radialMatrixD_regular hf.eg) (radialMatrixD_bound heg)).trans (by norm_num; linarith)
  · exact (normalize_matrix_two hB hf.ek hek).trans (by norm_num; linarith)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    have h := normalize_three_bound (contDiffAt_pi.mp hf.b a) ((norm_le_pi_norm _ a).trans hb)
    norm_num at h
    exact h
  · exact (normalize_two_bound hf.err herr).trans (by norm_num; linarith)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_neg_nat (n : ℕ) (x : Point) : radiusPower (-(n:ℝ)) x = 1/Real.exp (x 0)^n := by
  rw [radiusPower,neg_mul,Real.exp_neg,Real.exp_nat_mul,one_div]
lemma radiusPower_inverse (x : Point) : radiusPower (-1) x = 1/Real.exp (x 0) := by
  simpa using radiusPower_neg_nat 1 x

lemma radiusPower_two (x : Point) : radiusPower 2 x = Real.exp (x 0)^2 := radiusPower_nat 2 x
lemma radiusPower_three (x : Point) : radiusPower 3 x = Real.exp (x 0)^3 := radiusPower_nat 3 x
lemma radiusPower_six (x : Point) : radiusPower 6 x = Real.exp (x 0)^6 := radiusPower_nat 6 x
lemma radiusPower_minus_five (x : Point) : radiusPower (-5) x = 1/Real.exp (x 0)^5 := radiusPower_neg_nat 5 x

lemma D_radiusPower_angular (n : ℝ) (a : A) : D (basis a.succ) (radiusPower n) = 0 := by
  rw [D_radiusPower]
  funext x
  simp [basis]

lemma normalizedLie_radius (n m : ℝ) {q : Point → Mat} {S : Point → A → ℝ} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : A) :
    normalizedLie (fun y => radiusPower n y • q y) (fun y => radiusPower m y • S y) x i k =
      (radiusPower n x*radiusPower m x)*normalizedLie q S x i k := by
  have hqd (a b : A) := (component_diff hq a b).differentiableAt (by norm_num)
  have hSd (a : A) := (contDiffAt_pi.mp hS a).differentiableAt (by norm_num)
  have hn := (radiusPower_diff n 1 x).differentiableAt (by norm_num)
  have hm := (radiusPower_diff m 1 x).differentiableAt (by norm_num)
  unfold normalizedLie
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (radiusPower m x*S x a)*D (basis a.succ) (fun y => radiusPower n y*q y i k) x+
    (radiusPower n x*q x a k)*D (basis i.succ) (fun y => radiusPower m y*S y a) x+
    (radiusPower n x*q x i a)*D (basis k.succ) (fun y => radiusPower m y*S y a) x = _
  rw [D_mul _ hn (hqd i k),D_mul _ hm (hSd a),D_mul _ hm (hSd a),
    D_radiusPower_angular,D_radiusPower_angular,D_radiusPower_angular]
  dsimp
  ring

def logScaledQ (f : MassFields) : Point → Mat := fun y =>
  (1/Real.exp (y 0))^3 • ((-3:ℝ) • f.mg y+(1/Real.exp (y 0)) •
    (Real.exp (y 0)^2 • radialMatrixD f.eg y-(2:ℝ) • (Real.exp (y 0)^2 • f.eg y)))

lemma logGamma_normalized (f : MassFields) : logGamma f = fun y =>
    radiusPower 2 y • cksQField (radiusPower (-1)) (normalizeMassLogFields f) y := by
  funext y i k
  unfold logGamma cksQField normalizeMassLogFields
  simp only [radiusPower_inverse,radiusPower_two]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logGammaRadial_normalized (f : MassFields) : logGammaRadial f = fun y =>
    (2*Real.exp (y 0)) • cksQField (radiusPower (-1)) (normalizeMassLogFields f) y+
    Real.exp (y 0) • logScaledQ f y := by
  funext y i k
  unfold logGammaRadial cksQField normalizeMassLogFields logScaledQ
  simp only [radiusPower_inverse,radiusPower_two]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp
  ring

lemma logShift_normalized (f : MassFields) : logShift f = fun y =>
    radiusPower (-5) y • cksHField (radiusPower (-1)) (normalizeMassLogFields f) y := by
  funext y a
  unfold logShift cksHField
  rw [logGamma_normalized]
  have hr := Real.exp_ne_zero (y 0)
  simp only [radiusPower_two,inverse_smul _ _ (pow_ne_zero 2 hr)]
  change (∑ b, inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) a b/Real.exp (y 0)^2*f.b y b) =
    radiusPower (-5) y*(∑ b, inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) a b*(radiusPower 3 y*f.b y b))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [radiusPower_minus_five,radiusPower_three]
  field_simp

lemma logTangentialK_normalized (f : MassFields) : logTangentialK f = fun y =>
    Real.exp (y 0)^2 • (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y+
      (1/Real.exp (y 0))^3 • (f.mK y-f.mg y+(1/Real.exp (y 0)) •
        (Real.exp (y 0)^2 • f.ek y-Real.exp (y 0)^2 • f.eg y))) := by
  funext y i k
  unfold logTangentialK cksQField normalizeMassLogFields
  simp only [radiusPower_inverse,radiusPower_two]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp
  ring

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t :=
  CKSAngularGeometry.traceProduct_add q p t
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p :=
  CKSAngularGeometry.traceProduct_smul c q p
lemma traceProduct_smul_left (c : ℝ) (q p : Mat) : traceProduct (c • q) p = c*traceProduct q p := by
  unfold traceProduct
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma log_trace_coefficient {f : MassFields} {x : Point}
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0) :
    (1/2:ℝ)*traceProduct (inverse (logGamma f x)) (logTangentialK f x) =
      1+(1/Real.exp (x 0))^3*cksTField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hr := Real.exp_ne_zero (x 0)
  rw [logGamma_normalized,logTangentialK_normalized]
  simp only [radiusPower_two]
  have hi : inverse (Real.exp (x 0)^2 • cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) =
      (1/Real.exp (x 0)^2) • inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) := by
    funext i k
    rw [inverse_smul _ _ (pow_ne_zero 2 hr)]
    dsimp; ring
  rw [hi,traceProduct_smul_left,traceProduct_smul,traceProduct_add,traceProduct_smul]
  have hinv := inverse_trace _ h0
  change traceProduct (inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x))
    (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) = 2 at hinv
  rw [hinv]
  unfold cksTField normalizeMassLogFields
  simp only [radiusPower_inverse,radiusPower_two]
  field_simp

lemma log_schur_coefficient (f : MassFields) (x : Point) :
    (1+Real.exp (x 0)^2)*logSchur f x =
      1+(1/Real.exp (x 0))^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hr := Real.exp_ne_zero (x 0)
  have hbb : (∑ i, ∑ k, inverse (logGamma f x) i k*(f.b x i*f.b x k)) =
      (1/Real.exp (x 0))^8*cksBBField (radiusPower (-1)) (normalizeMassLogFields f) x := by
    rw [logGamma_normalized]
    simp only [radiusPower_two]
    unfold cksBBField
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [inverse_smul _ _ (pow_ne_zero 2 hr)]
    dsimp only [normalizeMassLogFields]
    rw [radiusPower_three]
    dsimp
    field_simp
  unfold logSchur
  rw [hbb]
  unfold logRadialMetric cksVField
  dsimp only [normalizeMassLogFields]
  rw [radiusPower_inverse,radiusPower_six]
  have hn : 1+Real.exp (x 0)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actual_tensorH {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (a : A) :
    actualScalarJet (fun y => cksHField z f.base y a) x =
      tensorH (actualThreeJet z x,tensorInputOf f x) a := by
  have h := congrFun (cksHField_realized hz hf.base h0) a
  exact congrArg Prod.fst h

lemma tensorCrossField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    ContDiffAt ℝ 2 (tensorCrossField z f) x := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact ContDiffAt.sum fun a _ => (contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hf.kb a)

lemma tensorQuadField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    ContDiffAt ℝ 2 (tensorQuadField z f) x := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hK := tensorKField_diff hz hf
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
    (component_diff hK a b).mul ((contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hH b))

lemma actual_tensorCross {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    actualScalarJet (tensorCrossField z f) x = tensorCross (actualThreeJet z x,tensorInputOf f x) := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  unfold tensorCrossField tensorCross
  rw [actualScalarJet_sum _ (fun a _ => (contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hf.kb a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [actualScalarJet_mul (contDiffAt_pi.mp hH a) (contDiffAt_pi.mp hf.kb a),actual_tensorH hz hf h0]
  rfl

lemma actual_tensorQuad {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    actualScalarJet (tensorQuadField z f) x = tensorNormalQuad (actualThreeJet z x,tensorInputOf f x) := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hK := tensorKField_diff hz hf
  have hprod (a b : A) := (component_diff hK a b).mul
    ((contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hH b))
  unfold tensorQuadField tensorNormalQuad
  rw [actualScalarJet_sum _ (fun a _ => ContDiffAt.sum fun b _ => hprod a b)]
  apply Finset.sum_congr rfl
  intro a _
  rw [actualScalarJet_sum _ (fun b _ => hprod a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [actualScalarJet_mul (component_diff hK a b) ((contDiffAt_pi.mp hH a).mul (contDiffAt_pi.mp hH b)),
    actualScalarJet_mul (contDiffAt_pi.mp hH a) (contDiffAt_pi.mp hH b),
    actual_tensorH hz hf h0,actual_tensorH hz hf h0]
  have hk := congrFun (congrFun (actual_tensorK hz hf) a) b
  exact congrArg (fun j => productJet j
    (productJet (tensorH (actualThreeJet z x,tensorInputOf f x) a)
      (tensorH (actualThreeJet z x,tensorInputOf f x) b))) hk

lemma tensorLapseSqField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    ContDiffAt ℝ 2 (tensorLapseSqField z f) x := by
  exact (contDiffAt_const.add ((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 2)).mul
    ((tensorDenField_diff hz hf h0).inv hd.ne')

lemma tensorLapseField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    ContDiffAt ℝ 2 (tensorLapseField z f) x := by
  have ht : ContDiffAt ℝ 2 (fun y => 1+z y^2) x :=
    contDiffAt_const.add ((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 2)
  exact (ht.sqrt (ne_of_gt (by positivity))).mul
    (((tensorDenField_diff hz hf h0).sqrt hd.ne').inv (Real.sqrt_pos.mpr hd).ne')

lemma actual_tensorL {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    actualScalarJet (tensorLField z f) x = tensorLCoeff (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hkr := hf.kr
  have hmr := hf.base.mr
  have herr := hf.base.err
  have hl := tensorLapseSqField_diff hz hf h0 hd
  have hbb := cksBBField_diff hz hf.base h0
  have hcross := tensorCrossField_diff hz hf h0
  have hquad := tensorQuadField_diff hz hf h0
  unfold tensorLField tensorLCoeff
  simp (disch := fun_prop) only [actualScalarJet_mul,actualScalarJet_add,actualScalarJet_sub,
    actualScalarJet_pow,actualScalarJet_const,productJet_constant_left]
  rw [actual_tensorLapseSq hz hf h0 hd,cksBBField_realized hz hf.base h0,
    actual_tensorCross hz hf h0,actual_tensorQuad hz hf h0]
  rfl

lemma actual_tensorEta {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) (a : A) :
    actualScalarJet (fun y => tensorEtaField z f y a) x =
      tensorEtaCoeff (actualThreeJet z x,tensorInputOf f x) a := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hK := tensorKField_diff hz hf
  have hm (b : A) := (contDiffAt_pi.mp hH b).mul (component_diff hK b a)
  unfold tensorEtaField tensorEtaCoeff
  rw [actualScalarJet_mul (tensorLapseField_diff hz hf h0 hd)
    ((contDiffAt_pi.mp hf.kb a).sub (ContDiffAt.sum fun b _ => hm b)),
    actual_tensorLapse hz hf h0 hd,
    actualScalarJet_sub (contDiffAt_pi.mp hf.kb a) (ContDiffAt.sum fun b _ => hm b),
    actualScalarJet_sum _ (fun b _ => hm b)]
  congr 2
  apply Finset.sum_congr rfl
  intro b _
  rw [actualScalarJet_mul (contDiffAt_pi.mp hH b) (component_diff hK b a),actual_tensorH hz hf h0]
  exact congrArg (productJet (tensorH (actualThreeJet z x,tensorInputOf f x) b))
    (congrFun (congrFun (actual_tensorK hz hf) b) a)

lemma actual_tensorTau {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    matrixScalarJets (tensorTauField z f) x = tensorTauCoeff (actualThreeJet z x,tensorInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hmg := hf.base.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.base.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf.base).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have ht := cksTField_diff hz hf.base h0
  unfold tensorTauField tensorTauCoeff
  erw [matrixScalarJets_sub ((hf.base.mK.sub hmg).add (hz2.smul (hf.base.ek.sub heg))) (ht.smul hq),
    matrixScalarJets_add (hf.base.mK.sub hmg) (hz2.smul (hf.base.ek.sub heg)),
    matrixScalarJets_sub hf.base.mK hmg,matrixScalarJets_mul hz2 (hf.base.ek.sub heg),
    matrixScalarJets_sub hf.base.ek heg,matrixScalarJets_mul ht hq,
    cksTField_realized hz hf.base h0,cksQField_two_realized hz hf.base]
  rfl

lemma tensorLField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) :
    ContDiffAt ℝ 2 (tensorLField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (tensorLapseSqField_diff hz hf h0 hd).mul
    (((hf.kr.sub hf.base.mr).sub (hz2.mul hf.base.err)).add
      ((hz2.pow 3).mul (((cksBBField_diff hz hf.base h0).sub
        (contDiffAt_const.mul (tensorCrossField_diff hz hf h0))).add (tensorQuadField_diff hz hf h0))))

lemma tensorEtaField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) (hd : 0 < tensorDenField z f x) (a : A) :
    ContDiffAt ℝ 2 (fun y => tensorEtaField z f y a) x := by
  have hH := (cksHField_diff hz hf.base h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (tensorLapseField_diff hz hf h0 hd).mul ((contDiffAt_pi.mp hf.kb a).sub
    (ContDiffAt.sum fun b _ => (contDiffAt_pi.mp hH b).mul (component_diff (tensorKField_diff hz hf) b a)))

lemma tensorTauField_diff {z : Point → ℝ} {f : TensorFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f.base x) ≠ 0) :
    ContDiffAt ℝ 2 (tensorTauField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hmg := hf.base.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have heg := hf.base.eg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hq := (cksQField_diff hz hf.base).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (((hf.base.mK.sub hmg).add (hz2.smul (hf.base.ek.sub heg))).sub
    ((cksTField_diff hz hf.base h0).smul hq))

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem cks_normalized_mass_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MassFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x → matrixThreeJets f.sigma x ∈ K →
      ‖matrixThreeJets f.sigma x‖ ≤ B → ‖matrixThreeJets f.mg x‖ ≤ B →
      ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.mK x‖ ≤ B → ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.mr x‖ ≤ B → ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6 →
      determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 →
      1+(radiusPower (-1) x)^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x ≠ 0 →
      ‖actualScalarJet (cksFField (radiusPower (-1)) (normalizeMassLogFields f)) x-
        actualScalarJet (cksLeadingField f) x‖ ≤ C/Real.exp (x 0) := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_mass_uniform_bounded hK hreg (216*B)
  refine ⟨R,hR,C,hC,?_⟩
  intro f x hr hf hσ hs hmg heg hmk hek hb hmr herr h0 hV
  have hn := normalizeMassLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  have hσ0 : determinant (f.sigma x) ≠ 0 := hreg _ hσ
  have hnB := normalized_log_mass_input_bound hB hf hs hmg heg hmk hek hb hmr herr
  rw [cksFField_realized hz hn h0 hV,cksLeadingField_realized hf hσ0]
  have hleading : leadingMassJet (massInputOf (normalizeMassLogFields f) x) = leadingMassJet (massInputOf f x) := rfl
  rw [← hleading]
  exact hh (Real.exp (x 0)) (actualThreeJet (radiusPower (-1)) x)
    (massInputOf (normalizeMassLogFields f) x) hr (inverse_radius_three_norm x) hσ hnB

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_inverse_smul {r : ℝ} (hr : r ≠ 0) (q p : Mat) :
    traceProduct (inverse (r • q)) p = (1/r)*traceProduct (inverse q) p := by
  have hi : inverse (r • q) = (1/r) • inverse q := by
    funext i k
    rw [inverse_smul _ _ hr]
    dsimp; ring
  exact hi ▸ traceProduct_smul_left (1/r) (inverse q) p

lemma log_lie_coefficient {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0) :
    normalizedLie (logGamma f) (logShift f) x =
      (1/Real.exp (x 0))^3 • cksLieField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  rw [logGamma_normalized,logShift_normalized]
  have hn := normalizeMassLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  have hq := cksQField_diff hz hn
  have hH := cksHField_diff hz hn h0
  funext i k
  rw [normalizedLie_radius 2 (-5) hq hH i k,radiusPower_two,radiusPower_minus_five]
  change (Real.exp (x 0)^2*(1/Real.exp (x 0)^5))*
    normalizedLie (cksQField (radiusPower (-1)) (normalizeMassLogFields f))
        (cksHField (radiusPower (-1)) (normalizeMassLogFields f)) x i k =
    (1/Real.exp (x 0))^3*normalizedLie (cksQField (radiusPower (-1)) (normalizeMassLogFields f))
        (cksHField (radiusPower (-1)) (normalizeMassLogFields f)) x i k
  have hr := Real.exp_ne_zero (x 0)
  field_simp

lemma log_expansion_coefficient {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0) :
    logExpansion f x =
      1+(1/Real.exp (x 0))^3*cksDField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  let r := Real.exp (x 0)
  let z := 1/r
  let g := normalizeMassLogFields f
  let q := cksQField (radiusPower (-1)) g x
  let a : Mat := (-3:ℝ) • g.mg x+z • (g.er x-(2:ℝ) • g.eg x-cksLieField (radiusPower (-1)) g x)
  have hr : r ≠ 0 := Real.exp_ne_zero _
  have hm : logGammaRadial f x-(show Mat from normalizedLie (logGamma f) (logShift f) x) =
      (2*r) • q+(r*z^3) • a := by
    funext i k
    change logGammaRadial f x i k-normalizedLie (logGamma f) (logShift f) x i k =
      (2*r)*q i k+(r*z^3)*a i k
    have hrad := congrArg (fun F : Point → Mat => F x i k) (logGammaRadial_normalized f)
    change logGammaRadial f x i k = (2*r)*q i k+r*logScaledQ f x i k at hrad
    have hlie := congrArg (fun M : Mat => M i k) (log_lie_coefficient hf h0)
    change normalizedLie (logGamma f) (logShift f) x i k =
      z^3*cksLieField (radiusPower (-1)) g x i k at hlie
    rw [hrad,hlie]
    change (2*r)*q i k+r*(z^3*((-3)*f.mg x i k+z*(Real.exp (x 0)^2*radialMatrixD f.eg x i k-
      2*(Real.exp (x 0)^2*f.eg x i k))))-z^3*cksLieField (radiusPower (-1)) g x i k =
      (2*r)*q i k+(r*z^3)*((-3)*f.mg x i k+z*(radiusPower 2 x*radialMatrixD f.eg x i k-
        2*(radiusPower 2 x*f.eg x i k)-cksLieField (radiusPower (-1)) g x i k))
    rw [radiusPower_two]
    dsimp only [z,r]
    field_simp
    ring
  have hi : traceProduct (inverse q) q = 2 := inverse_trace q h0
  unfold logExpansion
  rw [hm,logGamma_normalized]
  simp only [radiusPower_two]
  change r/4*traceProduct (inverse (r^2 • q)) ((2*r) • q+(r*z^3) • a) = _
  rw [traceProduct_inverse_smul (pow_ne_zero 2 hr),traceProduct_add,
    traceProduct_smul,traceProduct_smul,hi]
  change _ = 1+z^3*((1/4:ℝ)*traceProduct (inverse q)
    ((-3:ℝ) • g.mg x+radiusPower (-1) x • (g.er x-(2:ℝ) • g.eg x-cksLieField (radiusPower (-1)) g x)))
  rw [radiusPower_inverse]
  change _ = 1+z^3*((1/4:ℝ)*traceProduct (inverse q) a)
  dsimp only [z]
  field_simp
  ring

lemma log_physical_mass_eq {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0)
    (hpos : 0 < logSchur f x) :
    logPhysicalMass f x = cksFField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hr := Real.exp_ne_zero (x 0)
  have hsch := log_schur_coefficient f x
  have hp : 0 < 1+(1/Real.exp (x 0))^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x := by
    rw [← hsch]
    positivity
  have hU : (1/Real.sqrt (logSchur f x))^2 =
      (1+Real.exp (x 0)^2)/(1+(1/Real.exp (x 0))^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x) := by
    rw [div_pow,one_pow,Real.sq_sqrt hpos.le,← hsch]
    have hn : 1+Real.exp (x 0)^2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  have hT := log_trace_coefficient h0
  have hd := log_expansion_coefficient hf h0
  have ht' : Real.exp (x 0)/2*traceProduct (inverse (logGamma f x)) (logTangentialK f x) =
      Real.exp (x 0)*(1+(1/Real.exp (x 0))^3*cksTField (radiusPower (-1)) (normalizeMassLogFields f) x) := by
    rw [← hT]
    ring
  unfold logPhysicalMass
  rw [ht',mul_pow (1/Real.sqrt (logSchur f x)),hU,hd]
  unfold cksFField normalizedMassField massNumeratorField
  rw [radiusPower_inverse]
  simpa only [mul_assoc] using CKSAngularGeometry.physical_mass_normalized
    (D := cksDField (radiusPower (-1)) (normalizeMassLogFields f) x)
    (T := cksTField (radiusPower (-1)) (normalizeMassLogFields f) x) hr hp.ne'

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def normalizeTensorLogFields (f : TensorFields) : TensorFields where
  base := normalizeMassLogFields f.base
  kr := fun y => radiusPower 5 y*f.kr y
  kb := fun y => radiusPower 3 y • f.kb y

lemma logTensorK_normalized (f : TensorFields) (y : Point) :
    tensorKField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      (Real.exp (y 0)^2)⁻¹ • logTangentialK f.base y := by
  ext i k
  unfold tensorKField normalizeTensorLogFields normalizeMassLogFields logTangentialK
  simp only [radiusPower_inverse,radiusPower_two]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logLapseSq_normalized {f : TensorFields} {y : Point} (hs : 0 < logSchur f.base y) :
    tensorLapseSqField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      (1/Real.sqrt (logSchur f.base y))^2/Real.exp (y 0)^2 := by
  have hd := log_schur_coefficient f.base y
  unfold tensorLapseSqField tensorDenField
  change (1+radiusPower (-1) y^2)*(1+radiusPower (-1) y^3*
    cksVField (radiusPower (-1)) (normalizeMassLogFields f.base) y)⁻¹ = _
  rw [radiusPower_inverse,← hd]
  simp only [div_pow,one_pow,Real.sq_sqrt hs.le]
  have hr := Real.exp_ne_zero (y 0)
  have hrr : 1+Real.exp (y 0)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

lemma logLapse_normalized {f : TensorFields} {y : Point} (hs : 0 < logSchur f.base y) :
    tensorLapseField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      (1/Real.sqrt (logSchur f.base y))/Real.exp (y 0) := by
  have hd := log_schur_coefficient f.base y
  have hden : 0 < tensorDenField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
    unfold tensorDenField
    change 0 < 1+radiusPower (-1) y^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f.base) y
    rw [radiusPower_inverse,← hd]
    positivity
  have ht := logLapseSq_normalized (f := f) hs
  have heq : (tensorLapseField (radiusPower (-1)) (normalizeTensorLogFields f) y)^2 =
      tensorLapseSqField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
    unfold tensorLapseField tensorLapseSqField
    rw [mul_pow,Real.sq_sqrt (by positivity),inv_pow,Real.sq_sqrt hden.le]
  rw [ht,← div_pow] at heq
  have hleft : 0 ≤ tensorLapseField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
    unfold tensorLapseField
    positivity
  have hright : 0 ≤ (1/Real.sqrt (logSchur f.base y))/Real.exp (y 0) := by positivity
  nlinarith [sq_nonneg (tensorLapseField (radiusPower (-1)) (normalizeTensorLogFields f) y-
    (1/Real.sqrt (logSchur f.base y))/Real.exp (y 0))]

lemma radiusPower_minus_three (y : Point) : radiusPower (-3) y = 1/Real.exp (y 0)^3 :=
  radiusPower_neg_nat 3 y

lemma logOriginalEta_normalized {f : TensorFields} {y : Point} (hs : 0 < logSchur f.base y) (a : A) :
    logOriginalEta f y a/Real.exp (y 0) =
      radiusPower (-3) y*tensorEtaField (radiusPower (-1)) (normalizeTensorLogFields f) y a := by
  unfold logOriginalEta tensorEtaField
  rw [logLapse_normalized hs,logTensorK_normalized]
  have hh := congrFun (logShift_normalized f.base) y
  have hh' (b : A) : cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y b =
      Real.exp (y 0)^5*logShift f.base y b := by
    have hb := congrFun hh b
    rw [radiusPower_minus_five] at hb
    dsimp at hb
    have hr := Real.exp_ne_zero (y 0)
    field_simp at hb ⊢
    nlinarith
  change _ = radiusPower (-3) y*((1/Real.sqrt (logSchur f.base y))/Real.exp (y 0)*
    (radiusPower 3 y*f.kb y a-∑ b, cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y b*
      ((Real.exp (y 0)^2)⁻¹*logTangentialK f.base y b a)))
  simp only [hh',radiusPower_minus_three,radiusPower_three]
  rw [show (∑ b, Real.exp (y 0)^5*logShift f.base y b*((Real.exp (y 0)^2)⁻¹*logTangentialK f.base y b a)) =
    Real.exp (y 0)^3*∑ b, logShift f.base y b*logTangentialK f.base y b a from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      have hr := Real.exp_ne_zero (y 0)
      field_simp]
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logOriginalTau_normalized {f : TensorFields} {y : Point}
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y) ≠ 0) :
    (Real.exp (y 0)^2)⁻¹ • logOriginalTau f y = radiusPower (-3) y •
      tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
  have ht := log_trace_coefficient h0
  have ht' : traceProduct (inverse (logGamma f.base y)) (logTangentialK f.base y)/2 =
      1+(1/Real.exp (y 0))^3*cksTField (radiusPower (-1)) (normalizeMassLogFields f.base) y := by linarith [ht]
  unfold logOriginalTau tensorTauField
  rw [ht',logGamma_normalized,logTangentialK_normalized]
  ext i k
  change (Real.exp (y 0)^2)⁻¹*(Real.exp (y 0)^2*
    (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y i k+
      (1/Real.exp (y 0))^3*(f.base.mK y i k-f.base.mg y i k+
        1/Real.exp (y 0)*(Real.exp (y 0)^2*f.base.ek y i k-Real.exp (y 0)^2*f.base.eg y i k)))-
    (1+(1/Real.exp (y 0))^3*cksTField (radiusPower (-1)) (normalizeMassLogFields f.base) y)*
      (radiusPower 2 y*cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y i k)) = _
  unfold normalizeTensorLogFields normalizeMassLogFields
  simp only [radiusPower_inverse,radiusPower_two,radiusPower_minus_three]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp
  ring

lemma logBB_normalized (f : TensorFields) (y : Point) :
    cksBBField (radiusPower (-1)) (normalizeMassLogFields f.base) y =
      Real.exp (y 0)^8*∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b) := by
  unfold cksBBField
  rw [logGamma_normalized]
  simp only [radiusPower_two,CKSAngularGeometry.inverse_smul _ _ (pow_ne_zero 2 (Real.exp_ne_zero (y 0))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y) a b*
    ((radiusPower 3 y*f.base.b y a)*(radiusPower 3 y*f.base.b y b)) = _
  rw [radiusPower_three]
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logShift_coefficient (f : TensorFields) (y : Point) (a : A) :
    cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y a =
      Real.exp (y 0)^5*logShift f.base y a := by
  have h := congrFun (congrFun (logShift_normalized f.base) y) a
  rw [radiusPower_minus_five] at h
  dsimp at h
  have hr := Real.exp_ne_zero (y 0)
  field_simp at h ⊢
  nlinarith

lemma logCross_normalized (f : TensorFields) (y : Point) :
    tensorCrossField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      Real.exp (y 0)^8*∑ a, logShift f.base y a*f.kb y a := by
  unfold tensorCrossField
  change (∑ a, cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y a*
    (radiusPower 3 y*f.kb y a)) = _
  simp only [logShift_coefficient,radiusPower_three,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma logQuad_normalized (f : TensorFields) (y : Point) :
    tensorQuadField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      Real.exp (y 0)^8*∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b) := by
  unfold tensorQuadField
  rw [logTensorK_normalized]
  change (∑ a, ∑ b, ((Real.exp (y 0)^2)⁻¹*logTangentialK f.base y a b)*
    (cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y a*
      cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y b)) = _
  simp only [logShift_coefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logOriginalL_normalized {f : TensorFields} {y : Point} (hs : 0 < logSchur f.base y) :
    logOriginalL f y-1 = radiusPower (-3) y*
      tensorLField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
  have hU : (1/Real.sqrt (logSchur f.base y))^2*logSchur f.base y = 1 := by
    rw [div_pow,one_pow,Real.sq_sqrt hs.le]
    field_simp
  unfold tensorLField
  erw [logLapseSq_normalized hs,logBB_normalized,logCross_normalized,logQuad_normalized]
  change logOriginalL f y-1 = radiusPower (-3) y*((1/Real.sqrt (logSchur f.base y))^2/Real.exp (y 0)^2*
    (radiusPower 5 y*f.kr y-f.base.mr y-radiusPower (-1) y*(radiusPower 6 y*f.base.err y)+
      radiusPower (-1) y^3*(Real.exp (y 0)^8*(∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b))-
        2*(Real.exp (y 0)^8*(∑ a, logShift f.base y a*f.kb y a))+
        Real.exp (y 0)^8*(∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b)))))
  have h5 : radiusPower 5 y = Real.exp (y 0)^5 := radiusPower_nat 5 y
  rw [radiusPower_minus_three,radiusPower_inverse,h5,radiusPower_six]
  have hS : logSchur f.base y = logSchur f.base y := rfl
  change logSchur f.base y = logRadialMetric f.base y-
    ∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b) at hS
  unfold logRadialMetric at hS
  unfold logOriginalL logRadialK
  have hr := Real.exp_ne_zero (y 0)
  have hcoeff :
      (1/Real.exp (y 0)^3)*((1/Real.sqrt (logSchur f.base y))^2/Real.exp (y 0)^2*
      (Real.exp (y 0)^5*f.kr y-f.base.mr y-1/Real.exp (y 0)*(Real.exp (y 0)^6*f.base.err y)+
      (1/Real.exp (y 0))^3*(Real.exp (y 0)^8*(∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b))-
        2*(Real.exp (y 0)^8*(∑ a, logShift f.base y a*f.kb y a))+
        Real.exp (y 0)^8*(∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b))))) =
      (1/Real.sqrt (logSchur f.base y))^2*(f.kr y-f.base.mr y/Real.exp (y 0)^5-f.base.err y+
        (∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b))-
        2*(∑ a, logShift f.base y a*f.kb y a)+
        (∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b))) := by
    field_simp; ring
  rw [hcoeff]
  nlinarith [hU]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def logLapse (f : MassFields) : Point → ℝ := fun y => 1/Real.sqrt (logSchur f y)
def logU (f : MassFields) : Point → ℝ := fun y => logLapse f y*logExpansion f y

lemma foliationDenField_positive {f : MassFields} {x : Point} (h : 0 < logSchur f x) :
    0 < foliationDenField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  change 0 < 1+radiusPower (-1) x^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x
  rw [radiusPower_inverse,← log_schur_coefficient]
  positivity
lemma log_lapse_normalized {f : MassFields} {x : Point} (h : 0 < logSchur f x) :
    logLapse f x/Real.sqrt (1+Real.exp (x 0)^2)-1 =
      radiusPower (-3) x*lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hden := foliationDenField_positive h
  have heq : logLapse f x/Real.sqrt (1+Real.exp (x 0)^2) =
      (Real.sqrt (foliationDenField (radiusPower (-1)) (normalizeMassLogFields f) x))⁻¹ := by
    unfold logLapse foliationDenField
    rw [radiusPower_inverse,← log_schur_coefficient,Real.sqrt_mul (by positivity)]
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  have hz3 : radiusPower (-1) x^3 = radiusPower (-3) x := by
    rw [radiusPower_inverse,radiusPower_minus_three]
    ring
  have hh := reciprocal_sqrt_factor (z := radiusPower (-1) x)
    (V := cksVField (radiusPower (-1)) (normalizeMassLogFields f) x) hden
  simpa only [foliationDenField,lapseCorrectionField,hz3] using hh
lemma log_u_normalized {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0)
    (h : 0 < logSchur f x) :
    logU f x/Real.sqrt (1+Real.exp (x 0)^2)-1 =
      radiusPower (-3) x*uCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hl := log_lapse_normalized h
  have hd := log_expansion_coefficient hf h0
  have hz3 : (1/Real.exp (x 0))^3 = radiusPower (-3) x := by rw [radiusPower_minus_three]; ring
  rw [hz3] at hd
  unfold logU uCorrectionField
  rw [hd]
  rw [radiusPower_inverse,hz3]
  rw [mul_div_right_comm,show logLapse f x/Real.sqrt (1+Real.exp (x 0)^2) =
    1+radiusPower (-3) x*lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) x by linarith]
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma logMetric_normalized_positive {f : MassFields} {x : Point}
    (h : (logMetric f x).PosDef) :
    (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x).PosDef ∧ 0 < logSchur f x := by
  constructor
  · have hγ : (logGamma f x).PosDef := CKSAngularGeometry.metricBlock_leaf_posDef h
    have he : cksQField (radiusPower (-1)) (normalizeMassLogFields f) x =
        (1/Real.exp (x 0)^2) • logGamma f x := by
      rw [logGamma_normalized]
      simp only [radiusPower_two]
      rw [smul_smul]
      have hc : (1/Real.exp (x 0)^2)*Real.exp (x 0)^2=1 := by
        have hr := Real.exp_ne_zero (x 0)
        field_simp
      rw [hc,one_smul]
    rw [he]
    exact hγ.smul (one_div_pos.mpr (by positivity))
  · exact CKSAngularGeometry.metricBlock_schur_positive h

lemma MassFields.RegularAt.eventually {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    ∀ᶠ y in 𝓝 x, f.RegularAt y := by
  filter_upwards [hf.sigma.eventually (by norm_num),hf.mg.eventually (by norm_num),
    hf.eg.eventually (by norm_num),hf.er.eventually (by norm_num),
    hf.mK.eventually (by norm_num),hf.ek.eventually (by norm_num),
    hf.b.eventually (by norm_num),hf.mr.eventually (by norm_num),hf.err.eventually (by norm_num)]
    with y hs hm he her hk hek hb hr herr
  exact ⟨hs,hm,he,her,hk,hek,hb,hr,herr⟩

lemma log_physical_mass_jet_eq {f : MassFields} {x : Point}
    (hf : f.RegularAt x) (hp : ∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) :
    actualScalarJet (logPhysicalMass f) x =
      actualScalarJet (cksFField (radiusPower (-1)) (normalizeMassLogFields f)) x := by
  apply actualScalarJet_congr
  filter_upwards [hf.eventually,hp] with y hy hpy
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hpy
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  exact log_physical_mass_eq hy hd hs

theorem cks_physical_mass_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MassFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) → matrixThreeJets f.sigma x ∈ K →
      ‖matrixThreeJets f.sigma x‖ ≤ B → ‖matrixThreeJets f.mg x‖ ≤ B →
      ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.mK x‖ ≤ B → ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.mr x‖ ≤ B → ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6 →
      ‖actualScalarJet (logPhysicalMass f) x-actualScalarJet (cksLeadingField f) x‖ ≤
        C/Real.exp (x 0) := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_normalized_mass_mixed hK hreg hB
  refine ⟨R,hR,C,hC,?_⟩
  intro f x hr hf hp hσ hs hmg heg hmk hek hb hmr herr
  obtain ⟨hq,hS⟩ := logMetric_normalized_positive
    (Filter.Eventually.self_of_nhds (x := x) (p := fun y : Point => (logMetric f y).PosDef) hp)
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  have hV : 1+(radiusPower (-1) x)^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x ≠ 0 := by
    rw [radiusPower_inverse,← log_schur_coefficient]
    exact ne_of_gt (mul_pos (by positivity) hS)
  rw [log_physical_mass_jet_eq hf hp]
  exact hh f x hr hf hσ hs hmg heg hmk hek hb hmr herr hd hV

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

attribute [local irreducible] cksMassJet leadingMassJet

lemma leadingMassJet_continuousAt {j : MassInput}
    (h : determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ContinuousAt leadingMassJet j := by
  have hr := massRegion_zero h
  have hm := (cksMassJet_smooth hr.1 hr.2).continuousAt.comp
    (show ContinuousAt (fun i : MassInput => ((0:ScalarThreeJet),i)) j from by fun_prop)
  change ContinuousAt (fun i : MassInput => cksMassJet 0 i) j at hm
  have he : (fun i : MassInput => cksMassJet 0 i) = (fun i => leadingMassJet i) := funext (fun i => cksMassJet_zero i)
  rw [he] at hm
  exact hm

lemma leading_mass_uniform_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : MassInput, j.1 0 ∈ K → ‖j‖ ≤ B → ‖leadingMassJet j‖ ≤ C := by
  obtain ⟨C,hC⟩ := (boundedMassFamily_compact hK B).exists_bound_of_continuousOn
    (fun j hj => (leadingMassJet_continuousAt (hreg _ hj.1)).continuousWithinAt)
  exact ⟨max C 0,le_max_right _ _,fun j hj hb => (hC j (boundedMassFamily_mem hj hb)).trans (le_max_left _ _)⟩

lemma cks_leading_mixed_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MassFields, ∀ x : Point,
      f.RegularAt x → matrixThreeJets f.sigma x ∈ K →
      ‖matrixThreeJets f.sigma x‖ ≤ B → ‖matrixThreeJets f.mg x‖ ≤ B →
      ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.mK x‖ ≤ B → ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.mr x‖ ≤ B → ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6 →
      ‖actualScalarJet (cksLeadingField f) x‖ ≤ C := by
  obtain ⟨C,hC,hh⟩ := leading_mass_uniform_bounded hK hreg (216*B)
  refine ⟨C,hC,?_⟩
  intro f x hf hσ hs hmg heg hmk hek hb hmr herr
  have hd : determinant (f.sigma x) ≠ 0 := hreg _ hσ
  have hn := normalizeMassLogFields_regular hf
  have hbound := normalized_log_mass_input_bound hB hf hs hmg heg hmk hek hb hmr herr
  have hreal := cksLeadingField_realized hn hd
  change actualScalarJet (cksLeadingField f) x=leadingMassJet (massInputOf (normalizeMassLogFields f) x) at hreal
  rw [hreal]
  exact hh _ hσ hbound

lemma logQError_three_bound {f : MassFields} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hr : 1 ≤ Real.exp (x 0)) (hf : f.RegularAt x)
    (hm : ‖matrixThreeJets f.mg x‖ ≤ B)
    (he : ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2) (a b : A) :
    ‖actualThreeJet (fun y => logQError f y a b) x‖ ≤ 280*B/Real.exp (x 0)^3 := by
  have hmab := (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans hm)
  have heab := (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans he)
  have h3 : ‖actualThreeJet (radiusPower (-3)) x‖ ≤ 27/Real.exp (x 0)^3 := by
    have hh := radiusPower_three_norm (-3) x
    norm_num only [abs_neg,abs_of_pos (show (0:ℝ)<3 by norm_num),max_eq_right (show (1:ℝ)≤3 by norm_num),radiusPower_minus_three] at hh
    norm_num at hh
    exact hh
  have h2 : ‖actualThreeJet (radiusPower (-2)) x‖ ≤ 8/Real.exp (x 0)^2 := by
    have hh := radiusPower_three_norm (-2) x
    norm_num only [abs_neg,abs_of_pos (show (0:ℝ)<2 by norm_num),max_eq_right (show (1:ℝ)≤2 by norm_num)] at hh
    rw [show (-2:ℝ)=-(2:ℕ) by norm_num,radiusPower_neg_nat] at hh
    norm_num at hh
    exact hh
  change ‖actualThreeJet (fun y => radiusPower (-3) y*f.mg y a b+radiusPower (-2) y*f.eg y a b) x‖ ≤ _
  rw [actualThreeJet_add ((radiusPower_diff (-3) 3 x).mul (component_diff hf.mg a b))
    ((radiusPower_diff (-2) 3 x).mul (component_diff hf.eg a b)),
    actualThreeJet_mul (radiusPower_diff (-3) 3 x) (component_diff hf.mg a b),
    actualThreeJet_mul (radiusPower_diff (-2) 3 x) (component_diff hf.eg a b)]
  have hraw := (norm_add_le _ _).trans (add_le_add (productThreeJet_norm h3 hmab) (productThreeJet_norm h2 heab))
  apply hraw.trans
  have hp : Real.exp (x 0)^3 ≤ Real.exp (x 0)^4 := by
    simpa only [pow_succ,mul_one] using mul_le_mul_of_nonneg_left hr (show 0≤Real.exp (x 0)^3 by positivity)
  have hdec : B/Real.exp (x 0)^4 ≤ B/Real.exp (x 0)^3 :=
    div_le_div_of_nonneg_left hB (by positivity) hp
  have hid : 8*(27/Real.exp (x 0)^3)*B+8*(8/Real.exp (x 0)^2)*(B/Real.exp (x 0)^2) =
      216*B/Real.exp (x 0)^3+64*(B/Real.exp (x 0)^4) := by ring
  rw [hid]
  calc
    _ ≤ 216*B/Real.exp (x 0)^3+64*(B/Real.exp (x 0)^3) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdec (show (0:ℝ) ≤ 64 by norm_num))
    _ = _ := by ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma normalizeTensorLogFields_regular {f : TensorFields} {x : Point} (hf : f.RegularAt x) :
    (normalizeTensorLogFields f).RegularAt x := by
  exact ⟨normalizeMassLogFields_regular hf.base,(radiusPower_diff 5 2 x).mul hf.kr,
    (radiusPower_diff 3 2 x).smul hf.kb⟩

lemma normalize_tensor_kr_bound {f : TensorFields} {x : Point} {B : ℝ}
    (hf : f.RegularAt x) (h : ‖actualScalarJet f.kr x‖ ≤ B/Real.exp (x 0)^5) :
    ‖actualScalarJet (normalizeTensorLogFields f).kr x‖ ≤ 100*B := by
  have hh := normalize_two_bound hf.kr h
  norm_num at hh
  exact hh

lemma normalize_tensor_kb_bound {f : TensorFields} {x : Point} {B : ℝ} (hB : 0 ≤ B)
    (hf : f.RegularAt x) (h : ‖fun a => actualScalarJet (fun y => f.kb y a) x‖ ≤ B/Real.exp (x 0)^3) :
    ‖fun a => actualScalarJet (fun y => (normalizeTensorLogFields f).kb y a) x‖ ≤ 36*B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  have hh := normalize_two_bound (contDiffAt_pi.mp hf.kb a) ((norm_le_pi_norm _ a).trans h)
  norm_num at hh
  exact hh

lemma tensorDenField_positive {f : TensorFields} {x : Point} (h : 0 < logSchur f.base x) :
    0 < tensorDenField (radiusPower (-1)) (normalizeTensorLogFields f) x := by
  change 0 < 1+radiusPower (-1) x^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f.base) x
  rw [radiusPower_inverse,← log_schur_coefficient]
  positivity

lemma minus_three_product_bound {g : Point → ℝ} {x : Point} {C : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hC : ‖actualScalarJet g x‖ ≤ C) :
    ‖actualScalarJet (fun y => radiusPower (-3) y*g y) x‖ ≤ 36*C/Real.exp (x 0)^3 := by
  rw [actualScalarJet_mul (radiusPower_diff (-3) 2 x) hg]
  have hz : ‖actualScalarJet (radiusPower (-3)) x‖ ≤ 9/Real.exp (x 0)^3 := by
    have hh := radiusPower_two_norm (-3) x
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 3),
      max_eq_right (by norm_num : (1:ℝ) ≤ 3),radiusPower_minus_three] at hh
    norm_num at hh
    exact hh
  exact (productJet_norm hz hC).trans_eq (by ring)

theorem cks_physical_tensor_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : TensorFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) → matrixThreeJets f.base.sigma x ∈ K →
      ‖matrixThreeJets f.base.sigma x‖ ≤ B → ‖matrixThreeJets f.base.mg x‖ ≤ B →
      ‖matrixThreeJets f.base.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.base.mK x‖ ≤ B → ‖matrixScalarJets f.base.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.base.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.base.mr x‖ ≤ B → ‖actualScalarJet f.base.err x‖ ≤ B/Real.exp (x 0)^6 →
      ‖actualScalarJet f.kr x‖ ≤ B/Real.exp (x 0)^5 →
      ‖fun a => actualScalarJet (fun y => f.kb y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet (fun y => logOriginalL f y-1) x‖ ≤ C/Real.exp (x 0)^3 ∧
      (∀ a, ‖actualScalarJet (fun y => logOriginalEta f y a/Real.exp (y 0)) x‖ ≤ C/Real.exp (x 0)^3) ∧
      (∀ a b, ‖actualScalarJet (fun y => logOriginalTau f y a b/Real.exp (y 0)^2) x‖ ≤ C/Real.exp (x 0)^3) := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_tensor_coefficients_bounded hK hreg (216*B)
  refine ⟨R,hR,36*C,by positivity,?_⟩
  intro f x hr hf hp hσ hs hmg heg hmk hek hb hmr herr hkr hkb
  have hn := normalizeTensorLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  obtain ⟨hq,hS⟩ := logMetric_normalized_positive hp.self_of_nhds
  have h0 : determinant (cksQField (radiusPower (-1)) (normalizeTensorLogFields f).base x) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  have hden := tensorDenField_positive (f := f) hS
  have hnB := normalized_log_mass_input_bound hB hf.base hs hmg heg hmk hek hb hmr herr
  have hnkr : ‖actualScalarJet (normalizeTensorLogFields f).kr x‖ ≤ 216*B :=
    (normalize_tensor_kr_bound hf hkr).trans (by linarith)
  have hnkb : ‖fun a => actualScalarJet (fun y => (normalizeTensorLogFields f).kb y a) x‖ ≤ 216*B :=
    (normalize_tensor_kb_bound hB hf hkb).trans (by linarith)
  have ht := hh (Real.exp (x 0)) (actualThreeJet (radiusPower (-1)) x)
    (tensorInputOf (normalizeTensorLogFields f) x) hr (inverse_radius_three_norm x) hσ hnB hnkr hnkb
  obtain ⟨hL,hET⟩ := norm_prod_le_iff.mp ht
  obtain ⟨hE,hT⟩ := norm_prod_le_iff.mp hET
  have hL' : ‖actualScalarJet (tensorLField (radiusPower (-1)) (normalizeTensorLogFields f)) x‖ ≤ C := by
    rw [actual_tensorL hz hn h0 hden]
    exact hL
  have hE' (a : A) : ‖actualScalarJet (fun y => tensorEtaField (radiusPower (-1)) (normalizeTensorLogFields f) y a) x‖ ≤ C := by
    rw [actual_tensorEta hz hn h0 hden]
    exact (norm_le_pi_norm _ a).trans hE
  have hT' (a b : A) : ‖actualScalarJet (fun y => tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b) x‖ ≤ C := by
    have hm := actual_tensorTau hz hn h0
    have hab := congrFun (congrFun hm a) b
    rw [show actualScalarJet (fun y => tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b) x = _ from hab]
    exact (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans hT)
  have hSnear : ∀ᶠ y in 𝓝 x, 0 < logSchur f.base y := by
    filter_upwards [hp] with y hy using (logMetric_normalized_positive hy).2
  refine ⟨?_,?_,?_⟩
  · have heq : actualScalarJet (fun y => logOriginalL f y-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*tensorLField (radiusPower (-1)) (normalizeTensorLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hSnear] with y hy using logOriginalL_normalized hy
    rw [heq]
    exact minus_three_product_bound (tensorLField_diff hz hn h0 hden) hL'
  · intro a
    have heq : actualScalarJet (fun y => logOriginalEta f y a/Real.exp (y 0)) x =
        actualScalarJet (fun y => radiusPower (-3) y*tensorEtaField (radiusPower (-1)) (normalizeTensorLogFields f) y a) x := by
      apply actualScalarJet_congr
      filter_upwards [hSnear] with y hy using logOriginalEta_normalized hy a
    rw [heq]
    exact minus_three_product_bound (tensorEtaField_diff hz hn h0 hden a) (hE' a)
  · intro a b
    have heq : actualScalarJet (fun y => logOriginalTau f y a b/Real.exp (y 0)^2) x =
        actualScalarJet (fun y => radiusPower (-3) y*tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b) x := by
      apply actualScalarJet_congr
      filter_upwards [hp] with y hy
      have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y) ≠ 0 := by
        rw [determinant_eq]
        exact (logMetric_normalized_positive hy).1.det_pos.ne'
      have h := congrFun (congrFun (logOriginalTau_normalized hd) a) b
      change (Real.exp (y 0)^2)⁻¹*logOriginalTau f y a b = radiusPower (-3) y*
        tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b at h
      simpa only [div_eq_mul_inv,mul_comm] using h
    rw [heq]
    exact minus_three_product_bound (component_diff (tensorTauField_diff hz hn h0) a b) (hT' a b)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma minus_five_product_bound {g : Point → ℝ} {x : Point} {C : ℝ}
    (hg : ContDiffAt ℝ 3 g x) (hC : ‖actualThreeJet g x‖ ≤ C) :
    ‖actualThreeJet (fun y => radiusPower (-5) y*g y) x‖ ≤ 1000*C/Real.exp (x 0)^5 := by
  rw [actualThreeJet_mul (radiusPower_diff (-5) 3 x) hg]
  have hz : ‖actualThreeJet (radiusPower (-5)) x‖ ≤ 125/Real.exp (x 0)^5 := by
    have hh := radiusPower_three_norm (-5) x
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 5),
      max_eq_right (by norm_num : (1:ℝ) ≤ 5),radiusPower_minus_five] at hh
    norm_num at hh
    exact hh
  exact (productThreeJet_norm hz hC).trans_eq (by ring)

attribute [local irreducible] coefficientD coefficientT coefficientShift lapseCorrection uCorrection

theorem cks_physical_foliation_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MassFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) → matrixThreeJets f.sigma x ∈ K →
      ‖matrixThreeJets f.sigma x‖ ≤ B → ‖matrixThreeJets f.mg x‖ ≤ B →
      ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.mK x‖ ≤ B → ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.mr x‖ ≤ B → ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6 →
      ‖actualScalarJet (fun y => logExpansion f y-1) x‖ ≤ C/Real.exp (x 0)^3 ∧
      ‖actualScalarJet (fun y => logT f y-1) x‖ ≤ C/Real.exp (x 0)^3 ∧
      (∀ a, ‖actualThreeJet (fun y => logShift f y a) x‖ ≤ C/Real.exp (x 0)^5) ∧
      ‖actualScalarJet (fun y => logLapse f y/Real.sqrt (1+Real.exp (y 0)^2)-1) x‖ ≤ C/Real.exp (x 0)^3 ∧
      ‖actualScalarJet (fun y => logU f y/Real.sqrt (1+Real.exp (y 0)^2)-1) x‖ ≤ C/Real.exp (x 0)^3 := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_foliation_coefficients_bounded hK hreg (216*B)
  refine ⟨R,hR,1000*C,by positivity,?_⟩
  intro f x hr hf hp hσ hs hmg heg hmk hek hb hmr herr
  have hn := normalizeMassLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  obtain ⟨hq,hS⟩ := logMetric_normalized_positive hp.self_of_nhds
  have h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  have hden := foliationDenField_positive (f := f) hS
  have hnB := normalized_log_mass_input_bound hB hf hs hmg heg hmk hek hb hmr herr
  have ht := hh (Real.exp (x 0)) (actualThreeJet (radiusPower (-1)) x)
    (massInputOf (normalizeMassLogFields f) x) hr (inverse_radius_three_norm x) hσ hnB
  simp only [foliationCoefficients] at ht
  obtain ⟨hD,hrest⟩ := norm_prod_le_iff.mp ht
  obtain ⟨hT,hrest⟩ := norm_prod_le_iff.mp hrest
  obtain ⟨hH,hrest⟩ := norm_prod_le_iff.mp hrest
  obtain ⟨hL,hW⟩ := norm_prod_le_iff.mp hrest
  have hD' : ‖actualScalarJet (cksDField (radiusPower (-1)) (normalizeMassLogFields f)) x‖ ≤ C := by
    rw [cksDField_realized hz hn h0]; exact hD
  have hT' : ‖actualScalarJet (cksTField (radiusPower (-1)) (normalizeMassLogFields f)) x‖ ≤ C := by
    rw [cksTField_realized hz hn h0]; exact hT
  have hH' (a : A) : ‖actualThreeJet (fun y => cksHField (radiusPower (-1)) (normalizeMassLogFields f) y a) x‖ ≤ C := by
    rw [congrFun (cksHField_realized hz hn h0) a]
    exact (norm_le_pi_norm _ a).trans hH
  have hL' : ‖actualScalarJet (lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f)) x‖ ≤ C := by
    rw [actual_lapseCorrection hz hn h0 hden]; exact hL
  have hW' : ‖actualScalarJet (uCorrectionField (radiusPower (-1)) (normalizeMassLogFields f)) x‖ ≤ C := by
    rw [actual_uCorrection hz hn h0 hden]; exact hW
  have hsmall : 36*C/Real.exp (x 0)^3 ≤ 1000*C/Real.exp (x 0)^3 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hnear : ∀ᶠ y in 𝓝 x, determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 ∧
      0 < logSchur f y := by
    filter_upwards [hp] with y hy
    obtain ⟨hq,hs⟩ := logMetric_normalized_positive hy
    exact ⟨by rw [determinant_eq]; exact hq.det_pos.ne',hs⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · have heq : actualScalarJet (fun y => logExpansion f y-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*cksDField (radiusPower (-1)) (normalizeMassLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear,hf.eventually] with y hy hfy
      rw [log_expansion_coefficient hfy hy.1,radiusPower_minus_three]
      ring
    rw [heq]
    exact (minus_three_product_bound (cksDField_diff hz hn h0) hD').trans hsmall
  · have heq : actualScalarJet (fun y => logT f y-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*cksTField (radiusPower (-1)) (normalizeMassLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear] with y hy
      unfold logT
      rw [log_trace_coefficient hy.1,radiusPower_minus_three]
      ring
    rw [heq]
    exact (minus_three_product_bound (cksTField_diff hz hn h0) hT').trans hsmall
  · intro a
    have heq : (fun y => logShift f y a) = fun y =>
        radiusPower (-5) y*cksHField (radiusPower (-1)) (normalizeMassLogFields f) y a := by
      rw [logShift_normalized]; rfl
    rw [heq]
    exact minus_five_product_bound (contDiffAt_pi.mp (cksHField_diff hz hn h0) a) (hH' a)
  · have heq : actualScalarJet (fun y => logLapse f y/Real.sqrt (1+Real.exp (y 0)^2)-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear] with y hy using log_lapse_normalized hy.2
    rw [heq]
    exact (minus_three_product_bound (lapseCorrectionField_diff hz hn h0 hden) hL').trans hsmall
  · have heq : actualScalarJet (fun y => logU f y/Real.sqrt (1+Real.exp (y 0)^2)-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*uCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear,hf.eventually] with y hy hfy using log_u_normalized hfy hy.1 hy.2
    rw [heq]
    exact (minus_three_product_bound (uCorrectionField_diff hz hn h0 hden) hW').trans hsmall

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma cksLeadingField_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hσ : determinant (f.sigma x) ≠ 0) : ContDiffAt ℝ 2 (cksLeadingField f) x := by
  have hs := inverse_diff_at (hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) hσ
  exact ((hf.mr.const_smul (1/2:ℝ)).add
    ((traceProduct_diff hs (hf.mg.of_le (by norm_num))).const_smul (1/4:ℝ))).add
    ((traceProduct_diff hs hf.mK).const_smul (1/2:ℝ))

lemma cksFField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (hq : determinant (cksQField z f x) ≠ 0)
    (hV : 1+z x^3*cksVField z f x ≠ 0) : ContDiffAt ℝ 2 (cksFField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hd := cksDField_diff hz hf hq
  have ht := cksTField_diff hz hf hq
  have hv := cksVField_diff hz hf hq
  exact ((massNumeratorField_diff hz2 hd ht hv).mul
    ((contDiffAt_const.add ((hz2.pow 3).mul hv)).inv hV)).const_smul (1/2:ℝ)

lemma logPhysicalMass_diff {f : MassFields} {x : Point}
    (hf : f.RegularAt x) (hp : ∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) :
    ContDiffAt ℝ 2 (logPhysicalMass f) x := by
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hp.self_of_nhds
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  have hV : 1+radiusPower (-1) x^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x ≠ 0 := by
    rw [radiusPower_inverse,← log_schur_coefficient]
    positivity
  apply (cksFField_diff (radiusPower_diff (-1) 3 x) (normalizeMassLogFields_regular hf) hd hV).congr_of_eventuallyEq
  filter_upwards [hf.eventually,hp] with y hy hpy
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hpy
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  exact log_physical_mass_eq hy hd hs

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem cks_sourceCollarData_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : TensorFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) → matrixThreeJets f.base.sigma x ∈ K →
      f.LogComponentBound B x → (sourceCollarData f).BoundedAt C x := by
  obtain ⟨Rl,hRl,Cl,hCl,hl⟩ := cks_physical_foliation_mixed hK hreg hB
  obtain ⟨Rt,hRt,Ct,hCt,ht⟩ := cks_physical_tensor_mixed hK hreg hB
  obtain ⟨Rm,hRm,Cm,hCm,hm⟩ := cks_physical_mass_mixed hK hreg hB
  obtain ⟨Cf,hCf,hf⟩ := cks_leading_mixed_bounded hK hreg hB
  let R := max Rl (max Rt Rm)
  let C := 281*B+Cl+Ct+Cm+Cf
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hqC : 280*B ≤ C := by dsimp [C]; linarith
  have hlC : Cl ≤ C := by dsimp [C]; linarith
  have htC : Ct ≤ C := by dsimp [C]; linarith
  have hmC : Cm ≤ C := by dsimp [C]; linarith
  have hfC : Cf ≤ C := by dsimp [C]; linarith
  refine ⟨R,hRl.trans (le_max_left _ _),C,hC,?_⟩
  intro f x hr hregular hp hs hb
  have hrl : Rl ≤ Real.exp (x 0) := (le_max_left _ _).trans hr
  have hrt : Rt ≤ Real.exp (x 0) := (le_max_left Rt Rm).trans ((le_max_right _ _).trans hr)
  have hrm : Rm ≤ Real.exp (x 0) := (le_max_right Rt Rm).trans ((le_max_right _ _).trans hr)
  have hr1 : 1 ≤ Real.exp (x 0) := hRl.trans hrl
  obtain ⟨_,hT,hS,_,_⟩ := hl f.base x hrl hregular.base hp hs hb.sigma hb.mg hb.eg hb.mK hb.ek hb.b hb.mr hb.err
  obtain ⟨hL,hE,hτ⟩ := ht f x hrt hregular hp hs hb.sigma hb.mg hb.eg hb.mK hb.ek hb.b hb.mr hb.err hb.kr hb.kb
  have hF := hm f.base x hrm hregular.base hp hs hb.sigma hb.mg hb.eg hb.mK hb.ek hb.b hb.mr hb.err
  have hfstar := hf f.base x hregular.base hs hb.sigma hb.mg hb.eg hb.mK hb.ek hb.b hb.mr hb.err
  have hscale {a b : ℝ} (hab : a ≤ b) (n : ℕ) : a/Real.exp (x 0)^n ≤ b/Real.exp (x 0)^n :=
    div_le_div_of_nonneg_right hab (by positivity)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a b
    exact ((norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans hb.sigma)).trans hBC
  · intro a b
    exact (logQError_three_bound hB hr1 hregular.base hb.mg hb.eg a b).trans (hscale hqC 3)
  · intro a; exact (hS a).trans (hscale hlC 5)
  · exact hT.trans (hscale hlC 3)
  · exact hL.trans (hscale htC 3)
  · change ‖actualScalarJet (fun y => logPhysicalMass f.base y-cksLeadingField f.base y) x‖ ≤ _
    rw [actualScalarJet_sub (logPhysicalMass_diff hregular.base hp)
      (cksLeadingField_diff hregular.base (hreg _ hs))]
    exact hF.trans (by simpa only [pow_one] using hscale hmC 1)
  · exact hfstar.trans hfC
  · intro a; exact (hE a).trans (hscale htC 3)
  · intro a b; exact (hτ a b).trans (hscale htC 3)

end
end CKSMixedGeometry

end

end OAI
end

theorem solution : type_of% @OAI.CKSMixedGeometry.cks_sourceCollarData_bounded := @OAI.CKSMixedGeometry.cks_sourceCollarData_bounded

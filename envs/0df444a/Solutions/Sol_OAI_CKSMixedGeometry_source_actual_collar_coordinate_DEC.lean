-- Prove2me | solution 1 for OAI.CKSMixedGeometry.source_actual_collar_coordinate_DEC
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:28:40.483487+00:00
-- url     : https://prove2.me/submissions/a41f4c9d-0e77-435b-b1d3-1334e666b24f

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSAngularGeometry_bounded_thin_field_map_DEC
import Theorems.Thm_OAI_CKSMixedGeometry_cks_sourceCollarData_bounded

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

lemma component_diff {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) (i k : I) :
    ContDiffAt ℝ 2 (fun y => q y i k) x := by
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

end
end CKSAngularGeometry

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

end
end CKSAngularGeometry

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

lemma productJet_smooth : ContDiff ℝ ∞ (fun j : ScalarJet × ScalarJet => productJet j.1 j.2) := by
  unfold productJet
  fun_prop

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
end CKSAngularGeometry

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

lemma actual_determinantJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) :
    actualScalarJet (fun y => determinant (q y)) x = determinantJet (matrixScalarJets q x) := by
  unfold determinant determinantJet matrixScalarJets
  rw [actualScalarJet_sub ((component_diff hq 0 0).mul (component_diff hq 1 1))
    ((component_diff hq 0 1).mul (component_diff hq 1 0)),
    actualScalarJet_mul (component_diff hq 0 0) (component_diff hq 1 1),
    actualScalarJet_mul (component_diff hq 0 1) (component_diff hq 1 0)]

lemma actual_inverseMatrixJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (i k : I) :
    actualScalarJet (fun y => inverse (q y) i k) x = inverseMatrixJet (matrixScalarJets q x) i k := by
  have hd : ContDiffAt ℝ 2 (fun y => determinant (q y)) x :=
    (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
  have hg : ContDiffAt ℝ 2 (fun y => 1/determinant (q y)) x := contDiffAt_const.div hd h0
  have hi (a b : I) := component_diff hq a b
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
    (h0 : determinant (fun i k => (q i k).1) ≠ 0) (i k : I) :
    ContDiffAt ℝ ∞ (fun p : MatrixScalarJet => inverseMatrixJet p i k) q := by
  have hc : ContDiffAt ℝ ∞ (fun p : MatrixScalarJet =>
      (!![p 1 1, -p 0 1; -p 1 0, p 0 0] : MatrixScalarJet) i k) q := by
    fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  exact productJet_smooth.contDiffAt.comp q
    (hc.prodMk ((reciprocalJet_smooth h0).comp q determinantJet_smooth.contDiffAt))

end
end CKSAngularGeometry

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

lemma productJet_smul_left (c : ℝ) (f g : ScalarJet) : productJet (c • f) g = c • productJet f g := by
  apply Prod.ext
  · change (c*f.1)*g.1 = c*(f.1*g.1)
    ring
  apply Prod.ext
  · funext a
    change (c*f.1)*g.2.1 a+g.1*(c*f.2.1 a) = c*(f.1*g.2.1 a+g.1*f.2.1 a)
    ring
  · funext a b
    change (c*f.1)*g.2.2 a b+g.1*(c*f.2.2 a b)+(c*f.2.1 a)*g.2.1 b+g.2.1 a*(c*f.2.1 b) = c*(f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)
    ring

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
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma normalizedLieJet_smooth (i k : I) : ContDiff ℝ ∞ (fun j : ExpansionInput => normalizedLieJet j i k) := by
  unfold normalizedLieJet
  apply ContDiff.sum
  intro a ha
  exact ((productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.2.2.2.1 a,j.2.1 a i k)))).add
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.1 a k,j.2.2.2.2 i a))))).add
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.1 i a,j.2.2.2.2 k a))))

def actualExpansionInput (q Q : Point → Mat) (S : Point → Point) (x : Point) : ExpansionInput :=
  (matrixScalarJets q x,
    (fun a => matrixScalarJets (fun y i k => D (basis a) (fun z => q z i k) y) x),
    matrixScalarJets Q x,
    (fun a => actualScalarJet (fun y => S y a) x),
    fun a b => actualScalarJet (D (basis a) (fun y => S y b)) x)

lemma component_three {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 3 q x) (i k : I) :
    ContDiffAt ℝ 3 (fun y => q y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

lemma normalizedLie_diff {q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : I) :
    ContDiffAt ℝ 2 (fun y => normalizedLie q S y i k) x := by
  have hSa (a : I) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  apply ContDiffAt.sum
  intro a ha
  exact ((((hSa a).of_le h23).mul (contDiffAt_D (hqa i k) (by norm_num) (basis a))).add
      (((hqa a k).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis i)))).add
      (((hqa i a).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis k)))

lemma actual_normalizedLieJet {q Q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : I) :
    actualScalarJet (fun y => normalizedLie q S y i k) x =
      normalizedLieJet (actualExpansionInput q Q S x) i k := by
  have hSa (a : I) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  have hdS (a b : I) : ContDiffAt ℝ 2 (D (basis a) (fun y => S y b)) x :=
    contDiffAt_D (hSa b) (by norm_num) (basis a)
  have hdq (a i k : I) : ContDiffAt ℝ 2 (D (basis a) (fun y => q y i k)) x :=
    contDiffAt_D (hqa i k) (by norm_num) (basis a)
  have hterm (a : I) : ContDiffAt ℝ 2 (fun y =>
      S y a*D (basis a) (fun z => q z i k) y+
      q y a k*D (basis i) (fun z => S z a) y+q y i a*D (basis k) (fun z => S z a) y) x :=
    ((((hSa a).of_le h23).mul (hdq a i k)).add
      (((hqa a k).of_le h23).mul (hdS i a))).add
      (((hqa i a).of_le h23).mul (hdS k a))
  unfold normalizedLie normalizedLieJet
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
end CKSAngularGeometry

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

lemma matrixScalarJets_linear (c d : ℝ) {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => c • q y+d • p y) x =
      c • matrixScalarJets q x+d • matrixScalarJets p x := by
  funext i k
  change actualScalarJet (fun y => c*q y i k+d*p y i k) x = _
  exact actualScalarJet_linear c d (component_diff hq i k) (component_diff hp i k)

end
end CKSAngularGeometry

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
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma component_diff {n : ℕ∞ω} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (i k : A) : ContDiffAt ℝ n (fun y => q y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k
lemma component_three {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (i k : A) : ContDiffAt ℝ 3 (fun y => q y i k) x :=
  component_diff hq i k

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

lemma matrixScalarJets_add {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => q y+p y) x = matrixScalarJets q x+matrixScalarJets p x := by
  simpa using matrixScalarJets_linear 1 1 hq hp

lemma matrixScalarJets_smul (c : ℝ) {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) :
    matrixScalarJets (fun y => c • q y) x = c • matrixScalarJets q x := by
  funext i k
  exact actualScalarJet_smul c (component_diff hq i k)

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

lemma radiusPower_smooth (n : ℝ) : ContDiff ℝ ∞ (radiusPower n) := by unfold radiusPower; fun_prop
lemma radiusPower_diff (n : ℝ) (m : ℕ) (x : Point) : ContDiffAt ℝ m (radiusPower n) x :=
  ((radiusPower_smooth n).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt

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

lemma scalarJet_norm_of_components {u : ScalarJet} {B : ℝ} (hB : 0 ≤ B)
    (h0 : |u.1| ≤ B) (h1 : ∀ a, |u.2.1 a| ≤ B) (h2 : ∀ a b, |u.2.2 a b| ≤ B) :
    ‖u‖ ≤ B := by
  exact norm_prod_le_iff.mpr ⟨h0,norm_prod_le_iff.mpr
    ⟨(pi_norm_le_iff_of_nonneg hB).mpr h1,(pi_norm_le_iff_of_nonneg hB).mpr
    (fun a => (pi_norm_le_iff_of_nonneg hB).mpr (h2 a))⟩⟩

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

def lapseCoefficientRegion : Set LapseCoefficientInput :=
  {p | 0 < (lapseRad p).1 ∧ (lapseD p).1 ≠ 0}
lemma lapseV_smooth : ContDiff ℝ ∞ lapseV := by
  have hp : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => productJet (lT p) (lT p)) :=
    productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => (lT p,lT p)))
  unfold lapseV
  exact ((contDiff_const.fun_div (by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => 1+lz p^2)) (by intro p; positivity))).fun_smul
    (((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => (2:ℝ) • lT p)).add
      ((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => lz p^3)).fun_smul hp)).sub (by fun_prop))
lemma lapseRad_smooth : ContDiff ℝ ∞ lapseRad :=
  contDiff_const.add ((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => lz p^3)).fun_smul lapseV_smooth)
lemma lapseD_smooth : ContDiff ℝ ∞ lapseD := by unfold lapseD; fun_prop
lemma lapseA_smooth {p : LapseCoefficientInput} (hp : p ∈ lapseCoefficientRegion) :
    ContDiffAt ℝ ∞ lapseA p := by
  have hs := (sqrtJet_smooth hp.1).comp p lapseRad_smooth.contDiffAt
  have hs1 := hs.add (contDiffAt_const (c := constantJet 1))
  have hs0 : (sqrtJet (lapseRad p)+constantJet 1).1 ≠ 0 := by
    change Real.sqrt (lapseRad p).1+1 ≠ 0
    positivity
  have hi := (reciprocalJet_smooth hs0).comp p hs1
  have hvi : ContDiffAt ℝ ∞ (fun p : LapseCoefficientInput =>
      productJet (lapseV p) (reciprocalJet (sqrtJet (lapseRad p)+constantJet 1))) p :=
    productJet_smooth.contDiffAt.comp p (lapseV_smooth.contDiffAt.prodMk hi)
  exact productJet_smooth.contDiffAt.comp p
    ((hvi.sub (by fun_prop)).prodMk ((reciprocalJet_smooth hp.2).comp p lapseD_smooth.contDiffAt))
lemma lapseCoefficientRegion_open : IsOpen lapseCoefficientRegion :=
  (isOpen_lt continuous_const (continuous_fst.comp lapseRad_smooth.continuous)).inter
    (isOpen_ne_fun (continuous_fst.comp lapseD_smooth.continuous) continuous_const)
lemma lapseCoefficientRegion_zero (T F D : ScalarJet) : (0,T,F,D) ∈ lapseCoefficientRegion := by
  simp [lapseCoefficientRegion,lapseRad,lapseD,constantJet,lz]

lemma lapseA_identity {p : LapseCoefficientInput} (hp : p ∈ lapseCoefficientRegion) :
    Real.sqrt ((lz p^2+(1+lz p^3*(lT p).1)^2-2*lz p^3*(lF p).1)/(1+lz p^2)) /
      (1+lz p^3*(lD p).1) = 1+lz p^3*(lapseA p).1 := by
  have hrad : (lz p^2+(1+lz p^3*(lT p).1)^2-2*lz p^3*(lF p).1)/(1+lz p^2) =
      (lapseRad p).1 := by
    simp only [lapseRad,lapseV,Prod.fst_add,Prod.fst_sub,Prod.smul_fst,smul_eq_mul,constantJet,productJet]
    have hz : 1+lz p^2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hrad]
  have hden : 1+lz p^3*(lD p).1 ≠ 0 := hp.2
  have hs : Real.sqrt (lapseRad p).1+1 ≠ 0 := by positivity
  have he : Real.sqrt (lapseRad p).1^2 = 1+lz p^3*(lapseV p).1 := Real.sq_sqrt hp.1.le
  change Real.sqrt (lapseRad p).1/(1+lz p^3*(lD p).1) =
    1+lz p^3*(((lapseV p).1*(1/(Real.sqrt (lapseRad p).1+1))-(lD p).1)*(1/(1+lz p^3*(lD p).1)))
  field_simp
  linear_combination he

end
end CKSAngularGeometry

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
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixScalarJets_norm_le_three (q : Point → Mat) (x : Point) :
    ‖matrixScalarJets q x‖ ≤ ‖matrixThreeJets q x‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro i k
  exact (norm_fst_le (matrixThreeJets q x i k)).trans
    (Matrix.norm_entry_le_entrywise_sup_norm (matrixThreeJets q x))

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
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_diff {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    ContDiffAt ℝ 2 (fun y => traceProduct (q y) (p y)) x := by
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hq i k).mul (component_diff hp k i)

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
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

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

lemma radialMatrixD_regular {f : Point → Mat} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    ContDiffAt ℝ 2 (radialMatrixD f) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact contDiffAt_D (component_diff hf i k) (by norm_num) (basis 0)

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

lemma matrixScalarJets_sub {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => q y-p y) x = matrixScalarJets q x-matrixScalarJets p x := by
  funext i k
  exact actualScalarJet_sub (component_diff hq i k) (component_diff hp i k)

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

lemma logQError_diff {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (logQError f) x :=
  ((radiusPower_diff (-3) 3 x).smul hf.mg).add ((radiusPower_diff (-2) 3 x).smul hf.eg)

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

lemma tensorDenField_positive {f : TensorFields} {x : Point} (h : 0 < logSchur f.base x) :
    0 < tensorDenField (radiusPower (-1)) (normalizeTensorLogFields f) x := by
  change 0 < 1+radiusPower (-1) x^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f.base) x
  rw [radiusPower_inverse,← log_schur_coefficient]
  positivity

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
open scoped Topology ContDiff NNReal

lemma logRadiusChart_smooth : ContDiff ℝ ∞ logRadiusChart := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · simp only [logRadiusChart,hi,ite_eq_left]; fun_prop
  · simp only [logRadiusChart,hi,ite_false]; fun_prop

lemma radialFactor_smooth (a : I) : ContDiff ℝ ∞ (radialFactor a) := by
  unfold radialFactor
  by_cases ha : a = 0 <;> simp only [ha,ite_true,ite_false] <;> fun_prop

theorem coordinate_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

theorem coordinate_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

def chartDerivative (x : Point) : Point →L[ℝ] Point :=
  letI := pointDimension_neZero
  letI := coordinate_smulCommClass
  letI := coordinate_continuousConstSMul
  ContinuousLinearMap.pi (fun i => if i = 0 then Real.exp (x 0) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma logRadiusChart_hasFDerivAt (x : Point) : HasFDerivAt logRadiusChart (chartDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [logRadiusChart,chartDerivative,Function.comp_def] using
      (Real.hasDerivAt_exp (x 0)).comp_hasFDerivAt x (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).hasFDerivAt
  · simp only [logRadiusChart,hi,ite_false]
    change HasFDerivAt (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) (ContinuousLinearMap.proj i) x
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt

lemma chartDerivative_basis (a : I) (x : Point) :
    chartDerivative x (basis a) = radialFactor a (logRadiusChart x) • basis a := by
  ext i
  by_cases ha : a = 0 <;> by_cases hi : i = 0
  · subst a; subst i; simp [chartDerivative,radialFactor,logRadiusChart,basis]
  · subst a; simp [chartDerivative,radialFactor,logRadiusChart,basis,hi]
  · subst i; simp [chartDerivative,radialFactor,basis,ha,Ne.symm ha]
  · simp [chartDerivative,radialFactor,basis,ha,hi]

lemma D_pullback (a : I) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (logRadiusChart x)) :
    D (basis a) (fun y => f (logRadiusChart y)) x = scaledD a f (logRadiusChart x) := by
  unfold D
  change (fderiv ℝ (f ∘ logRadiusChart) x) (basis a) = _
  rw [fderiv_comp x hf (logRadiusChart_hasFDerivAt x).differentiableAt,
    (logRadiusChart_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.comp_apply,chartDerivative_basis,map_smul,smul_eq_mul,scaledD,D]

def coordinateIter : List I → (Point → ℝ) → Point → ℝ
  | [], f => f
  | a::l,f => D (basis a) (coordinateIter l f)

lemma scaledIter_contDiffAt (l : List I) (m : ℕ) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ (↑(m+l.length) : ℕ∞ω) f x) : ContDiffAt ℝ m (scaledIter l f) x := by
  induction l generalizing m with
  | nil => simpa only [List.length_nil,add_zero,scaledIter] using hf
  | cons a l ih =>
    have heq : m+(a::l).length = (m+1)+l.length := by simp; omega
    rw [heq] at hf
    exact ((radialFactor_smooth a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt.mul
      (contDiffAt_D (ih (m+1) hf) (m := m) (by simp) (basis a))

lemma coordinateIter_pullback (l : List I) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ l.length f (logRadiusChart x)) :
    coordinateIter l (fun y => f (logRadiusChart y)) x = scaledIter l f (logRadiusChart x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    have heq : coordinateIter l (fun y => f (logRadiusChart y)) =ᶠ[𝓝 x]
        (fun y => scaledIter l f (logRadiusChart y)) := by
      have hf' : ContDiffAt ℝ l.length f (logRadiusChart x) := hf.of_le (by simp)
      have he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ l.length f (logRadiusChart y) :=
        (logRadiusChart_smooth.continuous.continuousAt.tendsto).eventually (hf'.eventually (by simp))
      filter_upwards [he] with y hy
      exact ih hy
    change D (basis a) (coordinateIter l (fun y => f (logRadiusChart y))) x = _
    rw [D_congr heq]
    have hf' : ContDiffAt ℝ (↑(1+l.length) : ℕ∞ω) f (logRadiusChart x) := by
      simpa only [List.length_cons,Nat.add_comm] using hf
    exact D_pullback a ((scaledIter_contDiffAt l 1 hf').differentiableAt (by norm_num))

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

lemma lapseVField_diff (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (lapseVField z T F) x := by
  exact (((hT.const_smul (2:ℝ)).add ((hT.mul hT).const_smul (z^3))).sub
    (hF.const_smul (2:ℝ))).const_smul (1/(1+z^2))
lemma lapseRadField_diff (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (lapseRadField z T F) x :=
  contDiffAt_const.add ((lapseVField_diff z hT hF).const_smul (z^3))
lemma lapseDField_diff (z : ℝ) {d : Point → ℝ} {x : Point} (hd : ContDiffAt ℝ 2 d x) :
    ContDiffAt ℝ 2 (lapseDField z d) x := contDiffAt_const.add (hd.const_smul (z^3))
lemma lapseAField_diff (z : ℝ) {T F d : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (hd : ContDiffAt ℝ 2 d x)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    ContDiffAt ℝ 2 (lapseAField z T F d) x := by
  have hv := lapseVField_diff z hT hF
  have hs := ((lapseRadField_diff z hT hF).sqrt hr.ne').add (contDiffAt_const (c := (1:ℝ)))
  have hs0 : Real.sqrt (lapseRadField z T F x)+1 ≠ 0 := by positivity
  exact ((hv.mul (contDiffAt_const.div hs hs0)).sub hd).mul
    (contDiffAt_const.div (lapseDField_diff z hd) h0)

lemma actual_lapseVField (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (d : ScalarJet) :
    actualScalarJet (lapseVField z T F) x = lapseV (z,actualScalarJet T x,actualScalarJet F x,d) := by
  unfold lapseVField
  erw [actualScalarJet_smul _ (((hT.const_smul (2:ℝ)).add ((hT.mul hT).const_smul (z^3))).sub
      (hF.const_smul (2:ℝ))),
    actualScalarJet_sub ((hT.const_smul (2:ℝ)).add ((hT.mul hT).const_smul (z^3))) (hF.const_smul (2:ℝ)),
    actualScalarJet_add (hT.const_smul (2:ℝ)) ((hT.mul hT).const_smul (z^3)),
    actualScalarJet_smul _ hT,actualScalarJet_smul _ (hT.mul hT),actualScalarJet_mul hT hT,
    actualScalarJet_smul _ hF]
  rfl
lemma actual_lapseRadField (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (d : ScalarJet) :
    actualScalarJet (lapseRadField z T F) x = lapseRad (z,actualScalarJet T x,actualScalarJet F x,d) := by
  unfold lapseRadField
  erw [actualScalarJet_add contDiffAt_const ((lapseVField_diff z hT hF).const_smul (z^3)),
    actualScalarJet_const,actualScalarJet_smul _ (lapseVField_diff z hT hF),actual_lapseVField z hT hF d]
  rfl
lemma actual_lapseDField (z : ℝ) {d : Point → ℝ} {x : Point}
    (hd : ContDiffAt ℝ 2 d x) (T F : ScalarJet) :
    actualScalarJet (lapseDField z d) x = lapseD (z,T,F,actualScalarJet d x) := by
  unfold lapseDField
  erw [actualScalarJet_add contDiffAt_const (hd.const_smul (z^3)),actualScalarJet_const,actualScalarJet_smul _ hd]
  rfl
lemma actual_lapseAField (z : ℝ) {T F d : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (hd : ContDiffAt ℝ 2 d x)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    actualScalarJet (lapseAField z T F d) x =
      lapseA (z,actualScalarJet T x,actualScalarJet F x,actualScalarJet d x) := by
  have hv := lapseVField_diff z hT hF
  have hs := ((lapseRadField_diff z hT hF).sqrt hr.ne').add (contDiffAt_const (c := (1:ℝ)))
  have hs0 : Real.sqrt (lapseRadField z T F x)+1 ≠ 0 := by positivity
  have hi := (contDiffAt_const (c := (1:ℝ))).div hs hs0
  have hid := (contDiffAt_const (c := (1:ℝ))).div (lapseDField_diff z hd) h0
  unfold lapseAField
  erw [actualScalarJet_mul ((hv.mul hi).sub hd) hid,actualScalarJet_sub (hv.mul hi) hd,
    actualScalarJet_mul hv hi,actual_reciprocal hs hs0,
    actualScalarJet_add ((lapseRadField_diff z hT hF).sqrt hr.ne') contDiffAt_const,
    actualScalarJet_sqrt (lapseRadField_diff z hT hF) hr,actualScalarJet_const,
    actual_reciprocal (lapseDField_diff z hd) h0,
    actual_lapseVField z hT hF (actualScalarJet d x),
    actual_lapseRadField z hT hF (actualScalarJet d x),
    actual_lapseDField z hd (actualScalarJet T x) (actualScalarJet F x)]
  rfl

lemma lapseAField_identity (z : ℝ) (T F d : Point → ℝ) (x : Point)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    lapseNormalizedField z T F d x = 1+z^3*lapseAField z T F d x := by
  have hp : (z,constantJet (T x),constantJet (F x),constantJet (d x)) ∈ lapseCoefficientRegion := ⟨hr,h0⟩
  exact lapseA_identity hp

theorem actual_normalized_lapse_coefficient (z : ℝ) {T F d : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (hd : ContDiffAt ℝ 2 d x)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    actualScalarJet (lapseNormalizedField z T F d) x = constantJet 1+
      z^3 • lapseA (z,actualScalarJet T x,actualScalarJet F x,actualScalarJet d x) := by
  have her : ∀ᶠ y in 𝓝 x, 0 < lapseRadField z T F y :=
    (lapseRadField_diff z hT hF).continuousAt.eventually (eventually_gt_nhds hr)
  have hed : ∀ᶠ y in 𝓝 x, lapseDField z d y ≠ 0 :=
    (lapseDField_diff z hd).continuousAt.eventually (eventually_ne_nhds h0)
  have he : lapseNormalizedField z T F d =ᶠ[𝓝 x] (fun y => 1+z^3*lapseAField z T F d y) := by
    filter_upwards [her,hed] with y hyr hyd
    exact lapseAField_identity z T F d y hyr hyd
  erw [actualScalarJet_congr he,actualScalarJet_add contDiffAt_const
    ((lapseAField_diff z hT hF hd hr h0).const_smul (z^3)),actualScalarJet_const,
    actualScalarJet_smul _ (lapseAField_diff z hT hF hd hr h0),actual_lapseAField z hT hF hd hr h0]

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

lemma logShift_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hp : (logMetric f x).PosDef) : ContDiffAt ℝ 3 (logShift f) x := by
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hp).1.det_pos.ne'
  rw [logShift_normalized]
  exact (radiusPower_diff (-5) 3 x).smul
    (cksHField_diff (radiusPower_diff (-1) 3 x) (normalizeMassLogFields_regular hf) hd)

lemma logTError_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) :
    ContDiffAt ℝ 2 (fun y => logT f y-1) x := by
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hp.self_of_nhds).1.det_pos.ne'
  apply ((radiusPower_diff (-3) 2 x).mul
    (cksTField_diff (radiusPower_diff (-1) 3 x) (normalizeMassLogFields_regular hf) hd)).congr_of_eventuallyEq
  filter_upwards [hp] with y hy
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hy).1.det_pos.ne'
  unfold logT
  rw [log_trace_coefficient hd,radiusPower_minus_three]
  ring

lemma logOriginalLError_diff {f : TensorFields} {x : Point} (hf : f.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) :
    ContDiffAt ℝ 2 (fun y => logOriginalL f y-1) x := by
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hp.self_of_nhds
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeTensorLogFields f).base x) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  apply ((radiusPower_diff (-3) 2 x).mul
    (tensorLField_diff (radiusPower_diff (-1) 3 x) (normalizeTensorLogFields_regular hf) hd
      (tensorDenField_positive hs))).congr_of_eventuallyEq
  filter_upwards [hp] with y hy using logOriginalL_normalized (logMetric_normalized_positive hy).2

lemma logOriginalEtaDiv_diff {f : TensorFields} {x : Point} (hf : f.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) :
    ContDiffAt ℝ 2 (fun y a => logOriginalEta f y a/Real.exp (y 0)) x := by
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hp.self_of_nhds
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeTensorLogFields f).base x) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  apply contDiffAt_pi.mpr; intro a
  apply ((radiusPower_diff (-3) 2 x).mul
    (tensorEtaField_diff (radiusPower_diff (-1) 3 x) (normalizeTensorLogFields_regular hf) hd
      (tensorDenField_positive hs) a)).congr_of_eventuallyEq
  filter_upwards [hp] with y hy using logOriginalEta_normalized (logMetric_normalized_positive hy).2 a

lemma logOriginalTauDiv_diff {f : TensorFields} {x : Point} (hf : f.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) :
    ContDiffAt ℝ 2 (fun y a b => logOriginalTau f y a b/Real.exp (y 0)^2) x := by
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeTensorLogFields f).base x) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hp.self_of_nhds).1.det_pos.ne'
  apply contDiffAt_pi.mpr; intro a; apply contDiffAt_pi.mpr; intro b
  apply ((radiusPower_diff (-3) 2 x).mul
    (component_diff (tensorTauField_diff (radiusPower_diff (-1) 3 x)
      (normalizeTensorLogFields_regular hf) hd) a b)).congr_of_eventuallyEq
  filter_upwards [hp] with y hy
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hy).1.det_pos.ne'
  have hh := congrFun (congrFun (logOriginalTau_normalized hd) a) b
  change (Real.exp (y 0)^2)⁻¹*logOriginalTau f y a b =
    radiusPower (-3) y*tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b at hh
  simpa only [div_eq_mul_inv,mul_comm] using hh

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

lemma source_two_jet_bound {f : Point → ℝ} {x : Point} {q : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 2 f (logRadiusChart x))
    (hb : ScaledComponentBound f 2 q B (logRadiusChart x)) :
    ‖actualScalarJet (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q := by
  have he (l : List I) (hl : l.length ≤ 2) :
      |coordinateIter l (fun y => f (logRadiusChart y)) x| ≤ B/Real.exp (x 0)^q := by
    rw [coordinateIter_pullback l (hf.of_le (by exact_mod_cast hl))]
    simpa only [logRadiusChart,ite_true] using hb l hl
  apply scalarJet_norm_of_components (by positivity)
  · exact he [] (by simp)
  · intro a; exact he [a] (by simp)
  · intro a b; exact he [a,b] (by simp)

lemma source_three_jet_bound {f : Point → ℝ} {x : Point} {q : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 3 f (logRadiusChart x))
    (hb : ScaledComponentBound f 3 q B (logRadiusChart x)) :
    ‖actualThreeJet (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q := by
  have he (l : List I) (hl : l.length ≤ 3) :
      |coordinateIter l (fun y => f (logRadiusChart y)) x| ≤ B/Real.exp (x 0)^q := by
    rw [coordinateIter_pullback l (hf.of_le (by exact_mod_cast hl))]
    simpa only [logRadiusChart,ite_true] using hb l hl
  apply norm_prod_le_iff.mpr
  constructor
  · apply scalarJet_norm_of_components (by positivity)
    · exact he [] (by simp)
    · intro a; exact he [a] (by simp)
    · intro a b; exact he [a,b] (by simp)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    apply scalarJet_norm_of_components (by positivity)
    · exact he [a] (by simp)
    · intro b; exact he [b,a] (by simp)
    · intro b c; exact he [b,c,a] (by simp)

lemma source_matrix_three_bound {f : Point → Mat} {x : Point} {q : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 3 f (logRadiusChart x))
    (hb : ∀ i k, ScaledComponentBound (fun y => f y i k) 3 q B (logRadiusChart x)) :
    ‖matrixThreeJets (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  exact source_three_jet_bound hB (component_diff hf i k) (hb i k)

lemma source_matrix_two_bound {f : Point → Mat} {x : Point} {q : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ContDiffAt ℝ 2 f (logRadiusChart x))
    (hb : ∀ i k, ScaledComponentBound (fun y => f y i k) 2 q B (logRadiusChart x)) :
    ‖matrixScalarJets (fun y => f (logRadiusChart y)) x‖ ≤ B/Real.exp (x 0)^q := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  exact source_two_jet_bound hB (component_diff hf i k) (hb i k)

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

def momentumRegion : Set MomentumInput :=
  {p | determinant (mq p).1 ≠ 0 ∧ 1+mz p^3*(mc p 0).1 ≠ 0}

lemma momentumRegion_open : IsOpen momentumRegion := by
  apply IsOpen.inter
  · exact isOpen_ne_fun (determinant_smooth.continuous.comp (by fun_prop)) continuous_const
  · exact isOpen_ne_fun (by fun_prop) continuous_const

end
end CKSAngularGeometry

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

def rawRegular (p : RawCollarInput) : Prop := determinant (fun i k => (rawQ p i k).1) ≠ 0

lemma rawQ_smooth : ContDiff ℝ ∞ rawQ := by unfold rawQ; fun_prop
lemma rawExpansionInput_smooth : ContDiff ℝ ∞ rawExpansionInput := by
  unfold rawExpansionInput rawQ rawDQ rawQr rawS rawDS
  fun_prop
lemma rawC_smooth (i k : I) : ContDiff ℝ ∞ (fun p => rawC p i k) := by
  unfold rawC
  exact (by unfold rawQr; fun_prop : ContDiff ℝ ∞ (fun p : RawCollarInput => rawQr p i k)).sub
    ((by fun_prop : ContDiff ℝ ∞ rz).fun_smul ((normalizedLieJet_smooth i k).comp rawExpansionInput_smooth))
lemma matrixTraceJet_smooth {q t : MatrixScalarJet}
    (h : determinant (fun i k => (q i k).1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => matrixTraceJet qt.1 qt.2) (q,t) := by
  unfold matrixTraceJet
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  exact productJet_smooth.contDiffAt.comp (q,t)
    (((inverseMatrixJet_smooth h i k).comp (q,t) (by fun_prop :
      ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.1) (q,t))).prodMk (by fun_prop : ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.2 k i) (q,t)))
lemma traceFreeJet_smooth {q t : MatrixScalarJet}
    (h : determinant (fun i k => (q i k).1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => traceFreeJet qt.1 qt.2) (q,t) := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  unfold traceFreeJet
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.2 i k) (q,t)).sub
    ((productJet_smooth.contDiffAt.comp (q,t) ((matrixTraceJet_smooth h).prodMk (by fun_prop))).const_smul (1/2:ℝ))
lemma rawD_smooth {p : RawCollarInput} (hp : rawRegular p) : ContDiffAt ℝ ∞ rawD p := by
  have hc : ContDiff ℝ ∞ rawC := contDiff_pi.mpr fun i => contDiff_pi.mpr fun k => rawC_smooth i k
  exact ((matrixTraceJet_smooth hp).comp p (rawQ_smooth.contDiffAt.prodMk hc.contDiffAt)).const_smul (1/4:ℝ)
lemma rawT_smooth : ContDiff ℝ ∞ rawT := by unfold rawT; fun_prop
lemma rawF_smooth : ContDiff ℝ ∞ rawF := by
  unfold rawF constantJet
  fun_prop
lemma rawLapseInput_smooth {p : RawCollarInput} (hp : rawRegular p) :
    ContDiffAt ℝ ∞ rawLapseInput p :=
  (by fun_prop : ContDiffAt ℝ ∞ rz p).prodMk
    (rawT_smooth.contDiffAt.prodMk (rawF_smooth.contDiffAt.prodMk (rawD_smooth hp)))
lemma rawA_smooth {p : RawCollarInput} (hp : rawRegular p)
    (hl : rawLapseInput p ∈ lapseCoefficientRegion) : ContDiffAt ℝ ∞ rawA p :=
  (lapseA_smooth hl).comp p (rawLapseInput_smooth hp)
lemma rawMomentumInput_smooth {p : RawCollarInput} (hp : rawRegular p)
    (hl : rawLapseInput p ∈ lapseCoefficientRegion) : ContDiffAt ℝ ∞ rawMomentumInput p := by
  have hq := rawQ_smooth.contDiffAt (x:=p)
  have ha := rawA_smooth hp hl
  have hD := rawD_smooth hp
  have ht0 := traceFreeJet_smooth (q:=rawQ p) (t:=rtau p) hp
  have ht1 := ht0.comp p (hq.prodMk
      (by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => rtau p) p))
  have hτ : ContDiffAt ℝ ∞ (fun p : RawCollarInput => traceFreeJet (rawQ p) (rtau p)) p := ht1
  have hc : ContDiff ℝ ∞ rawC := contDiff_pi.mpr fun i => contDiff_pi.mpr fun k => rawC_smooth i k
  have hx0 := traceFreeJet_smooth (q:=rawQ p) (t:=rawC p) hp
  have hx1 := hx0.comp p (hq.prodMk hc.contDiffAt)
  have hχ : ContDiffAt ℝ ∞ (fun p : RawCollarInput => traceFreeJet (rawQ p) (rawC p)) p := hx1
  have hs : ContDiff ℝ ∞ (fun p : RawCollarInput => Real.sqrt (1+rz p^2)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun p : RawCollarInput => 1+rz p^2)).sqrt (by intro p; positivity)
  have hspeed : ContDiffAt ℝ ∞ rawLambda p := by
    unfold rawLambda
    exact hs.contDiffAt.mul (contDiffAt_const.add ((by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => rz p^3) p).mul (contDiffAt_fst.comp p ha)))
  have hX : ContDiffAt ℝ ∞ rawX p := by
    apply contDiffAt_pi.mpr; intro i
    apply contDiffAt_pi.mpr; intro k
    exact (hspeed.div_const 2).mul (contDiffAt_fst.comp p (contDiffAt_pi.mp (contDiffAt_pi.mp hχ i) k))
  unfold rawMomentumInput scalarMatrixToJet
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk
  · fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    fin_cases a <;> dsimp <;>
      first | exact ha | exact rawT_smooth.contDiffAt | exact hD | dsimp [rawL,rawTr]; fun_prop
  apply ContDiffAt.prodMk
  · unfold rawS; fun_prop
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => 1-re p) p).smul hτ
  exact hX.prodMk (by fun_prop)

end
end CKSAngularGeometry

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

def rawDomain : Set RawCollarInput := {p | rawRegular p ∧
  rawLapseInput p ∈ lapseCoefficientRegion ∧ rawMomentumInput p ∈ momentumRegion}

lemma rawRegular_cont {p : RawCollarInput} (hp : rawRegular p) :
    ∀ᶠ q in 𝓝 p, rawRegular q := by
  have hc : ContinuousAt (fun p : RawCollarInput => determinant (fun i k => (rawQ p i k).1)) p :=
    determinant_smooth.contDiffAt.continuousAt.comp
      (by fun_prop : ContinuousAt (fun p : RawCollarInput => (fun i k => (rawQ p i k).1)) p)
  exact hc.eventually (eventually_ne_nhds hp)
lemma rawDomain_open : IsOpen rawDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hl := (rawLapseInput_smooth hp.1).continuousAt.eventually
    (lapseCoefficientRegion_open.mem_nhds hp.2.1)
  have hm := (rawMomentumInput_smooth hp.1 hp.2.1).continuousAt.eventually
    (momentumRegion_open.mem_nhds hp.2.2)
  filter_upwards [rawRegular_cont hp.1,hl,hm] with q hq hql hqm
  exact ⟨hq,hql,hqm⟩
lemma rawDomain_at_zero {p : RawCollarInput} (hz : rz p = 0)
    (hσ : determinant (fun i k => (rmat p 0 i k).1) ≠ 0) : p ∈ rawDomain := by
  have hq : rawQ p = rmat p 0 := by simp [rawQ,hz]
  have hreg : rawRegular p := by simpa [rawRegular,hq] using hσ
  have hl : rawLapseInput p ∈ lapseCoefficientRegion := by
    simpa only [rawLapseInput,hz] using lapseCoefficientRegion_zero (rawT p) (rawF p) (rawD p)
  refine ⟨hreg,hl,?_⟩
  change determinant (scalarMatrixToJet (rawQ p)).1 ≠ 0 ∧
    1+rz p^3*(rawA p).1 ≠ 0
  exact ⟨by simpa [scalarMatrixToJet,hq] using hσ,by simp [hz]⟩

def rawZeroRadius (p : RawCollarInput) : RawCollarInput := (fun i => if i=0 then 0 else p.1 i,p.2)

lemma rawOriginal_z (p : RawCollarInput) : rz (rawOriginal p) = rz p := by simp [rawOriginal,rz]

lemma rawZeroRadius_z (p : RawCollarInput) : rz (rawZeroRadius p) = 0 := by simp [rawZeroRadius,rz]
lemma rawZeroRadius_dist (p : RawCollarInput) : dist p (rawZeroRadius p) ≤ |rz p| := by
  rw [dist_eq_norm]
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro i
    by_cases hi : i=0
    · subst i; simp [rawZeroRadius,rz]
    · simp [rawZeroRadius,hi,abs_nonneg]
  · simp [rawZeroRadius]

end
end CKSAngularGeometry

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

abbrev nr (p : RawNullInput) := p.1

def rawNullDomain : Set RawNullInput := nr ⁻¹' rawDomain
lemma rawNullDomain_open : IsOpen rawNullDomain := rawDomain_open.preimage (by fun_prop)

end
end CKSAngularGeometry

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

def rawNullZeroRadius (p : RawNullInput) : RawNullInput := (rawZeroRadius p.1,p.2)
def rawReferenceFamily (K : Set MatrixScalarJet) (B : ℝ) : Set RawNullInput :=
  {p | rmat p.1 0 ∈ K ∧ rz p.1 = 0} ∩ Metric.closedBall 0 B
lemma rawReferenceFamily_compact {K : Set MatrixScalarJet} (hK : IsCompact K) (B : ℝ) :
    IsCompact (rawReferenceFamily K B) := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  exact (isCompact_closedBall (0:RawNullInput) B).inter_left
    ((hK.isClosed.preimage (by fun_prop)).inter (isClosed_eq (by fun_prop) continuous_const))
lemma rawReferenceFamily_regular {K : Set MatrixScalarJet}
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    rawReferenceFamily K B ⊆ rawNullDomain := by
  intro p hp
  exact rawDomain_at_zero hp.1.2 (hreg _ hp.1.1)

lemma rawOriginal_norm (p : RawCollarInput) : ‖rawOriginal p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨?_,?_⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    by_cases hi : i=0
    · subst i
      exact (norm_le_pi_norm p.1 0).trans (norm_fst_le p)
    · simp only [rawOriginal,hi,ite_false,norm_zero]
      exact norm_nonneg p
  · exact norm_snd_le p
lemma rawZeroRadius_norm (p : RawCollarInput) : ‖rawZeroRadius p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨?_,norm_snd_le p⟩
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  by_cases hi : i=0
  · simp only [rawZeroRadius,hi,ite_true,norm_zero]
    exact norm_nonneg p
  · simp only [rawZeroRadius,hi,ite_false]
    exact (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
lemma rawNullOriginal_norm (p : RawNullInput) : ‖rawNullOriginal p‖ ≤ ‖p‖ :=
  norm_prod_le_iff.mpr ⟨(rawOriginal_norm p.1).trans (norm_fst_le p),norm_snd_le p⟩
lemma rawNullZeroRadius_norm (p : RawNullInput) : ‖rawNullZeroRadius p‖ ≤ ‖p‖ :=
  norm_prod_le_iff.mpr ⟨(rawZeroRadius_norm p.1).trans (norm_fst_le p),norm_snd_le p⟩
lemma rawNullZeroRadius_close (p : RawNullInput) :
    dist p (rawNullZeroRadius p) ≤ |rz p.1| := by
  change max (dist p.1 (rawZeroRadius p.1)) (dist p.2 p.2) ≤ _
  rw [max_le_iff,dist_self]
  exact ⟨rawZeroRadius_dist p.1,abs_nonneg _⟩
lemma rawNullZeroRadius_mem {K : Set MatrixScalarJet} {B : ℝ} {p : RawNullInput}
    (hq : rmat p.1 0 ∈ K) (hp : ‖p‖ ≤ B) :
    rawNullZeroRadius p ∈ rawReferenceFamily K B := by
  refine ⟨⟨hq,rawZeroRadius_z _⟩,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using (rawNullZeroRadius_norm p).trans hp
lemma raw_reference_tube {K : Set MatrixScalarJet} {B δ : ℝ} {p : RawNullInput}
    (hq : rmat p.1 0 ∈ K) (hp : ‖p‖ ≤ B) (hz : |rz p.1| ≤ δ) :
    p ∈ Metric.cthickening δ (rawReferenceFamily K B) ∧
    rawNullOriginal p ∈ Metric.cthickening δ (rawReferenceFamily K B) := by
  constructor
  · exact Metric.mem_cthickening_of_dist_le p (rawNullZeroRadius p) δ _
      (rawNullZeroRadius_mem hq hp) ((rawNullZeroRadius_close p).trans hz)
  · apply Metric.mem_cthickening_of_dist_le (rawNullOriginal p)
      (rawNullZeroRadius (rawNullOriginal p)) δ _
      (rawNullZeroRadius_mem hq ((rawNullOriginal_norm p).trans hp))
    exact (rawNullZeroRadius_close _).trans (by simpa only [rawNullOriginal,rawOriginal_z] using hz)

end
end CKSAngularGeometry

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

def CollarCoefficientFields.RegularAt (f : CollarCoefficientFields) (x : Point) : Prop :=
  (ContDiffAt ℝ 3 (f.metric 0) x ∧ ContDiffAt ℝ 3 (f.metric 1) x ∧
    ContDiffAt ℝ 2 (f.metric 2) x) ∧ ContDiffAt ℝ 3 f.shift x ∧
  (∀ i, ContDiffAt ℝ 2 (f.scalar i) x) ∧ ContDiffAt ℝ 2 f.eta x ∧
    ContDiffAt ℝ 2 f.tau x

lemma fieldQ_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (fieldQ b f) x := (hf.1.1).add ((hf.1.2.1).const_smul _)
lemma fieldQr_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldQr b f) x := (hf.1.2.2.const_smul _).sub ((hf.1.2.1.of_le (by norm_num)).const_smul _)
lemma fieldS_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (fieldS b f) x := hf.2.1.const_smul _

lemma field_rawQ (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    matrixScalarJets (fieldQ b f) x=rawQ (fieldRaw b f x).1 := by
  unfold fieldQ
  rw [matrixScalarJets_add ((hf.1.1).of_le (by norm_num)) (((hf.1.2.1).of_le (by norm_num)).const_smul _),
    matrixScalarJets_smul _ ((hf.1.2.1).of_le (by norm_num))]
  rfl
lemma field_rawQr (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    matrixScalarJets (fieldQr b f) x=rawQr (fieldRaw b f x).1 := by
  unfold fieldQr
  rw [matrixScalarJets_sub (((hf.1.2.2).of_le (by norm_num)).const_smul _) (((hf.1.2.1).of_le (by norm_num)).const_smul _),
    matrixScalarJets_smul _ ((hf.1.2.2).of_le (by norm_num)),matrixScalarJets_smul _ ((hf.1.2.1).of_le (by norm_num))]
  rfl
lemma field_rawS (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) (a : I) :
    actualScalarJet (fun y => fieldS b f y a) x=rawS (fieldRaw b f x).1 a := by
  exact actualScalarJet_smul (1-b 1) ((contDiffAt_pi.mp hf.2.1 a).of_le (by norm_num))

end
end CKSAngularGeometry

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

def thinTensor (t : RawTensorData) : RawTensorData :=
  (((fun i => if i=3 then constantJet (t.1.1 i).1 else t.1.1 i),t.1.2),t.2)
def thinRaw (p : RawNullInput) : RawNullInput :=
  ((p.1.1,(p.1.2.1,thinTensor p.1.2.2)),p.2)

lemma thinQ (p : RawNullInput) : rawQ (thinRaw p).1=rawQ p.1 := rfl

lemma thinD (p : RawNullInput) : rawD (thinRaw p).1=rawD p.1 := rfl
lemma thinT (p : RawNullInput) : rawT (thinRaw p).1=rawT p.1 := rfl
lemma thinF (p : RawNullInput) : rawF (thinRaw p).1=rawF p.1 := rfl

attribute [local irreducible] rawA rawX rawQ rawD rawT rawL rawF rawTr

end
end CKSAngularGeometry

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

lemma inverse_radius_threshold {δ r : ℝ} (hδ : 0 < δ) (hr : max 1 (1/δ) ≤ r) :
    1 ≤ r ∧ |1/r| ≤ δ := by
  have hr1 := (le_max_left 1 (1/δ)).trans hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine ⟨hr1,?_⟩
  rw [abs_of_pos (one_div_pos.mpr hr0)]
  apply (div_le_iff₀ hr0).mpr
  simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))

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

lemma angularLift_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Angle → E} {x : Point} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f (angularProjection x)) :
    ContDiffAt ℝ n (angularLift f) x := hf.comp x angularProjection.contDiff.contDiffAt

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

lemma field_rawDQ (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) (a : I) :
    matrixScalarJets (fun y i k => D (basis a) (fun z => fieldQ b f z i k) y) x=
      rawDQ (fieldRaw b f x).1 a := by
  funext i k
  have h0 := component_three (hf.1.1) i k
  have h1 := component_three (hf.1.2.1) i k
  have he : (D (basis a) (fun z => fieldQ b f z i k)) =ᶠ[𝓝 x]
      (fun y => D (basis a) (fun z => f.metric 0 z i k) y+
        (b 0^3*(1-b 1))*D (basis a) (fun z => f.metric 1 z i k) y) := by
    filter_upwards [h0.eventually (by norm_num),h1.eventually (by norm_num)] with y hy0 hy1
    change D (basis a) (fun z => f.metric 0 z i k+(b 0^3*(1-b 1))*f.metric 1 z i k) y = _
    rw [D_add _ (hy0.differentiableAt (by norm_num))
      ((hy1.differentiableAt (by norm_num)).const_mul _),D_const_mul _ _ (hy1.differentiableAt (by norm_num))]
  have hd0 : ContDiffAt ℝ 2 (D (basis a) (fun z => f.metric 0 z i k)) x :=
    contDiffAt_D h0 (by norm_num) _
  have hd1 : ContDiffAt ℝ 2 (D (basis a) (fun z => f.metric 1 z i k)) x :=
    contDiffAt_D h1 (by norm_num) _
  change actualScalarJet _ x=_
  erw [actualScalarJet_congr he,actualScalarJet_add hd0 (contDiffAt_const.mul hd1),
    actualScalarJet_smul _ hd1]
  rfl

lemma field_rawDS (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) (a k : I) :
    actualScalarJet (D (basis a) (fun y => fieldS b f y k)) x=rawDS (fieldRaw b f x).1 a k := by
  have h := contDiffAt_pi.mp hf.2.1 k
  have he : (D (basis a) (fun y => fieldS b f y k)) =ᶠ[𝓝 x]
      (fun y => (1-b 1)*D (basis a) (fun y => f.shift y k) y) := by
    filter_upwards [h.eventually (by norm_num)] with y hy
    exact D_const_mul _ _ (hy.differentiableAt (by norm_num))
  erw [actualScalarJet_congr he,actualScalarJet_smul _ (contDiffAt_D h (by norm_num) _)]
  rfl

lemma field_rawExpansionInput (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualExpansionInput (fieldQ b f) (fieldQr b f) (fieldS b f) x=
      rawExpansionInput (fieldRaw b f x).1 := by
  apply Prod.ext (field_rawQ b hf)
  apply Prod.ext (funext (field_rawDQ b hf))
  apply Prod.ext (field_rawQr b hf)
  exact Prod.ext (funext (field_rawS b hf)) (funext fun a => funext (field_rawDS b hf a))

lemma fieldC_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldC b f) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  exact ((component_diff (fieldQr_diff b hf) i k).of_le (by norm_num)).sub
    ((normalizedLie_diff (fieldQ_diff b hf) (fieldS_diff b hf) i k).const_smul (b 0))

lemma field_rawC (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    matrixScalarJets (fieldC b f) x=rawC (fieldRaw b f x).1 := by
  funext i k
  have hq := component_diff (fieldQr_diff b hf) i k
  have hl := normalizedLie_diff (fieldQ_diff b hf) (fieldS_diff b hf) i k
  change actualScalarJet (fun y => fieldQr b f y i k-b 0*normalizedLie (fieldQ b f) (fieldS b f) y i k) x = _
  erw [actualScalarJet_sub (hq.of_le (by norm_num)) (contDiffAt_const.mul hl),actualScalarJet_smul _ hl,
    actual_normalizedLieJet (Q:=fieldQr b f) (fieldQ_diff b hf) (fieldS_diff b hf),field_rawExpansionInput b hf]
  change matrixScalarJets (fieldQr b f) x i k-_=_
  rw [field_rawQr b hf]
  rfl

lemma matrixTraceField_diff {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ 2 (fun y => ∑ i, ∑ k, inverse (q y) i k*t y k i) x := by
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  have hi : ContDiffAt ℝ 2 (fun y => inverse (q y) i k) x := by
    unfold inverse
    apply ContDiffAt.div
    · fin_cases i <;> fin_cases k <;> dsimp <;>
        first | exact component_diff hq _ _ | exact (component_diff hq _ _).neg
    · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
    · exact h0
  exact hi.mul (component_diff ht k i)

lemma actual_matrixTraceJet {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    actualScalarJet (fun y => ∑ i, ∑ k, inverse (q y) i k*t y k i) x=
      matrixTraceJet (matrixScalarJets q x) (matrixScalarJets t x) := by
  have hi (i k : I) : ContDiffAt ℝ 2 (fun y => inverse (q y) i k) x := by
    unfold inverse
    apply ContDiffAt.div
    · fin_cases i <;> fin_cases k <;> dsimp <;>
        first | exact component_diff hq _ _ | exact (component_diff hq _ _).neg
    · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
    · exact h0
  erw [actualScalarJet_sum _ (fun i _ => ContDiffAt.sum fun k _ => (hi i k).mul (component_diff ht k i))]
  apply Finset.sum_congr rfl; intro i _
  erw [actualScalarJet_sum _ (fun k _ => (hi i k).mul (component_diff ht k i))]
  apply Finset.sum_congr rfl; intro k _
  erw [actualScalarJet_mul (hi i k) (component_diff ht k i),actual_inverseMatrixJet hq h0]
  rfl

lemma fieldD_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0) : ContDiffAt ℝ 2 (fieldD b f) x :=
  (matrixTraceField_diff ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0).const_smul (1/4:ℝ)

lemma field_rawD (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0) :
    actualScalarJet (fieldD b f) x=rawD (fieldRaw b f x).1 := by
  unfold fieldD
  erw [actualScalarJet_smul _ (matrixTraceField_diff ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0),
    actual_matrixTraceJet ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0,
    field_rawQ b hf,field_rawC b hf]
  rfl

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

lemma source_logFields_regular {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) : f.logFields.RegularAt x := by
  have hσ := hf.sigma
  have hmg := hf.mg
  have hmk := hf.mK
  have hmr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hmg hmk hmr
  have hc3 := ((logRadiusChart_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt (x := x))
  have hc2 := ((logRadiusChart_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt (x := x))
  exact ⟨angularLift_diff hσ,angularLift_diff hmg,hf.eg.comp x hc3,contDiffAt_const,
    angularLift_diff hmk,hf.ek.comp x hc2,hf.b.comp x hc3,angularLift_diff hmr,hf.err.comp x hc2⟩

lemma sourceGamma_pullback (f : SourceMassFields) :
    (fun y => sourceGamma f (logRadiusChart y)) = logGamma f.logFields := by
  funext y
  simp [sourceGamma,logGamma,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

lemma sourceRadialMetric_pullback (f : SourceMassFields) :
    (fun y => sourceRadialMetric f (logRadiusChart y)) = logRadialMetric f.logFields := by
  funext y
  simp [sourceRadialMetric,logRadialMetric,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

lemma source_log_remainder_bounds {f : SourceMassFields} {x : Point} {B : ℝ} (hB : 0 ≤ B)
    (hf : f.RegularAt (logRadiusChart x)) (hb : f.ComponentBounds B (logRadiusChart x)) :
    ‖matrixThreeJets f.logFields.eg x‖ ≤ B/Real.exp (x 0)^2 ∧
    ‖matrixScalarJets f.logFields.ek x‖ ≤ B/Real.exp (x 0)^2 ∧
    ‖fun a => actualThreeJet (fun y => f.logFields.b y a) x‖ ≤ B/Real.exp (x 0)^3 ∧
    ‖actualScalarJet f.logFields.err x‖ ≤ B/Real.exp (x 0)^6 := by
  refine ⟨source_matrix_three_bound hB hf.eg hb.eg,source_matrix_two_bound hB hf.ek hb.ek,?_,
    source_two_jet_bound hB hf.err hb.err⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  exact source_three_jet_bound hB (contDiffAt_pi.mp hf.b a) (hb.b a)

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

lemma fieldT_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldT b f) x := by
  unfold fieldT; exact contDiffAt_const.mul (hf.2.2.1 0)
lemma fieldF_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldF b f) x :=
by
  unfold fieldF
  exact ((contDiffAt_const.mul (hf.2.2.1 1)).add (contDiffAt_const.mul (hf.2.2.1 4))).add contDiffAt_const

lemma field_rawT (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (fieldT b f) x=rawT (fieldRaw b f x).1 :=
  actualScalarJet_smul _ (hf.2.2.1 0)
lemma field_rawF (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (fieldF b f) x=rawF (fieldRaw b f x).1 := by
  unfold fieldF
  erw [actualScalarJet_add ((contDiffAt_const.mul (hf.2.2.1 1)).add (contDiffAt_const.mul (hf.2.2.1 4))) contDiffAt_const,
    actualScalarJet_add (contDiffAt_const.mul (hf.2.2.1 1)) (contDiffAt_const.mul (hf.2.2.1 4)),
    actualScalarJet_smul _ (hf.2.2.1 1),actualScalarJet_smul _ (hf.2.2.1 4),actualScalarJet_const]
  rfl
lemma field_rawL (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (fieldL b f) x=rawL (fieldRaw b f x).1 :=
  actualScalarJet_smul _ (hf.2.2.1 2)
lemma field_rawTr (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (fieldTr b f) x=rawTr (fieldRaw b f x).1 := by
  unfold fieldTr
  erw [actualScalarJet_sub (contDiffAt_const.mul (hf.2.2.1 3)) (contDiffAt_const.mul (hf.2.2.1 0)),
    actualScalarJet_smul _ (hf.2.2.1 3),actualScalarJet_smul _ (hf.2.2.1 0)]
  rfl

lemma field_rawA (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    actualScalarJet (fieldA b f) x=rawA (fieldRaw b f x).1 := by
  unfold fieldA
  rw [actual_lapseAField _ (fieldT_diff b hf) (fieldF_diff b hf) (fieldD_diff b hf h0) hr hd,
    field_rawT b hf,field_rawF b hf,field_rawD b hf h0]
  rfl

lemma field_normalizedLapse_jet (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    actualScalarJet (fieldNormalizedLapse b f) x=constantJet 1+b 0^3 • rawA (fieldRaw b f x).1 := by
  unfold fieldNormalizedLapse
  rw [actual_normalized_lapse_coefficient _ (fieldT_diff b hf) (fieldF_diff b hf) (fieldD_diff b hf h0) hr hd,
    field_rawT b hf,field_rawF b hf,field_rawD b hf h0]
  rfl

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
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma sourceMetric_pullback (f : SourceMassFields) (x : Point) :
    sourceMetric f (logRadiusChart x) = logMetric f.logFields x := by
  have hq := congrFun (sourceGamma_pullback f) x
  have hr := congrFun (sourceRadialMetric_pullback f) x
  unfold sourceMetric logMetric
  rw [hq,hr]
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

lemma traceFreeField_diff {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ 2 (traceFreeField q t) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  exact (component_diff ht i k).sub
    ((contDiffAt_const.mul (matrixTraceField_diff hq ht h0)).mul (component_diff hq i k))

lemma actual_traceFreeJet {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    matrixScalarJets (traceFreeField q t) x=traceFreeJet (matrixScalarJets q x) (matrixScalarJets t x) := by
  funext i k
  change actualScalarJet (fun y => t y i k-(1/2:ℝ)*(∑ a, ∑ b, inverse (q y) a b*t y b a)*q y i k) x=_
  have htrace := matrixTraceField_diff hq ht h0
  erw [actualScalarJet_sub (component_diff ht i k) ((contDiffAt_const.mul htrace).mul (component_diff hq i k)),
    actualScalarJet_mul (contDiffAt_const.mul htrace) (component_diff hq i k),
    actualScalarJet_smul (1/2:ℝ) htrace,actual_matrixTraceJet hq ht h0]
  unfold traceFreeJet
  rw [productJet_smul_left]
  rfl

lemma field_rawEta (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    (fun a => actualScalarJet (fun y => fieldEta b f y a) x)=
      (1-re (fieldRaw b f x).1) • reta (fieldRaw b f x).1 := by
  funext a
  exact actualScalarJet_smul (1-b 1) (contDiffAt_pi.mp hf.2.2.2.1 a)

lemma field_rawTau (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0) :
    matrixScalarJets (fieldTau b f) x=
      (1-re (fieldRaw b f x).1) • traceFreeJet (rawQ (fieldRaw b f x).1) (rtau (fieldRaw b f x).1) := by
  unfold fieldTau
  rw [matrixScalarJets_smul _ (traceFreeField_diff ((fieldQ_diff b hf).of_le (by norm_num)) hf.2.2.2.2 h0),
    actual_traceFreeJet ((fieldQ_diff b hf).of_le (by norm_num)) hf.2.2.2.2 h0,field_rawQ b hf]
  rfl

lemma field_rawX (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    fieldX b f x=rawX (fieldRaw b f x).1 := by
  have hl := congrArg Prod.fst (field_normalizedLapse_jet b hf h0 hr hd)
  change fieldNormalizedLapse b f x=1+b 0^3*(rawA (fieldRaw b f x).1).1 at hl
  have ht := actual_traceFreeJet ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0
  rw [field_rawQ b hf,field_rawC b hf] at ht
  funext i k
  have hv := congrArg (fun t : MatrixScalarJet => (t i k).1) ht
  change traceFreeField (fieldQ b f) (fieldC b f) x i k=(traceFreeJet _ _ i k).1 at hv
  change (Real.sqrt (1+b 0^2)*fieldNormalizedLapse b f x/2)*traceFreeField (fieldQ b f) (fieldC b f) x i k=_
  rw [hl,hv]
  rfl

end
end CKSAngularGeometry

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

lemma matrixDerivedJets_norm_le_three (q : Point → Mat) (x : Point) (a : I) :
    ‖matrixScalarJets (fun y i k => D (basis a) (fun z => q z i k) y) x‖ ≤ ‖matrixThreeJets q x‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro i k
  exact ((norm_le_pi_norm (matrixThreeJets q x i k).2 a).trans
    (norm_snd_le (matrixThreeJets q x i k))).trans
    (Matrix.norm_entry_le_entrywise_sup_norm (matrixThreeJets q x))

def CollarCoefficientFields.BoundedAt (f : CollarCoefficientFields) (B : ℝ) (x : Point) : Prop :=
  (∀ i : Fin 2, ‖matrixThreeJets (f.metric i.castSucc) x‖ ≤ B) ∧
  ‖matrixScalarJets (f.metric 2) x‖ ≤ B ∧
  ‖fun a => actualThreeJet (fun y => f.shift y a) x‖ ≤ B ∧
  (∀ i, ‖actualScalarJet (f.scalar i) x‖ ≤ B) ∧
  ‖fun a => actualScalarJet (fun y => f.eta y a) x‖ ≤ B ∧
  ‖matrixScalarJets f.tau x‖ ≤ B ∧ ‖f.etar x‖ ≤ B ∧
  |f.massRadial x| ≤ B ∧ |f.massGap x| ≤ B

lemma fieldRaw_norm {b : Fin 5 → ℝ} {f : CollarCoefficientFields} {x : Point}
    {B : ℝ} (hB : 0 ≤ B) (hb : ‖b‖ ≤ B) (hf : f.BoundedAt B x) :
    ‖fieldRaw b f x‖ ≤ B := by
  apply norm_prod_le_iff.mpr
  constructor
  · apply norm_prod_le_iff.mpr
    refine ⟨hb,?_⟩
    apply norm_prod_le_iff.mpr
    constructor
    · apply norm_prod_le_iff.mpr
      constructor
      · apply norm_prod_le_iff.mpr
        constructor
        · apply (pi_norm_le_iff_of_nonneg hB).mpr
          intro i
          fin_cases i
          · exact (matrixScalarJets_norm_le_three _ _).trans (hf.1 0)
          · exact (matrixScalarJets_norm_le_three _ _).trans (hf.1 1)
          · exact hf.2.1
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro i
          apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          exact (matrixDerivedJets_norm_le_three _ _ _).trans (hf.1 i)
      · apply norm_prod_le_iff.mpr
        constructor
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          exact (norm_fst_le (actualThreeJet (fun y => f.shift y a) x)).trans
            ((norm_le_pi_norm (fun a => actualThreeJet (fun y => f.shift y a) x) a).trans hf.2.2.1)
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          apply (pi_norm_le_iff_of_nonneg hB).mpr; intro k
          exact ((norm_le_pi_norm (actualThreeJet (fun y => f.shift y k) x).2 a).trans
            (norm_snd_le (actualThreeJet (fun y => f.shift y k) x))).trans
            ((norm_le_pi_norm (fun k => actualThreeJet (fun y => f.shift y k) x) k).trans hf.2.2.1)
    · apply norm_prod_le_iff.mpr
      constructor
      · exact norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg hB).mpr hf.2.2.2.1,hf.2.2.2.2.1⟩
      · exact norm_prod_le_iff.mpr ⟨hf.2.2.2.2.2.1,hf.2.2.2.2.2.2.1⟩
  · apply norm_prod_le_iff.mpr
    simpa only [fieldRaw, Real.norm_eq_abs] using (show ‖f.massRadial x‖ ≤ B ∧ ‖f.massGap x‖ ≤ B from
      And.intro (by simpa only [Real.norm_eq_abs] using hf.2.2.2.2.2.2.2.1)
        (by simpa only [Real.norm_eq_abs] using hf.2.2.2.2.2.2.2.2))

end
end CKSAngularGeometry

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

lemma thinRaw_old (p : RawNullInput) : thinRaw (rawNullOriginal p)=rawNullOriginal (thinRaw p) := rfl

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma injection_basis (a : A) : injection (CKSAngularGeometry.basis a)=CKSMixedGeometry.basis a.succ := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [CKSMixedGeometry.basis]
  · simp [CKSAngularGeometry.basis,CKSMixedGeometry.basis,Pi.single_apply]

lemma slice_hasFDerivAt (r : ℝ) (x : AP) : HasFDerivAt (slice r) injection x :=
  injection.hasFDerivAt.const_add _
lemma slice_smooth (r : ℝ) : ContDiff ℝ ∞ (slice r) :=
  contDiff_const.add injection.contDiff

lemma D_slice (a : A) (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : DifferentiableAt ℝ f (slice r x)) :
    D (CKSAngularGeometry.basis a) (fun y => f (slice r y)) x=
      D (CKSMixedGeometry.basis a.succ) f (slice r x) := by
  unfold D
  erw [fderiv_comp x hf (slice_hasFDerivAt r x).differentiableAt,
    (slice_hasFDerivAt r x).fderiv,ContinuousLinearMap.comp_apply,injection_basis]

 def restrictJet (p : CKSMixedGeometry.ScalarJet) : CKSAngularGeometry.ScalarJet :=
  (p.1,fun a => p.2.1 a.succ,fun a b => p.2.2 a.succ b.succ)
 def restrictThree (p : CKSMixedGeometry.ScalarThreeJet) : CKSAngularGeometry.ScalarThreeJet :=
  (restrictJet p.1,fun a => restrictJet (p.2 a.succ))

lemma actualScalarJet_slice (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 2 f (slice r x)) :
    CKSAngularGeometry.actualScalarJet (fun y => f (slice r y)) x=
      restrictJet (CKSMixedGeometry.actualScalarJet f (slice r x)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a; exact D_slice a r (hf.differentiableAt (by norm_num))
  · funext a b
    have he : D (CKSAngularGeometry.basis b) (fun y => f (slice r y)) =ᶠ[𝓝 x]
        (fun y => D (CKSMixedGeometry.basis b.succ) f (slice r y)) := by
      have hn := (slice_smooth r).continuous.continuousAt.tendsto.eventually (hf.eventually (by simp))
      filter_upwards [hn] with y hy
      exact D_slice b r (hy.differentiableAt (by norm_num))
    change D (CKSAngularGeometry.basis a) (D (CKSAngularGeometry.basis b) (fun y => f (slice r y))) x=_
    rw [D_congr he]
    exact D_slice a r ((contDiffAt_D hf (m:=1) (by norm_num) _).differentiableAt (by norm_num))

lemma actualThreeJet_slice (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 3 f (slice r x)) :
    CKSAngularGeometry.actualThreeJet (fun y => f (slice r y)) x=
      restrictThree (CKSMixedGeometry.actualThreeJet f (slice r x)) := by
  apply Prod.ext (actualScalarJet_slice r (hf.of_le (by norm_num)))
  funext a
  have he : D (CKSAngularGeometry.basis a) (fun y => f (slice r y)) =ᶠ[𝓝 x]
      (fun y => D (CKSMixedGeometry.basis a.succ) f (slice r y)) := by
    have hn := (slice_smooth r).continuous.continuousAt.tendsto.eventually (hf.eventually (by simp))
    filter_upwards [hn] with y hy
    exact D_slice a r (hy.differentiableAt (by norm_num))
  change CKSAngularGeometry.actualScalarJet (D (CKSAngularGeometry.basis a) (fun y => f (slice r y))) x=_
  rw [CKSAngularGeometry.actualScalarJet_congr he]
  exact actualScalarJet_slice r (contDiffAt_D hf (m:=2) (by norm_num) _)

lemma restrictJet_norm (p : CKSMixedGeometry.ScalarJet) : ‖restrictJet p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨norm_fst_le p, norm_prod_le_iff.mpr ⟨?_,?_⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
    intro a
    exact (norm_le_pi_norm p.2.1 a.succ).trans ((norm_fst_le p.2).trans (norm_snd_le p))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
    intro b
    exact ((norm_le_pi_norm (p.2.2 a.succ) b.succ).trans (norm_le_pi_norm p.2.2 a.succ)).trans
      ((norm_snd_le p.2).trans (norm_snd_le p))

lemma restrictThree_norm (p : CKSMixedGeometry.ScalarThreeJet) : ‖restrictThree p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨(restrictJet_norm p.1).trans (norm_fst_le p),?_⟩
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
  intro a
  exact (restrictJet_norm (p.2 a.succ)).trans ((norm_le_pi_norm p.2 a.succ).trans (norm_snd_le p))

lemma angular_twojet_le_mixed (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 2 f (slice r x)) :
    ‖CKSAngularGeometry.actualScalarJet (fun y => f (slice r y)) x‖ ≤
      ‖CKSMixedGeometry.actualScalarJet f (slice r x)‖ := by
  rw [actualScalarJet_slice r hf]; exact restrictJet_norm _
lemma angular_threejet_le_mixed (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : ContDiffAt ℝ 3 f (slice r x)) :
    ‖CKSAngularGeometry.actualThreeJet (fun y => f (slice r y)) x‖ ≤
      ‖CKSMixedGeometry.actualThreeJet f (slice r x)‖ := by
  rw [actualThreeJet_slice r hf]; exact restrictThree_norm _

end
end CKSAngularSlice

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

def CollarCoefficientFields.freezeRadial (f : CollarCoefficientFields) (x : Point) : CollarCoefficientFields :=
  { f with scalar := fun i y => if i=3 then f.scalar 3 x else f.scalar i y }

lemma fieldRaw_freeze (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) :
    fieldRaw b (f.freezeRadial x) x=thinRaw (fieldRaw b f x) := by
  have he : (fun i => actualScalarJet ((f.freezeRadial x).scalar i) x)=
      (fun i => if i=3 then constantJet (actualScalarJet (f.scalar i) x).1 else actualScalarJet (f.scalar i) x) := by
    funext i
    by_cases hi : i=3
    · subst i; simp only [CollarCoefficientFields.freezeRadial,ite_true]
      exact actualScalarJet_const _ _
    · simp only [CollarCoefficientFields.freezeRadial,hi,ite_false]
  unfold fieldRaw
  rw [he]
  rfl

lemma freezeRadial_bounded {f : CollarCoefficientFields} {B : ℝ} {x : Point}
    (hB : 0 ≤ B) (hf : f.ThinBoundedAt B x) : (f.freezeRadial x).BoundedAt B x := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,hf.2.2.2.2.2⟩
  intro i
  by_cases hi : i=3
  · subst i
    change ‖actualScalarJet (fun _ : Point => f.scalar 3 x) x‖ ≤ B
    rw [actualScalarJet_const]
    exact norm_prod_le_iff.mpr ⟨by simpa only [constantJet,Real.norm_eq_abs] using hf.2.2.2.2.1,
      norm_prod_le_iff.mpr ⟨by simpa [constantJet] using hB,by simpa [constantJet] using hB⟩⟩
  · simpa only [CollarCoefficientFields.freezeRadial,hi,ite_false] using hf.2.2.2.1 i hi

lemma fieldRaw_thin_norm {b : Fin 5 → ℝ} {f : CollarCoefficientFields} {B : ℝ} {x : Point}
    (hB : 0 ≤ B) (hb : ‖b‖ ≤ B) (hf : f.ThinBoundedAt B x) :
    ‖thinRaw (fieldRaw b f x)‖ ≤ B := by
  rw [← fieldRaw_freeze]
  exact fieldRaw_norm hB hb (freezeRadial_bounded hB hf)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma normalized_angular_two {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hf : ContDiffAt ℝ 2 f (slice ρ x))
    (hb : ‖CKSMixedGeometry.actualScalarJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    ‖CKSAngularGeometry.actualScalarJet (fun y => Real.exp ρ^n*f (slice ρ y)) x‖ ≤ B := by
  have hd : ContDiffAt ℝ 2 (fun y => f (slice ρ y)) x :=
    hf.comp x ((slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [CKSAngularGeometry.actualScalarJet_smul _ hd,norm_smul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (Real.exp_pos ρ) n)]
  calc
    _ ≤ Real.exp ρ^n*(B/Real.exp ρ^n) := mul_le_mul_of_nonneg_left
      ((angular_twojet_le_mixed ρ hf).trans hb) (by positivity)
    _ = B := by field_simp

lemma normalized_angular_three {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hf : ContDiffAt ℝ 3 f (slice ρ x))
    (hb : ‖CKSMixedGeometry.actualThreeJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    ‖CKSAngularGeometry.actualThreeJet (fun y => Real.exp ρ^n*f (slice ρ y)) x‖ ≤ B := by
  have hd : ContDiffAt ℝ 3 (fun y => f (slice ρ y)) x :=
    hf.comp x ((slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤)))
  rw [CKSAngularGeometry.actualThreeJet_smul _ hd,norm_smul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (Real.exp_pos ρ) n)]
  calc
    _ ≤ Real.exp ρ^n*(B/Real.exp ρ^n) := mul_le_mul_of_nonneg_left
      ((angular_threejet_le_mixed ρ hf).trans hb) (by positivity)
    _ = B := by field_simp

lemma radial_value_le_jet (f : MP → ℝ) (x : MP) :
    |D (CKSMixedGeometry.basis 0) f x| ≤ ‖CKSMixedGeometry.actualScalarJet f x‖ := by
  change ‖(CKSMixedGeometry.actualScalarJet f x).2.1 0‖ ≤ _
  exact (norm_le_pi_norm _ 0).trans ((norm_fst_le _).trans (norm_snd_le _))

lemma normalized_radial_value {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hb : ‖CKSMixedGeometry.actualScalarJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    |Real.exp ρ^n*D (CKSMixedGeometry.basis 0) f (slice ρ x)| ≤ B := by
  rw [abs_mul,abs_of_pos (pow_pos (Real.exp_pos ρ) n)]
  exact (mul_le_mul_of_nonneg_left ((radial_value_le_jet f _).trans hb) (by positivity)).trans_eq (by field_simp)

lemma normalized_value {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hb : ‖CKSMixedGeometry.actualScalarJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    |Real.exp ρ^n*f (slice ρ x)| ≤ B := by
  rw [abs_mul,abs_of_pos (pow_pos (Real.exp_pos ρ) n)]
  have hv : |f (slice ρ x)| ≤ ‖CKSMixedGeometry.actualScalarJet f (slice ρ x)‖ := by
    simpa only [CKSMixedGeometry.actualScalarJet,Prod.fst,Real.norm_eq_abs] using (norm_fst_le (CKSMixedGeometry.actualScalarJet f (slice ρ x)))
  exact (mul_le_mul_of_nonneg_left (hv.trans hb) (by positivity)).trans_eq (by field_simp)

lemma normalized_angular_radial_two {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hf : ContDiffAt ℝ 3 f (slice ρ x))
    (hb : ‖CKSMixedGeometry.actualThreeJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    ‖CKSAngularGeometry.actualScalarJet
      (fun y => Real.exp ρ^n*D (CKSMixedGeometry.basis 0) f (slice ρ y)) x‖ ≤ B := by
  apply normalized_angular_two n (contDiffAt_D hf (m:=2) (by norm_num) _)
  exact ((norm_le_pi_norm (CKSMixedGeometry.actualThreeJet f (slice ρ x)).2 0).trans (norm_snd_le _)).trans hb

end
end CKSAngularSlice

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

lemma field_momentum_realization (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x) (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    fieldMomentumInput b f x=rawMomentumInput (fieldRaw b f x).1 := by
  have hq : actualJet (fieldQ b f) x=scalarMatrixToJet (rawQ (fieldRaw b f x).1) := by
    rw [← field_rawQ b hf]; rfl
  have hs : (fun a => actualScalarJet (fun y => fieldS b f y a) x)=rawS (fieldRaw b f x).1 :=
    funext (field_rawS b hf)
  have he : fieldEr b f x=(fun a => (1-re (fieldRaw b f x).1)*retar (fieldRaw b f x).1 a-
      rθ (fieldRaw b f x).1*(reta (fieldRaw b f x).1 a).1) := rfl
  unfold fieldMomentumInput rawMomentumInput
  rw [hq,hs,he,field_rawA b hf h0 hr hd,field_rawT b hf,field_rawL b hf,
    field_rawTr b hf,field_rawD b hf h0,field_rawEta b hf,field_rawTau b hf h0,
    field_rawX b hf h0 hr hd]
  rfl

lemma field_null_realization (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x) (h0 : determinant (fieldQ b f x) ≠ 0)
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : lapseDField (b 0) (fieldD b f) x ≠ 0) :
    fieldNullInput b f x=rawNullMap (fieldRaw b f x) := by
  unfold fieldNullInput rawNullMap
  rw [field_momentum_realization b hf h0 hr hd,field_rawF b hf]
  rfl

lemma fieldRaw_old (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) :
    fieldRaw (oldParams b) f x=rawNullOriginal (fieldRaw b f x) := rfl

lemma field_angular_matrix (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x) : fieldQ b f x=rawAngularMatrix (fieldRaw b f x) := by
  have hh := field_rawQ b hf
  exact congrArg (fun q : MatrixScalarJet => fun i k => (q i k).1) hh

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev AJ := CKSAngularGeometry.actualScalarJet

structure LogCollarData.RegularAt (f : LogCollarData) (x : MP) : Prop where
  sigma : ContDiffAt ℝ 3 f.sigma x
  metricError : ContDiffAt ℝ 3 f.metricError x
  shift : ContDiffAt ℝ 3 f.shift x
  tError : ContDiffAt ℝ 2 f.tError x
  LError : ContDiffAt ℝ 2 f.LError x
  massError : ContDiffAt ℝ 2 f.massError x
  fstar : ContDiffAt ℝ 2 f.fstar x
  etaDivR : ContDiffAt ℝ 2 f.etaDivR x
  tauDivR2 : ContDiffAt ℝ 2 f.tauDivR2 x

theorem angular_thin_bounded {f : LogCollarData} {ρ B : ℝ} {x : AP}
    (hB : 0 ≤ B) (hr : 1 ≤ Real.exp ρ) (hf : f.RegularAt (slice ρ x))
    (hb : f.BoundedAt B (slice ρ x)) : (f.angular ρ).ThinBoundedAt (2*B) x := by
  have hB2 : B ≤ 2*B := by linarith
  have hc (n : ℕ) : ContDiffAt ℝ n (slice ρ) x :=
    (slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))
  have hmc (a b : A) := CKSMixedGeometry.component_diff hf.metricError a b
  have hsg (a b : A) := CKSMixedGeometry.component_diff hf.sigma a b
  have hme (a b : A) : ‖M3 (fun z => f.metricError z a b) (slice ρ x)‖ ≤ B/Real.exp ρ^3 := by
    simpa only [slice_zero] using hb.metricError a b
  have htv : ‖MJ f.tError (slice ρ x)‖ ≤ B/Real.exp ρ^3 := by simpa only [slice_zero] using hb.tError
  have hlv : ‖MJ f.LError (slice ρ x)‖ ≤ B/Real.exp ρ^3 := by simpa only [slice_zero] using hb.LError
  have hmv : ‖MJ f.massError (slice ρ x)‖ ≤ B/Real.exp ρ := by simpa only [slice_zero] using hb.massError
  have hev (a : A) : ‖MJ (fun z => f.etaDivR z a) (slice ρ x)‖ ≤ B/Real.exp ρ^3 := by
    simpa only [slice_zero] using hb.etaDivR a
  unfold CKSAngularGeometry.CollarCoefficientFields.ThinBoundedAt
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro b
    fin_cases i
    · exact ((angular_threejet_le_mixed ρ (hsg a b)).trans (hb.sigma a b)).trans hB2
    · exact (normalized_angular_three 3 (hmc a b) (hme a b)).trans hB2
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro b
    exact (normalized_angular_radial_two 3 (hmc a b) (hme a b)).trans hB2
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    apply (normalized_angular_three 5 (contDiffAt_pi.mp hf.shift a) ?_).trans hB2
    simpa only [slice_zero] using hb.shift a
  · intro i hi
    fin_cases i
    · exact (normalized_angular_two 3 hf.tError htv).trans hB2
    · change ‖AJ (fun y => f.fstar (slice ρ y)+f.massError (slice ρ y)) x‖ ≤ _
      have hfs : ContDiffAt ℝ 2 (fun y => f.fstar (slice ρ y)) x := hf.fstar.comp x (hc 2)
      have hfm : ContDiffAt ℝ 2 (fun y => f.massError (slice ρ y)) x := hf.massError.comp x (hc 2)
      change ‖CKSAngularGeometry.actualScalarJet (fun y => f.fstar (slice ρ y)+f.massError (slice ρ y)) x‖ ≤ _
      rw [CKSAngularGeometry.actualScalarJet_add hfs hfm]
      have hm : ‖AJ (fun y => f.massError (slice ρ y)) x‖ ≤ B :=
        ((angular_twojet_le_mixed ρ hf.massError).trans hmv).trans (div_le_self hB hr)
      exact (norm_add_le _ _).trans (add_le_add ((angular_twojet_le_mixed ρ hf.fstar).trans hb.fstar) hm) |>.trans_eq (by ring)
    · exact (normalized_angular_two 3 hf.LError hlv).trans hB2
    · exact (hi rfl).elim
    · exact ((angular_twojet_le_mixed ρ hf.fstar).trans hb.fstar).trans hB2
  · exact (normalized_radial_value 3 htv).trans hB2
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    exact (normalized_angular_two 3 (contDiffAt_pi.mp hf.etaDivR a) (hev a)).trans hB2
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro b
    apply (normalized_angular_two 3 (CKSMixedGeometry.component_diff hf.tauDivR2 a b) ?_).trans hB2
    simpa only [slice_zero] using hb.tauDivR2 a b
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    change |Real.exp ρ^3*(_+_)| ≤ _
    rw [mul_add]
    exact (abs_add_le _ _).trans ((add_le_add (normalized_value 3 (hev a))
      (normalized_radial_value 3 (hev a))).trans_eq (by ring))
  · simpa only [LogCollarData.angular,pow_one] using (normalized_radial_value 1 (by simpa only [pow_one] using hmv)).trans hB2
  · simpa only [LogCollarData.angular,pow_one] using (normalized_value 1 (by simpa only [pow_one] using hmv)).trans hB2

end
end CKSAngularSlice

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

lemma sourceCollarData_regular {f : TensorFields} {x : Point}
    (hf : f.RegularAt x) (hp : ∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef)
    (hs : determinant (f.base.sigma x) ≠ 0) : (sourceCollarData f).RegularAt x := by
  have hlead := cksLeadingField_diff hf.base hs
  exact ⟨hf.base.sigma,logQError_diff hf.base,logShift_diff hf.base hp.self_of_nhds,
    logTError_diff hf.base hp,logOriginalLError_diff hf hp,
    (logPhysicalMass_diff hf.base hp).sub hlead,hlead,
    logOriginalEtaDiv_diff hf hp,logOriginalTauDiv_diff hf hp⟩

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
open CKSAngularGeometry (determinant determinant_eq inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma logTError_three_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hK : ContDiffAt ℝ 3 f.mK x) (hk : ContDiffAt ℝ 3 f.ek x)
    (hp : (logMetric f x).PosDef) : ContDiffAt ℝ 3 (fun y => logT f y-1) x := by
  have he : ContDiffAt ℝ 3 (fun y : Point => Real.exp (y 0)) x := by fun_prop
  have he1 : ContDiffAt ℝ 3 (fun y : Point => 1/Real.exp (y 0)) x :=
    contDiffAt_const.div he (Real.exp_ne_zero _)
  have hq : ContDiffAt ℝ 3 (logGamma f) x :=
    ((he.pow 2).smul hf.sigma |>.add (he1.smul hf.mg)).add hf.eg
  have ht : ContDiffAt ℝ 3 (logTangentialK f) x :=
    ((he.pow 2).smul hf.sigma |>.add (he1.smul hK)).add hk
  have hd : determinant (logGamma f x) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_diff_at hq hd
  unfold logT traceProduct
  apply ContDiffAt.sub _ contDiffAt_const
  apply ContDiffAt.mul contDiffAt_const
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hi i k).mul (component_diff ht k i)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma angular_regular {f : LogCollarData} {ρ : ℝ} {x : AP}
    (hf : f.RegularAt (slice ρ x))
    (ht : ContDiffAt ℝ 3 f.tError (slice ρ x)) : (f.angular ρ).RegularAt x := by
  have hc (n : ℕ) : ContDiffAt ℝ n (slice ρ) x :=
    (slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))
  have hs : ContDiffAt ℝ 3 (fun y => f.sigma (slice ρ y)) x := hf.sigma.comp x (hc 3)
  have hq : ContDiffAt ℝ 3 (fun y => Real.exp ρ^3 • f.metricError (slice ρ y)) x :=
    (hf.metricError.comp x (hc 3)).const_smul (Real.exp ρ^3)
  have hqr : ContDiffAt ℝ 2 (fun y a b => Real.exp ρ^3*
      D (CKSMixedGeometry.basis 0) (fun z => f.metricError z a b) (slice ρ y)) x := by
    apply contDiffAt_pi.mpr; intro a
    apply contDiffAt_pi.mpr; intro b
    simpa only [smul_eq_mul, Function.comp_apply] using
      ((contDiffAt_D (CKSMixedGeometry.component_diff hf.metricError a b)
      (m:=2) (by norm_num) (CKSMixedGeometry.basis 0)).comp x (hc 2)).const_smul (Real.exp ρ^3)
  refine ⟨⟨hs,hq,hqr⟩,?_,?_,?_,?_⟩
  · exact (hf.shift.comp x (hc 3)).const_smul (Real.exp ρ^5)
  · intro i
    fin_cases i
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*f.tError (slice ρ y)) x
      exact contDiffAt_const.mul (hf.tError.comp x (hc 2))
    · exact (hf.fstar.comp x (hc 2)).add (hf.massError.comp x (hc 2))
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*f.LError (slice ρ y)) x
      exact contDiffAt_const.mul (hf.LError.comp x (hc 2))
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*D (CKSMixedGeometry.basis 0) f.tError (slice ρ y)) x
      exact contDiffAt_const.mul ((contDiffAt_D ht (m:=2) (by norm_num) (CKSMixedGeometry.basis 0)).comp x (hc 2))
    · exact hf.fstar.comp x (hc 2)
  · exact (hf.etaDivR.comp x (hc 2)).const_smul (Real.exp ρ^3)
  · exact (hf.tauDivR2.comp x (hc 2)).const_smul (Real.exp ρ^3)

end
end CKSAngularSlice

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

theorem bounded_thin_field_coordinate_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      (fieldQ b f x) 1 0=(fieldQ b f x) 0 1 →
      (fieldQ (oldParams b) f x) 1 0=(fieldQ (oldParams b) f x) 0 1 →
      determinant (fieldQ b f x) ≠ 0 → determinant (fieldQ (oldParams b) f x) ≠ 0 →
      0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x →
      0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) f) (fieldF (oldParams b) f) x →
      lapseDField (b 0) (fieldD b f) x ≠ 0 →
      lapseDField ((oldParams b) 0) (fieldD (oldParams b) f) x ≠ 0 →
      coordinateDEC (fieldNullInput (oldParams b) f x) r → coordinateDEC (fieldNullInput b f x) r := by
  obtain ⟨R,hR,hh⟩ := bounded_thin_field_map_DEC hK hreg hB hA
  refine ⟨R,hR,?_⟩
  intro b f x hf hq hb hbound r hr hz hw hparams hs hs₀ hdet hdet₀ hrad hrad₀ hd hd₀ hDEC
  rw [field_null_realization b hf hdet hrad hd]
  rw [field_null_realization (oldParams b) hf hdet₀ hrad₀ hd₀,fieldRaw_old] at hDEC
  rw [field_angular_matrix b hf] at hs
  rw [field_angular_matrix (oldParams b) hf,fieldRaw_old] at hs₀
  exact hh b f x hq hb hbound r hr hz hw hparams hs hs₀ hDEC

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
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma source_tensor_log_regular {f : SourceTensorFields} {x : Point} (hf : f.RegularAt (logRadiusChart x)) :
    f.logFields.RegularAt x := by
  have hc := (logRadiusChart_smooth.contDiffAt (x := x)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact ⟨source_logFields_regular hf.base,hf.kr.comp x hc,hf.kb.comp x hc⟩

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

lemma thinRaw_primitive_regular (p : RawNullInput) :
    (rawRegular (thinRaw p).1 ∧ rawLapseInput (thinRaw p).1 ∈ lapseCoefficientRegion) ↔
      (rawRegular p.1 ∧ rawLapseInput p.1 ∈ lapseCoefficientRegion) := by
  have hq : rawRegular (thinRaw p).1 ↔ rawRegular p.1 := by
    unfold rawRegular
    rw [thinQ]
  have hl : rawLapseInput (thinRaw p).1=rawLapseInput p.1 := by
    unfold rawLapseInput
    rw [thinT,thinF,thinD]
    rfl
  rw [hq,hl]

lemma field_primitive_regular (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x)
    (hp : rawRegular (fieldRaw b f x).1 ∧ rawLapseInput (fieldRaw b f x).1 ∈ lapseCoefficientRegion) :
    determinant (fieldQ b f x) ≠ 0 ∧
    0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x ∧
    lapseDField (b 0) (fieldD b f) x ≠ 0 := by
  have hq : determinant (fieldQ b f x) ≠ 0 := by
    rw [field_angular_matrix b hf]
    exact hp.1
  refine ⟨hq,?_,?_⟩
  · have hh := congrArg Prod.fst (actual_lapseRadField (b 0) (fieldT_diff b hf)
      (fieldF_diff b hf) (rawD (fieldRaw b f x).1))
    rw [field_rawT b hf,field_rawF b hf] at hh
    change lapseRadField (b 0) (fieldT b f) (fieldF b f) x=
      (lapseRad (rawLapseInput (fieldRaw b f x).1)).1 at hh
    rw [hh]
    exact hp.2.1
  · have hh := congrArg Prod.fst (actual_lapseDField (b 0) (fieldD_diff b hf hq)
      (rawT (fieldRaw b f x).1) (rawF (fieldRaw b f x).1))
    rw [field_rawD b hf hq] at hh
    change lapseDField (b 0) (fieldD b f) x=(lapseD (rawLapseInput (fieldRaw b f x).1)).1 at hh
    rw [hh]
    exact hp.2.2

theorem bounded_thin_field_regions {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r →
      (determinant (fieldQ b f x) ≠ 0 ∧
        0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x ∧
        lapseDField (b 0) (fieldD b f) x ≠ 0) ∧
      (determinant (fieldQ (oldParams b) f x) ≠ 0 ∧
        0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) f) (fieldF (oldParams b) f) x ∧
        lapseDField ((oldParams b) 0) (fieldD (oldParams b) f) x ≠ 0) := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  obtain ⟨δ,hδ,hdom⟩ := (rawReferenceFamily_compact hK B).exists_cthickening_subset_open
    rawNullDomain_open (rawReferenceFamily_regular hreg B)
  refine ⟨max 1 (1/δ),le_max_left _ _,?_⟩
  intro b f x hf hq hb hbound r hr hz
  obtain ⟨_,hd⟩ := inverse_radius_threshold hδ hr
  have hh : |rz (thinRaw (fieldRaw b f x)).1| ≤ δ := by change |b 0| ≤ δ; rw [hz]; exact hd
  obtain ⟨hp,hp₀⟩ := raw_reference_tube (p:=thinRaw (fieldRaw b f x)) hq
    (fieldRaw_thin_norm hB hb hbound) hh
  have h1 := hdom hp
  have h0 := hdom hp₀
  have h1' := (thinRaw_primitive_regular (fieldRaw b f x)).mp ⟨h1.1,h1.2.1⟩
  have h0' : rawRegular (thinRaw (fieldRaw (oldParams b) f x)).1 ∧
      rawLapseInput (thinRaw (fieldRaw (oldParams b) f x)).1 ∈ lapseCoefficientRegion := by
    rw [fieldRaw_old,thinRaw_old]
    exact ⟨h0.1,h0.2.1⟩
  exact ⟨field_primitive_regular b hf h1',field_primitive_regular (oldParams b) hf
    ((thinRaw_primitive_regular (fieldRaw (oldParams b) f x)).mp h0')⟩

theorem bounded_thin_coordinate_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      f.metric 0 x 1 0=f.metric 0 x 0 1 → f.metric 1 x 1 0=f.metric 1 x 0 1 →
      coordinateDEC (fieldNullInput (oldParams b) f x) r → coordinateDEC (fieldNullInput b f x) r := by
  obtain ⟨R,hR,hh⟩ := bounded_thin_field_coordinate_DEC hK hreg hB hA
  obtain ⟨T,hT,ht⟩ := bounded_thin_field_regions hK (fun q hq => (hreg q hq).2.ne') hB
  refine ⟨max R T,hR.trans (le_max_left _ _),?_⟩
  intro b f x hf hq hb hbound r hr hz hw hparams hs₀ hs₁ hDEC
  obtain ⟨⟨hq₁,hr₁,hd₁⟩,⟨hq₀,hr₀,hd₀⟩⟩ := ht b f x hf hq hb hbound r
    ((le_max_right _ _).trans hr) hz
  have hsym (c : Fin 5 → ℝ) : fieldQ c f x 1 0=fieldQ c f x 0 1 := by
    change f.metric 0 x 1 0+(c 0^3*(1-c 1))*f.metric 1 x 1 0 =
      f.metric 0 x 0 1+(c 0^3*(1-c 1))*f.metric 1 x 0 1
    rw [hs₀,hs₁]
  exact hh b f x hf hq hb hbound r ((le_max_left _ _).trans hr) hz hw hparams
    (hsym b) (hsym (oldParams b)) hq₁ hq₀ hr₁ hr₀ hd₁ hd₀ hDEC

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def restrictMatrixThree (q : CKSMixedGeometry.MatrixThreeJet) : CKSAngularGeometry.MatrixScalarJet :=
  fun a b => restrictJet (q a b).1

lemma restrictMatrixThree_continuous : Continuous restrictMatrixThree := by
  unfold restrictMatrixThree restrictJet
  fun_prop

lemma sigma_slice_jets {f : MP → CKSAngularGeometry.Mat} {ρ : ℝ} {x : AP}
    (hf : ContDiffAt ℝ 3 f (slice ρ x)) :
    CKSAngularGeometry.matrixScalarJets (fun y => f (slice ρ y)) x=
      restrictMatrixThree (CKSMixedGeometry.matrixThreeJets f (slice ρ x)) := by
  funext a b
  exact actualScalarJet_slice ρ ((CKSMixedGeometry.component_diff hf a b).of_le (by norm_num))

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open scoped Matrix.Norms.Elementwise
lemma CollarCoefficientFields.ThinBoundedAt.mono {f : CollarCoefficientFields} {x : Point}
    {B C : ℝ} (hf : f.ThinBoundedAt B x) (hBC : B ≤ C) : f.ThinBoundedAt C x := by
  rcases hf with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  exact ⟨fun i => (h1 i).trans hBC,h2.trans hBC,h3.trans hBC,
    fun i hi => (h4 i hi).trans hBC,h5.trans hBC,h6.trans hBC,h7.trans hBC,
    h8.trans hBC,h9.trans hBC,h10.trans hBC⟩
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma logQError_scaled (f : MassFields) (x : Point) :
    logQError f x=(1/Real.exp (x 0)^2) • logGamma f x-f.sigma x := by
  funext a b
  simp only [logQError,logGamma,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [show (-3:ℝ)=-(3:ℕ) by norm_num,show (-2:ℝ)=-(2:ℕ) by norm_num,
    radiusPower_neg_nat,radiusPower_neg_nat]
  field_simp
  ring

lemma logQError_symmetric {f : MassFields} {x : Point} (hp : (logMetric f x).PosDef)
    (hs : (f.sigma x).PosDef) : logQError f x 1 0=logQError f x 0 1 := by
  have hγ := (CKSAngularGeometry.metricBlock_leaf_posDef hp).isHermitian.eq
  have hσ := hs.isHermitian.eq
  have hγ' : logGamma f x 1 0=logGamma f x 0 1 := by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hγ 0) 1
  have hσ' : f.sigma x 1 0=f.sigma x 0 1 := by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hσ 0) 1
  rw [logQError_scaled]
  change (1/Real.exp (x 0)^2)*logGamma f x 1 0-f.sigma x 1 0 =
    (1/Real.exp (x 0)^2)*logGamma f x 0 1-f.sigma x 0 1
  rw [hγ',hσ']

theorem cks_coordinate_collar_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B A P : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (f : TensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ Real.exp ρ → f.RegularAt (slice ρ x) →
      ContDiffAt ℝ 3 f.base.mK (slice ρ x) → ContDiffAt ℝ 3 f.base.ek (slice ρ x) →
      (∀ᶠ y in 𝓝 (slice ρ x), (logMetric f.base y).PosDef) →
      matrixThreeJets f.base.sigma (slice ρ x) ∈ K → f.LogComponentBound B (slice ρ x) →
      ∀ b : Fin 5 → ℝ, ‖b‖ ≤ P → b 0=1/Real.exp ρ → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSAngularGeometry.oldParams b) ((sourceCollarData f).angular ρ) x) (Real.exp ρ) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput b ((sourceCollarData f).angular ρ) x) (Real.exp ρ) := by
  have hd (q) (hq : q ∈ K) : determinant (fun i k => (q i k).1.1) ≠ 0 := by
    exact (CKSAngularGeometry.determinant_eq (fun i k => (q i k).1.1)).symm ▸ (hreg q hq).det_pos.ne'
  obtain ⟨R,hR,C,hC,hcoeff⟩ := cks_sourceCollarData_bounded hK hd hB
  let L := restrictMatrixThree '' K
  have hL : IsCompact L := hK.image restrictMatrixThree_continuous
  have hpos : ∀ q ∈ L, CKSAngularGeometry.positiveAngular (fun i k => (q i k).1) := by
    rintro _ ⟨q,hq,rfl⟩
    refine ⟨(hreg q hq).diag_pos,?_⟩
    change 0 < determinant (fun i k => (q i k).1.1)
    exact (CKSAngularGeometry.determinant_eq (fun i k => (q i k).1.1)).symm ▸ (hreg q hq).det_pos
  let T := max P (2*C)
  have hT : 0 ≤ T := hP.trans (le_max_left _ _)
  obtain ⟨S,hS,hDEC⟩ := CKSAngularGeometry.bounded_thin_coordinate_DEC hL hpos hT hA
  refine ⟨max R S,hR.trans (le_max_left _ _),?_⟩
  intro f ρ x hr hf hmk hek hp hs hb b hbp hz hw hparams hold
  have hrR : R ≤ Real.exp ρ := (le_max_left _ _).trans hr
  have hrS : S ≤ Real.exp ρ := (le_max_right _ _).trans hr
  have hsig : (f.base.sigma (slice ρ x)).PosDef := hreg _ hs
  have hsd : determinant (f.base.sigma (slice ρ x)) ≠ 0 := hd _ hs
  have hsource := sourceCollarData_regular hf hp hsd
  have hfield := angular_regular hsource (logTError_three_diff hf.base hmk hek hp.self_of_nhds)
  have hbound := hcoeff f (slice ρ x) (by simpa only [slice_zero] using hrR) hf hp hs hb
  have hthin := angular_thin_bounded hC (hR.trans hrR) hsource hbound
  have hmem : CKSAngularGeometry.matrixScalarJets (((sourceCollarData f).angular ρ).metric 0) x ∈ L := by
    change CKSAngularGeometry.matrixScalarJets (fun y => f.base.sigma (slice ρ y)) x ∈ L
    rw [sigma_slice_jets hf.base.sigma]
    exact ⟨_,hs,rfl⟩
  apply hDEC b _ x hfield hmem (hbp.trans (le_max_left _ _))
    (hthin.mono (le_max_right _ _)) (Real.exp ρ) hrS hz hw hparams
  · change f.base.sigma (slice ρ x) 1 0=f.base.sigma (slice ρ x) 0 1
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hsig.isHermitian.eq 0) 1
  · change Real.exp ρ^3*logQError f.base (slice ρ x) 1 0=Real.exp ρ^3*logQError f.base (slice ρ x) 0 1
    rw [logQError_symmetric hp.self_of_nhds hsig]
  · exact hold

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma positive_uIcc {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : uIcc a r ⊆ Ioi 0 := by
  intro s hs
  exact lt_of_lt_of_le (lt_min ha hr) hs.1

lemma positive_interval_integrable {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IntervalIntegrable q volume a r :=
  (hq.mono (positive_uIcc ha hr)).intervalIntegrable

lemma paddingDensity_smooth : ContDiffOn ℝ ∞ paddingDensity (Ioi 0) := by
  exact contDiffOn_const.div (contDiffOn_id.mul (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)))
    (fun r hr => mul_ne_zero (ne_of_gt hr) (Real.sqrt_ne_zero'.mpr hr))
lemma paddingDensity_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ paddingDensity r := by
  unfold paddingDensity
  positivity

lemma padding_antideriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => -2 / Real.sqrt s) (paddingDensity r) r := by
  have hs := Real.hasDerivAt_sqrt hr.ne'
  have hh := (hasDerivAt_const r (-2:ℝ)).div hs (Real.sqrt_ne_zero'.mpr hr)
  convert! hh using 1
  unfold paddingDensity
  have he := Real.sq_sqrt hr.le
  field_simp
  nlinarith [Real.sqrt_pos.mpr hr]

lemma paddingDensity_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    primitive a paddingDensity r = 2/Real.sqrt a - 2/Real.sqrt r := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => padding_antideriv (positive_uIcc ha hr hs))
    (positive_interval_integrable paddingDensity_smooth.continuousOn ha hr)
  unfold primitive
  rw [hh]
  ring

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma paddingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (paddingWeight R) := by
  unfold paddingWeight
  fun_prop
lemma paddingWeight_nonneg (R r : ℝ) : 0 ≤ paddingWeight R r := Real.smoothTransition.nonneg _
lemma paddingWeight_le_one (R r : ℝ) : paddingWeight R r ≤ 1 := Real.smoothTransition.le_one _
lemma paddingWeight_monotone {R : ℝ} (hR : 0 < R) : Monotone (paddingWeight R) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (sub_le_sub_right ((div_le_div_iff_of_pos_right hR).mpr hxy) _)
lemma paddingWeight_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : paddingWeight R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : r/R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa using hr)
  linarith
lemma paddingWeight_one {R r : ℝ} (hR : 0 < R) (hr : 2*R ≤ r) : paddingWeight R r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : 2 ≤ r/R := (le_div_iff₀ hR).mpr hr
  linarith
lemma paddingIntegrand_smooth (R : ℝ) :
    ContDiffOn ℝ ∞ (fun r => paddingWeight R r * paddingDensity r) (Ioi 0) :=
  (paddingWeight_smooth R).contDiffOn.mul paddingDensity_smooth

lemma paddingMass_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : paddingMass R r = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [] with s hs
  rw [uIoc_of_ge hr] at hs
  simp only [paddingWeight_zero hR hs.2,zero_mul]
lemma paddingMass_nonneg {R r : ℝ} (hR : 0 < R) (_hr : 0 < r) : 0 ≤ paddingMass R r := by
  by_cases h : r ≤ R
  · rw [paddingMass_initial hR h]
  · apply intervalIntegral.integral_nonneg (le_of_not_ge h)
    intro s hs
    exact mul_nonneg (paddingWeight_nonneg _ _) (paddingDensity_nonneg (hR.trans_le hs.1))

lemma paddingMass_weighted_bound {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    paddingMass R r ≤ paddingWeight R r * (2/Real.sqrt R) := by
  have hrp : 0 < r := hR.trans_le hr
  have hint := positive_interval_integrable (paddingIntegrand_smooth R).continuousOn hR hrp
  have hdint := positive_interval_integrable paddingDensity_smooth.continuousOn hR hrp
  have hh := intervalIntegral.integral_mono_on hr hint (hdint.const_mul (paddingWeight R r))
    (fun s hs => mul_le_mul_of_nonneg_right (paddingWeight_monotone hR hs.2)
      (paddingDensity_nonneg (hR.trans_le hs.1)))
  change paddingMass R r ≤ _ at hh
  rw [intervalIntegral.integral_const_mul] at hh
  change paddingMass R r ≤ paddingWeight R r * primitive R paddingDensity r at hh
  rw [paddingDensity_integral hR hrp] at hh
  have hw := paddingWeight_nonneg R r
  have hd : 0 ≤ 2/Real.sqrt r := by positivity
  nlinarith

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma roundingWeight_nonneg (R r : ℝ) : 0 ≤ roundingWeight R r := Real.smoothTransition.nonneg _

lemma roundingWeight_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ 2*R) : roundingWeight R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := (div_le_iff₀ hR).mpr hr
  linarith

lemma roundingWeight_le_paddingWeight (R r : ℝ) : roundingWeight R r ≤ paddingWeight R r := by
  apply Real.smoothTransition.monotone
  linarith
lemma roundingWeight_deriv_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ 2*R) :
    deriv (roundingWeight R) r = 0 := by
  have hm : IsLocalMin (roundingWeight R) r := by
    apply Filter.Eventually.of_forall
    intro y
    rw [roundingWeight_zero hR hr]
    exact roundingWeight_nonneg R y
  exact hm.deriv_eq_zero
lemma roundingWeight_deriv (R r : ℝ) :
    deriv (roundingWeight R) r = deriv Real.smoothTransition (r/R-2)/R := by
  have hi : HasDerivAt (fun t : ℝ => t/R-2) (1/R) r := by
    simpa using ((hasDerivAt_id r).div_const R).sub_const 2
  have ho := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp) (r/R-2)
  have hh : HasDerivAt (roundingWeight R) (deriv Real.smoothTransition (r/R-2)/R) r := by
    convert! ho.hasDerivAt.comp r hi using 1
    ring
  exact hh.deriv

theorem roundingWeight_weighted_deriv :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R r : ℝ, 0 < R → R ≤ r → r ≤ 3*R →
      |r*deriv (roundingWeight R) r| ≤ B*paddingWeight R r := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv (by simp)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Icc (0:ℝ) 1)
  refine ⟨3*max C 0,by positivity,?_⟩
  intro R r hR hRr hr
  by_cases hlow : r ≤ 2*R
  · rw [roundingWeight_deriv_initial hR hlow,mul_zero,abs_zero]
    exact mul_nonneg (by positivity) (paddingWeight_nonneg R r)
  have hw : paddingWeight R r = 1 := paddingWeight_one hR (lt_of_not_ge hlow).le
  rw [hw,mul_one,roundingWeight_deriv]
  have h0 : 0 ≤ r/R-2 := by
    have hh : 2 ≤ r/R := (le_div_iff₀ hR).mpr (lt_of_not_ge hlow).le
    linarith
  have h1 : r/R-2 ≤ 1 := by
    have hh : r/R ≤ 3 := (div_le_iff₀ hR).mpr hr
    linarith
  have hd0 : |deriv Real.smoothTransition (r/R-2)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (r/R-2) ⟨h0,h1⟩
  have hd : |deriv Real.smoothTransition (r/R-2)| ≤ max C 0 := hd0.trans (le_max_left _ _)
  have hrr : 0 ≤ r/R := div_nonneg (hR.le.trans hRr) hR.le
  have hrr3 : r/R ≤ 3 := (div_le_iff₀ hR).mpr hr
  calc
    |r*(deriv Real.smoothTransition (r/R-2)/R)| = |r/R| *|deriv Real.smoothTransition (r/R-2)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ 3*max C 0 := by
      rw [abs_of_nonneg hrr]
      exact mul_le_mul hrr3 hd (abs_nonneg _) (by norm_num)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma collarParams_weighted : ∃ A : ℝ, 1 ≤ A ∧ ∀ R r : ℝ, 1 ≤ R → R ≤ r → r ≤ 3*R →
    (∀ i, i ≠ 0 → |collarParams R r i| ≤ A*paddingWeight R r) ∧
    ‖collarParams R r‖ ≤ A := by
  obtain ⟨B,hB,hderiv⟩ := roundingWeight_weighted_deriv
  let A := B+3
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hA2 : 2 ≤ A := by dsimp [A]; linarith
  refine ⟨A,hA1,?_⟩
  intro R r hR hr htop
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hrp : 0 < r := hRp.trans_le hr
  have hw := paddingWeight_nonneg R r
  have hw1 := paddingWeight_le_one R r
  have hparam (i : Fin 5) (hi : i ≠ 0) : |collarParams R r i| ≤ A*paddingWeight R r := by
    fin_cases i
    · exact (hi rfl).elim
    · change |roundingWeight R r| ≤ _
      rw [abs_of_nonneg (roundingWeight_nonneg _ _)]
      exact (roundingWeight_le_paddingWeight _ _).trans (by nlinarith)
    · change |r*deriv (roundingWeight R) r| ≤ _
      exact (hderiv R r hRp hr htop).trans (by dsimp [A]; nlinarith)
    · change |paddingMass R r| ≤ _
      rw [abs_of_nonneg (paddingMass_nonneg hRp hrp)]
      have hs : 1 ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt hR
      have hspos : 0 < Real.sqrt R := by positivity
      have hinv : 2/Real.sqrt R ≤ 2 := (div_le_iff₀ hspos).mpr (by nlinarith)
      exact (paddingMass_weighted_bound hRp hr).trans (by nlinarith)
    · change |paddingWeight R r| ≤ _
      rw [abs_of_nonneg hw]
      nlinarith
  refine ⟨hparam,(pi_norm_le_iff_of_nonneg (zero_le_one.trans hA1)).mpr ?_⟩
  intro i
  rw [Real.norm_eq_abs]
  by_cases hi : i=0
  · subst i
    change |1/r| ≤ A
    rw [abs_of_pos (by positivity : 0 < 1/r)]
    exact (one_div_le_one_div_of_le zero_lt_one (hR.trans hr)).trans (by simpa using hA1)
  · exact (hparam i hi).trans (by nlinarith)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem cks_actual_collar_coordinate_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : TensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R → f.RegularAt (slice ρ x) →
      ContDiffAt ℝ 3 f.base.mK (slice ρ x) → ContDiffAt ℝ 3 f.base.ek (slice ρ x) →
      (∀ᶠ y in 𝓝 (slice ρ x), (logMetric f.base y).PosDef) →
      matrixThreeJets f.base.sigma (slice ρ x) ∈ K → f.LogComponentBound B (slice ρ x) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSAngularGeometry.oldParams (CKSBending.collarParams R (Real.exp ρ)))
          ((sourceCollarData f).angular ρ) x) (Real.exp ρ) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSBending.collarParams R (Real.exp ρ))
          ((sourceCollarData f).angular ρ) x) (Real.exp ρ) := by
  obtain ⟨A,hA,hparams⟩ := CKSBending.collarParams_weighted
  obtain ⟨R₀,hR₀,hh⟩ := cks_coordinate_collar_DEC hK hreg hB
    (zero_le_one.trans hA) (zero_le_one.trans hA)
  refine ⟨R₀,hR₀,?_⟩
  intro R f ρ x hR hr htop hf hmk hek hp hs hb hold
  obtain ⟨hweight,hnorm⟩ := hparams R (Real.exp ρ) (hR₀.trans hR) hr htop
  apply hh f ρ x (hR.trans hr) hf hmk hek hp hs hb _ hnorm rfl
    (CKSBending.paddingWeight_nonneg R (Real.exp ρ)) hweight hold

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
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma source_tensor_log_bounds {f : SourceTensorFields} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hf : f.RegularAt (logRadiusChart x))
    (hσ : ‖matrixThreeJets (angularLift f.base.sigma) x‖ ≤ B)
    (hmg : ‖matrixThreeJets (angularLift f.base.mg) x‖ ≤ B)
    (hmk : ‖matrixScalarJets (angularLift f.base.mK) x‖ ≤ B)
    (hmr : ‖actualScalarJet (angularLift f.base.mr) x‖ ≤ B)
    (hb : f.ComponentBounds B (logRadiusChart x)) : f.logFields.LogComponentBound B x := by
  obtain ⟨heg,hek,hb',herr⟩ := source_log_remainder_bounds hB hf.base hb.base
  refine ⟨hσ,hmg,heg,hmk,hek,hb',hmr,herr,
    source_two_jet_bound hB hf.kr hb.kr,?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  exact source_two_jet_bound hB (contDiffAt_pi.mp hf.kb a) (hb.kb a)

lemma source_tensor_log_positive {f : SourceTensorFields} {x : Point}
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f.base y).PosDef) :
    ∀ᶠ y in 𝓝 x, (logMetric f.logFields.base y).PosDef := by
  have hc := logRadiusChart_smooth.continuous.continuousAt (x := x)
  filter_upwards [hc.tendsto.eventually hp] with y hpy
  rwa [sourceMetric_pullback] at hpy

theorem source_actual_collar_coordinate_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.RegularAt (logRadiusChart (slice ρ x)) →
      ContDiffAt ℝ 3 f.base.mK (angularProjection (logRadiusChart (slice ρ x))) →
      ContDiffAt ℝ 3 f.base.ek (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput
          (CKSAngularGeometry.oldParams (CKSBending.collarParams R (Real.exp ρ)))
          ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSBending.collarParams R (Real.exp ρ))
          ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) := by
  obtain ⟨R₀,hR₀,hh⟩ := cks_actual_collar_coordinate_DEC hK hreg hB
  refine ⟨R₀,hR₀,?_⟩
  intro R f ρ x hR hr htop hf hmk hek hp hσ hs hmg hmK hmr hb hold
  have hmk' := hmk
  rw [angularProjection_logRadiusChart] at hmk'
  have hcl := (logRadiusChart_smooth.contDiffAt (x := slice ρ x)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  exact hh R f.logFields ρ x hR hr htop (source_tensor_log_regular hf)
    (angularLift_diff hmk') (hek.comp _ hcl) (source_tensor_log_positive hp) hσ
    (source_tensor_log_bounds hB hf hs hmg hmK hmr hb) hold

end
end CKSMixedGeometry

end

end OAI
end

theorem solution : type_of% @OAI.CKSMixedGeometry.source_actual_collar_coordinate_DEC := @OAI.CKSMixedGeometry.source_actual_collar_coordinate_DEC

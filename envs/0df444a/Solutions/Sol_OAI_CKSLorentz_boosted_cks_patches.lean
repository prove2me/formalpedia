-- Prove2me | solution 1 for OAI.CKSLorentz.boosted_cks_patches
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:45:43.717309+00:00
-- url     : https://prove2.me/submissions/1c6193de-c87c-4e20-99c0-c375f7e875c9

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

lemma D_comp_real (e : E) {f : ℝ → ℝ} {g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f (g y)) x = deriv f (g x) * D e g x := by
  unfold D
  change fderiv ℝ (f ∘ g) x e = _
  rw [(hf.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt).fderiv]
  simp

end
end CKSCalculus

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

end
end CKSAngularSlice

end

end OAI
end

section
namespace OAI



noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

def boundaryAmbient (e m : ℝ) (p : E) (n : E) : E :=
  (denominator e m p n)⁻¹ • boundarySpatial e m p n

lemma boundaryAmbient_smooth {e m : ℝ} {p : E} {n : E}
    (hd : denominator e m p n ≠ 0) : ContDiffAt ℝ ∞ (boundaryAmbient e m p) n := by
  have hi : ContDiff ℝ ∞ (fun n : E => inner ℝ p n) :=
    ContDiff.inner ℝ contDiff_const contDiff_id
  have hD : ContDiff ℝ ∞ (denominator e m p) :=
    (contDiff_const.add hi).div_const m
  have hS : ContDiff ℝ ∞ (boundarySpatial e m p) :=
    contDiff_id.add ((contDiff_const.add (hi.div_const (m*(e+m)))).smul contDiff_const)
  exact (hD.contDiffAt.inv hd).smul hS.contDiffAt

lemma boundary_smooth (e : ℝ) (p : E) (he : ‖p‖ < e) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (boundary e p he) := by
  have h : ContMDiff (𝓡 2) 𝓘(ℝ,E) ∞
      (fun n : Sphere => boundaryAmbient e (mass e p) p n) := by
    intro n
    exact (boundaryAmbient_smooth (denominator_pos he (mass_pos he) n).ne').comp_contMDiffAt
      (contMDiff_coe_sphere (E := E) (n := 2)).contMDiffAt
  exact h.codRestrict_sphere fun n => (boundary e p he n).property

end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff

lemma denominator_derivative (e m : ℝ) (p n : E) :
    HasFDerivAt (denominator e m p) (timeDifferential m p) n := by
  convert! ((innerSL ℝ p).hasFDerivAt.const_add e).mul_const m⁻¹ using 1

lemma boundarySpatial_derivative (e m : ℝ) (p n : E) :
    HasFDerivAt (boundarySpatial e m p) (spaceDifferential e m p) n := by
  convert! (hasFDerivAt_id n).add
    ((((innerSL ℝ p).hasFDerivAt.mul_const (m*(e+m))⁻¹).const_add (1/m)).smul_const p) using 1

lemma boundaryAmbient_fderiv {e m : ℝ} {p n : E} (hd : denominator e m p n ≠ 0) (Y : E) :
    fderiv ℝ (boundaryAmbient e m p) n Y =
      (denominator e m p n)⁻¹ • spaceDifferential e m p Y -
        (timeDifferential m p Y / (denominator e m p n)^2) • boundarySpatial e m p n := by
  have hi := (hasDerivAt_inv hd).comp_hasFDerivAt n (denominator_derivative e m p n)
  have h := hi.smul (boundarySpatial_derivative e m p n)
  change HasFDerivAt (boundaryAmbient e m p) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  change _ = _
  simp only [smul_eq_mul, Function.comp_apply]
  module

lemma minkowski_null_tangent {e m : ℝ} {p n : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (Y : E) :
    -(denominator e m p n) * timeDifferential m p Y +
      inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Y) = inner ℝ n Y := by
  convert boost_minkowski hm0 hd hm ((1:ℝ),n) ((0:ℝ),Y) using 1 <;>
    simp [minkowski, boost, denominator, boundarySpatial]

lemma minkowski_tangent_tangent {e m : ℝ} {p : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (Y Z : E) :
    -timeDifferential m p Y * timeDifferential m p Z +
      inner ℝ (spaceDifferential e m p Y) (spaceDifferential e m p Z) = inner ℝ Y Z := by
  convert boost_minkowski hm0 hd hm ((0:ℝ),Y) ((0:ℝ),Z) using 1 <;>
    simp [minkowski, boost]

theorem boundary_conformal {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (n : Sphere) (Y Z : E)
    (hY : inner ℝ (n:E) Y = 0) (hZ : inner ℝ (n:E) Z = 0) :
    inner ℝ (fderiv ℝ (boundaryAmbient e m p) n Y)
      (fderiv ℝ (boundaryAmbient e m p) n Z) =
        (denominator e m p n)⁻¹ ^2 * inner ℝ Y Z := by
  have hD := (denominator_pos he hm0 n).ne'
  have hd := (add_pos (energy_pos he) hm0).ne'
  have hy := minkowski_null_tangent hm0.ne' hd hm Y (n := (n:E))
  have hz := minkowski_null_tangent hm0.ne' hd hm Z (n := (n:E))
  have hyz := minkowski_tangent_tangent hm0.ne' hd hm Y Z
  rw [hY] at hy
  rw [hZ] at hz
  have hself : inner ℝ (boundarySpatial e m p n) (boundarySpatial e m p n) =
      (denominator e m p n)^2 := by
    rw [real_inner_self_eq_norm_sq, boundarySpatial_norm he hm0 hm]
  rw [boundaryAmbient_fderiv hD, boundaryAmbient_fderiv hD]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_trivial, hself]
  rw [real_inner_comm (boundarySpatial e m p n) (spaceDifferential e m p Y)]
  have hy' : inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Y) =
      denominator e m p n * timeDifferential m p Y := by linarith
  have hz' : inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Z) =
      denominator e m p n * timeDifferential m p Z := by linarith
  have hyz' : inner ℝ (spaceDifferential e m p Y) (spaceDifferential e m p Z) =
      inner ℝ Y Z + timeDifferential m p Y * timeDifferential m p Z := by linarith
  rw [hy', hz', hyz']
  field_simp [hD]
  ring

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

lemma compactRoot_pos (s : ℝ) : 0 < compactRoot s := Real.sqrt_pos.2 (by positivity)

lemma compactRoot_sq (s : ℝ) : compactRoot s ^2 = 1+s^2 := Real.sq_sqrt (by positivity)

lemma compactRoot_smooth : ContDiff ℝ ∞ compactRoot :=
  (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun s => by positivity)

lemma compactSpatial_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (compactSpatial e m p) := by
  have hi := ContDiff.inner ℝ (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => p)) contDiff_snd
  exact contDiff_snd.add ((((compactRoot_smooth.comp contDiff_fst).div_const m).add
    (hi.div_const (m*(e+m)))).smul contDiff_const)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

def compactRegion (e m : ℝ) (p : E) : Set (ℝ × E) :=
  {z | 0 < denominator e m p z.2 ∧ 0 < compactScale e m p z}

lemma denominator_joint_smooth (e m : ℝ) (p : E) :
    ContDiff ℝ ∞ (fun z : ℝ × E => denominator e m p z.2) :=
  (contDiff_const.add (ContDiff.inner ℝ contDiff_const contDiff_snd)).div_const m

lemma compactRegion_open (e m : ℝ) (p : E) : IsOpen (compactRegion e m p) :=
  (isOpen_lt continuous_const (denominator_joint_smooth e m p).continuous).inter
    (isOpen_lt continuous_const (compactSpatial_smooth e m p).continuous.norm)

lemma compactScale_smooth_region (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : ContDiffAt ℝ ∞ (compactScale e m p) z :=
  (compactSpatial_smooth e m p).contDiffAt.norm ℝ (norm_ne_zero_iff.mp hz.2.ne')

lemma hyperTime_polar {ρ : ℝ} (hρ : 0 < ρ) (n : Sphere) :
    hyperTime (ρ • (n:E)) = ρ * compactRoot ρ⁻¹ := by
  have hsq : (ρ*compactRoot ρ⁻¹)^2 = 1+‖ρ • (n:E)‖^2 := by
    rw [mul_pow, compactRoot_sq, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, sphere_norm, mul_one]
    field_simp
    ring
  have hp : 0 < ρ * compactRoot ρ⁻¹ := mul_pos hρ (compactRoot_pos _)
  nlinarith [hyperTime_sq (ρ • (n:E)), hyperTime_pos (ρ • (n:E))]

lemma hyperbolicMap_polar {ρ : ℝ} (hρ : 0 < ρ) (e m : ℝ) (p : E) (n : Sphere) :
    hyperbolicMap e m p (ρ • (n:E)) = ρ • compactSpatial e m p (ρ⁻¹,(n:E)) := by
  unfold hyperbolicMap boost hyperboloid
  rw [hyperTime_polar hρ]
  simp only [compactSpatial, inner_smul_right]
  module

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma sum_coordinate_basis (v : Point) : ∑ k : I, v k • basis k = v := by
  ext k
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma multilinear_norm_of_components {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Point) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : Fin n → I, ‖M (fun i => basis (a i))‖ ≤ C) :
    ‖M‖ ≤ 3^n * C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he : M v = ∑ a : Fin n → I, (∏ i, v i (a i)) * M (fun i => basis (a i)) := by
    calc M v = M (fun i => ∑ k : I, v i k • basis k) := by
          congr 1; funext i; exact (sum_coordinate_basis _).symm
         _ = ∑ a : Fin n → I, M (fun i => v i (a i) • basis (a i)) := M.map_sum _
         _ = _ := by simp only [M.map_smul_univ, smul_eq_mul]
  rw [he]
  calc ‖∑ a : Fin n → I, (∏ i, v i (a i)) * M (fun i => basis (a i))‖
      ≤ ∑ a : Fin n → I, ‖(∏ i, v i (a i)) * M (fun i => basis (a i))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin n → I, (∏ i, ‖v i‖) * C := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, norm_prod]
      apply mul_le_mul
      · apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
        intro i _
        exact norm_le_pi_norm (v i) (a i)
      · exact hb a
      · exact norm_nonneg _
      · positivity
    _ = 3^n * C * ∏ i, ‖v i‖ := by simp [mul_comm, mul_left_comm, mul_assoc]

lemma iteratedFDeriv_basis_ofFn (n : ℕ) (a : Fin n → I)
    {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ n f x) :
    iteratedFDeriv ℝ n f x (fun i => basis (a i)) = coordinateIter (List.ofFn a) f x := by
  induction n generalizing x with
  | zero => simp [coordinateIter]
  | succ n ih =>
    have hd := hf.differentiableAt_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun y => iteratedFDeriv ℝ n f y (Fin.tail (fun i => basis (a i)))) =ᶠ[𝓝 x]
        coordinateIter (List.ofFn (Fin.tail a)) f := by
      have hfn : ContDiffAt ℝ n f x := hf.of_le (by exact_mod_cast Nat.le_succ n)
      filter_upwards [hfn.eventually (by simp)] with y hy
      exact ih (Fin.tail a) hy
    have hlist : List.ofFn a = a 0 :: List.ofFn (Fin.tail a) := by
      conv_lhs => rw [← Fin.cons_self_tail a]
      exact List.ofFn_cons _ _
    rw [hlist]
    change D (basis (a 0)) (fun y => iteratedFDeriv ℝ n f y (Fin.tail (fun i => basis (a i)))) x = _
    exact D_congr he _

lemma coordinateIter_le_iteratedFDeriv (l : List I)
    {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ l.length f x) :
    |coordinateIter l f x| ≤ ‖iteratedFDeriv ℝ l.length f x‖ := by
  have he := iteratedFDeriv_basis_ofFn l.length l.get hf
  rw [List.ofFn_get] at he
  rw [← he, ← Real.norm_eq_abs]
  have h := (iteratedFDeriv ℝ l.length f x).le_opNorm (fun i => basis (l.get i))
  have hn (i : Fin l.length) : ‖basis (l.get i)‖ = 1 := by simp [basis, Pi.norm_single]
  simpa only [hn, Finset.prod_const_one, mul_one] using h

lemma source_scaledComponent_norm_derivative
    (j q n : ℕ) {B : ℝ} (hB : 0 ≤ B) (hn : n ≤ j)
    {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ j f (logRadiusChart x))
    (hb : ScaledComponentBound f j q B (logRadiusChart x)) :
    ‖iteratedFDeriv ℝ n (fun y => f (logRadiusChart y)) x‖ ≤
      3^n * (B / (Real.exp (x 0))^q) := by
  apply multilinear_norm_of_components _ (by positivity)
  intro a
  have hfn : ContDiffAt ℝ n f (logRadiusChart x) := hf.of_le (by exact_mod_cast hn)
  have hcomp := hfn.comp x (logRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  change ‖iteratedFDeriv ℝ n (f ∘ logRadiusChart) x (fun i => basis (a i))‖ ≤ _
  rw [iteratedFDeriv_basis_ofFn n a hcomp, Real.norm_eq_abs]
  simp only [Function.comp_def]
  rw [coordinateIter_pullback (f := f) (x := x) (List.ofFn a) (by simpa only [List.length_ofFn] using hfn)]
  have h := hb (List.ofFn a) (by simpa using hn)
  simpa only [logRadiusChart, ite_true] using h

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma inverseLogRadiusChart_smooth : ContDiff ℝ ∞ inverseLogRadiusChart := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=0 <;> simp only [inverseLogRadiusChart,hi,ite_true,ite_false] <;> fun_prop

lemma backwardFactor_smooth (a : I) : ContDiff ℝ ∞ (backwardFactor a) := by
  change ContDiff ℝ ∞ (fun y : Point => if a=0 then -y 0 else 1)
  split_ifs <;> fun_prop

def inverseChartDerivative (x : Point) : Point →L[ℝ] Point :=
  letI := pointDimension_neZero
  letI := coordinate_smulCommClass
  letI := coordinate_continuousConstSMul
  ContinuousLinearMap.pi (fun i => if i=0 then (-Real.exp (-x 0)) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma inverseLogRadiusChart_hasFDerivAt (x : Point) :
    HasFDerivAt inverseLogRadiusChart (inverseChartDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    have h := (Real.hasDerivAt_exp (-x 0)).comp_hasFDerivAt x
      ((ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).hasFDerivAt.neg)
    change HasFDerivAt (fun y : Point => Real.exp (-y 0))
      ((-Real.exp (-x 0)) • ContinuousLinearMap.proj 0) x
    convert h using 1 <;> ext y <;> simp
  · simp only [inverseLogRadiusChart,hi,ite_false]
    change HasFDerivAt (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) (ContinuousLinearMap.proj i) x
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt

lemma inverseChartDerivative_basis (a : I) (x : Point) :
    inverseChartDerivative x (basis a) = backwardFactor a (inverseLogRadiusChart x) • basis a := by
  ext i
  by_cases ha : a=0 <;> by_cases hi : i=0
  · subst a; subst i; simp [inverseChartDerivative,backwardFactor,inverseLogRadiusChart,basis]
  · subst a; simp [inverseChartDerivative,backwardFactor,inverseLogRadiusChart,basis,hi]
  · subst i; simp [inverseChartDerivative,backwardFactor,basis,ha,Ne.symm ha]
  · simp [inverseChartDerivative,backwardFactor,basis,ha,hi]

lemma D_inverse_pullback (a : I) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (inverseLogRadiusChart x)) :
    D (basis a) (fun y => f (inverseLogRadiusChart y)) x =
      backwardScaledD a f (inverseLogRadiusChart x) := by
  unfold D
  change (fderiv ℝ (f ∘ inverseLogRadiusChart) x) (basis a) = _
  rw [fderiv_comp x hf (inverseLogRadiusChart_hasFDerivAt x).differentiableAt,
    (inverseLogRadiusChart_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.comp_apply,inverseChartDerivative_basis,map_smul,
    smul_eq_mul,backwardScaledD,D]

lemma backwardScaledIter_contDiffAt (l : List I) (m : ℕ) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ (↑(m+l.length) : ℕ∞ω) f x) :
    ContDiffAt ℝ m (backwardScaledIter l f) x := by
  induction l generalizing m with
  | nil => simpa only [List.length_nil,add_zero,backwardScaledIter_nil] using hf
  | cons a l ih =>
    have heq : m+(a::l).length = (m+1)+l.length := by simp; omega
    rw [heq] at hf
    exact ((backwardFactor_smooth a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt.mul
      (contDiffAt_D (ih (m+1) hf) (m := m) (by simp) (basis a))

lemma coordinateIter_inverse_pullback (l : List I) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ l.length f (inverseLogRadiusChart x)) :
    coordinateIter l (fun y => f (inverseLogRadiusChart y)) x =
      backwardScaledIter l f (inverseLogRadiusChart x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    have heq : coordinateIter l (fun y => f (inverseLogRadiusChart y)) =ᶠ[𝓝 x]
        (fun y => backwardScaledIter l f (inverseLogRadiusChart y)) := by
      have hf' : ContDiffAt ℝ l.length f (inverseLogRadiusChart x) := hf.of_le (by simp)
      have he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ l.length f (inverseLogRadiusChart y) :=
        inverseLogRadiusChart_smooth.continuous.continuousAt.eventually (hf'.eventually (by simp))
      filter_upwards [he] with y hy
      exact ih hy
    change D (basis a) (coordinateIter l (fun y => f (inverseLogRadiusChart y))) x = _
    rw [D_congr heq]
    have hf' : ContDiffAt ℝ (↑(1+l.length) : ℕ∞ω) f (inverseLogRadiusChart x) := by
      simpa only [List.length_cons,Nat.add_comm] using hf
    exact D_inverse_pullback a ((backwardScaledIter_contDiffAt l 1 hf').differentiableAt (by norm_num))

theorem compactified_scalar_uniform_jets (n : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → ℝ} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ ≤ C := by
  let Q : Point → (Fin n → I) → ℝ := fun z a => backwardScaledIter (List.ofFn a) f z
  have hQ : ContinuousOn Q K := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro a
    exact (backwardScaledIter_contDiffAt (List.ofFn a) 0
      ((hf z hz).of_le (by exact_mod_cast le_top))).continuousAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hQ
  refine ⟨3^n * max 0 C,by positivity,?_⟩
  intro x hx
  apply multilinear_norm_of_components _ (le_max_left _ _)
  intro a
  have hfn : ContDiffAt ℝ n f (inverseLogRadiusChart x) :=
    (hf _ hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    hfn.comp x (inverseLogRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  rw [iteratedFDeriv_basis_ofFn n a hcomp]
  rw [coordinateIter_inverse_pullback (f := f) (x := x) (List.ofFn a) (by simpa using hfn)]
  exact (norm_le_pi_norm (Q (inverseLogRadiusChart x)) a).trans ((hC _ hx).trans (le_max_right _ _))

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

theorem compactified_vector_uniform_jets (n : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → Point} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ ≤ C := by
  classical
  have hc (k : I) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y) k) x‖ ≤ C :=
    compactified_scalar_uniform_jets n hK (f := fun z => f z k)
      (fun z hz => (contDiffAt_pi.mp (hf z hz)) k)
  choose C hC hbound using hc
  refine ⟨∑ k, C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro x hx
  have hcomp : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    ((hf _ hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).comp x
      (inverseLogRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun k _ => hC k))
  intro v
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (Finset.sum_nonneg (fun k _ => hC k)) (Finset.prod_nonneg (fun i _ => norm_nonneg (v i))))).mpr
  intro k
  have he := (ContinuousLinearMap.proj k : Point →L[ℝ] ℝ).iteratedFDeriv_comp_left hcomp (i := n) le_rfl
  have hv : (iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x v) k =
      iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y) k) x v := by
    exact (congrArg (fun M => M v) he).symm
  rw [hv]
  exact ((iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y) k) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((hbound k x hx).trans
      (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ k))) (by positivity))

lemma linear_positive_jet_bound (L : Point →L[ℝ] Point) (n : ℕ) (hn : 1 ≤ n) (x : Point) :
    ‖iteratedFDeriv ℝ n L x‖ ≤ ‖L‖ := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      rw [← norm_iteratedFDeriv_fderiv]
      have he : fderiv ℝ L = fun _ => L := funext (fun y => L.fderiv)
      rw [he,iteratedFDeriv_succ_const]
      simp

theorem logAffineCompactMap_uniform_jets (j : ℕ) (L : Point →L[ℝ] Point)
    {K : Set Point} (hK : IsCompact K) {f : Point → Point}
    (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ∀ n : ℕ, 1 ≤ n → n ≤ j →
        ‖iteratedFDeriv ℝ n (logAffineCompactMap L f) x‖ ≤ D^n := by
  classical
  choose C hC hbound using (fun n : Fin (j+1) => compactified_vector_uniform_jets n.val hK hf)
  let D : ℝ := 1 + ‖L‖ + ∑ n, C n
  have hs : 0 ≤ ∑ n, C n := Finset.sum_nonneg (fun n _ => hC n)
  have hD : 1 ≤ D := by dsimp [D]; linarith [norm_nonneg L]
  refine ⟨D,hD,?_⟩
  intro x hx n hn hnj
  have hfn : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    ((hf _ hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).comp x
      (inverseLogRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  change ‖iteratedFDeriv ℝ n ((L : Point → Point) + (fun y => f (inverseLogRadiusChart y))) x‖ ≤ _
  rw [iteratedFDeriv_add_apply L.contDiff.contDiffAt hfn]
  have hCn : C ⟨n,by omega⟩ ≤ ∑ i, C i :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _)
  calc ‖iteratedFDeriv ℝ n L x + iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖
      ≤ ‖iteratedFDeriv ℝ n L x‖ + ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ := norm_add_le _ _
    _ ≤ ‖L‖ + C ⟨n,by omega⟩ := add_le_add (linear_positive_jet_bound L n hn x) (hbound ⟨n,by omega⟩ x hx)
    _ ≤ D := by dsimp [D]; linarith
    _ ≤ D^n := by simpa only [pow_one] using pow_le_pow_right₀ hD hn

end
end CKSMixedGeometry

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma compactPolar_contDiffAt {φ : Angle → E} {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z)) : ContDiffAt ℝ ∞ (compactPolar φ) z :=
  (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).contDiff.contDiffAt.prodMk
    (hφ.comp z angularProjection.contDiff.contDiffAt)

lemma compactAngle_contDiffAt (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : ContDiffAt ℝ ∞ (compactAngle e m p) z :=
  ((compactScale_smooth_region e m p hz).inv hz.2.ne').smul
    (compactSpatial_smooth e m p).contDiffAt

lemma compactLorentzCoefficients_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) z := by
  have hp := compactPolar_contDiffAt hφ
  have hA := (compactScale_smooth_region e m p hz).comp z hp
  have ha := (compactAngle_contDiffAt e m p hz).comp z hp
  have hang := hψ.comp z ha
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [compactLorentzCoefficients,slice_zero,Function.comp_def] using hA.log hz.2.ne'
  · simpa only [compactLorentzCoefficients,slice_succ,Function.comp_def] using (contDiffAt_pi.mp hang) a

lemma logLorentzChart_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {x : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x)))) :
    ContDiffAt ℝ ∞ (logLorentzChart e m p φ ψ) x :=
  radialLinear.contDiff.contDiffAt.add
    ((compactLorentzCoefficients_contDiffAt e m p φ ψ hφ hz hψ).comp x
      inverseLogRadiusChart_smooth.contDiffAt)

theorem logLorentzChart_uniform_jets (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ∀ n : ℕ, 1 ≤ n → n ≤ j →
        ‖iteratedFDeriv ℝ n (logLorentzChart e m p φ ψ) x‖ ≤ D^n :=
  logAffineCompactMap_uniform_jets j radialLinear hK
    (fun z hz => compactLorentzCoefficients_contDiffAt e m p φ ψ (hφ z hz) (hreg z hz) (hψ z hz))

lemma logLorentzChart_eq_slice (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) (x : Point) :
    logLorentzChart e m p φ ψ x =
      slice (x 0 + Real.log (compactScale e m p (compactPolar φ (inverseLogRadiusChart x))))
        (ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x)))) := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [logLorentzChart,logAffineCompactMap,radialLinear,basis,compactLorentzCoefficients]
  · simp [logLorentzChart,logAffineCompactMap,radialLinear,basis,compactLorentzCoefficients,
      Fin.succ_ne_zero]

lemma logLorentzChart_radial_exp (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) {x : Point}
    (hA : 0 < compactScale e m p (compactPolar φ (inverseLogRadiusChart x))) :
    Real.exp ((logLorentzChart e m p φ ψ x) 0) =
      Real.exp (x 0) * compactScale e m p (compactPolar φ (inverseLogRadiusChart x)) := by
  rw [logLorentzChart_eq_slice,slice_zero,Real.exp_add,Real.exp_log hA]

lemma logRadiusChart_slice (r : ℝ) (a : Angle) :
    logRadiusChart (slice r a) = slice (Real.exp r) a := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart,Fin.succ_ne_zero]

theorem lorentzPolarChart_logRadiusChart (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {x : Point}
    (hn : φ (angularProjection x) ∈ Metric.sphere (0 : E) 1)
    (hA : 0 < compactScale e m p (compactPolar φ (inverseLogRadiusChart x))) :
    lorentzPolarChart e m p φ ψ (logRadiusChart x) =
      logRadiusChart (logLorentzChart e m p φ ψ x) := by
  let ρ := Real.exp (x 0)
  let n : Sphere := ⟨φ (angularProjection x),hn⟩
  have hρ : 0 < ρ := Real.exp_pos _
  have he : compactPolar φ (inverseLogRadiusChart x) = (ρ⁻¹,(n:E)) := by
    simp [compactPolar,inverseLogRadiusChart,ρ,n,Real.exp_neg]
  have hv : hyperbolicMap e m p ((logRadiusChart x) 0 • φ (angularProjection (logRadiusChart x))) =
      ρ • compactSpatial e m p (compactPolar φ (inverseLogRadiusChart x)) := by
    simpa only [logRadiusChart,ite_true,angularProjection_logRadiusChart,he] using
      hyperbolicMap_polar hρ e m p n
  unfold lorentzPolarChart
  rw [hv,logLorentzChart_eq_slice,logRadiusChart_slice,Real.exp_add,Real.exp_log hA]
  dsimp only
  congr 1
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    rfl
  · congr 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ,smul_smul,mul_inv_rev]
    simp only [mul_assoc,inv_mul_cancel₀ hρ.ne',mul_one]
    rfl

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma local_norm_iteratedFDeriv_comp {f : Point → Point} {g : Point → ℝ}
    {n : ℕ} {x : Point} (hg : ContDiffAt ℝ n g (f x)) (hf : ContDiffAt ℝ n f x)
    {C D : ℝ}
    (hC : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (n.factorial : ℝ) * C * D^n := by
  obtain ⟨t,htsub,htopen,hft⟩ := mem_nhds_iff.mp (hg.eventually (by simp))
  have ht : t ∈ 𝓝 (f x) := htopen.mem_nhds hft
  have he := (hf.eventually (by simp)).and (hf.continuousAt.preimage_mem_nhds ht)
  obtain ⟨s,hsub,hsopen,hxs⟩ := mem_nhds_iff.mp he
  have hgs : ContDiffOn ℝ n g t := fun y hy => (show ContDiffAt ℝ n g y from htsub hy).contDiffWithinAt
  have hfs : ContDiffOn ℝ n f s := fun y hy => (hsub hy).1.contDiffWithinAt
  have hst : MapsTo f s t := fun y hy => (hsub hy).2
  have hCv (i : ℕ) (hi : i ≤ n) : ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv htopen.uniqueDiffOn
      (hg.of_le (by exact_mod_cast hi)) hft]
    exact hC i hi
  have hDv (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D^i := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn
      (hf.of_le (by exact_mod_cast hi)) hxs]
    exact hD i hi1 hi
  have h := norm_iteratedFDerivWithin_comp_le hgs hfs (by rfl) htopen.uniqueDiffOn
    hsopen.uniqueDiffOn hst hxs hCv hDv
  rwa [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn (hg.comp x hf) hxs] at h

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

theorem source_scaledComponent_pullback
    (j q : ℕ) {B D : ℝ} (hB : 0 ≤ B) (_hD0 : 1 ≤ D)
    {f : Point → ℝ} {F : Point → Point} {x : Point}
    (hf : ContDiffAt ℝ j f (logRadiusChart (F x)))
    (hF : ContDiffAt ℝ j F x)
    (hb : ScaledComponentBound f j q B (logRadiusChart (F x)))
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i F x‖ ≤ D^i) :
    ∀ l : List I, l.length ≤ j →
      |coordinateIter l (fun y => f (logRadiusChart (F y))) x| ≤
        (l.length.factorial : ℝ) * 3^l.length * D^l.length * B /
          (Real.exp ((F x) 0))^q

 := by
  intro l hl
  let g : Point → ℝ := fun y => f (logRadiusChart y)
  have hg : ContDiffAt ℝ j g (F x) := hf.comp (F x)
    (logRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))
  have hgn : ContDiffAt ℝ l.length g (F x) := hg.of_le (by exact_mod_cast hl)
  have hFn : ContDiffAt ℝ l.length F x := hF.of_le (by exact_mod_cast hl)
  have hC (i : ℕ) (hi : i ≤ l.length) :
      ‖iteratedFDeriv ℝ i g (F x)‖ ≤ 3^l.length * (B / (Real.exp ((F x) 0))^q) := by
    exact (source_scaledComponent_norm_derivative j q i hB (hi.trans hl) hf hb).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hi) (by positivity))
  have h := local_norm_iteratedFDeriv_comp hgn hFn hC
    (fun i hi1 hi => hD i hi1 (hi.trans hl))
  have hh := coordinateIter_le_iteratedFDeriv l (hgn.comp x hFn)
  have he : (l.length.factorial : ℝ) *
      (3^l.length * (B / (Real.exp ((F x) 0))^q)) * D^l.length =
      (l.length.factorial : ℝ) * 3^l.length * D^l.length * B /
          (Real.exp ((F x) 0))^q := by ring
  rw [he] at h
  exact hh.trans h

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem lorentz_finite_remainder_pullback (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Point → ℝ) (B : ℝ), 0 ≤ B →
      ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ContDiffAt ℝ j f (logRadiusChart (logLorentzChart e m p φ ψ x)) →
      ScaledComponentBound f j q B (logRadiusChart (logLorentzChart e m p φ ψ x)) →
      ∀ l : List I, l.length ≤ j →
      |coordinateIter l (fun y => f (logRadiusChart (logLorentzChart e m p φ ψ y))) x| ≤
        C * B / (Real.exp (x 0))^q := by
  classical
  let A : Point → ℝ := fun z => compactScale e m p (compactPolar φ z)
  have hA (z : Point) (hz : z ∈ K) : 0 < A z := (hreg z hz).2
  have hAs (z : Point) (hz : z ∈ K) : ContDiffAt ℝ ∞ A z :=
    (compactScale_smooth_region e m p (hreg z hz)).comp z (compactPolar_contDiffAt (hφ z hz))
  have hc : ContinuousOn (fun z => ((A z)^q)⁻¹) K := by
    intro z hz
    exact (((hAs z hz).pow q).inv (pow_ne_zero q (hA z hz).ne')).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨D,hD,hjets⟩ := logLorentzChart_uniform_jets e m p φ ψ j hK hφ hreg hψ
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  let N : ℝ := (j.factorial : ℝ)*3^j*D^j
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨N * max 0 M,mul_nonneg hN0 (le_max_left _ _),?_⟩
  intro f B hB x hx hf hb l hl
  have hFx : ContDiffAt ℝ j (logLorentzChart e m p φ ψ) x :=
    (logLorentzChart_contDiffAt e m p φ ψ (hφ _ hx) (hreg _ hx) (hψ _ hx)).of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hscaled := source_scaledComponent_pullback j q hB hD hf hFx hb (hjets x hx) l hl
  have hfac : (l.length.factorial : ℝ) ≤ (j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hl
  have hN : (l.length.factorial : ℝ)*3^l.length*D^l.length ≤ N :=
    mul_le_mul (mul_le_mul hfac (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hl)
      (by positivity) (by positivity)) (pow_le_pow_right₀ hD hl) (pow_nonneg hD0 _)
      (by positivity)
  have hAi0 : 0 ≤ ((A (inverseLogRadiusChart x))^q)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (hA _ hx).le _)
  have hAi : ((A (inverseLogRadiusChart x))^q)⁻¹ ≤ max 0 M := by
    have h := hM (inverseLogRadiusChart x) hx
    rw [Real.norm_eq_abs,abs_of_nonneg hAi0] at h
    exact h.trans (le_max_right _ _)
  have hcoef := mul_le_mul hN hAi hAi0 hN0
  have heq : (l.length.factorial : ℝ)*3^l.length*D^l.length*B /
        Real.exp ((logLorentzChart e m p φ ψ x) 0)^q =
      ((l.length.factorial : ℝ)*3^l.length*D^l.length) *
        ((A (inverseLogRadiusChart x))^q)⁻¹ * B / Real.exp (x 0)^q := by
    rw [logLorentzChart_radial_exp e m p φ ψ (hA _ hx)]
    dsimp [A]
    simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq] at hscaled
  exact hscaled.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hB) (by positivity))
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def LogJetBound (f : Point → ℝ) (j : ℕ) (q C : ℝ) (x : Point) : Prop :=
  ∀ n : ℕ, n ≤ j → ‖iteratedFDeriv ℝ n f x‖ ≤ C * radiusPower (-q) x

lemma local_norm_iteratedFDeriv_mul {f g : Point → ℝ} {n : ℕ} {x : Point}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨s,hs,hsopen,hxs⟩ := mem_nhds_iff.mp
    ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  have hfs : ContDiffOn ℝ n f s := fun y hy => (hs hy).1.contDiffWithinAt
  have hgs : ContDiffOn ℝ n g s := fun y hy => (hs hy).2.contDiffWithinAt
  have h := norm_iteratedFDerivWithin_mul_le hfs hgs hsopen.uniqueDiffOn hxs (le_refl (n : ℕ∞ω))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn (hf.mul hg) hxs] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn
      (hf.of_le (by exact_mod_cast hi')) hxs,
    iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn
      (hg.of_le (by exact_mod_cast Nat.sub_le n i)) hxs]

lemma LogJetBound.mul {f g : Point → ℝ} {x : Point} {j : ℕ} {q r C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x)
    (hb : LogJetBound f j q C x) (hc : LogJetBound g j r D x) :
    LogJetBound (fun y => f y * g y) j (q+r) (2^j*C*D) x := by
  intro n hn
  have hfn : ContDiffAt ℝ n f x := hf.of_le (by exact_mod_cast hn)
  have hgn : ContDiffAt ℝ n g x := hg.of_le (by exact_mod_cast hn)
  calc
    ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤
        ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ :=
      local_norm_iteratedFDeriv_mul hfn hgn
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
          (C * radiusPower (-q) x)*(D * radiusPower (-r) x) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i (hi'.trans hn)) (by positivity))
        (hc (n-i) ((Nat.sub_le n i).trans hn)) (norm_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg hC (radiusPower_pos _ _).le))
    _ = 2^n*C*D * radiusPower (-(q+r)) x := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) = 2^n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [hsum]
      have he : radiusPower (-(q+r)) x = radiusPower (-q) x * radiusPower (-r) x := by
        simp only [radiusPower,neg_add,add_mul,Real.exp_add]
      rw [he]
      ring
    _ ≤ 2^j*C*D * radiusPower (-(q+r)) x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn) hC) hD)
        (radiusPower_pos _ _).le

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma coordinateIter_radiusPower (t : ℝ) (l : List I) :
    coordinateIter l (radiusPower t) = fun x => radialEigenvalue t l * radiusPower t x := by
  induction l with
  | nil => simp [coordinateIter,radialEigenvalue]
  | cons a l ih =>
    funext x
    simp only [coordinateIter,ih]
    rw [D_const_mul (basis a) _ ((radiusPower_smooth t).contDiffAt.differentiableAt (by simp))]
    simp only [D_radiusPower,radialEigenvalue_cons]
    ring

lemma abs_radialEigenvalue (t : ℝ) (l : List I) :
    |radialEigenvalue t l| ≤ |t|^l.length := by
  induction l with
  | nil => simp [radialEigenvalue]
  | cons a l ih =>
    simp only [radialEigenvalue_cons,abs_mul,List.length_cons,pow_succ]
    calc |t| * |basis a 0| * |radialEigenvalue t l|
        ≤ (|t| *1) * |t|^l.length :=
          mul_le_mul (mul_le_mul_of_nonneg_left (basis_rad_abs a) (abs_nonneg t)) ih
            (abs_nonneg _) (by positivity)
      _ = |t|^l.length * |t| := by ring

lemma radiusPower_logJet (j : ℕ) (q : ℝ) (x : Point) :
    LogJetBound (radiusPower (-q)) j q (3^j * (max 1 |q|)^j) x := by
  intro n hn
  have hc : 0 ≤ |q|^n * radiusPower (-q) x :=
    mul_nonneg (pow_nonneg (abs_nonneg q) _) (radiusPower_pos _ _).le
  have hb := multilinear_norm_of_components (iteratedFDeriv ℝ n (radiusPower (-q)) x) hc
    (fun a => by
      rw [iteratedFDeriv_basis_ofFn n a (radiusPower_diff (-q) n x),
        coordinateIter_radiusPower,Real.norm_eq_abs,abs_mul,
        abs_of_pos (radiusPower_pos (-q) x)]
      have he : |radialEigenvalue (-q) (List.ofFn a)| ≤ |q|^n := by
        simpa only [abs_neg,List.length_ofFn] using abs_radialEigenvalue (-q) (List.ofFn a)
      exact mul_le_mul_of_nonneg_right he (radiusPower_pos _ _).le)
  have hpow : |q|^n ≤ (max 1 |q|)^j :=
    (pow_le_pow_left₀ (abs_nonneg q) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hn)
  calc _ ≤ 3^n * (|q|^n * radiusPower (-q) x) := hb
    _ ≤ 3^j * ((max 1 |q|)^j * radiusPower (-q) x) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hn)
        (mul_le_mul_of_nonneg_right hpow (radiusPower_pos _ _).le) hc (by positivity)
    _ = _ := by ring

lemma compactified_uniform_logJet (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → ℝ} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      LogJetBound (fun y => f (inverseLogRadiusChart y)) j 0 C x := by
  classical
  choose C hC hb using (fun n : Fin (j+1) => compactified_scalar_uniform_jets n.val hK hf)
  refine ⟨∑ n, C n, Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro x hx n hn
  have hc : C ⟨n,by omega⟩ ≤ ∑ k, C k :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ _)
  simpa [radiusPower] using (hb ⟨n,by omega⟩ x hx).trans hc

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma boundaryProjection_sub (z : Point) : z - boundaryProjection z = z 0 • basis 0 := by
  simp [boundaryProjection]

lemma norm_sub_boundaryProjection (z : Point) : ‖z - boundaryProjection z‖ = |z 0| := by
  rw [boundaryProjection_sub,norm_smul,Real.norm_eq_abs]
  simp [basis,Pi.norm_single]

lemma angular_D_vanishes_boundary {f : Point → ℝ}
    (hf : ∀ z : Point, z 0 = 0 → f z = 0) {z : Point} (hz : z 0 = 0)
    {a : I} (ha : a ≠ 0) : D (basis a) f z = 0 := by
  by_cases hd : DifferentiableAt ℝ f z
  · have he : (fun t : ℝ => f (z + t • basis a)) = fun _ => (0:ℝ) := by
      funext t
      apply hf
      simp [hz,basis,Ne.symm ha]
    have hline := hd.hasFDerivAt.hasLineDerivAt (basis a)
    change HasDerivAt (fun t : ℝ => f (z + t • basis a)) (D (basis a) f z) 0 at hline
    rw [he] at hline
    exact hline.unique (hasDerivAt_const 0 0)
  · simp [D,fderiv_zero_of_not_differentiableAt hd]

lemma backwardScaledIter_vanishes_boundary {f : Point → ℝ}
    (hf : ∀ z : Point, z 0 = 0 → f z = 0) (l : List I) :
    ∀ z : Point, z 0 = 0 → backwardScaledIter l f z = 0 := by
  induction l with
  | nil => exact hf
  | cons a l ih =>
    intro z hz
    by_cases ha : a=0
    · simp [backwardScaledIter_cons,backwardScaledD,backwardFactor,ha,hz]
    · simp [backwardScaledIter_cons,backwardScaledD,backwardFactor,ha,
        angular_D_vanishes_boundary ih hz ha]

lemma coefficient_difference_vanishes (f : Point → ℝ) :
    ∀ z : Point, z 0 = 0 → (f z - f (boundaryProjection z)) = 0 := by
  intro z hz
  have he : boundaryProjection z = z := by simp [boundaryProjection,hz]
  rw [he,sub_self]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

theorem compactified_vanishing_jets (n : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → ℝ} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z)
    (hv : ∀ z : Point, z 0 = 0 → f z = 0)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ ≤
        C / Real.exp (x 0) := by
  let Q : Point → (Fin n → I) → (Point →L[ℝ] ℝ) :=
    fun z a => fderiv ℝ (backwardScaledIter (List.ofFn a) f) z
  have hQ : ContinuousOn Q K := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro a
    exact (backwardScaledIter_contDiffAt (List.ofFn a) 1
      ((hf z hz).of_le (by exact_mod_cast le_top))).continuousAt_fderiv
        (by norm_num)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hQ
  refine ⟨3^n * max 0 C,by positivity,?_⟩
  intro x hx
  let z := inverseLogRadiusChart x
  have hz : z ∈ K := hx
  have hbound (a : Fin n → I) :
      |backwardScaledIter (List.ofFn a) f z| ≤ max 0 C / Real.exp (x 0) := by
    have hd (w : Point) (hw : w ∈ segment ℝ (boundaryProjection z) z) :
        DifferentiableAt ℝ (backwardScaledIter (List.ofFn a) f) w :=
      (backwardScaledIter_contDiffAt (List.ofFn a) 1
        ((hf w (hsegment z hz hw)).of_le
          (by exact_mod_cast le_top))).differentiableAt (by norm_num)
    have hb (w : Point) (hw : w ∈ segment ℝ (boundaryProjection z) z) :
        ‖fderiv ℝ (backwardScaledIter (List.ofFn a) f) w‖ ≤ max 0 C :=
      (norm_le_pi_norm (Q w) a).trans ((hC w (hsegment z hz hw)).trans (le_max_right _ _))
    have h := (convex_segment (boundaryProjection z) z).norm_image_sub_le_of_norm_fderiv_le
      hd hb (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    rw [backwardScaledIter_vanishes_boundary hv _ _ (boundaryProjection_zero z),sub_zero,
      norm_sub_boundaryProjection,Real.norm_eq_abs] at h
    have he : |z 0| = (Real.exp (x 0))⁻¹ := by
      simp [z,inverseLogRadiusChart,Real.exp_neg]
    rw [he] at h
    simpa only [div_eq_mul_inv] using h
  have hfn : ContDiffAt ℝ n f z :=
    (hf z hz).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    hfn.comp x (inverseLogRadiusChart_smooth.contDiffAt.of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  have hb := multilinear_norm_of_components (iteratedFDeriv ℝ n
      (fun y => f (inverseLogRadiusChart y)) x)
      (show 0 ≤ max 0 C / Real.exp (x 0) by positivity)
      (fun a => by
        rw [iteratedFDeriv_basis_ofFn n a hcomp,Real.norm_eq_abs]
        rw [coordinateIter_inverse_pullback (f := f) (x := x) (List.ofFn a)
          (by simpa using hfn)]
        exact hbound a)
  simpa only [mul_div_assoc] using hb

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

structure FiniteLogDecay (j : ℕ) (q : ℝ) (U : Set Point) (f : Point → ℝ) : Prop where
  regular : ∀ x ∈ U, ContDiffAt ℝ j f x
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, LogJetBound f j q C x

namespace FiniteLogDecay
variable {j : ℕ} {q r : ℝ} {U : Set Point} {f g : Point → ℝ}

lemma germ_congr (hf : FiniteLogDecay j q U f)
    (he : ∀ x ∈ U, f =ᶠ[𝓝 x] g) : FiniteLogDecay j q U g := by
  refine ⟨fun x hx => (hf.regular x hx).congr_of_eventuallyEq (he x hx).symm, ?_⟩
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨C,hC,fun x hx n hn => ?_⟩
  rw [← ((he x hx).iteratedFDeriv ℝ n).eq_of_nhds]
  exact hb x hx n hn

lemma congr (hf : FiniteLogDecay j q U f) (he : f = g) : FiniteLogDecay j q U g := he ▸ hf

lemma add (hf : FiniteLogDecay j q U f) (hg : FiniteLogDecay j q U g) :
    FiniteLogDecay j q U (fun x => f x + g x) := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  obtain ⟨D,hD,hc⟩ := hg.bound
  refine ⟨fun x hx => (hf.regular x hx).add (hg.regular x hx),
    C+D,add_nonneg hC hD,?_⟩
  intro x hx n hn
  rw [fun_iteratedFDeriv_add_apply ((hf.regular x hx).of_le (by exact_mod_cast hn))
    ((hg.regular x hx).of_le (by exact_mod_cast hn))]
  exact (norm_add_le _ _).trans ((add_le_add (hb x hx n hn) (hc x hx n hn)).trans_eq
    (add_mul C D (radiusPower (-q) x)).symm)

lemma mul (hf : FiniteLogDecay j q U f) (hg : FiniteLogDecay j r U g) :
    FiniteLogDecay j (q+r) U (fun x => f x*g x) := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  obtain ⟨D,hD,hc⟩ := hg.bound
  exact ⟨fun x hx => (hf.regular x hx).mul (hg.regular x hx),2^j*C*D,by positivity,
    fun x hx => LogJetBound.mul hC hD (hf.regular x hx) (hg.regular x hx) (hb x hx) (hc x hx)⟩

lemma weaken (hf : FiniteLogDecay j q U f) (h : r ≤ q)
    (hU : ∀ x ∈ U, 0 ≤ x 0) : FiniteLogDecay j r U f := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨hf.regular,C,hC,?_⟩
  intro x hx n hn
  refine (hb x hx n hn).trans (mul_le_mul_of_nonneg_left ?_ hC)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg h) (hU x hx)

lemma zero (j : ℕ) (q : ℝ) (U : Set Point) : FiniteLogDecay j q U (fun _ => 0) := by
  refine ⟨fun _ _ => contDiffAt_const,0,le_refl _,?_⟩
  intro x hx n hn
  simp

lemma sum {ι : Type*} (s : Finset ι) (F : ι → Point → ℝ)
    (hF : ∀ i ∈ s, FiniteLogDecay j q U (F i)) :
    FiniteLogDecay j q U (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero j q U
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hF i (Finset.mem_insert_self _ _)).add (ih (fun k hk => hF k (Finset.mem_insert_of_mem hk)))

lemma radiusPower (j : ℕ) (q : ℝ) (U : Set Point) :
    FiniteLogDecay j q U (CKSMixedGeometry.radiusPower (-q)) :=
  ⟨fun x _ => radiusPower_diff (-q) j x,
    3^j*(max 1 |q|)^j,by positivity,fun x _ => radiusPower_logJet j q x⟩

lemma compactified (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z) :
    FiniteLogDecay j 0 (inverseLogRadiusChart ⁻¹' K)
      (fun x => F (inverseLogRadiusChart x)) := by
  refine ⟨fun x hx => ?_,compactified_uniform_logJet j hK hF⟩
  exact ((hF _ hx).comp x inverseLogRadiusChart_smooth.contDiffAt).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))

lemma vanishing (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z)
    (hv : ∀ z : Point, z 0 = 0 → F z = 0)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K) :
    FiniteLogDecay j 1 (inverseLogRadiusChart ⁻¹' K)
      (fun x => F (inverseLogRadiusChart x)) := by
  classical
  have hs := compactified j hK hF
  choose C hC hb using (fun n : Fin (j+1) => compactified_vanishing_jets n.val hK hF hv hsegment)
  refine ⟨hs.regular,∑ n, C n,Finset.sum_nonneg (fun n _ => hC n),?_⟩
  intro x hx n hn
  have hc : C ⟨n,by omega⟩ ≤ ∑ k, C k :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ _)
  calc _ ≤ C ⟨n,by omega⟩ / Real.exp (x 0) := hb ⟨n,by omega⟩ x hx
    _ ≤ (∑ k, C k) / Real.exp (x 0) := div_le_div_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := by simp [CKSMixedGeometry.radiusPower,Real.exp_neg,div_eq_mul_inv]

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff
namespace FiniteLogDecay

lemma mono {j : ℕ} {q : ℝ} {U V : Set Point} {f : Point → ℝ}
    (hf : FiniteLogDecay j q U f) (hV : V ⊆ U) : FiniteLogDecay j q V f := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  exact ⟨fun x hx => hf.regular x (hV hx),C,hC,fun x hx => hb x (hV hx)⟩

lemma compactified_difference (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K) :
    FiniteLogDecay j 1 (inverseLogRadiusChart ⁻¹' K)
      (fun x => F (inverseLogRadiusChart x) - F (boundaryProjection (inverseLogRadiusChart x))) := by
  apply vanishing j hK _ (coefficient_difference_vanishes F) hsegment
  intro z hz
  have hp : boundaryProjection z ∈ K := hsegment z hz (left_mem_segment ℝ _ _)
  exact (hF z hz).sub ((hF _ hp).comp z boundaryProjection.contDiff.contDiffAt)

lemma weighted_compactified (j : ℕ) (q : ℝ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z) :
    FiniteLogDecay j q (inverseLogRadiusChart ⁻¹' K)
      (fun x => CKSMixedGeometry.radiusPower (-q) x * F (inverseLogRadiusChart x)) := by
  simpa only [add_zero] using (radiusPower j q _).mul (compactified j hK hF)

lemma weighted_difference (j : ℕ) (q : ℝ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K) :
    FiniteLogDecay j (q+1) (inverseLogRadiusChart ⁻¹' K)
      (fun x => CKSMixedGeometry.radiusPower (-q) x * F (inverseLogRadiusChart x) -
        CKSMixedGeometry.radiusPower (-q) x * F (boundaryProjection (inverseLogRadiusChart x))) := by
  have h := (radiusPower j q _).mul (compactified_difference j hK hF hsegment)
  simpa only [mul_sub] using h

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem lorentz_source_remainder_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    (U : Set Point) (hU : U ⊆ inverseLogRadiusChart ⁻¹' K)
    {f : Point → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x ∈ U, ContDiffAt ℝ j f (logRadiusChart (logLorentzChart e m p φ ψ x)))
    (hb : ∀ x ∈ U, ScaledComponentBound f j q B (logRadiusChart (logLorentzChart e m p φ ψ x))) :
    FiniteLogDecay j q U (fun x => f (logRadiusChart (logLorentzChart e m p φ ψ x))) := by
  have hs (x : Point) (hx : x ∈ U) : ContDiffAt ℝ j
      (fun y => f (logRadiusChart (logLorentzChart e m p φ ψ y))) x := by
    have hc := (logLorentzChart_contDiffAt e m p φ ψ (hφ _ (hU hx))
      (hreg _ (hU hx)) (hψ _ (hU hx))).of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    exact (hf x hx).comp x ((logRadiusChart_smooth.contDiffAt.of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).comp x hc)
  obtain ⟨C,hC,hc⟩ := lorentz_finite_remainder_pullback e m p φ ψ j q hK hφ hreg hψ
  refine ⟨hs,3^j*C*B,by positivity,?_⟩
  intro x hx n hn
  have h := multilinear_norm_of_components (iteratedFDeriv ℝ n
      (fun y => f (logRadiusChart (logLorentzChart e m p φ ψ y))) x)
      (show 0 ≤ C*B/Real.exp (x 0)^q by positivity)
      (fun a => by rw [iteratedFDeriv_basis_ofFn n a ((hs x hx).of_le (by exact_mod_cast hn)),
        Real.norm_eq_abs]
                   exact hc f B hB x (hU hx) (hf x hx) (hb x hx) _ (by simpa using hn))
  calc _ ≤ 3^n*(C*B/Real.exp (x 0)^q) := h
    _ ≤ 3^j*(C*B/Real.exp (x 0)^q) := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hn) (by positivity)
    _ = _ := by rw [radiusPower_neg_nat]; ring

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma radiusPower_add (t u : ℝ) (x : Point) :
    radiusPower (t+u) x = radiusPower t x*radiusPower u x := by
  simp only [radiusPower,add_mul,Real.exp_add]

lemma logLorentzChart_radial_coeff (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (x : Point) : (logLorentzChart e m p φ ψ x) 0 =
      x 0 + compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart x) 0 := by
  rw [logLorentzChart_eq_slice]
  simp only [slice_zero,compactLorentzCoefficients]

lemma logLorentzChart_angular_coeff (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (x : Point) : angularProjection (logLorentzChart e m p φ ψ x) =
      angularProjection (compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart x)) := by
  rw [logLorentzChart_eq_slice]
  ext a
  simp [compactLorentzCoefficients,angularProjection]

lemma radiusPower_lorentz (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) (t : ℝ)
    (x : Point) : radiusPower t (logLorentzChart e m p φ ψ x) = radiusPower t x *
      Real.exp (t*compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart x) 0) := by
  simp only [radiusPower,logLorentzChart_radial_coeff,mul_add,Real.exp_add]

lemma ordinaryLeadingComponent_log_lorentz (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) (q : ℕ) (M : Angle → ℝ) (x : Point) :
    ordinaryLeadingComponent q M (logRadiusChart (logLorentzChart e m p φ ψ x)) =
      radiusPower (-(q:ℝ)) (logLorentzChart e m p φ ψ x) *
        M (angularProjection (compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart x))) := by
  simp only [ordinaryLeadingComponent,logRadiusChart,ite_true,
    angularProjection_logRadiusChart,radiusPower_neg_nat,logLorentzChart_angular_coeff]

lemma weighted_ordinary_leading (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) (q : ℕ) (w : ℝ) (M : Angle → ℝ) (x : Point) :
    radiusPower w (logLorentzChart e m p φ ψ x) *
      ordinaryLeadingComponent q M (logRadiusChart (logLorentzChart e m p φ ψ x)) =
      radiusPower (-(q-w)) x * compactLeadingCoefficient e m p φ ψ (q-w) M (inverseLogRadiusChart x) := by
  rw [ordinaryLeadingComponent_log_lorentz,← mul_assoc,← radiusPower_add]
  have he : w + -(q:ℝ) = -((q:ℝ)-w) := by ring
  rw [he,radiusPower_lorentz]
  exact mul_assoc _ _ _

lemma compactLeadingCoefficient_regular (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (q : ℝ) {M : Angle → ℝ} {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    (hM : ContDiffAt ℝ ∞ M (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    ContDiffAt ℝ ∞ (compactLeadingCoefficient e m p φ ψ q M) z := by
  have hc := compactLorentzCoefficients_contDiffAt e m p φ ψ hφ hz hψ
  exact (contDiffAt_const.mul ((contDiffAt_pi.mp hc) 0)).exp.mul
    (hM.comp z (angularProjection.contDiff.contDiffAt.comp z hc))

lemma lorentz_radius_weight_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) (t : ℝ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    FiniteLogDecay j (-t) (inverseLogRadiusChart ⁻¹' K)
      (fun x => radiusPower t (logLorentzChart e m p φ ψ x)) := by
  have h := FiniteLogDecay.weighted_compactified j (-t) hK (fun z hz =>
    ((contDiffAt_const (c := t)).mul ((contDiffAt_pi.mp
      (compactLorentzCoefficients_contDiffAt e m p φ ψ (hφ z hz) (hreg z hz) (hψ z hz))) 0)).exp)
  apply h.congr
  funext x
  rw [neg_neg,radiusPower_lorentz]

end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma source_remainder_lorentz_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    {U V : Set Point} (hU : U ⊆ inverseLogRadiusChart ⁻¹' K)
    (hV : ∀ x ∈ U, logRadiusChart (logLorentzChart e m p φ ψ x) ∈ V)
    {f : Point → ℝ} (hf : SourceRemainderOn j q V f) :
    FiniteLogDecay j q U (fun x => f (logRadiusChart (logLorentzChart e m p φ ψ x))) := by
  obtain ⟨B,hB,hb⟩ := hf.bound
  exact lorentz_source_remainder_decay e m p φ ψ j q hK hφ hreg hψ U hU hB
    (fun x hx => hf.regular _ (hV x hx)) (fun x hx => hb _ (hV x hx))

lemma weighted_source_remainder_lorentz_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q : ℕ) (w : ℝ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    {U V : Set Point} (hU : U ⊆ inverseLogRadiusChart ⁻¹' K)
    (hV : ∀ x ∈ U, logRadiusChart (logLorentzChart e m p φ ψ x) ∈ V)
    {f : Point → ℝ} (hf : SourceRemainderOn j q V f) :
    FiniteLogDecay j (q-w) U (fun x => radiusPower w (logLorentzChart e m p φ ψ x) *
      f (logRadiusChart (logLorentzChart e m p φ ψ x))) := by
  have hpow := (lorentz_radius_weight_decay e m p φ ψ j w hK hφ hreg hψ).mono hU
  have hr := source_remainder_lorentz_decay e m p φ ψ j q hK hφ hreg hψ hU hV hf
  convert hpow.mul hr using 1
  ring

lemma weighted_source_leading_remainder (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q qlead : ℕ) (w : ℝ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    {U V : Set Point} (hU : U ⊆ inverseLogRadiusChart ⁻¹' K)
    (hV : ∀ x ∈ U, logRadiusChart (logLorentzChart e m p φ ψ x) ∈ V)
    {f : Point → ℝ} {M : Angle → ℝ}
    (hf : SourceRemainderOn j q V (fun y => f y-ordinaryLeadingComponent qlead M y)) :
    FiniteLogDecay j (q-w) U (fun x => radiusPower w (logLorentzChart e m p φ ψ x) *
      f (logRadiusChart (logLorentzChart e m p φ ψ x)) -
        radiusPower (-(qlead-w)) x * compactLeadingCoefficient e m p φ ψ (qlead-w) M (inverseLogRadiusChart x)) := by
  have h := weighted_source_remainder_lorentz_decay e m p φ ψ j q w hK hφ hreg hψ hU hV hf
  apply h.congr
  funext x
  rw [mul_sub,weighted_ordinary_leading]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set
open scoped ContDiff Topology

def squaredCompactSpatial (e m : ℝ) (p : E) (φ : Angle → E) (z : Point) : E :=
  φ (angularProjection z) +
    (Real.sqrt (1+z 0) / m + inner ℝ p (φ (angularProjection z)) / (m*(e+m))) • p

def squaredLorentzCoefficients (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (z : Point) : Point :=
  let v := squaredCompactSpatial e m p φ z
  slice (Real.log ‖v‖) (ψ (‖v‖⁻¹ • v))

lemma squareRadialChart_smooth : ContDiff ℝ ∞ squareRadialChart := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [squareRadialChart,slice_zero,ContinuousLinearMap.proj_apply] using
      ((ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).contDiff.pow 2)
  · simpa only [squareRadialChart,slice_succ,ContinuousLinearMap.proj_apply,Function.comp_def] using
      (ContinuousLinearMap.proj a : Angle →L[ℝ] ℝ).contDiff.comp angularProjection.contDiff

lemma squaredCompactSpatial_square (e m : ℝ) (p : E) (φ : Angle → E) (z : Point) :
    squaredCompactSpatial e m p φ (squareRadialChart z) =
      compactSpatial e m p (compactPolar φ z) := by
  simp [squaredCompactSpatial,squareRadialChart,compactSpatial,compactPolar,compactRoot,angularProjection]

lemma compactLorentzCoefficients_squared (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) (z : Point) :
    compactLorentzCoefficients e m p φ ψ z =
      squaredLorentzCoefficients e m p φ ψ (squareRadialChart z) := by
  simp [squaredLorentzCoefficients,squaredCompactSpatial_square,
    compactLorentzCoefficients,compactScale,compactAngle]

lemma squaredCompactSpatial_contDiffAt (e m : ℝ) (p : E) (φ : Angle → E)
    {z : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection z)) (hz : -1 < z 0) :
    ContDiffAt ℝ ∞ (squaredCompactSpatial e m p φ) z := by
  have hang := hφ.comp z angularProjection.contDiff.contDiffAt
  have hroot : ContDiffAt ℝ ∞ (fun w : Point => Real.sqrt (1+w 0)) z :=
    (contDiffAt_const.add (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).contDiff.contDiffAt).sqrt
      (by change 1 + z 0 ≠ 0; linarith)
  exact hang.add (((hroot.div_const m).add
    ((ContDiffAt.inner ℝ (contDiffAt_const (c := p)) hang).div_const (m*(e+m)))).smul_const p)

lemma squaredLorentzCoefficients_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z)) (hz : -1 < z 0)
    (hv : squaredCompactSpatial e m p φ z ≠ 0)
    (hψ : ContDiffAt ℝ ∞ ψ (‖squaredCompactSpatial e m p φ z‖⁻¹ •
      squaredCompactSpatial e m p φ z)) :
    ContDiffAt ℝ ∞ (squaredLorentzCoefficients e m p φ ψ) z := by
  have h := squaredCompactSpatial_contDiffAt e m p φ hφ hz
  have hn := h.norm ℝ hv
  have ha := hψ.comp z ((hn.inv (norm_ne_zero_iff.mpr hv)).smul h)
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [squaredLorentzCoefficients,slice_zero] using hn.log (norm_ne_zero_iff.mpr hv)
  · simpa [squaredLorentzCoefficients,Function.comp_def,Pi.smul_apply,Pi.inv_apply] using (contDiffAt_pi.mp ha) a

lemma squaredLorentzCoefficients_regular (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ContDiffAt ℝ ∞ (squaredLorentzCoefficients e m p φ ψ) (squareRadialChart z) := by
  apply squaredLorentzCoefficients_contDiffAt
  · simpa only [angularProjection_squareRadialChart] using hφ
  · simp only [squareRadialChart,slice_zero]
    linarith [sq_nonneg (z 0)]
  · rw [squaredCompactSpatial_square]
    exact norm_ne_zero_iff.mp hz.2.ne'
  · simpa only [squaredCompactSpatial_square,compactScale,compactAngle] using hψ

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set
open scoped ContDiff Topology

def squareRadialDerivative (z : Point) : Point →L[ℝ] Point :=
  ContinuousLinearMap.pi (fun i => if i=0 then (2*z 0) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma squareRadialChart_hasFDerivAt (z : Point) :
    HasFDerivAt squareRadialChart (squareRadialDerivative z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [squareRadialChart,slice_zero,ite_true]
    change HasFDerivAt (fun w : Point => (w 0)^2)
      ((2*z 0) • (ContinuousLinearMap.proj (0 : I) : Point →L[ℝ] ℝ)) z
    have hd : HasFDerivAt (fun w : Point => w 0) (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ) z :=
      hasFDerivAt_apply (0 : I) z
    simpa only [Nat.reduceSub,pow_one,nsmul_eq_mul,Nat.cast_ofNat] using hd.pow 2
  · simp only [squareRadialChart,slice_succ,Fin.succ_ne_zero,ite_false]
    change HasFDerivAt (fun w : Point => w a.succ) (ContinuousLinearMap.proj a.succ) z
    exact hasFDerivAt_apply a.succ z

lemma squareRadialDerivative_zero (z : Point) :
    squareRadialDerivative z (basis 0) = (2*z 0) • basis 0 := by
  ext i
  by_cases hi : i=0
  · subst i; simp [squareRadialDerivative,basis]
  · simp [squareRadialDerivative,basis,hi]

lemma D_zero_square_pullback {f : Point → ℝ} {z : Point}
    (hf : DifferentiableAt ℝ f (squareRadialChart z)) :
    D (basis 0) (fun w => f (squareRadialChart w)) z =
      (2*z 0)*D (basis 0) f (squareRadialChart z) := by
  unfold D
  change fderiv ℝ (f ∘ squareRadialChart) z (basis 0) = _
  rw [fderiv_comp z hf (squareRadialChart_hasFDerivAt z).differentiableAt,
    (squareRadialChart_hasFDerivAt z).fderiv]
  simp only [ContinuousLinearMap.comp_apply,squareRadialDerivative_zero,
    map_smul,smul_eq_mul]

def lorentzRadialJacCorrection (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (i : I) (z : Point) : ℝ :=
  -2 * D (basis 0) (fun w => squaredLorentzCoefficients e m p φ ψ w i) (squareRadialChart z)

lemma lorentzLogJac_contDiffAt (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {z : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) (a i : I) :
    ContDiffAt ℝ ∞ (lorentzLogJac e m p φ ψ a i) z := by
  have hf := (contDiffAt_pi.mp (compactLorentzCoefficients_contDiffAt e m p φ ψ hφ hz hψ)) i
  exact contDiffAt_const.add ((backwardFactor_smooth a).contDiffAt.mul
    (contDiffAt_D hf (by simp) (basis a)))

lemma lorentzRadialJacCorrection_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) (i : I) :
    ContDiffAt ℝ ∞ (lorentzRadialJacCorrection e m p φ ψ i) z := by
  have hf := (contDiffAt_pi.mp (squaredLorentzCoefficients_regular e m p φ ψ hφ hz hψ)) i
  exact contDiffAt_const.mul
    ((contDiffAt_D hf (by simp) (basis 0)).comp z squareRadialChart_smooth.contDiffAt)

lemma D_logLorentzChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {x : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x)))) (a i : I) :
    D (basis a) (fun y => logLorentzChart e m p φ ψ y i) x =
      lorentzLogJac e m p φ ψ a i (inverseLogRadiusChart x) := by
  let L : Point →L[ℝ] ℝ := (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).comp radialLinear
  have he : (fun y => logLorentzChart e m p φ ψ y i) =
      fun y => L y + compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart y) i := rfl
  have hf := (contDiffAt_pi.mp (compactLorentzCoefficients_contDiffAt e m p φ ψ hφ hz hψ)) i
  have hd : DifferentiableAt ℝ
      (fun y => compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart y) i) x :=
    (hf.comp x inverseLogRadiusChart_smooth.contDiffAt).differentiableAt (by simp)
  rw [he,D_add (basis a) L.differentiableAt hd,
    D_clm,D_inverse_pullback a (hf.differentiableAt (by simp))]
  unfold lorentzLogJac
  congr 1
  change (basis a 0) * basis 0 i = (if a = 0 ∧ i = 0 then 1 else 0)
  by_cases ha : a = 0 <;> by_cases hi : i = 0
  · subst a; subst i; simp [basis]
  · subst a; simp [basis,hi]
  · subst i; simp [basis,ha,Ne.symm ha]
  · simp [basis,ha,Ne.symm ha,hi]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma lorentzLogJac_radial_of_differentiable (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (i : I) {z : Point} (hf : DifferentiableAt ℝ
      (fun w => squaredLorentzCoefficients e m p φ ψ w i) (squareRadialChart z)) :
    lorentzLogJac e m p φ ψ 0 i z =
      (if i=0 then 1 else 0) + (z 0)^2 * lorentzRadialJacCorrection e m p φ ψ i z := by
  have he : (fun w => compactLorentzCoefficients e m p φ ψ w i) =
      fun w => squaredLorentzCoefficients e m p φ ψ (squareRadialChart w) i := by
    funext w
    rw [compactLorentzCoefficients_squared]
  simp only [lorentzLogJac,backwardScaledD,backwardFactor,ite_true,true_and,he]
  rw [D_zero_square_pullback hf]
  unfold lorentzRadialJacCorrection
  ring

lemma lorentzLogJac_radial_germ (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {z : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) (i : I) :
    lorentzLogJac e m p φ ψ 0 i =ᶠ[𝓝 z]
      (fun w => (if i=0 then 1 else 0) + (w 0)^2 * lorentzRadialJacCorrection e m p φ ψ i w) := by
  have hf := (contDiffAt_pi.mp (squaredLorentzCoefficients_regular e m p φ ψ hφ hz hψ)) i
  have hf1 : ContDiffAt ℝ 1 (fun w => squaredLorentzCoefficients e m p φ ψ w i)
      (squareRadialChart z) := hf.of_le (by simp)
  have hn := squareRadialChart_smooth.continuous.continuousAt.eventually
    (hf1.eventually (by simp))
  filter_upwards [hn] with w hw
  exact lorentzLogJac_radial_of_differentiable e m p φ ψ i (hw.differentiableAt (by simp))

lemma lorentzLogJac_radial_log_germ (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {x : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x)))) (i : I) :
    (fun y => lorentzLogJac e m p φ ψ 0 i (inverseLogRadiusChart y)) =ᶠ[𝓝 x]
      (fun y => (if i=0 then 1 else 0) + radiusPower (-2) y *
        lorentzRadialJacCorrection e m p φ ψ i (inverseLogRadiusChart y)) := by
  have hn := inverseLogRadiusChart_smooth.continuous.continuousAt.eventually
    (lorentzLogJac_radial_germ e m p φ ψ hφ hz hψ i)
  filter_upwards [hn] with y hy
  rw [hy]
  have he : (inverseLogRadiusChart y 0)^2 = radiusPower (-2) y := by
    simp only [inverseLogRadiusChart,ite_true,radiusPower]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

theorem lorentz_jacobian_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    (∀ a i, FiniteLogDecay j 0 (inverseLogRadiusChart ⁻¹' K)
      (fun x => lorentzLogJac e m p φ ψ a i (inverseLogRadiusChart x))) ∧
    (∀ i, FiniteLogDecay j 2 (inverseLogRadiusChart ⁻¹' K)
      (fun x => lorentzLogJac e m p φ ψ 0 i (inverseLogRadiusChart x) - (if i=0 then 1 else 0))) := by
  constructor
  · intro a i
    exact FiniteLogDecay.compactified j hK (fun z hz =>
      lorentzLogJac_contDiffAt e m p φ ψ (hφ z hz) (hreg z hz) (hψ z hz) a i)
  · intro i
    have h := FiniteLogDecay.weighted_compactified j 2 hK (fun z hz =>
      lorentzRadialJacCorrection_contDiffAt e m p φ ψ (hφ z hz) (hreg z hz) (hψ z hz) i)
    apply h.germ_congr
    intro x hx
    filter_upwards [lorentzLogJac_radial_log_germ e m p φ ψ (hφ _ hx) (hreg _ hx) (hψ _ hx) i]
      with y hy
    rw [hy]
    ring

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def logTensorRate (i k : I) : ℝ :=
  if i=0 then (if k=0 then 3 else 2) else (if k=0 then 2 else 1)

def logJacRate (a i : I) : ℝ := if a=0 ∧ i≠0 then 2 else 0

lemma tensor_rate_inequality (a b i k : I) :
    logTensorRate a b ≤ logJacRate a i + logJacRate b k + logTensorRate i k := by
  by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    by_cases hi : i=0 <;> by_cases hk : k=0 <;>
      norm_num [logTensorRate,logJacRate,ha,hb,hi,hk]

theorem finite_log_tensor_pullback_rates (j : ℕ) {U : Set Point}
    (hU : ∀ x ∈ U, 0 ≤ x 0) {J T : I → I → Point → ℝ}
    (hJ : ∀ a i, FiniteLogDecay j (logJacRate a i) U (J a i))
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k)) :
    ∀ a b, FiniteLogDecay j (logTensorRate a b) U (logCovariantPullback J T a b) := by
  intro a b
  apply FiniteLogDecay.sum
  intro i _
  apply FiniteLogDecay.sum
  intro k _
  exact (((hJ a i).mul (hJ b k)).mul (hT i k)).weaken (tensor_rate_inequality a b i k) hU

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma angular_leading_term_decay (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K)
    {U : Set Point} (hUK : U ⊆ inverseLogRadiusChart ⁻¹' K) (hU : ∀ x ∈ U, 0 ≤ x 0)
    {J C T : I → I → Point → ℝ}
    (hJ : ∀ a i z, z ∈ K → ContDiffAt ℝ ∞ (J a i) z)
    (hC : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (C i k) z)
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k))
    (hE : ∀ i k, i≠0 → k≠0 → FiniteLogDecay j 2 U
      (fun x => T i k x - radiusPower (-1) x * C i k (inverseLogRadiusChart x)))
    (a b i k : I) :
    FiniteLogDecay j 2 U (fun x =>
      J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x) * T i k x -
        radiusPower (-1) x * (J a i (boundaryProjection (inverseLogRadiusChart x)) *
          J b k (boundaryProjection (inverseLogRadiusChart x)) *
          angularLeadingEntry C i k (boundaryProjection (inverseLogRadiusChart x)))) := by
  have hJJ := ((FiniteLogDecay.compactified j hK (hJ a i)).mono hUK).mul
    ((FiniteLogDecay.compactified j hK (hJ b k)).mono hUK)
  by_cases hi : i=0
  · have hTi : FiniteLogDecay j 2 U (T i k) :=
      (hT i k).weaken (by simp [logTensorRate,hi]; split_ifs <;> norm_num) hU
    simpa only [zero_add,angularLeadingEntry,hi,ne_eq,not_true_eq_false,false_and,ite_false,
      mul_zero,sub_zero] using hJJ.mul hTi
  by_cases hk : k=0
  · have hTi : FiniteLogDecay j 2 U (T i k) :=
      (hT i k).weaken (by simp [logTensorRate,hi,hk]) hU
    simpa only [zero_add,angularLeadingEntry,hk,ne_eq,not_true_eq_false,and_false,ite_false,
      mul_zero,sub_zero] using hJJ.mul hTi
  have he : FiniteLogDecay j 2 U (fun x =>
      (J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x)) *
        (T i k x - radiusPower (-1) x * C i k (inverseLogRadiusChart x))) := by
    simpa only [zero_add] using hJJ.mul (hE i k hi hk)
  have hd := (FiniteLogDecay.weighted_difference j 1 hK
    (fun z hz => ((hJ a i z hz).mul (hJ b k z hz)).mul (hC i k hi hk z hz)) hsegment).mono hUK
  have hadd : FiniteLogDecay j 2 U (fun x =>
      (J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x)) *
        (T i k x - radiusPower (-1) x * C i k (inverseLogRadiusChart x)) +
      (radiusPower (-1) x * (J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x) *
        C i k (inverseLogRadiusChart x)) - radiusPower (-1) x *
        (J a i (boundaryProjection (inverseLogRadiusChart x)) *
         J b k (boundaryProjection (inverseLogRadiusChart x)) * C i k (boundaryProjection (inverseLogRadiusChart x))))) :=
    he.add (by simpa only [show (1:ℝ)+1=2 by norm_num] using hd)
  apply hadd.congr
  funext x
  simp only [angularLeadingEntry,ne_eq,hi,hk,not_false_eq_true,true_and,ite_true]
  ring

theorem finite_log_tensor_angular_leading (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K)
    {U : Set Point} (hUK : U ⊆ inverseLogRadiusChart ⁻¹' K) (hU : ∀ x ∈ U, 0 ≤ x 0)
    {J C T : I → I → Point → ℝ}
    (hJ : ∀ a i z, z ∈ K → ContDiffAt ℝ ∞ (J a i) z)
    (hC : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (C i k) z)
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k))
    (hE : ∀ i k, i≠0 → k≠0 → FiniteLogDecay j 2 U
      (fun x => T i k x - radiusPower (-1) x * C i k (inverseLogRadiusChart x))) :
    ∀ a b, FiniteLogDecay j 2 U (fun x =>
      logCovariantPullback (fun a i x => J a i (inverseLogRadiusChart x)) T a b x -
        radiusPower (-1) x * transformedAngularLeading J C a b (boundaryProjection (inverseLogRadiusChart x))) := by
  intro a b
  let F : I → I → Point → ℝ := fun i k x =>
    J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x) * T i k x -
      radiusPower (-1) x * (J a i (boundaryProjection (inverseLogRadiusChart x)) *
        J b k (boundaryProjection (inverseLogRadiusChart x)) *
        angularLeadingEntry C i k (boundaryProjection (inverseLogRadiusChart x)))
  have h := FiniteLogDecay.sum Finset.univ (fun i x => ∑ k, F i k x)
    (fun i _ => FiniteLogDecay.sum Finset.univ (F i) (fun k _ =>
      angular_leading_term_decay j hK hsegment hUK hU hJ hC hT hE a b i k))
  apply h.congr
  funext x
  simp only [F,logCovariantPullback,transformedAngularLeading,Finset.sum_sub_distrib,Finset.mul_sum]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma radial_leading_00_decay (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K)
    {U : Set Point} (hUK : U ⊆ inverseLogRadiusChart ⁻¹' K) (hU : ∀ x ∈ U, 0 ≤ x 0)
    {J T C : Point → ℝ} (hC : ∀ z ∈ K, ContDiffAt ℝ ∞ C z)
    (hJ : FiniteLogDecay j 0 U J)
    (hδ : FiniteLogDecay j 2 U (fun x => J x-1))
    (hE : FiniteLogDecay j 4 U
      (fun x => T x - radiusPower (-3) x * C (inverseLogRadiusChart x))) :
    FiniteLogDecay j 4 U (fun x => J x*J x*T x -
      radiusPower (-3) x*C (boundaryProjection (inverseLogRadiusChart x))) := by
  have hsq : FiniteLogDecay j 2 U (fun x => J x*J x-1) := by
    have hmul : FiniteLogDecay j 2 U (fun x => (J x-1)*J x) := by
      simpa only [add_zero] using hδ.mul hJ
    apply (hmul.add hδ).congr
    funext x
    ring
  have hlead := (FiniteLogDecay.weighted_compactified j 3 hK hC).mono hUK
  have hrest : FiniteLogDecay j 4 U (fun x =>
      (J x*J x)*(T x-radiusPower (-3) x*C (inverseLogRadiusChart x))) := by
    simpa only [zero_add] using (hJ.mul hJ).mul hE
  have hsquare : FiniteLogDecay j 4 U (fun x =>
      (radiusPower (-3) x*C (inverseLogRadiusChart x))*(J x*J x-1)) :=
    (hlead.mul hsq).weaken (by norm_num) hU
  have hdiff : FiniteLogDecay j 4 U (fun x =>
      radiusPower (-3) x*C (inverseLogRadiusChart x) -
        radiusPower (-3) x*C (boundaryProjection (inverseLogRadiusChart x))) := by
    simpa only [show (3:ℝ)+1=4 by norm_num] using
      (FiniteLogDecay.weighted_difference j 3 hK hC hsegment).mono hUK
  apply ((hrest.add hsquare).add hdiff).congr
  funext x
  ring

lemma radial_off_diagonal_entry_decay (j : ℕ) {U : Set Point}
    (hU : ∀ x ∈ U, 0 ≤ x 0) {J T : I → I → Point → ℝ}
    (hJ : ∀ i, FiniteLogDecay j (logJacRate 0 i) U (J 0 i))
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k))
    (i k : I) (hik : ¬(i=0 ∧ k=0)) :
    FiniteLogDecay j 4 U (fun x => J 0 i x*J 0 k x*T i k x) := by
  refine (((hJ i).mul (hJ k)).mul (hT i k)).weaken ?_ hU
  by_cases hi : i=0 <;> by_cases hk : k=0
  · exact False.elim (hik ⟨hi,hk⟩)
  · norm_num [logJacRate,logTensorRate,hi,hk]
  · norm_num [logJacRate,logTensorRate,hi,hk]
  · norm_num [logJacRate,logTensorRate,hi,hk]

theorem finite_log_tensor_radial_leading (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K)
    {U : Set Point} (hUK : U ⊆ inverseLogRadiusChart ⁻¹' K) (hU : ∀ x ∈ U, 0 ≤ x 0)
    {J T : I → I → Point → ℝ} {C : Point → ℝ}
    (hC : ∀ z ∈ K, ContDiffAt ℝ ∞ C z)
    (hJ : ∀ i, FiniteLogDecay j (logJacRate 0 i) U (J 0 i))
    (hδ : FiniteLogDecay j 2 U (fun x => J 0 0 x-1))
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k))
    (hE : FiniteLogDecay j 4 U (fun x => T 0 0 x -
      radiusPower (-3) x * C (inverseLogRadiusChart x))) :
    FiniteLogDecay j 4 U (fun x => logCovariantPullback J T 0 0 x -
      radiusPower (-3) x * C (boundaryProjection (inverseLogRadiusChart x))) := by
  classical
  have he (i k : I) : FiniteLogDecay j 4 U (fun x => J 0 i x*J 0 k x*T i k x -
      if i=0 ∧ k=0 then radiusPower (-3) x*C (boundaryProjection (inverseLogRadiusChart x)) else 0) := by
    by_cases hik : i=0 ∧ k=0
    · rcases hik with ⟨rfl,rfl⟩
      simpa only [and_self,ite_true] using radial_leading_00_decay j hK hsegment hUK hU hC
        (by simpa [logJacRate] using hJ 0) hδ hE
    · simpa only [hik,ite_false,sub_zero] using radial_off_diagonal_entry_decay j hU hJ hT i k hik
  have h := FiniteLogDecay.sum Finset.univ _ (fun i _ => FiniteLogDecay.sum Finset.univ _
    (fun k _ => he i k))
  apply h.congr
  funext x
  simp [logCovariantPullback,Finset.sum_sub_distrib,ite_and]

end
end CKSMixedGeometry

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

structure LorentzChartDomain (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (K U V : Set Point) : Prop where
  compact : IsCompact K
  chart : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z)
  region : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p
  chartInv : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))
  segment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K
  newRegion : U ⊆ inverseLogRadiusChart ⁻¹' K
  oldRegion : ∀ x ∈ U, logRadiusChart (logLorentzChart e m p φ ψ x) ∈ V
  largeRadius : ∀ x ∈ U, 0 ≤ x 0

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma oldLogTensor_radial_remainder (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg) :
    FiniteLogDecay j (qrad-2) U (fun x => oldLogTensor e m p φ ψ A 0 0 x -
      radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr (inverseLogRadiusChart x)) := by
  have h := weighted_source_leading_remainder e m p φ ψ j qrad 5 2
      hd.compact hd.chart hd.region hd.chartInv hd.newRegion hd.oldRegion hA.radial
  convert h using 1
  norm_num [oldLogTensor,radialIndexWeight]

lemma oldLogTensor_angular_remainder (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg) (i k : I) (hi : i≠0) (hk : k≠0) :
    FiniteLogDecay j 2 U (fun x => oldLogTensor e m p φ ψ A i k x -
      radiusPower (-1) x * compactAngularCoefficient e m p φ ψ mg i k (inverseLogRadiusChart x)) := by
  simpa [oldLogTensor,radialIndexWeight,hi,hk,compactAngularCoefficient] using weighted_source_leading_remainder e m p φ ψ j 2 1 0
      hd.compact hd.chart hd.region hd.chartInv hd.newRegion hd.oldRegion (hA.angular i k hi hk)

lemma oldLogTensor_mixed_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg) (i k : I)
    (hik : (i=0 ∧ k≠0) ∨ (i≠0 ∧ k=0)) :
    FiniteLogDecay j 2 U (oldLogTensor e m p φ ψ A i k) := by
  have hw : radialIndexWeight i k = 1 := by
    rcases hik with ⟨hi,hk⟩ | ⟨hi,hk⟩ <;> simp [radialIndexWeight,hi,hk]
  have h := weighted_source_remainder_lorentz_decay e m p φ ψ j 3 1 hd.compact hd.chart
      hd.region hd.chartInv hd.newRegion hd.oldRegion (hA.mixed i k hik)
  change FiniteLogDecay j 2 U (fun x => radiusPower (radialIndexWeight i k)
    (logLorentzChart e m p φ ψ x) * A i k (logRadiusChart (logLorentzChart e m p φ ψ x)))
  convert h using 1 <;> norm_num [hw]

lemma lorentz_compact_radial_leading_regular (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {mr : Angle → ℝ}
    (hr : ∀ z ∈ K, ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    ∀ z ∈ K, ContDiffAt ℝ ∞ (compactLeadingCoefficient e m p φ ψ 3 mr) z := by
  intro z hz
  exact compactLeadingCoefficient_regular e m p φ ψ 3 (hd.chart z hz)
    (hd.region z hz) (hd.chartInv z hz) (hr z hz)

lemma lorentz_compact_angular_leading_regular (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {mg : I → I → Angle → ℝ}
    (hg : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    ∀ i k, i≠0 → k≠0 → ∀ z ∈ K,
      ContDiffAt ℝ ∞ (compactAngularCoefficient e m p φ ψ mg i k) z := by
  intro i k hi hk z hz
  exact compactLeadingCoefficient_regular e m p φ ψ 1 (hd.chart z hz)
    (hd.region z hz) (hd.chartInv z hz) (hg i k hi hk z hz)

lemma oldLogTensor_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) (hq : 5 ≤ qrad) {K U V : Set Point}
    (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg)
    (hr : ∀ z ∈ K, ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ z)))
    (hg : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    ∀ i k, FiniteLogDecay j (logTensorRate i k) U (oldLogTensor e m p φ ψ A i k) := by
  intro i k
  by_cases hi : i=0 <;> by_cases hk : k=0
  · subst i; subst k
    have he : FiniteLogDecay j 3 U (fun x => oldLogTensor e m p φ ψ A 0 0 x -
        radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr (inverseLogRadiusChart x)) :=
      (oldLogTensor_radial_remainder e m p φ ψ j qrad hd hA).weaken
        (by exact_mod_cast (show (3:ℤ) ≤ (qrad:ℤ)-2 by omega)) hd.largeRadius
    have hl := (FiniteLogDecay.weighted_compactified j 3 hd.compact
      (lorentz_compact_radial_leading_regular e m p φ ψ hd hr)).mono hd.newRegion
    simpa only [logTensorRate,ite_true,sub_add_cancel] using he.add hl
  · simpa only [logTensorRate,hi,hk,ite_true,ite_false] using
      oldLogTensor_mixed_decay e m p φ ψ j qrad hd hA i k (Or.inl ⟨hi,hk⟩)
  · simpa only [logTensorRate,hi,hk,ite_true,ite_false] using
      oldLogTensor_mixed_decay e m p φ ψ j qrad hd hA i k (Or.inr ⟨hi,hk⟩)
  · have he := (oldLogTensor_angular_remainder e m p φ ψ j qrad hd hA i k hi hk).weaken
        (by norm_num : (1:ℝ) ≤ 2) hd.largeRadius
    have hl := (FiniteLogDecay.weighted_compactified j 1 hd.compact
      (lorentz_compact_angular_leading_regular e m p φ ψ hd hg i k hi hk)).mono hd.newRegion
    simpa only [logTensorRate,hi,hk,ite_false,sub_add_cancel] using he.add hl

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma lorentz_jacobian_sharp_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V) :
    ∀ a i, FiniteLogDecay j (logJacRate a i) U
      (fun x => lorentzLogJac e m p φ ψ a i (inverseLogRadiusChart x)) := by
  obtain ⟨h0,h2⟩ := lorentz_jacobian_decay e m p φ ψ j hd.compact hd.chart hd.region hd.chartInv
  intro a i
  by_cases h : a=0 ∧ i≠0
  · rcases h with ⟨rfl,hi⟩
    simpa only [logJacRate,hi,ne_eq,not_false_eq_true,true_and,ite_true,ite_false,sub_zero] using
      (h2 i).mono hd.newRegion
  · simpa only [logJacRate,h,ite_false] using (h0 a i).mono hd.newRegion

theorem lorentz_CKS_finite_components (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) (hq : 5 ≤ qrad) {K U V : Set Point}
    (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg)
    (hr : ∀ z ∈ K, ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ z)))
    (hg : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    (∀ a b, FiniteLogDecay j (logTensorRate a b) U (lorentzLogTensor e m p φ ψ A a b)) ∧
    (∀ a b, FiniteLogDecay j 2 U (fun x => lorentzLogTensor e m p φ ψ A a b x -
      radiusPower (-1) x * transformedAngularLeading (lorentzLogJac e m p φ ψ)
        (compactAngularCoefficient e m p φ ψ mg) a b (boundaryProjection (inverseLogRadiusChart x)))) ∧
    (6 ≤ qrad → FiniteLogDecay j 4 U (fun x => lorentzLogTensor e m p φ ψ A 0 0 x -
      radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr
        (boundaryProjection (inverseLogRadiusChart x)))) := by
  have hT := oldLogTensor_decay e m p φ ψ j qrad hq hd hA hr hg
  have hJ := lorentz_jacobian_sharp_decay e m p φ ψ j hd
  refine ⟨finite_log_tensor_pullback_rates j hd.largeRadius hJ hT,?_,?_⟩
  · exact finite_log_tensor_angular_leading j hd.compact hd.segment hd.newRegion hd.largeRadius
      (fun a i z hz => lorentzLogJac_contDiffAt e m p φ ψ (hd.chart z hz)
        (hd.region z hz) (hd.chartInv z hz) a i)
      (lorentz_compact_angular_leading_regular e m p φ ψ hd hg) hT
      (oldLogTensor_angular_remainder e m p φ ψ j qrad hd hA)
  · intro hq6
    have hδ : FiniteLogDecay j 2 U
        (fun x => lorentzLogJac e m p φ ψ 0 0 (inverseLogRadiusChart x)-1) := by
      simpa only [ite_true] using ((lorentz_jacobian_decay e m p φ ψ j
        hd.compact hd.chart hd.region hd.chartInv).2 0).mono hd.newRegion
    have he : FiniteLogDecay j 4 U (fun x => oldLogTensor e m p φ ψ A 0 0 x -
        radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr (inverseLogRadiusChart x)) :=
      (oldLogTensor_radial_remainder e m p φ ψ j qrad hd hA).weaken
        (by exact_mod_cast (show (4:ℤ) ≤ (qrad:ℤ)-2 by omega)) hd.largeRadius
    exact finite_log_tensor_radial_leading j hd.compact hd.segment hd.newRegion hd.largeRadius
      (lorentz_compact_radial_leading_regular e m p φ ψ hd hr) (hJ 0) hδ hT he

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus CKSAngularSlice
open scoped ContDiff Topology

lemma logRadiusChart_radialLogChart {y : Point} (hy : 0 < y 0) :
    logRadiusChart (radialLogChart y) = y := by
  ext i
  by_cases hi : i=0 <;> simp [radialLogChart,logRadiusChart,hi,Real.exp_log hy]

lemma radialLogChart_contDiffAt {y : Point} (hy : 0 < y 0) :
    ContDiffAt ℝ ∞ radialLogChart y := by
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i=0
  · simp only [radialLogChart,hi,ite_true]
    exact (show ContDiffAt ℝ ∞ (fun z : Point => z 0) y by fun_prop).log (ne_of_gt hy)
  · simp only [radialLogChart,hi,ite_false]
    fun_prop

theorem FiniteLogDecay.to_source {j q : ℕ} {U : Set Point} {f : Point → ℝ}
    (hf : FiniteLogDecay j q U f) :
    SourceRemainderOn j q (logRadiusChart '' U) (fun y => f (radialLogChart y)) := by
  have hr (x : Point) (hx : x ∈ U) : ContDiffAt ℝ j
      (fun y => f (radialLogChart y)) (logRadiusChart x) := by
    have hl := (radialLogChart_contDiffAt (show 0 < (logRadiusChart x) 0 by
      simpa only [logRadiusChart,ite_true] using Real.exp_pos (x 0))).of_le
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    have hfx : ContDiffAt ℝ j f (radialLogChart (logRadiusChart x)) := by
      simpa only [radialLogChart_logRadiusChart] using hf.regular x hx
    exact hfx.comp _ hl
  refine ⟨?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact hr x hx
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨C,hC,?_⟩
  rintro y ⟨x,hx,rfl⟩ l hl
  have he := coordinateIter_pullback l ((hr x hx).of_le (by exact_mod_cast hl))
  have hi : (fun z => f (radialLogChart (logRadiusChart z))) = f := by
    funext z
    rw [radialLogChart_logRadiusChart]
  rw [hi] at he
  rw [← he]
  calc |coordinateIter l f x| ≤ ‖iteratedFDeriv ℝ l.length f x‖ :=
        coordinateIter_le_iteratedFDeriv l ((hf.regular x hx).of_le (by exact_mod_cast hl))
    _ ≤ C*CKSMixedGeometry.radiusPower (-(q:ℝ)) x := hb x hx _ hl
    _ = C/(logRadiusChart x 0)^q := by rw [radiusPower_neg_nat]; simp [logRadiusChart,div_eq_mul_inv]

theorem FiniteLogDecay.source_of_log {j q : ℕ} {U : Set Point} {g : Point → ℝ}
    (hf : FiniteLogDecay j q U (fun x => g (logRadiusChart x))) :
    SourceRemainderOn j q (logRadiusChart '' U) g := by
  have hr (x : Point) (hx : x ∈ U) : ContDiffAt ℝ j g (logRadiusChart x) := by
    have h := hf.to_source.regular (logRadiusChart x) ⟨x,hx,rfl⟩
    have he : g =ᶠ[𝓝 (logRadiusChart x)]
        (fun y => g (logRadiusChart (radialLogChart y))) := by
      have hp : ∀ᶠ y in 𝓝 (logRadiusChart x), 0 < y 0 :=
        (isOpen_lt continuous_const (continuous_apply (0:I))).mem_nhds
          (by change 0 < (logRadiusChart x) 0
              simpa only [logRadiusChart,ite_true] using Real.exp_pos (x 0))
      filter_upwards [hp] with y hy
      rw [logRadiusChart_radialLogChart hy]
    exact h.congr_of_eventuallyEq he
  refine ⟨?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact hr x hx
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨C,hC,?_⟩
  rintro y ⟨x,hx,rfl⟩ l hl
  rw [← coordinateIter_pullback l ((hr x hx).of_le (by exact_mod_cast hl))]
  calc _ ≤ ‖iteratedFDeriv ℝ l.length (fun z => g (logRadiusChart z)) x‖ :=
        coordinateIter_le_iteratedFDeriv l ((hf.regular x hx).of_le (by exact_mod_cast hl))
    _ ≤ C*CKSMixedGeometry.radiusPower (-(q:ℝ)) x := hb x hx _ hl
    _ = C/(logRadiusChart x 0)^q := by rw [radiusPower_neg_nat]; simp [logRadiusChart,div_eq_mul_inv]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma boundary_inverseLogRadiusChart (x : Point) :
    boundaryProjection (inverseLogRadiusChart x) = slice 0 (angularProjection x) := by
  ext i
  fin_cases i <;> simp [boundaryProjection,inverseLogRadiusChart,angularProjection,slice,injection,basis] <;> rfl

lemma ordinaryLeadingComponent_log (q : ℕ) (M : Angle → ℝ) (x : Point) :
    ordinaryLeadingComponent q M (logRadiusChart x) =
      radiusPower (-(q:ℝ)) x * M (angularProjection x) := by
  simp [ordinaryLeadingComponent,logRadiusChart,angularProjection_logRadiusChart,radiusPower_neg_nat]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma lorentzOrdinaryTensor_mixed (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {U : Set Point} {A : I → I → Point → ℝ}
    (hT : ∀ a b, FiniteLogDecay j (logTensorRate a b) U (lorentzLogTensor e m p φ ψ A a b))
    (a b : I) (hab : (a=0 ∧ b≠0) ∨ (a≠0 ∧ b=0)) :
    SourceRemainderOn j 3 (logRadiusChart '' U) (lorentzOrdinaryTensor e m p φ ψ A a b) := by
  have hw : radialIndexWeight a b = 1 := by
    rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [radialIndexWeight,ha,hb]
  have hrate : logTensorRate a b = 2 := by
    rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [logTensorRate,ha,hb]
  have h := (FiniteLogDecay.radiusPower j 1 U).mul (hT a b)
  have hh : FiniteLogDecay j (3:ℕ) U
      (fun x => lorentzOrdinaryTensor e m p φ ψ A a b (logRadiusChart x)) := by
    simpa only [lorentzOrdinaryTensor_log,hw,hrate,show (1:ℝ)+2=3 by norm_num,Nat.cast_ofNat] using h
  exact hh.source_of_log

lemma lorentzOrdinaryTensor_radial_rough (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {U : Set Point} {A : I → I → Point → ℝ}
    (hT : FiniteLogDecay j 3 U (lorentzLogTensor e m p φ ψ A 0 0)) :
    SourceRemainderOn j 5 (logRadiusChart '' U) (lorentzOrdinaryTensor e m p φ ψ A 0 0) := by
  have h := (FiniteLogDecay.radiusPower j 2 U).mul hT
  have hh : FiniteLogDecay j (5:ℕ) U
      (fun x => lorentzOrdinaryTensor e m p φ ψ A 0 0 (logRadiusChart x)) := by
    convert h using 1 <;> norm_num [lorentzOrdinaryTensor_log,radialIndexWeight]
  exact hh.source_of_log

lemma lorentzOrdinaryTensor_radial_sharp (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {U : Set Point} {A : I → I → Point → ℝ} {mr : Angle → ℝ}
    (hT : FiniteLogDecay j 4 U (fun x => lorentzLogTensor e m p φ ψ A 0 0 x -
      radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr
        (boundaryProjection (inverseLogRadiusChart x)))) :
    SourceRemainderOn j 6 (logRadiusChart '' U) (fun y => lorentzOrdinaryTensor e m p φ ψ A 0 0 y -
      ordinaryLeadingComponent 5 (lorentzRadialLeading e m p φ ψ mr) y) := by
  have h : FiniteLogDecay j 6 U (fun x => radiusPower (-2) x *
      (lorentzLogTensor e m p φ ψ A 0 0 x - radiusPower (-3) x *
        compactLeadingCoefficient e m p φ ψ 3 mr (boundaryProjection (inverseLogRadiusChart x)))) := by
    simpa only [show (2:ℝ)+4=6 by norm_num] using (FiniteLogDecay.radiusPower j 2 U).mul hT
  have hh : FiniteLogDecay j (6:ℕ) U (fun x => lorentzOrdinaryTensor e m p φ ψ A 0 0 (logRadiusChart x) -
      ordinaryLeadingComponent 5 (lorentzRadialLeading e m p φ ψ mr) (logRadiusChart x)) := by
    apply h.congr
    funext x
    rw [lorentzOrdinaryTensor_log,ordinaryLeadingComponent_log]
    norm_num only [radialIndexWeight,ite_true]
    simp only [lorentzRadialLeading,boundary_inverseLogRadiusChart,mul_sub,← mul_assoc,← radiusPower_add]
    norm_num
  exact hh.source_of_log

lemma lorentzOrdinaryTensor_angular_sharp (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {U : Set Point} {A : I → I → Point → ℝ} {mg : I → I → Angle → ℝ}
    (hT : ∀ a b, FiniteLogDecay j 2 U (fun x => lorentzLogTensor e m p φ ψ A a b x -
      radiusPower (-1) x * transformedAngularLeading (lorentzLogJac e m p φ ψ)
        (compactAngularCoefficient e m p φ ψ mg) a b (boundaryProjection (inverseLogRadiusChart x))))
    (a b : I) (ha : a≠0) (hb : b≠0) :
    SourceRemainderOn j 2 (logRadiusChart '' U) (fun y => lorentzOrdinaryTensor e m p φ ψ A a b y -
      ordinaryLeadingComponent 1 (lorentzAngularLeading e m p φ ψ mg a b) y) := by
  have hh : FiniteLogDecay j (2:ℕ) U (fun x => lorentzOrdinaryTensor e m p φ ψ A a b (logRadiusChart x) -
      ordinaryLeadingComponent 1 (lorentzAngularLeading e m p φ ψ mg a b) (logRadiusChart x)) := by
    convert hT a b using 1
    · norm_num
    funext x
    simp [lorentzOrdinaryTensor_log,ordinaryLeadingComponent_log,lorentzAngularLeading,
      radialIndexWeight,ha,hb,radiusPower,boundary_inverseLogRadiusChart]
  exact hh.source_of_log

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem lorentz_metric_CKS (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents 3 6 V A mr mg)
    (hr : ∀ z ∈ K, ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ z)))
    (hg : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    SourceCKSComponents 3 6 (logRadiusChart '' U) (lorentzOrdinaryTensor e m p φ ψ A)
      (lorentzRadialLeading e m p φ ψ mr) (lorentzAngularLeading e m p φ ψ mg) := by
  obtain ⟨hT,hg',hr'⟩ := lorentz_CKS_finite_components e m p φ ψ 3 6 (by norm_num) hd hA hr hg
  exact ⟨lorentzOrdinaryTensor_radial_sharp e m p φ ψ 3 (hr' le_rfl),
    lorentzOrdinaryTensor_mixed e m p φ ψ 3 hT,
    lorentzOrdinaryTensor_angular_sharp e m p φ ψ 3 hg'⟩

theorem lorentz_second_CKS (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {B : I → I → Point → ℝ} {mK : I → I → Angle → ℝ}
    (hB : SourceCKSComponents 2 5 V B (fun _ => 0) mK)
    (hK : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mK i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    SourceCKSComponents 2 5 (logRadiusChart '' U) (lorentzOrdinaryTensor e m p φ ψ B)
      (fun _ => 0) (lorentzAngularLeading e m p φ ψ mK) := by
  obtain ⟨hT,hg',_⟩ := lorentz_CKS_finite_components e m p φ ψ 2 5 (by norm_num) hd hB
    (fun z hz => contDiffAt_const) hK
  refine ⟨?_,lorentzOrdinaryTensor_mixed e m p φ ψ 2 hT,
    lorentzOrdinaryTensor_angular_sharp e m p φ ψ 2 hg'⟩
  have hr : FiniteLogDecay 2 3 U (lorentzLogTensor e m p φ ψ B 0 0) := by
    simpa only [logTensorRate,ite_true] using hT 0 0
  simpa only [ordinaryLeadingComponent,mul_zero,sub_zero] using
    lorentzOrdinaryTensor_radial_rough e m p φ ψ 2 hr

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice

def ordinaryConjugate (F : Point → Point) (y : Point) : Point :=
  logRadiusChart (F (radialLogChart y))

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma chartDerivative_apply (x v : Point) (i : I) :
    chartDerivative x v i = radialFactor i (logRadiusChart x) * v i := by
  by_cases hi : i=0 <;> simp [chartDerivative,radialFactor,logRadiusChart,hi]

lemma D_logRadius_comp {F : Point → Point} {x : Point}
    (hF : DifferentiableAt ℝ F x) (a i : I) :
    D (basis a) (fun z => logRadiusChart (F z) i) x =
      radialFactor i (logRadiusChart (F x)) * D (basis a) (fun z => F z i) x := by
  have hL := ((ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt.comp (F x)
    (logRadiusChart_hasFDerivAt (F x))).comp x hF.hasFDerivAt
  have hFi := ((ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt)
  change HasFDerivAt (fun z => logRadiusChart (F z) i) _ x at hL
  change HasFDerivAt (fun z => F z i) _ x at hFi
  unfold D
  rw [hL.fderiv,hFi.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,chartDerivative_apply]

lemma ordinaryConjugate_differentiableAt {F : Point → Point} {x : Point}
    (hF : DifferentiableAt ℝ F x) :
    DifferentiableAt ℝ (ordinaryConjugate F) (logRadiusChart x) := by
  have hl := (radialLogChart_contDiffAt (show 0 < (logRadiusChart x) 0 by
    simpa only [logRadiusChart,ite_true] using Real.exp_pos (x 0))).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ F (radialLogChart (logRadiusChart x)) := by simpa using hF
  exact logRadiusChart_smooth.differentiable (by simp) |>.differentiableAt.comp _ (hf.comp _ hl)

lemma radialFactor_pos (a : I) (x : Point) : 0 < radialFactor a (logRadiusChart x) := by
  by_cases ha : a=0 <;> simp [radialFactor,logRadiusChart,ha,Real.exp_pos]

lemma D_ordinaryConjugate {F : Point → Point} {x : Point}
    (hF : DifferentiableAt ℝ F x) (a i : I) :
    D (basis a) (fun y => ordinaryConjugate F y i) (logRadiusChart x) =
      (radialFactor a (logRadiusChart x))⁻¹ *
        radialFactor i (logRadiusChart (F x)) * D (basis a) (fun z => F z i) x := by
  have hdi : DifferentiableAt ℝ (fun y => ordinaryConjugate F y i) (logRadiusChart x) := by
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).differentiableAt.comp _
      (ordinaryConjugate_differentiableAt hF)
  have he := D_pullback a hdi
  have heq : (fun z => ordinaryConjugate F (logRadiusChart z) i) =
      (fun z => logRadiusChart (F z) i) := by
    funext z
    simp only [ordinaryConjugate,radialLogChart_logRadiusChart]
  rw [heq,D_logRadius_comp hF] at he
  unfold scaledD at he
  have hne := (radialFactor_pos a x).ne'
  calc
    _ = (radialFactor a (logRadiusChart x))⁻¹ *
        (radialFactor a (logRadiusChart x) *
          D (basis a) (fun y => ordinaryConjugate F y i) (logRadiusChart x)) := by
            rw [←mul_assoc,inv_mul_cancel₀ hne,one_mul]
    _ = _ := by rw [←he]; ring

lemma radialFactor_pair (a b : I) (x : Point) :
    radialFactor a (logRadiusChart x) * radialFactor b (logRadiusChart x) =
      radiusPower (radialIndexWeight a b) x := by
  simp only [radialIndexWeight,radiusPower,add_mul,Real.exp_add]
  congr 1 <;> split_ifs <;> simp_all [radialFactor,logRadiusChart]

lemma radialFactor_inv_pair (a b : I) (x : Point) :
    (radialFactor a (logRadiusChart x))⁻¹ * (radialFactor b (logRadiusChart x))⁻¹ =
      radiusPower (-radialIndexWeight a b) x := by
  rw [←mul_inv,radialFactor_pair]
  simp only [radiusPower,neg_mul,Real.exp_neg]

theorem coordinateTensorPullback_log {F : Point → Point} {x : Point}
    (hF : DifferentiableAt ℝ F x) (A : I → I → Point → ℝ) (a b : I) :
    coordinateTensorPullback (ordinaryConjugate F) A a b (logRadiusChart x) =
      radiusPower (-radialIndexWeight a b) x *
        ∑ i, ∑ k, D (basis a) (fun z => F z i) x * D (basis b) (fun z => F z k) x *
          (radiusPower (radialIndexWeight i k) (F x) * A i k (logRadiusChart (F x))) := by
  simp only [coordinateTensorPullback]
  simp_rw [D_ordinaryConjugate hF]
  simp only [ordinaryConjugate,radialLogChart_logRadiusChart,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [←radialFactor_inv_pair,←radialFactor_pair]
  ring

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma coordinateTensorPullback_congr {F G : Point → Point} {y : Point}
    (hFG : F =ᶠ[𝓝 y] G) (A : I → I → Point → ℝ) (a b : I) :
    coordinateTensorPullback F A a b y = coordinateTensorPullback G A a b y := by
  have he (i : I) : (fun z => F z i) =ᶠ[𝓝 y] (fun z => G z i) :=
    hFG.mono (fun z hz => congrFun hz i)
  simp only [coordinateTensorPullback,D,(he _).fderiv_eq,hFG.eq_of_nhds]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma lorentzPolarChart_germ (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {x : Point}
    (hn : ∀ᶠ θ in 𝓝 (angularProjection x), φ θ ∈ Metric.sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p) :
    lorentzPolarChart e m p φ ψ =ᶠ[𝓝 (logRadiusChart x)]
      ordinaryConjugate (logLorentzChart e m p φ ψ) := by
  have hnr : ∀ᶠ z in 𝓝 x, φ (angularProjection z) ∈ Metric.sphere (0 : E) 1 :=
    angularProjection.continuous.continuousAt.eventually hn
  have hscale : ContinuousAt (fun z => compactScale e m p (compactPolar φ (inverseLogRadiusChart z))) x :=
    ((compactScale_smooth_region e m p hz).continuousAt.comp
      (compactPolar_contDiffAt hφ).continuousAt).comp inverseLogRadiusChart_smooth.continuous.continuousAt
  have hpos : ∀ᶠ z in 𝓝 x, 0 < compactScale e m p (compactPolar φ (inverseLogRadiusChart z)) :=
    hscale.eventually (Ioi_mem_nhds hz.2)
  have he : (fun z => lorentzPolarChart e m p φ ψ (logRadiusChart z)) =ᶠ[𝓝 x]
      (fun z => logRadiusChart (logLorentzChart e m p φ ψ z)) := by
    filter_upwards [hnr,hpos] with z hzn hzp
    exact lorentzPolarChart_logRadiusChart e m p φ ψ hzn hzp
  have hr : 0 < (logRadiusChart x) 0 := by
    simpa only [logRadiusChart,ite_true] using Real.exp_pos (x 0)
  have hlc : Tendsto radialLogChart (𝓝 (logRadiusChart x)) (𝓝 x) := by
    simpa only [ContinuousAt,radialLogChart_logRadiusChart] using (radialLogChart_contDiffAt hr).continuousAt
  have hy : ∀ᶠ y in 𝓝 (logRadiusChart x), 0 < y 0 :=
    (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).continuous.continuousAt.eventually
      (Ioi_mem_nhds hr)
  filter_upwards [he.comp_tendsto hlc,hy] with y hey hry
  simpa only [Function.comp_def,logRadiusChart_radialLogChart hry,ordinaryConjugate] using hey

theorem lorentzOrdinaryTensor_eq_pullback (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {x : Point}
    (hn : ∀ᶠ θ in 𝓝 (angularProjection x), φ θ ∈ Metric.sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x))))
    (A : I → I → Point → ℝ) (a b : I) :
    lorentzOrdinaryTensor e m p φ ψ A a b (logRadiusChart x) =
      coordinateTensorPullback (lorentzPolarChart e m p φ ψ) A a b (logRadiusChart x) := by
  rw [coordinateTensorPullback_congr (lorentzPolarChart_germ e m p φ ψ hn hφ hz),
    coordinateTensorPullback_log
      ((logLorentzChart_contDiffAt e m p φ ψ hφ hz hψ).differentiableAt (by simp)),
    lorentzOrdinaryTensor_log]
  simp only [D_logLorentzChart e m p φ ψ hφ hz hψ,lorentzLogTensor,logCovariantPullback,
    oldLogTensor]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

def boundaryChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) (θ : Angle) : Angle :=
  ψ (boundaryAmbient e m p (φ θ))

def angularCoordinatePullback (Φ : Angle → Angle) (mg : I → I → Angle → ℝ)
    (a b : Fin 2) (θ : Angle) : ℝ :=
  ∑ i : Fin 2, ∑ k : Fin 2,
    D (CKSAngularGeometry.basis a) (fun η => Φ η i) θ *
    D (CKSAngularGeometry.basis b) (fun η => Φ η k) θ * mg i.succ k.succ (Φ θ)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularProjection_slice (r : ℝ) (θ : Angle) : angularProjection (slice r θ)=θ := by
  ext a
  exact slice_succ r θ a

lemma compactPolar_slice (r : ℝ) (θ : Angle) (φ : Angle → E) :
    compactPolar φ (slice r θ) = (r,φ θ) := by
  simp [compactPolar,angularProjection_slice]

lemma compactScale_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) :
    compactScale e m p (0,n) = denominator e m p n := by
  change ‖compactSpatial e m p (0,n)‖ = _
  rw [compactSpatial_zero]
  exact boundarySpatial_norm he hm0 hm ⟨n,hn⟩

lemma compactAngle_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) :
    compactAngle e m p (0,n) = boundaryAmbient e m p n := by
  simp only [compactAngle,compactScale_boundary he hm0 hm hn,compactSpatial_zero,boundaryAmbient]

lemma compactRegion_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) : (0,n) ∈ compactRegion e m p := by
  refine ⟨denominator_pos he hm0 ⟨n,hn⟩,?_⟩
  rw [compactScale_boundary he hm0 hm hn]
  exact denominator_pos he hm0 ⟨n,hn⟩

lemma compactLorentzCoefficients_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    compactLorentzCoefficients e m p φ ψ (slice 0 θ) =
      slice (Real.log (denominator e m p (φ θ))) (boundaryChart e m p φ ψ θ) := by
  simp only [compactLorentzCoefficients,compactPolar_slice,compactScale_boundary he hm0 hm hn,
    compactAngle_boundary he hm0 hm hn,boundaryChart]

lemma compactLeadingCoefficient_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (q : ℕ) (M : Angle → ℝ) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    compactLeadingCoefficient e m p φ ψ q M (slice 0 θ) =
      (denominator e m p (φ θ))⁻¹^q * M (boundaryChart e m p φ ψ θ) := by
  simp only [compactLeadingCoefficient,compactLorentzCoefficients_boundary he hm0 hm φ ψ hn,
    slice_zero,angularProjection_slice,neg_mul,Real.exp_neg,Real.exp_nat_mul,
    Real.exp_log (denominator_pos he hm0 ⟨φ θ,hn⟩),inv_pow]

theorem lorentzRadialLeading_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (mr : Angle → ℝ) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    lorentzRadialLeading e m p φ ψ mr θ =
      (denominator e m p (φ θ))⁻¹^3 * mr (boundaryChart e m p φ ψ θ) :=
  compactLeadingCoefficient_boundary he hm0 hm φ ψ 3 mr hn

lemma lorentzLogJac_boundary_angular {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    (hn : ∀ᶠ η in 𝓝 θ, φ η ∈ Metric.sphere (0:E) 1)
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hψ : ContDiffAt ℝ ∞ ψ (boundaryAmbient e m p (φ θ))) (a i : Fin 2) :
    lorentzLogJac e m p φ ψ a.succ i.succ (slice 0 θ) =
      D (CKSAngularGeometry.basis a) (fun η => boundaryChart e m p φ ψ η i) θ := by
  have hn0 := hn.self_of_nhds
  have hc : ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) (slice 0 θ) := by
    apply compactLorentzCoefficients_contDiffAt e m p φ ψ
    · simpa only [angularProjection_slice] using hφ
    · simpa only [compactPolar_slice] using compactRegion_boundary he hm0 hm hn0
    · simpa only [compactPolar_slice,compactAngle_boundary he hm0 hm hn0] using hψ
  have hci := ((contDiffAt_pi.mp hc) i.succ).differentiableAt (by simp)
  simp only [lorentzLogJac,Fin.succ_ne_zero,false_and,ite_false,zero_add,
    backwardScaledD,backwardFactor,one_mul]
  rw [←D_slice a 0 hci]
  apply D_congr
  filter_upwards [hn] with η hη
  simp only [compactLorentzCoefficients_boundary he hm0 hm φ ψ hη,slice_succ]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

theorem lorentzAngularLeading_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (mg : I → I → Angle → ℝ) {θ : Angle}
    (hn : ∀ᶠ η in 𝓝 θ, φ η ∈ Metric.sphere (0:E) 1)
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hψ : ContDiffAt ℝ ∞ ψ (boundaryAmbient e m p (φ θ))) (a b : Fin 2) :
    lorentzAngularLeading e m p φ ψ mg a.succ b.succ θ =
      (denominator e m p (φ θ))⁻¹ *
        angularCoordinatePullback (boundaryChart e m p φ ψ) mg a b θ := by
  simp only [lorentzAngularLeading,transformedAngularLeading,Fin.sum_univ_succ,
    angularLeadingEntry,ne_eq,not_true_eq_false,false_and,and_false,ite_false,
    mul_zero,Finset.sum_const_zero,zero_add,Fin.succ_ne_zero,not_false_eq_true,
    and_self,ite_true,compactAngularCoefficient]
  simp_rw [lorentzLogJac_boundary_angular he hm0 hm φ ψ hn hφ hψ]
  have hc (M : Angle → ℝ) :
      compactLeadingCoefficient e m p φ ψ 1 M (slice 0 θ) =
        (denominator e m p (φ θ))⁻¹ * M (boundaryChart e m p φ ψ θ) := by
    simpa only [Nat.cast_one,pow_one] using
      compactLeadingCoefficient_boundary he hm0 hm φ ψ 1 M hn.self_of_nhds
  simp_rw [hc]
  simp only [angularCoordinatePullback,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  ring

lemma lorentzRadialLeading_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {mr : Angle → ℝ} {θ : Angle}
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hz : compactPolar φ (slice 0 θ) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (slice 0 θ))))
    (hr : ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ (slice 0 θ)))) :
    ContDiffAt ℝ ∞ (lorentzRadialLeading e m p φ ψ mr) θ := by
  have hp : ContDiffAt ℝ ∞ φ (angularProjection (slice 0 θ)) := by
    simpa only [angularProjection_slice] using hφ
  exact (compactLeadingCoefficient_regular e m p φ ψ 3 hp hz hψ hr).comp θ
    (slice_smooth 0).contDiffAt

lemma lorentzAngularLeading_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {mg : I → I → Angle → ℝ} {θ : Angle}
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hz : compactPolar φ (slice 0 θ) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (slice 0 θ))))
    (hg : ∀ i k, i≠0 → k≠0 → ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ (slice 0 θ)))) (a b : I) :
    ContDiffAt ℝ ∞ (lorentzAngularLeading e m p φ ψ mg a b) θ := by
  have hp : ContDiffAt ℝ ∞ φ (angularProjection (slice 0 θ)) := by
    simpa only [angularProjection_slice] using hφ
  have hJ i k := lorentzLogJac_contDiffAt e m p φ ψ hp hz hψ i k
  have hC (i k : I) : ContDiffAt ℝ ∞
      (fun z => angularLeadingEntry (compactAngularCoefficient e m p φ ψ mg) i k z) (slice 0 θ) := by
    simp only [angularLeadingEntry]
    split_ifs with hik
    · exact compactLeadingCoefficient_regular e m p φ ψ 1 hp hz hψ (hg i k hik.1 hik.2)
    · exact contDiffAt_const
  have ht : ContDiffAt ℝ ∞
      (transformedAngularLeading (lorentzLogJac e m p φ ψ)
        (compactAngularCoefficient e m p φ ψ mg) a b) (slice 0 θ) := by
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro k hk
    exact ((hJ a i).mul (hJ b k)).mul (hC i k)
  exact ht.comp θ (slice_smooth 0).contDiffAt

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def angularLogTail (L : ℝ) (θ : Angle) (δ : ℝ) : Set Point :=
  {x | L ≤ x 0 ∧ angularProjection x ∈ Metric.ball θ δ}

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma boundaryProjection_closedBall {θ : Angle} {δ : ℝ} (hδ : 0 ≤ δ)
    {z : Point} (hz : z ∈ Metric.closedBall (slice 0 θ) δ) :
    boundaryProjection z ∈ Metric.closedBall (slice 0 θ) δ := by
  apply (dist_pi_le_iff hδ).2
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [boundaryProjection_zero,slice_zero,dist_self]
    exact hδ
  · have hi := (dist_pi_le_iff hδ).1 hz a.succ
    simpa only [boundaryProjection,sub_apply,
      ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      basis,Pi.single_apply,Fin.succ_ne_zero,ite_false,mul_zero,sub_zero] using hi

lemma inverseLogRadius_mem_closedBall {θ : Angle} {δ : ℝ} (hδ : 0 < δ)
    {x : Point} (hr : Real.exp (-x 0) ≤ δ)
    (ha : angularProjection x ∈ Metric.closedBall θ δ) :
    inverseLogRadiusChart x ∈ Metric.closedBall (slice 0 θ) δ := by
  apply (dist_pi_le_iff hδ.le).2
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [inverseLogRadiusChart,ite_true,slice_zero,Real.dist_eq,sub_zero,
      abs_of_pos (Real.exp_pos _)] using hr
  · have hi := (dist_pi_le_iff hδ.le).1 ha a
    simpa only [inverseLogRadiusChart,Fin.succ_ne_zero,ite_false,slice_succ,
      angularProjection,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply] using hi

lemma eventually_full_log_tail {δ d : ℝ} (hδ : 0 < δ) (hd : 0 < d) (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℝ, L ≤ t →
      Real.exp (-t) ≤ δ ∧ R < Real.exp t*d := by
  have hs : ∀ᶠ t : ℝ in atTop, Real.exp (-t) < δ :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hδ)
  have he : ∀ᶠ t : ℝ in atTop, R/d < Real.exp t :=
    Real.tendsto_exp_atTop.eventually (eventually_gt_atTop (R/d))
  obtain ⟨L,hL⟩ := eventually_atTop.1 ((eventually_ge_atTop (0:ℝ)).and (hs.and he))
  refine ⟨L,(hL L le_rfl).1,fun t ht => ?_⟩
  exact ⟨(hL t ht).2.1.le,(div_lt_iff₀ hd).mp (hL t ht).2.2⟩

end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology


attribute [local instance] stereoDimension

def stereoOrthogonalEquiv (v : Sphere) : (ℝ ∙ (v:E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr

def stereoAngularExtension (v : Sphere) (x : E) : Angle :=
  stereoAngleEquiv (stereoOrthogonalEquiv v (stereoToFun (v:E) x))

def stereoAmbientDomain (v : Sphere) : Set E :=
  letI := two_atLeastTwo
  letI : Inner ℝ E :=
    @InnerProductSpace.toInner ℝ E _
      (PiLp.seminormedAddCommGroup 2 (fun _ : Fin 3 => ℝ))
      (PiLp.innerProductSpace (fun _ : Fin 3 => ℝ))
  {x | inner ℝ (v:E) x ≠ 1}

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

attribute [local instance] stereoDimension

lemma stereoAngularChart_param (v : Sphere) (θ : Angle) :
    ((stereoAngularChart v).symm θ : E) = stereoInvFunAux (v:E)
      ((stereoOrthogonalEquiv v).symm (stereoAngleEquiv.symm θ) : E) := rfl

lemma stereoAngularChart_param_smooth (v : Sphere) :
    ContDiff ℝ ∞ (fun θ => ((stereoAngularChart v).symm θ : E)) := by
  simp_rw [stereoAngularChart_param]
  exact contDiff_stereoInvFunAux.comp
    ((ℝ ∙ (v:E))ᗮ.subtypeL.contDiff.comp
      ((stereoOrthogonalEquiv v).symm.toContinuousLinearEquiv.contDiff.comp
        stereoAngleEquiv.symm.contDiff))

lemma stereoAmbientDomain_open (v : Sphere) : IsOpen (stereoAmbientDomain v) :=
  isOpen_ne_fun (innerSL ℝ (v:E)).continuous continuous_const

lemma stereoAngularExtension_smooth (v : Sphere) :
    ContDiffOn ℝ ∞ (stereoAngularExtension v) (stereoAmbientDomain v) := by
  exact stereoAngleEquiv.contDiff.comp_contDiffOn
    ((stereoOrthogonalEquiv v).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      contDiffOn_stereoToFun)

lemma stereoAngularChart_source_domain (v n : Sphere)
    (hn : n ∈ (stereoAngularChart v).source) : (n:E) ∈ stereoAmbientDomain v := by
  change inner ℝ (v:E) (n:E) ≠ 1
  intro h
  have he : v=n := (sphere_ext_iff v n).mpr h
  simp [stereoAngularChart_source,he] at hn

lemma stereoAngularExtension_eq (v n : Sphere) :
    stereoAngularExtension v n=stereoAngularChart v n := rfl

def stereoSmoothPatch (v : Sphere) : SmoothAngularPatch where
  chart := stereoAngularChart v
  param_smooth := (stereoAngularChart_param_smooth v).contDiffOn
  extension := stereoAngularExtension v
  domain := stereoAmbientDomain v
  isOpen_domain := stereoAmbientDomain_open v
  extension_smooth := stereoAngularExtension_smooth v
  source_domain := stereoAngularChart_source_domain v
  extension_eq := fun n _ => stereoAngularExtension_eq v n

theorem exists_smoothAngularPatch (n : Sphere) :
    ∃ P : SmoothAngularPatch, n ∈ P.chart.source := by
  refine ⟨stereoSmoothPatch (-n),?_⟩
  change n ∈ (stereoAngularChart (-n)).source
  simpa only [stereoAngularChart_source,mem_compl_iff,mem_singleton_iff] using
    ne_neg_of_mem_unit_sphere ℝ n

namespace SmoothAngularPatch

lemma sphereRegion_open (P : SmoothAngularPatch) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (P.sphereRegion W) :=
  P.chart.isOpen_inter_preimage hW

lemma param_chart (P : SmoothAngularPatch) {n : Sphere} (hn : n ∈ P.chart.source) :
    P.param (P.chart n)=(n:E) := congrArg Subtype.val (P.chart.left_inv hn)

end SmoothAngularPatch
end
end CKSLorentz

end





noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularSlice Set
open scoped ContDiff Topology

lemma SourceRemainderOn.mono {j q : ℕ} {U V : Set Point} {f : Point → ℝ}
    (hf : SourceRemainderOn j q V f) (hUV : U ⊆ V) : SourceRemainderOn j q U f := by
  obtain ⟨B,hB,hb⟩ := hf.bound
  exact ⟨fun y hy => hf.regular y (hUV hy),B,hB,fun y hy => hb y (hUV hy)⟩

lemma slice_mem_closedBall {θ η : Angle} {δ : ℝ} (hδ : 0 ≤ δ)
    (hη : η ∈ Metric.closedBall θ δ) : slice 0 η ∈ Metric.closedBall (slice 0 θ) δ := by
  apply (dist_pi_le_iff hδ).2
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [slice_zero,dist_self] using hδ
  · simpa only [slice_succ] using (dist_pi_le_iff hδ).1 hη a

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma SourceCKSComponents.mono {j q : ℕ} {U V : Set Point}
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j q V A mr mg) (hUV : U ⊆ V) :
    SourceCKSComponents j q U A mr mg :=
  ⟨hA.radial.mono hUV,fun i k hik => (hA.mixed i k hik).mono hUV,
    fun i k hi hk => (hA.angular i k hi hk).mono hUV⟩

lemma angularRadialTail_subset_log (L : ℝ) (θ : Angle) (δ : ℝ) :
    angularRadialTail (Real.exp L) (Metric.ball θ δ) ⊆ logRadiusChart '' angularLogTail L θ δ := by
  intro y hy
  have hp : 0 < y 0 := (Real.exp_pos L).trans hy.1
  refine ⟨radialLogChart y,⟨?_,?_⟩,logRadiusChart_radialLogChart hp⟩
  · change L ≤ Real.log (y 0)
    exact ((Real.lt_log_iff_exp_lt hp).2 hy.1).le
  · simpa only [angularProjection_radialLogChart] using hy.2

lemma BoostPatchEstimates.mono_radius {e R₁ R₂ δ : ℝ} {p : E} {Q : CKSTensorPatch}
    {P : SmoothAngularPatch} {θ : Angle}
    (h : BoostPatchEstimates e p Q P θ δ R₁) (hR : R₁ ≤ R₂) :
    BoostPatchEstimates e p Q P θ δ R₂ := by
  have hs : angularRadialTail R₂ (Metric.ball θ δ) ⊆ angularRadialTail R₁ (Metric.ball θ δ) :=
    fun y hy => ⟨hR.trans_lt hy.1,hy.2⟩
  exact ⟨h.radius_pos.trans_le hR,h.ball_pos,h.ball_target,h.metric_CKS.mono hs,
    h.second_CKS.mono hs,h.radial_smooth,h.angular_smooth,h.second_smooth⟩

end
end CKSLorentz

end



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
def angularJacobian (Φ : Angle → Angle) (θ : Angle) : AngularMatrix := fun a i =>
  D (CKSAngularGeometry.basis a) (fun η => Φ η i) θ
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

lemma param_fderiv_leftInverse (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) :
    (fderiv ℝ P.extension (P.param θ)).comp (fderiv ℝ P.param θ) =
      ContinuousLinearMap.id ℝ Angle := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hψ := (P.extension_contDiffAt_param hθ).differentiableAt (by simp)
  have hg : (fun η => P.extension (P.param η)) =ᶠ[𝓝 θ] id := by
    filter_upwards [P.chart.open_target.mem_nhds hθ] with η hη
    exact P.extension_param hη
  have ht := hg.fderiv_eq (𝕜:=ℝ)
  change fderiv ℝ (P.extension ∘ P.param) θ = fderiv ℝ id θ at ht
  rw [fderiv_comp θ hψ hφ,fderiv_id] at ht
  exact ht

lemma param_fderiv_injective (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : Function.Injective (fderiv ℝ P.param θ) := by
  intro v w hvw
  have h := congrArg (fderiv ℝ P.extension (P.param θ)) hvw
  have hl := P.param_fderiv_leftInverse hθ
  have hv := congrArg (fun L : Angle →L[ℝ] Angle => L v) hl
  have hw := congrArg (fun L : Angle →L[ℝ] Angle => L w) hl
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
    hv.symm.trans (h.trans hw)

lemma param_tangent (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (v : Angle) : inner ℝ (P.param θ) (fderiv ℝ P.param θ v) = 0 := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hconst : (fun η => inner ℝ (P.param η) (P.param η)) = fun _ : Angle => (1:ℝ) := by
    funext η
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖P.param η‖=1 := P.param_norm η
    rw [hn,one_pow]
  have hd := fderiv_inner_apply (𝕜:=ℝ) hφ hφ v
  rw [hconst] at hd
  simp only [fderiv_fun_const] at hd
  change 0 = inner ℝ (P.param θ) (fderiv ℝ P.param θ v) +
    inner ℝ (fderiv ℝ P.param θ v) (P.param θ) at hd
  have hc := real_inner_comm (fderiv ℝ P.param θ v) (P.param θ)
  linarith

lemma roundMetric_posDef (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    (angularRoundMetric P.param θ).PosDef := by
  change (Matrix.gram ℝ (fun a => fderiv ℝ P.param θ (CKSAngularGeometry.basis a))).PosDef
  apply Matrix.posDef_gram_iff_linearIndependent.mpr
  have h := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map'
    (fderiv ℝ P.param θ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (P.param_fderiv_injective hθ))
  simpa only [Function.comp_def,Pi.basisFun_apply,CKSAngularGeometry.basis,
    ContinuousLinearMap.coe_coe] using h

end SmoothAngularPatch

lemma angular_vector_expansion (v : Angle) :
    ∑ a : Fin 2, v a • CKSAngularGeometry.basis a = v := by
  funext i
  fin_cases i <;> simp [CKSAngularGeometry.basis,Pi.single_apply]

lemma angularJacobian_apply {Φ : Angle → Angle} {θ : Angle}
    (hΦ : DifferentiableAt ℝ Φ θ) (a : Fin 2) :
    fderiv ℝ Φ θ (CKSAngularGeometry.basis a) =
      ∑ i : Fin 2, angularJacobian Φ θ a i • CKSAngularGeometry.basis i := by
  conv_lhs => rw [← angular_vector_expansion (fderiv ℝ Φ θ (CKSAngularGeometry.basis a))]
  congr 1; funext i
  congr 1
  simp only [angularJacobian,D,fderiv_apply hΦ,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped Topology ContDiff

lemma fderiv_coordinate_expansion {F : Point → Point} {y : Point}
    (hF : DifferentiableAt ℝ F y) (a : I) :
    fderiv ℝ F y (basis a) = ∑ i, D (basis a) (fun z => F z i) y • basis i := by
  conv_lhs => rw [← sum_coordinate_basis (fderiv ℝ F y (basis a))]
  congr 1; funext i
  congr 1
  simp only [D,fderiv_apply hF,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
lemma coordinateTensorPullback_polar {F : Point → Point} {y : Point}
    (hF : DifferentiableAt ℝ F y) (Q : SmoothAngularPatch) (A : SpatialTensor) (a b : I) :
    coordinateTensorPullback F (polarTensorComponents Q A) a b y =
      A (polarParam Q (F y))
        (fderiv ℝ (polarParam Q) (F y) (fderiv ℝ F y (basis a)))
        (fderiv ℝ (polarParam Q) (F y) (fderiv ℝ F y (basis b))) := by
  rw [fderiv_coordinate_expansion hF a,fderiv_coordinate_expansion hF b]
  simp only [map_sum,map_smul,_root_.sum_apply,smul_apply,
    smul_eq_mul,Finset.mul_sum,coordinateTensorPullback,polarTensorComponents]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma polarTensor_covariance {F : Point → Point} {H : E → E} {y : Point}
    (P Q : SmoothAngularPatch) (A : SpatialTensor)
    (hF : DifferentiableAt ℝ F y)
    (hP : DifferentiableAt ℝ (polarParam P) y)
    (hQ : DifferentiableAt ℝ (polarParam Q) (F y))
    (hH : DifferentiableAt ℝ H (polarParam P y))
    (he : (polarParam Q ∘ F) =ᶠ[𝓝 y] (H ∘ polarParam P)) (a b : I) :
    coordinateTensorPullback F (polarTensorComponents Q A) a b y =
      polarTensorComponents P (spatialTensorPullback H A) a b y := by
  have hp : polarParam Q (F y)=H (polarParam P y) := he.eq_of_nhds
  have hd := he.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp y hQ hF,fderiv_comp y hH hP] at hd
  have ha := congrArg (fun L : Point →L[ℝ] E => L (basis a)) hd
  have hb := congrArg (fun L : Point →L[ℝ] E => L (basis b)) hd
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  rw [coordinateTensorPullback_polar hF Q A a b,hp,ha,hb]
  rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open Set

lemma homeomorph_full_tail (H : E ≃ₜ E) (r : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : E, R < ‖x‖ → r < ‖H x‖ := by
  have hc : IsCompact (H ⁻¹' Metric.closedBall 0 r) :=
    H.isCompact_preimage.mpr (isCompact_closedBall 0 r)
  obtain ⟨C,hC⟩ := isBounded_iff_forall_norm_le.mp hc.isBounded
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  by_contra hn
  have hm : x ∈ H ⁻¹' Metric.closedBall 0 r := by
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using le_of_not_gt hn
  exact (not_le_of_gt hx) ((hC x hm).trans (le_max_right _ _))

theorem hyperbolic_boost_full_tails {e : ℝ} {p : E} (he : ‖p‖ < e) (r : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : E, R < ‖x‖ →
      r < ‖hyperbolicMap e (mass e p) p x‖ ∧
      r < ‖hyperbolicMap e (mass e p) (-p) x‖ := by
  obtain ⟨R₁,h₁,q₁⟩ := homeomorph_full_tail (hyperbolicHomeomorph e p he) r
  obtain ⟨R₂,h₂,q₂⟩ := homeomorph_full_tail (hyperbolicHomeomorph e p he).symm r
  refine ⟨max R₁ R₂,h₁.trans_le (le_max_left _ _),?_⟩
  intro x hx
  exact ⟨q₁ x (lt_of_le_of_lt (le_max_left _ _) hx),
    q₂ x (lt_of_le_of_lt (le_max_right _ _) hx)⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma angularRadialTail_open (R : ℝ) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (angularRadialTail R W) := by
  exact (isOpen_Ioi.preimage (continuous_apply 0)).inter
    (hW.preimage angularProjection.continuous)

lemma GenuineBoostPatch.spatial_nonzero {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ)) :
    hyperbolicMap e (mass e p) p (polarParam P y) ≠ 0 := by
  obtain ⟨n,_,hn⟩ := h.chart_image y hy
  intro hz
  change (n:E) = ‖hyperbolicMap e (mass e p) p (polarParam P y)‖⁻¹ •
    hyperbolicMap e (mass e p) p (polarParam P y) at hn
  have hn0 : (n:E)=0 := by simpa only [hz,norm_zero,inv_zero,zero_smul] using hn
  exact (ne_zero_of_mem_unit_sphere n) hn0

lemma GenuineBoostPatch.polar_commutes {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ)) :
    polarParam Q.patch (lorentzPolarChart e (mass e p) p P.param Q.patch.extension y) =
      hyperbolicMap e (mass e p) p (polarParam P y) := by
  obtain ⟨n,hn,heq⟩ := h.chart_image y hy
  simp only [polarParam,lorentzPolarChart,slice_zero,angularProjection_slice]
  change ‖hyperbolicMap e (mass e p) p (polarParam P y)‖ •
    Q.patch.param (Q.patch.extension (boostedDirection e (mass e p) p P.param y)) = _
  rw [← heq,Q.patch.extension_eq n hn.1,Q.patch.param_chart hn.1,heq]
  change ‖hyperbolicMap e (mass e p) p (polarParam P y)‖ •
    (‖hyperbolicMap e (mass e p) p (polarParam P y)‖⁻¹ •
      hyperbolicMap e (mass e p) p (polarParam P y)) = _
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (h.spatial_nonzero hy)),one_smul]
  rfl

lemma GenuineBoostPatch.old_angle {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ)) :
    angularProjection (lorentzPolarChart e (mass e p) p P.param Q.patch.extension y) ∈ Q.region := by
  obtain ⟨n,hn,heq⟩ := h.chart_image y hy
  simp only [lorentzPolarChart,angularProjection_slice]
  change Q.patch.extension (boostedDirection e (mass e p) p P.param y) ∈ Q.region
  rw [← heq,Q.patch.extension_eq n hn.1]
  exact hn.2

lemma GenuineBoostPatch.chart_contDiffAt {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ)) :
    ContDiffAt ℝ ∞ (lorentzPolarChart e (mass e p) p P.param Q.patch.extension) y := by
  have hP := polarParam_contDiffAt P (h.estimates.ball_target hy.2)
  have hv := (hyperbolicMap_smooth e (mass e p) p).contDiffAt.comp y hP
  have hnorm := hv.norm ℝ (h.spatial_nonzero hy)
  have hnormalize := (hnorm.inv (norm_ne_zero_iff.mpr (h.spatial_nonzero hy))).smul hv
  obtain ⟨n,hn,heq⟩ := h.chart_image y hy
  have hdom : boostedDirection e (mass e p) p P.param y ∈ Q.patch.domain := by
    rw [← heq]; exact Q.patch.source_domain n hn.1
  have hangle := (Q.patch.extension_smooth.contDiffAt (Q.patch.isOpen_domain.mem_nhds hdom)).comp y hnormalize
  change ContDiffAt ℝ ∞ (fun z => slice _ _) y
  have hsingle : ContDiffAt ℝ ∞ (fun z => (Pi.single (0:I)
      ‖hyperbolicMap e (mass e p) p (polarParam P z)‖ : Point)) y := by
    apply contDiffAt_pi.mpr
    intro i
    by_cases hi : i=0
    · subst i; simp only [Pi.single_eq_same]; exact hnorm
    · simpa only [Pi.single_eq_of_ne hi] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Point => (0:ℝ)) y)
  exact hsingle.add (injection.contDiff.contDiffAt.comp y hangle)

lemma GenuineBoostPatch.tensor_components {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ))
    (A : SpatialTensor) (a b : I) :
    coordinateTensorPullback (lorentzPolarChart e (mass e p) p P.param Q.patch.extension)
      (polarTensorComponents Q.patch A) a b y =
    polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A) a b y := by
  apply polarTensor_covariance P Q.patch A
  · exact (h.chart_contDiffAt hy).differentiableAt (by simp)
  · exact (polarParam_contDiffAt P (h.estimates.ball_target hy.2)).differentiableAt (by simp)
  · exact (polarParam_contDiffAt Q.patch (Q.region_target (h.old_angle hy))).differentiableAt (by simp)
  · exact (hyperbolicMap_smooth e (mass e p) p).differentiable (by simp) |>.differentiableAt
  · filter_upwards [(angularRadialTail_open R Metric.isOpen_ball).mem_nhds hy] with z hz
    exact h.polar_commutes hz
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped ContDiff Topology
lemma scaledIter_congr_germ {f g : Point → ℝ} {y : Point} (h : f =ᶠ[𝓝 y] g)
    (l : List I) : scaledIter l f =ᶠ[𝓝 y] scaledIter l g := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    filter_upwards [ih.fderiv (𝕜:=ℝ)] with z hz
    exact congrArg (fun L : Point →L[ℝ] ℝ => radialFactor a z * L (basis a)) hz
lemma SourceRemainderOn.congrOn {j q : ℕ} {V : Set Point} {f g : Point → ℝ}
    (hf : SourceRemainderOn j q V f) (hV : IsOpen V) (he : EqOn f g V) :
    SourceRemainderOn j q V g := by
  have hg {y} (hy : y ∈ V) : f =ᶠ[𝓝 y] g := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact he hz
  refine ⟨fun y hy => (hf.regular y hy).congr_of_eventuallyEq (hg hy).symm,?_⟩
  obtain ⟨B,hB,hb⟩ := hf.bound
  refine ⟨B,hB,?_⟩
  intro y hy l hl
  rw [← (scaledIter_congr_germ (hg hy) l).eq_of_nhds]
  exact hb y hy l hl
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Set
lemma SourceCKSComponents.congrOn {j q : ℕ} {V : Set Point}
    {A B : I → I → Point → ℝ} {mr : Angle → ℝ}
    {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j q V A mr mg) (hV : IsOpen V)
    (he : ∀ i k, EqOn (A i k) (B i k) V) : SourceCKSComponents j q V B mr mg := by
  refine ⟨hA.radial.congrOn hV (fun y hy => by dsimp only; rw [he 0 0 hy]),?_,?_⟩
  · intro i k hik
    exact (hA.mixed i k hik).congrOn hV (he i k)
  · intro i k hi hk
    exact (hA.angular i k hi hk).congrOn hV (fun y hy => by dsimp only; rw [he i k hy])
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

theorem exists_lorentzChartDomain_image {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    {A W : Set Angle} {B : Set E}
    (hA : IsOpen A) (hθ : θ ∈ A) (hφ : ContDiffOn ℝ ∞ φ A)
    (hn : ∀ η ∈ A, φ η ∈ Metric.sphere (0:E) 1)
    (hB : IsOpen B) (hψ : ContDiffOn ℝ ∞ ψ B)
    (hb : boundaryAmbient e m p (φ θ) ∈ B)
    (hW : IsOpen W) (hw : boundaryChart e m p φ ψ θ ∈ W) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧
      LorentzChartDomain e m p φ ψ (Metric.closedBall (slice 0 θ) δ)
        (angularLogTail L θ (δ/2)) (angularRadialTail R W) ∧
      MapsTo angularProjection (Metric.closedBall (slice 0 θ) δ) A ∧
      MapsTo (fun z => angularProjection (compactLorentzCoefficients e m p φ ψ z))
        (Metric.closedBall (slice 0 θ) δ) W ∧
      MapsTo (fun z => compactAngle e m p (compactPolar φ z))
        (Metric.closedBall (slice 0 θ) δ) B := by
  let z₀ : Point := slice 0 θ
  have hφ₀ := hφ.contDiffAt (hA.mem_nhds hθ)
  have hp : ContDiffAt ℝ ∞ (compactPolar φ) z₀ := by
    apply compactPolar_contDiffAt
    simpa only [z₀,angularProjection_slice] using hφ₀
  have hz₀ : compactPolar φ z₀ ∈ compactRegion e m p := by
    simpa only [z₀,compactPolar_slice] using compactRegion_boundary he hm0 hm (hn θ hθ)
  have hb₀ : compactAngle e m p (compactPolar φ z₀) ∈ B := by
    simpa only [z₀,compactPolar_slice,compactAngle_boundary he hm0 hm (hn θ hθ)] using hb
  have hψ₀ := hψ.contDiffAt (hB.mem_nhds hb₀)
  have hc : ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) z₀ := by
    apply compactLorentzCoefficients_contDiffAt e m p φ ψ
    · simpa only [z₀,angularProjection_slice] using hφ₀
    · exact hz₀
    · exact hψ₀
  have hw₀ : angularProjection (compactLorentzCoefficients e m p φ ψ z₀) ∈ W := by
    simpa only [z₀,compactLorentzCoefficients_boundary he hm0 hm φ ψ (hn θ hθ),
      angularProjection_slice] using hw
  let d : ℝ := denominator e m p (φ θ)/2
  have hd : 0 < d := half_pos (denominator_pos he hm0 ⟨φ θ,hn θ hθ⟩)
  have hds : d < compactScale e m p (compactPolar φ z₀) := by
    rw [show z₀ = slice 0 θ from rfl,compactPolar_slice,compactScale_boundary he hm0 hm (hn θ hθ)]
    exact half_lt_self (denominator_pos he hm0 ⟨φ θ,hn θ hθ⟩)
  have ha : ∀ᶠ z : Point in 𝓝 z₀, angularProjection z ∈ A :=
    angularProjection.continuous.continuousAt.preimage_mem_nhds
      (hA.mem_nhds (by simpa only [z₀,angularProjection_slice] using hθ))
  have hr : ∀ᶠ z : Point in 𝓝 z₀, compactPolar φ z ∈ compactRegion e m p :=
    hp.continuousAt.preimage_mem_nhds ((compactRegion_open e m p).mem_nhds hz₀)
  have hb' : ∀ᶠ z : Point in 𝓝 z₀, compactAngle e m p (compactPolar φ z) ∈ B :=
    ((compactAngle_contDiffAt e m p hz₀).comp z₀ hp).continuousAt.preimage_mem_nhds
      (hB.mem_nhds hb₀)
  have hw' : ∀ᶠ z : Point in 𝓝 z₀,
      angularProjection (compactLorentzCoefficients e m p φ ψ z) ∈ W :=
    (angularProjection.contDiff.contDiffAt.comp z₀ hc).continuousAt.preimage_mem_nhds
      (hW.mem_nhds hw₀)
  have hs : ∀ᶠ z : Point in 𝓝 z₀, d < compactScale e m p (compactPolar φ z) :=
    ((compactScale_smooth_region e m p hz₀).comp z₀ hp).continuousAt
      (lt_mem_nhds hds)
  obtain ⟨ρ,hρ,hsub⟩ := Metric.mem_nhds_iff.1 (ha.and (hr.and (hb'.and (hw'.and hs))))
  let δ : ℝ := ρ/2
  have hδ : 0 < δ := half_pos hρ
  have hδρ : δ < ρ := half_lt_self hρ
  have hK z (hz : z ∈ Metric.closedBall z₀ δ) :=
    hsub (Metric.closedBall_subset_ball hδρ hz)
  obtain ⟨L,hL,hLt⟩ := eventually_full_log_tail (half_pos hδ) hd R
  have hnew {x : Point} (hx : x ∈ angularLogTail L θ (δ/2)) :
      inverseLogRadiusChart x ∈ Metric.closedBall z₀ δ := by
    apply inverseLogRadius_mem_closedBall hδ
    · exact ((hLt (x 0) hx.1).1).trans (half_le_self hδ.le)
    · exact ((Metric.mem_ball.mp hx.2).le).trans (half_le_self hδ.le)
  refine ⟨δ,hδ,L,hL,?_,fun z hz => (hK z hz).1,fun z hz => (hK z hz).2.2.2.1,
    fun z hz => (hK z hz).2.2.1⟩
  refine ⟨isCompact_closedBall _ _,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact hφ.contDiffAt (hA.mem_nhds (hK z hz).1)
  · intro z hz
    exact (hK z hz).2.1
  · intro z hz
    exact hψ.contDiffAt (hB.mem_nhds (hK z hz).2.2.1)
  · intro z hz
    exact (convex_closedBall z₀ δ).segment_subset (boundaryProjection_closedBall hδ.le hz) hz
  · intro x hx
    exact hnew hx
  · intro x hx
    have hk := hK _ (hnew hx)
    refine ⟨?_,?_⟩
    · change R < Real.exp ((logLorentzChart e m p φ ψ x) 0)
      rw [logLorentzChart_radial_exp e m p φ ψ hk.2.1.2]
      exact ((hLt (x 0) hx.1).2).trans_le
        (mul_le_mul_of_nonneg_left hk.2.2.2.2.le (Real.exp_pos _).le)
    · simpa only [angularProjection_logRadiusChart,logLorentzChart_angular_coeff] using hk.2.2.2.1
  · intro x hx
    exact hL.trans hx.1

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped Topology ContDiff
lemma SmoothAngularPatch.exists_exact_domain (P : SmoothAngularPatch) :
    ∃ B : Set E, IsOpen B ∧ B ⊆ P.domain ∧
      ∀ n : Sphere, (n:E) ∈ B ↔ n ∈ P.chart.source := by
  obtain ⟨V,hV,hPV⟩ := isOpen_induced_iff.mp P.chart.open_source
  refine ⟨P.domain ∩ V,P.isOpen_domain.inter hV,inter_subset_left,?_⟩
  intro n
  have hv : (n:E) ∈ V ↔ n ∈ P.chart.source := by rw [← hPV]; rfl
  exact ⟨fun h => hv.mp h.2,fun h => ⟨P.source_domain n h,hv.mpr h⟩⟩

lemma compactAngle_sphere (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : compactAngle e m p z ∈ Metric.sphere (0:E) 1 := by
  simp only [Metric.mem_sphere,dist_zero_right,compactAngle,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hz.2)]
  exact inv_mul_cancel₀ hz.2.ne'

lemma boostedDirection_log (e m : ℝ) (p : E) (P : SmoothAngularPatch) {x : Point}
    (_hz : compactPolar P.param (inverseLogRadiusChart x) ∈ compactRegion e m p) :
    boostedDirection e m p P.param (logRadiusChart x) =
      compactAngle e m p (compactPolar P.param (inverseLogRadiusChart x)) := by
  have ht := hyperbolicMap_polar (e:=e) (m:=m) (p:=p) (Real.exp_pos (x 0))
    (P.chart.symm (angularProjection x))
  change hyperbolicMap e m p (Real.exp (x 0) • P.param (angularProjection x)) =
    Real.exp (x 0) • compactSpatial e m p
      ((Real.exp (x 0))⁻¹, P.param (angularProjection x)) at ht
  simp only [boostedDirection,angularProjection_logRadiusChart,show logRadiusChart x 0=Real.exp (x 0) from rfl]
  rw [ht,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos (x 0)),smul_smul,mul_inv_rev]
  simp only [mul_assoc,inv_mul_cancel₀ (Real.exp_ne_zero (x 0)),mul_one]
  change (compactScale e m p ((Real.exp (x 0))⁻¹,P.param (angularProjection x)))⁻¹ •
    compactSpatial e m p ((Real.exp (x 0))⁻¹,P.param (angularProjection x)) = _
  rw [← Real.exp_neg]
  rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem exists_genuineBoostPatch {e : ℝ} {p : E} (he : ‖p‖ < e)
    (Q : CKSTensorPatch) (P : SmoothAngularPatch) {n : Sphere}
    (hn : n ∈ P.chart.source)
    (hQ : boundary e p he n ∈ Q.patch.sphereRegion Q.region) :
    ∃ δ R : ℝ, GenuineBoostPatch e p he Q P (P.chart n) δ R := by
  let θ := P.chart n
  have hθ : θ ∈ P.chart.target := P.chart.map_source hn
  obtain ⟨B,hB,hQB,hBS⟩ := Q.patch.exists_exact_domain
  have hb : boundaryAmbient e (mass e p) p (P.param θ) ∈ B := by
    rw [P.param_chart hn]
    exact (hBS _).mpr hQ.1
  have hw : boundaryChart e (mass e p) p P.param Q.patch.extension θ ∈ Q.region := by
    change Q.patch.extension (boundaryAmbient e (mass e p) p (P.param θ)) ∈ Q.region
    rw [P.param_chart hn]
    rw [show boundaryAmbient e (mass e p) p (n:E) = (boundary e p he n : E) from rfl]
    rw [Q.patch.extension_eq _ hQ.1]
    exact hQ.2
  obtain ⟨δ,hδ,L,hL,hd,ha,ho,hi⟩ := exists_lorentzChartDomain_image he (mass_pos he) (mass_sq he)
    P.param Q.patch.extension P.chart.open_target hθ P.param_smooth
    (fun η hη => P.param_sphere η) hB (Q.patch.extension_smooth.mono hQB) hb
    Q.open_region hw Q.radius
  have hs {η : Angle} (hη : η ∈ Metric.ball θ (δ/2)) :
      slice 0 η ∈ Metric.closedBall (slice 0 θ) δ := by
    apply slice_mem_closedBall hδ.le
    exact Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hη).le.trans (half_le_self hδ.le))
  have hm := lorentz_metric_CKS e (mass e p) p P.param Q.patch.extension hd Q.metric_CKS
    (fun z hz => Q.mr_smooth.contDiffAt (Q.open_region.mem_nhds (ho hz)))
    (fun i k hi hk z hz => (Q.mg_smooth i k hi hk).contDiffAt
      (Q.open_region.mem_nhds (ho hz)))
  have hk := lorentz_second_CKS e (mass e p) p P.param Q.patch.extension hd Q.second_CKS
    (fun i k hi hk z hz => (Q.mK_smooth i k hi hk).contDiffAt
      (Q.open_region.mem_nhds (ho hz)))
  have hest : BoostPatchEstimates e p Q P (P.chart n) (δ/2) (Real.exp L) := by
    refine ⟨Real.exp_pos L,half_pos hδ,?_,
      hm.mono (angularRadialTail_subset_log L θ (δ/2)),
      hk.mono (angularRadialTail_subset_log L θ (δ/2)),?_,?_,?_⟩
    · intro η hη
      simpa only [angularProjection_slice] using ha (hs hη)
    · intro η hη
      apply ContDiffAt.contDiffWithinAt
      apply lorentzRadialLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
      · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
      · exact hd.region _ (hs hη)
      · exact hd.chartInv _ (hs hη)
      · exact Q.mr_smooth.contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))
    · intro i k η hη
      apply ContDiffAt.contDiffWithinAt
      apply lorentzAngularLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
      · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
      · exact hd.region _ (hs hη)
      · exact hd.chartInv _ (hs hη)
      · intro a b ha hb
        exact (Q.mg_smooth a b ha hb).contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))
    · intro i k η hη
      apply ContDiffAt.contDiffWithinAt
      apply lorentzAngularLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
      · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
      · exact hd.region _ (hs hη)
      · exact hd.chartInv _ (hs hη)
      · intro a b ha hb
        exact (Q.mK_smooth a b ha hb).contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))
  refine ⟨δ/2,Real.exp L,⟨hest,?_,?_,?_⟩⟩
  · intro η hη
    have hsrc : boundary e p he (P.chart.symm η) ∈ Q.patch.chart.source := by
      apply (hBS _).mp
      have ht := hi (hs hη)
      change boundaryAmbient e (mass e p) p (P.param η) ∈ B
      simpa only [compactPolar_slice,compactAngle_boundary he (mass_pos he) (mass_sq he)
        (P.param_sphere η)] using ht
    refine ⟨hsrc,?_⟩
    have ht := ho (hs hη)
    change angularProjection (compactLorentzCoefficients e (mass e p) p P.param
      Q.patch.extension (slice 0 η)) ∈ Q.region at ht
    rw [compactLorentzCoefficients_boundary he (mass_pos he) (mass_sq he) P.param
      Q.patch.extension (P.param_sphere η),angularProjection_slice] at ht
    change Q.patch.chart (boundary e p he (P.chart.symm η)) ∈ Q.region
    rw [← Q.patch.extension_eq _ hsrc]
    exact ht
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := angularRadialTail_subset_log L θ (δ/2) hy
    have hz := hd.newRegion hx
    let n' : Sphere := ⟨compactAngle e (mass e p) p (compactPolar P.param (inverseLogRadiusChart x)),
      compactAngle_sphere e (mass e p) p (hd.region _ hz)⟩
    have hn' : n' ∈ Q.patch.chart.source := (hBS _).mp (hi hz)
    refine ⟨n',⟨hn',?_⟩,(boostedDirection_log e (mass e p) p P (hd.region _ hz)).symm⟩
    change Q.patch.chart n' ∈ Q.region
    rw [← Q.patch.extension_eq _ hn']
    simpa only [compactLorentzCoefficients,angularProjection_slice,n'] using ho hz
  · intro y hy A a b
    obtain ⟨x,hx,rfl⟩ := angularRadialTail_subset_log L θ (δ/2) hy
    have hz := hd.newRegion hx
    exact lorentzOrdinaryTensor_eq_pullback e (mass e p) p P.param Q.patch.extension
      (Filter.Eventually.of_forall P.param_sphere) (hd.chart _ hz) (hd.region _ hz) (hd.chartInv _ hz) A a b

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma GenuineBoostPatch.mono_radius {e R₁ R₂ δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R₁) (hR : R₁ ≤ R₂) :
    GenuineBoostPatch e p he Q P θ δ R₂ := by
  have hs : angularRadialTail R₂ (Metric.ball θ δ) ⊆ angularRadialTail R₁ (Metric.ball θ δ) :=
    fun y hy => ⟨hR.trans_lt hy.1,hy.2⟩
  exact ⟨h.estimates.mono_radius hR,h.boundary_image,
    fun y hy => h.chart_image y (hs hy),fun y hy => h.genuine_tensor y (hs hy)⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology
lemma GenuineBoostPatch.toSpatial {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R) (A B : SpatialTensor)
    (hr : Q.Realizes A B)
    (htail : MapsTo (lorentzPolarChart e (mass e p) p P.param Q.patch.extension)
      (angularRadialTail R (Metric.ball θ δ)) (angularRadialTail Q.radius Q.region)) :
    SpatialBoostPatch e p he A B Q P θ δ R := by
  have hm (a b : I) : EqOn
      (lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension Q.metric a b)
      (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A) a b)
      (angularRadialTail R (Metric.ball θ δ)) := by
    intro y hy
    rw [h.genuine_tensor y hy]
    rw [← h.tensor_components hy A a b]
    unfold coordinateTensorPullback
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [(hr _ (htail hy) i k).1]
  have hk (a b : I) : EqOn
      (lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension Q.second a b)
      (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) B) a b)
      (angularRadialTail R (Metric.ball θ δ)) := by
    intro y hy
    rw [h.genuine_tensor y hy]
    rw [← h.tensor_components hy B a b]
    unfold coordinateTensorPullback
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [(hr _ (htail hy) i k).2]
  exact ⟨h,htail,h.estimates.metric_CKS.congrOn (angularRadialTail_open R Metric.isOpen_ball) hm,
    h.estimates.second_CKS.congrOn (angularRadialTail_open R Metric.isOpen_ball) hk⟩

theorem exists_spatialBoostPatch {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (Q : CKSTensorPatch) (hr : Q.Realizes A B)
    (P : SmoothAngularPatch) {n : Sphere} (hn : n ∈ P.chart.source)
    (hQ : boundary e p he n ∈ Q.patch.sphereRegion Q.region) :
    ∃ δ R : ℝ, SpatialBoostPatch e p he A B Q P (P.chart n) δ R := by
  obtain ⟨δ,R,h⟩ := exists_genuineBoostPatch he Q P hn hQ
  obtain ⟨R₀,hR₀,hproper⟩ := hyperbolic_boost_full_tails he Q.radius
  have h' := h.mono_radius (le_max_left R R₀)
  refine ⟨δ,max R R₀,h'.toSpatial A B hr ?_⟩
  intro y hy
  refine ⟨?_,h'.old_angle hy⟩
  simp only [lorentzPolarChart,slice_zero]
  change Q.radius < ‖hyperbolicMap e (mass e p) p (polarParam P y)‖
  apply (hproper _ ?_).1
  rw [polarParam_norm P (h'.estimates.radius_pos.trans hy.1).le]
  exact lt_of_le_of_lt (le_max_right R R₀) hy.1

lemma SpatialBoostPatch.mono_radius {e R₁ R₂ δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle} {A B : SpatialTensor}
    (h : SpatialBoostPatch e p he A B Q P θ δ R₁) (hR : R₁ ≤ R₂) :
    SpatialBoostPatch e p he A B Q P θ δ R₂ := by
  have hs : angularRadialTail R₂ (Metric.ball θ δ) ⊆ angularRadialTail R₁ (Metric.ball θ δ) :=
    fun y hy => ⟨hR.trans_lt hy.1,hy.2⟩
  exact ⟨h.genuine.mono_radius hR,fun y hy => h.old_tail (hs hy),
    h.metric_CKS.mono hs,h.second_CKS.mono hs⟩
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology
theorem exists_precompact_spatial_boost_atlas {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hreal : ∀ n, (old n).Realizes A B) :
    ∃ (s : Finset Sphere) (P : Sphere → SmoothAngularPatch) (δ : Sphere → ℝ) (R : ℝ),
      0 < R ∧
      (∀ n ∈ s, SpatialBoostPatch e p he A B (old (boundary e p he n)) (P n) ((P n).chart n) (2*δ n) R) ∧
      ∀ q : Sphere, ∃ n ∈ s, q ∈ (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n)) := by
  classical
  choose P hP using exists_smoothAngularPatch
  choose δ R hR using fun n => exists_spatialBoostPatch he A B
    (old (boundary e p he n)) (hreal _) (P n) (hP n) (hold (boundary e p he n))
  let U (n : Sphere) := (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n/2))
  have hU n : IsOpen (U n) := (P n).sphereRegion_open Metric.isOpen_ball
  have hn n : n ∈ U n := ⟨hP n,Metric.mem_ball_self (half_pos (hR n).genuine.estimates.ball_pos)⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (show univ ⊆ ⋃ n, U n from fun n _ => mem_iUnion.2 ⟨n,hn n⟩)
  have hsum : 0 ≤ ∑ n ∈ s, R n := Finset.sum_nonneg (fun n _ => (hR n).genuine.estimates.radius_pos.le)
  refine ⟨s,P,(fun n => δ n/2),1+∑ n ∈ s, R n,by linarith,?_,?_⟩
  · intro n hn
    have hh : 2 * (δ n / 2) = δ n := by ring
    rw [hh]
    apply (hR n).mono_radius
    have hle : R n ≤ ∑ m ∈ s, R m :=
      Finset.single_le_sum (fun m _ => (hR m).genuine.estimates.radius_pos.le) hn
    linarith
  · intro q
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hs (mem_univ q))
    obtain ⟨hns,hqn⟩ := mem_iUnion.mp hn
    exact ⟨n,hns,hqn⟩

end
end CKSLorentz

end
































































































end OAI
end

section
namespace OAI















































































noncomputable section
namespace CKSLorentz
noncomputable section
open Matrix

lemma trace_conformal_congruence {d : ℝ} (hd : d ≠ 0)
    (σ J A : AngularMatrix) (hσ : IsUnit σ.det) (hJ : IsUnit J.det) :
    angularMetricTrace (d^2 • (J*σ*J.transpose)) (d⁻¹ • (J*A*J.transpose)) =
      d⁻¹^3 * angularMetricTrace σ A := by
  have hJt : IsUnit J.transpose.det := by simpa using hJ
  have hi : (d^2 • (J*σ*J.transpose))⁻¹ =
      (d^2)⁻¹ • (J.transpose⁻¹ * σ⁻¹ * J⁻¹) := by
    apply Matrix.inv_eq_left_inv
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hd),one_smul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
    rw [← Matrix.mul_assoc σ⁻¹, Matrix.nonsing_inv_mul _ hσ,Matrix.one_mul]
    exact Matrix.nonsing_inv_mul _ hJt
  simp only [angularMetricTrace,hi,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.trace_smul]
  have ht : (J.transpose⁻¹ * σ⁻¹ * J⁻¹ * (J*A*J.transpose)).trace = (σ⁻¹*A).trace := by
    calc
      _ = (J.transpose⁻¹ * (σ⁻¹ * A) * J.transpose).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
      _ = (J.transpose * J.transpose⁻¹ * (σ⁻¹*A)).trace := Matrix.trace_mul_cycle _ _ _
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hJt,Matrix.one_mul]
  rw [ht]
  simp only [smul_eq_mul,inv_pow]
  ring

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularGram_congruence (L : Angle →L[ℝ] E) {Φ : Angle → Angle} {θ : Angle}
    (hΦ : DifferentiableAt ℝ Φ θ) (a b : Fin 2) :
    (angularJacobian Φ θ *
      Matrix.gram ℝ (fun i : Fin 2 => L (CKSAngularGeometry.basis i)) *
      (angularJacobian Φ θ).transpose) a b =
    inner ℝ (L (fderiv ℝ Φ θ (CKSAngularGeometry.basis a)))
      (L (fderiv ℝ Φ θ (CKSAngularGeometry.basis b))) := by
  rw [angularJacobian_apply hΦ a,angularJacobian_apply hΦ b]
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    conj_trivial,Matrix.gram_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
  ring

lemma boundaryChart_regular {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    boundaryChart e (mass e p) p P.param Q.extension θ ∈ Q.chart.target ∧
    ContDiffAt ℝ ∞ (boundaryChart e (mass e p) p P.param Q.extension) θ := by
  have hb : boundaryAmbient e (mass e p) p (P.param θ) ∈ Q.domain :=
    Q.source_domain _ hQ
  constructor
  · change Q.extension (boundaryAmbient e (mass e p) p (P.param θ)) ∈ Q.chart.target
    rw [show boundaryAmbient e (mass e p) p (P.param θ)=
      (boundary e p he (P.chart.symm θ):E) from rfl,Q.extension_eq _ hQ]
    exact Q.chart.map_source hQ
  · have hB : ContDiffAt ℝ ∞ (fun η => boundaryAmbient e (mass e p) p (P.param η)) θ :=
      (boundaryAmbient_smooth (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne').comp
        (f := P.param) (g := boundaryAmbient e (mass e p) p) θ
        (P.param_contDiffAt hθ)
    exact (Q.extension_smooth.contDiffAt (Q.isOpen_domain.mem_nhds hb)).comp θ hB

lemma boundary_param_fderiv {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    (fderiv ℝ Q.param (boundaryChart e (mass e p) p P.param Q.extension θ)).comp
        (fderiv ℝ (boundaryChart e (mass e p) p P.param Q.extension) θ) =
      (fderiv ℝ (boundaryAmbient e (mass e p) p) (P.param θ)).comp (fderiv ℝ P.param θ) := by
  have hs : ContinuousAt (fun η => boundary e p he (P.chart.symm η)) θ :=
    (boundary_smooth e p he).continuous.continuousAt.comp (P.chart.symm.continuousAt hθ)
  have hn : ∀ᶠ η in 𝓝 θ, boundary e p he (P.chart.symm η) ∈ Q.chart.source :=
    hs.preimage_mem_nhds (Q.chart.open_source.mem_nhds hQ)
  have hg : (fun η => Q.param (boundaryChart e (mass e p) p P.param Q.extension η)) =ᶠ[𝓝 θ]
      (fun η => boundaryAmbient e (mass e p) p (P.param η)) := by
    filter_upwards [hn] with η hη
    change Q.param (Q.extension (boundary e p he (P.chart.symm η))) =
      (boundary e p he (P.chart.symm η):E)
    rw [Q.extension_eq _ hη]
    exact Q.param_chart hη
  have hreg := boundaryChart_regular he P Q hθ hQ
  have h := hg.fderiv_eq (𝕜:=ℝ)
  change fderiv ℝ (Q.param ∘ boundaryChart e (mass e p) p P.param Q.extension) θ =
    fderiv ℝ (boundaryAmbient e (mass e p) p ∘ P.param) θ at h
  rw [fderiv_comp θ ((Q.param_contDiffAt hreg.1).differentiableAt (by simp))
      (hreg.2.differentiableAt (by simp)),
    fderiv_comp θ ((boundaryAmbient_smooth
      (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne').differentiableAt (by simp))
      ((P.param_contDiffAt hθ).differentiableAt (by simp))] at h
  exact h

lemma boundary_roundMetric_conformal {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    let Φ := boundaryChart e (mass e p) p P.param Q.extension
    angularJacobian Φ θ * angularRoundMetric Q.param (Φ θ) * (angularJacobian Φ θ).transpose =
      (denominator e (mass e p) p (P.param θ))⁻¹ ^ 2 • angularRoundMetric P.param θ := by
  dsimp only
  ext a b
  change (angularJacobian _ θ * Matrix.gram ℝ (fun i : Fin 2 =>
    fderiv ℝ Q.param _ (CKSAngularGeometry.basis i)) * (angularJacobian _ θ).transpose) a b = _
  rw [angularGram_congruence _ ((boundaryChart_regular he P Q hθ hQ).2.differentiableAt (by simp))]
  have hd := boundary_param_fderiv he P Q hθ hQ
  have ha := congrArg (fun L : Angle →L[ℝ] E => L (CKSAngularGeometry.basis a)) hd
  have hb := congrArg (fun L : Angle →L[ℝ] E => L (CKSAngularGeometry.basis b)) hd
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  rw [ha,hb]
  exact boundary_conformal he (mass_pos he) (mass_sq he) (P.chart.symm θ) _ _
    (P.param_tangent hθ _) (P.param_tangent hθ _)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

theorem lorentz_leading_trace {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source)
    (mg : I → I → Angle → ℝ) :
    angularMetricTrace (angularRoundMetric P.param θ)
      (fun a b => lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ) =
    (denominator e (mass e p) p (P.param θ))⁻¹ ^ 3 *
      angularMetricTrace (angularRoundMetric Q.param (boundaryChart e (mass e p) p P.param Q.extension θ))
        (fun a b => mg a.succ b.succ (boundaryChart e (mass e p) p P.param Q.extension θ)) := by
  let Φ := boundaryChart e (mass e p) p P.param Q.extension
  let J := angularJacobian Φ θ
  let d := denominator e (mass e p) p (P.param θ)
  let σ := angularRoundMetric Q.param (Φ θ)
  let A : AngularMatrix := fun a b => mg a.succ b.succ (Φ θ)
  have hd : d ≠ 0 := (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne'
  have hreg := boundaryChart_regular he P Q hθ hQ
  have hσ : IsUnit σ.det := isUnit_iff_ne_zero.mpr (Q.roundMetric_posDef hreg.1).det_pos.ne'
  have hconf : J*σ*J.transpose = d⁻¹^2 • angularRoundMetric P.param θ :=
    boundary_roundMetric_conformal he P Q hθ hQ
  have hp : (J*σ*J.transpose).PosDef := by
    rw [hconf]
    exact (P.roundMetric_posDef hθ).smul (sq_pos_of_ne_zero (inv_ne_zero hd))
  have hJ : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hdet := hp.det_pos.ne'
    simp only [Matrix.det_mul,Matrix.det_transpose,hz,zero_mul,mul_zero,ne_eq,not_true_eq_false] at hdet
  have hback : angularRoundMetric P.param θ=d^2 • (J*σ*J.transpose) := by
    rw [hconf,smul_smul,inv_pow,mul_inv_cancel₀ (pow_ne_zero 2 hd),one_smul]
  have hψ : ContDiffAt ℝ ∞ Q.extension (boundaryAmbient e (mass e p) p (P.param θ)) :=
    Q.extension_smooth.contDiffAt (Q.isOpen_domain.mem_nhds (Q.source_domain _ hQ))
  have hA : (fun a b : Fin 2 =>
      lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ) =
      d⁻¹ • (J*A*J.transpose) := by
    ext a b
    change lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ =
      d⁻¹ * ∑ i : Fin 2, (∑ j : Fin 2, J a j * A j i) * J b i
    rw [lorentzAngularLeading_boundary he (mass_pos he) (mass_sq he) P.param Q.extension mg
      (Eventually.of_forall P.param_sphere) (P.param_contDiffAt hθ) hψ a b]
    simp only [angularCoordinatePullback,J,A,d,Φ,angularJacobian,Fin.sum_univ_two]
    ring
  rw [hback,hA]
  exact trace_conformal_congruence hd σ J A hσ hJ

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
lemma angularMetricTrace_add (σ A B : AngularMatrix) :
    angularMetricTrace σ (A+B)=angularMetricTrace σ A+angularMetricTrace σ B := by
  simp only [angularMetricTrace,Matrix.mul_add,Matrix.trace_add]
lemma angularMetricTrace_smul (σ A : AngularMatrix) (c : ℝ) :
    angularMetricTrace σ (c • A)=c*angularMetricTrace σ A := by
  simp only [angularMetricTrace,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
lemma cksChartMassAspect_split (φ : Angle → E) (mr : Angle → ℝ)
    (mg mK : I → I → Angle → ℝ) (θ : Angle) :
    cksChartMassAspect φ mr mg mK θ =
      angularMetricTrace (angularRoundMetric φ θ) (fun a b => mg a.succ b.succ θ) +
      2*angularMetricTrace (angularRoundMetric φ θ) (fun a b => mK a.succ b.succ θ) + 2*mr θ := by
  let σ := angularRoundMetric φ θ
  let A : AngularMatrix := fun a b => mg a.succ b.succ θ
  let B : AngularMatrix := fun a b => mK a.succ b.succ θ
  change angularMetricTrace σ (A + (2:ℝ) • B) + 2*mr θ =
    angularMetricTrace σ A + 2*angularMetricTrace σ B + 2*mr θ
  rw [angularMetricTrace_add,angularMetricTrace_smul]

theorem lorentz_cks_massAspect {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) :
    cksChartMassAspect P.param (lorentzRadialLeading e (mass e p) p P.param Q.extension mr)
      (lorentzAngularLeading e (mass e p) p P.param Q.extension mg)
      (lorentzAngularLeading e (mass e p) p P.param Q.extension mK) θ =
    (denominator e (mass e p) p (P.param θ))⁻¹ ^3 *
      cksChartMassAspect Q.param mr mg mK
        (boundaryChart e (mass e p) p P.param Q.extension θ) := by
  rw [cksChartMassAspect_split,cksChartMassAspect_split,
    lorentz_leading_trace he P Q hθ hQ mg,lorentz_leading_trace he P Q hθ hQ mK,
    lorentzRadialLeading_boundary he (mass_pos he) (mass_sq he) P.param Q.extension mr
      (P.param_sphere θ)]
  ring
end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
lemma genuine_patch_massAspect {M : Sphere → ℝ} {e : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ₀ : Angle} {δ R : ℝ}
    (h : GenuineBoostPatch e p he Q P θ₀ δ R) (hrep : Q.RepresentsMassAspect M)
    {θ : Angle} (hθ : θ ∈ Metric.ball θ₀ δ) :
    cksChartMassAspect P.param
      (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
      (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
      (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK) θ =
      aspectPullback e p he M (P.chart.symm θ) := by
  have hb := h.boundary_image θ hθ
  rw [lorentz_cks_massAspect he P Q.patch (h.estimates.ball_target hθ) hb.1]
  change (denominator e (mass e p) p (P.param θ))⁻¹ ^3 *
      cksChartMassAspect Q.patch.param Q.mr Q.mg Q.mK
        (Q.patch.extension (boundary e p he (P.chart.symm θ))) = _
  rw [Q.patch.extension_eq _ hb.1,hrep _ hb]
  rfl
end
end CKSLorentz

end









































end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

def SpatialBoostPatch.asCKS {e : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch}
    {θ : Angle} {δ R : ℝ} (h : SpatialBoostPatch e p he A B Q P θ δ R) : CKSTensorPatch where
  patch := P
  region := Metric.ball θ δ
  open_region := Metric.isOpen_ball
  region_target := h.genuine.estimates.ball_target
  radius := R
  metric := polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
  second := polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)
  mr := lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr
  mg := lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg
  mK := lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK
  mr_smooth := h.genuine.estimates.radial_smooth
  mg_smooth := fun i k _ _ => h.genuine.estimates.angular_smooth i k
  mK_smooth := fun i k _ _ => h.genuine.estimates.second_smooth i k
  metric_CKS := h.metric_CKS
  second_CKS := h.second_CKS

lemma SpatialBoostPatch.asCKS_realizes {e : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch}
    {θ : Angle} {δ R : ℝ} (h : SpatialBoostPatch e p he A B Q P θ δ R) :
    h.asCKS.Realizes (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
      (spatialTensorPullback (hyperbolicMap e (mass e p) p) B) := by
  intro y hy i k
  exact ⟨rfl,rfl⟩

lemma SpatialBoostPatch.asCKS_aspect {M : Sphere → ℝ} {e : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch}
    {θ : Angle} {δ R : ℝ} (h : SpatialBoostPatch e p he A B Q P θ δ R)
    (hrep : Q.RepresentsMassAspect M) : h.asCKS.RepresentsMassAspect (aspectPullback e p he M) := by
  intro n hn
  change n ∈ P.sphereRegion (Metric.ball θ δ) at hn
  have hm := genuine_patch_massAspect h.genuine hrep hn.2
  simpa only [SpatialBoostPatch.asCKS, P.chart.left_inv hn.1] using hm

lemma boosted_cks_patches {M : Sphere → ℝ} {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hcovers : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hreal : ∀ n, (old n).Realizes A B) (hrep : ∀ n, (old n).RepresentsMassAspect M) :
    ∃ new : Sphere → CKSTensorPatch,
      (∀ n, n ∈ (new n).patch.sphereRegion (new n).region) ∧
      (∀ n, (new n).Realizes (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
        (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)) ∧
      (∀ n, (new n).RepresentsMassAspect (aspectPullback e p he M)) := by
  classical
  obtain ⟨s,P,δ,R,hR,hpatch,hcover⟩ :=
    exists_precompact_spatial_boost_atlas he A B old hcovers hreal
  choose index hmem hindex using hcover
  let H (n : Sphere) := hpatch (index n) (hmem n)
  refine ⟨fun n => (H n).asCKS,?_,?_,?_⟩
  · intro n
    refine ⟨(hindex n).1,?_⟩
    have hδ : δ (index n) ≤ 2*δ (index n) := by
      have hp := (H n).genuine.estimates.ball_pos
      linarith
    exact Metric.ball_subset_ball hδ (hindex n).2
  · intro n
    exact (H n).asCKS_realizes
  · intro n
    exact (H n).asCKS_aspect (hrep _)
end
end CKSLorentz

end

end OAI
end

theorem solution : type_of% @OAI.CKSLorentz.boosted_cks_patches := @OAI.CKSLorentz.boosted_cks_patches

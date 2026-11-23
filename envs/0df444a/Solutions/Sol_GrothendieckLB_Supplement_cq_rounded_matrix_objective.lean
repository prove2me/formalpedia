-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_rounded_matrix_objective
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:53:50.559805+00:00
-- url     : https://prove2.me/submissions/02e82ffb-0652-401c-988f-4e31db8e5890

import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_GrothendieckLB_Supplement_cqRhoPoly
import Mathlib.Analysis.Matrix.Order
import Mathlib
import Definitions.Def_KrivineSchemeDefs
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
open GrothendieckConstant MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology
set_option maxHeartbeats 500000
namespace CubicFeatures
/- The Schur-power and real Gram arguments follow the public proof of Krivine's bound on Prove2Me. -/
variable {ι : Type*} [Fintype ι]

lemma psd_entrywise_pow (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (k : ℕ) :
    Matrix.PosSemidef (fun i j => G i j ^ k) := by
  induction k with
  | zero =>
    have he : (fun i j => G i j ^ 0 : Matrix ι ι ℝ) =
        Matrix.vecMulVec (fun _ : ι => (1:ℝ)) (star (fun _ : ι => (1:ℝ))) := by
      ext i j; simp [Matrix.vecMulVec]
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star _
  | succ k hk =>
    have he : (fun i j => G i j ^ (k+1) : Matrix ι ι ℝ) =
        (fun i j => G i j ^ k) ⊙ G := by
      ext i j; simp [pow_succ, Matrix.hadamard]
    rw [he]
    exact hk.hadamard hG

section Factorization
open scoped MatrixOrder

/-- Columns of the positive square root realize any finite real PSD matrix. -/
lemma exists_gram (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    ∃ w : ι → EuclideanSpace ℝ ι, ∀ i j, inner ℝ (w i) (w j) = B i j := by
  classical
  let R := CFC.sqrt B
  have hR : R.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian
  have hsq : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  refine ⟨fun i => WithLp.toLp 2 (R.transpose i), ?_⟩
  intro i j
  rw [inner_matrix_col_col, hR, hsq]

end Factorization

lemma exists_unit_gram (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (hdiag : ∀ i, B i i = 1) :
    ∃ w : ι → EuclideanSpace ℝ (Fin (Fintype.card ι)),
      (∀ i, ‖w i‖ = 1) ∧ (∀ i j, inner ℝ (w i) (w j) = B i j) := by
  classical
  obtain ⟨w, hw⟩ := exists_gram B hB
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  refine ⟨fun i => e (w i), ?_, ?_⟩
  · intro i
    rw [e.norm_map]
    have h := hw i i
    rw [real_inner_self_eq_norm_sq, hdiag] at h
    nlinarith [norm_nonneg (w i)]
  · intro i j
    rw [e.inner_map_map, hw]

open GrothendieckLB.Supplement
private theorem powers_psd {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (hb : B.PosSemidef) (s : ι → ℝ) :
    Matrix.PosSemidef (fun i j => s i*s j*(B i j)^3) := by
  have h := (Matrix.posSemidef_vecMulVec_self_star s).hadamard (psd_entrywise_pow B hb 3)
  have e : (fun i j => s i*s j*(B i j)^3 : Matrix ι ι ℝ) = (Matrix.vecMulVec s (star s)) ⊙ (fun i j => B i j^3) := by
    ext i j
    simp only [Matrix.hadamard,Matrix.vecMulVec,Matrix.of_apply,star_trivial]
  rw [e]
  exact h

private theorem cubic_gram {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (hb : B.PosSemidef)
    (s : ι → ℝ) (u v : ℝ) :
    Matrix.PosSemidef (fun i j => 1/(1+u^2+v^2)*(B i j + u^2*(s i*s j*(B i j)^3)+v^2*(B i j)^5)) := by
  have h := (hb.add ((powers_psd B hb s).smul (sq_nonneg u))).add ((psd_entrywise_pow B hb 5).smul (sq_nonneg v))
  apply h.smul (show 0 ≤ 1/(1+u^2+v^2) by positivity)

theorem features {m n d : ℕ} (U : Fin m → EuclideanSpace ℝ (Fin d)) (V : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖U i‖=1) (hv : ∀ j, ‖V j‖=1) (u v r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ D : ℕ, ∃ P : Fin m → EuclideanSpace ℝ (Fin D), ∃ Q : Fin n → EuclideanSpace ℝ (Fin D),
      ∃ S : Fin m → EuclideanSpace ℝ (Fin D), ∃ T : Fin n → EuclideanSpace ℝ (Fin D),
      (∀ i, ‖P i‖=1) ∧ (∀ j, ‖Q j‖=1) ∧ (∀ i, ‖S i‖=1) ∧ (∀ j, ‖T j‖=1) ∧
      (∀ i j, inner ℝ (P i) (Q j)=(cqRhoPoly u v).eval (r*inner ℝ (U i) (V j))) ∧
      (∀ i j, inner ℝ (S i) (T j)=r*inner ℝ (U i) (V j)) := by
  classical
  let w := Sum.elim U V
  let G := Matrix.gram ℝ w
  let side : Fin m ⊕ Fin n → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  let B := r • G +(1-r) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)
  let C : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ := fun i j =>
    1/(1+u^2+v^2)*(B i j+u^2*(side i*side j*(B i j)^3)+v^2*(B i j)^5)
  have hB : B.PosSemidef := ((Matrix.posSemidef_gram ℝ w).smul hr0).add
    ((Matrix.PosSemidef.one : (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ).PosSemidef).smul (sub_nonneg.mpr hr1))
  have hdiag (i : Fin m ⊕ Fin n) : B i i=1 := by
    cases i with
    | inl i => simp [B,G,w,Matrix.gram_apply,hu]
    | inr j => simp [B,G,w,Matrix.gram_apply,hv]
  have hsc (i : Fin m ⊕ Fin n) : side i*side i=1 := by cases i <;> norm_num [side]
  have hcdiag (i : Fin m ⊕ Fin n) : C i i=1 := by
    have hne : (1+u^2+v^2) ≠ 0 := by positivity
    simp [C,hdiag,hsc,hne]
  obtain ⟨p,hp,hpg⟩ := exists_unit_gram C (cubic_gram B hB side u v) hcdiag
  obtain ⟨s,hs,hsg⟩ := exists_unit_gram B hB hdiag
  refine ⟨_,fun i => p (.inl i),fun j => p (.inr j),fun i => s (.inl i),fun j => s (.inr j),
    fun i => hp _,fun j => hp _,fun i => hs _,fun j => hs _,?_,?_⟩
  · intro i j
    rw [hpg]
    simp [C,B,side,G,w,Matrix.gram_apply,Matrix.one_apply,cqRhoPoly]
    ring_nf <;> simp
  · intro i j
    rw [hsg]
    simp [B,G,w,Matrix.gram_apply,Matrix.one_apply]

end CubicFeatures
open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace Topology NNReal ENNReal
namespace GaussianChannel
/- The joint projection law below is the characteristic-function argument in the accepted Prove2Me proof of Krivine's bound. -/
lemma dual_pair (L : StrongDual ℝ (ℝ × ℝ)) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have h : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
  rw [h, map_add, map_smul, map_smul]
  rfl

lemma charFunDual_standard_real (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L = Complex.exp (- (L 1 : ℂ) ^ 2 / 2) := by
  have h : charFunDual (gaussianReal 0 1) L = charFun (gaussianReal 0 1) (L 1) := by
    rw [charFunDual_apply, charFun_apply_real]
    congr 1
    ext x
    have hx : L x = x * L 1 := by
      simpa using L.map_smul x (1 : ℝ)
    rw [hx]
    push_cast
    ring_nf
  rw [h, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one,
    one_mul, zero_sub]
  congr 1
  ring

noncomputable def projectionPair {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] (ℝ × ℝ) :=
  (innerSL ℝ u).prod (innerSL ℝ v)

noncomputable def planePair (θ : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (Real.cos θ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Real.sin θ • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma dual_projectionPair {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (L : StrongDual ℝ (ℝ × ℝ)) :
    L.comp (projectionPair u v) = innerSL ℝ (L (1, 0) • u + L (0, 1) • v) := by
  ext g
  simp only [ContinuousLinearMap.comp_apply, projectionPair, ContinuousLinearMap.prod_apply,
    innerSL_apply_apply, inner_add_left, real_inner_smul_left]
  rw [dual_pair]
  ring

lemma norm_combination_sq {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (t s : ℝ) :
    ‖t • u + s • v‖ ^ 2 = t ^ 2 + s ^ 2 + 2 * t * s * inner ℝ u v := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hv, real_inner_comm v u]
  ring

/-- Equality of the joint projection laws, including singular Gram matrices. -/
theorem projectionPair_law {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (θ : ℝ) (hθ : Real.cos θ = inner ℝ u v) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (projectionPair u v) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (planePair θ) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_map, dual_projectionPair, charFunDual_stdGaussian,
    innerSL_apply_norm, charFunDual_prod, charFunDual_standard_real,
    charFunDual_standard_real, ← Complex.exp_add]
  have hleft : (L.comp (planePair θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1 =
      L (1, 0) + Real.cos θ * L (0, 1) := by
    change L (1, Real.cos θ * 1 + Real.sin θ * 0) = _
    rw [dual_pair]
    simp
  have hright : (L.comp (planePair θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1 =
      Real.sin θ * L (0, 1) := by
    change L (0, Real.cos θ * 0 + Real.sin θ * 1) = _
    rw [dual_pair]
    simp
  rw [hleft, hright]
  have hnorm := norm_combination_sq u v hu hv (L (1, 0)) (L (0, 1))
  have hgram : ‖L (1, 0) • u + L (0, 1) • v‖ ^ 2 =
      (L (1, 0) + Real.cos θ * L (0, 1)) ^ 2 + (Real.sin θ * L (0, 1)) ^ 2 := by
    rw [hnorm, ← hθ]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  congr 1
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hgram
  push_cast at hc ⊢
  linear_combination -hc / 2

private abbrev Pair := ℝ × ℝ
private noncomputable def density (r : ℝ) (z : Pair) :=
  GrothendieckConstant.gaussianPairDensity 1 r (fun _ => z.1) (fun _ => z.2)
private noncomputable def law (r : ℝ) : Measure Pair :=
  volume.withDensity fun z => ENNReal.ofReal (density r z)
private theorem dens_m (r : ℝ) : Measurable (density r) := by
  unfold density GrothendieckConstant.gaussianPairDensity
  simp only [Fin.prod_univ_one]
  fun_prop
private theorem dens_nonneg (r : ℝ) (z : Pair) : 0 ≤ density r z := by
  unfold density GrothendieckConstant.gaussianPairDensity
  simp only [Fin.prod_univ_one]
  positivity
private theorem dpos {r : ℝ} (hr : |r| < 1) : 0 < 1-r^2 := by
  have h := abs_lt.mp hr
  nlinarith only [mul_pos (sub_pos.mpr h.2) (by linarith only [h.1] : 0 < 1+r)]

private noncomputable def variance (r : ℝ) : ℝ≥0 := ⟨(Real.sqrt (1-r^2))^2,sq_nonneg _⟩
private theorem var_coe {r : ℝ} (hr : |r| < 1) : (variance r : ℝ) = 1-r^2 := Real.sq_sqrt (dpos hr).le
private theorem var_ne {r : ℝ} (hr : |r| < 1) : variance r ≠ 0 := by
  intro h
  have h' := var_coe hr
  rw [h,NNReal.coe_zero] at h'
  linarith only [dpos hr,h']
private theorem density_factor {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    gaussianPDFReal 0 1 x*gaussianPDFReal (r*x) (variance r) y = density r (x,y) := by
  have hd := dpos hr
  have hp : 0 < 2*Real.pi := by positivity
  have he : (-(x^2)/2)+(-((y-r*x)^2)/(2*(1-r^2))) =
      -(x^2-2*r*x*y+y^2)/(2*(1-r^2)) := by field_simp [hd.ne'] <;> ring
  simp only [gaussianPDFReal,density,GrothendieckConstant.gaussianPairDensity,Fin.prod_univ_one,
    NNReal.coe_one,mul_one,sub_zero,var_coe hr,Real.sqrt_mul hp.le]
  rw [←he,Real.exp_add]
  have hs := Real.sq_sqrt hp.le
  have hsp : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hsd : Real.sqrt (1-r^2) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  field_simp [hsp,hsd,Real.pi_ne_zero]
  nlinarith only [hs]

private theorem affine_map (r x : ℝ) :
    (gaussianReal 0 1).map (fun y : ℝ => r*x+Real.sqrt (1-r^2)*y) =
      gaussianReal (r*x) (variance r) := by
  let s := Real.sqrt (1-r^2)
  change (gaussianReal 0 1).map ((fun y : ℝ => r*x+y) ∘ (fun y : ℝ => s*y)) = _
  rw [←Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_mul,gaussianReal_map_const_add]
  simp [variance,s]
  rfl

private theorem lin_gauss {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ≥0∞} (hm : Measurable F) :
    (∫⁻ x, F x ∂gaussianReal m v) = ∫⁻ x, gaussianPDF m v x*F x := by
  rw [gaussianReal_of_var_ne_zero _ hv,lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hm]
  rfl

private theorem affine_law {r : ℝ} (hr : |r| < 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun z : Pair => (z.1,r*z.1+Real.sqrt (1-r^2)*z.2)) = law r := by
  apply Measure.ext_of_lintegral
  intro h hm
  let P (z : Pair) := (z.1,r*z.1+Real.sqrt (1-r^2)*z.2)
  have hP : Measurable P := by unfold P; fun_prop
  have hm' : Measurable (fun z => h (P z)) := hm.comp hP
  let J (x : ℝ) := ∫⁻ y, h (P (x,y)) ∂gaussianReal 0 1
  have hJ : Measurable J := hm'.lintegral_prod_right
  have hinner (x : ℝ) : J x = ∫⁻ y, gaussianPDF (r*x) (variance r) y*h (x,y) := by
    have hh : Measurable (fun y : ℝ => h (x,y)) := hm.comp measurable_prodMk_left
    rw [←lin_gauss (var_ne hr) hh,←affine_map r x,lintegral_map hh (by fun_prop)]
  change (∫⁻ z, h z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)).map P) = _
  rw [lintegral_map hm hP,lintegral_prod _ hm'.aemeasurable]
  change (∫⁻ x, J x ∂gaussianReal 0 1) = _
  rw [lin_gauss (by norm_num) hJ,law,lintegral_withDensity_eq_lintegral_mul _ (dens_m r).ennreal_ofReal hm,
    Measure.volume_eq_prod ℝ ℝ,lintegral_prod _ (((dens_m r).ennreal_ofReal.mul hm).aemeasurable)]
  apply lintegral_congr
  intro x
  have hi : Measurable (fun y : ℝ => gaussianPDF (r*x) (variance r) y*h (x,y)) := (measurable_gaussianPDF _ _).mul (hm.comp measurable_prodMk_left)
  rw [hinner,← lintegral_const_mul (gaussianPDF 0 1 x) hi]
  apply lintegral_congr
  intro y
  rw [←mul_assoc,gaussianPDF,gaussianPDF,←ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),density_factor hr]
  rfl

theorem projection_density {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖=1) (hv : ‖v‖=1) {r : ℝ} (hr : |r| < 1) (hxy : inner ℝ u v=r) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => (inner ℝ u z,inner ℝ v z)) = law r := by
  have hc := Real.cos_arccos (abs_lt.mp hr).1.le (abs_lt.mp hr).2.le
  change (stdGaussian _).map (projectionPair u v) = law r
  rw [projectionPair_law u v hu hv (Real.arccos r) (hc.trans hxy.symm)]
  have he : ⇑(planePair (Real.arccos r)) = (fun z : Pair => (z.1,r*z.1+Real.sqrt (1-r^2)*z.2)) := by
    funext z
    change (z.1,Real.cos (Real.arccos r)*z.1+Real.sin (Real.arccos r)*z.2)=_
    rw [hc,Real.sin_arccos]
  rw [he]
  exact affine_law hr

end GaussianChannel
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal Topology
namespace GaussianChannel
private theorem density_int {r : ℝ} (hr : |r| < 1) : Integrable (density r) := by
  refine ⟨(dens_m r).aestronglyMeasurable,?_⟩
  have hP : law r univ = 1 := by
    rw [←affine_law hr,Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  have hi : (∫⁻ z : Pair, ENNReal.ofReal (density r z))=1 := by simpa [law] using hP
  change (∫⁻ z : Pair, ‖density r z‖ₑ) < ⊤
  simp_rw [← ofReal_norm,Real.norm_eq_abs,fun z : Pair => abs_of_nonneg (dens_nonneg r z),hi]
  norm_num

private abbrev four := Pair × Pair
private def exchange : four ≃ᵐ four := (Homeomorph.prodProdProdComm ℝ ℝ ℝ ℝ).toMeasurableEquiv

private theorem preserve_exchange : MeasurePreserving exchange volume volume := by
  let a := volume_preserving_prodAssoc (α₁:=ℝ) (β₁:=ℝ) (γ₁:=Pair)
  let b := volume_preserving_prodAssoc (α₁:=ℝ) (β₁:=ℝ) (γ₁:=ℝ)
  let i := MeasurePreserving.id (volume : Measure ℝ)
  let sw : MeasurePreserving (MeasurableEquiv.prodComm (α:=ℝ) (β:=ℝ)) volume volume :=
    Measure.measurePreserving_swap
  exact a.symm.comp ((i.prod b).comp ((i.prod (sw.prod i)).comp ((i.prod b.symm).comp a)))

private theorem law_prod_integral (r t : ℝ) (J : four → ℝ) :
    (∫ z, J z ∂(law r).prod (law t)) =
      ∫ z : four, (density r z.1*density t z.2)*J z := by
  let w (z : four) := ENNReal.ofReal (density r z.1)*ENNReal.ofReal (density t z.2)
  have hw : Measurable w := (((dens_m r).ennreal_ofReal.comp measurable_fst).mul
    ((dens_m t).ennreal_ofReal.comp measurable_snd))
  have hwf (z : four) : w z < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [law,law,MeasureTheory.prod_withDensity (dens_m r).ennreal_ofReal (dens_m t).ennreal_ofReal]
  change (∫ z, J z ∂(volume.prod volume).withDensity w) = _
  rw [integral_withDensity_eq_integral_toReal_smul hw (Filter.Eventually.of_forall hwf) J,
    Measure.volume_eq_prod Pair Pair]
  simp only [w,ENNReal.toReal_mul,ENNReal.toReal_ofReal (dens_nonneg _ _),smul_eq_mul]

private theorem paired_expectation {D : ℕ} (P Q S T : EuclideanSpace ℝ (Fin D))
    (hp : ‖P‖=1) (hq : ‖Q‖=1) (hs : ‖S‖=1) (ht : ‖T‖=1)
    {r t : ℝ} (hr : |r| < 1) (ht' : |t| < 1) (hrp : inner ℝ P Q=r) (htp : inner ℝ S T=t)
    {f g : Pair → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ z, ‖f z‖ ≤ 1) (hgb : ∀ z, ‖g z‖ ≤ 1) :
    (∫ w, f (inner ℝ P w.1,inner ℝ S w.2)*g (inner ℝ Q w.1,inner ℝ T w.2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin D))).prod (stdGaussian _)) =
      ∫ x : Pair, ∫ y : Pair, f x*g y*(density r (x.1,y.1)*density t (x.2,y.2)) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin D))
  let U (z : EuclideanSpace ℝ (Fin D)) := (inner ℝ P z,inner ℝ Q z)
  let V (z : EuclideanSpace ℝ (Fin D)) := (inner ℝ S z,inner ℝ T z)
  let J (w : four) := f (w.1.1,w.2.1)*g (w.1.2,w.2.2)
  have hU : Measurable U := by unfold U; fun_prop
  have hV : Measurable V := by unfold V; fun_prop
  have hJ : Measurable J := (hf.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).mul
    (hg.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hJb (z : four) : ‖J z‖ ≤ 1 := by
    dsimp only [J]
    rw [norm_mul]
    exact mul_le_one₀ (hfb _) (norm_nonneg _) (hgb _)
  let K (z : four) := (density r z.1*density t z.2)*J z
  have hKi : Integrable K := by
    apply ((density_int hr).mul_prod (density_int ht')).mono
    · exact ((((dens_m r).comp measurable_fst).mul ((dens_m t).comp measurable_snd)).mul hJ).aestronglyMeasurable
    · filter_upwards with z
      dsimp only [K]
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hJb z)
  change (∫ w, J (Prod.map U V w) ∂μ.prod μ) = _
  rw [←integral_map (hU.prodMap hV).aemeasurable hJ.aestronglyMeasurable,←Measure.map_prod_map _ _ hU hV]
  have huv : μ.map U=law r := projection_density P Q hp hq hr hrp
  have hsv : μ.map V=law t := projection_density S T hs ht ht' htp
  rw [huv,hsv,law_prod_integral]
  change (∫ z : four, K z) = _
  rw [←preserve_exchange.integral_comp' K]
  have hi : Integrable (fun z => K (exchange z)) := (preserve_exchange.integrable_comp_emb exchange.measurableEmbedding).mpr hKi
  rw [Measure.volume_eq_prod Pair Pair,integral_prod _ hi]
  congr 1
  funext x
  congr 1
  funext y
  change (density r (x.1,y.1)*density t (x.2,y.2))*(f x*g y) = _
  ring
end GaussianChannel
open GrothendieckLB GrothendieckLB.Supplement GrothendieckConstant MeasureTheory Real ProbabilityTheory
namespace GaussianChannel
private theorem rho_contracts (u v t : ℝ) (ht : |t| ≤ 1) : |(cqRhoPoly u v).eval t| ≤ |t| := by
  let V := 1+u^2+v^2
  have hp : 0 < V := by dsimp [V]; positivity
  have h3 := pow_le_of_le_one (abs_nonneg t) ht (by decide : 3 ≠ 0)
  have h5 := pow_le_of_le_one (abs_nonneg t) ht (by decide : 5 ≠ 0)
  simp only [cqRhoPoly,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_pow,Polynomial.eval_X]
  change |1/V*(t-u^2*t^3+v^2*t^5)| ≤ |t|
  rw [abs_mul,abs_of_pos (one_div_pos.mpr hp),one_div,mul_comm,←div_eq_mul_inv,div_le_iff₀ hp]
  calc _ ≤ |t-u^2*t^3|+|v^2*t^5| := abs_add_le _ _
       _ ≤ (|t|+|u^2*t^3|)+|v^2*t^5| := add_le_add_left (abs_sub _ _) _
       _ = |t|+u^2*|t|^3+v^2*|t|^5 := by simp [abs_mul,abs_pow,sq_abs]
       _ ≤ |t|+u^2*|t|+v^2*|t| := by gcongr
       _ = |t| *V := by dsimp [V]; ring

theorem optSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (optSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨x, y, hx, hy, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 := le_abs_self (A i j)
  have h2 := neg_abs_le (A i j)
  rcases hx i with h | h <;> rcases hy j with h' | h' <;> rw [h, h'] <;> linarith



private noncomputable def partition (c u v : ℝ) (z : Pair) := cqF c u v z.1 z.2
private noncomputable def partition' (c u v : ℝ) (z : Pair) := cqG c u v z.1 z.2

private theorem partition_m (c u v : ℝ) : Measurable (partition c u v) := by
  unfold partition cqF
  change Measurable (fun z : Pair => if 0 ≤ z.1+c/Real.sqrt (1+u^2+v^2)*((z.2^3-3*z.2)/Real.sqrt 6) then (1:ℝ) else -1)
  apply Measurable.ite (measurableSet_le measurable_const ?_) measurable_const measurable_const
  fun_prop
private theorem partition_m' (c u v : ℝ) : Measurable (partition' c u v) := by
  unfold partition' cqG
  change Measurable (fun z : Pair => if 0 ≤ z.1-c/Real.sqrt (1+u^2+v^2)*((z.2^3-3*z.2)/Real.sqrt 6) then (1:ℝ) else -1)
  apply Measurable.ite (measurableSet_le measurable_const ?_) measurable_const measurable_const
  fun_prop
private theorem sign_p (c u v : ℝ) (z : Pair) : partition c u v z=1 ∨ partition c u v z= -1 := by unfold partition cqF; split <;> simp
private theorem sign_p' (c u v : ℝ) (z : Pair) : partition' c u v z=1 ∨ partition' c u v z= -1 := by unfold partition' cqG; split <;> simp

private theorem coord_integral (J : Pair → ℝ) : (∫ x : Fin 2 → ℝ, J (x 0,x 1))=∫ x : Pair, J x :=
  (volume_preserving_finTwoArrow ℝ).integral_comp' J

private theorem corr_pair (η u v t : ℝ) : cqCorr η u v t =
    Real.pi/2* ∫ x : Pair, ∫ y : Pair, partition η u v x * partition' η u v y *
      (density ((cqRhoPoly u v).eval t) (x.1,y.1)*density t (x.2,y.2)) := by
  unfold cqCorr multiCorr
  congr 1
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  let J (x y : Pair) := partition η u v x * partition' η u v y *
    (density ((cqRhoPoly u v).eval t) (x.1,y.1)*density t (x.2,y.2))
  change (∫ x : Fin 2 → ℝ, ∫ y : Fin 2 → ℝ, J (x 0,x 1) (y 0,y 1)) = ∫ x : Pair, ∫ y : Pair, J x y
  simp_rw [fun x => coord_integral (J x)]
  exact coord_integral (fun x => ∫ y, J x y)

end GaussianChannel

open GaussianChannel in
theorem solution (η u v : ℝ) (m n d : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Fin m → EuclideanSpace ℝ (Fin d)) (V : Fin n → EuclideanSpace ℝ (Fin d))
    (hU : ∀ i, ‖U i‖=1) (hV : ∀ j, ‖V j‖=1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (∑ i, ∑ j, A i j*cqCorr η u v (r*inner ℝ (U i) (V j))) ≤ Real.pi/2*optValue A := by
  obtain ⟨D,P,Q,S,T,hp,hq,hs,ht,hpq,hst⟩ := CubicFeatures.features U V hU hV u v r hr.le hr1.le
  let μ := (stdGaussian (EuclideanSpace ℝ (Fin D))).prod (stdGaussian (EuclideanSpace ℝ (Fin D)))
  let f := partition η u v
  let g := partition' η u v
  let F (i : Fin m) (z : EuclideanSpace ℝ (Fin D) × EuclideanSpace ℝ (Fin D)) := f (inner ℝ (P i) z.1,inner ℝ (S i) z.2)
  let G (j : Fin n) (z : EuclideanSpace ℝ (Fin D) × EuclideanSpace ℝ (Fin D)) := g (inner ℝ (Q j) z.1,inner ℝ (T j) z.2)
  have hF (i z) : F i z=1 ∨ F i z= -1 := sign_p η u v _
  have hG (j z) : G j z=1 ∨ G j z= -1 := sign_p' η u v _
  have hFm (i) : Measurable (F i) := (partition_m η u v).comp (by fun_prop)
  have hGm (j) : Measurable (G j) := (partition_m' η u v).comp (by fun_prop)
  have hfb (z) : ‖f z‖ ≤ 1 := by rcases sign_p η u v z with e|e <;> change ‖partition η u v z‖ ≤ _ <;> simp [e]
  have hgb (z) : ‖g z‖ ≤ 1 := by rcases sign_p' η u v z with e|e <;> change ‖partition' η u v z‖ ≤ _ <;> simp [e]
  have hcoef (i j) : cqCorr η u v (r*inner ℝ (U i) (V j)) = Real.pi/2*∫ z, F i z*G j z ∂μ := by
    have hxy : |r*inner ℝ (U i) (V j)| < 1 := by
      rw [abs_mul,abs_of_pos hr]
      have h : |inner ℝ (U i) (V j)| ≤ 1 := by simpa only [hU,hV,mul_one] using abs_real_inner_le_norm (U i) (V j)
      exact (mul_le_of_le_one_right hr.le h).trans_lt hr1
    rw [corr_pair]
    apply congrArg (fun x : ℝ => Real.pi/2*x)
    exact (paired_expectation (P i) (Q j) (S i) (T j) (hp i) (hq j) (hs i) (ht j)
      ((rho_contracts _ _ _ hxy.le).trans_lt hxy) hxy (hpq i j) (hst i j)
      (partition_m η u v) (partition_m' η u v) hfb hgb).symm
  have hInt (i j) : Integrable (fun z => F i z*G j z) μ := by
    apply (integrable_const (μ:=μ) (c:=(1:ℝ))).mono'
    · exact ((hFm i).mul (hGm j)).aestronglyMeasurable
    · filter_upwards with z
      rcases hF i z with e|e <;> rcases hG j z with e'|e' <;> simp [e,e']
  let J i j z := A i j*(F i z*G j z)
  have hJ (i j) : Integrable (J i j) μ := (hInt i j).const_mul _
  have hrow (i : Fin m) : Integrable (fun z => ∑ j, J i j z) μ := integrable_finsetSum _ (fun j _ => hJ i j)
  have hall : Integrable (fun z => ∑ i, ∑ j, J i j z) μ := integrable_finsetSum _ (fun i _ => hrow i)
  have point (z) : (∑ i, ∑ j, J i j z) ≤ optValue A := by
    apply le_csSup (optSet_bdd A)
    exact ⟨fun i => F i z,fun j => G j z,fun i => hF i z,fun j => hG j z,by simp only [J,mul_assoc]⟩
  have hopt : (∫ z, ∑ i, ∑ j, J i j z ∂μ) ≤ optValue A := by
    simpa using integral_mono hall (integrable_const (μ:=μ) (c:=optValue A)) point
  calc _ = Real.pi/2*(∫ z, ∑ i, ∑ j, J i j z ∂μ) := by
          rw [integral_finsetSum _ (fun i _ => hrow i),Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_finsetSum _ (fun j _ => hJ i j),Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          dsimp only [J]
          rw [hcoef,integral_const_mul]
          ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hopt (by positivity)

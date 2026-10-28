-- Prove2me | solution 1 for OAI.C11InteriorRegularity.holder_hessian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:15:33.531721+00:00
-- url     : https://prove2.me/submissions/d5e0ea4f-d842-407b-b86d-ab1fd393c9f5

import Mathlib
import Definitions.Def_OAIW2LB000

section
-- module Solutions.OAIW2_LogBM.LogVolume_BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology NNReal

open Set Filter
open scoped Topology NNReal

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

open scoped ENNReal

open scoped InnerProductSpace ContDiff Topology
open scoped ENNReal

open Set MeasureTheory Filter
open scoped ENNReal Topology

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace RadialBarrier
section
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gradient_radial {f f' : ℝ → ℝ} (hd : ∀ t≥0, HasDerivAt f (f' t) t) (x : E) :
    gradient (fun x : E => f (‖x‖^2)) x=(2*f' (‖x‖^2)) • x := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  have hh := (hd _ (sq_nonneg _)).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [show (fun x : E => f (‖x‖^2))=f ∘ (fun x : E => ‖x‖^2) from rfl,hh.fderiv]
  ext v
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply,real_inner_smul_left]
  ring

lemma hessian_radial {f f' f'' : ℝ → ℝ}
    (hd : ∀ t≥0, HasDerivAt f (f' t) t)
    (hd' : ∀ t≥0, HasDerivAt f' (f'' t) t) (x v : E) :
    fderiv ℝ (gradient (fun x : E => f (‖x‖^2))) x v=
      (2*f' (‖x‖^2)) • v+(4*f'' (‖x‖^2)*⟪x,v⟫_ℝ) • x := by
  have he : gradient (fun x : E => f (‖x‖^2))=fun x => (2*f' (‖x‖^2)) • x :=
    funext (gradient_radial hd)
  rw [he]
  have hh := (((hd' _ (sq_nonneg _)).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_smul (2:ℝ)).smul (hasFDerivAt_id x)
  rw [show (fun x : E => (2*f' (‖x‖^2)) • x)=((2:ℝ) • (f' ∘ (fun x : E => ‖x‖^2))) • id from rfl,
    hh.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
    Pi.smul_apply,Function.comp_apply,smul_eq_mul,innerSL_apply_apply,id_eq]
  congr 1
  ring_nf

lemma profile_deriv (p t : ℝ) (ht : 0≤t) :
    HasDerivAt (fun t : ℝ => (1+t)^(-p)) (-p*(1+t)^(-p-1)) t := by
  have hs : 0<1+t := by linarith
  simpa only [one_mul,id_eq] using ((hasDerivAt_id t).const_add 1).rpow_const (p:=(-p)) (Or.inl hs.ne')

lemma profile_second (p t : ℝ) (ht : 0≤t) :
    HasDerivAt (fun t : ℝ => -p*(1+t)^(-p-1)) (p*(p+1)*(1+t)^(-p-2)) t := by
  have hs : 0<1+t := by linarith
  have hh := ((((hasDerivAt_id t).const_add 1).rpow_const (p:=(-p-1)) (Or.inl hs.ne')).const_mul (-p))
  simp only [id_eq,one_mul] at hh
  convert hh using 1 <;> first | rfl | ring_nf

lemma hessian_power (p : ℝ) (x v : E) :
    fderiv ℝ (gradient (fun x : E => (1+‖x‖^2)^(-p))) x v =
      (-2*p*(1+‖x‖^2)^(-p-1)) • v+
        (4*p*(p+1)*(1+‖x‖^2)^(-p-2)*⟪x,v⟫_ℝ) • x := by
  rw [hessian_radial (profile_deriv p) (profile_second p)]
  congr 1 <;> congr 1 <;> ring

end

section
open Set
open scoped InnerProductSpace Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
lemma matrix_rank_one (b : OrthonormalBasis ι ℝ E) (x : E) {A : E →L[ℝ] E} {a c : ℝ}
    (hA : ∀ v, A v=a • v+(c*⟪x,v⟫_ℝ) • x) :
    LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap=
      a • (1:Matrix ι ι ℝ)+c • Matrix.vecMulVec (b.repr x).ofLp (b.repr x).ofLp := by
  ext i j
  rw [LinearMap.toMatrix_apply']
  change b.toBasis.repr (A (b.toBasis j)) i=_
  rw [hA,map_add,map_smul,map_smul]
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,Matrix.add_apply,
    Matrix.smul_apply,Matrix.vecMulVec_apply,Module.Basis.repr_self, Finsupp.single_apply]
  simp only [b.coe_toBasis_repr_apply,b.repr_apply_apply,b.coe_toBasis]
  by_cases he : i=j
  · subst j
    simp only [ite_true,Matrix.one_apply_eq]
    rw [real_inner_comm x (b i)]
    ring
  · simp only [Ne.symm he,ite_false,Matrix.one_apply_ne he,mul_zero,zero_add]
    rw [real_inner_comm x (b j)]
    ring

lemma trace_hessian_power (b : OrthonormalBasis ι ℝ E) (A : Matrix ι ι ℝ) (p : ℝ) (x : E) :
    (A*LinearMap.toMatrix b.toBasis b.toBasis
      (fderiv ℝ (gradient (fun x : E => (1+‖x‖^2)^(-p))) x).toLinearMap).trace=
      (-2*p*(1+‖x‖^2)^(-p-1))*A.trace+
        (4*p*(p+1)*(1+‖x‖^2)^(-p-2))*
          ((b.repr x).ofLp ⬝ᵥ A.mulVec (b.repr x).ofLp) := by
  rw [matrix_rank_one b x (hessian_power p x),Matrix.mul_add,Matrix.mul_smul,
    Matrix.mul_one,Matrix.mul_smul,Matrix.mul_vecMulVec,Matrix.trace_add,
    Matrix.trace_smul,Matrix.trace_smul,Matrix.trace_vecMulVec,dotProduct_comm]
  rfl

omit [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma coord_dot_self (b : OrthonormalBasis ι ℝ E) (x : E) :
    (b.repr x).ofLp ⬝ᵥ (b.repr x).ofLp=‖x‖^2 := by
  have hh := b.repr.inner_map_map x x
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,real_inner_self_eq_norm_sq] using hh

omit [FiniteDimensional ℝ E] in
lemma quadratic_lower (b : OrthonormalBasis ι ℝ E) {A : Matrix ι ι ℝ} {ell : ℝ}
    (hA : (A-ell • (1:Matrix ι ι ℝ)).PosSemidef) (x : E) :
    ell*‖x‖^2≤(b.repr x).ofLp ⬝ᵥ A.mulVec (b.repr x).ofLp := by
  have hh := hA.dotProduct_mulVec_nonneg (b.repr x).ofLp
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul,coord_dot_self] at hh
  linarith

end

open Set
open scoped InnerProductSpace Matrix ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma power_shift (p t : ℝ) (ht : 0≤t) : (1+t)^(-p-1)=(1+t)^(-p-2)*(1+t) := by
  calc
    _ = (1+t)^((-p-2)+1) := by congr 1; ring
    _ = _ := by rw [Real.rpow_add (by linarith),Real.rpow_one]

lemma norm_gradient_profile {p : ℝ} (hp : 0≤p) (x : E) :
    ‖gradient (profile p) x‖=2*p*(1+‖x‖^2)^(-p-1)*‖x‖ := by
  unfold profile
  rw [gradient_radial (profile_deriv p),norm_smul,Real.norm_eq_abs]
  have hh : 0≤2*p*(1+‖x‖^2)^(-p-1) := by positivity
  rw [show 2*(-p*(1+‖x‖^2)^(-p-1))=-(2*p*(1+‖x‖^2)^(-p-1)) by ring,abs_neg,abs_of_nonneg hh]

lemma trace_lower (b : OrthonormalBasis ι ℝ E) {A : Matrix ι ι ℝ} {p ell T : ℝ}
    (hp : 0≤p) (hA : (A-ell • (1:Matrix ι ι ℝ)).PosSemidef)
    (hT : A.trace≤T) (x : E) :
    2*p*(1+‖x‖^2)^(-p-2)*(2*(p+1)*ell*‖x‖^2-T*(1+‖x‖^2)) ≤
      (A*LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient (profile p)) x).toLinearMap).trace := by
  unfold profile
  rw [trace_hessian_power]
  have hq := quadratic_lower b hA x
  have hs : 0≤(1+‖x‖^2)^(-p-2) := Real.rpow_nonneg (by positivity) _
  have ht := mul_le_mul_of_nonpos_left hT (show -2*p*(1+‖x‖^2)^(-p-1)≤0 by
    have hpos : 0≤2*p*(1+‖x‖^2)^(-p-1) := by positivity
    linarith)
  have hq' := mul_le_mul_of_nonneg_left hq (show 0≤4*p*(p+1)*(1+‖x‖^2)^(-p-2) by positivity)
  rw [power_shift p _ (sq_nonneg _)] at ht ⊢
  nlinarith

lemma profile_coarse_bound (b : OrthonormalBasis ι ℝ E) {A : Matrix ι ι ℝ} {p ell T B R : ℝ}
    (hp : 0≤p) (hell : 0≤ell) (hTn : 0≤T) (hB : 0≤B)
    (hA : (A-ell • (1:Matrix ι ι ℝ)).PosSemidef) (hT : A.trace≤T)
    (x : E) (hx : ‖x‖≤R) :
    -2*p*(T+B*R) ≤
      (A*LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient (profile p)) x).toLinearMap).trace-
        B*‖gradient (profile p) x‖ := by
  have hq := quadratic_lower b hA x
  have hqn : 0≤(b.repr x).ofLp ⬝ᵥ A.mulVec (b.repr x).ofLp :=
    (mul_nonneg hell (sq_nonneg _)).trans hq
  have hs : 0≤(1+‖x‖^2)^(-p-1) := Real.rpow_nonneg (by positivity) _
  have hs1 : (1+‖x‖^2)^(-p-1)≤1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (show 1≤1+‖x‖^2 by linarith [sq_nonneg ‖x‖]) (show -p-1≤0 by linarith)
  have hh : 0≤4*p*(p+1)*(1+‖x‖^2)^(-p-2)*
      ((b.repr x).ofLp ⬝ᵥ A.mulVec (b.repr x).ofLp) := by positivity
  have ht := mul_le_mul_of_nonpos_left hT (show -2*p*(1+‖x‖^2)^(-p-1)≤0 by
    have hpos : 0≤2*p*(1+‖x‖^2)^(-p-1) := by positivity
    linarith)
  have hb : B*(2*p*(1+‖x‖^2)^(-p-1)*‖x‖)≤B*(2*p*R) := by
    apply mul_le_mul_of_nonneg_left _ hB
    calc
      _ ≤ 2*p*1*R := by gcongr
      _ = _ := by ring
  have ht' := mul_le_mul_of_nonneg_left hs1 (show 0≤2*p*T by positivity)
  rw [norm_gradient_profile hp]
  unfold profile
  rw [trace_hessian_power]
  nlinarith

lemma profile_positive_annulus (b : OrthonormalBasis ι ℝ E)
    {A : Matrix ι ι ℝ} {p ell T B a R : ℝ}
    (hp : 0≤p) (hell : 0≤ell) (hTn : 0≤T) (hB : 0≤B) (ha : 0≤a)
    (hA : (A-ell • (1:Matrix ι ι ℝ)).PosSemidef) (hT : A.trace≤T)
    (hP : T*(1+R^2)+B*(1+R^2)*R+1 ≤ 2*p*ell*a^2)
    (x : E) (hlo : a≤‖x‖) (hhi : ‖x‖≤R) :
    2*p*(1+R^2)^(-p-2) ≤
      (A*LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient (profile p)) x).toLinearMap).trace-
        B*‖gradient (profile p) x‖ := by
  have hlow := trace_lower b hp hA hT x
  rw [norm_gradient_profile hp,power_shift p _ (sq_nonneg _)]
  have hsqlo : a^2≤‖x‖^2 := sq_le_sq₀ ha (norm_nonneg x) |>.mpr hlo
  have hsqhi : ‖x‖^2≤R^2 := sq_le_sq₀ (norm_nonneg x) ((norm_nonneg x).trans hhi) |>.mpr hhi
  have h1 := mul_le_mul_of_nonneg_left hsqlo (show 0≤2*p*ell by positivity)
  have h2 := mul_le_mul_of_nonneg_left (add_le_add_left hsqhi 1) hTn
  have h3 : B*(1+‖x‖^2)*‖x‖≤B*(1+R^2)*R := by gcongr
  have hbr : 1≤2*(p+1)*ell*‖x‖^2-T*(1+‖x‖^2)-B*(1+‖x‖^2)*‖x‖ := by
    nlinarith [mul_nonneg hell (sq_nonneg ‖x‖)]
  have hs : 0≤2*p*(1+‖x‖^2)^(-p-2) := by positivity
  have hbr' := mul_le_mul_of_nonneg_left hbr hs
  have hm := Real.rpow_le_rpow_of_nonpos (show 0<1+‖x‖^2 by positivity)
    (show 1+‖x‖^2≤1+R^2 by linarith) (show -p-2≤0 by linarith)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0≤2*p by positivity)
  nlinarith

end RadialBarrier

namespace SmoothCompactify
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gradient_contDiff {u : E → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (gradient u) := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (hu.fderiv_right (m:=∞) (by simp))

lemma gradient_hasCompactSupport {u : E → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (gradient u) := by
  exact (hu.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ E).symm)

lemma gradient_lipschitz {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ∃ L : ℝ≥0, LipschitzWith L (gradient u) := by
  have hd := gradient_contDiff hu
  obtain ⟨B,hB⟩ := ((hd.fderiv_right (m:=0) (by simp)).continuous.norm).bddAbove_range_of_hasCompactSupport
    (((gradient_hasCompactSupport hc).fderiv ℝ).norm)
  have hn : 0≤B := (norm_nonneg (fderiv ℝ (gradient u) 0)).trans (hB (mem_range_self 0))
  refine ⟨⟨B,hn⟩,lipschitzWith_of_nnnorm_fderiv_le (hd.differentiable (by simp)) ?_⟩
  intro x
  exact hB (mem_range_self x)

theorem exists_extension {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {R : ℝ} (hR : 0≤R) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∃ L : ℝ≥0, LipschitzWith L (gradient ψ)) ∧
      ∀ x∈closedBall (0:E) R, ψ =ᶠ[𝓝 x] u := by
  let χ : ContDiffBump (0:E) := ⟨R+1,R+2,by linarith,by linarith⟩
  let ψ : E → ℝ := fun x => χ x*u x
  have hd : ContDiff ℝ ∞ ψ := χ.contDiff.mul hu
  have hc : HasCompactSupport ψ := χ.hasCompactSupport.mul_right
  refine ⟨ψ,hd,hc,gradient_lipschitz hd hc,?_⟩
  intro x hx
  have hxb : x∈ball (0:E) (R+1) := closedBall_subset_ball (by linarith) hx
  filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
  change χ y*u y=u y
  rw [χ.one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hy).le),one_mul]

end SmoothCompactify

namespace RadialBarrier
open Set Filter Metric
open scoped Topology InnerProductSpace Matrix ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
lemma profile_contDiff (p : ℝ) : ContDiff ℝ ∞ (profile p : E → ℝ) := by
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne (fun x => by positivity)

lemma gradient_affine {u : E → ℝ} (hu : Differentiable ℝ u) (K c : ℝ) :
    gradient (fun x => K*(u x-c))=fun x => K • gradient u x := by
  funext x
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [map_smul,toDual_gradient,toDual_gradient]
  have hh := ((hu x).hasFDerivAt.sub_const c).const_mul K
  simpa only [smul_eq_mul] using hh.fderiv

lemma hessian_affine {u : E → ℝ} (hu : Differentiable ℝ u)
    (hdu : Differentiable ℝ (gradient u)) (K c : ℝ) (x : E) :
    fderiv ℝ (gradient (fun x => K*(u x-c))) x=K • fderiv ℝ (gradient u) x := by
  rw [gradient_affine hu]
  exact fderiv_const_smul (hdu x) K

lemma trace_affine (b : OrthonormalBasis ι ℝ E) {u : E → ℝ}
    (hu : Differentiable ℝ u) (hdu : Differentiable ℝ (gradient u))
    (K c : ℝ) (A : Matrix ι ι ℝ) (x : E) :
    (A*LinearMap.toMatrix b.toBasis b.toBasis
      (fderiv ℝ (gradient (fun x => K*(u x-c))) x).toLinearMap).trace=
      K*(A*LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient u) x).toLinearMap).trace := by
  rw [hessian_affine hu hdu,ContinuousLinearMap.toLinearMap_smul,map_smul,Matrix.mul_smul,
    Matrix.trace_smul,smul_eq_mul]

theorem exists_elliptic_barrier (b : OrthonormalBasis ι ℝ E)
    {ell T B a q R r : ℝ} (hell : 0<ell) (hT : 0≤T) (hB : 0≤B)
    (ha : 0<a) (hq : 0≤q) (hqR : q<R) (hr : 0≤r) :
    ∃ (ψ : E → ℝ) (L : ℝ≥0) (M F : ℝ), ContDiff ℝ ∞ ψ ∧
      LipschitzWith L (gradient ψ) ∧ 1<M ∧ 0<F ∧
      (∀ x∈closedBall (0:E) R, ψ x≤M) ∧
      (∀ x∈frontier (closedBall (0:E) R), ψ x≤0) ∧
      (∀ x∈closedBall (0:E) q, 2≤ψ x) ∧
      ∀ (x : E) (A : Matrix ι ι ℝ), x∈closedBall (0:E) R →
        (A-ell • (1:Matrix ι ι ℝ)).PosSemidef → A.trace≤T →
        1+B*r-(ball (0:E) a).indicator (fun _ => F) x ≤
          (A*LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient ψ) x).toLinearMap).trace-
            B*‖gradient ψ x‖ := by
  classical
  have hR : 0<R := hq.trans_lt hqR
  let N := T*(1+R^2)+B*(1+R^2)*R+1
  have hN : 0<N := by dsimp [N]; positivity
  let p := 1+N/(2*ell*a^2)
  have hden : 0<2*ell*a^2 := by positivity
  have hp : 0<p := by dsimp [p]; positivity
  have hP : N≤2*p*ell*a^2 := by
    have he := div_mul_cancel₀ N hden.ne'
    dsimp [p]
    nlinarith
  let delta := (1+q^2)^(-p)-(1+R^2)^(-p)
  have hdelta : 0<delta := by
    apply sub_pos.mpr
    exact Real.rpow_lt_rpow_of_neg (by positivity)
      (by nlinarith) (neg_neg_of_pos hp)
  let margin := 2*p*(1+R^2)^(-p-2)
  have hmargin : 0 < margin := by dsimp [margin]; positivity
  let K := 2/delta+(1+B*r)/margin+1
  have hK : 0<K := by dsimp [K]; positivity
  have hKh : 2≤K*delta := by
    have he := div_mul_cancel₀ (2:ℝ) hdelta.ne'
    have hn : 0≤((1+B*r)/margin+1)*delta := by positivity
    dsimp [K]
    nlinarith
  have hKm : 1+B*r≤K*margin := by
    have he := div_mul_cancel₀ (1+B*r) hmargin.ne'
    have hn : 0≤(2/delta+1)*margin := by positivity
    dsimp [K]
    nlinarith
  let u : E → ℝ := fun x => K*(profile p x-(1+R^2)^(-p))
  have hd : ContDiff ℝ ∞ (profile p : E → ℝ) := profile_contDiff p
  have hu : ContDiff ℝ ∞ u := contDiff_const.mul (hd.sub contDiff_const)
  have hdg := (SmoothCompactify.gradient_contDiff hd).differentiable (by simp)
  obtain ⟨ψ,hψ,hψc,⟨L,hL⟩,heq⟩ := SmoothCompactify.exists_extension hu hR.le
  let M := K+1
  let F := 2*p*K*(T+B*R)+1+B*r+1
  have huval (x : E) (hx : x∈closedBall (0:E) R) : ψ x=u x := (heq x hx).eq_of_nhds
  have hugrad (x : E) (hx : x∈closedBall (0:E) R) : gradient ψ x=K • gradient (profile p) x := by
    rw [(heq x hx).gradient_eq]
    exact congrFun (gradient_affine (hd.differentiable (by simp)) K ((1+R^2)^(-p))) x
  have hut (x : E) (hx : x∈closedBall (0:E) R) (A : Matrix ι ι ℝ) :
      (A*LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient ψ) x).toLinearMap).trace=
      K*(A*LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient (profile p)) x).toLinearMap).trace := by
    rw [(heq x hx).gradient.fderiv_eq]
    exact trace_affine b (hd.differentiable (by simp)) hdg K ((1+R^2)^(-p)) A x
  refine ⟨ψ,L,M,F,hψ,hL,by dsimp [M]; linarith,by dsimp [F]; positivity,?_,?_,?_,?_⟩
  · intro x hx
    rw [huval x hx]
    have hpr : profile p x≤1 := by
      simpa only [profile,Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
        (show 1≤1+‖x‖^2 by nlinarith [sq_nonneg ‖x‖]) (neg_nonpos.mpr hp.le)
    have hn : 0≤(1+R^2)^(-p) := by positivity
    have hh := mul_le_mul_of_nonneg_left (show profile p x-(1+R^2)^(-p)≤1 by linarith) hK.le
    dsimp [u,M]
    linarith
  · intro x hx
    have hxR : ‖x‖=R := by simpa only [frontier_closedBall (0:E) hR.ne',mem_sphere,dist_zero_right] using hx
    have hxC : x∈closedBall (0:E) R := by simpa only [mem_closedBall,dist_zero_right,hxR] using (le_refl R)
    rw [huval x hxC]
    simp only [u,profile,hxR,sub_self,mul_zero,le_refl]
  · intro x hx
    have hxq : ‖x‖≤q := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hxC : x∈closedBall (0:E) R := mem_closedBall.mpr (by simpa using hxq.trans hqR.le)
    rw [huval x hxC]
    have hpr : (1+q^2)^(-p)≤profile p x := Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith [norm_nonneg x]) (neg_nonpos.mpr hp.le)
    have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hpr ((1+R^2)^(-p))) hK.le
    exact hKh.trans hh
  · intro x A hx hA hAT
    have hxR : ‖x‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hx
    rw [hut x hx A,hugrad x hx,norm_smul,Real.norm_eq_abs,abs_of_pos hK]
    by_cases hxa : x∈ball (0:E) a
    · rw [indicator_of_mem hxa]
      have hh := profile_coarse_bound b hp.le hell.le hT hB hA hAT x hxR
      have hh' := mul_le_mul_of_nonneg_left hh hK.le
      dsimp [F]
      nlinarith
    · rw [indicator_of_notMem hxa,sub_zero]
      have hxa' : a≤‖x‖ := le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hxa)
      have hh := profile_positive_annulus b hp.le hell.le hT hB ha.le hA hAT hP x hxa' hxR
      have hh' := mul_le_mul_of_nonneg_left hh hK.le
      exact hKm.trans (by dsimp [margin] at *; nlinarith)

end RadialBarrier

namespace ABPGeometry
open Set Filter Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ENNReal

lemma second_nonpos_at_localMax {g g' : ℝ → ℝ} {a : ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hh : HasDerivAt g' a 0)
    (hm : IsLocalMax g 0) : a ≤ 0 := by
  by_contra he
  have ha : 0<a := lt_of_not_ge he
  have hzero : g' 0=0 := hm.hasDerivAt_eq_zero (hg 0)
  have hp : ∀ᶠ t in 𝓝[>] (0:ℝ), 0<t⁻¹*(g' t) := by
    simpa only [zero_add,hzero,sub_zero,smul_eq_mul] using
      hh.tendsto_slope_zero_right.eventually (Ioi_mem_nhds ha)
  obtain ⟨r,hr,hpos⟩ := Metric.mem_nhdsWithin_iff.mp hp
  obtain ⟨s,hs,hmax⟩ := Metric.mem_nhds_iff.mp hm
  let t := min r s/2
  have ht : 0<t := by dsimp only [t]; positivity
  have htr : t<r := by dsimp only [t]; have := min_le_left r s; linarith
  have hts : t<s := by dsimp only [t]; have := min_le_right r s; linarith
  have hgt : g t≤g 0 := hmax (by simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using hts)
  obtain ⟨c,hc,hceq⟩ := exists_hasDerivAt_eq_slope g g' ht
    (show ContinuousOn g (Icc 0 t) from (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).continuousOn)
    (fun c _ => hg c)
  have hpc : 0<c⁻¹*g' c := hpos ⟨by
    simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hc.1] using hc.2.trans htr,hc.1⟩
  have hgc : g' c≤0 := by rw [hceq]; exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hgt) (by linarith)
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.1.le) hgc)) hpc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma localMax_hessian_nonpos {u : E → ℝ} (hu : Differentiable ℝ u) {x : E}
    (hH : DifferentiableAt ℝ (gradient u) x) (hm : IsLocalMax u x) (v : E) :
    ⟪fderiv ℝ (gradient u) x v,v⟫_ℝ ≤ 0 := by
  let g := fun t : ℝ => u (x+t • v)
  let g' := fun t : ℝ => ⟪gradient u (x+t • v),v⟫_ℝ
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => x+t • v) v t := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    have hh := (hu _).hasFDerivAt.comp_hasDerivAt t (hline t)
    simpa only [g,g',Function.comp_def,← toDual_gradient,InnerProductSpace.toDual_apply_apply] using hh
  have hd : HasDerivAt g' ⟪fderiv ℝ (gradient u) x v,v⟫_ℝ 0 := by
    have hd0 : HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) (x+(0:ℝ) • v) := by simpa using hH.hasFDerivAt
    have hh := hd0.comp_hasDerivAt 0 (hline 0)
    have hh' := hh.inner ℝ (hasDerivAt_const 0 v)
    simpa only [g',Function.comp_def,inner_zero_right,zero_add] using hh'
  have hgm : IsLocalMax g 0 := by
    have hl : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul,add_zero] using (hline 0).continuousAt.tendsto
    change ∀ᶠ t in 𝓝 0, g t≤g 0
    simpa only [g,zero_smul,add_zero] using hl.eventually hm
  exact second_nonpos_at_localMax hg hd hgm

lemma upperContact_measurable [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}
    (hu : Continuous u) (hg : Continuous (gradient u)) (C : Set E) :
    MeasurableSet (upperContact u C) := by
  have hc : IsClosed {x | ∀ y ∈ C, u y≤u x+⟪gradient u x,y-x⟫_ℝ} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun y => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (hu.add (hg.inner (continuous_const.sub continuous_id)))))
  exact isOpen_interior.measurableSet.inter hc.measurableSet

lemma small_slope_in_contact_image {u : E → ℝ} (hu : Differentiable ℝ u)
    {C : Set E} (hC : IsCompact C) {x : E} (hx : x∈C) {D : ℝ}
    (hD : ∀ y ∈ C, ‖y-x‖≤D) (hbd : ∀ y ∈ frontier C, u y≤0)
    {p : E} (hp : ‖p‖*D<u x) : p ∈ gradient u '' upperContact u C := by
  obtain ⟨y,hy,hmax⟩ := hC.exists_isMaxOn ⟨x,hx⟩
    ((hu.continuous.sub (continuous_const.inner continuous_id)).continuousOn)
  have hyx : u x-⟪p,x⟫_ℝ≤u y-⟪p,y⟫_ℝ := hmax hx
  have hyint : y∈interior C := by
    by_contra he
    have hyfr : y∈frontier C := by
      rw [frontier_eq_closure_inter_closure,closure_compl]
      exact ⟨subset_closure hy,he⟩
    have hbd' := hbd y hyfr
    have hip : -⟪p,y-x⟫_ℝ≤‖p‖*D := by
      calc
        _ ≤ |⟪p,y-x⟫_ℝ| := neg_le_abs _
        _ ≤ ‖p‖*‖y-x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖p‖*D := mul_le_mul_of_nonneg_left (hD y hy) (norm_nonneg p)
    rw [inner_sub_right] at hip
    linarith
  have hloc : IsLocalMax (fun z => u z-⟪p,z⟫_ℝ) y := by
    filter_upwards [isOpen_interior.mem_nhds hyint] with z hz
    exact hmax (interior_subset hz)
  have hgrad : gradient u y=p := by
    have hh := hloc.hasFDerivAt_eq_zero ((hu y).hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt)
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [toDual_gradient]
    exact sub_eq_zero.mp hh
  refine ⟨y,⟨hyint,?_⟩,hgrad⟩
  intro z hz
  have hh : u z-⟪p,z⟫_ℝ≤u y-⟪p,y⟫_ℝ := hmax hz
  rw [hgrad,inner_sub_right]
  linarith

lemma gradient_sub_inner {u : E → ℝ} (hu : Differentiable ℝ u) (p x : E) :
    gradient (fun y => u y-⟪p,y⟫_ℝ) x=gradient u x-p := by
  apply (InnerProductSpace.toDual ℝ E).injective
  have hh : HasFDerivAt (fun y => u y-⟪p,y⟫_ℝ) (fderiv ℝ u x-innerSL ℝ p) x :=
    (hu x).hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt
  rw [toDual_gradient,hh.fderiv]
  simp only [map_sub,toDual_gradient]
  rfl

lemma hessian_isSymmetric {u : E → ℝ} (hu : Differentiable ℝ u) {x : E}
    (hH : DifferentiableAt ℝ (gradient u) x) :
    (fderiv ℝ (gradient u) x).toLinearMap.IsSymmetric := by
  intro v w
  have hh := second_derivative_symmetric (fun y => (hu y).hasGradientAt.hasFDerivAt)
    ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.hasFDerivAt.comp x hH.hasFDerivAt) v w
  change ⟪(fderiv ℝ (gradient u) x) v,w⟫_ℝ=⟪(fderiv ℝ (gradient u) x) w,v⟫_ℝ at hh
  exact hh.trans (real_inner_comm _ _)

lemma contact_hessian_negative {u : E → ℝ} (hu : Differentiable ℝ u) {C : Set E}
    {x : E} (hx : x∈upperContact u C) (hH : DifferentiableAt ℝ (gradient u) x) :
    (-(fderiv ℝ (gradient u) x)).toLinearMap.IsPositive := by
  refine ⟨?_,fun v => ?_⟩
  · intro v w
    simpa only [ContinuousLinearMap.toLinearMap_neg,LinearMap.neg_apply,inner_neg_left,inner_neg_right] using
      congrArg Neg.neg (hessian_isSymmetric hu hH v w)
  let g := fun y => u y-⟪gradient u x,y⟫_ℝ
  have hg : Differentiable ℝ g := hu.sub (innerSL ℝ (gradient u x)).differentiable
  have hge : gradient g=fun y => gradient u y-gradient u x :=
    funext (gradient_sub_inner hu (gradient u x))
  have hgH : HasFDerivAt (gradient g) (fderiv ℝ (gradient u) x) x := by
    rw [hge]
    exact hH.hasFDerivAt.sub_const _
  have hm : IsLocalMax g x := by
    filter_upwards [isOpen_interior.mem_nhds hx.1] with y hy
    have hh := hx.2 y (interior_subset hy)
    rw [inner_sub_right] at hh
    dsimp only [g]
    linarith
  have hh := localMax_hessian_nonpos hg hgH.differentiableAt hm v
  rw [hgH.fderiv] at hh
  simpa only [ContinuousLinearMap.toLinearMap_neg,LinearMap.neg_apply,ContinuousLinearMap.coe_coe,
    inner_neg_left,RCLike.re_to_real,neg_nonneg] using hh

lemma small_slope_in_positive_contact_image {u : E → ℝ} (hu : Differentiable ℝ u)
    {C : Set E} (hC : IsCompact C) {x : E} (hx : x∈C) {D : ℝ}
    (hD : ∀ y ∈ C, ‖y-x‖≤D) (hbd : ∀ y ∈ frontier C, u y≤0)
    {p : E} (hp : ‖p‖*D<u x) :
    p∈gradient u '' (upperContact u C ∩ {y | 0<u y}) := by
  obtain ⟨y,hy,hpy⟩ := small_slope_in_contact_image hu hC hx hD hbd hp
  refine ⟨y,⟨hy,?_⟩,hpy⟩
  have hh := hy.2 x hx
  rw [hpy] at hh
  have hb : ⟪p,x-y⟫_ℝ ≤ ‖p‖*D := calc
    _ ≤ ‖p‖*‖x-y‖ := real_inner_le_norm _ _
    _ = ‖p‖*‖y-x‖ := by rw [norm_sub_rev]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hD y (interior_subset hy.1)) (norm_nonneg _)
  change 0<u y
  linarith

variable [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma lipschitz_image_null {L : ℝ≥0} {f : E → E} (hl : LipschitzWith L f)
    {s : Set E} (hs : μ s=0) : μ (f '' s)=0 := by
  have ha : μ ≪ μH[Module.finrank ℝ E] := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hb : μH[Module.finrank ℝ E] ≪ μ := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply ha
  apply le_antisymm _ (zero_le)
  simpa only [hb hs,mul_zero] using hl.hausdorffMeasure_image_le
    (d:=(Module.finrank ℝ E : ℝ)) (by positivity) s

lemma lipschitz_area_upper_bound {L : ℝ≥0} {f : E → E} (hl : LipschitzWith L f)
    {s : Set E} (hs : MeasurableSet s) :
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
  let D := {x | DifferentiableAt ℝ f x}
  have hD : MeasurableSet D := measurableSet_of_differentiableAt _ _
  have hn : μ (f '' (s\D))=0 := lipschitz_image_null μ hl
    (measure_mono_null (sdiff_subset_compl s D) (ae_iff.mp (hl.ae_differentiableAt (μ:=μ))))
  have hh := addHaar_image_le_lintegral_abs_det_fderiv μ (hs.inter hD)
    (f':=fderiv ℝ f) (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt)
  calc
    μ (f '' s) ≤ μ (f '' (s∩D))+μ (f '' (s\D)) := by
      apply (measure_mono (image_mono (show s⊆(s∩D)∪(s\D) from by
        intro x hx; by_cases hd : x∈D
        · exact Or.inl ⟨hx,hd⟩
        · exact Or.inr ⟨hx,hd⟩))).trans
      rw [image_union]
      exact measure_union_le _ _
    _ ≤ ∫⁻ x in s∩D, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by simpa only [hn,add_zero] using hh
    _ ≤ _ := lintegral_mono' (Measure.restrict_mono inter_subset_left le_rfl) (fun _ => le_rfl)

end ABPGeometry

namespace ABPMatrix
open Matrix
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_nonneg {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨Q,hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hQ]
  change 0 ≤ (Qᴴ * Q * B).trace
  rw [← Matrix.trace_mul_cycle Q B Qᴴ]
  exact (hB.mul_mul_conjTranspose_same Q).trace_nonneg

lemma det_le_trace_pow {B : Matrix ι ι ℝ} (hB : B.PosSemidef) :
    B.det ≤ B.trace^Fintype.card ι := by
  rw [hB.isHermitian.det_eq_prod_eigenvalues]
  calc
    ∏ i, hB.isHermitian.eigenvalues i ≤ ∏ _i : ι, B.trace := by
      apply Finset.prod_le_prod
      · intro i _; exact hB.eigenvalues_nonneg i
      · intro i _
        rw [hB.isHermitian.trace_eq_sum_eigenvalues]
        exact Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ]

lemma det_le_of_trace {A B : Matrix ι ι ℝ} {ell f : ℝ} (hell : 0<ell)
    (hA : (A-ell • (1:Matrix ι ι ℝ)).PosSemidef) (hB : B.PosSemidef)
    (hf : (A*B).trace ≤ f) : B.det ≤ (f/ell)^Fintype.card ι := by
  have hh := trace_mul_nonneg hA hB
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,
    Matrix.trace_smul,smul_eq_mul] at hh
  have hb : B.trace ≤ f/ell := (le_div_iff₀ hell).mpr (by nlinarith)
  exact (det_le_trace_pow hB).trans (pow_le_pow_left₀ hB.trace_nonneg hb _)

end ABPMatrix

namespace ABPGeometry
open Set Filter Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] in
lemma contact_det_bound (b : OrthonormalBasis ι ℝ E) {u : E → ℝ}
    (hu : Differentiable ℝ u) {C : Set E} {x : E} (hx : x∈upperContact u C)
    (hH : DifferentiableAt ℝ (gradient u) x) {A : Matrix ι ι ℝ} {ell f : ℝ}
    (hell : 0<ell) (hA : (A-ell • (1:Matrix ι ι ℝ)).PosSemidef)
    (hf : -f ≤ (A*hessianMatrix b u x).trace) :
    |(fderiv ℝ (gradient u) x).det| ≤ (f/ell)^Fintype.card ι := by
  have hneg : (-hessianMatrix b u x).PosSemidef := by
    simpa only [hessianMatrix,ContinuousLinearMap.toLinearMap_neg,map_neg] using
      (LinearMap.posSemidef_toMatrix_iff b).mpr (contact_hessian_negative hu hx hH)
  have hh := ABPMatrix.det_le_of_trace hell hA hneg (show (A*(-hessianMatrix b u x)).trace≤f by
    rw [Matrix.mul_neg,Matrix.trace_neg]; linarith)
  have he : |(hessianMatrix b u x).det|=(-hessianMatrix b u x).det := by
    calc
      _ = |(-hessianMatrix b u x).det| := by
        rw [Matrix.det_neg,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      _ = _ := abs_of_nonneg hneg.det_nonneg
  rw [← he] at hh
  simpa only [hessianMatrix,LinearMap.det_toMatrix] using hh

lemma boundedContact_measurable {u : E → ℝ} (hu : Continuous u)
    (hg : Continuous (gradient u)) (C : Set E) (r : ℝ) :
    MeasurableSet (boundedContact u C r) :=
  ((upperContact_measurable hu hg C).inter (isOpen_lt continuous_const hu).measurableSet).inter
    (isClosed_le hg.norm continuous_const).measurableSet

omit [MeasurableSpace E] [BorelSpace E] in
lemma bounded_slopes_image {u : E → ℝ} (hu : Differentiable ℝ u)
    {C : Set E} (hC : IsCompact C) {x : E} (hx : x∈C) {D r : ℝ} (hDp : 0<D)
    (hD : ∀ y ∈ C, ‖y-x‖≤D) (hbd : ∀ y ∈ frontier C, u y≤0)
    (hr : r*D≤u x) : ball (0:E) r ⊆ gradient u '' boundedContact u C r := by
  intro p hp
  have hp' : ‖p‖<r := by simpa only [mem_ball,dist_zero_right] using hp
  obtain ⟨y,hy,he⟩ := small_slope_in_positive_contact_image hu hC hx hD hbd
    ((mul_lt_mul_of_pos_right hp' hDp).trans_le hr)
  exact ⟨y,⟨hy,by change ‖gradient u y‖≤r; rw [he]; exact hp'.le⟩,he⟩

theorem abp_bounded_slopes (b : OrthonormalBasis ι ℝ E) {u : E → ℝ}
    (hu : Differentiable ℝ u) {L : ℝ≥0} (hl : LipschitzWith L (gradient u))
    {C : Set E} (hC : IsCompact C) {x : E} (hx : x∈C) {D r : ℝ} (hDp : 0<D)
    (hD : ∀ y ∈ C, ‖y-x‖≤D) (hbd : ∀ y ∈ frontier C, u y≤0) (hr : r*D≤u x)
    {ell : ℝ} (hell : 0<ell) (A : E → Matrix ι ι ℝ) (f : E → ℝ)
    (hA : ∀ᵐ y ∂μ, y∈boundedContact u C r → (A y-ell • (1:Matrix ι ι ℝ)).PosSemidef)
    (hf : ∀ᵐ y ∂μ, y∈boundedContact u C r → -f y ≤ (A y*hessianMatrix b u y).trace) :
    μ (ball (0:E) r) ≤
      ∫⁻ y in boundedContact u C r, ENNReal.ofReal ((f y/ell)^Fintype.card ι) ∂μ := by
  have hm := boundedContact_measurable hu.continuous hl.continuous C r
  apply (measure_mono (bounded_slopes_image hu hC hx hDp hD hbd hr)).trans
  apply (lipschitz_area_upper_bound μ hl hm).trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae hA,ae_restrict_of_ae hf,
    ae_restrict_of_ae (hl.ae_differentiableAt (μ:=μ)),ae_restrict_mem hm] with y hyA hyf hyd hy
  exact ENNReal.ofReal_le_ofReal (contact_det_bound b hu hy.1.1 hyd hell (hyA hy) (hyf hy))

theorem abp_localized_contact_mass [Nonempty ι] (b : OrthonormalBasis ι ℝ E) {u : E → ℝ}
    (hu : Differentiable ℝ u) {L : ℝ≥0} (hl : LipschitzWith L (gradient u))
    {C : Set E} (hC : IsCompact C) {x : E} (hx : x∈C) {D r : ℝ} (hDp : 0<D)
    (hD : ∀ y ∈ C, ‖y-x‖≤D) (hbd : ∀ y ∈ frontier C, u y≤0) (hr : r*D≤u x)
    {ell F : ℝ} (hell : 0<ell) (A : E → Matrix ι ι ℝ) {S : Set E} (hS : MeasurableSet S)
    (hA : ∀ᵐ y ∂μ, y∈boundedContact u C r → (A y-ell • (1:Matrix ι ι ℝ)).PosSemidef)
    (hf : ∀ᵐ y ∂μ, y∈boundedContact u C r →
      -(S.indicator (fun _ => F) y) ≤ (A y*hessianMatrix b u y).trace) :
    μ (ball (0:E) r) ≤ ENNReal.ofReal ((F/ell)^Fintype.card ι)*
      μ (boundedContact u C r ∩ S) := by
  have hh := abp_bounded_slopes μ b hu hl hC hx hDp hD hbd hr hell A
    (S.indicator (fun _ => F)) hA hf
  have he (y : E) : ENNReal.ofReal ((S.indicator (fun _ => F) y/ell)^Fintype.card ι)=
      S.indicator (fun _ => ENNReal.ofReal ((F/ell)^Fintype.card ι)) y := by
    by_cases hy : y∈S
    · simp only [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy,zero_div,zero_pow (Fintype.card_ne_zero),ENNReal.ofReal_zero]
  simp_rw [he] at hh
  rw [lintegral_indicator hS,lintegral_const,Measure.restrict_apply_univ,Measure.restrict_apply hS,
    inter_comm S] at hh
  exact hh


omit [MeasurableSpace E] [BorelSpace E] in
lemma gradient_sub_of_diff {u v : E → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) :
    gradient (fun x => u x-v x)=fun x => gradient u x-gradient v x := by
  funext x
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [map_sub,toDual_gradient,toDual_gradient,toDual_gradient]
  exact fderiv_sub (hu x) (hv x)

omit [MeasurableSpace E] [BorelSpace E] in
lemma hessian_sub_of_diff (b : OrthonormalBasis ι ℝ E) {u v : E → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) {x : E}
    (hdu : DifferentiableAt ℝ (gradient u) x) (hdv : DifferentiableAt ℝ (gradient v) x) :
    hessianMatrix b (fun x => u x-v x) x=hessianMatrix b u x-hessianMatrix b v x := by
  unfold hessianMatrix
  rw [gradient_sub_of_diff hu hv]
  change LinearMap.toMatrix _ _ (fderiv ℝ (gradient u-gradient v) x).toLinearMap=_
  rw [fderiv_sub hdu hdv,ContinuousLinearMap.toLinearMap_sub,map_sub]

theorem barrier_contact_mass [Nonempty ι] (b : OrthonormalBasis ι ℝ E)
    {v ψ : E → ℝ} (hv : Differentiable ℝ v) (hψ : Differentiable ℝ ψ)
    {Lv Lψ : ℝ≥0} (hLv : LipschitzWith Lv (gradient v)) (hLψ : LipschitzWith Lψ (gradient ψ))
    {C : Set E} (hC : IsCompact C) {x : E} (hx : x∈C) {D r M : ℝ} (hDp : 0<D)
    (hD : ∀ y ∈ C, ‖y-x‖≤D) (hbd : ∀ y∈frontier C, ψ y≤0)
    (hvn : ∀ y∈C, 0≤v y) (hm : ∀ y∈C, ψ y≤M) (hr : r*D≤ψ x-v x)
    {ell F B : ℝ} (hell : 0<ell) (hB : 0≤B) (A : E → Matrix ι ι ℝ) (f : E → ℝ)
    {S : Set E} (hS : MeasurableSet S)
    (hA : ∀ᵐ y ∂μ, y∈C → (A y-ell • (1:Matrix ι ι ℝ)).PosSemidef)
    (hvP : ∀ᵐ y ∂μ, y∈C → (A y*hessianMatrix b v y).trace≤f y+B*‖gradient v y‖)
    (hψP : ∀ᵐ y ∂μ, y∈C → -S.indicator (fun _ => F) y ≤
      (A y*hessianMatrix b ψ y).trace-f y-B*(‖gradient ψ y‖+r)) :
    μ (ball (0:E) r) ≤ ENNReal.ofReal ((F/ell)^Fintype.card ι)*μ (S∩C∩{y | v y<M}) := by
  have hge := gradient_sub_of_diff hψ hv
  have hlu : LipschitzWith (Lψ+Lv) (gradient (fun y => ψ y-v y)) := by
    rw [hge]
    exact hLψ.sub hLv
  have hsub (y : E) (hy : y∈boundedContact (fun y => ψ y-v y) C r) : y∈C :=
    interior_subset hy.1.1.1
  have hh := abp_localized_contact_mass μ b (hψ.sub hv) hlu hC hx hDp hD
    (fun y hy => sub_nonpos.mpr ((hbd y hy).trans (hvn y (hC.isClosed.frontier_subset hy)))) hr
    (F:=F) hell A hS
    (by filter_upwards [hA] with y hy hyc; exact hy (hsub y hyc))
    (by
      filter_upwards [hvP,hψP,hLv.ae_differentiableAt (μ:=μ),hLψ.ae_differentiableAt (μ:=μ)]
        with y hyv hyψ hydv hydψ hy
      have hyC := hsub y hy
      have hgr : ‖gradient v y‖≤‖gradient ψ y‖+r := by
        have hle := norm_sub_le (gradient ψ y) (gradient (fun y => ψ y-v y) y)
        rw [hge] at hle
        simp only [sub_sub_cancel] at hle
        have hrs : ‖gradient (fun y => ψ y-v y) y‖≤r := hy.2
        rw [hge] at hrs
        exact hle.trans (add_le_add le_rfl hrs)
      change -S.indicator (fun _ => F) y ≤ (A y*hessianMatrix b (fun y => ψ y-v y) y).trace
      rw [hessian_sub_of_diff b hψ hv hydψ hydv,Matrix.mul_sub,Matrix.trace_sub]
      have := mul_le_mul_of_nonneg_left hgr hB
      have := hyv hyC
      have := hyψ hyC
      linarith)
  apply hh.trans
  apply mul_le_mul le_rfl ?_ (by positivity) (by positivity)
  apply measure_mono
  intro y hy
  exact ⟨⟨hy.2,hsub y hy.1⟩,lt_of_lt_of_le (by exact sub_pos.mp hy.1.1.2) (hm y (hsub y hy.1))⟩

end ABPGeometry

namespace HarnackOneStep
open Set Filter Metric MeasureTheory
open scoped Topology InnerProductSpace Matrix ContDiff NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

theorem exists_mass_constants (b : OrthonormalBasis ι ℝ E)
    {ell T B a q R : ℝ} (hell : 0<ell) (hT : 0≤T) (hB : 0≤B)
    (ha : 0<a) (hq : 0≤q) (hqR : q<R) :
    ∃ M F : ℝ, 1<M ∧ 0<F ∧ ∀ (v : E → ℝ) (L : ℝ≥0) (A : E → Matrix ι ι ℝ),
      Differentiable ℝ v → LipschitzWith L (gradient v) →
      (∀ x∈closedBall (0:E) R, 0≤v x) →
      (∀ᵐ x ∂μ, x∈closedBall (0:E) R → (A x-ell • (1:Matrix ι ι ℝ)).PosSemidef) →
      (∀ᵐ x ∂μ, x∈closedBall (0:E) R → (A x).trace≤T) →
      (∀ᵐ x ∂μ, x∈closedBall (0:E) R →
        (A x*ABPGeometry.hessianMatrix b v x).trace≤1+B*‖gradient v x‖) →
      (∃ x∈closedBall (0:E) q, v x≤1) →
      μ (ball (0:E) (1/(2*R))) ≤ ENNReal.ofReal ((F/ell)^Fintype.card ι)*
        μ (ball (0:E) a∩{x | v x<M}) := by
  have hR : 0<R := hq.trans_lt hqR
  let r := 1/(2*R)
  have hr : 0<r := by dsimp [r]; positivity
  obtain ⟨ψ,Lψ,M,F,hψ,hLψ,hM,hF,hψM,hψbd,hψlo,hψP⟩ :=
    RadialBarrier.exists_elliptic_barrier b hell hT hB ha hq hqR hr.le
  refine ⟨M,F,hM,hF,?_⟩
  intro v L A hv hL hvn hA hAT hvP hlo
  obtain ⟨x,hx,hxv⟩ := hlo
  have hxq : ‖x‖≤q := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hxR : x∈closedBall (0:E) R := mem_closedBall.mpr (by simpa using hxq.trans hqR.le)
  have hD (y : E) (hy : y∈closedBall (0:E) R) : ‖y-x‖≤2*R := by
    have hyR : ‖y‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hh := norm_sub_le y x
    linarith
  have hh := ABPGeometry.barrier_contact_mass μ b hv (hψ.differentiable (by simp)) hL hLψ
    (isCompact_closedBall (0:E) R) hxR (show 0<2*R by positivity) hD hψbd hvn hψM
    (show r*(2*R)≤ψ x-v x by rw [div_mul_cancel₀ 1 (by positivity : 2*R≠0)]; linarith [hψlo x hx])
    hell hB A (fun _ => 1) isOpen_ball.measurableSet hA hvP
    (by
      filter_upwards [hA,hAT] with y hyA hyT hy
      have hp := hψP y (A y) hy (hyA hy) (hyT hy)
      change -(ball (0:E) a).indicator (fun _ => F) y ≤ _
      unfold ABPGeometry.hessianMatrix
      linarith)
  apply hh.trans
  apply mul_le_mul le_rfl ?_ (by positivity) (by positivity)
  exact measure_mono (fun _ hy => ⟨hy.1.1,hy.2⟩)

end HarnackOneStep

namespace DyadicBoxes
open Set Metric Filter BoxIntegral
open scoped Topology
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma box_le (I : Box ι) (p : List (Set ι)) : box I p≤I := by
  induction p generalizing I with
  | nil => exact le_rfl
  | cons s p ih => exact (ih _).trans (I.splitCenterBox_le s)

omit [Fintype ι] in
lemma comparable (I : Box ι) (p q : List (Set ι)) (hle : q.length≤p.length) :
    (box I p≤box I q) ∨ Disjoint (box I p : Set (ι → ℝ)) (box I q) := by
  induction q generalizing I p with
  | nil => exact Or.inl (box_le I p)
  | cons t q ih =>
    cases p with
    | nil => simp at hle
    | cons s p =>
      by_cases he : s=t
      · subst t
        exact ih (I.splitCenterBox s) p (by simpa using hle)
      · exact Or.inr ((I.disjoint_splitCenterBox he).mono (box_le _ p) (box_le _ q))

omit [Fintype ι] in
lemma same_level_disjoint (I : Box ι) (p q : List (Set ι))
    (hl : p.length=q.length) (hne : p≠q) :
    Disjoint (box I p : Set (ι → ℝ)) (box I q) := by
  induction p generalizing I q with
  | nil =>
    have hq : q=[] := List.length_eq_zero_iff.mp hl.symm
    exact (hne hq.symm).elim
  | cons s p ih =>
    cases q with
    | nil => simp at hl
    | cons t q =>
      by_cases he : s=t
      · subst t
        exact ih _ _ (by simpa using hl) (by simpa using hne)
      · exact (I.disjoint_splitCenterBox he).mono (box_le _ p) (box_le _ q)

omit [Fintype ι] in
lemma level_cover (I : Box ι) (n : ℕ) {x : ι → ℝ} (hx : x∈I) :
    ∃ p : List (Set ι), p.length=n ∧ x∈box I p := by
  induction n generalizing I with
  | zero => exact ⟨[],rfl,hx⟩
  | succ n ih =>
    obtain ⟨s,hs⟩ := Box.exists_mem_splitCenterBox.mpr hx
    obtain ⟨p,hp,hxp⟩ := ih (I.splitCenterBox s) hs
    exact ⟨s::p,by simp [hp],hxp⟩

omit [Fintype ι] in
lemma side_length (I : Box ι) (p : List (Set ι)) (i : ι) :
    (box I p).upper i-(box I p).lower i=(I.upper i-I.lower i)/(2:ℝ)^p.length := by
  induction p generalizing I with
  | nil => simp [box]
  | cons s p ih =>
    rw [box,ih,I.upper_sub_lower_splitCenterBox,List.length_cons,pow_succ',div_div]

omit [Fintype ι] in
lemma box_append (I : Box ι) (p q : List (Set ι)) : box I (p++q)=box (box I p) q := by
  induction p generalizing I with
  | nil => rfl
  | cons s p ih => exact ih _

lemma diameter_bound (I : Box ι) (p : List (Set ι)) (i : ι) :
    diam (box I p).Icc≤(I.distortion:ℝ)*(I.upper i-I.lower i)/(2:ℝ)^p.length := by
  have hd : (box I p).distortion=I.distortion := Box.distortion_eq_of_sub_eq_div (side_length I p)
  have hh := (box I p).diam_Icc_le_of_distortion_le i (le_of_eq hd)
  simpa only [side_length,mul_div_assoc] using hh

lemma exists_small_level [Nonempty ι] (I : Box ι) {U : Set (ι → ℝ)} (hU : IsOpen U)
    {x : ι → ℝ} (hx : x∈U) : ∃ n : ℕ, ∀ p : List (Set ι), p.length=n →
      x∈box I p → (box I p : Set (ι → ℝ))⊆U := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hx
  let i : ι := Classical.choice inferInstance
  let D : ℝ := I.distortion*(I.upper i-I.lower i)
  have ht : Tendsto (fun n : ℕ => D/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨n,hn⟩ := (eventually_atTop.mp (ht.eventually (gt_mem_nhds hr)))
  refine ⟨n,fun p hp hxp y hyp => hball ?_⟩
  have hb := diameter_bound I p i
  rw [hp] at hb
  have hxy := dist_le_diam_of_mem (box I p).isBounded_Icc (Box.coe_subset_Icc hyp) (Box.coe_subset_Icc hxp)
  exact (hxy.trans hb).trans_lt (hn n le_rfl)

end DyadicBoxes

namespace CubeGeometry
open Set Metric MeasureTheory BoxIntegral
open scoped Topology ENNReal Pointwise
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma side_pos (p : List (Set ι)) : 0<side p := by unfold side; positivity
omit [Fintype ι] in
lemma side_le_one (p : List (Set ι)) : side p≤1 := by
  unfold side
  exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) (by positivity)
omit [Fintype ι] in
lemma sides (p : List (Set ι)) (i : ι) :
    (DyadicBoxes.box unitBox p).upper i-(DyadicBoxes.box unitBox p).lower i=side p := by
  rw [DyadicBoxes.side_length]
  norm_num [unitBox,side]

lemma norm_le_card_mul {x : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0≤r)
    (hx : ∀ i, |x i|≤r) : ‖x‖≤Fintype.card ι*r := by
  classical
  have hsq : ‖x‖^2≤(Fintype.card ι:ℝ)*r^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : ι, r^2 := Finset.sum_le_sum (fun i _ => by nlinarith [hx i,abs_le.mp (hx i)])
      _ = _ := by simp
  have hn : (Fintype.card ι:ℝ)≤(Fintype.card ι:ℝ)^2 := by
    exact_mod_cast (Nat.le_self_pow (by omega : 2≠0) (Fintype.card ι))
  have hh := mul_le_mul_of_nonneg_right hn (sq_nonneg r)
  have hp : 0≤(Fintype.card ι:ℝ)*r := by positivity
  nlinarith [norm_nonneg x]

omit [Fintype ι] in
lemma center_mem (I : Box ι) : (center I).ofLp∈I := by
  intro i
  have hi := I.lower_lt_upper i
  change I.lower i < (I.lower i+I.upper i)/2 ∧ (I.lower i+I.upper i)/2≤I.upper i
  constructor <;> linarith

lemma norm_center (p : List (Set ι)) :
    ‖center (DyadicBoxes.box unitBox p)‖≤(Fintype.card ι:ℝ)/2 := by
  have hc : (fun i => ((DyadicBoxes.box unitBox p).lower i+(DyadicBoxes.box unitBox p).upper i)/2) ∈ (unitBox : Box ι) := by
    apply DyadicBoxes.box_le unitBox p
    intro i
    have hi := (DyadicBoxes.box unitBox p).lower_lt_upper i
    constructor <;> dsimp only <;> linarith
  have hh := norm_le_card_mul (x:=center (DyadicBoxes.box unitBox p)) (r:=1/2) (by norm_num) (by
    intro i
    have hi := hc i
    change -(1/2:ℝ)<((DyadicBoxes.box unitBox p).lower i+(DyadicBoxes.box unitBox p).upper i)/2 ∧
      ((DyadicBoxes.box unitBox p).lower i+(DyadicBoxes.box unitBox p).upper i)/2≤1/2 at hi
    exact abs_le.mpr ⟨hi.1.le,hi.2⟩)
  simpa only [div_eq_mul_inv,one_mul] using hh

omit [Fintype ι] in
lemma preimage_box (p : List (Set ι)) :
    (fun y : EuclideanSpace ℝ ι => center (DyadicBoxes.box unitBox p)+side p • y) ⁻¹'
      {x | x.ofLp∈DyadicBoxes.box unitBox p} = {y | y.ofLp∈(unitBox : Box ι)} := by
  ext y
  change (∀ i, (DyadicBoxes.box unitBox p).lower i < _ ∧ _ ≤ (DyadicBoxes.box unitBox p).upper i) ↔
    ∀ i, -(1/2:ℝ)<y i ∧ y i≤1/2
  have hs := side_pos p
  constructor <;> intro hy i <;> have hi := hy i <;> have hw := sides p i
  · change (DyadicBoxes.box unitBox p).lower i <
      ((DyadicBoxes.box unitBox p).lower i+(DyadicBoxes.box unitBox p).upper i)/2+side p*y i ∧
      ((DyadicBoxes.box unitBox p).lower i+(DyadicBoxes.box unitBox p).upper i)/2+side p*y i≤
      (DyadicBoxes.box unitBox p).upper i at hi
    constructor <;> nlinarith
  · change (DyadicBoxes.box unitBox p).lower i <
      ((DyadicBoxes.box unitBox p).lower i+(DyadicBoxes.box unitBox p).upper i)/2+side p*y i ∧
      ((DyadicBoxes.box unitBox p).lower i+(DyadicBoxes.box unitBox p).upper i)/2+side p*y i≤
      (DyadicBoxes.box unitBox p).upper i
    constructor <;> nlinarith

lemma inner_ball_subset : ball (0:EuclideanSpace ℝ ι) (1/2)⊆{x | x.ofLp∈(unitBox : Box ι)} := by
  intro x hx i
  have hn : ‖x‖<1/2 := by simpa only [mem_ball,dist_zero_right] using hx
  have hi : |x i|<1/2 := (PiLp.norm_apply_le x i).trans_lt hn
  exact ⟨(abs_lt.mp hi).1,(abs_lt.mp hi).2.le⟩

lemma volume_unitBox : volume ((unitBox : Box ι) : Set (ι → ℝ))=1 := by
  rw [Box.coe_eq_pi,volume_pi,Measure.pi_pi]
  simp only [unitBox,Real.volume_Ioc]
  norm_num

lemma volume_unitCube : volume {x : EuclideanSpace ℝ ι | x.ofLp∈(unitBox : Box ι)}=1 := by
  have h := (PiLp.volume_preserving_toLp ι).measure_preimage
    ((unitBox : Box ι).measurableSet_coe.preimage (EuclideanSpace.equiv ι ℝ).continuous.measurable).nullMeasurableSet
  change volume ((unitBox : Box ι) : Set (ι → ℝ))=volume {x : EuclideanSpace ℝ ι | x.ofLp∈(unitBox : Box ι)} at h
  exact h.symm.trans volume_unitBox

omit [Fintype ι] in
lemma parent_side (p : List (Set ι)) (a : Set ι) : side p=2*side (p++[a]) := by
  simp only [side,List.length_append,List.length_singleton,pow_succ]
  field_simp

lemma normalized_parent (p : List (Set ι)) (a : Set ι) {x : ι → ℝ}
    (hx : x∈DyadicBoxes.box unitBox p) :
    ‖(side (p++[a]))⁻¹ • (WithLp.toLp 2 x-center (DyadicBoxes.box unitBox (p++[a])))‖≤
      2*(Fintype.card ι:ℝ) := by
  let J := DyadicBoxes.box unitBox (p++[a])
  have hJ : J≤DyadicBoxes.box unitBox p := by
    dsimp [J]
    rw [DyadicBoxes.box_append]
    exact DyadicBoxes.box_le _ [a]
  have hc := hJ (center_mem J)
  have hd : ‖WithLp.toLp 2 x-center J‖≤(Fintype.card ι:ℝ)*side p :=
    norm_le_card_mul (side_pos p).le (by
      intro i
      have hxi := hx i
      have hci := hc i
      have hw := sides p i
      change |x i-(center J) i| ≤ side p
      exact abs_le.mpr ⟨by linarith [hxi.1,hxi.2,hci.1,hci.2],by linarith [hxi.1,hxi.2,hci.1,hci.2]⟩)
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (side_pos _),← div_eq_inv_mul]
  apply (div_le_iff₀ (side_pos _)).mpr
  rw [parent_side p a] at hd
  dsimp [J] at hd
  nlinarith

lemma global_ball (p : List (Set ι)) {R : ℝ} {x : EuclideanSpace ℝ ι}
    (hx : x∈closedBall (0:EuclideanSpace ℝ ι) R) :
    center (DyadicBoxes.box unitBox p)+side p • x∈
      closedBall 0 ((Fintype.card ι:ℝ)/2+R) := by
  have hxn : ‖x‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hc := norm_center p
  have hh := norm_add_le (center (DyadicBoxes.box unitBox p)) (side p • x)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (side_pos p)] at hh
  have hs := mul_le_mul (side_le_one p) hxn (norm_nonneg x) (by norm_num : (0:ℝ)≤1)
  rw [one_mul] at hs
  rw [mem_closedBall,dist_zero_right]
  linarith

lemma norm_unit {x : ι → ℝ} (hx : x∈(unitBox : Box ι)) :
    ‖WithLp.toLp 2 x‖≤(Fintype.card ι:ℝ)/2 := by
  have hh := norm_le_card_mul (x:=WithLp.toLp 2 x) (r:=1/2) (by norm_num) (by
    intro i
    have hi := hx i
    exact abs_le.mpr ⟨hi.1.le,hi.2⟩)
  simpa only [div_eq_mul_inv,one_mul] using hh

end CubeGeometry

namespace MassDecay
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma of_positive_mass {Q E F : Set X} (hQ : μ Q=1)
    (hE : E⊆Q) (hF : F⊆Q) (hd : Disjoint E F) (hmF : MeasurableSet F)
    {b c : ℝ} (hb : 0<b) (hc : 0<c)
    (hmass : ENNReal.ofReal b ≤ ENNReal.ofReal c * μ E) :
    μ F≤ENNReal.ofReal (1-min (1/2) (b/c)) := by
  have hfE : μ E≠⊤ := ne_top_of_le_ne_top (by simp [hQ]) (measure_mono hE)
  have hfF : μ F≠⊤ := ne_top_of_le_ne_top (by simp [hQ]) (measure_mono hF)
  have hsum : μ E+μ F≤1 := by
    rw [← measure_union hd hmF,← hQ]
    exact measure_mono (union_subset hE hF)
  have hsumR := ENNReal.toReal_mono (by simp) hsum
  rw [ENNReal.toReal_add hfE hfF,ENNReal.toReal_one] at hsumR
  have hmR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfE) hmass
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hb.le,ENNReal.toReal_ofReal hc.le] at hmR
  have hratio : b/c≤(μ E).toReal := (div_le_iff₀ hc).mpr (by nlinarith)
  have hmin : min (1/2) (b/c)≤(μ E).toReal := (min_le_right _ _).trans hratio
  have hn : 0≤1-min (1/2) (b/c) := by linarith [min_le_left (1/2:ℝ) (b/c)]
  apply (ENNReal.toReal_le_toReal hfF ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hn]
  linarith

lemma constants {b c : ℝ} (hb : 0<b) (hc : 0<c) :
    0<ENNReal.ofReal (1-min (1/2) (b/c)) ∧
      ENNReal.ofReal (1-min (1/2) (b/c))<1 := by
  have hp : 0 < min (1/2:ℝ) (b/c) := lt_min (by norm_num) (div_pos hb hc)
  have hn : 0<1-min (1/2:ℝ) (b/c) := by linarith [min_le_left (1/2:ℝ) (b/c)]
  constructor
  · exact ENNReal.ofReal_pos.mpr hn
  · exact ENNReal.ofReal_lt_one.mpr (by linarith)
end MassDecay

namespace HarnackCube
open Set Filter Metric MeasureTheory BoxIntegral
open scoped Topology InnerProductSpace Matrix NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_decay (b : OrthonormalBasis ι ℝ E) {ell T B q R : ℝ}
    (hell : 0 < ell) (hT : 0 ≤ T) (hB : 0 ≤ B) (hq : 0 ≤ q) (hqR : q < R) :
    ∃ (M : ℝ) (theta : ℝ≥0∞), 1 < M ∧ 0 < theta ∧ theta < 1 ∧
    ∀ (v : E → ℝ) (L : ℝ≥0) (A : E → Matrix ι ι ℝ),
      Differentiable ℝ v → LipschitzWith L (gradient v) →
      (∀ x∈closedBall (0:E) R, 0≤v x) →
      (∀ᵐ x ∂volume, x∈closedBall (0:E) R → (A x-ell • (1:Matrix ι ι ℝ)).PosSemidef) →
      (∀ᵐ x ∂volume, x∈closedBall (0:E) R → (A x).trace≤T) →
      (∀ᵐ x ∂volume, x∈closedBall (0:E) R →
        (A x*ABPGeometry.hessianMatrix b v x).trace≤1+B*‖gradient v x‖) →
      (∃ x∈closedBall (0:E) q, v x≤1) →
      volume ({x | M<v x}∩{x | x.ofLp∈(CubeGeometry.unitBox : Box ι)})≤theta := by
  have hR : 0 < R := hq.trans_lt hqR
  obtain ⟨M,F,hM,hF,hstep⟩ := HarnackOneStep.exists_mass_constants volume b hell hT hB
    (by norm_num : (0:ℝ)<1/2) hq hqR
  let mass := (volume (ball (0:E) (1/(2*R)))).toReal
  let C := (F/ell)^Fintype.card ι
  have hmass : 0 < mass := ENNReal.toReal_pos
    (measure_ball_pos volume (0:E) (by positivity)).ne' measure_ball_lt_top.ne
  have hC : 0 < C := by dsimp [C]; positivity
  let theta := ENNReal.ofReal (1-min (1/2) (mass/C))
  obtain ⟨hth0,hth1⟩ := MassDecay.constants hmass hC
  refine ⟨M,theta,hM,hth0,hth1,?_⟩
  intro v L A hv hL hvn hA hAT hvP hlo
  have hh := hstep v L A hv hL hvn hA hAT hvP hlo
  have hE : ball (0:E) (1/2)∩{x | v x<M} ⊆ {x | x.ofLp∈(CubeGeometry.unitBox : Box ι)} :=
    fun x hx => CubeGeometry.inner_ball_subset hx.1
  have hm : ENNReal.ofReal mass ≤ ENNReal.ofReal C*volume (ball (0:E) (1/2)∩{x | v x<M}) := by
    simpa only [mass,C,ENNReal.ofReal_toReal measure_ball_lt_top.ne] using hh
  apply MassDecay.of_positive_mass volume CubeGeometry.volume_unitCube hE inter_subset_right ?_
    ((isOpen_lt continuous_const hv.continuous).measurableSet.inter
      ((CubeGeometry.unitBox : Box ι).measurableSet_coe.preimage
        (EuclideanSpace.equiv ι ℝ).continuous.measurable)) hmass hC hm
  apply disjoint_left.mpr
  intro x hx hy
  exact lt_asymm (show v x<M from hx.2) (show M<v x from hy.1)

end HarnackCube

namespace AffineMeasure
open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
lemma quasi (c : E) {s : ℝ} (hs : s≠0) :
    QuasiMeasurePreserving (fun x : E => c+s • x) μ μ :=
  (measurePreserving_add_left μ c).quasiMeasurePreserving.comp (μ.quasiMeasurePreserving_smul hs)
lemma affine_image (c : E) {s : ℝ} (hs : 0 ≤ s) (S : Set E) :
    μ ((fun x : E => c+s • x) '' S)=ENNReal.ofReal (s^Module.finrank ℝ E)*μ S := by
  have he : (fun x : E => c+s • x) '' S=(fun x : E => c+x) '' (s • S) := by
    rw [← Set.image_smul,← Set.image_comp]
    rfl
  rw [he]
  have hh : μ ((fun x : E => c+x) '' (s • S))=μ (s • S) := by
    rw [← measure_preimage_add μ c ((fun x : E => c+x) '' (s • S)),
      preimage_image_eq _ (add_right_injective c)]
  rw [hh,μ.addHaar_smul_of_nonneg hs]
lemma preimage (c : E) {s : ℝ} (hs : 0 < s) (S : Set E) :
    μ S=ENNReal.ofReal (s^Module.finrank ℝ E)*μ ((fun x : E => c+s • x) ⁻¹' S) := by
  rw [← affine_image μ c hs.le]
  congr 1
  symm
  apply image_preimage_eq
  intro y
  refine ⟨s⁻¹ • (y-c),?_⟩
  dsimp only
  rw [smul_inv_smul₀ hs.ne']
  abel
end AffineMeasure

namespace AffineRescale
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma hasFDerivAt_map (c : E) (s : ℝ) (x : E) :
    HasFDerivAt (fun y => c+s • y) (s • ContinuousLinearMap.id ℝ E) x := by
  exact ((hasFDerivAt_id x).const_smul s).const_add c

omit [FiniteDimensional ℝ E] in
lemma differentiable {v : E → ℝ} (hv : Differentiable ℝ v) (c : E) (s k : ℝ) :
    Differentiable ℝ (fun x => k*v (c+s • x)) :=
  fun x => (((hv (c+s • x)).hasFDerivAt.comp x (hasFDerivAt_map c s x)).const_mul k).differentiableAt

lemma gradient {v : E → ℝ} (hv : Differentiable ℝ v) (c : E) (s k : ℝ) (x : E) :
    _root_.gradient (fun x => k*v (c+s • x)) x=(k*s) • _root_.gradient v (c+s • x) := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [map_smul,toDual_gradient,toDual_gradient]
  have hh := ((hv (c+s • x)).hasFDerivAt.comp x (hasFDerivAt_map c s x)).const_mul k
  change HasFDerivAt (fun y => k*v (c+s • y)) _ x at hh
  rw [hh.fderiv]
  ext y
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  ring

lemma hessian {v : E → ℝ} (hv : Differentiable ℝ v) (c : E) (s k : ℝ) (x : E)
    (hdg : DifferentiableAt ℝ (_root_.gradient v) (c+s • x)) :
    fderiv ℝ (_root_.gradient (fun x => k*v (c+s • x))) x=
      (k*s^2) • fderiv ℝ (_root_.gradient v) (c+s • x) := by
  have he : _root_.gradient (fun x => k*v (c+s • x))=
    fun x => (k*s) • _root_.gradient v (c+s • x) := funext (gradient hv c s k)
  rw [he]
  have hh := (hdg.hasFDerivAt.comp x (hasFDerivAt_map c s x)).const_smul (k*s)
  change HasFDerivAt (fun y => (k*s) • _root_.gradient v (c+s • y)) _ x at hh
  rw [hh.fderiv]
  ext y
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_smul]
  congr 1
  ring

lemma gradient_lipschitz {v : E → ℝ} (hv : Differentiable ℝ v) {L : ℝ≥0}
    (hl : LipschitzWith L (_root_.gradient v)) (c : E) (s k : ℝ) :
    LipschitzWith (‖k*s‖₊*(L*‖s‖₊)) (_root_.gradient (fun x => k*v (c+s • x))) := by
  have he : _root_.gradient (fun x => k*v (c+s • x))=
    fun x => (k*s) • _root_.gradient v (c+s • x) := funext (gradient hv c s k)
  rw [he]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,NNReal.coe_mul,coe_nnnorm]
  have hh := hl.norm_sub_le (c+s • x) (c+s • y)
  have he : c+s • x-(c+s • y)=s • (x-y) := by module
  rw [he,norm_smul,Real.norm_eq_abs] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (k*s))]

end AffineRescale

namespace HarnackScale
open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology InnerProductSpace Matrix NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma pde_rescale (b : OrthonormalBasis ι ℝ E)
    {v : E → ℝ} (hv : Differentiable ℝ v) {L : ℝ≥0} (hL : LipschitzWith L (gradient v))
    {A : E → Matrix ι ι ℝ} {S : Set E} {B : ℝ} (hB : 0≤B)
    (hP : ∀ᵐ x ∂μ, x∈S → (A x*ABPGeometry.hessianMatrix b v x).trace≤1+B*‖gradient v x‖)
    (c : E) {s k : ℝ} (hs : 0 < s) (hs1 : s≤1) (hk : 0<k) (hk1 : k≤1) :
    ∀ᵐ x ∂μ, c+s • x∈S →
      (A (c+s • x)*ABPGeometry.hessianMatrix b (fun y => k*v (c+s • y)) x).trace≤
        1+B*‖gradient (fun y => k*v (c+s • y)) x‖ := by
  have hdg := hL.ae_differentiableAt (μ:=μ)
  have hQ := AffineMeasure.quasi μ c hs.ne'
  filter_upwards [hQ.ae hP,hQ.ae hdg] with x hx hxd hxS
  have hh := hx hxS
  rw [AffineRescale.gradient hv]
  unfold ABPGeometry.hessianMatrix
  rw [AffineRescale.hessian hv c s k x hxd]
  simp only [ContinuousLinearMap.toLinearMap_smul,map_smul,Matrix.mul_smul,Matrix.trace_smul,
    smul_eq_mul,norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos hk hs)]
  have hks : 0≤k*s^2 := by positivity
  have hss : s^2≤1 := by nlinarith
  have hks1 : k*s^2≤1 := by nlinarith
  have hss' : s^2 ≤ s := by nlinarith
  have hb : B*(k*s^2*‖gradient v (c+s • x)‖)≤B*(k*s*‖gradient v (c+s • x)‖) := by gcongr
  have hmul := mul_le_mul_of_nonneg_left hh hks
  unfold ABPGeometry.hessianMatrix at hmul
  nlinarith

end HarnackScale

namespace LaminarCover
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} {I : Type*} [MeasurableSpace X] [Countable I]

omit [MeasurableSpace X] [Countable I] in
lemma covered_by_maximal (B : I → Set X) (rank : I → ℕ) (S : Set I)
    (horder : ∀ i j, rank j<rank i → ¬Disjoint (B i) (B j) → B i⊆B j) :
    (⋃ i∈S, B i) ⊆ ⋃ i∈maximal B rank S, B i := by
  classical
  intro x hx
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
  let P : ℕ → Prop := fun k => ∃ j∈S, rank j=k ∧ x∈B j
  have hp : ∃ k, P k := ⟨rank i,i,hi,rfl,hxi⟩
  obtain ⟨j,hj,hr,hxj⟩ := Nat.find_spec hp
  refine mem_iUnion₂.mpr ⟨j,⟨hj,?_⟩,hxj⟩
  intro k hk hkj
  by_contra hnd
  have hxk := horder j k hkj hnd hxj
  have hh : P (rank k) := ⟨k,hk,rfl,hxk⟩
  have hm := Nat.find_min' hp hh
  rw [← hr] at hm
  exact (not_le_of_gt hkj) hm

omit [MeasurableSpace X] [Countable I] in
lemma maximal_disjoint (B : I → Set X) (rank : I → ℕ) (S : Set I)
    (hequal : ∀ i j, rank i=rank j → i≠j → Disjoint (B i) (B j)) :
    (maximal B rank S).PairwiseDisjoint B := by
  intro i hi j hj hij
  rcases lt_trichotomy (rank i) (rank j) with h|h|h
  · exact (hj.2 i hi.1 h).symm
  · exact hequal i j h hij
  · exact hi.2 j hj.1 h

theorem measure_le_of_laminar_cover (μ : Measure X) (B : I → Set X)
    (rank : I → ℕ) (S : Set I) (E F : Set X) (theta : ℝ≥0∞)
    (hB : ∀ i, MeasurableSet (B i))
    (horder : ∀ i j, rank j<rank i → ¬Disjoint (B i) (B j) → B i⊆B j)
    (hequal : ∀ i j, rank i=rank j → i≠j → Disjoint (B i) (B j))
    (hcover : E⊆⋃ i∈S, B i) (hinside : ∀ i∈S, B i⊆F)
    (hdensity : ∀ i∈S, μ (E∩B i)≤theta*μ (B i)) :
    μ E≤theta*μ F := by
  let T := maximal B rank S
  have hcov : E⊆⋃ i∈T, B i := hcover.trans (covered_by_maximal B rank S horder)
  have hdis : T.PairwiseDisjoint B := maximal_disjoint B rank S hequal
  have hc : E=⋃ i∈T, E∩B i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcov hx)
      exact mem_iUnion₂.mpr ⟨i,hi,hx,hxi⟩
    · intro hx
      obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
      exact hxi.1
  calc
    μ E = μ (⋃ i∈T, E∩B i) := congrArg μ hc
    _ ≤ ∑' i : T, μ (E∩B i) := measure_biUnion_le μ (to_countable T) _
    _ ≤ ∑' i : T, theta*μ (B i) := ENNReal.tsum_le_tsum (fun i => hdensity i i.property.1)
    _ = theta*(∑' i : T, μ (B i)) := ENNReal.tsum_mul_left
    _ = theta*μ (⋃ i∈T, B i) := by rw [measure_biUnion (to_countable T) hdis (fun i _=>hB i)]
    _ ≤ theta*μ F := by
      gcongr
      exact iUnion₂_subset (fun i hi=>hinside i hi.1)

end LaminarCover
namespace DyadicBoxes
open Set MeasureTheory BoxIntegral
open scoped ENNReal
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma good_parents_cover (μ : Measure (ι → ℝ)) (I : Box ι) {U : Set (ι → ℝ)}
    (hU : IsOpen U) {theta : ℝ≥0∞} (htheta : theta<1)
    (hpos : ∀ p, μ (box I p : Set (ι → ℝ))≠0)
    (hfin : ∀ p, μ (box I p : Set (ι → ℝ))≠⊤)
    (hroot : μ (U∩I)≤theta*μ I) :
    (U∩I) ⊆ ⋃ p ∈ {p : List (Set ι) |
      μ ((U∩I)∩box I p)≤theta*μ (box I p) ∧
      ∃ s : Set ι, theta*μ (box I (p++[s]))<μ ((U∩I)∩box I (p++[s]))},
        (box I p : Set (ι → ℝ)) := by
  classical
  intro x hx
  obtain ⟨n,hn⟩ := exists_small_level I hU hx.1
  obtain ⟨p,hp,hxp⟩ := level_cover I n hx.2
  have hsub : (box I p : Set (ι → ℝ))⊆U∩I := subset_inter (hn p hp hxp) (box_le I p)
  have hi : (U∩I)∩(box I p : Set (ι → ℝ))=box I p := inter_eq_right.mpr hsub
  have hbad : theta*μ (box I p)<μ ((U∩I)∩box I p) := by
    rw [hi]
    simpa only [one_mul] using ENNReal.mul_lt_mul_left (hpos p) (hfin p) htheta
  let P : ℕ → Prop := fun k => ∃ p : List (Set ι), p.length=k ∧ x∈box I p ∧
    theta*μ (box I p)<μ ((U∩I)∩box I p)
  have hex : ∃ k,P k := ⟨p.length,p,rfl,hxp,hbad⟩
  obtain ⟨q,hq,hxq,hbadq⟩ := Nat.find_spec hex
  have hqne : q≠[] := by
    intro he
    subst q
    have hb : theta*μ I<μ (U∩I) := by simpa only [box,inter_assoc,inter_self] using hbadq
    exact (not_lt_of_ge hroot) hb
  let a := q.dropLast
  let s := q.getLast hqne
  have hqa : a++[s]=q := List.dropLast_append_getLast hqne
  have hxa : x∈box I a := by
    rw [← hqa,box_append] at hxq
    exact box_le (box I a) [s] hxq
  have ha : a.length<q.length := by rw [← hqa,List.length_append,List.length_singleton]; omega
  have hgood : μ ((U∩I)∩box I a)≤theta*μ (box I a) := by
    by_contra he
    have hh : P a.length := ⟨a,rfl,hxa,lt_of_not_ge he⟩
    have hm := Nat.find_min' hex hh
    rw [← hq] at hm
    exact (not_le_of_gt ha) hm
  exact mem_iUnion₂.mpr ⟨a,⟨hgood,s,by rw [hqa]; exact hbadq⟩,hxa⟩

theorem ink_spots (μ : Measure (ι → ℝ)) (I : Box ι) {U F : Set (ι → ℝ)}
    (hU : IsOpen U) {theta : ℝ≥0∞} (htheta : theta<1)
    (hpos : ∀ p, μ (box I p : Set (ι → ℝ))≠0)
    (hfin : ∀ p, μ (box I p : Set (ι → ℝ))≠⊤)
    (hroot : μ (U∩I)≤theta*μ I)
    (hparent : ∀ (p : List (Set ι)) (s : Set ι),
      theta*μ (box I (p++[s]))<μ ((U∩I)∩box I (p++[s])) →
      (box I p : Set (ι → ℝ))⊆F) :
    μ (U∩I)≤theta*μ F := by
  let S : Set (List (Set ι)) := {p |
    μ ((U∩I)∩box I p)≤theta*μ (box I p) ∧
    ∃ s : Set ι, theta*μ (box I (p++[s]))<μ ((U∩I)∩box I (p++[s]))}
  apply LaminarCover.measure_le_of_laminar_cover μ
    (fun p => (box I p : Set (ι → ℝ))) List.length S (U∩I) F theta
    (fun p => (box I p).measurableSet_coe)
  · intro p q hpq hnd
    exact (comparable I p q hpq.le).resolve_right hnd
  · exact same_level_disjoint I
  · exact good_parents_cover μ I hU htheta hpos hfin hroot
  · intro p hp
    obtain ⟨s,hs⟩ := hp.2
    exact hparent p s hs
  · exact fun p hp => hp.1


theorem superlevel_tail (μ : Measure (ι → ℝ)) (I : Box ι) {v : (ι → ℝ) → ℝ}
    (hv : Continuous v) {M : ℝ} (hM : 1≤M) {theta : ℝ≥0∞} (htheta : theta<1)
    (hpos : ∀ p, μ (box I p : Set (ι → ℝ))≠0)
    (hfin : ∀ p, μ (box I p : Set (ι → ℝ))≠⊤)
    (hroot : μ ({x | M<v x}∩I)≤theta*μ I)
    (hstep : ∀ (p : List (Set ι)) (s : Set ι) (k : ℕ),
      (∃ x∈box I p, v x≤M^k) →
      μ ({x | M^(k+1)<v x}∩box I (p++[s]))≤theta*μ (box I (p++[s]))) :
    ∀ k : ℕ, μ ({x | M^k<v x}∩I)≤theta^k*μ I := by
  intro k
  induction k with
  | zero => simpa only [pow_zero,one_mul] using measure_mono (inter_subset_right :
      ({x | 1<v x}∩(I:Set (ι → ℝ)))⊆I)
  | succ k ih =>
    let U : Set (ι → ℝ) := {x | M^(k+1)<v x}
    have hUI : μ (U∩I)≤theta*μ I := by
      apply le_trans (measure_mono (inter_subset_inter_left _ (show U⊆{x | M<v x} from ?_))) hroot
      intro x hx
      exact (le_self_pow₀ hM (by omega : k+1≠0)).trans_lt hx
    have hh := ink_spots μ I (U:=U) (F:={x | M^k<v x}∩I)
      (isOpen_lt continuous_const hv) htheta hpos hfin hUI (fun p s hbad => by
        intro x hx
        refine ⟨?_,box_le I p hx⟩
        by_contra he
        have hs := hstep p s k ⟨x,hx,le_of_not_gt he⟩
        have hi : (U∩I)∩(box I (p++[s]) : Set (ι → ℝ))=U∩box I (p++[s]) := by
          ext y
          constructor
          · exact fun hy => ⟨hy.1.1,hy.2⟩
          · exact fun hy => ⟨⟨hy.1,box_le I (p++[s]) hy.2⟩,hy.2⟩
        rw [hi] at hbad
        exact (not_lt_of_ge hs) hbad)
    exact hh.trans (by
      simpa only [pow_succ',mul_assoc] using
        (mul_le_mul (le_rfl : theta≤theta) ih (by positivity) (by positivity)))

end DyadicBoxes

namespace WeakHarnack
open Set Filter Metric MeasureTheory BoxIntegral
open scoped Topology InnerProductSpace Matrix NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "I₀" => (CubeGeometry.unitBox : Box ι)

omit [DecidableEq ι] [Nonempty ι] in
lemma toLp_measure (I : Box ι) {v : E → ℝ} (hv : Continuous v) (t : ℝ) :
    volume ({x : ι → ℝ | t<v (WithLp.toLp 2 x)}∩I)=
      volume ({x : E | t<v x}∩{x | x.ofLp∈I}) := by
  exact (PiLp.volume_preserving_toLp ι).measure_preimage
    (((isOpen_lt continuous_const hv).measurableSet).inter
      (I.measurableSet_coe.preimage (EuclideanSpace.equiv ι ℝ).continuous.measurable)).nullMeasurableSet

omit [DecidableEq ι] [Nonempty ι] in
lemma toLp_box_measure (I : Box ι) : volume (I:Set (ι → ℝ))=volume {x : E | x.ofLp∈I} := by
  exact (PiLp.volume_preserving_toLp ι).measure_preimage
    (I.measurableSet_coe.preimage (EuclideanSpace.equiv ι ℝ).continuous.measurable).nullMeasurableSet

omit [DecidableEq ι] [Nonempty ι] in
lemma box_pos (I : Box ι) : volume (I:Set (ι → ℝ))≠0 := by
  rw [Box.coe_eq_pi,volume_pi,Measure.pi_pi]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [Real.volume_Ioc]
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (I.lower_lt_upper i))).ne'

omit [DecidableEq ι] [Nonempty ι] in
lemma rescale_density {v : E → ℝ} (hv : Continuous v) {M t : ℝ}
    (ht : 0<t) (p : List (Set ι)) {theta : ℝ≥0∞}
    (hh : volume ({x : E | M<t⁻¹*v (CubeGeometry.center (DyadicBoxes.box I₀ p)+CubeGeometry.side p • x)}∩
      {x | x.ofLp∈I₀})≤theta) :
    volume ({x : ι → ℝ | M*t<v (WithLp.toLp 2 x)}∩DyadicBoxes.box I₀ p)≤
      theta*volume (DyadicBoxes.box I₀ p : Set (ι → ℝ)) := by
  rw [toLp_measure _ hv,toLp_box_measure]
  let c := CubeGeometry.center (DyadicBoxes.box I₀ p)
  let s := CubeGeometry.side p
  have hs := CubeGeometry.side_pos p
  rw [AffineMeasure.preimage volume c hs ({x : E | M*t<v x}∩{x | x.ofLp∈DyadicBoxes.box I₀ p}),
    AffineMeasure.preimage volume c hs {x : E | x.ofLp∈DyadicBoxes.box I₀ p}]
  rw [preimage_inter,CubeGeometry.preimage_box,CubeGeometry.volume_unitCube,mul_one]
  have he : (fun x : E => c+s • x) ⁻¹' {x | M*t<v x}=
      {x | M<t⁻¹*v (c+s • x)} := by
    ext x
    change M*t<v (c+s • x) ↔ M<t⁻¹*v (c+s • x)
    rw [← div_eq_inv_mul,lt_div_iff₀ ht]
  rw [he,mul_comm theta]
  exact mul_le_mul (le_rfl : ENNReal.ofReal (s^Module.finrank ℝ E)≤_) hh (by positivity) (by positivity)

theorem exists_tail (b : OrthonormalBasis ι ℝ E) {ell T B : ℝ}
    (hell : 0<ell) (hT : 0≤T) (hB : 0≤B) :
    ∃ (M : ℝ) (theta : ℝ≥0∞), 1<M ∧ 0<theta ∧ theta<1 ∧
    ∀ (v : E → ℝ) (L : ℝ≥0) (A : E → Matrix ι ι ℝ),
      Differentiable ℝ v → LipschitzWith L (gradient v) →
      (∀ x∈closedBall (0:E) ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1)),0≤v x) →
      (∀ᵐ x ∂volume, x∈closedBall (0:E) ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1)) →
        (A x-ell • (1:Matrix ι ι ℝ)).PosSemidef) →
      (∀ᵐ x ∂volume, x∈closedBall (0:E) ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1)) →
        (A x).trace≤T) →
      (∀ᵐ x ∂volume, x∈closedBall (0:E) ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1)) →
        (A x*ABPGeometry.hessianMatrix b v x).trace≤1+B*‖gradient v x‖) →
      (∃ x : ι → ℝ, x∈I₀ ∧ v (WithLp.toLp 2 x)≤1) →
      ∀ k : ℕ, volume ({x : ι → ℝ | M^k<v (WithLp.toLp 2 x)}∩I₀)≤theta^k := by
  let R := 2*(Fintype.card ι:ℝ)+1
  let D := (Fintype.card ι:ℝ)/2+R
  have hN : 0≤(Fintype.card ι:ℝ) := Nat.cast_nonneg _
  obtain ⟨M,theta,hM,hth0,hth1,hstep⟩ := HarnackCube.exists_decay b hell hT hB
    (show 0≤2*(Fintype.card ι:ℝ) by positivity) (show 2*(Fintype.card ι:ℝ)<R by dsimp [R]; linarith)
  refine ⟨M,theta,hM,hth0,hth1,?_⟩
  intro v L A hv hL hvn hA hAT hP hlo
  have hsub : closedBall (0:E) R⊆closedBall 0 D := closedBall_subset_closedBall (by dsimp [D]; linarith)
  have hroot : volume ({x : ι → ℝ | M<v (WithLp.toLp 2 x)}∩I₀)≤theta*volume (I₀:Set (ι → ℝ)) := by
    rw [CubeGeometry.volume_unitBox,mul_one,toLp_measure _ hv.continuous]
    apply hstep v L A hv hL (fun x hx => hvn x (hsub hx))
      (hA.mono (fun x hh hx => hh (hsub hx))) (hAT.mono (fun x hh hx => hh (hsub hx)))
      (hP.mono (fun x hh hx => hh (hsub hx)))
    obtain ⟨x,hx,hvx⟩ := hlo
    refine ⟨WithLp.toLp 2 x,?_,hvx⟩
    rw [mem_closedBall,dist_zero_right]
    have hh := CubeGeometry.norm_unit hx
    linarith
  have hlocal (p : List (Set ι)) (a : Set ι) (k : ℕ)
      (hp : ∃ x∈DyadicBoxes.box I₀ p, v (WithLp.toLp 2 x)≤M^k) :
      volume ({x : ι → ℝ | M^(k+1)<v (WithLp.toLp 2 x)}∩DyadicBoxes.box I₀ (p++[a]))≤
        theta*volume (DyadicBoxes.box I₀ (p++[a]) : Set (ι → ℝ)) := by
    let c := CubeGeometry.center (DyadicBoxes.box I₀ (p++[a]))
    let s := CubeGeometry.side (p++[a])
    let t := M^k
    let w : E → ℝ := fun x => t⁻¹*v (c+s • x)
    have hs : 0<s := CubeGeometry.side_pos _
    have hs1 : s≤1 := CubeGeometry.side_le_one _
    have ht1 : 1≤t := one_le_pow₀ hM.le
    have ht : 0<t := zero_lt_one.trans_le ht1
    have hk : 0<t⁻¹ := inv_pos.mpr ht
    have hk1 : t⁻¹≤1 := inv_le_one_of_one_le₀ ht1
    have hQ := AffineMeasure.quasi volume c hs.ne'
    have hb (x : E) (hx : x∈closedBall (0:E) R) : c+s • x∈closedBall 0 D :=
      CubeGeometry.global_ball (p++[a]) hx
    have hwp := HarnackScale.pde_rescale volume b hv hL hB hP c hs hs1 hk hk1
    have hw := hstep w _ (fun x => A (c+s • x))
      (AffineRescale.differentiable hv c s t⁻¹) (AffineRescale.gradient_lipschitz hv hL c s t⁻¹)
      (fun x hx => mul_nonneg hk.le (hvn _ (hb x hx)))
      ((hQ.ae hA).mono (fun x hh hx => hh (hb x hx)))
      ((hQ.ae hAT).mono (fun x hh hx => hh (hb x hx)))
      (hwp.mono (fun x hh hx => hh (hb x hx)))
    have hloW : ∃ x∈closedBall (0:E) (2*(Fintype.card ι:ℝ)),w x≤1 := by
      obtain ⟨x,hx,hvx⟩ := hp
      refine ⟨s⁻¹ • (WithLp.toLp 2 x-c),?_,?_⟩
      · rw [mem_closedBall,dist_zero_right]
        exact CubeGeometry.normalized_parent p a hx
      · have he : c+s • (s⁻¹ • (WithLp.toLp 2 x-c))=WithLp.toLp 2 x := by
          rw [smul_inv_smul₀ hs.ne']
          abel
        dsimp only [w]
        rw [he,← div_eq_inv_mul]
        exact (div_le_one ht).mpr hvx
    have hh := rescale_density hv.continuous ht (p++[a]) (hw hloW)
    simpa only [t,pow_succ',Nat.add_comm] using hh
  have hh := DyadicBoxes.superlevel_tail volume I₀
    (hv.continuous.comp (PiLp.continuous_toLp 2 _)) hM.le hth1
    (fun p => box_pos _) (fun p => (Box.measure_coe_lt_top (DyadicBoxes.box I₀ p) volume).ne) hroot (by simpa only [Function.comp_apply] using hlocal)
  simpa only [CubeGeometry.volume_unitBox,mul_one,Function.comp_apply] using hh

end WeakHarnack

namespace TailLimit
open MeasureTheory Filter Set Topology
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

lemma superlevel {v : ℕ → X → ℝ} {w : X → ℝ} {K : Set X} {t : ℝ} {c : ℝ≥0∞}
    (hv : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (w x)))
    (hm : ∀ᶠ n in atTop, μ ({x | t<v n x}∩K)≤c) : μ ({x | t<w x}∩K)≤c := by
  let S (N : ℕ) := K∩⋂ n≥N, {x | t<v n x}
  have hS : Monotone S := by
    intro N M hNM x hx
    refine ⟨hx.1,?_⟩
    exact mem_iInter₂.mpr (fun n hn => mem_iInter₂.mp hx.2 n (hNM.trans hn))
  have hSc (N : ℕ) : μ (S N)≤c := by
    obtain ⟨i,hi,hiN⟩ := (hm.and (eventually_ge_atTop N)).exists
    apply le_trans (measure_mono (show S N⊆{x | t<v i x}∩K from ?_)) hi
    intro x hx
    exact ⟨mem_iInter₂.mp hx.2 i hiN,hx.1⟩
  have hUc : μ (⋃ N,S N)≤c := le_of_tendsto (tendsto_measure_iUnion_atTop hS) (Eventually.of_forall hSc)
  apply le_trans (measure_mono_ae (show ∀ᵐ x ∂μ, x∈({x | t<w x}∩K) → x∈⋃ N,S N from ?_)) hUc
  filter_upwards [hv] with x hx hh
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hx.eventually (Ioi_mem_nhds hh.1))
  exact mem_iUnion.mpr ⟨N,hh.2,mem_iInter₂.mpr (fun n hn => hN n hn)⟩

lemma finite_common {ι : Type*} [Fintype ι] {S : ι → Set X} {K : Set X} {c : ℝ≥0∞}
    (hS : ∀ i, μ (S i∩K)≤c) (hc : (Fintype.card ι:ℝ≥0∞)*c<μ K) :
    ∃ x∈K, ∀ i, x∉S i := by
  by_contra! h
  have hk : K⊆⋃ i,S i∩K := by
    intro x hx
    obtain ⟨i,hi⟩ := h x hx
    exact mem_iUnion.mpr ⟨i,hi,hx⟩
  have hh := (measure_mono (μ:=μ) hk).trans (measure_iUnion_le (μ:=μ) (fun i => S i∩K))
  have hs : (∑' i, μ (S i∩K))≤(Fintype.card ι:ℝ≥0∞)*c := by
    rw [tsum_fintype]
    simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hS i)
  exact (not_lt_of_ge (hh.trans hs)) hc

end TailLimit

namespace WeakHarnack
open MeasureTheory Set Metric Filter BoxIntegral
open scoped NNReal ENNReal Topology InnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "I₀" => (CubeGeometry.unitBox : Box ι)

theorem exists_limit_tail (b : OrthonormalBasis ι ℝ E) {ell T B : ℝ}
    (hell : 0<ell) (hT : 0≤T) (hB : 0≤B) :
    ∃ (M : ℝ) (theta : ℝ≥0∞), 1<M ∧ 0<theta ∧ theta<1 ∧
    ∀ (v : ℕ → E → ℝ) (L : ℕ → ℝ≥0) (A : ℕ → E → Matrix ι ι ℝ) (w : E → ℝ),
      (∀ n, Differentiable ℝ (v n)) → (∀ n, LipschitzWith (L n) (gradient (v n))) →
      (∀ n, ∀ x∈closedBall (0:E) ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1)),0≤v n x) →
      (∀ n, ∀ᵐ x ∂volume, x∈closedBall (0:E) ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1)) →
        (A n x-ell • (1:Matrix ι ι ℝ)).PosSemidef) →
      (∀ n, ∀ᵐ x ∂volume, x∈closedBall (0:E) ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1)) →
        (A n x).trace≤T) →
      (∀ n, ∀ᵐ x ∂volume, x∈closedBall (0:E) ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1)) →
        (A n x*ABPGeometry.hessianMatrix b (v n) x).trace≤1+B*‖gradient (v n) x‖) →
      (∀ᶠ n in atTop, ∃ x : ι → ℝ, x∈I₀ ∧ v n (WithLp.toLp 2 x)≤1) →
      (∀ᵐ x ∂volume, Tendsto (fun n => v n x) atTop (𝓝 (w x))) →
      ∀ k : ℕ, volume ({x : ι → ℝ | M^k<w (WithLp.toLp 2 x)}∩I₀)≤theta^k := by
  obtain ⟨M,theta,hM,ht0,ht1,hh⟩ := exists_tail b hell hT hB
  refine ⟨M,theta,hM,ht0,ht1,?_⟩
  intro v L A w hv hL hn hA hT hP hlo hconv k
  apply TailLimit.superlevel volume ((PiLp.volume_preserving_toLp ι).quasiMeasurePreserving.ae hconv)
  filter_upwards [hlo] with n hnlo
  exact hh (v n) (L n) (A n) (hv n) (hL n) (hn n) (hA n) (hT n) (hP n) hnlo k

end WeakHarnack

namespace SecondDifference
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma scalar_hasFDerivAt {φ : E → ℝ} {h z : E}
    (hp : DifferentiableAt ℝ φ (z+h)) (hm : DifferentiableAt ℝ φ (z-h))
    (h0 : DifferentiableAt ℝ φ z) :
    HasFDerivAt (scalar φ h)
      (fderiv ℝ φ (z+h)+fderiv ℝ φ (z-h)-(2:ℝ) • fderiv ℝ φ z) z := by
  have hp' := hp.hasFDerivAt.comp z ((hasFDerivAt_id z).add_const h)
  have hm' := hm.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const h)
  change HasFDerivAt (fun x => φ (x+h)+φ (x-h)-2*φ x) _ z
  convert (hp'.add hm').sub (h0.hasFDerivAt.const_smul (2:ℝ)) using 1 <;>
    rfl

omit [FiniteDimensional ℝ E] in
lemma vector_hasFDerivAt {X : E → E} {h z : E}
    (hp : DifferentiableAt ℝ X (z+h)) (hm : DifferentiableAt ℝ X (z-h))
    (h0 : DifferentiableAt ℝ X z) :
    HasFDerivAt (vector X h)
      (fderiv ℝ X (z+h)+fderiv ℝ X (z-h)-(2:ℝ) • fderiv ℝ X z) z := by
  have hp' := hp.hasFDerivAt.comp z ((hasFDerivAt_id z).add_const h)
  have hm' := hm.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const h)
  change HasFDerivAt (fun x => X (x+h)+X (x-h)-(2:ℝ) • X x) _ z
  convert (hp'.add hm').sub (h0.hasFDerivAt.const_smul (2:ℝ)) using 1 <;>
    rfl

end SecondDifference

namespace DeficitQuotient
open Set Matrix
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
lemma differentiable {φ : E → ℝ} (hd : Differentiable ℝ φ) (h : E) (M k : ℝ) :
    Differentiable ℝ (deficit φ h M k) := by
  intro x
  exact (((SecondDifference.scalar_hasFDerivAt (hd _) (hd _) (hd _)).const_mul k).const_sub M).differentiableAt

lemma gradient_deficit {φ : E → ℝ} (hd : Differentiable ℝ φ) (h : E) (M k : ℝ) (x : E) :
    gradient (deficit φ h M k) x=(-k) • SecondDifference.vector (gradient φ) h x := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [map_smul,toDual_gradient]
  have hh := ((SecondDifference.scalar_hasFDerivAt (hd (x+h)) (hd (x-h)) (hd x)).const_mul k).const_sub M
  rw [show (fun y => M-k*SecondDifference.scalar φ h y)=deficit φ h M k from rfl] at hh
  rw [hh.fderiv]
  simp only [SecondDifference.vector,map_sub,map_add,map_smul,toDual_gradient]
  module

lemma gradient_lipschitz {φ : E → ℝ} (hd : Differentiable ℝ φ) {L : ℝ≥0}
    (hL : LipschitzWith L (gradient φ)) (h : E) (M k : ℝ) :
    LipschitzWith (‖k‖₊*(L+L+2*L)) (gradient (deficit φ h M k)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [gradient_deficit hd,gradient_deficit hd,dist_eq_norm,← smul_sub,norm_smul]
  have hp := hL.norm_sub_le (x+h) (y+h)
  have hm := hL.norm_sub_le (x-h) (y-h)
  have h0 := hL.norm_sub_le x y
  simp only [add_sub_add_right_eq_sub] at hp
  simp only [sub_sub_sub_cancel_right] at hm
  have he : SecondDifference.vector (gradient φ) h x-SecondDifference.vector (gradient φ) h y =
      (gradient φ (x+h)-gradient φ (y+h))+(gradient φ (x-h)-gradient φ (y-h))-
      (2:ℝ) • (gradient φ x-gradient φ y) := by
    simp only [SecondDifference.vector,smul_sub]; abel
  rw [he]
  have hh := norm_sub_le ((gradient φ (x+h)-gradient φ (y+h))+
    (gradient φ (x-h)-gradient φ (y-h))) ((2:ℝ) • (gradient φ x-gradient φ y))
  have hj := norm_add_le (gradient φ (x+h)-gradient φ (y+h)) (gradient φ (x-h)-gradient φ (y-h))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  simp only [norm_neg,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_ofNat,coe_nnnorm,dist_eq_norm]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg k)
  nlinarith

lemma hessian_deficit (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ}
    (hd : Differentiable ℝ φ) {h x : E} (M k : ℝ)
    (hp : DifferentiableAt ℝ (gradient φ) (x+h))
    (hm : DifferentiableAt ℝ (gradient φ) (x-h))
    (h0 : DifferentiableAt ℝ (gradient φ) x) :
    hessian b (deficit φ h M k) x = (-k) •
      (hessian b φ (x+h)+hessian b φ (x-h)-(2:ℝ) • hessian b φ x) := by
  have he : gradient (deficit φ h M k) = fun x => (-k) • SecondDifference.vector (gradient φ) h x :=
    funext (gradient_deficit hd h M k)
  dsimp only [hessian]
  rw [he]
  have hh := (SecondDifference.vector_hasFDerivAt hp hm h0).const_smul (-k)
  change HasFDerivAt (fun x => (-k) • SecondDifference.vector (gradient φ) h x) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.toLinearMap_sub,ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul,map_smul,map_sub,map_add]

lemma pde (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} (hd : Differentiable ℝ φ)
    {h x : E} {M k F B σ : ℝ} (hk : 0≤k) {A : Matrix ι ι ℝ} {v : E}
    (hp : DifferentiableAt ℝ (gradient φ) (x+h))
    (hm : DifferentiableAt ℝ (gradient φ) (x-h))
    (h0 : DifferentiableAt ℝ (gradient φ) x)
    (hv : ‖v‖≤B) (hF : σ*SecondDifference.scalar φ h x≤F)
    (he : ⟪v,SecondDifference.vector (gradient φ) h x⟫_ℝ ≤
      (A*(hessian b φ (x+h)+hessian b φ (x-h)-(2:ℝ) • hessian b φ x)).trace+
        σ*SecondDifference.scalar φ h x) :
    (A*hessian b (deficit φ h M k) x).trace ≤ k*F+B*‖gradient (deficit φ h M k) x‖ := by
  rw [hessian_deficit b hd M k hp hm h0,Matrix.mul_smul,Matrix.trace_smul]
  rw [gradient_deficit hd,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hk]
  have hvip := abs_real_inner_le_norm v (SecondDifference.vector (gradient φ) h x)
  have hw := mul_le_mul_of_nonneg_right hv (norm_nonneg (SecondDifference.vector (gradient φ) h x))
  have hc := mul_le_mul_of_nonneg_left (le_trans (neg_le_abs _) (hvip.trans hw)) hk
  have h1 := mul_le_mul_of_nonneg_left he hk
  have h2 := mul_le_mul_of_nonneg_left hF hk
  simp only [smul_eq_mul]
  nlinarith

end DeficitQuotient

namespace AESlice
section
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_lines {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) (e : E) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂(volume : Measure ℝ), P (x+t • e) := by
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hNae : ∀ᵐ x ∂μ, x∉N := by
    rw [ae_iff]
    convert hN0 using 2; ext x; simp
  have hpre : MeasurableSet {p : E×ℝ | p.1+p.2 • e∉N} := by
    exact (hNm.preimage (show Measurable (fun p : E×ℝ => p.1+p.2 • e) by fun_prop)).compl
  have ht : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂μ, x+t • e∉N := by
    exact ae_of_all _ (fun t => (measurePreserving_add_right μ (t • e)).quasiMeasurePreserving.ae hNae)
  have hh := (ae_ae_comm hpre).mpr ht
  filter_upwards [hh] with x hx
  filter_upwards [hx] with t ht
  exact not_not.mp (fun hn => ht (hN hn))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma line_lipschitz (x e : E) : LipschitzWith ‖e‖₊ (fun t : ℝ => x+t • e) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  simp only [dist_eq_norm,add_sub_add_left_eq_sub,← sub_smul,norm_smul,Real.norm_eq_abs]
  exact le_of_eq (mul_comm _ _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma line_deriv (g : E → ℝ) {x e : E} {t : ℝ} (hg : DifferentiableAt ℝ g (x+t • e)) :
    HasDerivAt (fun s : ℝ => g (x+s • e)) ((fderiv ℝ g (x+t • e)) e) t := by
  simpa only [id_eq,one_smul,Function.comp_def] using hg.hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const e).const_add x)

lemma difference_le_ae {g : E → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) {e : E} {M : ℝ}
    (ha : ∀ᵐ x ∂μ, x∈Ω → DifferentiableAt ℝ g x ∧ fderiv ℝ g x e≤M)
    {x : E} {a : ℝ} (ha0 : 0≤a) (hx : x∈Ω) (hxa : x+a • e∈Ω) :
    g (x+a • e)-g x≤M*a := by
  have hl := ae_lines μ ha e
  let U : Set E := Ω∩(fun y => y+a • e) ⁻¹' Ω
  have hU : IsOpen U := hΩ.inter (hΩ.preimage (by fun_prop))
  have hxU : x∈U := ⟨hx,hxa⟩
  have hgood : ∀ᵐ y ∂μ, y∈U → g (y+a • e)-g y≤M*a := by
    filter_upwards [hl] with y hy hyU
    have hs (t : ℝ) (ht : t∈Icc 0 a) : y+t • e∈Ω := by
      by_cases haZ : a=0
      · have htZ : t=0 := by rw [haZ] at ht; linarith [ht.1,ht.2]
        simpa only [htZ,zero_smul,add_zero] using hyU.1
      have haP : 0<a := lt_of_le_of_ne ha0 (Ne.symm haZ)
      have hh := hc hyU.1 hyU.2 (show 0≤1-t/a by rw [sub_nonneg]; exact (div_le_one haP).mpr ht.2)
        (div_nonneg ht.1 ha0) (by ring : (1-t/a)+t/a=1)
      convert hh using 1
      dsimp only at hh ⊢
      simp only [smul_add,smul_smul,sub_smul,one_smul]
      rw [div_mul_cancel₀ _ haZ]
      abel
    have hline := hg.comp (line_lipschitz y e)
    have hac : AbsolutelyContinuousOnInterval (fun s => g (y+s • e)) 0 a :=
      hline.lipschitzOnWith.absolutelyContinuousOnInterval
    have hi := hac.intervalIntegrable_deriv
    have hd : ∀ᵐ t ∂(volume.restrict (Icc 0 a)), deriv (fun s => g (y+s • e)) t≤M := by
      filter_upwards [ae_restrict_of_ae hy,ae_restrict_mem measurableSet_Icc] with t ht hta
      rw [(line_deriv g (ht (hs t hta)).1).deriv]
      exact (ht (hs t hta)).2
    have hh := intervalIntegral.integral_mono_ae_restrict ha0 hi (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 a) hd
    rw [hac.integral_deriv_eq_sub] at hh
    simpa only [zero_smul,add_zero,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using hh
  have hdense := μ.dense_of_ae hgood
  have hcl := hdense.open_subset_closure_inter hU hxU
  have hclosed : IsClosed {y : E | g (y+a • e)-g y≤M*a} :=
    isClosed_le ((hg.continuous.comp (by fun_prop)).sub hg.continuous) continuous_const
  exact hclosed.closure_subset_iff.mpr (fun y hy => hy.2 hy.1) hcl

end
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
open scoped InnerProductSpace

lemma second_difference_le {φ : E → ℝ} (hd : Differentiable ℝ φ)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient φ))
    {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) {e : E} {M : ℝ}
    (ha : ∀ᵐ y ∂μ, y∈Ω → DifferentiableAt ℝ (gradient φ) y ∧
      ⟪(fderiv ℝ (gradient φ) y) e,e⟫_ℝ≤M)
    {x : E} {a : ℝ} (ha0 : 0≤a)
    (hs : ∀ t∈Icc (-a) a, x+t • e∈Ω) :
    φ (x+a • e)+φ (x-a • e)-2*φ x≤M*a^2 := by
  let g : E → ℝ := fun y => ⟪e,gradient φ y⟫_ℝ
  have hg : LipschitzWith (‖innerSL ℝ e‖₊ * L) g := by
    exact (innerSL ℝ e).lipschitz.comp hL
  have hga : ∀ᵐ y ∂μ, y∈Ω → DifferentiableAt ℝ g y ∧ fderiv ℝ g y e≤M := by
    filter_upwards [ha] with y hy hyΩ
    have hh := (innerSL ℝ e).hasFDerivAt.comp y (hy hyΩ).1.hasFDerivAt
    refine ⟨hh.differentiableAt,?_⟩
    change (fderiv ℝ (⇑(innerSL ℝ e) ∘ gradient φ) y) e≤M
    rw [hh.fderiv]
    simpa only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_comm] using (hy hyΩ).2
  let F : ℝ → ℝ := fun t => φ (x+t • e)+φ (x-t • e)-2*φ x-M*t^2
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => φ (x+s • e)) (g (x+t • e)) t := by
    have hh := (hd (x+t • e)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const e).const_add x)
    simpa only [Function.comp_def,id_eq,one_smul,← toDual_gradient,
      InnerProductSpace.toDual_apply_apply,g,real_inner_comm] using hh
  have hF (t : ℝ) : HasDerivAt F (g (x+t • e)-g (x-t • e)-2*M*t) t := by
    have hn := (hline (-t)).comp t (hasDerivAt_neg t)
    convert ((hline t).add hn |>.sub_const (2*φ x)).sub
      (((hasDerivAt_id t).pow 2).const_mul M) using 1 <;>
      first | rfl | (dsimp only [id_eq]; simp only [neg_smul,← sub_eq_add_neg]; ring) |
        (ext s; dsimp only [F,Function.comp_def,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id_eq];
          simp only [neg_smul,← sub_eq_add_neg])
  have hnon (t : ℝ) (ht : t∈Icc 0 a) : deriv F t≤0 := by
    have hm : x-t • e∈Ω := by
      simpa only [neg_smul,← sub_eq_add_neg] using hs (-t) (by constructor <;> linarith [ht.1,ht.2])
    have hp : x+t • e∈Ω := hs t ⟨by linarith [ht.1],ht.2⟩
    have he : x-t • e+(2*t) • e=x+t • e := by module
    have hh := difference_le_ae μ hg hΩ hc hga (show 0≤2*t by linarith [ht.1]) hm (he.symm ▸ hp)
    rw [he] at hh
    rw [(hF t).deriv]
    nlinarith
  have hfanti := antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) a)
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    (fun t ht => hnon t (interior_subset ht))
  have hh := hfanti ⟨le_rfl,ha0⟩ ⟨ha0,le_rfl⟩ ha0
  change F a≤F 0 at hh
  dsimp only [F] at hh
  simp only [zero_smul,add_zero,sub_zero,zero_pow (by decide : 2≠0),mul_zero] at hh
  linarith


end AESlice

namespace SecondQuotient
open Filter Set Topology Asymptotics
open scoped InnerProductSpace

lemma scalar_limit {f g : ℝ → ℝ} {A : ℝ} (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : HasDerivAt g A 0) :
    Tendsto (fun t => (f t+f (-t)-2*f 0)/t^2) (𝓝[≠] 0) (𝓝 A) := by
  let R : ℝ → ℝ := fun t => f t-f 0-t*g 0-t^2/2*A
  have hR (t : ℝ) : HasDerivAt R (g t-g 0-t*A) t := by
    convert ((hf t).sub_const (f 0) |>.sub ((hasDerivAt_id t).mul_const (g 0))).sub
      (((hasDerivAt_id t).pow 2).div_const 2 |>.mul_const A) using 1 <;> first | rfl | (dsimp only [R,id_eq]; ring)
  have hgo : (fun t => g t-g 0-t*A) =o[𝓝[univ] 0] (fun t : ℝ => (t-0)^1) := by
    simpa only [nhdsWithin_univ,sub_zero,pow_one,smul_eq_mul] using hg.isLittleO
  have hro := Convex.isLittleO_pow_succ_real convex_univ (mem_univ (0:ℝ))
    (fun t (_ : t∈(univ:Set ℝ)) => (hR t).hasDerivWithinAt) hgo
  have hlim : Tendsto (fun t => R t/t^2) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [nhdsWithin_univ,show R 0=0 by simp [R],sub_zero] using hro.tendsto_div_nhds_zero
  have hneg : Tendsto (fun t : ℝ => R (-t)/t^2) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,neg_sq] using hlim.comp (show Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) from by simpa only [neg_zero] using continuous_neg.tendsto (0:ℝ))
  have hsum := ((hlim.add hneg).add_const A).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ)≤𝓝 0)
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t≠0 := ht
  dsimp only [R]
  field_simp [ht0]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gradient_limit {φ : E → ℝ} (hd : Differentiable ℝ φ) {x e : E}
    (hH : DifferentiableAt ℝ (gradient φ) x) :
    Tendsto (fun t : ℝ => (φ (x+t • e)+φ (x-t • e)-2*φ x)/t^2)
      (𝓝[≠] 0) (𝓝 (⟪(fderiv ℝ (gradient φ) x) e,e⟫_ℝ)) := by
  let f : ℝ → ℝ := fun t => φ (x+t • e)
  let g : ℝ → ℝ := fun t => ⟪gradient φ (x+t • e),e⟫_ℝ
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • e) e t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const e).const_add x
  have hf (t : ℝ) : HasDerivAt f (g t) t := by
    have hh := (hd (x+t • e)).hasFDerivAt.comp_hasDerivAt t (hline t)
    simpa only [f,g,Function.comp_def,← toDual_gradient,InnerProductSpace.toDual_apply_apply] using hh
  have hg : HasDerivAt g (⟪(fderiv ℝ (gradient φ) x) e,e⟫_ℝ) 0 := by
    have h0 : x+(0:ℝ) • e=x := by simp
    have hh := (h0 ▸ hH.hasFDerivAt).comp_hasDerivAt 0 (hline 0)
    have hj := (innerSL ℝ e).hasFDerivAt.comp_hasDerivAt 0 hh
    simpa only [g,Function.comp_def,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
      h0,real_inner_comm] using hj
  simpa only [f,zero_smul,add_zero,neg_smul,← sub_eq_add_neg] using scalar_limit hf hg

end SecondQuotient

namespace C11Difference
open MeasureTheory Set Filter
open scoped InnerProductSpace NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma directional_bound {φ : E → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (gradient φ)) (x e : E) :
    ⟪(fderiv ℝ (gradient φ) x) e,e⟫_ℝ≤(L:ℝ)*‖e‖^2 := by
  have h1 := (fderiv ℝ (gradient φ) x).le_opNorm e
  have h2 := norm_fderiv_le_of_lipschitz ℝ hL (x₀:=x)
  have h3 := real_inner_le_norm ((fderiv ℝ (gradient φ) x) e) e
  nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg e),
    mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖e‖)]

lemma scalar_bound {φ : E → ℝ} (hd : Differentiable ℝ φ) {L : ℝ≥0}
    (hL : LipschitzWith L (gradient φ)) (x e : E) {a : ℝ} (ha : 0≤a) :
    φ (x+a • e)+φ (x-a • e)-2*φ x≤((L:ℝ)*‖e‖^2)*a^2 := by
  apply AESlice.second_difference_le volume hd hL isOpen_univ convex_univ _ ha
    (fun _ _ => mem_univ _)
  filter_upwards [hL.ae_differentiableAt (μ:=(volume:Measure E))] with y hy _
  exact ⟨hy,directional_bound hL y e⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma deficit_limit {φ : E → ℝ} (hd : Differentiable ℝ φ) {x e : E}
    (hH : DifferentiableAt ℝ (gradient φ) x) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 (0:ℝ))) (hδ0 : ∀ n, δ n≠0) {s : ℝ} (hs : s≠0) (M : ℝ) :
    Tendsto (fun n => M/s-(1/(s*(δ n)^2))*(φ (x+δ n • e)+φ (x-δ n • e)-2*φ x))
      atTop (𝓝 ((M-⟪(fderiv ℝ (gradient φ) x) e,e⟫_ℝ)/s)) := by
  have hδ' : Tendsto δ atTop (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ,Filter.Eventually.of_forall hδ0⟩
  have hh := ((SecondQuotient.gradient_limit (e:=e) hd hH).comp hδ').const_sub M |>.div_const s
  convert hh using 1
  ext n
  dsimp only [Function.comp_def]
  field_simp [hs,hδ0 n]

end C11Difference

namespace HessianTail
open MeasureTheory Set Filter Metric BoxIntegral
open scoped InnerProductSpace NNReal ENNReal Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "D" => ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1))
local notation "I₀" => (CubeGeometry.unitBox : Box ι)

theorem exists_constants (b : OrthonormalBasis ι ℝ E) {ell T B : ℝ}
    (hell : 0 < ell) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∃ (K : ℝ) (theta : ℝ≥0∞), 1 < K ∧ 0 < theta ∧ theta < 1 ∧
    ∀ (φ : E → ℝ) (L : ℝ≥0) (A : E → Matrix ι ι ℝ) (β : E → E)
      (e : E) (M s σ : ℝ) (Ω : Set E) (δ : ℕ → ℝ),
      Differentiable ℝ φ → LipschitzWith L (gradient φ) →
      IsOpen Ω → Convex ℝ Ω → 0 < s → 0 ≤ σ → σ*((L:ℝ)*‖e‖^2) ≤ s →
      (∀ n,0 < δ n) → Tendsto δ atTop (𝓝 0) →
      (∀ n,∀ x∈closedBall (0:E) D,∀ t∈Icc (-δ n) (δ n),x+t • e∈Ω) →
      (∀ᵐ x ∂volume, x∈Ω → ⟪(fderiv ℝ (gradient φ) x) e,e⟫_ℝ ≤ M) →
      (∀ᵐ x ∂volume,x∈closedBall (0:E) D → (A x-ell • (1:Matrix ι ι ℝ)).PosSemidef) →
      (∀ᵐ x ∂volume,x∈closedBall (0:E) D → (A x).trace ≤ T) →
      (∀ᵐ x ∂volume,x∈closedBall (0:E) D → ‖β x‖ ≤ B) →
      (∀ h : E,∀ᵐ x ∂volume,x∈closedBall (0:E) D →
        ⟪β x,SecondDifference.vector (gradient φ) h x⟫_ℝ  ≤
          (A x*(DeficitQuotient.hessian b φ (x+h)+DeficitQuotient.hessian b φ (x-h)-
              (2:ℝ) • DeficitQuotient.hessian b φ x)).trace+σ*SecondDifference.scalar φ h x) →
      (∃ y : ι → ℝ,y∈I₀ ∧ DifferentiableAt ℝ (gradient φ) (WithLp.toLp 2 y) ∧
        (M-⟪(fderiv ℝ (gradient φ) (WithLp.toLp 2 y)) e,e⟫_ℝ)/s < 1) →
      ∀ k : ℕ, volume ({x : ι → ℝ | K^k < (M-⟪(fderiv ℝ (gradient φ) (WithLp.toLp 2 x)) e,e⟫_ℝ)/s}∩I₀) ≤ theta^k := by
  obtain ⟨K,theta,hK,ht0,ht1,hh⟩ := WeakHarnack.exists_limit_tail b hell hT hB
  refine ⟨K,theta,hK,ht0,ht1,?_⟩
  intro φ L A β e M s σ Ω δ hd hL hΩ hc hs hσ hsF hδ hδlim hseg hupper hA htrace hβ hP hlo
  let v : ℕ → E → ℝ := fun n => DeficitQuotient.deficit φ (δ n • e) (M/s) (1/(s*(δ n)^2))
  let C : ℕ → ℝ≥0 := fun n => ‖1/(s*(δ n)^2)‖₊*(L+L+2*L)
  have hv (n : ℕ) : Differentiable ℝ (v n) := DeficitQuotient.differentiable hd _ _ _
  have hLv (n : ℕ) : LipschitzWith (C n) (gradient (v n)) := DeficitQuotient.gradient_lipschitz hd hL _ _ _
  have hH := hL.ae_differentiableAt (μ:=(volume:Measure E))
  have hnn (n : ℕ) (x : E) (hx : x∈closedBall (0:E) D) : 0 ≤ v n x := by
    have hbd := AESlice.second_difference_le volume hd hL hΩ hc
      (show ∀ᵐ y ∂volume, y∈Ω → DifferentiableAt ℝ (gradient φ) y ∧
        ⟪(fderiv ℝ (gradient φ) y) e,e⟫_ℝ ≤ M by filter_upwards [hH,hupper] with y hy hu hyΩ; exact ⟨hy,hu hyΩ⟩)
      (hδ n).le (hseg n x hx)
    have hk : 0 < 1/(s*(δ n)^2) := one_div_pos.mpr (mul_pos hs (sq_pos_of_pos (hδ n)))
    have hbd' := mul_le_mul_of_nonneg_left hbd hk.le
    have he : (1/(s*(δ n)^2))*(M*(δ n)^2)=M/s := by field_simp [ne_of_gt hs,ne_of_gt (hδ n)]
    rw [he] at hbd'
    exact sub_nonneg.mpr hbd'
  have hconv : ∀ᵐ x ∂volume,Tendsto (fun n => v n x) atTop
      (𝓝 ((M-⟪(fderiv ℝ (gradient φ) x) e,e⟫_ℝ)/s)) := by
    filter_upwards [hH] with x hx
    exact C11Difference.deficit_limit (e:=e) hd hx hδlim (fun n => ne_of_gt (hδ n)) (ne_of_gt hs) M
  have hpde (n : ℕ) : ∀ᵐ x ∂volume,x∈closedBall (0:E) D →
      (A x*ABPGeometry.hessianMatrix b (v n) x).trace ≤ 1+B*‖gradient (v n) x‖ := by
    have hHp := (measurePreserving_add_right (volume:Measure E) (δ n • e)).quasiMeasurePreserving.ae hH
    have hHm := (measurePreserving_add_right (volume:Measure E) (-(δ n • e))).quasiMeasurePreserving.ae hH
    filter_upwards [hH,hHp,hHm,hP (δ n • e),hβ] with x hx hxp hxm hep hb hxD
    simp only [← sub_eq_add_neg] at hxm
    have hF := mul_le_mul_of_nonneg_left (C11Difference.scalar_bound hd hL x e (hδ n).le) hσ
    have hpde := DeficitQuotient.pde b hd (M:=M/s) (k:=1/(s*(δ n)^2)) (by positivity)
      hxp hxm hx (hb hxD) hF (hep hxD)
    have he : (1/(s*(δ n)^2))*(σ*(((L:ℝ)*‖e‖^2)*(δ n)^2)) = (σ*((L:ℝ)*‖e‖^2))/s := by
      field_simp [ne_of_gt hs,ne_of_gt (hδ n)]
    rw [he] at hpde
    exact hpde.trans (add_le_add ((div_le_one hs).mpr hsF) le_rfl)
  have hlow : ∀ᶠ n in atTop,∃ y : ι → ℝ,y∈I₀ ∧ v n (WithLp.toLp 2 y) ≤ 1 := by
    obtain ⟨y,hy,hyd,hyl⟩ := hlo
    have hcy := C11Difference.deficit_limit (e:=e) hd hyd hδlim (fun n => ne_of_gt (hδ n)) (ne_of_gt hs) M
    filter_upwards [hcy.eventually (gt_mem_nhds hyl)] with n hn
    exact ⟨y,hy,hn.le⟩
  exact hh v C (fun _ => A) _ hv hLv hnn (fun _ => hA) (fun _ => htrace) hpde hlow hconv

end HessianTail

namespace SmallSequence
open Filter Set Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_shift_sequence (e : E) : ∃ δ : ℕ → ℝ,
    (∀ n,0<δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
    ∀ (R : ℝ) (n : ℕ) (x : E),x∈closedBall 0 R →
      ∀ t∈Icc (-δ n) (δ n),x+t • e∈ball 0 (R+1) := by
  let a : ℝ := 1/(2*(‖e‖+1))
  have ha : 0<a := by dsimp only [a]; positivity
  let δ : ℕ → ℝ := fun n => a/((n:ℝ)+1)
  have hδ (n : ℕ) : 0<δ n := div_pos ha (by positivity)
  have hδle (n : ℕ) : δ n≤a := by
    apply (div_le_iff₀ (by positivity : 0<(n:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul a
  refine ⟨δ,hδ,hlim,?_⟩
  intro R n x hx t ht
  have ht' : |t|≤δ n := abs_le.mpr ht
  have hn : δ n*‖e‖<1 := by
    have hb : a*‖e‖<1 := by
      dsimp only [a]
      rw [one_div_mul_eq_div]
      apply (div_lt_one (by positivity)).mpr
      linarith [norm_nonneg e]
    exact (mul_le_mul_of_nonneg_right (hδle n) (norm_nonneg e)).trans_lt hb
  rw [mem_ball,dist_zero_right]
  have hh := norm_add_le x (t • e)
  rw [norm_smul,Real.norm_eq_abs] at hh
  have hx' : ‖x‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have ht'' := mul_le_mul_of_nonneg_right ht' (norm_nonneg e)
  linarith

end SmallSequence

namespace OscillationEnvelope
open Set

variable {X : Type*} {f : X → ℝ} {K J : Set X}
lemma le_upper (h : BddAbove (f '' K)) {x : X} (hx : x∈K) : f x ≤ upper f K := le_csSup h (mem_image_of_mem f hx)
lemma lower_le (h : BddBelow (f '' K)) {x : X} (hx : x∈K) : lower f K ≤ f x := csInf_le h (mem_image_of_mem f hx)
lemma upper_mono (hJK : J⊆K) (hJ : J.Nonempty) (hK : BddAbove (f '' K)) : upper f J ≤ upper f K :=
  csSup_le (hJ.image f) (fun _ hx => le_csSup hK (image_mono hJK hx))
lemma lower_mono (hJK : J⊆K) (hJ : J.Nonempty) (hK : BddBelow (f '' K)) : lower f K ≤ lower f J :=
  le_csInf (hJ.image f) (fun _ hx => csInf_le hK (image_mono hJK hx))
lemma span_nonneg (hK : K.Nonempty) (hu : BddAbove (f '' K)) (hl : BddBelow (f '' K)) : 0 ≤ span f K := by
  obtain ⟨x,hx⟩ := hK
  exact sub_nonneg.mpr ((lower_le hl hx).trans (le_upper hu hx))

lemma exists_near_upper (hK : K.Nonempty) {η : ℝ} (hη : 0 < η) :
    ∃ x∈K,upper f K-η < f x := by
  obtain ⟨v,hv,hlt⟩ := exists_lt_of_lt_csSup (hK.image f) (show upper f K-η < sSup (f '' K) by dsimp only [upper]; linarith)
  obtain ⟨x,hx,rfl⟩ := hv
  exact ⟨x,hx,hlt⟩

lemma span_le_of_osc (hK : K.Nonempty) {C : ℝ}
    (h : ∀ x∈K,∀ y∈K,f x-f y ≤ C) : span f K ≤ C := by
  have h1 (x : X) (hx : x∈K) : f x-C ≤ lower f K := by
    apply le_csInf (hK.image f)
    rintro _ ⟨y,hy,rfl⟩
    linarith [h x hx y hy]
  have h2 : upper f K ≤ C+lower f K := by
    apply csSup_le (hK.image f)
    rintro _ ⟨x,hx,rfl⟩
    linarith [h1 x hx]
  exact sub_le_iff_le_add.mpr (by linarith)

lemma span_drop (hJK : J⊆K) (hJ : J.Nonempty) (hl : BddBelow (f '' K)) :
    span f J ≤ span f K-(upper f K-upper f J) := by
  have hh := lower_mono hJK hJ hl
  dsimp only [span]
  linarith

variable {ι : Type*} [Fintype ι]

lemma sum_drop {f : ι → X → ℝ} (hJK : J⊆K) (hJ : J.Nonempty)
    (hl : ∀ i,BddBelow (f i '' K)) :
    Finset.univ.sum (fun i => span (f i) J) ≤ Finset.univ.sum (fun i => span (f i) K) -
      Finset.univ.sum (fun i => upper (f i) K - upper (f i) J) := by
  have hh := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => span_drop (f:=f i) hJK hJ (hl i))
  simp only [Finset.sum_sub_distrib] at hh ⊢
  exact hh

end OscillationEnvelope

namespace HessianTail
open MeasureTheory Set Filter Metric BoxIntegral OscillationEnvelope
open scoped InnerProductSpace NNReal ENNReal Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "D" => ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1))
local notation "I₀" => (CubeGeometry.unitBox : Box ι)

omit [DecidableEq ι] [Nonempty ι] in
lemma direction_bound {φ : E → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (gradient φ)) (e x : E) :
    |direction φ e x| ≤ (L:ℝ)*‖e‖^2 := by
  have hh := abs_real_inner_le_norm (fderiv ℝ (gradient φ) x e) e
  have hb := (ContinuousLinearMap.le_opNorm (fderiv ℝ (gradient φ) x) e).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL (x₀:=x)) (norm_nonneg e))
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg e)])

omit [DecidableEq ι] [Nonempty ι] in
lemma direction_bddAbove {φ : E → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (gradient φ)) (e : E) (O : Set E) :
    BddAbove (direction φ e '' O) := by
  refine ⟨(L:ℝ)*‖e‖^2,?_⟩
  rintro _ ⟨x,_,rfl⟩
  exact (le_abs_self _).trans (direction_bound hL e x)

omit [DecidableEq ι] [Nonempty ι] in
lemma direction_bddBelow {φ : E → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (gradient φ)) (e : E) (O : Set E) :
    BddBelow (direction φ e '' O) := by
  refine ⟨-((L:ℝ)*‖e‖^2),?_⟩
  rintro _ ⟨x,_,rfl⟩
  exact (abs_le.mp (direction_bound hL e x)).1

omit [DecidableEq ι] [Nonempty ι] in
lemma cube_measure_inter {G : Set E} (hG : ∀ᵐ x ∂volume,x∈G) : volume (cube∩G)=1 := by
  have he : (cube∩G : Set E) =ᵐ[volume] (cube : Set E) := by
    filter_upwards [hG] with x hx
    exact propext ⟨fun h => h.1,fun h => ⟨h,hx⟩⟩
  rw [he.measure_eq]
  exact CubeGeometry.volume_unitCube

omit [DecidableEq ι] [Nonempty ι] in
lemma small_ball_nonempty {G : Set E} (hG : ∀ᵐ x ∂volume,x∈G) :
    (ball (0:E) (1/2)∩G).Nonempty := by
  exact ((volume:Measure E).dense_of_ae hG).inter_open_nonempty _ isOpen_ball (nonempty_ball.mpr (by norm_num))

theorem exists_envelope_constants (b : OrthonormalBasis ι ℝ E) {ell T B : ℝ}
    (hell : 0 < ell) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∃ (K : ℝ) (theta : ℝ≥0∞), 1 < K ∧ 0 < theta ∧ theta < 1 ∧
    ∀ (φ : E → ℝ) (L : ℝ≥0) (A : E → Matrix ι ι ℝ) (β : E → E)
      (G : Set E) (e : E) (σ F η : ℝ),
      Differentiable ℝ φ → LipschitzWith L (gradient φ) →
      (∀ᵐ x ∂volume,x∈G) → (∀ x∈G,DifferentiableAt ℝ (gradient φ) x) →
      0 ≤ σ → 0 ≤ F → σ*((L:ℝ)*‖e‖^2) ≤ F → 0 < η →
      (∀ᵐ x ∂volume,x∈closedBall (0:E) D → (A x-ell • (1:Matrix ι ι ℝ)).PosSemidef) →
      (∀ᵐ x ∂volume,x∈closedBall (0:E) D → (A x).trace ≤ T) →
      (∀ᵐ x ∂volume,x∈closedBall (0:E) D → ‖β x‖ ≤ B) →
      (∀ h : E,∀ᵐ x ∂volume,x∈closedBall (0:E) D →
        ⟪β x,SecondDifference.vector (gradient φ) h x⟫_ℝ ≤
          (A x*(DeficitQuotient.hessian b φ (x+h)+DeficitQuotient.hessian b φ (x-h)-
            (2:ℝ) • DeficitQuotient.hessian b φ x)).trace+σ*SecondDifference.scalar φ h x) →
      ∀ k : ℕ, volume ({x | K^k <
        (upper (direction φ e) (ball 0 (D+1)∩G)-direction φ e x)/
        (upper (direction φ e) (ball 0 (D+1)∩G)-upper (direction φ e) (ball 0 (1/2)∩G)+η+F)}∩(cube∩G)) ≤ theta^k := by
  obtain ⟨K,theta,hK,ht0,ht1,hh⟩ := exists_constants b hell hT hB
  refine ⟨K,theta,hK,ht0,ht1,?_⟩
  intro φ L A β G e σ F η hd hL hG hGd hσ hF hsF hη hA htrace hβ hP k
  let J : Set E := ball 0 (1/2)∩G
  let O : Set E := ball 0 (D+1)∩G
  let M := upper (direction φ e) O
  let m := upper (direction φ e) J
  have hJ : J.Nonempty := small_ball_nonempty hG
  have hJO : J⊆O := by
    apply inter_subset_inter_left
    exact ball_subset_ball (by have hn := Nat.cast_nonneg (α:=ℝ) (Fintype.card ι); linarith)
  have hdrop : 0 ≤ M-m := sub_nonneg.mpr (upper_mono hJO hJ (direction_bddAbove hL e O))
  let s := M-m+η+F
  have hs : 0 < s := by dsimp only [s]; linarith
  obtain ⟨δ,hδ,hδlim,hseg⟩ := SmallSequence.exists_shift_sequence e
  have hupper : ∀ᵐ x ∂volume,x∈ball (0:E) (D+1) → direction φ e x ≤ M := by
    filter_upwards [hG] with x hx hxB
    exact le_upper (direction_bddAbove hL e O) ⟨hxB,hx⟩
  have hlo : ∃ y : ι → ℝ,y∈I₀ ∧ DifferentiableAt ℝ (gradient φ) (WithLp.toLp 2 y) ∧
      (M-direction φ e (WithLp.toLp 2 y))/s < 1 := by
    obtain ⟨y,hy,hyv⟩ := exists_near_upper (f:=direction φ e) hJ hη
    refine ⟨y.ofLp,CubeGeometry.inner_ball_subset hy.1,hGd y hy.2,?_⟩
    apply (div_lt_one hs).mpr
    change M-direction φ e y < s
    dsimp only [s,m] at *
    linarith
  have hb := hh φ L A β e M s σ (ball 0 (D+1)) δ hd hL isOpen_ball (convex_ball _ _)
    hs hσ (by dsimp only [s]; linarith) hδ hδlim (fun n x hx t ht => hseg D n x hx t ht)
    hupper hA htrace hβ hP hlo k
  let Q : Set E := {x | K^k < (M-direction φ e x)/s}∩cube
  have hQm : MeasurableSet Q := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const
        ((measurable_const.sub ((measurable_fderiv_apply_const ℝ (gradient φ) e).inner measurable_const)).div_const s)
    · exact (CubeGeometry.unitBox : Box ι).measurableSet_coe.preimage (EuclideanSpace.equiv ι ℝ).continuous.measurable
  have he := (PiLp.volume_preserving_toLp ι).measure_preimage hQm.nullMeasurableSet
  change volume {x : ι → ℝ | WithLp.toLp 2 x∈Q}=volume Q at he
  have hQ : volume Q ≤ theta^k := by
    rw [← he]
    exact hb
  exact (measure_mono (show {x | K^k < (M-direction φ e x)/s}∩(cube∩G)⊆Q from fun _ hx => ⟨hx.1,hx.2.1⟩)).trans hQ

end HessianTail

namespace FiniteElliptic
open Set Metric Matrix
open scoped MatrixOrder Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ

omit [DecidableEq ι] in
lemma quadratic_continuous (e : ι → ℝ) : Continuous (fun D : Mat => quadratic D e) := by
  unfold quadratic Matrix.mulVec dotProduct
  fun_prop

omit [DecidableEq ι] in
lemma quadratic_smul (D : Mat) (e : ι → ℝ) (a : ℝ) :
    quadratic (a • D) e=a*quadratic D e := by
  simp only [quadratic,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma hermitian_closed : IsClosed {D : Mat | D.IsHermitian} :=
  isClosed_eq continuous_id.matrix_conjTranspose continuous_id

omit [DecidableEq ι] in
lemma positive_closed : IsClosed {D : Mat | D.PosSemidef} := by
  have he : {D : Mat | D.PosSemidef}={D | D.IsHermitian}∩⋂ e : ι → ℝ,{D | 0≤quadratic D e} := by
    ext D
    simp only [mem_ofPred_eq,mem_inter_iff,mem_iInter,Matrix.posSemidef_iff_dotProduct_mulVec,
      quadratic,star_trivial]
  rw [he]
  exact hermitian_closed.inter (isClosed_iInter (fun e => isClosed_le continuous_const (quadratic_continuous e)))

lemma trace_mul_nonneg {A D : Mat} (hA : A.PosSemidef) (hD : D.PosSemidef) :
    0≤(A*D).trace := by
  obtain ⟨Q,hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hQ]
  change 0≤(Qᴴ*Q*D).trace
  rw [← Matrix.trace_mul_cycle Q D Qᴴ]
  exact (hD.mul_mul_conjTranspose_same Q).trace_nonneg

lemma trace_mul_pos {A D : Mat} {ell : ℝ} (hell : 0<ell)
    (hA : (A-ell • (1:Mat)).PosSemidef) (hD : D.PosSemidef) (hne : D≠0) :
    0<(A*D).trace := by
  have hp : 0<D.trace := lt_of_le_of_ne hD.trace_nonneg (Ne.symm (hD.trace_eq_zero_iff.not.mpr hne))
  have hh := trace_mul_nonneg hA hD
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,
     Matrix.trace_smul,smul_eq_mul] at hh
  exact (mul_pos hell hp).trans_le (by linarith)

theorem exists_directions {ell T : ℝ} (hell : 0<ell) :
    ∃ (S : Finset (ι → ℝ)) (C : ℝ), 0<C ∧
    ∀ (A D : Mat) (d r : ℝ), (A-ell • (1:Mat)).PosSemidef → ‖A‖≤T →
      D.IsHermitian → 0≤d → 0≤r → (A*D).trace≤r →
      (∀ e∈S, -d≤quadratic D e) → ‖D‖≤C*(d+r) := by
  classical
  let K : Set Mat := {A | (A-ell • (1:Mat)).PosSemidef ∧ ‖A‖≤T}
  let H : Set Mat := {D | D.IsHermitian ∧ ‖D‖=1}
  have hK : IsCompact K := (isCompact_closedBall (0:Mat) T).of_isClosed_subset
    ((positive_closed.preimage (continuous_id.sub continuous_const)).inter
      (isClosed_le continuous_norm continuous_const))
    (fun A hA => by simpa only [mem_closedBall,dist_zero_right] using hA.2)
  have hH : IsCompact H := (isCompact_sphere (0:Mat) 1).of_isClosed_subset
    (hermitian_closed.inter (isClosed_eq continuous_norm continuous_const))
    (fun D hD => by simpa only [mem_sphere_zero_iff_norm] using hD.2)
  let U : (ι → ℝ) → Set (Mat×Mat) := fun e =>
    {p | 0<(p.1*p.2).trace ∨ quadratic p.2 e<0}
  have hU (e : ι → ℝ) : IsOpen (U e) := by
    dsimp only [U]
    exact (isOpen_lt continuous_const (show Continuous (fun p : Mat×Mat => (p.1*p.2).trace) by unfold Matrix.trace; fun_prop)).union
      (isOpen_lt ((quadratic_continuous e).comp continuous_snd) continuous_const)
  have hcover : K×ˢH⊆⋃ e,U e := by
    intro p hp
    by_cases ht : 0<(p.1*p.2).trace
    · exact mem_iUnion.mpr ⟨0,Or.inl ht⟩
    have hn : ¬ p.2.PosSemidef := by
      intro hd
      apply ht
      exact trace_mul_pos hell hp.1.1 hd (by intro he; simpa only [he,norm_zero,zero_ne_one] using hp.2.2)
    have hx : ∃ e,quadratic p.2 e<0 := by
      by_contra h
      push Not at h
      exact hn (Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hp.2.1,by simpa only [quadratic,star_trivial] using h⟩)
    obtain ⟨e,he⟩ := hx
    exact mem_iUnion.mpr ⟨e,Or.inr he⟩
  obtain ⟨S,hS⟩ := (hK.prod hH).elim_finite_subcover U hU hcover
  let g : Mat×Mat → ℝ := fun p => max (p.1*p.2).trace 0+∑ e∈S,max (-quadratic p.2 e) 0
  have hg : Continuous g := by
    apply Continuous.add
    · exact (show Continuous (fun p : Mat×Mat => (p.1*p.2).trace) by unfold Matrix.trace; fun_prop).max continuous_const
    · exact continuous_finsetSum _ (fun e _ => (((quadratic_continuous e).comp continuous_snd).neg.max continuous_const))
  have hgp : ∀ p∈K×ˢH,0<g p := by
    intro p hp
    obtain ⟨e,he,heU⟩ := mem_iUnion₂.mp (hS hp)
    have hn : 0≤∑ e∈S,max (-quadratic p.2 e) 0 := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
    rcases heU with ht|ht
    · exact add_pos_of_pos_of_nonneg (ht.trans_le (le_max_left _ _)) hn
    · have hh : 0<∑ e∈S,max (-quadratic p.2 e) 0 :=
        lt_of_lt_of_le ((neg_pos.mpr ht).trans_le (le_max_left _ (0:ℝ)))
          (Finset.single_le_sum (fun e _ => le_max_right (-quadratic p.2 e) 0) he)
      exact add_pos_of_nonneg_of_pos (le_max_right _ _) hh
  obtain ⟨δ,hδ,hdg⟩ := (hK.prod hH).exists_forall_le' hg.continuousOn hgp
  refine ⟨S,(1+(S.card:ℝ))/δ,by positivity,?_⟩
  intro A D d r hA hAT hD hd hr htr hdir
  by_cases hDz : D=0
  · simp only [hDz,norm_zero]
    positivity
  have hn : 0<‖D‖ := norm_pos_iff.mpr hDz
  let D' := ‖D‖⁻¹ • D
  have hD' : D'∈H := by
    constructor
    · exact hD.smul (IsSelfAdjoint.all ‖D‖⁻¹)
    · dsimp only [D']
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hn.ne']
  have hlow := hdg (A,D') ⟨⟨hA,hAT⟩,hD'⟩
  have hb : g (A,D')≤‖D‖⁻¹*(r+(S.card:ℝ)*d) := by
    have htr' : (A*D').trace≤‖D‖⁻¹*r := by
      dsimp only [D']
      simpa only [Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul] using
        mul_le_mul_of_nonneg_left htr (inv_nonneg.mpr hn.le)
    have he (e : ι → ℝ) (he : e∈S) : max (-quadratic D' e) 0≤‖D‖⁻¹*d := by
      dsimp only [D']
      rw [quadratic_smul]
      apply max_le
      · nlinarith [mul_le_mul_of_nonneg_left (hdir e he) (inv_nonneg.mpr hn.le)]
      · positivity
    dsimp only [g]
    calc
      _ ≤ ‖D‖⁻¹*r+∑ _e∈S,‖D‖⁻¹*d := add_le_add (max_le htr' (by positivity)) (Finset.sum_le_sum he)
      _ = _ := by simp; ring
  have hb' : δ*‖D‖≤r+(S.card:ℝ)*d := by
    have hh := mul_le_mul_of_nonneg_right (hlow.trans hb) hn.le
    have he : (‖D‖⁻¹*(r+(S.card:ℝ)*d))*‖D‖=r+(S.card:ℝ)*d := by field_simp
    rwa [he] at hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hδ).mpr
  have hh : r+(S.card:ℝ)*d≤(1+(S.card:ℝ))*(d+r) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg S.card : (0:ℝ)≤S.card) hr]
  convert hb'.trans hh using 1; ring

end FiniteElliptic

namespace EllipticOscillation
open MeasureTheory Set Filter Matrix FiniteElliptic
open scoped ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ

omit [DecidableEq ι] in
lemma quadratic_sub (A D : Mat) (e : ι → ℝ) :
    quadratic (A-D) e=quadratic A e-quadratic D e := by
  simp only [quadratic,Matrix.sub_mulVec,dotProduct_sub]

omit [DecidableEq ι] in
lemma abs_quadratic_le (D : Mat) (e : ι → ℝ) :
    |quadratic D e|≤(∑ i,|e i|)^2*‖D‖ := by
  simp only [quadratic,Matrix.mulVec,dotProduct]
  calc
    |∑ i,e i*(∑ j,D i j*e j)| ≤ ∑ i,|e i*(∑ j,D i j*e j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,|e i| *(∑ j,‖D‖*|e j|) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |∑ j,D i j*e j| ≤ ∑ j,|D i j*e j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j,‖D‖*|e j| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm D (i:=i) (j:=j)) (abs_nonneg _)
    _ = (∑ i,|e i|)^2*‖D‖ := by simp only [← Finset.mul_sum,← Finset.sum_mul]; ring

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem high_point_control {ell T : ℝ} (hell : 0<ell) :
    ∃ (S : Finset (ι → ℝ)) (C : ℝ), 0<C ∧
    (∀ (A D : Mat) (d r : ℝ), (A-ell • (1:Mat)).PosSemidef → ‖A‖≤T →
      D.IsHermitian → 0≤d → 0≤r → (A*D).trace≤r →
      (∀ e∈S, -d≤quadratic D e) → ‖D‖≤C*(d+r)) ∧
    ∀ (H A : X → Mat) (K : Set X) (M : (ι → ℝ) → ℝ) (d r : ℝ) (c : ℝ≥0∞),
      0≤d → 0≤r →
      (∀ x∈K, (A x-ell • (1:Mat)).PosSemidef ∧ ‖A x‖≤T) →
      (∀ x∈K, (H x).IsHermitian) →
      (∀ x∈K, ∀ y∈K, (A y*(H y-H x)).trace≤r) →
      (∀ x∈K, ∀ e∈S, quadratic (H x) e≤M e) →
      (∀ e∈S, μ ({x | d<M e-quadratic (H x) e}∩K)≤c) →
      (S.card:ℝ≥0∞)*c<μ K →
      ∃ y∈K, ∀ x∈K, ‖H y-H x‖≤C*(d+r) := by
  obtain ⟨S,C,hC,hbound⟩ := FiniteElliptic.exists_directions (ι:=ι) (T:=T) hell
  refine ⟨S,C,hC,hbound,?_⟩
  intro H A K M d r c hd hr hA hH htrace hM htail hmass
  have hmass' : (Fintype.card {e // e∈S}:ℝ≥0∞)*c<μ K := by simpa only [Fintype.card_coe] using hmass
  obtain ⟨y,hy,hgood⟩ := TailLimit.finite_common μ
    (S:=fun e : {e // e∈S} => {x | d<M e-quadratic (H x) e})
    (fun e => htail e e.prop) hmass'
  refine ⟨y,hy,fun x hx => ?_⟩
  apply hbound (A y) (H y-H x) d r (hA y hy).1 (hA y hy).2
    ((hH y hy).sub (hH x hx)) hd hr (htrace x hx y hy)
  intro e he
  have hg : M e-quadratic (H y) e≤d := not_lt.mp (hgood ⟨e,he⟩)

  rw [quadratic_sub]
  have hu := hM x hx e he
  linarith

lemma contraction {o i d r C : ℝ} (hC : 0≤C) (hdrop : i≤o-d)
    (hbound : i≤C*(d+r)) :
    i≤C/(C+1)*o+C/(C+1)*r := by
  have hp : 0<C+1 := by linarith
  have hm := mul_le_mul_of_nonneg_left hdrop hC
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← add_div]
  apply (le_div_iff₀ hp).mpr
  nlinarith

end EllipticOscillation

namespace FiniteOscillation
open MeasureTheory Set Filter Matrix FiniteElliptic OscillationEnvelope
open scoped ENNReal Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ
variable {X : Type*} [MeasurableSpace X]

omit [DecidableEq ι] [MeasurableSpace X] in
lemma sum_span_of_high_point (S : Finset (ι → ℝ)) (H : X → Mat) {J : Set X}
    (hJ : J.Nonempty) {y : X} {a : ℝ}
    (h : ∀ x∈J, ‖H y-H x‖ ≤ a) :
    (∑ e : {e // e∈S}, span (fun x => quadratic (H x) e.val) J) ≤
      (∑ e : {e // e∈S}, (∑ i, |e.val i|)^2)* (2*a) := by
  have hm (x z : X) (hx : x∈J) (hz : z∈J) : ‖H x-H z‖ ≤ 2*a := by
    calc
      ‖H x-H z‖ = ‖(H y-H z)-(H y-H x)‖ := by congr 1; abel
      _ ≤ ‖H y-H z‖+‖H y-H x‖ := norm_sub_le _ _
      _ ≤ 2*a := by linarith [h x hx,h z hz]
  have hd (e : {e // e∈S}) : span (fun x => quadratic (H x) e.val) J ≤
      (∑ i, |e.val i|)^2*(2*a) := by
    apply span_le_of_osc hJ
    intro x hx z hz
    rw [← EllipticOscillation.quadratic_sub]
    exact (le_abs_self _).trans ((EllipticOscillation.abs_quadratic_le _ _).trans
      (mul_le_mul_of_nonneg_left (hm x z hx hz) (sq_nonneg _)))
  simpa only [Finset.sum_mul] using Finset.sum_le_sum (s:=Finset.univ) (fun e _ => hd e)

theorem exists_contraction (μ : Measure X) {ell T K : ℝ} {theta : ℝ≥0∞}
    (hell : 0 < ell) (hK : 1 < K) (ht : theta < 1) :
    ∃ (S : Finset (ι → ℝ)) (C rho : ℝ), 0 < C ∧ 0 < rho ∧ rho < 1 ∧
    (∀ (A D : Mat) (d r : ℝ), (A-ell • (1:Mat)).PosSemidef → ‖A‖≤T →
      D.IsHermitian → 0≤d → 0≤r → (A*D).trace≤r →
      (∀ e∈S, -d≤quadratic D e) → ‖D‖≤C*(d+r)) ∧
    ∀ (H A : X → Mat) (J U O : Set X) (F r : ℝ),
      J.Nonempty → J⊆U → U⊆O → μ U=1 → 0 ≤ F → 0 ≤ r →
      (∀ x∈U, (A x-ell • (1:Mat)).PosSemidef ∧ ‖A x‖ ≤ T) →
      (∀ x∈U, (H x).IsHermitian) →
      (∀ x∈U, ∀ y∈U, (A y*(H y-H x)).trace ≤ r) →
      (∀ e∈S, BddAbove ((fun x => quadratic (H x) e) '' O)) →
      (∀ e∈S, BddBelow ((fun x => quadratic (H x) e) '' O)) →
      (∀ η : ℝ, 0 < η → ∀ e∈S, ∀ k : ℕ,
        μ ({x | K^k < (upper (fun z => quadratic (H z) e) O-quadratic (H x) e)/
          (upper (fun z => quadratic (H z) e) O-upper (fun z => quadratic (H z) e) J+η+F)}∩U) ≤ theta^k) →
      (∑ e : {e // e∈S}, span (fun x => quadratic (H x) e.val) J) ≤
        rho*(∑ e : {e // e∈S}, span (fun x => quadratic (H x) e.val) O)+rho*(F+r) := by
  classical
  obtain ⟨S,C,hC,hbound,hcontrol⟩ := EllipticOscillation.high_point_control (ι:=ι) μ (T:=T) hell
  have hlim : Tendsto (fun k : ℕ => (S.card:ℝ≥0∞)*theta^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a:=(S.card:ℝ≥0∞))
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ht) (Or.inr (by simp))
  obtain ⟨k,hk⟩ := (hlim.eventually_lt_const (by norm_num : (0:ℝ≥0∞)<1)).exists
  let W : ℝ := ∑ e : {e // e∈S}, (∑ i,|e.val i|)^2
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let D : ℝ := 2*W*C*(K^k+1)+1
  have hpow : 0 < K^k := pow_pos (by linarith) _
  have hD : 0 < D := by dsimp only [D]; positivity
  let rho : ℝ := D/(D+1)
  have hrho : 0 < rho := div_pos hD (by linarith)
  have hrho1 : rho < 1 := (div_lt_one (by linarith : 0<D+1)).mpr (by linarith)
  refine ⟨S,C,rho,hC,hrho,hrho1,hbound,?_⟩
  intro H A J U O F r hJ hJU hUO hμ hF hr hA hH htr hu hl htail
  let f : {e // e∈S} → X → ℝ := fun e x => quadratic (H x) e.val
  let drop : {e // e∈S} → ℝ := fun e => upper (f e) O-upper (f e) J
  let d : ℝ := ∑ e, drop e
  have he0 (e : {e // e∈S}) : 0 ≤ drop e :=
    sub_nonneg.mpr (upper_mono (hJU.trans hUO) hJ (hu e.val e.prop))
  have hd : 0 ≤ d := Finset.sum_nonneg (fun e _ => he0 e)
  have hed (e : {e // e∈S}) : drop e ≤ d := Finset.single_le_sum (fun e _ => he0 e) (Finset.mem_univ e)
  have hi (η : ℝ) (hη : 0 < η) : (∑ e, span (f e) J) ≤ D*(d+η+F+r) := by
    let a := K^k*(d+η+F)
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    have hta (e : ι → ℝ) (he : e∈S) :
        μ ({x | a < upper (fun z => quadratic (H z) e) O-quadratic (H x) e}∩U) ≤ theta^k := by
      apply (measure_mono (show {x | a < upper (fun z => quadratic (H z) e) O-quadratic (H x) e}∩U ⊆
        {x | K^k < (upper (fun z => quadratic (H z) e) O-quadratic (H x) e)/(drop ⟨e,he⟩+η+F)}∩U from ?_)).trans
        (htail η hη e he k)
      intro x hx
      refine ⟨(lt_div_iff₀ (by linarith [he0 ⟨e,he⟩] : 0<drop ⟨e,he⟩+η+F)).mpr ?_,hx.2⟩
      exact (mul_le_mul_of_nonneg_left (by linarith [hed ⟨e,he⟩]) hpow.le).trans_lt hx.1
    obtain ⟨y,hy,hyb⟩ := hcontrol H A U (fun e => upper (fun z => quadratic (H z) e) O) a r (theta^k)
      ha hr hA hH htr (fun x hx e he => le_upper (hu e he) (hUO hx)) hta (hμ ▸ hk)
    have hh := sum_span_of_high_point S H hJ
      (fun x hx => hyb x (hJU hx))
    have hcoef : 2*W*C*(K^k*(d+η+F)+r) ≤ D*(d+η+F+r) := by
      have h1 : K^k*(d+η+F)+r ≤ (K^k+1)*(d+η+F+r) := by nlinarith
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2*W*C)
      dsimp only [D]
      nlinarith
    change (∑ e, span (f e) J) ≤ W*(2*(C*(a+r))) at hh
    calc
      (∑ e, span (f e) J) ≤ W*(2*(C*(a+r))) := hh
      _ = 2*W*C*(K^k*(d+η+F)+r) := by dsimp only [a]; ring
      _ ≤ D*(d+η+F+r) := hcoef
  have hi0 : (∑ e, span (f e) J) ≤ D*(d+F+r) := by
    by_contra hn
    have hz : 0 < ((∑ e,span (f e) J)-D*(d+F+r))/(2*D) := div_pos (sub_pos.mpr (lt_of_not_ge hn)) (by positivity)
    have hh := hi _ hz
    have he : D*(((∑ e,span (f e) J)-D*(d+F+r))/(2*D)) = ((∑ e,span (f e) J)-D*(d+F+r))/2 := by field_simp
    nlinarith
  have hdrop := sum_drop (f:=f) (hJU.trans hUO) hJ (fun e => hl e.val e.prop)
  have hh := EllipticOscillation.contraction hD.le hdrop (show (∑ e,span (f e) J) ≤ D*(d+(F+r)) by simpa only [add_assoc] using hi0)
  exact hh

end FiniteOscillation

namespace HessianCoordinates
open Matrix
open scoped InnerProductSpace Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_toMatrix (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (e : ι → ℝ) :
    FiniteElliptic.quadratic (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap) e =
      ⟪A (vector b e),vector b e⟫_ℝ := by
  have he : (b.toBasis.repr (vector b e) : ι → ℝ)=e := by
    ext i
    simp only [OrthonormalBasis.coe_toBasis_repr_apply,vector,LinearIsometryEquiv.apply_symm_apply]
  have hm := LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis A.toLinearMap (vector b e)
  rw [he] at hm
  unfold FiniteElliptic.quadratic
  rw [hm,← b.repr.inner_map_map (A (vector b e)) (vector b e),EuclideanSpace.inner_eq_star_dotProduct]
  simp only [vector,LinearIsometryEquiv.apply_symm_apply,star_trivial]
  rfl

end HessianCoordinates

namespace InteriorOscillation
open Set Filter Metric Matrix MeasureTheory OscillationEnvelope FiniteElliptic
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ
local notation "D" => ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1))

theorem exists_constants (b : OrthonormalBasis ι ℝ E) {ell T Tm B : ℝ}
    (hell : 0 < ell) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∃ (S : Finset (ι → ℝ)) (C rho : ℝ), 0 < C ∧ 0 < rho ∧ rho < 1 ∧
    (∀ (A H : Mat) (d r : ℝ), (A-ell • (1:Mat)).PosSemidef → ‖A‖≤Tm →
      H.IsHermitian → 0≤d → 0≤r → (A*H).trace≤r →
      (∀ e∈S, -d≤quadratic H e) → ‖H‖≤C*(d+r)) ∧
    ∀ (φ : E → ℝ) (L : ℝ≥0) (A : E → Mat) (β : E → E)
      (G : Set E) (σ F r : ℝ),
      Differentiable ℝ φ → LipschitzWith L (gradient φ) →
      (∀ᵐ x ∂volume,x∈G) → (∀ x∈G,DifferentiableAt ℝ (gradient φ) x) →
      0 ≤ σ → 0 ≤ F → 0 ≤ r →
      (∀ e∈S,σ*((L:ℝ)*‖HessianCoordinates.vector b e‖^2) ≤ F) →
      (∀ x∈G, x∈closedBall (0:E) D →
        (A x-ell • (1:Mat)).PosSemidef ∧ (A x).trace ≤ T ∧ ‖A x‖≤Tm ∧ ‖β x‖≤B) →
      (∀ x∈G,(DeficitQuotient.hessian b φ x).IsHermitian) →
      (∀ x∈G, x∈HessianTail.cube → ∀ y∈G, y∈HessianTail.cube →
        (A y*(DeficitQuotient.hessian b φ y-DeficitQuotient.hessian b φ x)).trace ≤ r) →
      (∀ h : E,∀ᵐ x ∂volume,x∈closedBall (0:E) D →
        ⟪β x,SecondDifference.vector (gradient φ) h x⟫_ℝ ≤
          (A x*(DeficitQuotient.hessian b φ (x+h)+DeficitQuotient.hessian b φ (x-h)-
            (2:ℝ) • DeficitQuotient.hessian b φ x)).trace+σ*SecondDifference.scalar φ h x) →
      oscillation S (DeficitQuotient.hessian b φ) (ball 0 (1/2)∩G) ≤
        rho*oscillation S (DeficitQuotient.hessian b φ) (ball 0 (D+1)∩G)+rho*(F+r) := by
  obtain ⟨K,theta,hK,_,ht,htail⟩ := HessianTail.exists_envelope_constants b hell hT hB
  obtain ⟨S,C,rho,hC,hr0,hr1,hmat,hcon⟩ := FiniteOscillation.exists_contraction
    (ι:=ι) (T:=Tm) (volume:Measure E) hell hK ht
  refine ⟨S,C,rho,hC,hr0,hr1,hmat,?_⟩
  intro φ L A β G σ F r hd hL hG hGd hσ hF hr hSF hA hH htr hP
  have hcube (x : E) (hx : x∈HessianTail.cube) : x∈closedBall (0:E) D := by
    have hh := CubeGeometry.norm_unit hx
    rw [mem_closedBall_zero_iff]
    have hn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
    dsimp only at hh
    change ‖x‖ ≤ _ at hh
    linarith
  have hcoord (e : ι → ℝ) : (fun x => quadratic (DeficitQuotient.hessian b φ x) e)=
      HessianTail.direction φ (HessianCoordinates.vector b e) := by
    funext x
    exact HessianCoordinates.quadratic_toMatrix b _ e
  have hUO : HessianTail.cube∩G ⊆ ball (0:E) (D+1)∩G := by
    intro x hx
    refine ⟨?_,hx.2⟩
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hcube x hx.1)).trans_lt (lt_add_one D))
  apply hcon (DeficitQuotient.hessian b φ) A (ball 0 (1/2)∩G) (HessianTail.cube∩G)
    (ball 0 (D+1)∩G) F r (HessianTail.small_ball_nonempty hG)
    (fun x hx => ⟨CubeGeometry.inner_ball_subset hx.1,hx.2⟩)
    hUO (HessianTail.cube_measure_inter hG) hF hr
    (fun x hx => ⟨(hA x hx.2 (hcube x hx.1)).1,(hA x hx.2 (hcube x hx.1)).2.2.1⟩)
    (fun x hx => hH x hx.2) (fun x hx y hy => htr x hx.2 hx.1 y hy.2 hy.1)
  · intro e _
    rw [hcoord]
    exact HessianTail.direction_bddAbove hL _ _
  · intro e _
    rw [hcoord]
    exact HessianTail.direction_bddBelow hL _ _
  · intro η hη e he k
    simp only [congrFun (hcoord e)]
    apply htail φ L A β G (HessianCoordinates.vector b e) σ F η hd hL hG hGd hσ hF (hSF e he) hη
    · filter_upwards [hG] with x hx hxB
      exact (hA x hx hxB).1
    · filter_upwards [hG] with x hx hxB
      exact (hA x hx hxB).2.1
    · filter_upwards [hG] with x hx hxB
      exact (hA x hx hxB).2.2.2
    · exact hP

end InteriorOscillation

namespace MARescale
open Set Filter MeasureTheory Matrix
open scoped InnerProductSpace NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
lemma point_add (c : E) (r : ℝ) (x h : E) : point c r (x+h)=point c r x+r • h := by
  dsimp only [point]; module
omit [FiniteDimensional ℝ E] in
lemma point_sub (c : E) (r : ℝ) (x h : E) : point c r (x-h)=point c r x-r • h := by
  dsimp only [point]; module

omit [FiniteDimensional ℝ E] in
lemma scalar (φ : E → ℝ) (c : E) (r : ℝ) (h x : E) :
    SecondDifference.scalar (potential φ c r) h x =
      (1/r^2)*SecondDifference.scalar φ (r • h) (point c r x) := by
  change (1/r^2)*φ (point c r (x+h))+(1/r^2)*φ (point c r (x-h))-
    2*((1/r^2)*φ (point c r x))=_
  rw [point_add,point_sub]
  dsimp only [SecondDifference.scalar]
  ring

lemma gradient {φ : E → ℝ} (hd : Differentiable ℝ φ) (c : E) {r : ℝ} (hr : r≠0) (x : E) :
    _root_.gradient (potential φ c r) x=(1/r) • _root_.gradient φ (point c r x) := by
  rw [show potential φ c r=(fun x => (1/r^2)*φ (c+r • x)) from rfl,AffineRescale.gradient hd]
  congr 1
  field_simp

lemma gradient_lipschitz {φ : E → ℝ} (hd : Differentiable ℝ φ) {L : ℝ≥0}
    (hL : LipschitzWith L (_root_.gradient φ)) (c : E) {r : ℝ} (hr : 0<r) :
    LipschitzWith L (_root_.gradient (potential φ c r)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [gradient hd c (ne_of_gt hr),gradient hd c (ne_of_gt hr),dist_eq_norm,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hr),dist_eq_norm]
  have hh := hL.norm_sub_le (point c r x) (point c r y)
  have he : point c r x-point c r y=r • (x-y) := by dsimp only [point]; module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hh
  calc
    (1/r)*‖_‖ ≤ (1/r)*((L:ℝ)*(r*‖x-y‖)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp

lemma hessian (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} (hd : Differentiable ℝ φ)
    (c : E) {r : ℝ} (hr : r≠0) {x : E}
    (hg : DifferentiableAt ℝ (_root_.gradient φ) (point c r x)) :
    DeficitQuotient.hessian b (potential φ c r) x=DeficitQuotient.hessian b φ (point c r x) := by
  change LinearMap.toMatrix b.toBasis b.toBasis
    (fderiv ℝ (_root_.gradient (fun x => (1/r^2)*φ (c+r • x))) x).toLinearMap = _
  rw [AffineRescale.hessian hd c r (1/r^2) x hg,show (1/r^2)*r^2=1 by field_simp,one_smul]
  rfl

lemma vector {φ : E → ℝ} (hd : Differentiable ℝ φ) (c : E) {r : ℝ} (hr : r≠0) (h x : E) :
    SecondDifference.vector (_root_.gradient (potential φ c r)) h x=
      (1/r) • SecondDifference.vector (_root_.gradient φ) (r • h) (point c r x) := by
  simp only [SecondDifference.vector,gradient hd c hr,point_add,point_sub,smul_add,smul_sub,
    smul_smul]
  rw [mul_comm (2:ℝ) (1/r)]

lemma pde (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} (hd : Differentiable ℝ φ)
    (c : E) {r : ℝ} (hr : r≠0) {x h β : E} {A : Matrix ι ι ℝ}
    (h0 : DifferentiableAt ℝ (_root_.gradient φ) (point c r x))
    (hp : DifferentiableAt ℝ (_root_.gradient φ) (point c r (x+h)))
    (hm : DifferentiableAt ℝ (_root_.gradient φ) (point c r (x-h)))
    (he : ⟪β,SecondDifference.vector (_root_.gradient φ) (r • h) (point c r x)⟫_ℝ ≤
      (A*(DeficitQuotient.hessian b φ (point c r x+r • h)+DeficitQuotient.hessian b φ (point c r x-r • h)-
        (2:ℝ) • DeficitQuotient.hessian b φ (point c r x))).trace+
        SecondDifference.scalar φ (r • h) (point c r x)) :
    ⟪r • β,SecondDifference.vector (_root_.gradient (potential φ c r)) h x⟫_ℝ ≤
      (A*(DeficitQuotient.hessian b (potential φ c r) (x+h)+DeficitQuotient.hessian b (potential φ c r) (x-h)-
        (2:ℝ) • DeficitQuotient.hessian b (potential φ c r) x)).trace+
        r^2*SecondDifference.scalar (potential φ c r) h x := by
  rw [vector hd c hr,real_inner_smul_left,real_inner_smul_right,
    hessian b hd c hr hp,hessian b hd c hr hm,hessian b hd c hr h0,point_add,point_sub,scalar]
  convert he using 1 <;> field_simp

end MARescale

namespace OscillationScale
open Set Metric OscillationEnvelope
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dist_point (c : E) {s : ℝ} (hs : 0 ≤ s) (x : E) :
    dist (c+s • x) c=s*‖x‖ := by
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]

lemma image_ball (c : E) {s : ℝ} (hs : 0 < s) (R : ℝ) (G : Set E) :
    (fun x => c+s • x) '' (ball (0:E) R ∩ (fun x => c+s • x) ⁻¹' G)=ball c (s*R)∩G := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨?_,hx.2⟩
    rw [mem_ball,dist_point c hs.le]
    exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hx.1) hs
  · intro hy
    let x := s⁻¹ • (y-c)
    have he : c+s • x=y := by dsimp only [x]; rw [smul_inv_smul₀ hs.ne']; abel
    refine ⟨x,⟨?_,by change c+s • x∈G; rw [he]; exact hy.2⟩,he⟩
    rw [mem_ball_zero_iff]
    have hh := hy.1
    rw [mem_ball,← he,dist_point c hs.le] at hh
    exact (mul_lt_mul_iff_right₀ hs).mp (by simpa only [mul_comm] using hh)

lemma span_comp {X : Type*} {Y : Type*} (p : X → Y) (f : Y → ℝ) (U : Set X) :
    span (f ∘ p) U=span f (p '' U) := by
  unfold span upper lower
  rw [image_image]
  rfl

lemma span_congr {X : Type*} {f g : X → ℝ} {U : Set X} (h : ∀ x∈U,f x=g x) :
    span f U=span g U := by
  have he : f '' U=g '' U := image_congr h
  unfold span upper lower
  rw [he]

end OscillationScale

namespace MARescale
open Set Filter MeasureTheory Matrix
open scoped InnerProductSpace NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma differentiable_potential {φ : E → ℝ} (hd : Differentiable ℝ φ) (c : E) (r : ℝ) :
    Differentiable ℝ (potential φ c r) := by
  exact (hd.comp ((differentiable_const c).add (differentiable_id.const_smul r))).const_mul _

lemma differentiable_gradient {φ : E → ℝ} (hd : Differentiable ℝ φ) (c : E) {r : ℝ} (hr : r≠0)
    {x : E} (hg : DifferentiableAt ℝ (_root_.gradient φ) (point c r x)) :
    DifferentiableAt ℝ (_root_.gradient (potential φ c r)) x := by
  have he : _root_.gradient (potential φ c r)=(fun y => (1/r) • _root_.gradient φ (c+r • y)) := by
    funext y
    exact gradient hd c hr y
  rw [he]
  exact (hg.comp x ((differentiableAt_const c).add (differentiableAt_id.const_smul r))).const_smul _

end MARescale

namespace InteriorOscillation
open Set Filter Metric Matrix MeasureTheory OscillationEnvelope FiniteElliptic
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ
local notation "D" => ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1))

theorem exists_scaled_constants (b : OrthonormalBasis ι ℝ E) {ell T Tm B : ℝ}
    (hell : 0 < ell) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∃ (S : Finset (ι → ℝ)) (C rho : ℝ), 0 < C ∧ 0 < rho ∧ rho < 1 ∧
    (∀ (A H : Mat) (d r : ℝ), (A-ell • (1:Mat)).PosSemidef → ‖A‖≤Tm →
      H.IsHermitian → 0≤d → 0≤r → (A*H).trace≤r →
      (∀ e∈S, -d≤quadratic H e) → ‖H‖≤C*(d+r)) ∧
    ∀ (φ : E → ℝ) (L : ℝ≥0) (A : E → Mat) (β : E → E)
      (G : Set E) (c : E) (s F r : ℝ),
      Differentiable ℝ φ → LipschitzWith L (gradient φ) →
      (∀ᵐ x ∂volume,x∈G) → (∀ x∈G,DifferentiableAt ℝ (gradient φ) x) →
      0 < s → s ≤ 1 → 0 ≤ F → 0 ≤ r →
      (∀ e∈S,s^2*((L:ℝ)*‖HessianCoordinates.vector b e‖^2) ≤ F) →
      (∀ x∈G, x∈closedBall c (s*D) →
        (A x-ell • (1:Mat)).PosSemidef ∧ (A x).trace ≤ T ∧ ‖A x‖≤Tm ∧ ‖β x‖≤B) →
      (∀ x∈G,(DeficitQuotient.hessian b φ x).IsHermitian) →
      (∀ x∈G, x∈closedBall c (s*D) → ∀ y∈G, y∈closedBall c (s*D) →
        (A y*(DeficitQuotient.hessian b φ y-DeficitQuotient.hessian b φ x)).trace ≤ r) →
      (∀ h : E,∀ᵐ x ∂volume,
        ⟪β x,SecondDifference.vector (gradient φ) h x⟫_ℝ ≤
          (A x*(DeficitQuotient.hessian b φ (x+h)+DeficitQuotient.hessian b φ (x-h)-
            (2:ℝ) • DeficitQuotient.hessian b φ x)).trace+SecondDifference.scalar φ h x) →
      oscillation S (DeficitQuotient.hessian b φ) (ball c (s/2)∩G) ≤
        rho*oscillation S (DeficitQuotient.hessian b φ) (ball c (s*(D+1))∩G)+rho*(F+r) := by
  obtain ⟨S,C,rho,hC,hr0,hr1,hmat,hcon⟩ := exists_constants b (Tm:=Tm) hell hT hB
  refine ⟨S,C,rho,hC,hr0,hr1,hmat,?_⟩
  intro φ L A β G c s F r hd hL hG hGd hs hs1 hF hr hSF hA hH htr hP
  let p := MARescale.point c s
  let ψ := MARescale.potential φ c s
  let G' := p ⁻¹' G
  let A' := A ∘ p
  let β' : E → E := fun x => s • β (p x)
  have hQ := AffineMeasure.quasi (volume:Measure E) c hs.ne'
  have hG' : ∀ᵐ x ∂volume,x∈G' := hQ.ae hG
  have hψ := MARescale.differentiable_potential hd c s
  have hψL := MARescale.gradient_lipschitz hd hL c hs
  have hψd (x : E) (hx : x∈G') : DifferentiableAt ℝ (gradient ψ) x :=
    MARescale.differentiable_gradient hd c hs.ne' (hGd (p x) hx)
  have hess (x : E) (hx : x∈G') : DeficitQuotient.hessian b ψ x=DeficitQuotient.hessian b φ (p x) :=
    MARescale.hessian b hd c hs.ne' (hGd (p x) hx)
  have hpoint {x : E} (hx : x∈closedBall (0:E) D) : p x∈closedBall c (s*D) := by
    change dist (c+s • x) c ≤ s*D
    rw [OscillationScale.dist_point c hs.le]
    exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hs.le
  have hcube {x : E} (hx : x∈HessianTail.cube) : x∈closedBall (0:E) D := by
    rw [mem_closedBall_zero_iff]
    have hn := Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)
    have hh := CubeGeometry.norm_unit hx
    change ‖x‖ ≤ _ at hh
    linarith
  have hpde (h : E) : ∀ᵐ x ∂volume,x∈closedBall (0:E) D →
      ⟪β' x,SecondDifference.vector (gradient ψ) h x⟫_ℝ ≤
        (A' x*(DeficitQuotient.hessian b ψ (x+h)+DeficitQuotient.hessian b ψ (x-h)-
          (2:ℝ) • DeficitQuotient.hessian b ψ x)).trace+s^2*SecondDifference.scalar ψ h x := by
    have hgplus := (measurePreserving_add_right (volume:Measure E) h).quasiMeasurePreserving.ae hG'
    have hgminus := (measurePreserving_add_right (volume:Measure E) (-h)).quasiMeasurePreserving.ae hG'
    filter_upwards [hQ.ae (hP (s • h)),hG',hgplus,hgminus] with x hx hxG hxP hxM _
    simp only [← sub_eq_add_neg] at hxM
    exact MARescale.pde b hd c hs.ne' (hGd (p x) hxG) (hGd (p (x+h)) hxP) (hGd (p (x-h)) hxM) hx
  have hresult := hcon ψ L A' β' G' (s^2) F r hψ hψL hG' hψd (sq_nonneg s) hF hr hSF
    (fun x hx hxB => ⟨(hA (p x) hx (hpoint hxB)).1,(hA (p x) hx (hpoint hxB)).2.1,
      (hA (p x) hx (hpoint hxB)).2.2.1,?_⟩)
    (fun x hx => by rw [hess x hx]; exact hH (p x) hx)
    (fun x hx hxB y hy hyB => by
      rw [hess x hx,hess y hy]
      exact htr (p x) hx (hpoint (hcube hxB)) (p y) hy (hpoint (hcube hyB))) hpde
  · have hosc (R : ℝ) : oscillation S (DeficitQuotient.hessian b ψ) (ball 0 R∩G')=
        oscillation S (DeficitQuotient.hessian b φ) (ball c (s*R)∩G) := by
      unfold oscillation
      apply Finset.sum_congr rfl
      intro e _
      calc
        span (fun x => quadratic (DeficitQuotient.hessian b ψ x) e.val) (ball 0 R∩G') =
            span ((fun x => quadratic (DeficitQuotient.hessian b φ x) e.val) ∘ p) (ball 0 R∩G') :=
          OscillationScale.span_congr (fun x hx => by rw [hess x hx.2]; rfl)
        _ = span (fun x => quadratic (DeficitQuotient.hessian b φ x) e.val) (p '' (ball 0 R∩G')) :=
          OscillationScale.span_comp _ _ _
        _ = _ := by
          change span _ ((fun x => c+s • x) '' (ball 0 R∩(fun x => c+s • x) ⁻¹' G))=_
          rw [OscillationScale.image_ball c hs R G]
    rw [hosc (1/2),hosc (D+1)] at hresult
    simpa only [mul_one_div] using hresult
  · change ‖s • β (p x)‖≤B
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_left (hA (p x) hx (hpoint hxB)).2.2.2 hs.le).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 hB)

end InteriorOscillation
end

namespace OscillationIteration
open Filter
open scoped Topology

theorem exists_bound {rho q U C : ℝ} (hr0 : 0 ≤ rho) (hr1 : rho < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hU : 0 ≤ U) (hC : 0 ≤ C) :
    ∃ M theta : ℝ, 0 ≤ M ∧ 0 < theta ∧ theta < 1 ∧
      ∀ u : ℕ → ℝ, u 0 ≤ U → (∀ n,u (n+1) ≤ rho*u n+C*q^n) →
        ∀ n,u n ≤ M*theta^n := by
  let theta := (max rho q+1)/2
  have ht0 : 0 < theta := by dsimp only [theta]; have := le_max_left rho q; linarith
  have ht1 : theta < 1 := by dsimp only [theta]; have := max_lt hr1 hq1; linarith
  have hrt : rho < theta := by dsimp only [theta]; have := le_max_left rho q; have := max_lt hr1 hq1; linarith
  have hqt : q ≤ theta := by dsimp only [theta]; have := le_max_right rho q; have := max_lt hr1 hq1; linarith
  let M := U+C/(theta-rho)
  have hden : 0 < theta-rho := sub_pos.mpr hrt
  have hM : 0 ≤ M := add_nonneg hU (div_nonneg hC hden.le)
  have hMC : rho*M+C ≤ theta*M := by
    have he : (theta-rho)*(C/(theta-rho))=C := mul_div_cancel₀ _ (ne_of_gt hden)
    have hp := mul_nonneg hden.le hU
    dsimp only [M]
    nlinarith
  refine ⟨M,theta,hM,ht0,ht1,?_⟩
  intro u hu hrec n
  induction n with
  | zero => simpa only [pow_zero,mul_one] using hu.trans (le_add_of_nonneg_right (div_nonneg hC hden.le))
  | succ n ih =>
    calc
      u (n+1) ≤ rho*u n+C*q^n := hrec n
      _ ≤ rho*(M*theta^n)+C*theta^n := add_le_add
        (mul_le_mul_of_nonneg_left ih hr0) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hqt _) hC)
      _ = (rho*M+C)*theta^n := by ring
      _ ≤ (theta*M)*theta^n := mul_le_mul_of_nonneg_right hMC (pow_nonneg ht0.le _)
      _ = M*theta^(n+1) := by rw [pow_succ]; ring

end OscillationIteration

noncomputable section
namespace OscillationDecay
open Set Filter Metric OscillationEnvelope
open scoped Topology
variable {E : Type*} [MetricSpace E] {ι : Type*} [Fintype ι]

omit [MetricSpace E] in
lemma difference_le_total {f : ι → E → ℝ} {U : Set E}
    (hu : ∀ i,BddAbove (f i '' U)) (hl : ∀ i,BddBelow (f i '' U))
    {x y : E} (hx : x∈U) (hy : y∈U) (i : ι) : f i x-f i y ≤ total f U := by
  have h0 (j : ι) : 0 ≤ span (f j) U := span_nonneg ⟨x,hx⟩ (hu j) (hl j)
  calc
    f i x-f i y ≤ span (f i) U := sub_le_sub (le_upper (hu i) hx) (lower_le (hl i) hy)
    _ ≤ total f U := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

lemma ball_inter_nonempty {G : Set E} (hG : Dense G) (c : E) {r : ℝ} (hr : 0<r) :
    (ball c r∩G).Nonempty := by
  obtain ⟨x,hx,hxG⟩ := hG.inter_open_nonempty (ball c r) isOpen_ball ⟨c,mem_ball_self hr⟩
  exact ⟨x,hx,hxG⟩

end OscillationDecay

namespace OscillationDecay
open Set Filter Metric OscillationEnvelope
variable {E : Type*} [MetricSpace E] {ι : Type*} [Fintype ι]

theorem exists_grid_constants {A rho C s0 U : ℝ} (hA : 1<A) (hr0 : 0≤rho)
    (hr1 : rho<1) (hC : 0≤C) (hs0 : 0<s0) (hU : 0≤U) :
    ∃ M theta : ℝ, 0≤M ∧ 1/(2*A)<theta ∧ theta<1 ∧
      ∀ (f : ι → E → ℝ) (G : Set E) (c : E), Dense G →
      (∀ i,BddAbove (f i '' G)) → (∀ i,BddBelow (f i '' G)) →
      total f (ball c (s0*A)∩G)≤U →
      (∀ (s : ℝ),0 < s → s ≤ s0 → total f (ball c (s/2)∩G)≤
        rho*total f (ball c (s*A)∩G)+C*s) →
      ∀ n x, x∈G → dist x c<s0*A*(1/(2*A))^n →
        ∀ y,y∈G → dist y c<s0*A*(1/(2*A))^n →
        ∀ i,|f i x-f i y|≤M*theta^n := by
  let q := 1/(2*A)
  have hAp : 0<A := by linarith
  have hq0 : 0<q := by dsimp only [q]; positivity
  have hq1 : q<1 := by dsimp only [q]; rw [div_lt_one (by positivity)]; linarith
  obtain ⟨M,k,hM,hk0,hk1,hb⟩ := OscillationIteration.exists_bound hr0 hr1 hq0.le hq1 hU (mul_nonneg hC hs0.le)
  let theta := (max q k+1)/2
  have ht0 : q<theta := by dsimp only [theta]; have := le_max_left q k; have := max_lt hq1 hk1; linarith
  have hkt : k≤theta := by dsimp only [theta]; have := le_max_right q k; have := max_lt hq1 hk1; linarith
  have ht1 : theta<1 := by dsimp only [theta]; have := max_lt hq1 hk1; linarith
  refine ⟨M,theta,hM,ht0,ht1,?_⟩
  intro f G c _hG hu hl hu0 hcon
  let u : ℕ → ℝ := fun n => total f (ball c (s0*A*q^n)∩G)
  have hrec (n : ℕ) : u (n+1)≤rho*u n+(C*s0)*q^n := by
    have hh := hcon (s0*q^n) (mul_pos hs0 (pow_pos hq0 _))
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0.le hq1.le) hs0.le)
    have he : s0*A*q^(n+1)=s0*q^n/2 := by dsimp only [q]; rw [pow_succ]; field_simp
    unfold u
    rw [he]
    convert hh using 1
    ring_nf
  have hub (n : ℕ) : u n≤M*theta^n := (hb u (by simpa only [u,pow_zero,mul_one] using hu0) hrec n).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0.le hkt _) hM)
  intro n x hx hxB y hy hyB i
  have hup (j : ι) := (hu j).mono (image_mono (inter_subset_right (s:=ball c (s0*A*q^n))))
  have hlo (j : ι) := (hl j).mono (image_mono (inter_subset_right (s:=ball c (s0*A*q^n))))
  have hxy := difference_le_total hup hlo ⟨hxB,hx⟩ ⟨hyB,hy⟩ i
  have hyx := difference_le_total hup hlo ⟨hyB,hy⟩ ⟨hxB,hx⟩ i
  change f i x-f i y≤u n at hxy
  change f i y-f i x≤u n at hyx
  rw [abs_le]
  constructor <;> linarith [hub n]
end OscillationDecay
end

namespace GridHolder
open Metric

lemma exponent {q k : ℝ} (hq : 0<q) (hqk : q<k) (hk : k<1) :
    ∃ a : ℝ,0<a ∧ a<1 ∧ q^a=k := by
  have hk0 := hq.trans hqk
  have hq1 := hqk.trans hk
  have hlq := Real.log_neg hq hq1
  have hlk := Real.log_neg hk0 hk
  refine ⟨Real.log k/Real.log q,div_pos_of_neg_of_neg hlk hlq,?_,?_⟩
  · rw [div_lt_one_of_neg hlq]
    exact Real.log_lt_log hq hqk
  · rw [Real.rpow_def_of_pos hq]
    rw [mul_div_cancel₀ _ hlq.ne]
    exact Real.exp_log hk0

lemma pow_rpow {q k a : ℝ} (hq : 0≤q) (he : q^a=k) (N : ℕ) :
    (q^N)^a=k^N := by
  rw [← Real.rpow_natCast_mul hq,mul_comm,Real.rpow_mul_natCast hq,he]

theorem of_grid {E : Type*} {F : Type*} [MetricSpace E] [MetricSpace F]
    {f : E → F} {q k a M R : ℝ} (hq : 0<q) (hq1 : q<1) (hk : 0<k)
    (ha : 0<a) (he : q^a=k) (hM : 0≤M) (hR : 0<R)
    (hb : ∀ N x y,dist x y≤R*q^N → dist (f x) (f y)≤M*k^N) :
    ∀ x y,dist x y≤R → dist (f x) (f y)≤(M/k)*(dist x y/R)^a := by
  intro x y hxy
  by_cases hd : dist x y=0
  · have heq := dist_eq_zero.mp hd
    subst y
    simp [Real.zero_rpow ha.ne']
  · have hd0 : 0<dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one (div_pos hd0 hR)
      ((div_le_one hR).mpr hxy) hq hq1
    have hg := hb N x y (by have hh := (div_le_iff₀ hR).mp hhi; simpa only [mul_comm] using hh)
    have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤q^(N+1)) hlo.le ha.le
    rw [pow_rpow hq.le he,pow_succ] at hp
    calc
      dist (f x) (f y) ≤ M*k^N := hg
      _ = (M/k)*(k^N*k) := by field_simp
      _ ≤ (M/k)*(dist x y/R)^a := mul_le_mul_of_nonneg_left hp (div_nonneg hM hk.le)
end GridHolder
noncomputable section
namespace C11InteriorRegularity
open Set Filter Metric Matrix MeasureTheory OscillationEnvelope FiniteElliptic
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ
local notation "D" => ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1))

theorem holder_hessian_oai (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} {L : ℝ≥0}
    (hd : Differentiable ℝ φ) (hL : LipschitzWith L (gradient φ))
    {A : E → Mat} {β : E → E} {G : Set E}
    (hG : ∀ᵐ x ∂volume,x∈G) (hGd : ∀ x∈G,DifferentiableAt ℝ (gradient φ) x)
    (hH : ∀ x∈G,(DeficitQuotient.hessian b φ x).IsHermitian)
    {ell T Tm B K R : ℝ} {c0 : E}
    (hell : 0<ell) (hT : 0≤T) (hB : 0≤B) (hK : 0≤K) (hR : 0<R)
    (hA : ∀ x∈G,x∈ball c0 R →
      (A x-ell • (1:Mat)).PosSemidef ∧ (A x).trace≤T ∧ ‖A x‖≤Tm ∧ ‖β x‖≤B)
    (htr : ∀ x∈G,x∈ball c0 R → ∀ y∈G,y∈ball c0 R →
      (A y*(DeficitQuotient.hessian b φ y-DeficitQuotient.hessian b φ x)).trace≤K*dist x y)
    (hP : ∀ h : E,∀ᵐ x ∂volume,
      ⟪β x,SecondDifference.vector (gradient φ) h x⟫_ℝ ≤
        (A x*(DeficitQuotient.hessian b φ (x+h)+DeficitQuotient.hessian b φ (x-h)-
          (2:ℝ) • DeficitQuotient.hessian b φ x)).trace+SecondDifference.scalar φ h x) :
    ∃ a C r : ℝ,0<a ∧ a<1 ∧ 0≤C ∧ 0<r ∧
      ∀ x∈G,x∈ball c0 r → ∀ y∈G,y∈ball c0 r →
        dist (DeficitQuotient.hessian b φ x) (DeficitQuotient.hessian b φ y)≤C*dist x y^a := by
  classical
  have hDense : Dense G := Measure.dense_of_ae hG
  obtain ⟨S,C,rho,hC,hr0,hr1,hmat,hcon⟩ := InteriorOscillation.exists_scaled_constants b (Tm:=Tm) hell hT hB
  let f : {e // e∈S} → E → ℝ := fun e x => quadratic (DeficitQuotient.hessian b φ x) e.val
  have hcoord (e : {e // e∈S}) : f e=HessianTail.direction φ (HessianCoordinates.vector b e.val) := by
    funext x
    exact HessianCoordinates.quadratic_toMatrix b _ _
  have hu (e : {e // e∈S}) : BddAbove (f e '' G) := by
    rw [hcoord]; exact HessianTail.direction_bddAbove hL _ _
  have hl (e : {e // e∈S}) : BddBelow (f e '' G) := by
    rw [hcoord]; exact HessianTail.direction_bddBelow hL _ _
  let F0 := ∑ e∈S,(L:ℝ)*‖HessianCoordinates.vector b e‖^2
  have hF0 : 0≤F0 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hF0e (e) (he : e∈S) : (L:ℝ)*‖HessianCoordinates.vector b e‖^2≤F0 :=
    Finset.single_le_sum (f := fun e => (L:ℝ)*‖HessianCoordinates.vector b e‖^2) (fun _ _ => by positivity) he
  have hinit (c : E) (r : ℝ) (hr : 0<r) : OscillationDecay.total f (ball c r∩G)≤2*F0 := by
    calc
      _ ≤ ∑ e : {e // e∈S},2*((L:ℝ)*‖HessianCoordinates.vector b e.val‖^2) := by
        apply Finset.sum_le_sum
        intro e _
        apply span_le_of_osc (OscillationDecay.ball_inter_nonempty hDense c hr)
        intro x _ y _
        have hx := HessianTail.direction_bound hL (HessianCoordinates.vector b e.val) x
        have hy := HessianTail.direction_bound hL (HessianCoordinates.vector b e.val) y
        rw [hcoord]
        linarith [(abs_le.mp hx).2,(abs_le.mp hy).1]
      _ = 2*F0 := by
        rw [← Finset.mul_sum]
        exact congrArg (fun t : ℝ => 2*t) (Finset.sum_coe_sort S
          (fun e => (L:ℝ)*‖HessianCoordinates.vector b e‖^2))
  have hD : 0<D := by have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos; linarith
  have hD1 : 1<D+1 := by linarith
  let s0 := min 1 (R/(4*(D+1)))
  have hs0 : 0<s0 := lt_min zero_lt_one (by positivity)
  have hcon' (c : E) (hc : dist c c0<R/4) (s : ℝ) (hs : 0<s) (hss : s ≤ s0) :
      OscillationDecay.total f (ball c (s/2)∩G) ≤
        rho*OscillationDecay.total f (ball c (s*(D+1))∩G)+(rho*(F0+2*K*D))*s := by
    have hs1 : s≤1 := hss.trans (min_le_left _ _)
    have hsR : s*D<R/4 := by
      have hb := (le_div_iff₀ (show 0<4*(D+1) by positivity)).mp (hss.trans (min_le_right _ _))
      nlinarith
    have hxR {x : E} (hx : x∈closedBall c (s*D)) : x∈ball c0 R := by
      have hh := dist_triangle x c c0
      have hd := mem_closedBall.mp hx
      change dist x c0<R
      linarith
    have hh := hcon φ L A β G c s (s^2*F0) (2*K*D*s) hd hL hG hGd hs hs1
      (mul_nonneg (sq_nonneg s) hF0) (by positivity)
      (fun e he => mul_le_mul_of_nonneg_left (hF0e e he) (sq_nonneg s))
      (fun x hx hxB => hA x hx (hxR hxB)) hH
      (fun x hx hxB y hy hyB => (htr x hx (hxR hxB) y hy (hxR hyB)).trans (by
        have hxD := mem_closedBall.mp hxB
        have hyD := mem_closedBall.mp hyB
        have ht := dist_triangle x c y
        rw [dist_comm c y] at ht
        nlinarith [mul_le_mul_of_nonneg_left ht hK,mul_le_mul_of_nonneg_left hxD hK,mul_le_mul_of_nonneg_left hyD hK])) hP
    change OscillationDecay.total f _≤rho*OscillationDecay.total f _+rho*(s^2*F0+2*K*D*s) at hh
    apply hh.trans
    apply add_le_add_right
    have hsq : s^2 ≤ s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hF0,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hF0) hr0.le]
  obtain ⟨M,theta,hM,hqt,ht1,hgrid⟩ := OscillationDecay.exists_grid_constants
    («E» := EuclideanSpace ℝ ι) (ι := {e // e∈S}) (C := rho*(F0+2*K*D)) hD1 hr0.le hr1 (mul_nonneg hr0.le (by positivity)) hs0 (show 0≤2*F0 by positivity)
  let q := 1/(2*(D+1))
  have hq0 : 0<q := by dsimp only [q]; positivity
  have ht0 : 0<theta := hq0.trans hqt
  have hq1 : q<1 := hqt.trans ht1
  obtain ⟨a,ha,ha1,hea⟩ := GridHolder.exponent hq0 hqt ht1
  let R0 := s0*(D+1)/2
  have hR0 : 0<R0 := by dsimp only [R0]; positivity
  let r := min (R/4) (R0/2)
  have hr : 0<r := lt_min (by positivity) (by positivity)
  let X := G∩ball c0 r
  let H : X → Mat := fun x => DeficitQuotient.hessian b φ x.val
  have hX {x : X} : dist x.val c0<R/4 := (mem_ball.mp x.property.2).trans_le (min_le_left _ _)
  have hXR {x : X} : x.val∈ball c0 R := by change dist x.val c0<R; linarith [hX (x:=x)]
  have hbound (N : ℕ) (x y : X) (hxy : dist x y≤R0*q^N) :
      dist (H x) (H y)≤(C*(M+K*R0))*theta^N := by
    have hdir := hgrid f G x.val hDense hu hl (hinit x.val _ (by positivity)) (hcon' x.val hX) N
    have hp : 0<s0*(D+1)*q^N := by positivity
    have hdxy : dist y.val x.val<s0*(D+1)*q^N := by
      rw [dist_comm]
      change dist x.val y.val≤R0*q^N at hxy
      dsimp only [R0] at hxy
      linarith
    have hh := hmat (A x.val) (H x-H y) (M*theta^N) (K*R0*theta^N)
      (hA x.val x.property.1 hXR).1 (hA x.val x.property.1 hXR).2.2.1
      ((hH x.val x.property.1).sub (hH y.val y.property.1)) (by positivity) (by positivity)
      ((htr y.val y.property.1 hXR x.val x.property.1 hXR).trans (by
        rw [dist_comm]
        have hpow := pow_le_pow_left₀ hq0.le hqt.le N
        change dist x.val y.val≤R0*q^N at hxy
        nlinarith [mul_le_mul_of_nonneg_left hxy hK,mul_le_mul_of_nonneg_left hpow (mul_nonneg hK hR0.le)]))
      (fun e he => by
        have hh := hdir x.val x.property.1 (by simpa only [dist_self] using hp) y.val y.property.1 hdxy ⟨e,he⟩
        have hl := (abs_le.mp hh).1
        simpa only [H,f,quadratic,Matrix.sub_mulVec,dotProduct_sub] using hl)
    rw [dist_eq_norm]
    exact hh.trans_eq (by ring)
  have hh := GridHolder.of_grid hq0 hq1 ht0 ha hea (show 0≤C*(M+K*R0) by positivity) hR0 hbound
  refine ⟨a,(C*(M+K*R0)/theta)/R0^a,r,ha,ha1,by positivity,hr,?_⟩
  intro x hx hxr y hy hyr
  let x' : X := ⟨x,hx,hxr⟩
  let y' : X := ⟨y,hy,hyr⟩
  have hdxy : dist x' y'≤R0 := by
    have ht := dist_triangle x c0 y
    rw [dist_comm c0 y] at ht
    have hxx := (mem_ball.mp hxr).trans_le (min_le_right _ _)
    have hyy := (mem_ball.mp hyr).trans_le (min_le_right _ _)
    change dist x y≤R0
    linarith
  have hc := hh x' y' hdxy
  change dist (DeficitQuotient.hessian b φ x) (DeficitQuotient.hessian b φ y)≤
    C*(M+K*R0)/theta*(dist x y/R0)^a at hc
  convert hc using 1
  rw [Real.div_rpow dist_nonneg hR0.le]
  ring
end C11InteriorRegularity
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.C11InteriorRegularity.holder_hessian_oai.{u_1} := @OAI.C11InteriorRegularity.holder_hessian_oai.{u_1}

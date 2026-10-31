-- Prove2me | solution 1 for OAI.GeneralMahler.general_mahler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:06:07.136821+00:00
-- url     : https://prove2.me/submissions/09a95d64-5a6f-47ac-8348-c12da69c9648

import Mathlib
import Definitions.Def_GeneralMahler
import Definitions.Def_OAIQ026G002
import Theorems.Thm_OAI_GeneralMahler_Complete_profile_input
import Theorems.Thm_OAI_GeneralMahler_ProjField_C_bound

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Growth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Elementary bounds used throughout the Gaussian and layer integrations.
We keep pointwise growth and measurability hypotheses separate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Real
open scoped Topology ENNReal RealInnerProductSpace NNReal
namespace GeneralMahler
section
variable {X Y E F : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

namespace PolyBound

variable {f g : X → E}
theorem prodMk {h : X → F} (hf : PolyBound f) (hh : PolyBound h) :
    PolyBound fun x => (f x,h x) := by
  obtain ⟨C,n,hc,hb⟩ := common hf hh
  exact ⟨C,n,hc,fun x => max_le (hb x).1 (hb x).2⟩
end PolyBound
end

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rapid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Polynomial growth and rapid layer decay with polynomial loss in
the Gaussian variables. Fubini and moment estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise
namespace GeneralMahler
section
variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace mixed
variable {f g : X → Y → E}

lemma poly (hf : mixed f) : PolyBound f.uncurry := by
  obtain ⟨C,k,hc,h⟩ := hf 0
  simp only [pow_zero,mul_one] at h
  refine ⟨C,k,hc,?_⟩
  rintro ⟨x,y⟩
  apply (h x y).trans
  gcongr; exact le_max_right ..

end mixed

section Integrals
variable [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsAddHaarMeasure μ]

variable [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  {ν : Measure Y} [IsGaussian ν]

lemma mixed_integrable {f : X → Y → E}
    (h : mixed f) (hf : AEStronglyMeasurable f.uncurry (μ.prod ν)) :
    Integrable f.uncurry (μ.prod ν) := by
  let p := Module.finrank ℝ X+1
  let g := fun x:X => ((1+‖x‖)^p)⁻¹
  obtain ⟨C,l,hc,H⟩ := h p
  have hg : Integrable g μ := envelope_inv_int
  have hi := (hg.mul_prod ((integrable_envelope l (μ := ν)).const_mul C))
  apply hi.mono' hf (ae_of_all _ ?_)
  rintro ⟨x,y⟩
  change ‖f x y‖ ≤ g x * (C*(1+‖y‖)^l)
  dsimp only [g]; rw [ mul_comm, ← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  apply H
end Integrals
end
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LayerMeasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 scalar measure from the derivative of avH. Real densities here. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology ENNReal
namespace GeneralMahler

open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (q : ProjField m)

lemma H_infty : Tendsto q.avH atTop (𝓝 q.s0) := by
  have he := (q.tail_H.tail_limit).add_const q.s0
  rw [zero_add] at he
  apply Tendsto.congr' _ he
  filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx

  simp [st,(le_of_lt (show 0<x from hx))]

lemma H_bot : Tendsto q.avH atBot (𝓝 0) := by
  have h : rapid (fun x : ℝ => q.avH (-x)-st (-x)*q.s0) := by
    intro n
    obtain ⟨C,hc,h⟩ := q.tail_H n
    exact ⟨C,hc,fun x => by simpa only [norm_neg] using h (-x)⟩
  have he : Tendsto (fun x:ℝ => q.avH (-x)) atTop (𝓝 0) := by
    apply Tendsto.congr' _ h.tail_limit
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx

    simp [st,show ¬0 ≤ -x by have ha : 0 < x := hx; linarith]
  simpa [Function.comp_def] using he.comp tendsto_neg_atBot_atTop

theorem integrable_w : Integrable q.layerW := by simpa using q.w_moment 0
theorem integral_w : ∫ x, q.layerW x = q.s0 := by
  simpa using integral_of_hasDerivAt_of_tendsto q.H_deriv q.integrable_w q.H_bot q.H_infty

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Spectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Order and functional calculus for real symmetric matrices. -/
noncomputable section
open Set Filter Matrix Real
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
variable {m : ℕ} {A B : Mat m}

theorem cfc_eigen' (f : ℝ → ℝ) (h : A.IsHermitian) (i : Fin m) :
    op (cfc f A) (h.eigenvectorBasis i) = (f (h.eigenvalues i)) • h.eigenvectorBasis i := by
  open Unitary in
    rw [Matrix.IsHermitian.cfc_eq h,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    apply WithLp.ofLp_injective
    rw [show op = _ from (rfl : op = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)),
      Matrix.ofLp_toEuclideanCLM]
    simp only [← mulVec_mulVec, h.star_eigenvectorUnitary_mulVec, Matrix.diagonal_mulVec_single,
      Function.comp_apply,mul_one]
    ext j; simp [dotProduct,mulVec, Pi.single_apply,mul_comm]

variable {l r : ℝ}

lemma cfc_herm (f : ℝ→ℝ) (A : Mat m) : (cfc f A).IsHermitian :=
  (cfc_predicate _ _ : IsSelfAdjoint _)

lemma scalar_cfc_order (f : ℝ→ℝ) (A : Mat m) (hA : A.IsHermitian) :
    (scalar m l ≤ cfc f A ↔ ∀ x∈spectrum ℝ A, l ≤ f x) ∧
    (cfc f A ≤ scalar m r ↔ ∀ x∈spectrum ℝ A, f x ≤ r) := by
  rw [scalar_eq,scalar_eq]
  have hi : IsSelfAdjoint A := hA
  have hf : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  exact ⟨algebraMap_le_cfc_iff .., cfc_le_algebraMap_iff ..⟩

lemma spectrum_order (A : Mat m) (hA:A.IsHermitian) :
    (scalar m l ≤ A ↔ ∀ x∈spectrum ℝ A, l ≤ x) ∧
    (A ≤ scalar m r ↔ ∀ x∈spectrum ℝ A, x ≤ r) := by
  have hi : IsSelfAdjoint A := hA
  have h := scalar_cfc_order (l := l) (r := r) id A hA
  rw [cfc_id ℝ A] at h
  exact h

lemma spectrum_norm_box {K : ℝ} (hk : 0 ≤ K) (ha : A.IsHermitian)
    (hb : scalar m (-K) ≤ A) (ht : A ≤ scalar m K) : ‖A‖ ≤ K := by
  have hi : IsSelfAdjoint A := ha
  conv_lhs => rw [← cfc_id ℝ A]
  apply norm_cfc_le hk
  intro x hx
  rw [Real.norm_eq_abs,abs_le]; exact ⟨(spectrum_order (l := -K) (r := K) _ ha).1.mp hb x hx,
    (spectrum_order (l := -K) (r := K) _ ha).2.mp ht x hx⟩

lemma spectrum_poly_le (f : ℝ → ℝ) {C : ℝ} {n : ℕ} (hc : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^n) (ha : A.IsHermitian) :
    ‖cfc f A‖ ≤ C*(1+‖A‖)^n := by
  have hi : IsSelfAdjoint A := ha
  apply norm_cfc_le (by positivity)
  intro x hx
  apply (hf _).trans
  have he := norm_apply_le_norm_cfc (id : ℝ → ℝ) A hx
  rw [cfc_id ℝ A] at he
  change ‖x‖ ≤ ‖A‖ at he
  gcongr

lemma cfc_continuous_herm (f : ℝ → ℝ) (hf : Continuous f) :
    ContinuousOn (cfc f) {x : Mat m | x.IsHermitian} :=
  (continuousOn_id.cfc_of_mem_nhdsSet (s := univ) f Filter.univ_mem
    (fun _ h => (h : IsSelfAdjoint _)) hf.continuousOn)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MatrixBox
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Spectral boxes and clipping; normalization preparation. -/
noncomputable section
open Set Filter Real Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

lemma specBox_compact (a b:ℝ) : IsCompact (specBox m a b) := by
  let K := |a|+|b|
  have h₁ : ∀ A∈specBox m a b, ‖A‖ ≤ K := by
    intro A h
    apply spectrum_norm_box (by dsimp [K]; positivity) h.1
    · apply le_trans _ h.2.1; apply scalar_le'
      unfold K; linarith [neg_abs_le a,abs_nonneg b]
    apply le_trans h.2.2
    apply scalar_le'; unfold K; linarith [le_abs_self b,abs_nonneg a]
  have hc : IsClosed (specBox m a b) := by
    have h : specBox m a b =
        {A:Mat m|star A=A} ∩ ((⋂ v:Rn m,{A|a*‖v‖^2≤ opPair v v A}) ∩
          (⋂ v:Rn m,{A|opPair v v A ≤ b*‖v‖^2})) := by
      ext; simp only [mem_inter_iff, mem_iInter,mem_ofPred_eq,opPair_apply,mem_box_form]; rfl
    rw [h]
    exact (isClosed_eq continuous_star continuous_id).inter ((isClosed_iInter fun i =>
      isClosed_le continuous_const (opPair i i).continuous).inter (isClosed_iInter fun i =>
        isClosed_le (opPair i i).continuous continuous_const))
  exact (isCompact_closedBall (0:Mat m) K).of_isClosed_subset hc (by intro x hx; simpa using h₁ x hx)

lemma specBox_convex (a b:ℝ) : Convex ℝ (specBox m a b) := by
  intro x hx y hy l k hl hk hlk
  rw [mem_box_form] at hx hy ⊢
  have he (v : Rn m) :
      ⟪v,op (l • x+k • y) v⟫ = l * ⟪v,op x v⟫ + k*⟪v,op y v⟫ := by
    change opPair v v _ = l * opPair v v _ + k*opPair v v _
    simp only [_root_.map_add,_root_.map_smul,smul_eq_mul]
  refine ⟨(hx.1.smul (show IsSelfAdjoint l from rfl)).add
    (hy.1.smul (show IsSelfAdjoint k from rfl)),fun v => ?_,fun v => ?_⟩
  · rw [he]
    have hi := add_le_add (mul_le_mul_of_nonneg_left (hx.2.1 v) hl)
      (mul_le_mul_of_nonneg_left (hy.2.1 v) hk)
    rwa [← add_mul,hlk,one_mul] at hi
  rw [he]
  have hi := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 v) hl)
    (mul_le_mul_of_nonneg_left (hy.2.2 v) hk)
  rwa [← add_mul,hlk,one_mul] at hi

lemma specBox_nonempty (m : ℕ) (a b:ℝ) (h:a ≤ b) : (specBox m a b).Nonempty :=
  ⟨scalar m a,scalar_sym ..,le_rfl,scalar_le' _ _ h⟩

lemma cont_clip (a b:ℝ) : ContinuousOn (clip a b) {A : Mat m|A.IsHermitian} :=
  cfc_continuous_herm _ (by fun_prop)

lemma clip_mem (a b:ℝ) (hab:a ≤ b) {A : Mat m} (hA:A.IsHermitian) :
    clip a b A ∈ specBox m a b := by
  obtain ⟨h,h'⟩ := scalar_cfc_order (fun x:ℝ=>max a (min x b)) A hA (l := a) (r := b)
  exact ⟨cfc_herm .., h.mpr (fun _ _ => le_max_left ..),
    h'.mpr (fun _ _ => max_le hab (min_le_right ..))⟩

/-- If the projection update B ↦ clip(B+M) is fixed
and neither kind of extreme eigenvector with wrong outward sign exists,
then no clipping occurs and M=0. -/
lemma clip_eq {a b:ℝ} (hab:a ≤ b) {B M:Mat m}
    (he : clip a b (B+M)=B) (h : (B+M).IsHermitian)
    (h₁ : ∀ v : Rn m, ‖v‖=1 → op B v=a • v → 0 ≤ ⟪v,op M v⟫)
    (h₂ : ∀ v : Rn m, ‖v‖=1 → op B v=b • v → ⟪v,op M v⟫ ≤ 0) : M=0 := by
  let f := fun x:ℝ=>max a (min x b)
  have hb : ∀ i, f (h.eigenvalues i)=h.eigenvalues i := by
    intro i
    let v := h.eigenvectorBasis i
    let x := h.eigenvalues i
    change f x=x
    have hh : op B v=f x • v := by
      have hi := cfc_eigen' f h i
      change op (clip a b (B+M)) v=_ at hi
      rwa [he] at hi
    have hv : ‖v‖=1 := h.eigenvectorBasis.orthonormal.1 _
    have hw : ⟪v,op M v⟫ = x-f x := by
      have h : op (B+M) v=x • v := op_eigen h i
      rw [_root_.map_add,_root_.add_apply,hh] at h
      have he := congrArg (fun y=>inner ℝ v y) h
      rw [inner_add_right,real_inner_smul_right,real_inner_smul_right, real_inner_self_eq_norm_sq,hv] at he
      linarith
    rcases lt_or_ge x a with hx|hx
    · have he : f x=a := max_eq_left ((min_le_left ..).trans hx.le)
      have H := h₁ _ hv (he ▸ hh); rw [hw, he] at H; linarith
    rcases le_or_gt x b with hy|hy
    · dsimp [f]; rw [min_eq_left hy,max_eq_right hx]
    have he : f x=b := by dsimp [f]; rw [min_eq_right hy.le,max_eq_right hab]
    have H := h₂ _ hv (he ▸ hh); rw [hw,he] at H; linarith
  have hn : IsSelfAdjoint (B+M) := h
  have hu : clip a b (B+M)= B+M := by
    conv_rhs => rw [← cfc_id ℝ (B+M)]
    apply cfc_congr
    rw [h.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i,rfl⟩; apply hb
  rw [he] at hu; simpa [eq_comm] using hu

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Parameter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Coordinate and covariance parameters in compact boxes. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

lemma inv_norm_box (Q:ℝ) (hq : 0<Q) {A:Mat m} (hA:A∈specBox m Q⁻¹ Q)
    (e:Rn m≃L[ℝ]Rn m) (he : e.toContinuousLinearMap = op A) :
    ‖A‖ ≤ Q ∧ ‖e.symm.toContinuousLinearMap‖ ≤ Q := by
  have hi := inv_pos.mpr hq
  refine ⟨spectrum_norm_box hq.le hA.1 ((scalar_le' _ _ (by linarith)).trans hA.2.1)
    hA.2.2,e.symm.toContinuousLinearMap.opNorm_le_bound hq.le fun x=>?_⟩
  change ‖e.symm x‖ ≤ Q*‖x‖
  let y := e.symm x
  have hv := (mem_box_form.mp hA).2.1 y
  have hh : op A y=x := by rw [← he]; exact e.apply_symm_apply x
  rw [hh] at hv
  by_cases hz:y=0
  · change ‖y‖ ≤ _
    rw [hz,norm_zero]; positivity
  apply le_of_sub_nonneg
  have ha := hv.trans (real_inner_le_norm y x)
  rw [inv_mul_eq_div, div_le_iff₀ hq] at ha
  have hp := norm_pos_iff.mpr hz
  change 0 ≤ Q*‖x‖-‖y‖
  nlinarith

variable {R : ℝ}

namespace Param

lemma trans_apply (x : Param m R) (hr : 0<R) (a) :
    x.transE hr a = op x.B a :=
  congrFun (congrArg DFunLike.coe (equivPD_spec (form_posDef (inv_pos.mpr hr) x.in_box.1))) a

lemma contra_eq (x : Param m R) (hr : 0<R) :
    contra (x.transE hr).toLinearEquiv = (x.transE hr).symm.toLinearEquiv := by
  let b := x.transE hr
  ext y : 1
  apply ext_inner_left ℝ
  intro z
  obtain ⟨z,rfl⟩ := b.surjective z
  have hi (z v : Rn m) : ⟪b z,v⟫=⟪z,b v⟫ := by
    unfold b
    rw [x.trans_apply hr,x.trans_apply hr]; exact op_iff_hermitian.mp x.in_box.1.1 z v
  change ⟪b z,contra b.toLinearEquiv y⟫=⟪b z,b.symm y⟫
  rw [hi z (b.symm y), b.apply_symm_apply]
  apply pair_contra b.toLinearEquiv

lemma sigma_choice (x : Param m R) (hr : 0<R) (q : ProjField m) :
    (x.instanceQ hr q).covMat= 1+x.T :=
  CFC.sqrt_mul_sqrt_self _ ((form_posDef (by norm_num)
    (add_cov_box x.in_box.2)).posSemidef.nonneg)

lemma Bound_instance (x : Param m R) (hr : 2 ≤ R) (h : 0<R) {q:ProjField m} {K:ℝ}
    (hk : q.Bound K) :
    (x.instanceQ h q).Bound (K*R) := by
  have hv := inv_norm_box R h x.in_box.1 (x.transE h) (equivPD_spec _)
  have hew := (inv_norm_box 2 (by norm_num) (A := x.S) (by simpa using x.S_box)
    (equivPD x.S_pos) (equivPD_spec _))
  let b := x.transE h
  let b' := contra b.toLinearEquiv
  have hb (y : Rn m) : ‖b y‖ ≤ R * ‖y‖ := by
    rw [show b y = op x.B y from x.trans_apply h y]
    apply ((op x.B).le_opNorm y).trans
    rw [op_norm]; gcongr; exact hv.1
  have hb' (y : Rn m) : ‖b' y‖ ≤ R*‖y‖ := by
    dsimp only [b',b]; rw [contra_eq]
    apply ((x.transE h).symm.toContinuousLinearMap.le_opNorm y).trans
    apply mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
  have HH := hk.one_le
  have hkR : 2 ≤ K*R := by nlinarith
  refine ⟨by linarith,?_ ,?_ , hew.1.trans hkR, hew.2.trans hkR, ?_,?_⟩
  · apply (hb q.U).trans
    nlinarith [hk.Ub]
  · apply (hb' q.V).trans; nlinarith [hk.Vb]
  · intro y hy
    change y ∈ posDual (pushCone b.toLinearEquiv q.C) at hy
    obtain ⟨y,rfl⟩ := b'.surjective y
    rw [dual_pushCone] at hy
    have hu : y∈q.D := by simpa only [b',mem_pushCone,LinearEquiv.symm_apply_apply] using hy
    change ‖b' y‖ ≤ K*R*⟪b.toLinearEquiv q.U,b' y⟫
    rw [show ⟪b.toLinearEquiv q.U,b' y⟫ = _ from pair_contra ..]
    apply (hb' y).trans
    nlinarith [hk.inC y hu]
  · intro y hy
    obtain ⟨y,rfl⟩ := b.surjective y
    have hu : y∈q.C := by
      change b.toLinearEquiv y∈pushCone b.toLinearEquiv q.C at hy
      simpa using hy
    change ‖b y‖ ≤ K*R*⟪b' q.V,b.toLinearEquiv y⟫
    rw [real_inner_comm,show ⟪b.toLinearEquiv y,b' q.V⟫ = _ from pair_contra .., real_inner_comm q.V]
    apply (hb y).trans; nlinarith [hk.inD y hu]
end Param
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Moving
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Continuity for the normalization update. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler

lemma cluster_unique {F : Type*} [NormedAddCommGroup F] [ProperSpace F] (f : ℕ→F) (b : F)
    {C : ℝ} (hc : ∀ᶠ n in atTop, ‖f n‖ ≤ C)
    (hh : ∀ (u:ℕ→ℕ) (x:F), StrictMono u → Tendsto (f∘u) atTop (𝓝 x) → x=b) :
    Tendsto f atTop (𝓝 b) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hn
  let s := closedBall (0:F) C \ ball b ε
  have h : ∃ᶠ n in atTop, f n∈s := by
    have hi : ∃ᶠ n in atTop, f n∉ball b ε := by simpa [Filter.Frequently] using hn
    apply (hi.and_eventually hc).mono (fun x h=>?_)
    exact ⟨mem_closedBall_zero_iff.mpr h.2, h.1⟩
  obtain ⟨x,hx,u,hu,he⟩ := ((isCompact_closedBall (0:F) C).diff isOpen_ball).tendsto_subseq' h
  exact hx.2 (hh u x hu he ▸ mem_ball_self hε)

variable {m:ℕ} {R:ℝ}

lemma tendsto_inv_action {p : ℕ → Rn m ≃L[ℝ] Rn m}
    (q : Rn m ≃L[ℝ] Rn m)
    {C:ℝ} (hC : ∀ n, ‖(p n).symm.toContinuousLinearMap‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (q x)))
    {v : ℕ → Rn m} {y:Rn m} (hv : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun n => (p n).symm (v n)) atTop (𝓝 (q.symm y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he := hv.sub (ht (q.symm y))
  rw [q.apply_symm_apply,sub_self] at he
  have hh : Tendsto (fun n=> C* ‖v n-p n (q.symm y)‖) atTop (𝓝 0) := by
    simpa using he.norm.const_mul C
  apply squeeze_zero _ _ hh
  · intro n; positivity
  intro n
  have hu : (p n).symm (v n)-q.symm y=(p n).symm (v n-p n (q.symm y)) := by rw [_root_.map_sub];simp
  rw [hu]
  apply (((p n).symm.toContinuousLinearMap).le_opNorm _).trans
  gcongr; exact hC n

namespace Param

theorem cont_B : Continuous (@B m R) := continuous_fst.comp continuous_subtype_val
theorem cont_T : Continuous (@T m R) := continuous_snd.comp continuous_subtype_val

theorem cont_S : Continuous (@S m R) :=
  CFC.continuousOn_sqrt.comp_continuous (continuous_const.add cont_T)
    (fun x=> (form_posDef (by norm_num) (add_cov_box x.in_box.2)).posSemidef.nonneg)

theorem cont_trans (h:0<R) :
    Continuous fun p : Param m R × Rn m => (p.1.transE h) p.2 := by
  simp_rw [trans_apply]
  apply Continuous.clm_apply ((continuous_op.comp cont_B).comp continuous_fst) continuous_snd

variable (q : ProjField m)
theorem norm_proj (C : ProperCone ℝ (Rn m)) (x) :
    ‖coneProj C x‖ ≤ ‖x‖ := by
  simpa [proj_of_mem C C.zero_mem] using ((coneProj_lip C).dist_le_mul x 0)

theorem proj_cont (h:0<R) :
    Continuous fun p : Param m R × Rn m =>
      coneProj (p.1.instanceQ h q).C p.2 := by
  apply continuous_iff_seqContinuous.mpr
  rintro f a hf
  set B : Param m R → Rn m≃L[ℝ]Rn m := fun x => x.transE h
  set y := fun p : Param m R × Rn m => coneProj (p.1.instanceQ h q).C p.2
  have hh : ∀ᶠ n in atTop, ‖(f n).2‖ ≤ ‖a.2‖+1 :=
    hf.snd_nhds.norm (Iic_mem_nhds (by linarith))
  change Tendsto (y∘f) atTop (𝓝 (y a))
  apply cluster_unique _ _ (hc := hh.mono fun i hi=>(norm_proj _ _).trans hi)
  intro u x hu ht
  let g := f∘u
  have hl : Tendsto g atTop (𝓝 a) := hf.comp hu.tendsto_atTop
  have hlim (w): Tendsto (fun n=> B (g n).1 w) atTop (𝓝 (B a.1 w)) :=
    ((cont_trans h).tendsto _).comp (hl.fst_nhds.prodMk_nhds tendsto_const_nhds)
  have hC (x : Param m R) : ‖(B x).symm.toContinuousLinearMap‖ ≤ R :=
    (inv_norm_box _ h x.in_box.1 _ (equivPD_spec _)).2
  have hv := tendsto_inv_action (B a.1) (p := fun n=>B (g n).1)
    (fun n=>hC _) hlim ht
  have he : x ∈ (a.1.instanceQ h q).C := by
    apply (q.C.isClosed.mem_of_tendsto hv)
    apply Eventually.of_forall
    intro n
    exact (proj_mem ( (g n).1.instanceQ h q).C (g n).2)
  apply Eq.symm; apply proj_unique _ he
  intro z hz
  change (B a.1).symm z ∈ q.C at hz
  let w := (B a.1).symm z
  have hr := hlim w
  rw [show B a.1 w=z from (B a.1).apply_symm_apply z] at hr
  have hp := (hl.snd_nhds.sub ht).inner (𝕜 := ℝ) (hr.sub ht)
  refine le_of_tendsto hp (Eventually.of_forall fun n=>?_ )
  apply proj_vi (( (g n).1.instanceQ h q).C)
  change ((B _).symm ((B (g n).1) w))∈ q.C
  rwa [(B _).symm_apply_apply]

theorem mean_cont (_hr : 2≤R) (h:0<R) :
    Continuous fun p : Param m R × Rn m =>
      mean (p.1.instanceQ h q).C (p.1.instanceQ h q).root p.2 := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let F (p : Param m R × Rn m) (x : Rn m) :=
    sample (p.1.instanceQ h q).C (p.1.instanceQ h q).root p.2 x
  let g := fun x:Rn m=> (2:ℝ) * ‖x‖ + (‖p.2‖+1)
  have hg : Integrable g (normal m) :=
    ((ProjField.i_norm m).const_mul _).add (integrable_const _)
  change ContinuousAt (fun p => ∫ x, F p x ∂normal m) p
  have he : ∀ᶠ p' in 𝓝 p, ‖p'.2‖ ≤ ‖p.2‖ + 1 :=
    continuous_snd.norm.continuousAt (Iic_mem_nhds (by linarith))
  apply continuousAt_of_dominated (Eventually.of_forall fun _ =>
    (continuous_sample ..).aestronglyMeasurable)
    (he.mono fun p' hp => ae_of_all _ ?_) hg (ae_of_all _ ?_)
  · intro x
    have ha : Continuous (fun p : Param m R × Rn m => F p x) := by
      let v := fun p: Param m R × Rn m => op p.1.S x + p.2
      have hv : Continuous v :=
        (Continuous.clm_apply ((continuous_op.comp cont_S).comp continuous_fst)
          continuous_const).add continuous_snd
      convert (proj_cont q h).comp (continuous_fst.prodMk hv) using 1
      all_goals try with_reducible_and_instances rfl
      ext p : 1
      change coneProj _ ((equivPD p.1.S_pos x)+p.2) = _
      congr 2
      change (equivPD p.1.S_pos).toContinuousLinearMap x=op _ _
      rw [equivPD_spec]
    exact ha.continuousAt
  · intro x
    let p := p'.1
    have H := norm_proj (p.instanceQ h q).C (affineN (p.instanceQ h q).root p'.2 x)
    apply H.trans ((norm_add_le ..).trans ?_)
    apply add_le_add _ hp
    have hb := equivPD_spec p.S_pos
    change ‖(equivPD p.S_pos).toContinuousLinearMap x‖ ≤ _
    rw [equivPD_spec]; apply ((op p.S).le_opNorm x).trans
    gcongr
    rw [op_norm]
    exact (inv_norm_box 2 (by norm_num) (A := p.S) (by simpa using p.S_box)
      (equivPD p.S_pos) hb).1

section
variable [NeZero m]
omit [NeZero m] in
lemma U_cont (h:0<R) : Continuous fun p:Param m R => (p.instanceQ h q).U := by
  have hh : Continuous (fun p:Param m R=> (id p,q.U)) :=
    continuous_id.prodMk continuous_const
  have he := (cont_trans (m := m) h).comp hh
  exact he
theorem shift_cont (hr : 2≤R) (h:0<R) (z : ℝ) :
    Continuous fun p : Param m R => (p.instanceQ h q).shift z := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  have hh : 1 ≤ K*R := by nlinarith [hk.one_le]
  obtain ⟨C,hc,he⟩ := ProjField.layers_growth m hh
  apply continuous_iff_seqContinuous.mpr
  intro f a ha
  let g := fun p : Param m R => p.instanceQ h q
  refine cluster_unique (fun i=> (g (f i)).shift z) ((g a).shift z) (hc := Eventually.of_forall
    fun i => he (g (f i)) ((f i).Bound_instance hr h hk) z) ?_
  intro u x hu hx
  have h₂ := ha.comp hu.tendsto_atTop
  apply mean_injective (g a).C (g a).root ⟨_,(g a).U_in⟩
  have H (p:Param m R) : mean (g p).C (g p).root ((g p).shift z) = Layers.a z • (g p).U :=
    (g p).XT_mean _
  rw [H]
  have h₁ := ((mean_cont q hr h).tendsto (a,x)).comp (h₂.prodMk_nhds hx)
  have HU : Continuous (fun p:Param m R => (g p).U) := U_cont q h
  have hU : Continuous (fun p : Param m R=>Layers.a z • (g p).U) := (continuous_const (y := Layers.a z)).smul HU
  have hv : Tendsto (fun i => mean (g (f (u i))).C (g (f (u i))).root ((g (f (u i))).shift z)) atTop
      (𝓝 (mean (g a).C (g a).root x)) := h₁
  simp_rw [H] at hv
  exact tendsto_nhds_unique hv ((hU.tendsto a).comp h₂)
end
end Param
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_HMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
### H_f, A, L from Equation (7) and their growth bounds
-/
noncomputable section
open Set Filter Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)

variable [NeZero m] {f : ℝ→ℝ} (h : PolyBound (deriv f))

include h in
lemma H_integrable : Integrable (q.Hmat f) (normal m) :=
  (q.H_poly h).gaussian_integrable q.H_SM.aestronglyMeasurable

lemma A_integrable : Integrable q.Amat (normal m) := q.H_integrable poly_id_der

lemma avgA_sym : q.avgA.IsHermitian := hermitian_integral q.A_integrable
  (ae_of_all _ fun _z => q.H_hermitian poly_id_der _)

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ProjParts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Gaussian parts with an affine test; used to make moment continuity
independent of pointwise convergence of projection derivatives. -/
noncomputable section
open Set Filter Real Matrix MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)
variable [NeZero m]

omit [NeZero m] in
lemma weighted_P_integrable (z : ℝ) (l : Rn m→L[ℝ] ℝ) (c:ℝ) :
    Integrable (fun x:Rn m => (c+l x) • q.Pmat z x) (normal m) := by
  have hi := meanJac_integrable q.C q.root (q.shift z)
  apply PolyBound.gaussian_integrable
    (((PolyBound.const c).add (PolyBound.clm l)).smul
      (PolyBound.of_bound 1 fun x=>projJac_norm q.C (affineN q.root (q.shift z) x)))
  exact ((continuous_const.add l.continuous).aestronglyMeasurable.smul hi.aestronglyMeasurable)

omit [NeZero m] in
theorem weighted_P_ip (z : ℝ) (l : Rn m →L[ℝ] ℝ) (c:ℝ) (u v : Rn m) :
    (∫ g, (c+l g)*⟪v,op (q.Pmat z g) (op q.S u)⟫ ∂normal m) =
     (∫ g, ⟪g,u⟫*((c+l g)*⟪v,q.XT z g⟫) ∂normal m) -
        (∫ g, (l u)*⟪v,q.XT z g⟫ ∂normal m) := by
  let b := innerSL ℝ v
  let j := q.XT z
  obtain ⟨k,hk⟩ := q.XT_lipschitz z
  have hm : Continuous fun x => c+l x := continuous_const.add l.continuous
  have hi : LipschitzWith _ (b ∘ j) :=
    (innerSL ℝ v).lipschitz.comp hk
  let f := fun g => (c+l g)* ((b ∘ j) g)
  have hf : Continuous f := hm.mul hi.continuous
  have h₁ := (PolyBound.const c).add (PolyBound.clm l)
  have h₂ := PolyBound.lipschitz hi
  have he : PolyBound f := h₁.mul h₂
  let gD (g : Rn m) := b.comp ((op (q.Pmat z g)).comp (op q.S))
  have hd : ∀ᵐ x ∂normal m,
      HasFDerivAt f (((b∘j) x) • l + (c+l x) • gD x) x := by
    filter_upwards [q.XT_diff z] with x hx
    have he := ((hasFDerivAt_const c x).add l.hasFDerivAt).mul
      ((innerSL ℝ v).hasFDerivAt.comp x hx)
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp [b,j,gD] ; abel)
  let L : ℝ≥0 := ‖innerSL ℝ v‖₊*k
  have hi : LipschitzWith L (b ∘ j) := hi
  let bound := fun g => (‖c+l g‖ + ‖l‖)*(L:ℝ)+‖l‖*‖(b ∘ j) g‖
  have hbd : PolyBound bound :=
    ((h₁.norm.add (PolyBound.const _)).mul (PolyBound.const _)).add
      ((PolyBound.const _).mul h₂.norm)
  have hbc : Continuous bound := ((hm.norm.add continuous_const).mul continuous_const).add
    (continuous_const.mul hi.continuous.norm)
  have hg (x y : Rn m) (hy : ‖y‖<1) :
      ‖f (x+y)-f x‖ ≤ bound x *‖y‖ := by
    let z := x+y
    have hEq : f z-f x =
        (c+l z)*((b∘j) z-(b∘j) x) + l y*((b∘j) x) := by
      unfold f z; rw [_root_.map_add]; ring
    have hl : ‖c+l z‖ ≤ ‖c+l x‖+‖l‖ := by
      have hh := (l.le_opNorm y).trans (mul_le_of_le_one_right (norm_nonneg _) hy.le)
      unfold z; rw [_root_.map_add, ← add_assoc]
      exact (norm_add_le ..).trans (add_le_add le_rfl hh)
    have hj := hi.dist_le_mul (x+y) x
    rw [dist_eq_norm,dist_eq_norm,add_sub_cancel_left] at hj
    change ‖f z-f x‖≤_
    rw [hEq]
    apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul]
    have H3 := mul_le_mul hl hj (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    have H4 := mul_le_mul_of_nonneg_right (l.le_opNorm y) (norm_nonneg ((b∘j) x))
    dsimp only [bound,z] at *
    linarith
  have hh := normal_IBP he hf (hd.mono fun _ h=>h.differentiableAt)
    (hbd.gaussian_integrable hbc.aestronglyMeasurable) hg u
  let g := fun x => (c+l x)*⟪v,op (q.Pmat z x) (op q.S u)⟫
  have hia : Integrable g (normal m) := by
    have H := integral_opPair (q.weighted_P_integrable z l c) v (op q.S u)
    simpa only [_root_.map_smul,_root_.smul_apply,real_inner_smul_right] using H
  have hib : Integrable (fun x=>l u*⟪v,q.XT z x⟫) (normal m) :=
    ((innerSL ℝ v).integrable_comp (q.X_int ..)).const_mul _
  have h₅ : (∫ x, fderiv ℝ f x u ∂normal m) =
      (∫ x,l u*⟪v,q.XT z x⟫ ∂normal m)+ ∫ x,g x ∂normal m := by
    rw [← integral_add hib hia]
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    rw [hx.fderiv]
    simp [b,j,gD,g,mul_comm]
  change (∫ x, fderiv ℝ f x u ∂normal m) =
    ∫ x, ⟪x,u⟫ * ((c+l x)*⟪v,q.XT z x⟫) ∂normal m at hh
  rw [← hh,h₅]
  simp [g]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ParamMoment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 continuity of the Gaussian polynomial moments of P. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ} {R : ℝ}

-- generic dominated parameter expectation
theorem continuous_normal_integral {X F : Type*} [TopologicalSpace X] [FirstCountableTopology X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : X → Rn m → F} {g : Rn m→ℝ} (hg : Integrable g (normal m))
    (hm : ∀ x, AEStronglyMeasurable (f x) (normal m)) (he : ∀ x y, ‖f x y‖ ≤ g y)
    (hf : ∀ y, Continuous fun x=>f x y) : Continuous (fun x=>∫ y, f x y ∂normal m) :=
  continuous_iff_continuousAt.mpr (fun _x => continuousAt_of_dominated (Eventually.of_forall hm)
    (Eventually.of_forall fun x=>ae_of_all _ fun y=>he x y) hg (ae_of_all _ fun y=>(hf y).continuousAt))

lemma continuous_matrix_op {X : Type*} [TopologicalSpace X] (f:X → Mat m)
    (h : ∀ x y, Continuous fun z => ⟪x,op (f z) y⟫) :
    Continuous f := by
  apply continuous_matrix; intro i j
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  convert h (e i) (e j) using 1
  all_goals try with_reducible_and_instances rfl
  ext z; rw [inner_toEuclideanCLM]
  simp [e,EuclideanSpace.basisFun_apply,EuclideanSpace.single,mulVec,dotProduct]

namespace Param
lemma rootNorm (p:Param m R) :
    ‖p.S‖ ≤ 2 ∧ ‖(equivPD p.S_pos).symm.toContinuousLinearMap‖ ≤ 2 :=
  inv_norm_box _ (by norm_num) (by simpa using p.S_box) _ (equivPD_spec _)
theorem S_action (x : Rn m) :
    Continuous (fun p:Param m R=>equivPD p.S_pos x) := by
  have he (p:Param m R) : equivPD p.S_pos x = op p.S x := by
    change (equivPD _).toContinuousLinearMap x=_; rw [equivPD_spec]
  simp_rw [he]
  exact ((continuous_op.comp cont_S).clm_apply continuous_const)

theorem iS_action (x : Rn m) :
    Continuous (fun p:Param m R=>(equivPD p.S_pos).symm x) := by
  apply continuous_iff_seqContinuous.mpr
  intro f a ha
  exact tendsto_inv_action _ (p := fun i=>equivPD (f i).S_pos)
    (fun i=>(f i).rootNorm.2) (fun x => ((S_action x).tendsto a).comp ha) (v := fun _=>x) tendsto_const_nhds

variable (q : ProjField m) (hr : 2 ≤ R) (h : 0 < R) (z : ℝ)
variable [NeZero m]
include hr

theorem XT_cont (x:Rn m) :
    Continuous (fun p:Param m R=>(p.instanceQ h q).XT z x) := by
  have hu := shift_cont q hr h z
  let F := fun p:Param m R=>(equivPD p.S_pos x)+(p.instanceQ h q).shift z
  have hv : Continuous (fun p:Param m R=>(p,F p)) := continuous_id.prodMk
    ((S_action x).add hu)
  convert (proj_cont q h).comp hv ; rfl

theorem XT_bound : ∃ C ≥ (0:ℝ), ∀ p:Param m R, ∀ x,
    ‖(p.instanceQ h q).XT z x‖≤C*(1+‖x‖) := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  obtain ⟨C,hc,hh⟩ := ProjField.layers_growth m (K := K*R) (by nlinarith [hk.one_le])
  use 2+C*(1+|z|),by positivity
  intro p x
  let i := p.instanceQ h q
  have he := hh _ (p.Bound_instance hr h hk) z
  have hu := norm_proj i.C (i.Z x+i.shift z)
  apply hu.trans ((norm_add_le ..).trans ?_)
  have hb : ‖i.Z x‖ ≤ 2*‖x‖ := by
    rw [i.Z_def]; apply ((op i.S).le_opNorm _).trans
    rw [op_norm]
    exact mul_le_mul_of_nonneg_right p.rootNorm.1 (norm_nonneg x)
  change ‖i.shift z‖ ≤ _ at he
  nlinarith [norm_nonneg x,abs_nonneg z, show 0≤C*(1+|z|)*‖x‖ by positivity]

theorem weighted_P_cont (l : Rn m →L[ℝ] ℝ) (c:ℝ) :
    Continuous (fun p:Param m R=> ∫ x, (c+l x) • ((p.instanceQ h q).Pmat z x) ∂normal m) := by
  apply continuous_matrix_op; intro v u
  let g := fun p:Param m R=>p.instanceQ h q
  let w := fun p:Param m R=>(equivPD p.S_pos).symm u
  have hc := iS_action (R:=R) u
  have he (p:Param m R) : op (g p).S (w p)=u := by
    change op p.S _ = _
    rw [← equivPD_spec p.S_pos]; exact (equivPD p.S_pos).apply_symm_apply _
  let b (p:Param m R) (x : Rn m) := ⟪v,(g p).XT z x⟫
  let f (p:Param m R) (x : Rn m) := ⟪x,w p⟫ * ((c+l x)*b p x)
  have ha (p : Param m R) :
      ⟪v, op (∫ x, (c+l x) • ((g p).Pmat z x) ∂normal m) u⟫ =
      (∫ x, f p x ∂normal m) - l (w p)*⟪v,Layers.a z • (g p).U⟫ := by
    set a := g p
    rw [op_inner_integral (a.weighted_P_integrable ..)]
    simp_rw [_root_.map_smul,_root_.smul_apply,real_inner_smul_right]
    have H := a.weighted_P_ip z l c (w p) v
    rw [he p] at H
    rw [H,integral_const_mul]
    change _-l (w p)*(∫ x, innerSL ℝ v (a.XT z x) ∂_) = _
    rw [(innerSL ℝ v).integral_comp_comm (a.X_int ..),a.XT_mean,innerSL_apply_apply,real_inner_smul_right]
  change Continuous (fun p : Param m R => ⟪v,op _ u⟫)
  have heq : (fun p:Param m R=>⟪v,op (∫ x,(c+l x) • ((p.instanceQ h q).Pmat z x) ∂normal m) u⟫) =
      fun p=>(∫ x, f p x ∂normal m) - l (w p)*⟪v,Layers.a z • (g p).U⟫ := funext ha
  rw [heq]
  apply Continuous.sub
  · obtain ⟨C,hC,Hu⟩ := XT_bound q hr h z
    let J (x:Rn m) := ‖x‖*(2*‖u‖) * (‖c+l x‖*(‖v‖*(C*(1+‖x‖))))
    have hJ : PolyBound J :=
      let hnx := (PolyBound.id (X:=Rn m)).norm
      let h1 := ((PolyBound.const c).add (PolyBound.clm l)).norm
      let h2 := (PolyBound.const C).mul ((PolyBound.const 1).add hnx)
      (hnx.mul (PolyBound.const _)).mul (h1.mul ((PolyBound.const _).mul h2))
    have hJC : Continuous J := by unfold J; fun_prop
    have hlc (p:Param m R) : Continuous (f p) :=
      ((continuous_id.inner continuous_const).mul ((continuous_const.add l.continuous).mul
        (continuous_const.inner (continuous_sample ..))))
    apply continuous_normal_integral (hJ.gaussian_integrable hJC.aestronglyMeasurable)
      (fun p=>(hlc p).aestronglyMeasurable)
    · intro p x
      have hu : ‖w p‖ ≤ 2*‖u‖ := le_trans
        ((equivPD p.S_pos).symm.toContinuousLinearMap.le_opNorm _) (mul_le_mul_of_nonneg_right p.rootNorm.2 (norm_nonneg _))
      have h₁ : ‖b p x‖ ≤ ‖v‖ * (C*(1+‖x‖)) :=
        (abs_real_inner_le_norm v _).trans (mul_le_mul_of_nonneg_left (Hu p x) (norm_nonneg _))
      have h₂ : ‖(⟪x,w p⟫:ℝ)‖ ≤ ‖x‖*(2*‖u‖) :=
        (abs_real_inner_le_norm x _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
      dsimp only [f,J]; rw [norm_mul,norm_mul]; gcongr
    intro x
    exact ((continuous_const.inner hc).mul (continuous_const.mul
      (continuous_const.inner (XT_cont q hr h z x))))
  · have hU : Continuous fun p:Param m R => Layers.a z • (g p).U :=
      (continuous_const (y := Layers.a z)).smul (U_cont q h)
    exact (l.continuous.comp hc).mul (continuous_const.inner hU)
end Param
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ParamA
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02: continuity of layer expectations in normalization parameters. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ} [NeZero m] (l : Rn m →L[ℝ] ℝ) (c : ℝ)
namespace ProjField

variable (q : ProjField m)


omit [NeZero m] in
lemma PD_eq (z x) : q.PD z x = (p z-st z) • (1:Mat m) - q.Pstep z x := by
  simp [PD,Pstep,Gstep,sub_smul]

lemma mixed_aun : mixed (q.aun l c) :=
  q.mixed_PD.product (g := fun _ x=>c+l x)
    (((PolyBound.const c).add (PolyBound.clm l)).comp PolyBound.snd) (fun z x=>by
      rw [aun,norm_smul,mul_comm])

omit [NeZero m] in
lemma sm_aun : StronglyMeasurable (q.aun l c).uncurry :=
  (continuous_const.add (l.continuous.comp continuous_snd)).stronglyMeasurable.smul q.PD_sm

lemma int_aun : Integrable (q.aun l c).uncurry (volume.prod (normal m)) :=
  mixed_integrable (q.mixed_aun l c) (q.sm_aun l c).aestronglyMeasurable

lemma int_aun_right (z) : Integrable (q.aun l c z) (normal m) :=
  (((q.mixed_aun l c).poly.comp ((PolyBound.const z).prodMk PolyBound.id))).gaussian_integrable
    ((q.sm_aun l c).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable

lemma int_da : Integrable (q.da l c) := by
  exact (q.int_aun l c).integral_prod_left

lemma weighted_A : (∫ x,(c+l x) • q.Amat x ∂normal m) = ∫ z,q.da l c z := by
  have he (x) : (c+l x) • q.Amat x = ∫ z, q.aun l c z x := by
    rw [Amat,Hmat,← integral_smul]
    simp [kerH, aun]
  simp_rw [he]
  exact (integral_integral_swap (q.int_aun l c)).symm

omit [NeZero m] in
lemma da_eq (z : ℝ) :
    q.da l c z = (∫ x,(c+l x) • (p z • (1:Mat m)) ∂normal m)
      - (∫ x,(c+l x) • ((q.Pmat z x)) ∂normal m) := by
  have h : Integrable (fun x : Rn m => c+l x) (normal m) :=
    ((PolyBound.const c).add (PolyBound.clm l)).gaussian_integrable
      (continuous_const.add l.continuous).aestronglyMeasurable
  rw [← integral_sub (h.smul_const _) (q.weighted_P_integrable z l c)]
  simp [aun,da,PD,smul_sub]

variable (m) in
lemma da_uniform {K : ℝ} (hk : 1 ≤ K) (n : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ q:ProjField m, q.Bound K → ∀ z,
      ‖q.da l c z‖*(1+‖z‖)^n ≤ C := by
  obtain ⟨C,hc,hC⟩ := uniform_Pstep m hk n
  obtain ⟨D,hd,hD⟩ := rapid_p n
  let g (x:Rn m) := ‖c+l x‖*(D+C*(1+‖x‖)^n)
  have hh (x:Rn m) : 0 ≤ g x := by unfold g; positivity
  have hg : PolyBound g :=
    (((PolyBound.const c).add (PolyBound.clm l)).norm).mul
      ((PolyBound.const D).add ((PolyBound.const C).mul (((PolyBound.const 1).add
        (PolyBound.id (X := Rn m)).norm).pow n)))
  have hi := hg.gaussian_integrable (μ := normal m)
    ((by unfold g; fun_prop : Continuous g).aestronglyMeasurable)
  refine ⟨∫ x,g x ∂normal m,integral_nonneg hh,fun q hq z=>?_⟩
  calc
    _ ≤ (∫ x, ‖q.aun l c z x‖ ∂normal m)*(1+‖z‖)^n := by unfold da; gcongr; exact norm_integral_le_integral_norm _
    _ = ∫ x, ‖q.aun l c z x‖*(1+‖z‖)^n ∂normal m := (integral_mul_const _ _).symm
    _ ≤ _ := by
      apply integral_mono ((q.int_aun_right l c z).norm.mul_const _) hi
      intro x
      have hb : ‖q.PD z x‖ * (1+‖z‖)^n ≤ D+C*(1+‖x‖)^n := by
        rw [q.PD_eq]
        apply le_trans (mul_le_mul_of_nonneg_right (norm_sub_le ..)
          (show 0 ≤ (1+‖z‖)^n by positivity))
        rw [add_mul,norm_smul]
        have he := mul_le_of_le_one_right (norm_nonneg (p z-st z)) (one_op_le (m := m))
        exact add_le_add (le_trans (mul_le_mul_of_nonneg_right he (by positivity)) (hD _))
          (hC q hq _ _)
      change ‖(c+l x) • q.PD z x‖ * (1+‖z‖)^n ≤ g x; rw [norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
end ProjField

namespace Param
variable {R : ℝ} (q : ProjField m) (hr : 2 ≤ R) (h:0<R)
include hr

theorem cont_weightedA :
    Continuous (fun p:Param m R => ∫ x,(c+l x) • (p.instanceQ h q).Amat x ∂normal m) := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  have hh := hk.one_le
  let n := Module.finrank ℝ ℝ+1
  obtain ⟨C,hC,hd⟩ := ProjField.da_uniform m l c (show 1≤K*R by nlinarith) n
  let g := fun t:ℝ=> C*((1+‖t‖)^n)⁻¹
  have hi : Integrable g := envelope_inv_int.const_mul C
  simp_rw [ProjField.weighted_A]
  apply continuous_iff_continuousAt.mpr
  intro v
  apply continuousAt_of_dominated
    (Eventually.of_forall fun y => ((y.instanceQ h q).int_da l c).aestronglyMeasurable)
    _ hi
  · apply ae_of_all
    intro x
    have hh := weighted_P_cont q hr h x l c
    have he : Continuous (fun p:Param m R => (p.instanceQ h q).da l c x) := by
      simp_rw [ProjField.da_eq]
      exact continuous_const.sub hh
    exact he.continuousAt
  · apply Eventually.of_forall
    intro x
    apply ae_of_all
    intro z
    dsimp only [g]
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    exact hd _ (x.Bound_instance hr h hk) z

lemma cont_avgA : Continuous (fun p:Param m R => (p.instanceQ h q).avgA) := by
  simpa [ProjField.avgA] using cont_weightedA (m:=m) 0 1 q hr h

lemma cont_M (i:Fin m) : Continuous (fun p:Param m R => (p.instanceQ h q).M i) := by
  simpa [ProjField.M] using cont_weightedA (ProjField.coord i) 0 q hr h

lemma cont_L (x : Rn m) : Continuous (fun p:Param m R => (p.instanceQ h q).Lmat x) :=
  continuous_finsetSum _ (fun i _hi => (continuous_const (y := x i)).smul (cont_M q hr h i))
end Param
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Angle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Inward normalization estimate: layer as seen in a unit direction. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (q : ProjField m) (v : Rn m)

omit [NeZero m] in
lemma h_between (hv : ‖v‖=1) (z : ℝ) :
    0 ≤ q.dimH v z ∧ q.dimH v z ≤ 1 := by
  have hi := meanJac_integrable q.C q.root (q.shift z)
  constructor
  · apply integral_nonneg
    intro x; exact (op_posSemidef_iff.mp (q.Pmat_psd z x).posSemidef).2 v
  rw [← show (∫ x:Rn m,(1:ℝ) ∂normal m) = 1 by simp]
  apply integral_mono (integral_opPair hi v v) (integrable_const _)
  intro x
  have he := (op_order_iff (q.Pmat_herm z x) isHermitian_one).mp (q.Pmat_le z x) v
  rw [_root_.map_one] at he
  apply he.trans_eq; change ⟪v,v⟫=1; rw [real_inner_self_eq_norm_sq,hv]; norm_num

omit [NeZero m] in
lemma S_vp : op q.S (q.vp v)=v := by
  rw [← q.matrix_eq]; exact q.root.apply_symm_apply _
omit [NeZero m] in
lemma dimH_X (z : ℝ) :
    q.dimH v z = ∫ x:Rn m, ⟪x,q.vp v⟫*⟪v,q.XT z x⟫ ∂normal m := by
  have h := q.normal_XT_inner z (q.vp v) v
  rw [q.S_vp] at h; exact h

omit [NeZero m] in
lemma dimH_Y (hv : ‖v‖=1) (z : ℝ) :
    1-q.dimH v z = ∫ x:Rn m, ⟪x,q.vp v⟫*(-⟪v,q.YT z x⟫) ∂normal m := by
  let w := q.vp v
  let a (x : Rn m) := affineN q.root (q.shift z) x
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ v
  have hm : LipschitzWith _ (l ∘ a) :=
    l.lipschitz.comp ((q.root.toContinuousLinearMap.lipschitz).add (LipschitzWith.const _))
  have hf : (∫ x, ⟪x,w⟫*(l∘a) x ∂normal m)=1 := by
    have h := normal_IBP_lipschitz hm w
    have he (x:Rn m) : fderiv ℝ (l∘a) x w=1 := by
      have hi := (l.hasFDerivAt.comp x (q.root.hasFDerivAt.add_const (q.shift z))).fderiv
      change fderiv ℝ (l∘a) x = _ at hi
      rw [hi]
      change ⟪v,q.root w⟫=1
      rw [show q.root w=v from q.root.apply_symm_apply _,real_inner_self_eq_norm_sq,hv]; norm_num
    change (∫ x, ⟪x,w⟫ • (l∘a) x ∂normal m)=1
    rw [← h]; simp_rw [he]; simp
  have hi : Integrable (fun x=>⟪x,w⟫*(l∘a) x) (normal m) := by
    have he : PolyBound (fun x=>⟪x,w⟫) := by
      simp_rw [real_inner_comm w]
      exact PolyBound.clm (f := (show Rn m→L[ℝ] ℝ from innerSL ℝ w))
    exact (he.mul (PolyBound.lipschitz hm)).gaussian_integrable
      (((continuous_id.inner continuous_const).mul hm.continuous).aestronglyMeasurable)
  have hE (x) :
      ⟪x,q.vp v⟫*(-⟪v,q.YT z x⟫) = ⟪x,w⟫*(l∘a) x-⟪x,w⟫*⟪v,q.XT z x⟫ := by
    change ⟪x,w⟫*_ = ⟪x,w⟫*⟪v,q.Z x+q.shift z⟫-_
    rw [q.YT_sub,inner_sub_right]; ring
  simp_rw [hE]; rw [integral_sub hi (q.integrable_pair ..),hf,q.dimH_X]

lemma form_da (hv : ‖v‖=1) (z : ℝ) :
    opPair v v (q.da 0 1 z) = p z - q.dimH v z := by
  have hi := (q.int_aun_right 0 1 z)
  unfold da
  rw [← (opPair v v).integral_comp_comm hi]
  have he (x) : opPair v v (q.aun 0 1 z x) = p z-⟪v,op (q.Pmat z x) v⟫ := by
    simp only [aun,_root_.zero_apply,add_zero,one_smul,PD,_root_.map_sub,
      opPair_apply,_root_.map_smul,smul_eq_mul,_root_.map_one]
    change _*⟪v,v⟫-_ = _
    rw [real_inner_self_eq_norm_sq,hv]; ring
  simp_rw [he]
  rw [integral_sub (integrable_const _) (show Integrable (fun x:Rn m=>⟪v,op (q.Pmat z x) v⟫) (normal m) from integral_opPair
    (meanJac_integrable q.C q.root (q.shift z)) v v)]
  simp [dimH]

lemma whole (hv : ‖v‖=1) :
    ⟪v,op q.avgA v⟫ = ∫ z,(p z-q.dimH v z) := by
  have hh := q.weighted_A 0 1
  have he : q.avgA=∫ z,q.da 0 1 z := by simpa [avgA] using hh
  change opPair v v _=_
  rw [he, ← (opPair v v).integral_comp_comm (q.int_da ..)]
  simp_rw [q.form_da v hv]

lemma diff_int (hv : ‖v‖=1) : Integrable fun z=>p z-q.dimH v z := by
  simp_rw [← q.form_da v hv]
  exact (opPair v v).integrable_comp (q.int_da ..)

lemma int_pst : Integrable (fun z=>p z-st z) :=
  rapid_p.integrable_real (cp.measurable.sub measurable_st)

lemma p_step_zero : (∫ z,p z-st z)=0 := by
  have hi := integral_neg_eq_self (μ := volume) (fun z=>p z-st z)
  have he : (∫ z,p (-z)-st (-z)) = ∫ z,-(p z-st z) := by
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ z:ℝ,z ≠ 0 by rw [ae_iff];simp] with z hz
    rw [neg_p]; unfold st; split_ifs <;> grind
  rw [integral_neg] at he
  linarith

lemma step_int (hv : ‖v‖=1) : Integrable fun z=> st z-q.dimH v z := by
  convert (q.diff_int v hv).sub int_pst using 1
  all_goals try with_reducible_and_instances rfl
  ext x; change _=(p x-_) - (p x-_); ring

lemma pn (hv : ‖v‖=1) : ⟪v,op q.avgA v⟫ = q.plus v - q.minus v := by
  rw [whole q v hv]
  have he : (fun z=>p z - q.dimH v z) = fun z=> (p z-st z)+(st z-q.dimH v z) := by ext; ring
  rw [he, integral_add int_pst (q.step_int v hv),p_step_zero,zero_add]
  rw [← integral_add_compl measurableSet_Ici (q.step_int v hv) (s := Ici (0:ℝ)), compl_Ici]
  have he₁ : (∫ z in Ici (0:ℝ), (st z-q.dimH v z))=q.plus v :=
    setIntegral_congr_fun measurableSet_Ici fun z hz => by simp [st,show 0 ≤ z from hz]
  have he₂ : (∫ z in Iio (0:ℝ), (st z-q.dimH v z))= -q.minus v := by
    rw [minus, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Iio fun z hz => by
      have h : ¬0 ≤ z := not_le_of_gt hz
      simp [st,h]
  rw [he₁,he₂]; ring

lemma plus_int (hv : ‖v‖=1) :
    IntegrableOn (fun z=>1-q.dimH v z) (Ici (0:ℝ)) :=
  (q.step_int v hv).integrableOn.congr_fun (fun z hz=>by simp [st,show 0 ≤ z from hz]) measurableSet_Ici
lemma minus_int (hv : ‖v‖=1) : IntegrableOn (q.dimH v) (Iio (0:ℝ)) :=
  (q.step_int v hv).neg.integrableOn.congr_fun (fun z hz=>by simp only [Pi.neg_apply,st,ite_eq_right (not_le_of_gt (show z < 0 from hz)),zero_sub,neg_neg]) measurableSet_Iio
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_InPoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Estimates for one-dimensional layers under changing coordinates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers ProjField
variable {m : ℕ}

lemma exp_est_dir (m : ℕ) [NeZero m] :
    ∃ D ≥ 0, ∀ f : Rn m → ℝ, (∀ x y, ‖f x - f y‖ ≤ 2 * ‖x-y‖) →
    ∀ v : Rn m, ‖v‖ ≤ 2 → ∀ j : ℝ, 1 ≤ j →
    (∫ x, ⟪x,v⟫*f x ∂normal m) ≤
      D*(j*(∫ x, ‖f x‖ ∂normal m) + Real.exp (-(j^2)/4)) := by
  classical
  obtain ⟨C,hC,h₁⟩ := normal_tail m 2
  have hJ := j_nonneg m
  let D := 2+2*J m+4*(1+J m)*C
  use D
  refine ⟨by unfold D; positivity, fun f hf v hv j hj => ?_⟩
  have hk : LipschitzWith 2 f := LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [dist_eq_norm,NNReal.coe_ofNat] using hf x y
  let μ := normal m
  have hi : Integrable f μ := (PolyBound.lipschitz hk).gaussian_integrable
    hk.continuous.aestronglyMeasurable
  let F := ∫ x, ‖f x‖ ∂μ
  have hh : 0 ≤ F := integral_nonneg fun x => norm_nonneg _
  let E := fun x : Rn m => (1+‖x‖)^2
  let S : Set (Rn m) := {x| j ≤ ‖x‖}
  have hm : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  let b := 4*(1+J m)
  let g := fun x : Rn m => (2*j)*‖f x‖ + (2*F)*‖x‖ + b*S.indicator E x
  have hl (x) : ⟪x,v⟫*f x ≤ g x := by
    have h₀ : ⟪x,v⟫*f x ≤ (‖x‖*2)*‖f x‖ := calc
      _ ≤ |⟪x,v⟫*f x| := le_abs_self _
      _ ≤ _ := by
        rw [abs_mul, Real.norm_eq_abs (f x)]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg (f x))
        exact (abs_real_inner_le_norm x v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg x))
    apply h₀.trans
    by_cases hx:x∈S
    · change _ ≤ _+_+b*_
      rw [indicator_of_mem hx]
      have he := norm_le_mean_error hi hf (by norm_num) x
      change ‖f x‖ ≤ F+_ at he
      have hv : ‖x‖+J m ≤ (1+J m)*(1+‖x‖) := by nlinarith [norm_nonneg x]
      have ht : (‖x‖*2)*‖f x‖ ≤ (‖x‖*2)*(F+2*((1+J m)*(1+‖x‖))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      unfold b E
      nlinarith [norm_nonneg x,mul_nonneg hJ (norm_nonneg x),norm_nonneg (f x)]
    change _ ≤ _+_+b*_
    rw [indicator_of_notMem hx]
    change ¬j≤‖x‖ at hx
    nlinarith [norm_nonneg x,norm_nonneg (f x)]
  have hA : Integrable (fun x=> (2*j)*‖f x‖) μ := hi.norm.const_mul _
  have hB : Integrable (fun x:Rn m=> (2*F)*‖x‖) μ := (i_norm _).const_mul _
  have hE : Integrable (fun x:Rn m=> b*S.indicator E x) μ :=
    ((integrable_envelope 2).indicator hm).const_mul _
  have hg : Integrable (fun x:Rn m=>⟪x,v⟫*f x) μ := by
    have he : PolyBound (fun x:Rn m=>⟪x,v⟫) := by
      simp_rw [real_inner_comm v]
      exact PolyBound.clm (f := (show Rn m→L[ℝ] ℝ from innerSL ℝ v))
    exact (he.mul (PolyBound.lipschitz hk)).gaussian_integrable
      (((continuous_id.inner continuous_const).mul hk.continuous).aestronglyMeasurable)
  apply (integral_mono hg ((hA.add hB).add hE) hl).trans
  change ∫ x, _+_+b*S.indicator E x ∂μ ≤ _
  rw [integral_add (show Integrable (fun x=>2*j*‖f x‖+(2*F)*‖x‖) μ from hA.add hB) hE, integral_add hA hB]
  simp_rw [integral_const_mul]; rw [integral_indicator hm]
  change 2*j*F+2*F*J m+b*_ ≤ D*(j*F+_)
  have hx := h₁ j (by linarith)
  change ∫ x in S, E x ∂μ ≤ _ at hx
  have he := mul_le_mul_of_nonneg_left hx (show 0 ≤ b by unfold b; positivity)
  unfold D
  set e := Real.exp (-(j^2)/4)
  have hp : 0 ≤ e := Real.exp_nonneg _
  unfold b at *
  have hu : F ≤ j*F := by nlinarith
  calc
    _ ≤ 2*j*F + 2*(j*F)*J m + 4*(1+J m)*(C*e) := add_le_add (by nlinarith) he
    _ ≤ _ := by
      rw [← sub_nonneg]
      ring_nf
      positivity

namespace Param

variable {R:ℝ} (x:Param m R) (hr:0<R) (q₀:ProjField m) (v:Rn m) (hv:‖v‖=1)
lemma normS : ‖x.S‖ ≤ 2 ∧ ‖(equivPD x.S_pos).symm.toContinuousLinearMap‖ ≤ 2 :=
  inv_norm_box 2 (by norm_num) (A := x.S) (by simpa using x.S_box)
    (equivPD x.S_pos) (equivPD_spec _)
include hv in lemma vp_two : ‖(x.instanceQ hr q₀).vp v‖ ≤ 2 := by
  apply ((equivPD x.S_pos).symm.toContinuousLinearMap.le_opNorm v).trans
  rw [hv,mul_one]; exact x.normS.2

lemma Z_two (w:Rn m) : ‖(x.instanceQ hr q₀).Z w‖ ≤ 2*‖w‖ := by
  rw [(x.instanceQ hr q₀).Z_def]
  apply ((op (x.instanceQ hr q₀).S).le_opNorm w).trans
  rw [op_norm]; apply mul_le_mul_of_nonneg_right x.normS.1 (norm_nonneg _)

include hv in lemma coordLipX (z:ℝ) (a b:Rn m) :
    ‖⟪v,(x.instanceQ hr q₀).XT z a⟫-⟪v,(x.instanceQ hr q₀).XT z b⟫‖ ≤ 2*‖a-b‖ := by
  rw [← inner_sub_right]
  apply (abs_real_inner_le_norm ..).trans
  rw [hv,one_mul]
  apply le_trans _ (x.Z_two hr q₀ (a-b))
  have he : affineN (x.instanceQ hr q₀).root ((x.instanceQ hr q₀).shift z) a-affineN (x.instanceQ hr q₀).root ((x.instanceQ hr q₀).shift z) b=(x.instanceQ hr q₀).Z (a-b) := by
    unfold affineN Z; rw [_root_.map_sub]; abel
  rw [← he]
  simpa only [XT,sample,dist_eq_norm, NNReal.coe_one,one_mul] using (coneProj_lip (x.instanceQ hr q₀).C).dist_le_mul
    (affineN (x.instanceQ hr q₀).root ((x.instanceQ hr q₀).shift z) a) (affineN (x.instanceQ hr q₀).root ((x.instanceQ hr q₀).shift z) b)

include hv in lemma coordLipY (z:ℝ) (a b:Rn m) :
    ‖-⟪v,(x.instanceQ hr q₀).YT z a⟫- -⟪v,(x.instanceQ hr q₀).YT z b⟫‖ ≤ 2*‖a-b‖ := by
  rw [sub_neg_eq_add, ← sub_eq_neg_add, ← inner_sub_right]
  apply (abs_real_inner_le_norm ..).trans
  rw [hv,one_mul, norm_sub_rev ((x.instanceQ hr q₀).YT z b)]
  apply le_trans _ (x.Z_two hr q₀ (a-b))
  let f := fun t => -((x.instanceQ hr q₀).Z t + (x.instanceQ hr q₀).shift z)
  have he : f a-f b= -((x.instanceQ hr q₀).Z (a-b)) := by unfold f Z; rw [_root_.map_sub]; abel
  have h := (coneProj_lip (x.instanceQ hr q₀).D).dist_le_mul (f a) (f b)
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one, one_mul,he,norm_neg] at h
  exact h

include hv in lemma small_X {K} (hk:q₀.Bound K) (he : op x.B v=R⁻¹ • v) (z:ℝ) :
    (∫ t, ‖⟪v,(x.instanceQ hr q₀).XT z t⟫‖ ∂normal m) ≤ K*m/R*a z := by
  let e := x.transE hr
  have hb (w : Rn m) (hw : w∈(x.instanceQ hr q₀).C) : ‖⟪v,w⟫‖ ≤ R⁻¹*K*⟪(x.instanceQ hr q₀).V,w⟫ := by
    obtain ⟨w,rfl⟩ := e.surjective w
    change e.toLinearEquiv w ∈ pushCone e.toLinearEquiv q₀.C at hw
    have hi := hk.inD w (by simpa using hw)
    have HH : ⟪(x.instanceQ hr q₀).V,e w⟫=⟪q₀.V,w⟫ := by
      rw [real_inner_comm, real_inner_comm w]; apply pair_contra e.toLinearEquiv
    rw [HH,show e w= _ from x.trans_apply hr w,
      ← op_iff_hermitian.mp x.in_box.1.1,he,real_inner_smul_left,norm_mul,
      Real.norm_eq_abs, abs_of_nonneg (inv_pos.mpr hr).le,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hr).le
    apply (abs_real_inner_le_norm v w).trans
    rwa [hv,one_mul]
  let l : Rn m→L[ℝ]ℝ := innerSL ℝ (x.instanceQ hr q₀).V
  have hi := (x.instanceQ hr q₀).X_int z
  calc
    _ ≤ ∫ t,R⁻¹*K*l ((x.instanceQ hr q₀).XT z t) ∂normal m := integral_mono
      (ContinuousLinearMap.integrable_comp (show Rn m→L[ℝ]ℝ from innerSL ℝ v) hi).norm
      ((l.integrable_comp hi).const_mul _) (fun t=> hb _ (proj_mem ..))
    _ = _ := by
      rw [integral_const_mul,l.integral_comp_comm hi,(x.instanceQ hr q₀).XT_mean]
      change _*⟪(x.instanceQ hr q₀).V,a z • (x.instanceQ hr q₀).U⟫=_
      rw [real_inner_smul_right,real_inner_comm,(x.instanceQ hr q₀).ip]
      ring

include hv in lemma large_Y [NeZero m] {K} (hk:q₀.Bound K) (he : op x.B v=R • v) (z:ℝ) :
    (∫ t, ‖-⟪v,(x.instanceQ hr q₀).YT z t⟫‖ ∂normal m) ≤ K*m/R*(x.instanceQ hr q₀).Bt z := by
  let e := x.transE hr
  let b := contra e.toLinearEquiv
  have hb (w : Rn m) (hw : w∈(x.instanceQ hr q₀).D) : ‖-⟪v,w⟫‖ ≤ R⁻¹*K*⟪(x.instanceQ hr q₀).U,w⟫ := by
    obtain ⟨w,rfl⟩ := b.surjective w
    change b w ∈ posDual (pushCone e.toLinearEquiv q₀.C) at hw
    rw [dual_pushCone] at hw
    have hi := hk.inC w (by simpa only [b,mem_pushCone,LinearEquiv.symm_apply_apply] using hw)
    have HH : ⟪(x.instanceQ hr q₀).U,b w⟫=⟪q₀.U,w⟫ := pair_contra e.toLinearEquiv ..
    have hv' : e v= R • v := (x.trans_apply hr _).trans he
    have HH' : ⟪v,b w⟫= R⁻¹*⟪v,w⟫ := by
      have h := pair_contra e.toLinearEquiv v w
      change ⟪e v,b w⟫=_ at h
      rw [hv',real_inner_smul_left] at h
      rw [← h]; field_simp
    rw [norm_neg,HH,HH',norm_mul,Real.norm_eq_abs,abs_of_nonneg (inv_pos.mpr hr).le,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hr).le
    apply (abs_real_inner_le_norm v w).trans
    rwa [hv,one_mul]
  let l : Rn m→L[ℝ]ℝ := innerSL ℝ (x.instanceQ hr q₀).U
  have hi := (x.instanceQ hr q₀).Y_int z
  calc
    _ ≤ ∫ t,R⁻¹*K*l ((x.instanceQ hr q₀).YT z t) ∂normal m := integral_mono
      (ContinuousLinearMap.integrable_comp (show Rn m→L[ℝ]ℝ from innerSL ℝ v) hi).neg.norm
      ((l.integrable_comp hi).const_mul _) (fun t=> hb _ (proj_mem ..))
    _ = _ := by
      rw [integral_const_mul,l.integral_comp_comm hi]
      dsimp [l,Bt]; have H:= m_pos (m:=m); field_simp
end Param

lemma angle_est [NeZero m] (q₀:ProjField m) :
    ∃ D ≥ 0, ∀ R, ∀ hr:0<R, ∀ x : Param m R, ∀ v:Rn m, ‖v‖=1 →
      let q := x.instanceQ hr q₀
      ∀ (z:ℝ) (j:ℝ), 1 ≤ j →
       (op x.B v= R⁻¹ • v → q.dimH v z ≤ D*(j/R*a z+ Real.exp (-(j^2)/4))) ∧
       (op x.B v= R • v → 1-q.dimH v z ≤ D*(j/R*q.Bt z+ Real.exp (-(j^2)/4))) := by
  obtain ⟨K,hK⟩ := q₀.Field_isBound
  obtain ⟨C,hC,hc⟩ := exp_est_dir m
  have hv := hK.positive
  use C*(1+K*m)
  refine ⟨by positivity, fun R hr x v hv z j hj => ?_⟩
  let q := x.instanceQ hr q₀
  have HH (F g : ℝ) (hf : F ≤ K*m/R*g) (hg : 0 ≤ g) :
      C*(j*F+Real.exp (-(j^2)/4)) ≤ C*(1+K*m)*(j/R*g+Real.exp (-(j^2)/4)) := by
    rw [mul_assoc C]
    apply mul_le_mul_of_nonneg_left _ hC
    apply le_trans (add_le_add (mul_le_mul_of_nonneg_left hf (by linarith)) le_rfl)
    rw [← sub_nonneg]; ring_nf; positivity
  constructor
  · intro he
    change q.dimH _ _ ≤ _
    rw [q.dimH_X]
    exact (hc _ (x.coordLipX hr q₀ v hv z) (q.vp v) (x.vp_two hr q₀ v hv) j hj).trans
      (HH _ _ (x.small_X hr q₀ v hv hK he z) (a_pos z).le)
  intro he
  change 1-q.dimH v z≤_
  rw [q.dimH_Y v hv]
  exact (hc _ (x.coordLipY hr q₀ v hv z) (q.vp v) (x.vp_two hr q₀ v hv) j hj).trans
    (HH _ _ (x.large_Y hr q₀ v hv hK he z) (q.Bt_nonneg z))
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_InTail
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform tail integral estimate over a spectral box. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers ProjField
variable {m : ℕ} [NeZero m]
namespace Param
variable {R : ℝ} (x:Param m R) (hr:0<R) (q₀:ProjField m)
lemma s0_four : (x.instanceQ hr q₀).s0 ≤ 4 := by
  unfold s0 trN
  rw [div_le_iff₀ m_pos,← mul_one (x.instanceQ hr q₀).covMat,(x.instanceQ hr q₀).trace_SPS]
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  apply le_trans (Finset.sum_le_sum (g := fun i => (4:ℝ)) ?_)
  · simp; rw [mul_comm]
  intro i hi
  rw [_root_.map_one]
  change ⟪op (x.instanceQ hr q₀).S (b i), op (x.instanceQ hr q₀).S (b i)⟫ ≤ _
  have hn : ‖b i‖ = 1 := b.orthonormal.1 i
  rw [← Z_def,real_inner_self_eq_norm_sq]
  have hh := x.Z_two hr q₀ (b i)
  rw [hn,mul_one] at hh
  nlinarith [norm_nonneg ((x.instanceQ hr q₀).Z (b i))]

lemma area_B :
    IntegrableOn (x.instanceQ hr q₀).Bt (Ici (0:ℝ)) ∧ (∫ t in Ici (0:ℝ), (x.instanceQ hr q₀).Bt t) ≤ 8 := by
  let s := Ici (0:ℝ)
  let μ := (volume : Measure ℝ).restrict s
  have he (z:ℝ) (hz:z∈s) : (x.instanceQ hr q₀).Bt z ≤ 2*(x.instanceQ hr q₀).layerW z := by
    have hp : 1/2 ≤ p z := by rw [← p_half]; apply p_mono.monotone hz
    have hq := (x.instanceQ hr q₀).Bt_nonneg z
    unfold layerW
    nlinarith [(x.instanceQ hr q₀).r1_pos z,a_pos z]
  have hi : Integrable (fun z=> (2:ℝ)*(x.instanceQ hr q₀).layerW z) μ :=
    ((x.instanceQ hr q₀).integrable_w.const_mul _).integrableOn
  have hh : Integrable (x.instanceQ hr q₀).Bt μ := hi.mono' (x.instanceQ hr q₀).Bt_cd.continuous.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg ((x.instanceQ hr q₀).Bt_nonneg z)]
    apply he z hz)
  refine ⟨hh,?_⟩
  apply le_trans (setIntegral_mono_on hh hi measurableSet_Ici he)
  rw [integral_const_mul]
  have h := setIntegral_le_integral (s := s) (x.instanceQ hr q₀).integrable_w
    (ae_of_all _ fun z => ((x.instanceQ hr q₀).w_positive z).le)
  rw [(x.instanceQ hr q₀).integral_w] at h
  have h' := x.s0_four hr q₀
  linarith

lemma B_segment (z : ℝ) (h : -1 ≤ z) :
    (x.instanceQ hr q₀).Bt z ≤ 4/a (-1) := by
  have hp : a (-1) ≤ a z := a_mono.monotone h
  have hb := ((x.instanceQ hr q₀).mul_Bt_avH z).trans (((x.instanceQ hr q₀).avH_le_s z).trans (x.s0_four hr q₀))
  apply (le_div_iff₀ (a_pos _)).mpr
  nlinarith [(x.instanceQ hr q₀).Bt_nonneg z]
end Param

lemma exponential_area {N C:ℝ} (hc:0<C) :
    let L := C*(1+N)
    let g := fun z => Real.exp (-(z/C-1-N))
    IntegrableOn g (Ioi L) ∧ (∫ z in Ioi L, g z) = C := by
  intro L g
  let f := fun z : ℝ => -C*g z
  have hd (z:ℝ) : HasDerivAt f (g z) z := by
    have hi := ((((((hasDerivAt_id' z).div_const C).sub_const 1).sub_const N).neg.exp)).const_mul (-C)
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (unfold g; field_simp; rfl)
  have ht : Tendsto (fun z:ℝ=>-(z/C-1-N)) atTop atBot := by
    apply tendsto_neg_atTop_atBot.comp
    simp only [sub_eq_add_neg]
    apply tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ ?_)
    exact Tendsto.atTop_div_const hc tendsto_id
  have he : Tendsto f atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp ht).const_mul (-C)
    simpa only [mul_zero,f,g,Function.comp_def] using h
  have hi := integrableOn_Ioi_deriv_of_nonneg' (a:=L) (fun z _=>hd z) (fun z _=>Real.exp_nonneg _) he
  refine ⟨hi,?_⟩
  have hu := integral_Ioi_of_hasDerivAt_of_tendsto' (a:=L) (fun z _=>hd z) hi he
  rw [hu]
  change 0- -C*Real.exp _=C
  rw [show -(L/C-1-N)=0 from by dsimp [L]; field_simp; ring, Real.exp_zero]
  ring

lemma dir_tail_area (m:ℕ) [NeZero m] :
    ∃ A ≥ 0, ∀ K, ∀ q : ProjField m, q.Bound K → ∀ v:Rn m, ‖v‖=1 →
    ∀ N:ℝ, 4≤N →
    let C := cutoffC m K
    let L := C*(1+N)
    (∫ z in Ioi L,(1-q.dimH v z)) ≤ A*Real.exp (-(N^2)/4)*C := by
  classical
  obtain ⟨A,hA,h₁⟩ := normal_tail m 0
  refine ⟨A,hA,fun K q hk v hv N hn => ?_⟩
  let C := cutoffC m K
  let L := C*(1+N)
  let g := fun z => Real.exp (-(z/C-1-N))
  have hb := positive_exact m hk.one_le
  have hc : 0<C := lt_of_lt_of_le zero_lt_one hb.1
  have hi := exponential_area (N:=N) hc
  have HE (z) (hz:z∈Ioi L) : 1-q.dimH v z ≤ A*Real.exp (-(N^2)/4)*g z := by
    let y := z/C-1
    let S : Set (Rn m) := {x| y ≤ ‖x‖}
    have hm : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
    let f := fun x:Rn m => (1-⟪v,op (q.Pmat z x) v⟫)
    have hf (x) : f x ≤ S.indicator (fun x:Rn m=> (1+‖x‖)^0) x := by
      by_cases hx:x∈S
      · rw [indicator_of_mem hx,pow_zero]
        exact sub_le_self _ ((op_posSemidef_iff.mp (q.Pmat_psd z x).posSemidef).2 v)
      rw [indicator_of_notMem hx]
      have hh : q.Pmat z x = 1 := by
        apply projJac_id q.C (hb.2 q hk _ x ?_)
        change ¬ z/C-1≤‖x‖ at hx
        rw [mul_comm]
        apply (lt_div_iff₀ hc).mp
        linarith
      unfold f; rw [hh,_root_.map_one]; change 1-⟪v,v⟫≤0
      rw [real_inner_self_eq_norm_sq,hv]; norm_num
    let μ := normal m
    have hf' : Integrable (fun x:Rn m=>⟪v,op (q.Pmat z x) v⟫) μ :=
      integral_opPair (meanJac_integrable q.C q.root (q.shift z)) v v
    have he : 1-q.dimH v z=∫ x,f x ∂μ := by
      unfold f; rw [integral_sub (integrable_const (μ := μ) _) hf']; simp [ProjField.dimH,μ]
    have hny : N ≤ y := by
      change C*(1+N)<z at hz
      change N≤z/C-1
      have he : 1+N ≤ z/C := (le_div_iff₀ hc).mpr (by linarith)
      linarith
    rw [he]
    apply le_trans (integral_mono ((integrable_const _).sub hf')
      ((integrable_envelope (μ:=μ) 0).indicator hm) hf)
    rw [integral_indicator hm]
    apply le_trans (h₁ y (by linarith))
    rw [mul_assoc A]
    apply mul_le_mul_of_nonneg_left _ hA
    change Real.exp _ ≤ _*Real.exp (-(y-N))
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have hp := hi.1.const_mul (A*Real.exp (-(N^2)/4))
  have hl : Ioi L ⊆ Ici (0:ℝ) := fun z hz => by
    apply le_trans (show (0:ℝ) ≤ L by dsimp [L]; nlinarith) (le_of_lt (mem_Ioi.mp hz))
  apply le_trans (setIntegral_mono_on ((q.plus_int v hv).mono_set hl) hp measurableSet_Ioi HE)
  rw [integral_const_mul, hi.2]
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_AngleIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Diagonal balance, with separate estimates at the two ends of the coordinate box. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers ProjField
variable {m : ℕ} [NeZero m]

lemma ekpos (j:ℝ) : 0 ≤ ek j := Real.exp_nonneg _
lemma ekrapid : rapid ek := by
  convert rapid_exp_sq (show 0<(1/4:ℝ) by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  unfold ek; ring_nf
lemma small_minus_bound (m : ℕ) [NeZero m] {D:ℝ} (hd:0≤D) :
    ∃ W≥0, ∀ q:ProjField m, ∀ v:Rn m, ‖v‖=1 → ∀ R:ℝ, 2≤R →
    (∀ z j:ℝ, 1≤j → q.dimH v z ≤ D*(j/R*a z + ek j)) →
    q.minus v ≤ W := by
  let b := fun z:ℝ => (phi z * (1+‖z‖) + ek z)
  let c := fun z:ℝ => D*b z
  have hb : PolyBound (fun z:ℝ => 1+‖z‖) :=
    (PolyBound.const _).add PolyBound.id.norm
  have hm : Measurable ek := by unfold ek; fun_prop
  have hf : Integrable b := ((rapid_phi.product hb).integrable_real
    (by have h := (by unfold phi; fun_prop : Measurable phi); fun_prop)).add
    (ekrapid.integrable_real hm)
  refine ⟨∫ z,c z,?_, fun q v hv R hr h => ?_⟩
  · exact integral_nonneg fun z=>mul_nonneg hd
      (add_nonneg (mul_nonneg (phi_pos z).le (by positivity)) (ekpos _))
  change ∫ z in Iio (0:ℝ), q.dimH v z ≤ _
  have hI : Integrable c := hf.const_mul _
  apply le_trans _ (setIntegral_le_integral (s:=Iio 0) hI
    (ae_of_all _ fun z=>mul_nonneg hd
      (add_nonneg (mul_nonneg (phi_pos z).le (by positivity)) (ekpos _))))
  apply setIntegral_mono_on (q.minus_int v hv) hI.integrableOn measurableSet_Iio
  intro z hz
  apply le_trans (h z (1+‖z‖) (by have h := norm_nonneg z; linarith))
  apply mul_le_mul_of_nonneg_left _ hd
  apply add_le_add
  · rw [mul_comm (phi z)]
    have hA := a_high (-z) (by change z<0 at hz; linarith)
    rw [neg_neg, neg_phi] at hA
    exact mul_le_mul (div_le_self (by positivity) (show 1 ≤ R by linarith)) hA (a_pos z).le (by positivity)
  apply Real.exp_le_exp.mpr
  rw [Real.norm_eq_abs,abs_of_neg (mem_Iio.mp hz)]
  change z<0 at hz
  nlinarith

lemma small_plus_lower {D : ℝ} (q:ProjField m) (v:Rn m) (hv:‖v‖=1)
    {L R N : ℝ} (hd:0≤D) (hr:0<R) (hN : 1 ≤ N) (hl:0≤L)
    (h:∀ z:ℝ, q.dimH v z ≤ D*(N/R*a z+ek N))
    (hh:D*(N/R*a L+ek N) ≤ 1/2) :
    L*(1/2) ≤ q.plus v := by
  let s := Icc 0 L
  let f := fun z=>1-q.dimH v z
  have hi : IntegrableOn f (Ici 0) := q.plus_int v hv
  have hs : s ⊆ Ici 0 := Icc_subset_Ici_self
  apply le_trans _ (setIntegral_mono_set hi
    (ae_of_all _ fun z=> sub_nonneg.mpr (q.h_between v hv z).2)
    (Filter.Eventually.of_forall hs))
  have hL : (∫ _ : ℝ in s,(1/2:ℝ))=L*(1/2) := by
    rw [setIntegral_const]
    simp [s,Real.volume_real_Icc_of_le hl]
  rw [← hL]
  refine setIntegral_mono_on (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
    (hi.mono_set hs) measurableSet_Icc (fun z hz=>?_)
  have he : q.dimH v z ≤ 1/2 := le_trans (h z)
    (le_trans (show D*(N/R*a z+ek N) ≤ _ from
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (a_mono.monotone hz.2) (by positivity)) le_rfl) hd) hh)
  unfold f; linarith

lemma large_minus_lower {D R N : ℝ} (hr:0<R) (x:Param m R) (q₀:ProjField m)
    (v:Rn m) (hv:‖v‖=1) (hd:0≤D) (hN : 1 ≤ N)
    (hh:D*(N/R*(4/a (-1))+ek N) ≤ 1/2) :
    let q := x.instanceQ hr q₀
    (∀ z:ℝ, 1-q.dimH v z ≤ D*(N/R*q.Bt z+ek N)) →
      1/2 ≤ q.minus v := by
  intro q h
  let s := Ico (-1:ℝ) 0
  have hi := q.minus_int v hv
  have hs : s ⊆ Iio 0 := Ico_subset_Iio_self
  apply le_trans _ (setIntegral_mono_set hi (ae_of_all _ fun z=>(q.h_between v hv z).1)
    (Filter.Eventually.of_forall hs))
  have hL : (∫ _ : ℝ in s,(1/2:ℝ))=1/2 := by
    rw [setIntegral_const]
    norm_num [s,Real.volume_real_Ico]
  rw [← hL]
  refine setIntegral_mono_on (integrableOn_const
    (hs := (lt_of_le_of_lt (measure_mono Ico_subset_Icc_self)
      isCompact_Icc.measure_lt_top).ne)) (hi.mono_set hs) measurableSet_Ico ?_
  intro z hz
  have he : 1-q.dimH v z ≤ 1/2 := le_trans (h z)
    (le_trans (show D*(N/R*q.Bt z+ek N) ≤ _ from
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (x.B_segment hr q₀ z hz.1) (by positivity)) le_rfl) hd) hh)
  linarith

lemma large_core_upper {D R L N:ℝ} (hr:0<R) (x:Param m R) (q₀:ProjField m)
    (v:Rn m) (hv:‖v‖=1) (hd:0≤D) (hN:1≤N) (hl:0≤L) :
    let q := x.instanceQ hr q₀
    (∀ z, 1-q.dimH v z ≤ D*(N/R*q.Bt z+ek N)) →
    (∫ z in Icc (0:ℝ) L, (1-q.dimH v z)) ≤ D*N/R*8 + D*ek N*L := by
  intro q hh
  have h := x.area_B hr q₀
  have hi : IntegrableOn q.Bt (Ici 0) := h.1
  let s := Icc 0 L
  have hs : s ⊆ Ici 0 := Icc_subset_Ici_self
  have ha : IntegrableOn (fun z : ℝ=>D*N/R*q.Bt z) s := (hi.mono_set hs).const_mul _
  have hb : IntegrableOn (fun _ : ℝ=>D*ek N) s := integrableOn_const
    (hs := isCompact_Icc.measure_lt_top.ne)
  have he : (∫ z in s,q.Bt z) ≤ 8 := le_trans (setIntegral_mono_set hi
    (ae_of_all _ q.Bt_nonneg) (Filter.Eventually.of_forall hs)) h.2
  let f := fun z=>1-q.dimH v z
  have hf : IntegrableOn f s := (q.plus_int v hv).mono_set hs
  calc
    _ ≤ ∫ z in s,(D*N/R*q.Bt z+D*ek N) :=
      setIntegral_mono_on hf (ha.add hb) measurableSet_Icc
        (fun z _=> (hh z).trans_eq (by ring))
    _ = D*N/R*(∫ z in s,q.Bt z)+D*ek N*L := by
      rw [integral_add ha hb, integral_const_mul,setIntegral_const]
      simp [s,Real.volume_real_Icc_of_le hl,mul_comm]
    _ ≤ _ := by gcongr

lemma plus_split (q:ProjField m) (v:Rn m) (hv:‖v‖=1) {L : ℝ} (hl:0≤L) :
    let f := fun z=>1-q.dimH v z
    q.plus v = (∫ z in Icc 0 L,f z)+(∫ z in Ioi L, f z) := by
  intro f
  have he : Icc 0 L ∪ Ioi L = Ici 0 := by
    ext z
    change ((0≤z ∧ z≤L) ∨ L<z) ↔ _
    simp only [mem_Ici]
    grind
  have hi : IntegrableOn f (Ici 0) := q.plus_int v hv
  rw [← he] at hi
  change (∫ z in Ici 0,f z) = _
  rw [← he]
  refine setIntegral_union ?_ measurableSet_Ioi (hi.mono_set subset_union_left)
    (hi.mono_set subset_union_right)
  exact disjoint_left.mpr fun z hz hh=> not_lt_of_ge hz.2 hh
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Scarf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scarf incidence argument used to prove the fixed point principle needed
for the simultaneous normalization. In spirit cf. Ivanov "Beyond Sperner's
lemma". Here we use labels as extra ghost vertices so facets can use
ordinary Finset inclusion.
-/

noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

variable (r : Orders I T)

omit [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
lemma dom_subset {s d : Finset T} (h : d ⊆ s) (hd : dom r s) :
    dom r d := fun x => by
      obtain ⟨i,he⟩ := hd x
      exact ⟨i,fun y hy => he y (h hy)⟩

omit [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
lemma min_nodes {s : Finset T} (hs : s.Nonempty) :
    ∃ u : I → T, ∀ i, u i ∈ s ∧ ∀ x∈s, r.rank i (u i) ≤ r.rank i x := by
  have h (i : I) := Finset.exists_min_image s (r.rank i) hs
  choose u he hu using h
  exact ⟨u,fun i=>⟨he i,hu i⟩⟩

omit [DecidableEq I] [Fintype T] in
lemma min_cover {s : Finset T} (hs : dom r s) {u : I→T}
    (h : ∀ i, u i ∈ s ∧ ∀ x∈s, r.rank i (u i) ≤ r.rank i x) :
    univ.image u = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
    subst x; exact (h i).1
  · intro hx
    obtain ⟨i,hi⟩ := hs x
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,
      r.inj i (le_antisymm ((h i).2 _ hx) (hi _ (h i).1))⟩

variable {A B : Type*} [DecidableEq A] [DecidableEq B]
lemma image_erase_eq' {s:Finset A} {u : A→B} {a b : A}
    (hb:b∈s) (hne:a≠b) (he:u a=u b) :
    (s.erase a).image u = s.image u := by
  ext y
  simp only [Finset.mem_image,Finset.mem_erase]
  constructor
  · rintro ⟨i,⟨-,hi⟩,he⟩; exact ⟨i,hi,he⟩
  · rintro ⟨i,hi,hd⟩
    by_cases hu:i=a
    · subst i; exact ⟨b,⟨Ne.symm hne,hb⟩,he.symm.trans hd⟩
    · exact ⟨i,⟨hu,hi⟩,hd⟩

-- unique pair of repeated indices of a map onto one-less elements
lemma duplicate_pair {s:Finset A} (u : A→B)
    (h : s.card = (s.image u).card+1) :
    ∃ a ∈ s, ∃ b ∈ s, a≠b ∧ u a=u b ∧
      ∀ i ∈ s, ∀ j ∈ s, i≠j → u i=u j → (i=a ∧ j=b) ∨ (i=b ∧ j=a) := by
  obtain ⟨a,ha,b,hb,hab,he⟩ := exists_ne_map_eq_of_card_image_lt (f := u) (s := s) (by omega)
  have H (a b : A) (ha:a∈s) (hb:b∈s) (hab:a≠b) (he:u a=u b) :
      Set.InjOn u (↑(s.erase a)) := injOn_of_card_image_eq (by
        rw [image_erase_eq' hb hab he, card_erase_of_mem ha]; omega)
  refine ⟨a,ha,b,hb,hab,he,?_⟩
  intro i hi j hj hij heq
  have H₁ := H a b ha hb hab he
  have H₂ := H b a hb ha (Ne.symm hab) he.symm
  have heither (a:A) (H:Set.InjOn u (↑(s.erase a))) : i=a ∨ j=a := by
    by_contra! h
    exact hij (H (mem_erase.mpr ⟨h.1,hi⟩) (mem_erase.mpr ⟨h.2,hj⟩) heq)
  rcases heither a H₁ with h|h <;> rcases heither b H₂ with h'|h' <;> grind

section Door
variable (d : Finset T)
variable {d}

omit [DecidableEq T] in
lemma mem_cand' {u : I → T} {i : I} {x : T} :
    x∈cand r u i ↔ ∀ j:I, j≠i → r.rank j (u j) < r.rank j x := by simp [cand]

lemma extension_spec {d : Finset T} {u : I → T} {x : T}
    (hd : door r d) (hm : ∀ i, u i ∈ d ∧ ∀ x∈d, r.rank i (u i) ≤ r.rank i x) :
    (x∉d ∧ room r (insert x d)) ↔
      ∃ i:I, (∃ j, i≠j ∧ u i=u j) ∧ x ∈ cand r u i ∧
        ∀ y ∈ cand r u i, r.rank i y ≤ r.rank i x := by
  have hh := min_cover r hd.2 hm
  constructor
  · rintro ⟨hx,hc,H⟩
    obtain ⟨v,hmin⟩ := min_nodes r (Finset.insert_nonempty x d)
    have heq := min_cover r H hmin
    have hi : Set.InjOn v (↑(univ : Finset I)) := injOn_of_card_image_eq (by rw [heq,hc,card_univ])
    have hu : x ∈ (univ.image v) := by rw [heq]; exact mem_insert_self ..
    obtain ⟨i,-,he⟩ := Finset.mem_image.mp hu
    have hv (j) (hj:j≠i) : u j=v j ∧ r.rank j (u j) < r.rank j x := by
      have hne : v j ≠ x := fun h' => hj (hi (Finset.mem_univ _) (Finset.mem_univ _) (h'.trans he.symm))
      have hmj : v j∈d := (mem_insert.mp (hmin j).1).resolve_left hne
      have eq := r.inj j (le_antisymm ((hm j).2 _ hmj)
        ((hmin j).2 _ (mem_insert_of_mem (hm j).1)))
      rw [eq]
      exact ⟨rfl, lt_of_le_of_ne ((hmin j).2 _ (mem_insert_self ..)) (fun HH=>hne (r.inj j HH))⟩
    have hh' : u i ∈ univ.image v := heq.symm ▸ mem_insert_of_mem (hm i).1
    obtain ⟨j,-,hj⟩ := Finset.mem_image.mp hh'
    have hn : j ≠ i := by intro h; apply hx; rw [← he,← h,hj]; apply (hm i).1
    refine ⟨i,⟨j,Ne.symm hn,hj.symm.trans (hv j hn).1.symm⟩,
      (mem_cand' r).mpr (fun j h => (hv j h).2),fun y hy => ?_⟩
    obtain ⟨k,Hk⟩ := H y
    by_cases hk : k=i
    · subst k; exact Hk x (mem_insert_self ..)
    · exact False.elim ((not_lt_of_ge (Hk (u k) (mem_insert_of_mem (hm k).1))) ((mem_cand' r).mp hy k hk))
  · rintro ⟨i,⟨j,hne,hij⟩,hc,H⟩
    have hh₁ := (mem_cand' r).mp hc
    have hx : x∉d := by
      intro hx
      obtain ⟨l,hl⟩ := hd.2 x
      by_cases h:l=i
      · subst l
        have he := r.inj i (le_antisymm (hl _ (hm i).1) ((hm i).2 _ hx))
        have hp := hh₁ j (Ne.symm hne)
        rw [he,hij] at hp; exact lt_irrefl _ hp
      · exact not_lt_of_ge (hl _ (hm l).1) (hh₁ l h)
    have hk : r.rank i x ≤ r.rank i (u i) := by
      obtain ⟨l,hl⟩ := hd.2 x
      by_cases h:l=i
      · subst l; exact hl _ (hm i).1
      · exact False.elim (not_lt_of_ge (hl _ (hm l).1) (hh₁ l h))
    refine ⟨hx,by rw [card_insert_of_notMem hx, hd.1], fun y => ?_⟩
    by_cases hy : y ∈ cand r u i
    · refine ⟨i,?_⟩
      intro t ht
      rcases mem_insert.mp ht with h|h
      · subst t; exact H _ hy
      · exact (H _ hy).trans (hk.trans ((hm i).2 _ h))
    · rw [mem_cand'] at hy
      push Not at hy
      obtain ⟨l,hl,he⟩ := hy
      refine ⟨l,?_⟩
      intro t ht
      rcases mem_insert.mp ht with h|h
      · subst t; exact he.trans (hh₁ _ hl).le
      · exact he.trans ((hm l).2 _ h)
end Door
end GeneralMahler.Scarf

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Ghost
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Add labeled slack/ghost vertices. -/
noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] [Nonempty T]

variable (q : GOrders I T)

-- Either one or two extensions
omit [Nonempty T] in
lemma extensions_two {d: Finset (I⊕T)} (hd : door q.toOrders d) (hu : inside d) :
    ∃ s₁ s₂, s₁ ≠ s₂ ∧ ∀ s, room q.toOrders s ∧ d⊆s ↔ s=s₁ ∨ s=s₂ := by
  obtain ⟨x,hx⟩ := hu
  let r := q.toOrders
  obtain ⟨v,hv⟩ := min_nodes r (show d.Nonempty from ⟨_,hx⟩)
  have he := min_cover r hd.2 hv
  have hg (i j:I) (hi:i≠j) : v i ≠ Sum.inl j := by
    intro h
    have H := (hv i).2 (.inr x) hx
    rw [h] at H
    exact not_lt_of_ge H (q.high i j hi x)
  have hm : (univ:Finset I).card=(univ.image v).card+1 := by rw [card_univ,he]; exact hd.1
  obtain ⟨a,-,b,-,ha,hb,h⟩ := duplicate_pair v hm
  have hh (i j:I) (hi:i≠j) (hj:v i=v j) : (cand r v i).Nonempty := by
    refine ⟨Sum.inl i, (mem_cand' r).mpr ?_⟩
    intro l hl
    cases e:v l with
    | inl y =>
      have hy : l=y := by
        by_contra hn
        exact hg l y hn e
      subst l; exact (q.low y x).trans (q.high y _ hl _)
    | inr t => exact q.high _ _ hl _
  obtain ⟨s,hs,Hs⟩ := Finset.exists_max_image (cand r v a) (r.rank a) (hh _ _ ha hb)
  obtain ⟨t,ht,Ht⟩ := Finset.exists_max_image (cand r v b) (r.rank b) (hh _ _ (Ne.symm ha) hb.symm)
  have H₁ : s∉d ∧ room r (insert s d) :=
    (extension_spec r hd hv).mpr ⟨a,⟨b,ha,hb⟩,hs,Hs⟩
  have H₂ : t∉d ∧ room r (insert t d) :=
    (extension_spec r hd hv).mpr ⟨b,⟨a,Ne.symm ha,hb.symm⟩,ht,Ht⟩
  have hst : s ≠ t := by
    rintro rfl
    obtain ⟨i,hi⟩ := hd.2 s
    have he := hi (v i) (hv i).1
    by_cases h:i=a
    · subst i; exact not_lt_of_ge he ((mem_cand' r).mp ht a ha)
    · exact not_lt_of_ge he ((mem_cand' r).mp hs i h)
  refine ⟨insert s d, insert t d,fun ep => ?_,fun y => ?_⟩
  · have hh : s ∈ insert t d := ep ▸ mem_insert_self ..
    exact (mem_insert.mp hh).elim hst H₁.1
  constructor
  · rintro ⟨hr,hdy⟩
    obtain ⟨l,hl,rfl⟩ := Finset.exists_eq_insert_iff.mpr (show d⊆y ∧ d.card+1=y.card from
      ⟨hdy,hd.1.symm.trans hr.1.symm⟩)
    obtain ⟨i,⟨j,hij,heij⟩,hli,Hli⟩ := (extension_spec r hd hv).mp ⟨hl,hr⟩
    rcases h i (mem_univ _) j (mem_univ _) hij heij with ⟨hh,-⟩ | ⟨hh,-⟩
    · subst i
      exact Or.inl (congrArg (fun x => insert x d) (r.inj _ (le_antisymm (Hs _ hli) (Hli _ hs))))
    · subst i
      exact Or.inr (congrArg (fun x => insert x d) (r.inj _ (le_antisymm (Ht _ hli) (Hli _ ht))))
  · rintro (rfl|rfl)
    · exact ⟨H₁.2, subset_insert ..⟩
    · exact ⟨H₂.2, subset_insert ..⟩

-- handles also I singleton
omit [Fintype T] in
lemma outer_door (i:I) : door q.toOrders (outer i) := by
  constructor
  · have h : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
    unfold outer; rw [card_image_of_injective _ Sum.inl_injective,card_erase_of_mem (mem_univ _),card_univ]
    omega
  · intro w
    cases w with
    | inr x =>
      refine ⟨i,fun y hy=>?_⟩
      cases y with
      | inl j =>
        exact (q.high i j (Ne.symm ((mem_outer i j).mp hy)) x).le
      | inr y => exact False.elim (not_mem_outer i y hy)
    | inl j =>
      refine ⟨j,fun y hy=>?_⟩
      cases y with
      | inl y =>
        by_cases he:y=j
        · subst j; exact le_refl _
        · obtain ⟨x⟩ := ‹Nonempty T›
          exact ((q.low j x).trans (q.high j y (Ne.symm he) x)).le
      | inr x => exact (q.low j x).le

lemma extension_outer (i:I) :
    ∃! s, room q.toOrders s ∧ outer i ⊆ s := by
  let r := q.toOrders
  obtain ⟨x,hx,Hx⟩ := Finset.exists_max_image (univ:Finset T) (fun x=>r.rank i (Sum.inr x))
    univ_nonempty
  have hc := (outer_door q i).1
  let s := insert (Sum.inr x) (outer i : Finset (I⊕T))
  refine ⟨s,⟨⟨?_,?_⟩, subset_insert ..⟩,?_⟩
  · change (insert (Sum.inr x) (outer i)).card=_
    rw [card_insert_of_notMem (not_mem_outer i x)]
    exact hc.symm
  · intro y
    cases y with
    | inl j =>
      obtain ⟨j',hj⟩ := (outer_door q i).2 (Sum.inl j)
      refine ⟨j,fun w hw => ?_⟩
      cases w with
      | inr t => exact (q.low j t).le
      | inl k =>
        by_cases he:j=k
        · rw [he]
        · exact ((q.low j x).trans (q.high j k he x)).le
    | inr z =>
      refine ⟨i,fun w hw => ?_⟩
      rcases mem_insert.mp hw with he|he
      · subst w; exact Hx z (mem_univ _)
      cases w with
      | inl j => exact (q.high i j (Ne.symm ((mem_outer i j).mp he)) z).le
      | inr j => exact False.elim (not_mem_outer i j he)
  · rintro z ⟨hz,hzr⟩
    obtain ⟨w,hw,rfl⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨hzr,hc.symm.trans hz.1.symm⟩
    obtain ⟨j,hj⟩ := hz.2 (Sum.inr x)
    have he : j=i := by
      by_contra H
      have ha := hj (Sum.inl j) (mem_insert_of_mem ((mem_outer i j).mpr H))
      exact not_lt_of_ge ha (q.low j x)
    subst j
    cases w with
    | inr y =>
      have hxy : Sum.inr x = Sum.inr y :=
        q.inj i (le_antisymm (hj _ (mem_insert_self ..)) (Hx y (mem_univ _)))
      rw [← hxy]
    | inl j =>
      have hji : j=i := by
        by_contra he
        exact hw ((mem_outer i j).mpr he)
      subst j
      exact False.elim (not_lt_of_ge (hj _ (mem_insert_self ..)) (q.low i x))
end GeneralMahler.Scarf

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Color
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Incidence parity implies a full room for every coloring. -/
noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Nonempty T]

omit [DecidableEq I] [Fintype T] [Nonempty T] in
lemma erase_door {r : Orders I T} {s} (hs:room r s) {x:T} (hx:x∈s) :
    door r (s.erase x) := by
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨_,hx⟩
  refine ⟨?_,dom_subset r (erase_subset ..) hs.2⟩
  rw [card_erase_of_mem hx,← hs.1]; omega

omit [Fintype T] [Nonempty T] in
lemma two_if_not_colorful (r : Orders I T) (c:T→I) (i:I) {s:Finset T}
    (h : room r s) (hn : s.image c ≠ univ)
    (p : Finset T → Prop)
    (hp : ∀ d, p d ↔ door r d ∧ d⊆s ∧ d.image c=univ.erase i)
    (he : ∃ d,p d) :
    ∃ x y, x≠y ∧ ∀ d, p d ↔ d=x ∨ d=y := by
  obtain ⟨d₀,hd₀⟩ := he
  obtain ⟨ht,hds,heq⟩ := (hp d₀).mp hd₀
  have hh : s.image c=univ.erase i := Finset.Subset.antisymm (fun x hx=>by
    have hskip : x≠i := by
      intro a; subst x
      apply hn
      ext x
      simp only [mem_univ, iff_true]
      by_cases hv:x=i
      · subst x; exact hx
      · exact Finset.image_subset_image hds (by simp [heq,hv])
    simpa using hskip) (heq ▸ Finset.image_subset_image hds)
  have hI : Fintype.card I > 0 := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨x,hx,y,hy,hxy,hf,he⟩ := duplicate_pair (s := s) c (by
    rw [h.1,hh, Finset.card_erase_of_mem (mem_univ i), card_univ]
    omega)
  refine ⟨s.erase x,s.erase y,?_,fun d=>?_⟩
  · intro h
    have hn : y ∈ s.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy,hy⟩
    rw [h] at hn
    simp at hn
  constructor
  · intro h₁
    obtain ⟨h₂,h₃,h₄⟩ := (hp d).mp h₁
    obtain ⟨z,hz,heq⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨h₃,h₂.1.symm.trans h.1.symm⟩
    have hzs : z∈s := heq ▸ mem_insert_self ..
    have hm : d=s.erase z := by simp [← heq,hz]
    have hn : c z ∈ d.image c :=
      (hh.trans h₄.symm) ▸ Finset.mem_image_of_mem _ hzs
    obtain ⟨l,hl,hl'⟩ := Finset.mem_image.mp hn
    have hn : z≠l := by rintro hh; subst l; exact hz hl
    rcases he z hzs l (h₃ hl) hn hl'.symm with ⟨he,-⟩|⟨he,-⟩ <;> simp [hm,he]
  · rintro (rfl|rfl)
    · exact (hp _).mpr ⟨erase_door h hx, Finset.erase_subset .., (image_erase_eq' hy hxy hf).trans hh⟩
    · exact (hp _).mpr ⟨erase_door h hy, Finset.erase_subset ..,
        (image_erase_eq' hx (Ne.symm hxy) hf.symm).trans hh⟩

lemma count_unique [Fintype X] {p : X → Prop} [DecidablePred p]
    (h : ∃! x,p x) :
    ∑ x:X, (if p x then (1:ZMod 2) else 0) = 1 := by
  classical
  obtain ⟨x,hx,he⟩ := h
  rw [sum_eq_single x] <;> grind

lemma count_two [Fintype X] {p : X → Prop} [DecidablePred p]
    (h : ∃ x y, x≠y ∧ ∀ i, p i ↔ i=x ∨ i=y) :
    ∑ x:X, (if p x then (1:ZMod 2) else 0) = 0 := by
  classical
  obtain ⟨x,y,hx,he⟩ := h
  rw [← Finset.add_sum_erase univ _ (mem_univ x),
    Finset.sum_eq_single y]
  · simp [he]; decide
  · intro i hi h
    have hu : i≠x := (Finset.mem_erase.mp hi).1
    simp [he,hu,h]
  simp [Ne.symm hx]

theorem full_room [Nonempty I] (q : GOrders I T) (f : T → I) :
    ∃ s, room q.toOrders s ∧ s.image (Sum.elim id f) = univ := by
  classical
  obtain ⟨i⟩ := ‹Nonempty I›
  let c : I⊕T → I := Sum.elim id f
  let r := q.toOrders
  let P := fun (d s:Finset (I⊕T)) =>
    door r d ∧ room r s ∧ d ⊆ s ∧ d.image c = Finset.univ.erase i
  let H := fun d s => if P d s then (1:ZMod 2) else 0
  by_contra hh
  have hc (s) (hs: room r s) : s.image c ≠ univ := fun h => hh ⟨s,hs,h⟩
  have hr (s) : ∑ d,H d s = 0 := by
    by_cases h:∃ d,P d s
    · apply count_two
      obtain ⟨d,hd⟩ := h
      have hs := hd.2.1
      exact two_if_not_colorful r c i hs (hc _ hs) _ (by simp [P,hs]) ⟨d,hd⟩
    · simp only [not_exists] at h
      simp [H,h]
  let d₀ : Finset (I⊕T) := outer i
  have he : ∑ s,H d₀ s=1 := by
    have h : d₀.image c = univ.erase i := by simp [d₀,outer,image_image,c,Function.comp_def]
    have hh : door r d₀ := outer_door q _
    apply count_unique
    simpa [P,h,hh] using extension_outer q i
  have hm (d:Finset (I⊕T)) (hd:d≠d₀) : ∑ s,H d s=0 := by
    by_cases h:∃ s,P d s
    · obtain ⟨s,hs,Ht,hds,Hc⟩ := h
      have hh : inside d := by
        by_contra hno
        refine hd ?_
        ext x
        cases x with
        | inl j =>
          have hmem : j ∈ d.image c ↔ Sum.inl j ∈ d := by
            constructor
            · intro hv
              obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hv
              cases y with
              | inl y =>
                change y=j at he; subst j; exact hy
              | inr y => exact False.elim (hno ⟨_,hy⟩)
            · intro hy; exact Finset.mem_image.mpr ⟨_,hy,by simp [c]⟩
          rw [← hmem,Hc,mem_outer]; simp
        | inr y =>
          exact iff_of_false (fun hh => hno ⟨y,hh⟩) (not_mem_outer i y)
      apply count_two
      simpa [P,hs,Hc] using extensions_two q hs hh
    · simp only [not_exists] at h
      simp [H,h]
  have hs := Finset.sum_comm (s := univ) (t := univ) (f := H)
  simp_rw [hr,Finset.sum_const_zero] at hs
  rw [Finset.sum_eq_single d₀] at hs
  · rw [he] at hs
    exact one_ne_zero hs
  · exact fun _ _ h=>hm _ h
  simp

end GeneralMahler.Scarf

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Grid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! A colorful primitive room in grids on the standard simplex. -/
noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I]
  (N:ℕ)

lemma grid_extend (g : I → ℕ) (hg : ∑ i,g i ≤ N) :
    ∃ x : Grid I N, ∀ i, g i ≤ (x.val i).val := by
  obtain ⟨i⟩ := ‹Nonempty I›
  let f (j:I) := g j + if j=i then N - ∑ j,g j else 0
  have h : ∑ j,f j = N := by
    simp [f,sum_add_distrib,hg]
  have h1 (j:I) : f j<N+1 := by
    have he : f j ≤ ∑ j, f j := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ _)
    omega
  exact ⟨⟨fun j => ⟨f j,h1 j⟩, h⟩, fun j => Nat.le_add_right _ _⟩

instance instNonemptyGrid : Nonempty (Grid I N) :=
  have h := grid_extend I N (fun _=>0) (by simp); h.imp (fun _ _=>True.intro) |>
    fun he => by obtain ⟨x,hx⟩:=he; exact ⟨x⟩

lemma full_approx (f : Grid I N → I) :
    ∃ b : I→ℕ, ∃ s:Finset (I⊕Grid I N),
    inside s ∧ (∀ x:Grid I N, Sum.inr x∈s → ∀ i,
      b i ≤ (x.val i).val ∧ (x.val i).val ≤ b i+Fintype.card I) ∧
      (∀ i, b i=0 ∨ ∃ x:Grid I N, Sum.inr x∈s ∧ f x=i) := by
  let r := gridOrder I N
  obtain ⟨s,h,he⟩ := full_room r f
  have hs : inside s := by
    by_contra hn
    obtain ⟨x⟩ : Nonempty (Grid I N) := inferInstance
    obtain ⟨i,hi⟩ := h.2 (.inr x)
    have hmem : Sum.inl i ∈ s := by
      have hi' := Finset.mem_image.mp (show i∈s.image (Sum.elim id f) from he.symm ▸ mem_univ _)
      obtain ⟨a,ha,hb⟩ := hi'
      cases a with
      | inl j =>
        change j=i at hb; subst j; exact ha
      | inr y => exact False.elim (hn ⟨_,ha⟩)
    exact not_lt_of_ge (hi _ hmem) (r.low _ _)
  obtain ⟨x,hx⟩ := hs
  obtain ⟨v,hv⟩ := min_nodes r.toOrders (show s.Nonempty from ⟨_,hx⟩)
  have H (i j:I) (he:v i=.inl j) : i=j := by
    by_contra he'
    have hh := (hv i).2 _ hx
    rw [he] at hh; exact not_lt_of_ge hh (r.high i j he' _)
  let b := fun i => Sum.elim (fun _=>0) (fun a:Grid I N=>(a.val i).val) (v i)
  refine ⟨b,s,⟨x,hx⟩,?_,?_⟩
  · intro y hy
    have hh (i:I) : b i ≤ (y.val i).val := by
      simp only [b]; cases e : v i with
      | inl j => simp
      | inr z =>
        have h := (hv i).2 _ hy
        rw [e] at h
        by_contra! he
        exact not_lt_of_ge h (key_order I N _ _ _ he)
    have hc : N ≤ (∑ i, b i) + Fintype.card I := by
      by_contra! hn
      have hp : ∑ i, (b i+1) ≤ N := by simpa [Finset.sum_add_distrib] using hn.le
      obtain ⟨l,hl⟩ := grid_extend I N _ hp
      obtain ⟨i,hi⟩ := h.2 (.inr l)
      have hi' := hi _ (hv i).1
      have hf := hl i
      cases e : v i with
      | inl j =>
        rw [e, ← H i j e] at hi'
        exact not_lt_of_ge hi' (r.low _ _)
      | inr w =>
        simp only [b,e, Sum.elim_inr] at hf
        rw [e] at hi'; exact not_lt_of_ge hi' (key_order I N _ _ _ hf)
    intro i
    refine ⟨hh i,?_⟩
    have hp : ∑ j, (b j+ ((y.val j).val-b j)) = ∑ j,(y.val j).val :=
      Finset.sum_congr rfl fun j _ => Nat.add_sub_of_le (hh j)
    have hhi : (y.val i).val-b i ≤ ∑ j : I, ((y.val j).val-b j) :=
      Finset.single_le_sum (f := fun j : I => ((y.val j).val-b j)) (fun _ _=>Nat.zero_le _) (mem_univ i)
    rw [Finset.sum_add_distrib,y.property] at hp
    omega
  intro i
  have hi := Finset.mem_image.mp (show i∈s.image (Sum.elim id f) from he.symm ▸ mem_univ _)
  obtain ⟨y,hy,hfy⟩ := hi
  cases y with
  | inl j =>
    change j=i at hfy; subst j
    left; unfold b
    cases e:v i with
    | inl j=>simp
    | inr t =>
      have hh := (hv i).2 _ hy
      rw [e] at hh; exact False.elim (not_lt_of_ge hh (r.low i t))
  | inr t => exact Or.inr ⟨t,hy,hfy⟩
end GeneralMahler.Scarf

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.StdSimplexCompat
attribute [-instance] _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val _root_.OAI.vonNeumannToStarSubalgebraIsClosed
attribute [-simp] _root_.OAI.fin3_lit_0_1 _root_.OAI.fin3_lit_0_2 _root_.OAI.fin3_lit_1_0 _root_.OAI.fin3_lit_1_2 _root_.OAI.fin3_lit_2_0 _root_.OAI.fin3_lit_2_1 _root_.OAI.fin3_mk_0 _root_.OAI.fin3_mk_1 _root_.OAI.fin3_mk_2 _root_.OAI.fin4_lit_0_1 _root_.OAI.fin4_lit_0_2 _root_.OAI.fin4_lit_0_3 _root_.OAI.fin4_lit_1_0 _root_.OAI.fin4_lit_1_2 _root_.OAI.fin4_lit_1_3 _root_.OAI.fin4_lit_2_0 _root_.OAI.fin4_lit_2_1 _root_.OAI.fin4_lit_2_3 _root_.OAI.fin4_lit_3_0 _root_.OAI.fin4_lit_3_1 _root_.OAI.fin4_lit_3_2 _root_.OAI.fin4_mk_0 _root_.OAI.fin4_mk_1 _root_.OAI.fin4_mk_2 _root_.OAI.fin4_mk_3 _root_.OAI.fin5_lit_0_1 _root_.OAI.fin5_lit_0_2 _root_.OAI.fin5_lit_0_3 _root_.OAI.fin5_lit_0_4 _root_.OAI.fin5_lit_1_0 _root_.OAI.fin5_lit_1_2 _root_.OAI.fin5_lit_1_3 _root_.OAI.fin5_lit_1_4 _root_.OAI.fin5_lit_2_0 _root_.OAI.fin5_lit_2_1 _root_.OAI.fin5_lit_2_3 _root_.OAI.fin5_lit_2_4 _root_.OAI.fin5_lit_3_0 _root_.OAI.fin5_lit_3_1 _root_.OAI.fin5_lit_3_2 _root_.OAI.fin5_lit_3_4 _root_.OAI.fin5_lit_4_0 _root_.OAI.fin5_lit_4_1 _root_.OAI.fin5_lit_4_2 _root_.OAI.fin5_lit_4_3 _root_.OAI.fin5_mk_0 _root_.OAI.fin5_mk_1 _root_.OAI.fin5_mk_2 _root_.OAI.fin5_mk_3 _root_.OAI.fin5_mk_4 _root_.OAI.ofNat_le_infty _root_.OAI.vecCons3_one _root_.OAI.vecCons3_two _root_.OAI.vecCons4_one _root_.OAI.vecCons4_three _root_.OAI.vecCons4_two _root_.OAI.vecConsTail1_1 _root_.OAI.vecConsTail2_1 _root_.OAI.vecConsTail2_2 _root_.OAI.vecConsTail3_1 _root_.OAI.vecConsTail3_2 _root_.OAI.vecConsTail3_3 _root_.OAI.vecConsTail4_1 _root_.OAI.vecConsTail4_2 _root_.OAI.vecConsTail4_3 _root_.OAI.vecConsTail4_4 _root_.YoungDiagram.card_transpose
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

variable [IsStrictOrderedRing R]

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

end Semiring

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] _root_.Convexity.StdSimplex.topologicalSpace
lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Simplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Brouwer fixed point for the standard simplex. -/
noncomputable section
open Set Filter Real Metric
open scoped Topology
namespace GeneralMahler

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

lemma lattice_approx (f : (I→ℝ)→I→ℝ) (hf : MapsTo f (simplexSet I) (simplexSet I))
    (n:ℕ) :
    ∃ x ∈ simplexSet I, ∀ i:I, ∃ y ∈ simplexSet I,
      (∀ j:I, |x j-y j| ≤ Fintype.card I/((n+1:ℕ):ℝ)) ∧
        x i ≤ f y i + Fintype.card I/((n+1:ℕ):ℝ) := by
  let N := n+1
  have hp : (0:ℝ)<N := by dsimp [N]; positivity
  let F (x : Scarf.Grid I N) (i:I) : ℝ := (x.val i).val / (N:ℝ)
  have he (x) : F x ∈ simplexSet I := by
    refine ⟨fun i=>by dsimp only [F]; positivity,?_⟩
    dsimp only [F]
    rw [← Finset.sum_div,← Nat.cast_sum,x.property, div_self hp.ne']
  have hx (x) : ∃ i, F x i ≤ f (F x) i := by
    by_contra! hn
    have hu : ∑ i,f (F x) i < ∑ i, F x i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _=>hn i
    rw [(he x).2,(hf (he x)).2] at hu; exact lt_irrefl _ hu
  choose c hc using hx
  obtain ⟨b,s,⟨x,hx⟩,hl,hc'⟩ := Scarf.full_approx I N c
  let a : ℝ := Fintype.card I / (N:ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let B (i:I) : ℝ := b i / (N:ℝ)
  have hle (y : Scarf.Grid I N) (hy : Sum.inr y ∈ s) (i:I) :
      B i ≤ F y i ∧ F y i ≤ B i+a := by
    obtain ⟨h₁,h₂⟩ := hl y hy i
    dsimp only [B,F,a]
    rw [← add_div]
    constructor
    · gcongr
    · apply div_le_div_of_nonneg_right _ hp.le
      exact_mod_cast h₂
  refine ⟨F x,he x,fun i=>?_⟩
  obtain ⟨h₁,h₂⟩ := hle x hx i
  rcases hc' i with hi|⟨y,hy,hyi⟩
  · refine ⟨F x,he x,fun j=>by rw [sub_self,abs_zero]; exact ha,?_⟩
    have hu : B i=0 := by simp [B,hi]
    change _ ≤ _+a
    linarith [(hf (he x)).1 i]
  · refine ⟨F y,he y, fun j=>?_ ,?_⟩
    · change _ ≤ a; rw [abs_le]
      obtain ⟨h,h'⟩ := hle x hx j; obtain ⟨v,v'⟩ := hle y hy j
      constructor <;> linarith
    · change _ ≤ _+a
      have H := hc y; rw [hyi] at H
      exact h₂.trans (by linarith [(hle y hy i).1])

theorem BrouwerSimplex (f : (I→ℝ)→I→ℝ)
    (hf : MapsTo f (simplexSet I) (simplexSet I)) (hc : ContinuousOn f (simplexSet I)) :
    ∃ x ∈ simplexSet I, f x=x := by
  choose x hx y hy hd hle using lattice_approx f hf
  have hs : simplexSet I =
      Set.range (fun t : Convexity.StdSimplex ℝ I => (t.weights : I → ℝ)) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext f
    simp only [simplexSet, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  have hk : IsCompact (simplexSet I) := by
    rw [hs]
    exact isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ I).continuous
  obtain ⟨z,hz,b,hm,hb⟩ := hk.tendsto_subseq hx
  have hu := tendsto_pi_nhds.mp hb
  have he : Tendsto (fun n => (Fintype.card I:ℝ)/((b n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    have hv := tendsto_natCast_atTop_atTop (R := ℝ) |>.comp hm.tendsto_atTop
    have ha : Tendsto (fun n => ((b n+1:ℕ):ℝ)) atTop atTop := by
      simp; exact tendsto_atTop_add_const_right _ _ hv
    simpa using ((tendsto_const_nhds (x := (Fintype.card I:ℝ))).div_atTop ha)
  have hv (i:I) : Tendsto (fun n=>y (b n) i) atTop (𝓝 z) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have h₁ : Tendsto (fun n=>y (b n) i j - x (b n) j) atTop (𝓝 0) := by
      apply squeeze_zero_norm _ he
      intro n
      rw [Real.norm_eq_abs,abs_sub_comm]
      exact hd _ _ _
    convert h₁.add (hu j) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  have hh (i:I) : z i ≤ f z i := by
    have ha := hc z hz
    have h₁ : Tendsto (fun n=>y (b n) i) atTop (𝓝[simplexSet I] z) :=
      tendsto_nhdsWithin_iff.mpr ⟨hv i,Eventually.of_forall (fun n=>hy (b n) i)⟩
    have h₂ := tendsto_pi_nhds.mp (Tendsto.comp ha h₁) i
    have H := h₂.add he
    rw [add_zero] at H
    exact le_of_tendsto_of_tendsto (hu i) H (Eventually.of_forall fun n=>hle _ _)
  refine ⟨z,hz,funext fun i=>?_⟩
  by_contra hn
  have h : ∑ i,z i < ∑ i,f z i :=
    Finset.sum_lt_sum (fun j _=>hh j) ⟨i,Finset.mem_univ _,lt_of_le_of_ne (hh i) (Ne.symm hn)⟩
  rw [hz.2,(hf hz).2] at h
  exact lt_irrefl _ h
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Fixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! General fixed point for compact convex subsets of real normed spaces. -/
noncomputable section
open Set Filter Metric Real
open scoped Topology
namespace GeneralMahler
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma approx_fixedpoint (K : Set X) (hk : IsCompact K) (hc : Convex ℝ K)
    (he : K.Nonempty) (f:X→X) (hf : ContinuousOn f K) (hm : MapsTo f K K)
    {ε : ℝ} (hp : 0 < ε) :
    ∃ x∈K, ‖f x - x‖ ≤ ε := by
  classical
  obtain ⟨t,htk,ht,hcov⟩ := hk.finite_cover_balls hp
  let I := t
  let : Fintype I := ht.fintype
  have hec (x : X) (hx : x ∈ K) : ∃ i : I, dist x i.val < ε := by
    have h := hcov hx
    simp only [mem_iUnion] at h
    obtain ⟨z,hz,ha⟩ := h; exact ⟨⟨z,hz⟩,ha⟩
  let : Nonempty I := by
    obtain ⟨x,hx⟩ := he
    obtain ⟨i,_⟩ := hec x hx; exact ⟨i⟩
  let g (x:X) (i:I) := max 0 (ε-dist x i.val)
  let T (x:X) := ∑ i,g x i
  let r (x:X) (i:I) := g x i / T x
  have hg (x:X) (i:I) : 0 ≤ g x i := le_max_left ..
  have hT (x:X) (hx:x∈K) : 0<T x := by
    obtain ⟨i,hi⟩ := hec _ hx
    apply lt_of_lt_of_le _ (Finset.single_le_sum (f := g x)
      (fun j _=>hg x j) (Finset.mem_univ i))
    exact lt_of_lt_of_le (sub_pos.mpr hi) (le_max_right ..)
  have hmR (x) (hx:x∈K) : r x ∈ simplexSet I :=
    ⟨fun i=>div_nonneg (hg x i) (hT x hx).le,
      by dsimp only [r]; rw [← Finset.sum_div]; exact div_self (hT x hx).ne'⟩
  have hRc : ContinuousOn r K := by
    refine continuousOn_pi.mpr (fun i=>ContinuousOn.div ?_ ?_ ?_)
    · apply Continuous.continuousOn
      unfold g; fun_prop
    · apply Continuous.continuousOn
      unfold T g; fun_prop
    exact fun x hx=>(hT x hx).ne'
  let s (w:I→ℝ) := ∑ i:I,w i • i.val
  have hs : MapsTo s (simplexSet I) K :=
    fun x hx=>hc.sum_mem (fun i _ => hx.1 i) hx.2 (fun i _=>htk i.property)
  have hsc : Continuous s := by unfold s; fun_prop
  obtain ⟨w,hw,hew⟩ := BrouwerSimplex (r ∘ f ∘ s) (fun x hx=>hmR _ (hm (hs hx)))
    (hRc.comp (hf.comp hsc.continuousOn hs) (hm.comp hs))
  let x := s w
  have hx : x∈K := hs hw
  refine ⟨x,hx,?_⟩
  have he : ∑ i:I,w i • (f x - i.val) = f x - x := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw.2,one_smul]
    rfl
  calc
    _ = ‖∑ i:I,w i • (f x - i.val)‖ := by rw [he]
    _ ≤ ∑ i:I, ‖w i • (f x - i.val)‖ := norm_sum_le ..
    _ ≤ ∑ i:I,w i*ε := by
      apply Finset.sum_le_sum; intro i _
      rw [norm_smul,Real.norm_of_nonneg (hw.1 i)]
      by_cases h : dist (f x) i.val < ε
      · rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left h.le (hw.1 i)
      · have he : w i=0 := by
          have he : r (f x) i = w i := congrFun hew _
          rw [← he]
          unfold r g
          rw [max_eq_left (by linarith)]
          simp
        rw [he,zero_mul,zero_mul]
    _ = ε := by rw [← Finset.sum_mul,hw.2,one_mul]

theorem compact_fixedpoint (K : Set X) (hk : IsCompact K) (hc : Convex ℝ K)
    (he : K.Nonempty) (f:X→X) (hf : ContinuousOn f K) (hm : MapsTo f K K) :
    ∃ x∈K,f x=x := by
  obtain ⟨z,hz,h⟩ := hk.exists_isMinOn he (hf.sub continuous_id.continuousOn).norm
  by_cases hi : f z=z
  · exact ⟨z,hz,hi⟩
  have hpos : 0 < ‖f z-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hi)
  obtain ⟨x,hx,hx'⟩ := approx_fixedpoint K hk hc he f hf hm
    (ε:=‖f z-z‖/2) (by positivity)
  have hb : ‖f z-z‖ ≤ ‖f x-x‖ := h hx
  exfalso
  linarith
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Inward
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.Scarf.instNonemptyGrid _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! A Brouwer inward estimate using spectral boxes directly for the transform B
instead of round Frobenius balls in Q=log B. In particular the extreme
eigenvectors alone suffice. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers ProjField
variable {m : ℕ} [NeZero m]

lemma poly_cut (m:ℕ) (K:ℝ) : PolyBound fun x:ℝ=> cutoffC m (K*x^2) := by
  let f := fun x:ℝ=>K*x^2
  have hf : PolyBound f := (PolyBound.const _).mul (PolyBound.id.pow _)
  have he : PolyBound (fun x:ℝ=> f x * (m:ℝ) * f x ^ 2 * (a 0)⁻¹) :=
    (((hf.mul (PolyBound.const _)).mul (hf.pow _)).mul (PolyBound.const _))
  simp only [cutoffC,div_eq_mul_inv]
  exact (PolyBound.const _).add (((PolyBound.const _).mul hf).mul (hf.add he))

lemma inv_lim (D L : ℝ) :
    ∀ᶠ N : ℝ in atTop, D*(N/N^2*L+ek N) ≤ 1/2 := by
  have h : Tendsto (fun N:ℝ=>D*(N⁻¹*L+ek N)) atTop (𝓝 0) := by
    have he := ((tendsto_inv_atTop_zero (𝕜:=ℝ)).mul_const L).add ekrapid.tail_limit
    simpa using he.const_mul D
  filter_upwards [h.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), eventually_gt_atTop (0:ℝ)]
    with N hn hp
  change D*(N⁻¹*L+ek N)<_ at hn
  rw [show N/N^2=N⁻¹ from by field_simp]
  exact hn.le

lemma area_lim (D A K : ℝ) (m:ℕ) :
    ∀ᶠ N : ℝ in atTop,
      let C := cutoffC m (K*N^2)
      D*N/N^2*8 + D*ek N*(C*(1+N)) + A*ek N*C ≤ 1/2 := by
  let C := fun N:ℝ => cutoffC m (K*N^2)
  have h₁ := (ekrapid.product (poly_cut m K)).tail_limit
  have h₂ := (ekrapid.product ((poly_cut m K).mul
    ((PolyBound.const (1:ℝ)).add PolyBound.id))).tail_limit
  let f := fun N:ℝ=> D*N⁻¹*8 + D*(ek N*(C N*(1+N))) + A*(ek N*C N)
  have he : Tendsto f atTop (𝓝 0) := by
    have hh := ((((tendsto_inv_atTop_zero (𝕜:=ℝ)).const_mul D).mul_const 8).add
      (h₂.const_mul D)).add (h₁.const_mul A)
    simpa [C,f] using hh
  filter_upwards [he.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), eventually_gt_atTop (0:ℝ)]
    with N hn hp
  change f N < 1/2 at hn
  intro c
  rw [show D*N/N^2=D*N⁻¹ from by field_simp,mul_assoc D (ek N),mul_assoc A (ek N)]
  exact hn.le

theorem inward (q₀:ProjField m) :
    ∃ R≥(2:ℝ), ∀ hr:0<R, ∀ x:Param m R, ∀ v:Rn m, ‖v‖=1 →
      let A := (x.instanceQ hr q₀).avgA
      (op x.B v= R⁻¹ • v → 0 ≤ ⟪v,op A v⟫) ∧
      (op x.B v= R • v → ⟪v,op A v⟫ ≤ 0) := by
  obtain ⟨K,hK⟩ := q₀.Field_isBound
  obtain ⟨D,hD,h₁⟩ := angle_est q₀
  obtain ⟨B,hB,h₂⟩ := dir_tail_area m
  obtain ⟨W,hW,h₃⟩ := small_minus_bound m hD
  let L := 2*W
  have h : ∀ᶠ N:ℝ in atTop,
      4 ≤ N ∧ D*(N/N^2*(4/a (-1))+ek N) ≤ 1/2 ∧
      D*(N/N^2*a L+ek N) ≤ 1/2 ∧
      (let C := cutoffC m (K*N^2)
       D*N/N^2*8 + D*ek N*(C*(1+N))+B*ek N*C ≤ 1/2) :=
    (eventually_ge_atTop _).and ((inv_lim D _).and ((inv_lim D _).and (area_lim D B K m)))
  obtain ⟨N,hN,ha,hb,hc⟩ := h.exists
  let R := N^2
  have hr₀ : 2≤R := by dsimp [R]; nlinarith
  have hn : 1≤N := by linarith
  use R, hr₀
  intro hr x v hv A
  let q := x.instanceQ hr q₀
  have hh := h₁ R hr x v hv
  have hw : ⟪v,op A v⟫=q.plus v-q.minus v := q.pn _ hv
  rw [hw]
  constructor
  · intro he
    have hq := h₃ q v hv R hr₀ (fun z j hj=>(hh z j hj).1 he)
    have ht : 0≤L := mul_nonneg (by norm_num) hW
    have hp := small_plus_lower q v hv hD hr hn ht (fun z=>(hh z N hn).1 he) hb
    unfold L at hp
    linarith
  intro he
  have hy := large_minus_lower hr x q₀ v hv hD hn ha (fun z=>(hh z N hn).2 he)
  let C := cutoffC m (K*N^2)
  have ht := x.Bound_instance hr₀ hr hK
  let l := C*(1+N)
  have he' : 1≤C := (positive_exact m ht.one_le).1
  have hl : 0 ≤ l := by unfold l; nlinarith
  have hz := large_core_upper hr x q₀ v hv hD hn hl (fun z=>(hh z N hn).2 he)
  have hf : q.plus v ≤ 1/2 := calc
    _ = _ := plus_split _ _ hv hl
    _ ≤ _ := add_le_add hz (h₂ _ q ht v hv N hN)
    _ ≤ _ := hc
  change 1/2 ≤ q.minus v at hy
  linarith
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Update
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 covariance equation from scalar inequalities of §01. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler

variable {m : ℕ}

lemma jordan_sym {A B : Mat m} (ha:A.IsHermitian) (hb:B.IsHermitian) :
    (jprod A B).IsHermitian := by
  apply Matrix.IsHermitian.smul _ (show IsSelfAdjoint (1/2:ℝ) from rfl)
  change star (A*B+B*A) = _
  rw [star_add,star_mul,star_mul, (show star A=A from ha),(show star B=B from hb),add_comm]
lemma sqPSD {A : Mat m} (ha:A.IsHermitian) : 0 ≤ A*A := by
  change IsSelfAdjoint A at ha
  conv_lhs => skip
  simpa only [ha.star_eq] using star_mul_self_nonneg A
lemma upd_sym {C K T : Mat m} (hc:C.IsHermitian) (hk:K.IsHermitian) (ht:T.IsHermitian) :
    (updEq C K T).IsHermitian := by
  refine (((Matrix.nonneg_iff_posSemidef.mp (sqPSD ht)).1.smul (show IsSelfAdjoint lam from rfl)).add
    (jordan_sym hc ht)).add hk
lemma upd_form {C K T:Mat m} (ht:T.IsHermitian) {a:ℝ} {v:Rn m}
    (hv:op T v = a • v) :
    ⟪v,op (updEq C K T) v⟫ = ⟪v,op (scalar m (lam*a^2)+a• C + K) v⟫ := by
  have hh := op_iff_hermitian.mp ht v (op C v)
  simp only [updEq,jprod,scalar,_root_.map_add,_root_.map_smul,_root_.map_mul,_root_.map_one,
    _root_.add_apply,_root_.smul_apply,mul_apply_eq_comp,
    inner_add_right,real_inner_smul_right]
  change _ = lam*a^2*⟪v,v⟫+_+_
  rw [← hh,hv]
  simp only [_root_.map_smul, hv,real_inner_smul_left,real_inner_smul_right]
  ring

lemma gap_from_cov {C K T : Mat m} (hC:C.IsHermitian)
    (ht:T∈specBox m tmin tmax)
    (hc:C ≤ scalar m cupper)
    (hh: 0 ≤ scalar m (-(ell0^2)-mstar^2)+(2*ell0)•C+ (-(4*lam))•K)
    (he : updEq C K T = 0) : scalar m mstar ≤ updGap C T := by
  let n := 2*lam
  have hn : 0≤n := by dsimp [n,lam]; norm_num
  have hp : 0 ≤ updGap C T := by
    have h₁ := add_le_add hc (smul_le_smul_of_nonneg_left ht.2.2 hn)
    have h₂ : scalar m cupper+n•scalar m tmax ≤ 0 := by
      simp only [scalar,smul_smul,← add_smul]
      have hi := scalar_le' (m:=m) (cupper+n*tmax) 0 (by dsimp [cupper,tmax,n,lam]; norm_num)
      simpa [scalar] using hi
    change 0 ≤ -C-n•T
    have hi := h₁.trans h₂
    rw [sub_nonneg]
    exact (le_neg_iff_add_nonpos_right).mpr (by simpa only [add_comm] using hi)
  apply sq_order_cancel (scalar_psd (show 0 ≤ mstar by dsimp [mstar]; norm_num)) hp
  rw [← sub_nonneg]
  let d := scalar m ell0
  have hu : 0 ≤ (C-d)*(C-d) := sqPSD (hC.sub (scalar_sym ..))
  apply (add_nonneg hu hh).trans_eq
  have Hk : K = -(lam • (T*T) + jprod C T) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact he)
  rw [Hk]
  dsimp only [updGap,jprod,d]
  simp only [sub_mul,mul_sub,neg_mul,mul_neg,smul_mul_assoc,mul_smul_comm,
    scalar, one_mul,mul_one,smul_add,smul_neg, smul_smul]
  module

namespace ProjField
variable [NeZero m]

theorem intL (q : ProjField m) {f : ℝ→ℝ} (hm : Continuous f) (hf : PolyBound f) :
    Integrable (fun x=>cfc f (q.Lmat x)) (normal m) := by
  have hc : Continuous fun x=>cfc f (q.Lmat x) :=
    (cfc_continuous_herm f hm).comp_continuous q.L_cont q.L_sym
  obtain ⟨C,n,hc',hf⟩ := hf
  let g := fun x => C*(1+‖q.Lmat x‖)^n
  have h : PolyBound g :=
    (PolyBound.const _).mul (((PolyBound.const 1).add q.L_poly.norm).pow _)
  apply PolyBound.gaussian_integrable _ hc.aestronglyMeasurable
  refine h.mono fun x => ?_
  apply le_trans (spectrum_poly_le _ hc' hf (q.L_sym _))
  change g x ≤ ‖g x‖; exact le_abs_self _

lemma expL_sym (q:ProjField m) {f} (hm : Continuous f) (hf : PolyBound f) :
    (expL f q).IsHermitian :=
  hermitian_integral (q.intL hm hf) (ae_of_all _ fun _ => cfc_herm _ _)

lemma expL_affine_pos (q:ProjField m) {C K : ℝ→ℝ} (hc : Continuous C) (hk : Continuous K)
    (hh : PolyBound C) (hh' : PolyBound K) {x y z : ℝ}
    (he : ∀ t, 0 ≤ x + y*C t+z*K t) :
    0 ≤ scalar m x + y•expL C q + z•expL K q := by
  let f (t:Rn m) := scalar m x + y•cfc C (q.Lmat t)+ z•cfc K (q.Lmat t)
  have ic := (q.intL hc hh).smul y
  have ik := (q.intL hk hh').smul z
  have hp (t:Rn m) : 0 ≤ f t := by
    let A := q.Lmat t
    have hi : IsSelfAdjoint A := q.L_sym t
    have hl := cfc_nonneg (f := (fun t:ℝ=>x+y*C t+z*K t)) (a := A) (fun t _=>he t)
    have HE := cfc_add A (fun t => x+y*C t) (fun t=>z*K t)
      (show ContinuousOn _ (spectrum ℝ A) from (continuous_const.add (continuous_const.mul hc)).continuousOn)
      ((continuous_const.mul hk).continuousOn)
    conv at hl =>
      rhs
      rw [show cfc (fun t=>x+y*C t+z*K t) A = _ from HE, cfc_const_add x (fun t=>y*C t) A ((continuous_const.mul hc).continuousOn) hi, cfc_const_mul y C A hc.continuousOn,cfc_const_mul z K A hk.continuousOn, ← scalar_eq]
    exact hl
  have heq : ∫ t, f t ∂normal m = scalar m x + y•expL C q+z•expL K q := by
    unfold f expL
    rw [integral_add, integral_add, integral_smul,integral_smul]
    · simp; exact integral_smul z _
    all_goals first | exact integrable_const _ | exact ic | exact ik |
      exact (integrable_const _).add ic
  rw [← heq]
  apply Matrix.PosSemidef.nonneg
  exact psd_integral (((integrable_const _).add ic).add ik) (ae_of_all _ fun t=>(hp t).posSemidef)

lemma expL_bounds (q:ProjField m) {C K} (h:UpdatesOK C K) :
    expL C q ≤ scalar m cupper ∧
    0 ≤ scalar m (-(ell0^2)-mstar^2)+(2*ell0)•expL C q + (-(4*lam))•expL K q ∧
    0 ≤ scalar m (lam*tmin^2) + tmin • expL C q+ expL K q ∧
    scalar m (lam*tmax^2) + tmax • expL C q+ expL K q ≤ 0 := by
  have he (x y z) (hi : ∀ t, 0≤ x+y*C t+z*K t) := q.expL_affine_pos h.Cc h.Kc h.Cp h.Kp hi
  refine ⟨?_,he _ _ _ (fun t => by linarith [h.tan t]), ?_,?_⟩
  · have hb := he cupper (-1) 0 (fun t=>by linarith [h.C_hi t])
    simpa [sub_eq_add_neg,← sub_nonneg] using hb
  · have hb := he (lam*tmin^2) tmin 1 (fun t=>by linarith [h.lo t])
    simpa only [one_smul] using hb
  · have hb := he (-(lam*tmax^2)) (-tmax) (-1) (fun t=>by linarith [h.hi t])
    rw [← neg_nonneg]
    simpa only [scalar,neg_smul,one_smul,neg_add] using hb
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Normalize
attribute [-instance] _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Simultaneous normalization on two spectral boxes using scalar endpoint
and gap inequalities. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open ProjField
variable {m : ℕ} [NeZero m]
namespace Param
variable {R : ℝ}
lemma cont_ll (q:ProjField m) (hr:2≤R) (hr':0<R) :
    Continuous (fun p:Param m R => ∑ i, (coord i).smulRight ((p.instanceQ hr' q).M i)) := by
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℝ _ (Mat m) (coord i)).continuous.comp (cont_M q hr hr' i))

lemma cont_expL (q:ProjField m) (hr:2≤R) (hr':0<R) (f:ℝ→ℝ)
    (hf:Continuous f) (hp:PolyBound f) :
    Continuous (fun p:Param m R=> (p.instanceQ hr' q).expL f) := by
  let l := fun p:Param m R => ∑ i, (coord i).smulRight ((p.instanceQ hr' q).M i)
  have he (p:Param m R) (x) : l p x = (p.instanceQ hr' q).Lmat x := by simp [l,Lmat]
  apply continuous_iff_continuousAt.mpr
  intro p
  let b := ‖l p‖+1
  have hh : ∀ᶠ w in 𝓝 p, ‖l w‖≤b := by
    have hu : Continuous l := cont_ll q hr hr'
    have hb : Continuous (fun z : Rn m →L[ℝ] Mat m => ‖z‖) := continuous_norm (E:=Rn m →L[ℝ] Mat m)
    have h : ContinuousAt (fun w=>‖l w‖) p := (hb.comp hu).continuousAt
    filter_upwards [h.eventually (gt_mem_nhds (show ‖l p‖<b by unfold b; linarith))] with w hw
    exact le_of_lt hw
  obtain ⟨C,n,hC,h⟩ := hp
  let g := fun x:Rn m => C*(1+b*‖x‖)^n
  have hg : PolyBound g :=
    (PolyBound.const _).mul (((PolyBound.const _).add
      ((PolyBound.const _).mul (PolyBound.id.norm))).pow _)
  have hi := hg.gaussian_integrable (μ:=normal m) ((by unfold g; fun_prop : Continuous g).aestronglyMeasurable)
  have hc (y:Param m R) : Continuous fun x:Rn m=>cfc f ((y.instanceQ hr' q).Lmat x) :=
    (cfc_continuous_herm f hf).comp_continuous (y.instanceQ hr' q).L_cont (y.instanceQ hr' q).L_sym
  unfold expL
  apply continuousAt_of_dominated
    (Eventually.of_forall fun y => (hc y).aestronglyMeasurable) _ hi
  · apply ae_of_all
    intro x
    exact ((cfc_continuous_herm f hf).comp_continuous (cont_L q hr hr' x)
      (fun y=> (y.instanceQ hr' q).L_sym _)).continuousAt
  filter_upwards [hh] with y hy
  apply ae_of_all
  intro x
  apply le_trans (spectrum_poly_le f hC h ((y.instanceQ hr' q).L_sym _))
  unfold g
  rw [← he]
  have hi := ((l y).le_opNorm x).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  gcongr
end Param

lemma param_fixed (m:ℕ) (R:ℝ) (hr:2≤R) (f : Param m R → Param m R) (hf : Continuous f) :
    ∃ x:Param m R, f x=x := by
  classical
  let A := params m R
  let g := fun x : Mat m × Mat m => if h:x∈A then (f ⟨x,h⟩).val else x
  have ha : MapsTo g A A := by intro x h; simp only [g,dite_eq_left h]; apply Subtype.property
  have hc : ContinuousOn g A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : A.domRestrict g = Subtype.val ∘ f := by funext x; simp [Set.domRestrict,g,A,x.property]
    rw [he]; exact continuous_subtype_val.comp hf
  have hh : R⁻¹≤R := by
    have h : 0<R := by linarith
    rw [← one_div, div_le_iff₀ h]; nlinarith
  have hl : tmin ≤ tmax := by norm_num [tmin,tmax]
  have ht : A.Nonempty := (specBox_nonempty m _ _ hh).prod (specBox_nonempty m _ _ hl)
  obtain ⟨x,hx,h⟩ := compact_fixedpoint A ((specBox_compact ..).prod (specBox_compact ..))
    ((specBox_convex ..).prod (specBox_convex ..)) ht g hc ha
  exact ⟨⟨x,hx⟩,Subtype.ext (by simpa only [g,dite_eq_left hx] using h)⟩

/-- For a field q0 supplying the original cone with a normalized pair,
a positive coordinate transform and companion field exist. -/
theorem simultaneous (q:ProjField m) {c k:ℝ→ℝ}
    (hck:UpdatesOK c k) :
    ∃ R≥(2:ℝ), ∃ hr : 0<R, ∃ x:Param m R,
      let q' := x.instanceQ hr q
      q'.avgA=0 ∧ updEq (q'.expL c) (q'.expL k) x.T = 0 ∧
        scalar m mstar ≤ updGap (q'.expL c) x.T := by
  obtain ⟨R,hr,h⟩ := inward q
  have H : 0 < R := by linarith
  let Q := fun x:Param m R => x.instanceQ H q
  let E := fun x:Param m R => (Q x).avgA
  let C := fun x:Param m R => (Q x).expL c
  let K := fun x:Param m R => (Q x).expL k
  let u := fun x:Param m R => updEq (C x) (K x) x.T
  have hu (x:Param m R) : (u x).IsHermitian :=
    upd_sym ((Q x).expL_sym hck.Cc hck.Cp) ((Q x).expL_sym hck.Kc hck.Kp)
      x.in_box.2.1
  have ht (x:Param m R) : (x.T+u x).IsHermitian := x.in_box.2.1.add (hu x)
  have he (x:Param m R) : (x.B+E x).IsHermitian := x.in_box.1.1.add ((Q x).avgA_sym)
  let g := fun x:Param m R =>
    (clip R⁻¹ R (x.B+E x), clip tmin tmax (x.T+u x))
  have ha : R⁻¹≤R := by rw [← one_div, div_le_iff₀ H]; nlinarith
  have hb : tmin≤tmax := by norm_num [tmin,tmax]
  have hg (x:Param m R) : g x∈params m R :=
    ⟨clip_mem _ _ ha (he x),clip_mem _ _ hb (ht x)⟩
  let f := fun x:Param m R => (⟨g x,hg x⟩:Param m R)
  have hc : Continuous f := by
    have hC : Continuous C := Param.cont_expL q hr H _ hck.Cc hck.Cp
    have hK : Continuous K := Param.cont_expL q hr H _ hck.Kc hck.Kp
    have hT : Continuous (@Param.T m R) := Param.cont_T
    have hl : Continuous u := by unfold u updEq jprod; fun_prop
    have hh : Continuous g :=
      ((cont_clip R⁻¹ R).comp_continuous (Param.cont_B.add (Param.cont_avgA q hr H)) he).prodMk
        ((cont_clip tmin tmax).comp_continuous (hT.add hl) ht)
    exact hh.subtype_mk _
  obtain ⟨p,hp⟩ := param_fixed m R hr f hc
  have hx := h H p
  have hz := clip_eq ha (congrArg Param.B hp) (he p)
    (fun v hv => (hx v hv).1) (fun v hv => (hx v hv).2)
  refine ⟨R,hr,H,p,hz,?_⟩
  have hi := (Q p).expL_bounds hck
  have hi' : u p=0 := by
    apply clip_eq hb (congrArg Param.T hp) (ht p)
    · intro v hv ha
      rw [show u p = _ from (rfl : u p = updEq _ _ _),upd_form p.in_box.2.1 ha]
      exact (op_posSemidef_iff.mp hi.2.2.1.posSemidef).2 v
    · intro v hv ha
      rw [show u p = _ from (rfl : u p = updEq _ _ _),upd_form p.in_box.2.1 ha]
      have HE := hi.2.2.2
      rw [← neg_nonneg] at HE
      have hf := (op_posSemidef_iff.mp HE.posSemidef).2 v
      rw [_root_.map_neg,_root_.neg_apply,inner_neg_right] at hf
      exact neg_nonneg.mp hf
  exact ⟨hi',gap_from_cov ((Q p).expL_sym hck.Cc hck.Cp) p.in_box.2 hi.1 hi.2.1 hi'⟩

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Orthant
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Full-dimensional simplicial cones, coordinates and Laplace integrals. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp Module
open scoped RealInnerProductSpace ENNReal Topology
namespace GeneralMahler
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ}

section Orthant

variable (b : Basis (Fin m) ℝ E)

theorem basis_mem_orthant (i) : b i ∈ orthant b := by
  rw [mem_orthant]
  intro j
  simp
  split <;> norm_num

lemma mem_interior_orthant {p : E} :
    p ∈ interior (orthant b:Set E) ↔ ∀ i, 0 < b.equivFun p i := by
  constructor
  · intro hp i
    by_contra hn
    push Not at hn
    let f : ℝ → E := fun r => p - r • b i
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hv : ∀ᶠ r in 𝓝[>] (0:ℝ), f r ∈ (orthant b:Set E) :=
      nhdsWithin_le_nhds ((hf.tendsto 0) (by simpa [f] using mem_interior_iff_mem_nhds.mp hp))
    obtain ⟨r,hr,hm⟩ := hv.and (show ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r from self_mem_nhdsWithin)
      |>.exists
    have hh := (mem_orthant b).mp hr i
    simp [f] at hh hn
    linarith
  · intro h
    apply mem_interior_iff_mem_nhds.mpr
    change ∀ᶠ x in 𝓝 p, x ∈ (orthant b : Set E)
    have he : ∀ i, ∀ᶠ x in 𝓝 p, 0 < b.equivFun x i :=
      fun i => ((continuous_apply i).comp b.equivFun.toContinuousLinearEquiv.continuous).tendsto p
        (Ioi_mem_nhds (h i))
    filter_upwards [eventually_all.mpr he] with x hx
    exact (mem_orthant b).mpr fun i => (hx i).le

lemma pushCone_rebase (a : Basis (Fin m) ℝ E) :
    pushCone (rebase b a) (orthant b) = orthant a := by
  ext x
  rw [mem_pushCone, mem_orthant, mem_orthant]
  change (∀ i, 0 ≤ b.equivFun (b.equivFun.symm _) i) ↔ _
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional ℝ E] in
lemma rebase_apply_basis (a : Basis (Fin m) ℝ E) (i : Fin m) :
    rebase b a (b i) = a i := by
  apply a.equivFun.injective
  change a.equivFun (a.equivFun.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  ext j; simp

end Orthant

variable (b : OrthonormalBasis (Fin m) ℝ E)
local notation "C" => orthant b.toBasis

omit [FiniteDimensional ℝ E] in
lemma eq_basis_ip (x : E) (i : Fin m) :
    b.toBasis.equivFun x i = ⟪b i, x⟫ := by
  simpa using b.repr_apply_apply x i

omit [FiniteDimensional ℝ E] in
lemma ip_onb (x y : E) :
    ⟪x,y⟫ = ∑ i, b.toBasis.equivFun x i * b.toBasis.equivFun y i := by
  have he : (∑ i, b.toBasis.equivFun x i • b i) = x := by
    simpa only [Basis.equivFun_apply, OrthonormalBasis.coe_toBasis] using b.toBasis.sum_repr x
  conv_lhs => rw [← he, sum_inner]
  simp_rw [real_inner_smul_left, eq_basis_ip]

lemma orthant_self_dual : posDual C = C := by
  ext x; rw [mem_posDual,mem_orthant]
  constructor
  · intro h i
    rw [eq_basis_ip]
    exact h (basis_mem_orthant _ _)
  · intro h y hy
    rw [ip_onb b]
    apply Finset.sum_nonneg ; intro i hi
    exact mul_nonneg ((mem_orthant _).mp hy i) (h i)

-- Work with canonical Euclidean volumes.
variable [MeasurableSpace E] [BorelSpace E]

theorem chi_orthant {V : E} (h : V ∈ interior (C : Set E)) :
    chi C V = ∏ i, (b.toBasis.equivFun V i)⁻¹ := by
  classical
  let a := b.toBasis.equivFun
  have ha (i : Fin m) : 0 < a V i := (mem_interior_orthant _).mp h i
  let T : E ≃ᵐ (Fin m → ℝ) :=
    b.measurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm
  have hT : MeasurePreserving T :=
    MeasurePreserving.trans b.measurePreserving_measurableEquiv
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _)
  have hta (x : E) : T x = a x := by
    ext i
    change b.repr x i = _
    simp [a]
  let g (i : Fin m) : ℝ → ℝ :=
    (Ici 0).indicator fun t => exp (-(a V i) * t)
  let p (v : Fin m → ℝ) := ∏ i, g i (v i)
  have hip (i : Fin m) : (∫ t : ℝ, g i t) = (a V i)⁻¹ := by
    rw [show (∫ t : ℝ, g i t) = ∫ t : ℝ in Ici 0, exp (-(a V i) * t) from
      integral_indicator measurableSet_Ici,
      integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_neg_of_pos (ha i))]
    ring_nf
    simp
  unfold chi
  rw [← integral_indicator (orthant b.toBasis).isClosed.measurableSet]
  have heq (x : E) :
      (C : Set E).indicator (fun x => exp (-⟪V,x⟫)) x = p (T x) := by
    rw [hta]
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx, ip_onb b, ← Finset.sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_congr rfl; intro i hi
      have hn : 0 ≤ a x i := (mem_orthant _).mp hx i
      change exp (-(a V i * a x i)) = g i (a x i)
      rw [show g i (a x i) = _ from indicator_of_mem (mem_Ici.mpr hn) _]
      rw [neg_mul]
    · rw [indicator_of_notMem hx]
      rw [mem_orthant] at hx
      push Not at hx
      obtain ⟨i,hi⟩ := hx
      have hn : a x i ∉ Ici 0 := hi.not_ge
      exact Eq.symm (Finset.prod_eq_zero (Finset.mem_univ i)
        (indicator_of_notMem hn _))
  simp_rw [heq]
  rw [hT.integral_comp']
  exact (integral_fin_nat_prod_volume_eq_prod ..).trans (Finset.prod_congr rfl fun i _ => hip i)
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Santalo
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
## Santaló center

Rather than the spherical integral, we use equivalently
the cone Laplace integral and its divergence at the dual boundary. This way
of proving the center claims includes dimension 1 without a separate case.
-/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped RealInnerProductSpace ENNReal
namespace GeneralMahler
variable {n : ℕ}
namespace Body

theorem santalo_spec (K : Body n) :
    santalo K ∈ interior (K : Set (Rn n)) ∧
      IsMinOn K.polarVol (interior (K:Set (Rn n))) (santalo K) :=
  (santalo_exists K).exists.choose_spec

theorem product_min {K : Body n} {z : Rn n} (hz : z ∈ interior (K : Set (Rn n))) :
    K.P ≤ K.productAt z :=
  mul_le_mul_of_nonneg_left ((K.santalo_spec).2 hz) K.vol_pos.le

theorem product_inf (K : Body n) :
    K.P = sInf (K.productAt '' interior (K : Set (Rn n))) := by
  have hm : K.P ∈ K.productAt '' interior (K : Set (Rn n)) :=
    ⟨_,K.santalo_spec.1,rfl⟩
  have hl : K.P ∈ lowerBounds (K.productAt '' interior (K : Set (Rn n))) := by
    rintro x ⟨z,hz,rfl⟩
    exact product_min hz
  exact le_antisymm (le_csInf ⟨_,hm⟩ hl) (csInf_le ⟨_,hl⟩ hm)

end Body
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_SimplexCone
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! §§01,06: Full-dimensional simplicial cones and simplex sections. -/
noncomputable section
open Set Module
open scoped RealInnerProductSpace ENNReal Topology
namespace GeneralMahler
variable {n : ℕ}

theorem lift_finrank (n : ℕ) : finrank ℝ (LiftSpace n) = n+1 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × Rn n)).finrank_eq]
  simp [Rn, add_comm]

lemma independence_lift {ι : Type*} (v : ι → Rn n) :
    AffineIndependent ℝ v ↔ LinearIndependent ℝ (fun i => pair 1 (v i)) := by
  rw [linearIndependent_iff']
  constructor
  · intro h s w hw
    have h₁ := congrArg hgtL hw
    have h₂ := congrArg horizL hw
    simp only [map_sum,map_smul, hgtL_apply,pair_hgt,smul_eq_mul,mul_one,map_zero] at h₁
    simp only [map_sum,map_smul,horizL_apply,pair_horiz,map_zero] at h₂
    refine h s w h₁ ?_
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w v h₁ (0 : Rn n),
      Finset.weightedVSubOfPoint_apply]
    simpa using h₂
  · intro h s w hw he
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w v hw (0 : Rn n),
      Finset.weightedVSubOfPoint_apply] at he
    simp only [vsub_eq_sub,sub_zero] at he
    apply h
    let p := ∑ i ∈ s, w i • pair 1 (v i)
    change p = 0
    have h₁ : hgtL p = 0 := by simp only [p,map_sum,map_smul,hgtL_apply,pair_hgt,smul_eq_mul,mul_one,hw]
    have h₂ : horizL p = 0 := by simpa only [p,map_sum,map_smul,horizL_apply,pair_horiz] using he
    change hgt p = 0 at h₁
    change horiz p = 0 at h₂
    rw [← hgt_horiz_pair p,h₁,h₂,pair_zero]

theorem sum_coords (b : Basis (Fin (n+1)) ℝ (LiftSpace n)) (x : LiftSpace n) :
    ∑ i, b.equivFun x i • b i = x := by
  simpa only [Basis.equivFun_apply] using b.sum_repr x

namespace Body

lemma exists_basis_of_simplex {K : Body n} (hK : IsSimplex (K:Set (Rn n))) :
    ∃ b : Basis (Fin (n+1)) ℝ (LiftSpace n),
      (∀ i, hgt (b i) = 1) ∧ K.cone = orthant b := by
  rcases hK with ⟨v,hi,hv⟩
  have hvK (i) : v i ∈ K := by
    change v i ∈ (K:Set (Rn n))
    exact hv ▸ subset_convexHull ℝ _ (mem_range_self i)
  let vs := fun i => pair 1 (v i)
  have hd := (independence_lift v).mp hi
  have hf : Fintype.card (Fin (n+1)) = finrank ℝ (LiftSpace n) := by simp [lift_finrank]
  let b := basisOfLinearIndependentOfCardEqFinrank' vs hd hf
  have hbi (i) : b i = vs i := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' ..) i
  refine ⟨b, fun i => by rw [hbi]; rfl,?_⟩
  let S := {x : Rn n | pair 1 x ∈ orthant b}
  have hKs : (K : Set (Rn n)) ⊆ S := by
    rw [hv]
    apply convexHull_min
    · rintro x ⟨i,rfl⟩
      change vs i ∈ orthant b
      rw [← hbi]
      exact basis_mem_orthant _ _
    · intro x hx y hy a a' ha ha' haa
      change pair 1 (a • x + a' • y) ∈ orthant b
      have he : a • pair 1 x + a' • pair 1 y = pair 1 (a • x + a' • y) := calc
        _ = pair (a*1+a'*1) (a • x + a' • y) := rfl
        _ = _ := by rw [mul_one,mul_one,haa]
      rw [← he]; apply (orthant b).convex _ _ ha ha' haa <;> assumption
  ext x
  constructor
  · rw [← hgt_horiz_pair x]
    intro hx
    obtain ⟨hu,y,hy,he⟩ := (Body.pair_mem_cone ..).mp hx
    have hi : pair 1 y ∈ orthant b := hKs hy
    have hh := (orthant b).smul_mem hi hu
    rw [he]; simpa only [smul_pair,mul_one] using hh
  · intro h
    have H : (∑ i, b.equivFun x i • b i) ∈ K.cone := by
      apply K.cone.sum_mem
      intro i _
      apply K.cone.smul_mem _ ((mem_orthant _).mp h i)
      rw [hbi]
      have he := hvK i
      simp [vs,he]
    rwa [sum_coords] at H

theorem simplex_of_linearOrthant {K : Body n} (h : IsLinearOrthant (n+1) K.cone) :
    IsSimplex (K:Set (Rn n)) := by
  obtain ⟨b,hb⟩ := h
  let a := fun i => hgt (b i)
  have hbi (i) : 0 ≤ a i ∧ ∃ x ∈ K, horiz (b i) = a i • x := (hb.symm ▸ basis_mem_orthant b i :
    b i ∈ K.cone)
  choose g hg hge using fun i => (hbi i).2
  have hv (i) : b i = pair (a i) (a i • g i) := by rw [← hge]; exact (hgt_horiz_pair _).symm
  have ha (i) : 0 < a i := lt_of_le_of_ne (hbi i).1 (by
    intro he; apply b.ne_zero i
    rw [hv,← he,zero_smul,pair_zero])
  have he (i) : (a i)⁻¹ • b i = pair 1 (g i) := calc
    _ = (a i)⁻¹ • pair (a i) (a i • g i) := congrArg _ (hv _)
    _ = _ := by simp [smul_pair, (ha i).ne']
  have hd : AffineIndependent ℝ g := by
    rw [independence_lift]
    let u : Fin (n+1) → ℝˣ := fun i => Units.mk0 _ (inv_ne_zero (ha i).ne')
    simp_rw [← he]
    exact b.linearIndependent.units_smul u
  refine ⟨g,hd, le_antisymm ?_ (convexHull_min (range_subset_iff.mpr hg) K.convex)⟩
  intro x hx
  let q := pair 1 x
  have hh : q ∈ orthant b := by
    rw [← hb, pair_mem_cone]
    exact ⟨zero_le_one,x,hx,(one_smul _ x).symm⟩
  let c : Fin (n+1) → ℝ := fun i => b.equivFun q i * a i
  have hc (i) : 0 ≤ c i := mul_nonneg ((mem_orthant b).mp hh i) (ha i).le
  have hf := sum_coords b q
  have H₁ := congrArg hgtL hf
  have H₂ := congrArg horizL hf
  simp only [map_sum,map_smul,hgtL_apply,q,pair_hgt,smul_eq_mul] at H₁
  simp only [map_sum,map_smul,horizL_apply,hge,smul_smul,q,pair_horiz] at H₂
  exact mem_convexHull_of_exists_fintype c g (fun i => hc i)
    H₁ (fun i => mem_range_self i) H₂

end Body
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_SimplexVolume
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Simplex direction of equality, solved by sending the cone to an orthant. -/
noncomputable section
open Filter Set MeasureTheory Real Module
open scoped RealInnerProductSpace ENNReal
namespace GeneralMahler
namespace Body
variable {n : ℕ}

theorem simplex_attains {K : Body n} (hK : IsSimplex (K:Set (Rn n))) :
    K.P = ((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 := by
  obtain ⟨b,hbt,hb⟩ := exists_basis_of_simplex hK
  let m : ℝ := (n:ℝ)+1
  have hm : 0 < m := by dsimp [m]; positivity
  let a : OrthonormalBasis (Fin (n+1)) ℝ (LiftSpace n) :=
    (stdOrthonormalBasis ℝ _).reindex (finCongr (lift_finrank n))
  let B := rebase b a.toBasis
  let V := pair 1 (0:Rn n)
  let D := orthant a.toBasis
  let ef := a.toBasis.equivFun
  let c := fun x => ef (B x)
  have hcoord (x : LiftSpace n) : c x = b.equivFun x :=
    a.toBasis.equivFun.apply_symm_apply _
  have he : pushCone B K.cone = D := by
    rw [hb]
    exact pushCone_rebase b _
  have hv : ∀ i, ef (contra B V) i = 1 := by
    intro i
    dsimp only [ef]
    rw [eq_basis_ip]
    have ha : (a i) = B (b i) := by
      simpa only [OrthonormalBasis.coe_toBasis] using (rebase_apply_basis b a.toBasis i).symm
    rw [ha, pair_contra]
    rw [← hgt_horiz_pair (b i)]
    change ⟪pair _ _, pair _ _⟫ = _
    rw [pair_inner,inner_zero_right,add_zero,hbt,one_mul]
  have hiv : contra B V ∈ interior (D : Set (LiftSpace n)) :=
    (mem_interior_orthant a.toBasis).mpr fun i => by rw [hv]; norm_num
  let M := fun z : Rn n => pair m (m • z)
  have hsum (x : LiftSpace n) : ∑ i, c x i = hgt x := by
    have H := congrArg hgtL (sum_coords b x)
    simp only [_root_.map_sum,map_smul, hgtL_apply, smul_eq_mul,hbt, mul_one] at H
    rw [hcoord]; exact H
  let k : ℝ := (m^ (n+1)) / (n.factorial:ℝ)^2
  have hk : 0 < k := by dsimp [k]; positivity
  have hn (z : Rn n) (hz : z ∈ interior (K:Set (Rn n))) :
      (∀ i, 0 < c (M z) i) ∧ K.productAt z = k * ∏ i, (c (M z) i)⁻¹ := by
    have hh : B (M z) ∈ interior (D : Set (LiftSpace n)) := by
      rw [← he,apply_mem_interior_pushCone]
      exact (K.pair_mem_interior_cone_iff m hm _).mpr hz
    refine ⟨(mem_interior_orthant a.toBasis).mp hh,?_⟩
    have He := chi_transform B K.cone (M z) V
    rw [he, orthant_self_dual a, chi_orthant a hiv, chi_orthant a hh] at He
    change (∏ i, (ef _ i)⁻¹) * (∏ i, (ef _ i)⁻¹) = _ at He
    simp_rw [hv] at He
    have H : (m⁻¹)^(n+1)*(n.factorial:ℝ)^2*K.productAt z = ∏ i, (c (M z) i)⁻¹ := by
      change _*_*((volume _).toReal*(volume _).toReal) = _
      rw [← cone_volume K z hz m hm]
      change chi K.cone V * chi (posDual K.cone) (M z) = _
      rw [← He]
      simp only [inv_one, Finset.prod_const_one, one_mul]; rfl
    rw [← H]; dsimp only [k]
    rw [inv_pow]
    field_simp
  obtain ⟨z,hz,heq⟩ :
      ∃ z ∈ interior (K:Set (Rn n)), K.productAt z = k := by
    let p := b.equivFun.symm (fun _ => 1)
    have hp : c p = fun _ => 1 := (hcoord p).trans (b.equivFun.apply_symm_apply _)
    have hgtp := (hsum p).symm
    rw [hp] at hgtp
    have hg : hgt p = m := by simpa [m] using hgtp
    have hin : p ∈ interior (K.cone : Set (LiftSpace n)) := by
      rw [hb,mem_interior_orthant, ← hcoord,hp]
      intro i; norm_num
    let x := m⁻¹ • horiz p
    have he : M x = p := by
      dsimp only [M,x]
      rw [smul_smul,mul_inv_cancel₀ hm.ne',one_smul, ← hg,hgt_horiz_pair]
    have hx : x ∈ interior (K:Set (Rn n)) :=
      (K.pair_mem_interior_cone_iff m hm x).mp ((he.symm ▸ hin) : M x ∈ _)
    exact ⟨x,hx,by rw [(hn x hx).2,he,hp]; simp⟩
  change K.P = k
  apply le_antisymm ((product_min hz).trans_eq heq)
  let w := K.santalo
  change k ≤ K.productAt w
  obtain ⟨hw',hh⟩ := hn w K.santalo_spec.1
  set d := c (M w) with hdef
  have hd (i) : 0 < d i := hw' i
  have hl : ∑ i, Real.log (d i) ≤ 0 := calc
    _ ≤ ∑ i, (d i - 1) := Finset.sum_le_sum (fun i _ => log_le_sub_one_of_pos (hd i))
    _ = 0 := by rw [Finset.sum_sub_distrib,hdef,hsum]; simp [M,m]
  have h₂ : 1 ≤ ∏ i, (d i)⁻¹ := calc
    1 ≤ Real.exp (-∑ i, Real.log (d i)) := by
      have h := Real.exp_le_exp.mpr (show 0 ≤ -∑ i, Real.log (d i) from neg_nonneg.mpr hl)
      rwa [Real.exp_zero] at h
    _ = ∏ i, (d i)⁻¹ := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => by rw [Real.exp_neg, Real.exp_log (hd i)]
  rw [hh]
  exact le_mul_of_one_le_right hk.le h₂

end Body
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Laplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Geometric Mahler bounds from cone Laplace integrals and profile inequalities. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile Segment

variable {m:ℕ} [NeZero m]
omit [NeZero m] in
lemma orthant_pull {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {C:ProperCone ℝ E} {D:ProperCone ℝ F} (B:E≃ₗ[ℝ]F) (hB:∀ x,x∈C↔B x∈D)
    (h:IsLinearOrthant m D) : IsLinearOrthant m C := by
  obtain ⟨a,rfl⟩:=h
  let b:= a.map B.symm
  refine ⟨b,?_⟩
  ext x; rw [hB,mem_orthant,mem_orthant]
  have he : b.equivFun x=a.equivFun (B x) := by unfold b; rw [Basis.map_equivFun]; rfl
  rw [he]

lemma ConeLap (h:Input091) (C:ProperCone ℝ (Rn m)) (U V:Rn m)
    (hU:U∈interior (C:Set (Rn m))) (hV:V∈interior (posDual C:Set (Rn m))) (he:⟪U,V⟫=(m:ℝ)):
    1 ≤ chi C V*chi (posDual C) U ∧
      (chi C V*chi (posDual C) U=1 → IsLinearOrthant m C) := by
  let q:ProjField m:={
    C:=C,U:=U,V:=V,U_in:=hU,V_in:=hV,ip:=he,S:=1,pos:=Matrix.PosDef.one,
    root:=equivPD Matrix.PosDef.one, matrix_eq:=equivPD_spec _
  }
  obtain ⟨R,hR,hR',P,hP⟩:= simultaneous q h.ud
  let W:= P.instanceQ hR' q
  have hh : W.Balanced P.T :=
    ⟨P.in_box.2,(P.sigma_choice hR' q).symm,hP.2.1,hP.1,hP.2.2⟩
  let B := (P.transE hR').toLinearEquiv
  have h₁ : chi W.C W.V*chi W.D W.U = chi C V*chi (posDual C) U :=
    chi_transform B C U V
  obtain ⟨hf,hf'⟩:= W.C_bound P.T hh h.ud h.ly h.sg
  rw [h₁] at hf hf'
  refine ⟨hf,fun H=>orthant_pull B ?_ (hf' H)⟩
  intro x; change x∈C↔B x∈pushCone B C; rw [mem_pushCone,LinearEquiv.symm_apply_apply]

namespace Body
variable {n:ℕ}

-- transfer through an isometric identification with Rn(n+1)
lemma CLift (h:Input091) (C:ProperCone ℝ (LiftSpace n)) (U V:LiftSpace n)
    (hU:U∈interior (C:Set (LiftSpace n))) (hV:V∈interior (posDual C:Set (LiftSpace n)))
    (he:⟪U,V⟫=((n+1:ℕ):ℝ)):
    1 ≤ chi C V*chi (posDual C) U ∧
      (chi C V*chi (posDual C) U=1 → IsLinearOrthant (n+1) C) := by
  let a : OrthonormalBasis (Fin (n+1)) ℝ (LiftSpace n) :=
    (stdOrthonormalBasis ℝ _).reindex (finCongr (lift_finrank n))
  let B:= a.repr
  let M:=a.measurableEquiv
  have hB : MeasurePreserving M := a.measurePreserving_measurableEquiv
  let p := fun D: ProperCone ℝ (LiftSpace n)=> ProperCone.comap
    B.symm.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap D
  have hp (D) (x:LiftSpace n): B x ∈ p D ↔ x∈D := by
    change B.symm (B x)∈D↔_
    rw [B.symm_apply_apply]
  have hi (D:ProperCone ℝ (LiftSpace n)) (x:LiftSpace n) (hx:x∈interior (D:Set (LiftSpace n))):
      B x∈interior ((p D):Set (Rn (n+1))) := by
    let k:= B.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph
    change k x ∈ interior (k.symm ⁻¹' (D:Set (LiftSpace n)))
    rw [← k.symm.preimage_interior]
    simpa using hx
  have hh : posDual (p C) = p (posDual C) := by
    ext x
    obtain ⟨x,rfl⟩:=B.surjective x
    rw [hp,mem_posDual,mem_posDual]
    constructor
    · intro h y hy
      have hj:= h ((hp C y).2 hy); rwa [B.inner_map_map] at hj
    intro h y hy
    obtain ⟨y,rfl⟩:=B.surjective y
    rw [B.inner_map_map]; exact h ((hp C y).mp hy)
  have hc (D) (w:LiftSpace n): chi (p D) (B w)=chi D w := by
    classical
    unfold chi
    rw [← integral_indicator (p D).isClosed.measurableSet,
      ← integral_indicator D.isClosed.measurableSet,← hB.integral_comp']
    congr 1; ext x
    change ((p D):Set (Rn (n+1))).indicator _ (B x)=_
    by_cases h:x∈D
    · rw [indicator_of_mem ((hp D x).2 h),indicator_of_mem h]; rw [B.inner_map_map]
    rw [indicator_of_notMem (mt ((hp D x).1) h), indicator_of_notMem h]
  obtain ⟨h,h'⟩:= ConeLap h (p C) (B U) (B V) (hi _ U hU) (by rw [hh]; apply hi _ V hV)
    (by rw [B.inner_map_map,he])
  rw [hh,hc,hc] at h h'
  exact ⟨h,fun he=> orthant_pull B.toLinearEquiv (fun x=> (hp C x).symm) (h' he)⟩

lemma bound_at (h:Input091) (K:Body n) (z:Rn n) (hz:z∈interior (K:Set (Rn n))):
    ((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 ≤ K.productAt z ∧
      (K.productAt z=((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 → IsSimplex (K:Set (Rn n))) := by
  let m:ℝ:= (n:ℝ)+1
  have hm : 0 < m := by unfold m; positivity
  let U:=pair m (m • z)
  let V:=pair 1 (0:Rn n)
  have he : ⟪U,V⟫=((n+1:ℕ):ℝ) := by unfold U V; rw [pair_inner]; simp [m]
  obtain ⟨hh,hi⟩:=CLift h K.cone U V ((K.pair_mem_interior_cone_iff m hm _).2 hz)
    (axis_dual_interior K 1 zero_lt_one) he
  let k : ℝ := m^(n+1)/(n.factorial:ℝ)^2
  have hk : 0<k := by unfold k; positivity
  have H : chi K.cone V*chi (posDual K.cone) U= K.productAt z/k := by
    rw [cone_volume K z hz m hm]
    unfold k productAt polarVol
    rw [inv_pow]; field_simp
  rw [H] at hh hi
  change k≤ _ ∧ ((K.productAt z)=k → IsSimplex _)
  refine ⟨?_,fun he=>simplex_of_linearOrthant (hi (by rw [he,div_self hk.ne']))⟩
  rw [le_div_iff₀ hk,one_mul] at hh; exact hh

theorem main_with_profiles (h:Input091) (K:Body n) :
    ((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 ≤ K.P ∧
      (K.P=((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 ↔ IsSimplex (K:Set (Rn n))) := by
  obtain ⟨hh,hi⟩:= bound_at h K K.santalo K.santalo_spec.1
  exact ⟨hh,hi,@simplex_attains n K⟩
end Body
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general Mahler inequality, equality characterization, and Santaló minimum. -/

namespace GeneralMahler

open SCal SCal.Grid SCal.Mid Set MeasureTheory

/-- The sharp volume-product bound and its simplex equality case. -/
theorem mahal {n : ℕ} (K : Body n) :
    ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ≤ K.P ∧
      (K.P = ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ↔
        IsSimplex (K : Set (Rn n))) :=
  Body.main_with_profiles Complete_profile_input K

/-- The Santaló minimum is attained uniquely and satisfies the sharp Mahler inequality. -/
theorem general_geometric {n : ℕ} (_hn : 1 ≤ n) (K : Set (Rn n))
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    let D := ofSet K hK hc hi
    (∃! x, x ∈ interior K ∧ IsMinOn D.polarVol (interior K) x) ∧
    (D.santalo ∈ interior K ∧ IsMinOn D.polarVol (interior K) D.santalo) ∧
    (D.P = (volume K).toReal * (volume (polarAt K D.santalo)).toReal) ∧
    D.P = sInf (D.productAt '' interior K) ∧
    ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ≤ D.P ∧
      (D.P = ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ) ^ 2 ↔ IsSimplex K) := by
  intro D
  exact ⟨D.santalo_exists, D.santalo_spec, rfl, D.product_inf, (mahal D).1, (mahal D).2⟩

end GeneralMahler

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Theorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory

namespace GeneralMahler

/-- The sharp general Mahler inequality, with equality exactly for simplices. -/
theorem general_mahler_oai {n : ℕ} (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty) :
    ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ≤ volumeProduct K ∧
      (volumeProduct K = ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ↔
        ∃ vertices : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
          AffineIndependent ℝ vertices ∧ K = convexHull ℝ (range vertices)) := by
  let D := ofSet K hcompact hconvex hinterior
  have h := (general_geometric hn K hcompact hconvex hinterior).2.2.2.2
  change ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ≤ D.P ∧
    (D.P = ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ↔
      ∃ vertices : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
        AffineIndependent ℝ vertices ∧ K = convexHull ℝ (range vertices)) at h
  have hInf : D.P = volumeProduct K := D.product_inf
  rw [hInf] at h
  exact h

end GeneralMahler

end

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.general_mahler_oai := @OAI.GeneralMahler.general_mahler_oai

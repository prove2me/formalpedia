-- Prove2me | solution 1 for OAI.AllScaleInverseVolume.inverse_volume_without_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:01:14.941693+00:00
-- url     : https://prove2.me/submissions/5a1baf9b-6a7e-4f63-8a3f-bab7c4eb1e64

import Mathlib
import Definitions.Def_GaussianInformation_002
import Definitions.Def_OAIQWRLC001

section
-- module Solutions.OAIQW_RepeatedLocalization.Compat
namespace OAI
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434


end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_Ellipsoids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal

lemma diagonalMap_apply {q : ℕ} (c : Fin q → ℝ) (x : Ambient q) (j : Fin q) :
    diagonalMap c x j = c j*x j := by
  simp [diagonalMap,Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.mulVec_diagonal]

lemma diagonalMap_det {q : ℕ} (c : Fin q → ℝ) : LinearMap.det (diagonalMap c) = ∏ j,c j := by
  rw [diagonalMap,Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin,Matrix.det_diagonal]

lemma diagonalMap_contraction {q : ℕ} (c : Fin q → ℝ) (hc : ∀ j,0 ≤ c j ∧ c j ≤ 1) (x : Ambient q) :
    ‖diagonalMap c x‖ ≤ ‖x‖ := by
  have hs : ‖diagonalMap c x‖^2 ≤ ‖x‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change (diagonalMap c x j)^2 ≤ (x j)^2
    rw [diagonalMap_apply,mul_pow]
    have hh : (c j)^2 ≤ 1 := by nlinarith [(hc j).1,(hc j).2]
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (one_mul _)
  nlinarith [norm_nonneg (diagonalMap c x),norm_nonneg x]

lemma card_ellipsoid_separated {q : ℕ} (c : Fin q → ℝ) (hc : ∀ j,0 < c j ∧ c j ≤ 1)
    (s : Finset (Ambient q)) (hs : ∀ x ∈ s,‖diagonalMap c x‖ ≤ 2)
    (hsep : ∀ x ∈ s,∀ y ∈ s,x ≠ y → 1 ≤ ‖x-y‖) :
    (s.card:ℝ) ≤ 5^q * (∏ j,c j)⁻¹ := by
  let A := ⋃ x ∈ s,ball x (1/2)
  have hp : 0 < ∏ j,c j := Finset.prod_pos (fun j _ => (hc j).1)
  have hd : LinearMap.det (diagonalMap c) ≠ 0 := by rw [diagonalMap_det]; exact ne_of_gt hp
  have hdisj : (s:Set (Ambient q)).PairwiseDisjoint (fun x => ball x (1/2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep x hx y hy hxy using 1
    norm_num
  have hsub : A ⊆ diagonalMap c ⁻¹' ball 0 (5/2) := by
    intro y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    have he : ‖diagonalMap c (y-x)‖ < 1/2 :=
      (diagonalMap_contraction c (fun j => ⟨(hc j).1.le,(hc j).2⟩) (y-x)).trans_lt hy
    change ‖diagonalMap c y-0‖ < 5/2
    rw [sub_zero]
    have hi := norm_add_le (diagonalMap c (y-x)) (diagonalMap c x)
    rw [← map_add,sub_add_cancel] at hi
    linarith [hs x hx]
  have hb : (s.card:ℝ≥0∞)*ENNReal.ofReal ((1/2:ℝ)^q)*volume (ball (0:Ambient q) 1) ≤
      ENNReal.ofReal ((∏ j,c j)⁻¹)*ENNReal.ofReal ((5/2:ℝ)^q)*volume (ball (0:Ambient q) 1) := by
    calc
      _ = volume A := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [volume.addHaar_ball_of_pos _ (by norm_num : (0:ℝ)<1/2),finrank_euclideanSpace,
          Fintype.card_fin,Finset.sum_const,nsmul_eq_mul,mul_assoc]
      _ ≤ volume (diagonalMap c ⁻¹' ball 0 (5/2)) := measure_mono hsub
      _ = _ := by
        rw [Measure.addHaar_preimage_linearMap volume hd,diagonalMap_det,abs_of_pos (inv_pos.mpr hp),
          volume.addHaar_ball_of_pos _ (by norm_num : (0:ℝ)<5/2)]
        simp [mul_assoc]
  have hb' := (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0:Ambient q) zero_lt_one).ne'
    measure_ball_lt_top.ne).mp hb
  rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hp))] at hb'
  have hr : (s.card:ℝ)*(1/2:ℝ)^q ≤ (∏ j,c j)⁻¹*(5/2:ℝ)^q := by
    simpa [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (1/2:ℝ)^q)] using
      ENNReal.toReal_le_of_le_ofReal (by positivity) hb'
  have he : (5/2:ℝ)^q = 5^q*(1/2:ℝ)^q := by rw [← mul_pow]; congr 1; norm_num
  rw [he,← mul_assoc,mul_comm (∏ j,c j)⁻¹] at hr
  exact (mul_le_mul_iff_left₀ (pow_pos (by norm_num : (0:ℝ)<1/2) q)).mp hr

lemma exists_ellipsoid_cover {q : ℕ} (c : Fin q → ℝ) (hc : ∀ j,0 < c j ∧ c j ≤ 1) :
    ∃ s : Finset (Ambient q),
      (∀ x ∈ s,‖diagonalMap c x‖ ≤ 2) ∧
      (∀ x : Ambient q,‖diagonalMap c x‖ ≤ 2 → ∃ y ∈ s,dist x y ≤ 1) ∧
      (s.card:ℝ) ≤ 5^q*(∏ j,c j)⁻¹ := by
  classical
  let A := diagonalMap c ⁻¹' closedBall 0 2
  have hd : LinearMap.det (diagonalMap c) ≠ 0 := by
    rw [diagonalMap_det]
    exact ne_of_gt (Finset.prod_pos (fun j _ => (hc j).1))
  let e : Ambient q ≃ₗ[ℝ] Ambient q :=
    LinearMap.equivOfIsUnitDet (f := diagonalMap c) (isUnit_iff_ne_zero.mpr hd)
  have he : DFunLike.coe e = DFunLike.coe (diagonalMap c) := by
    funext x
    exact LinearMap.equivOfIsUnitDet_apply (f := diagonalMap c) (isUnit_iff_ne_zero.mpr hd) x
  have hA : IsCompact A := by
    change IsCompact (diagonalMap c ⁻¹' closedBall 0 2)
    rw [← he]
    exact e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  let ε : ℝ≥0 := 1
  obtain ⟨N,_,hNfin,hNcov⟩ := Metric.exists_finite_isCover_of_isCompact
    (s := A) (ε := ε/2) (by norm_num [ε]) hA
  have hp : Metric.packingNumber ε A < ⊤ := by
    calc
      _ = Metric.packingNumber (2*(ε/2)) A := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε/2) A := Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ N.encard := hNcov.externalCoveringNumber_le_encard
      _ < ⊤ := hNfin.encard_lt_top
  let S := Metric.maximalSeparatedSet ε A
  have hSfin : S.Finite := Set.encard_lt_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard < ⊤
    rw [Metric.encard_maximalSeparatedSet hp.ne]
    exact hp)
  have hs : ∀ x ∈ hSfin.toFinset,‖diagonalMap c x‖ ≤ 2 := by
    intro x hx
    have hm : x ∈ S := by simpa using hx
    simpa [A] using Metric.maximalSeparatedSet_subset hm
  refine ⟨hSfin.toFinset,hs,?_,card_ellipsoid_separated c hc _ hs ?_⟩
  · intro x hx
    have hm : x ∈ A := by simpa [A] using hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (Metric.isCover_iff_subset_iUnion_closedBall.mp
      (Metric.isCover_maximalSeparatedSet hp.ne) hm)
    exact ⟨y,by simpa using hy,by simpa [ε] using hxy⟩
  · intro x hx y hy hxy
    have hs := Metric.isSeparated_maximalSeparatedSet (ε := ε) (A := A)
      (by simpa using hx) (by simpa using hy) hxy
    have ht := ENNReal.toReal_mono (edist_ne_top x y) hs.le
    simpa [ε,edist_dist,dist_eq_norm] using ht

lemma weighted_group_bound {q : ℕ} (g : Fin q → ℕ) (x : Ambient q)
    (hx : ∀ h : ℕ,∑ j ∈ Finset.univ.filter (fun j => g j = h),(x j)^2 ≤ (4:ℝ)^h) :
    ‖diagonalMap (fun j => (1/4:ℝ)^(g j)) x‖ ≤ 2 := by
  classical
  let T := Finset.univ.image g
  have hsum : ∑ j : Fin q,((1/4:ℝ)^(g j)*(x j))^2 ≤ 4/3 := by
    calc
      _ = ∑ h ∈ T,∑ j ∈ Finset.univ.filter (fun j => g j = h),
          ((1/4:ℝ)^(g j)*(x j))^2 :=
        (Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) _).symm
      _ ≤ ∑ h ∈ T,(1/4:ℝ)^h := by
        apply Finset.sum_le_sum
        intro h hh
        calc
          _ = ((1/4:ℝ)^h)^2 * ∑ j ∈ Finset.univ.filter (fun j => g j = h),(x j)^2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [(Finset.mem_filter.mp hj).2,mul_pow]
          _ ≤ ((1/4:ℝ)^h)^2 * (4:ℝ)^h := mul_le_mul_of_nonneg_left (hx h) (sq_nonneg _)
          _ = (1/4:ℝ)^h := by
            rw [sq,mul_assoc,← mul_pow]
            norm_num
      _ ≤ ∑' h : ℕ,(1/4:ℝ)^h :=
        (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).sum_le_tsum
          T (fun _ _ => by positivity)
      _ = 4/3 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖<1)]; norm_num
  have hn : ‖diagonalMap (fun j => (1/4:ℝ)^(g j)) x‖^2 ≤ 4/3 := by
    simpa only [EuclideanSpace.real_norm_sq_eq,diagonalMap_apply] using hsum
  nlinarith [norm_nonneg (diagonalMap (fun j => (1/4:ℝ)^(g j)) x)]

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_Tubes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal

lemma synth_sub {q d : ℕ} (e : Fin q → Ambient d) (x y : Ambient q) :
    synth e (x-y) = synth e x-synth e y := by
  simp [synth,sub_smul,Finset.sum_sub_distrib]

lemma exists_groupedTube_cover {q d : ℕ} (e : Fin q → Ambient d)
    (he : ∀ x : Ambient q,‖synth e x‖ ≤ ‖x‖)
    (g : Fin q → ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset (Ambient d),
      groupedTube e g r ⊆ ⋃ y ∈ s,ball y (3*r) ∧
      (s.card:ℝ) ≤ 5^q*(4:ℝ)^(∑ j,g j) := by
  classical
  let c : Fin q → ℝ := fun j => (1/4:ℝ)^(g j)
  have hc : ∀ j,0 < c j ∧ c j ≤ 1 := fun j =>
    ⟨pow_pos (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num)⟩
  obtain ⟨s,_,hcov,hcard⟩ := exists_ellipsoid_cover c hc
  refine ⟨s.image (fun y => synth e (r • y)),?_,?_⟩
  · intro x hx
    let a := r⁻¹ • coordinates e x
    have ha : ∀ h : ℕ,∑ j ∈ Finset.univ.filter (fun j => g j=h),(a j)^2 ≤ (4:ℝ)^h := by
      intro h
      have hj : ∑ j ∈ Finset.univ.filter (fun j => g j=h),(a j)^2 =
          (r⁻¹)^2 * ∑ j ∈ Finset.univ.filter (fun j => g j=h),(inner ℝ (e j) x)^2 := by
        simp [a,coordinates,mul_pow,Finset.mul_sum]
      rw [hj]
      calc
        _ ≤ (r⁻¹)^2*(r^2*4^h) := mul_le_mul_of_nonneg_left (hx.2 h) (sq_nonneg _)
        _ = _ := by field_simp [hr.ne']
    obtain ⟨y,hy,hay⟩ := hcov a (weighted_group_bound g a ha)
    refine mem_iUnion₂.mpr ⟨synth e (r • y),Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
    have hra : r • a = coordinates e x := by simp [a,smul_smul,ne_of_gt hr]
    have hdist : ‖synth e (coordinates e x)-synth e (r • y)‖ ≤ r := by
      rw [← hra,← synth_sub,← smul_sub]
      calc
        _ ≤ ‖r • (a-y)‖ := he _
        _ = r*‖a-y‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        _ ≤ r := (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hay) hr.le).trans_eq (mul_one r)
    change ‖x-synth e (r • y)‖ < 3*r
    have hadd := norm_add_le (residual e x) (synth e (coordinates e x)-synth e (r • y))
    have heq : residual e x+(synth e (coordinates e x)-synth e (r • y)) = x-synth e (r • y) := by
      simp only [residual]; abel
    rw [heq] at hadd
    linarith [hx.1]
  · calc
      _ ≤ (s.card:ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ 5^q*(∏ j,c j)⁻¹ := hcard
      _ = _ := by
        simp only [c,← Finset.prod_pow_eq_pow_sum,Finset.prod_inv_distrib,one_div,inv_pow,inv_inv]

lemma measure_groupedTube_le {q d : ℕ} (ν : Measure (Ambient d)) (hν : BallBound ν)
    (u : Ambient d) (e : Fin q → Ambient d)
    (he : ∀ x : Ambient q,‖synth e x‖ ≤ ‖x‖)
    (g : Fin q → ℕ) {r : ℝ} (hr : 0 < r) :
    ν {z | z-u ∈ groupedTube e g r} ≤
      ENNReal.ofReal (5^q*(4:ℝ)^(∑ j,g j)*(3*r)^(((d:ℝ)-1)/2)) := by
  classical
  obtain ⟨s,hcov,hcard⟩ := exists_groupedTube_cover e he g hr
  have hsub : {z | z-u ∈ groupedTube e g r} ⊆ ⋃ y ∈ s,ball (u+y) (3*r) := by
    intro z hz
    obtain ⟨y,hy,hzy⟩ := mem_iUnion₂.mp (hcov hz)
    refine mem_iUnion₂.mpr ⟨y,hy,?_⟩
    simpa only [mem_ball,dist_eq_norm,sub_add_eq_sub_sub] using hzy
  calc
    _ ≤ ν (⋃ y ∈ s,ball (u+y) (3*r)) := measure_mono hsub
    _ ≤ ∑ y ∈ s,ν (ball (u+y) (3*r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s,ENNReal.ofReal ((3*r)^(((d:ℝ)-1)/2)) :=
      Finset.sum_le_sum (fun y _ => hν (u+y) (3*r) (by positivity))
    _ = (s.card:ℝ≥0∞)*ENNReal.ofReal ((3*r)^(((d:ℝ)-1)/2)) := by simp
    _ ≤ ENNReal.ofReal (5^q*(4:ℝ)^(∑ j,g j))*ENNReal.ofReal ((3*r)^(((d:ℝ)-1)/2)) := by
      gcongr
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_Orthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace

lemma Suborthonormal.inner_eq {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (i j : Fin k) : inner ℝ (e i) (e j) = if i=j then ‖e i‖^2 else 0 := by
  classical
  by_cases hij : i=j
  · subst j; simp
  · simp [hij,he.1 hij]

lemma Suborthonormal.norm_le {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (i : Fin k) : ‖e i‖ ≤ 1 := by
  rcases he.2 i with h|h <;> simp [h]

lemma orthogonal_sum_norm_sq {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Finset (Fin k)) (a : Fin k → ℝ) :
    ‖∑ j ∈ s,a j • e j‖^2 = ∑ j ∈ s,(a j)^2*‖e j‖^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,real_inner_smul_left,inner_sum,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  simp [he.inner_eq,hi,pow_two,mul_assoc]

lemma suborthonormal_synth_contraction {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (x : Ambient k) : ‖synth e x‖ ≤ ‖x‖ := by
  have hh : ‖synth e x‖^2 ≤ ‖x‖^2 := by
    rw [synth,orthogonal_sum_norm_sq he,EuclideanSpace.real_norm_sq_eq x]
    apply Finset.sum_le_sum
    intro j _
    have hn : ‖e j‖^2 ≤ 1 := by nlinarith [he.norm_le j,norm_nonneg (e j)]
    simpa using mul_le_mul_of_nonneg_left hn (sq_nonneg (x j))
  nlinarith [norm_nonneg (synth e x),norm_nonneg x]

lemma suborthonormal_coeff_norm {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (x : Ambient d) (j : Fin k) : inner ℝ (e j) x * ‖e j‖^2 = inner ℝ (e j) x := by
  rcases he.2 j with h|h <;> simp [h]

lemma orthoResidual_inner {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Finset (Fin k)) (x : Ambient d) (j : Fin k) :
    inner ℝ (e j) (orthoResidual e s x) = if j∈s then 0 else inner ℝ (e j) x := by
  classical
  simp only [orthoResidual,inner_sub_right,inner_sum,real_inner_smul_right]
  simp_rw [he.inner_eq j]
  by_cases hj : j∈s <;> simp [hj,suborthonormal_coeff_norm he x j]

lemma orthoResidual_norm_sq {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Finset (Fin k)) (x : Ambient d) :
    ‖orthoResidual e s x‖^2 = ‖x‖^2-∑ j ∈ s,(inner ℝ (e j) x)^2 := by
  rw [orthoResidual,norm_sub_sq_real,orthogonal_sum_norm_sq he]
  have hinner : inner ℝ x (∑ j ∈ s,(inner ℝ (e j) x) • e j) =
      ∑ j ∈ s,(inner ℝ (e j) x)^2 := by
    simp only [inner_sum,real_inner_smul_right,real_inner_comm x,pow_two]
  have hnorm : ∑ j ∈ s,(inner ℝ (e j) x)^2*‖e j‖^2 =
      ∑ j ∈ s,(inner ℝ (e j) x)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_two,mul_assoc,suborthonormal_coeff_norm he]
  rw [hinner,hnorm]
  ring

lemma orthoResidual_norm_antitone {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    {s t : Finset (Fin k)} (hst : s⊆t) (x : Ambient d) :
    ‖orthoResidual e t x‖ ≤ ‖orthoResidual e s x‖ := by
  have hs := orthoResidual_norm_sq he s x
  have ht := orthoResidual_norm_sq he t x
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun j _ _ => sq_nonneg (inner ℝ (e j) x))
  nlinarith [norm_nonneg (orthoResidual e t x),norm_nonneg (orthoResidual e s x)]

lemma suborthonormal_bessel {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Finset (Fin k)) (x : Ambient d) :
    ∑ j ∈ s,(inner ℝ (e j) x)^2 ≤ ‖x‖^2 := by
  have hh := orthoResidual_norm_sq he s x
  nlinarith [sq_nonneg ‖orthoResidual e s x‖]

lemma gramSchmidtNormed_suborthonormal {d k : ℕ} (f : Fin k → Ambient d) :
    Suborthonormal (gramSchmidtNormed ℝ f) := by
  constructor
  · intro i j hij
    simp only [gramSchmidtNormed,real_inner_smul_left,real_inner_smul_right,
      gramSchmidt_orthogonal ℝ f hij,mul_zero]
  · intro j
    by_cases hj : gramSchmidtNormed ℝ f j=0
    · exact Or.inl hj
    · exact Or.inr (gramSchmidtNormed_unit_length' hj)

lemma Suborthonormal.cut {d k : ℕ} {e : Fin k → Ambient d} (he : Suborthonormal e)
    (s : Set (Fin k)) [DecidablePred (·∈s)] : Suborthonormal (fun j => if j∈s then e j else 0) := by
  constructor
  · intro i j hij
    by_cases hi : i∈s <;> by_cases hj : j∈s <;> simp [hi,hj,he.1 hij]
  · intro j
    by_cases hj : j∈s
    · simpa only [ite_eq_left hj] using he.2 j
    · exact Or.inl (ite_eq_right hj)

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_GramVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_linearCombination {ι : Type*} [Fintype ι] (g : ι → E)
    (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, T i j • g i) = Tᵀ * Matrix.gram ℝ g * T := by
  ext i j
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma gramTriangular_expansion {q : ℕ} (f : Fin q → E) (j : Fin q) :
    f j = ∑ i, gramTriangular f i j • gramSchmidt ℝ f i := by
  rw [gramSchmidt_def'' ℝ f j]
  have hfin : (Finset.univ.filter fun i : Fin q => i < j) = Finset.Iio j := by
    ext i
    simp
  simp only [gramTriangular, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter, hfin]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

lemma gramTriangular_det {q : ℕ} (f : Fin q → E) : (gramTriangular f).det = 1 := by
  have htri : (gramTriangular f).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp only [gramTriangular, ite_eq_right (ne_of_gt hij), ite_eq_right (not_lt.mpr (le_of_lt hij)),
      zero_add]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gramTriangular]

lemma gram_gramSchmidt {q : ℕ} (f : Fin q → E) :
    Matrix.gram ℝ (gramSchmidt ℝ f) =
      Matrix.diagonal (fun i => ‖gramSchmidt ℝ f i‖ ^ 2) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h, gramSchmidt_orthogonal ℝ f h]

lemma gram_det_eq_prod_gramSchmidt {q : ℕ} (f : Fin q → E) :
    (Matrix.gram ℝ f).det = (∏ i, ‖gramSchmidt ℝ f i‖)^2 := by
  have he : f = (fun j => ∑ i, gramTriangular f i j • gramSchmidt ℝ f i) :=
    funext (gramTriangular_expansion f)
  calc
    (Matrix.gram ℝ f).det =
        ((gramTriangular f)ᵀ * Matrix.gram ℝ (gramSchmidt ℝ f) * gramTriangular f).det := by
      conv_lhs => rw [he]
      rw [gram_linearCombination]
    _ = (∏ i, ‖gramSchmidt ℝ f i‖)^2 := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        gramTriangular_det, one_mul, mul_one, gram_gramSchmidt, Matrix.det_diagonal,
        Finset.prod_pow]

lemma sqrt_gram_det_eq_prod_gramSchmidt {q : ℕ} (f : Fin q → E) :
    Real.sqrt (Matrix.gram ℝ f).det = ∏ i, ‖gramSchmidt ℝ f i‖ := by
  rw [gram_det_eq_prod_gramSchmidt, Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]

lemma gramSchmidt_real_def {q : ℕ} (f : Fin q → E) (j : Fin q) :
    gramSchmidt ℝ f j = f j - ∑ i ∈ Finset.Iio j,
      (⟪gramSchmidt ℝ f i, f j⟫ / ‖gramSchmidt ℝ f i‖ ^ 2) • gramSchmidt ℝ f i := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using (gramSchmidt_def'' ℝ f j).symm

lemma measurable_gramSchmidt {q : ℕ} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (j : Fin q) :
    Measurable (fun f : Fin q → E => gramSchmidt ℝ f j) := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    simp_rw [gramSchmidt_real_def (j := j)]
    refine (measurable_pi_apply j).sub (Finset.measurable_fun_sum _ fun i hi => ?_)
    have hmi := ih i (Finset.mem_Iio.mp hi)
    exact ((hmi.inner (measurable_pi_apply j)).div (hmi.norm.pow_const 2)).smul hmi

lemma gramSchmidt_prefix_congr {q : ℕ} {f g : Fin q → E} (j : Fin q)
    (h : ∀ i ≤ j, f i = g i) : gramSchmidt ℝ f j = gramSchmidt ℝ g j := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    rw [gramSchmidt_real_def, gramSchmidt_real_def, h j le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hgi := ih i (Finset.mem_Iio.mp hi) (fun a ha => h a (ha.trans (Finset.mem_Iio.mp hi).le))
    rw [hgi]

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_GreedyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma swap_preserves_lower_bound {k : ℕ} {b i j c : Fin k}
    (hij : i ≤ j) (hbi : b ≤ i) (hbc : b ≤ c) : b ≤ Equiv.swap i j c := by
  classical
  by_cases hci : c=i
  · subst c; simpa using hbi.trans hij
  by_cases hcj : c=j
  · subst c; simpa using hbi
  simpa [Equiv.swap_apply_of_ne_of_ne hci hcj] using hbc

lemma exists_greedy_permutation {α : Type*} {k : ℕ}
    (D : (Fin k → α) → Fin k → α → ℝ)
    (hD : ∀ f g i,(∀ j,i > j → f j=g j) → ∀ x,D f i x=D g i x)
    (f : Fin k → α) : ∃ π : Equiv.Perm (Fin k),Greedy D (f ∘ π) := by
  classical
  have build : ∀ m : ℕ,m ≤ k → ∃ π : Equiv.Perm (Fin k),
      ∀ i j : Fin k,i.val < m → i ≤ j → D (f ∘ π) i (f (π j)) ≤ D (f ∘ π) i (f (π i)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨Equiv.refl _,fun i j hi _ => (Nat.not_lt_zero _ hi).elim⟩
    | succ m ih =>
      intro hm
      obtain ⟨π,hπ⟩ := ih (by omega)
      let i : Fin k := ⟨m,by omega⟩
      obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.Ici i)
        (fun j : Fin k => D (f ∘ π) i (f (π j))) (by simp)
      have hij : i ≤ j := Finset.mem_Ici.mp hj
      let τ := Equiv.swap i j
      have hfix : ∀ a : Fin k,a < i → τ a=a := by
        intro a ha
        exact Equiv.swap_apply_of_ne_of_ne (ne_of_lt ha) (ne_of_lt (ha.trans_le hij))
      have hpref : ∀ b : Fin k,b ≤ i → ∀ a : Fin k,a < b →
          (f ∘ (τ.trans π)) a = (f ∘ π) a := by
        intro b hb a ha
        simp only [Function.comp_apply,Equiv.trans_apply,hfix a (ha.trans_le hb)]
      refine ⟨τ.trans π,?_⟩
      intro b c hb hbc
      have hbi : b ≤ i := by change b.val ≤ m; omega
      have hscore := hD (f ∘ (τ.trans π)) (f ∘ π) b (hpref b hbi)
      by_cases hbeq : b=i
      · subst b
        simp only [Equiv.trans_apply] at hscore ⊢
        rw [hscore,hscore]
        have hτi : τ i=j := Equiv.swap_apply_left i j
        rw [hτi]
        exact hmax (τ c) (Finset.mem_Ici.mpr (swap_preserves_lower_bound hij le_rfl hbc))
      · have hblt : b < i := lt_of_le_of_ne hbi hbeq
        simp only [Equiv.trans_apply] at hscore ⊢
        rw [hscore,hscore,hfix b hblt]
        exact hπ b (τ c) (by change b.val < m at hblt; exact hblt)
          (swap_preserves_lower_bound hij hbi hbc)
  obtain ⟨π,hπ⟩ := build k le_rfl
  exact ⟨π,fun i j hij => hπ i j i.isLt hij⟩

lemma prefixAxes_suborthonormal {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) :
    Suborthonormal (prefixAxes f i) :=
  (gramSchmidtNormed_suborthonormal f).cut (Set.Iio i)

lemma gramSchmidtNormed_term {d k : ℕ} (f : Fin k → Ambient d) (j : Fin k) (x : Ambient d) :
    (inner ℝ (gramSchmidtNormed ℝ f j) x) • gramSchmidtNormed ℝ f j =
      (inner ℝ (gramSchmidt ℝ f j) x / ‖gramSchmidt ℝ f j‖^2) • gramSchmidt ℝ f j := by
  simp only [gramSchmidtNormed,real_inner_smul_left,smul_smul]
  congr 1
  simp only [div_eq_mul_inv,RCLike.ofReal_real_eq_id,id_eq]
  ring

lemma prefixResidual_self {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) :
    prefixResidual f i (f i)=gramSchmidt ℝ f i := by
  calc
    _ = f i-∑ j ∈ Finset.Iio i,(inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖^2) • gramSchmidt ℝ f j := by
      simp only [prefixResidual,orthoResidual,gramSchmidtNormed_term]
    _ = _ := (gramSchmidt_real_def f i).symm

lemma prefixResidual_eq {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) (x : Ambient d) :
    residual (prefixAxes f i) x=prefixResidual f i x := by
  classical
  have hI : Finset.univ.filter (fun j : Fin k => j < i)=Finset.Iio i := by ext j; simp
  simp only [residual,synth,coordinates,prefixAxes,prefixResidual,orthoResidual,WithLp.ofLp_toLp]
  congr 1
  calc
    _ = ∑ j : Fin k,if j < i then (inner ℝ (gramSchmidtNormed ℝ f j) x) • gramSchmidtNormed ℝ f j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j < i <;> simp [hj]
    _ = _ := by rw [← Finset.sum_filter,hI]

lemma prefixResidual_prefix_congr {d k : ℕ} {f g : Fin k → Ambient d} (i : Fin k)
    (hfg : ∀ j,j < i → f j=g j) (x : Ambient d) : prefixResidual f i x=prefixResidual g i x := by
  unfold prefixResidual orthoResidual
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have he : gramSchmidtNormed ℝ f j=gramSchmidtNormed ℝ g j := by
    simp only [gramSchmidtNormed,gramSchmidt_prefix_congr j
      (fun a ha => hfg a (ha.trans_lt (Finset.mem_Iio.mp hj)))]
  rw [he]

lemma prefixAxes_prefix_congr {d k : ℕ} {f g : Fin k → Ambient d} (i : Fin k)
    (hfg : ∀ j,j < i → f j=g j) : prefixAxes f i=prefixAxes g i := by
  funext j
  by_cases hj : j < i
  · simp only [prefixAxes,ite_eq_left hj,gramSchmidtNormed,gramSchmidt_prefix_congr j
      (fun a ha => hfg a (ha.trans_lt hj))]
  · simp [prefixAxes,hj]

lemma measurable_gramSchmidtNormed {d k : ℕ} (j : Fin k) :
    Measurable (fun f : Fin k → Ambient d => gramSchmidtNormed ℝ f j) :=
  (measurable_gramSchmidt j).norm.inv.smul (measurable_gramSchmidt j)

lemma measurable_prefixAxes {d k : ℕ} (i j : Fin k) :
    Measurable (fun f : Fin k → Ambient d => prefixAxes f i j) := by
  by_cases hj : j < i
  · simpa [prefixAxes,hj] using measurable_gramSchmidtNormed (d := d) j
  · simp [prefixAxes,hj]

lemma measurable_prefixResidual {d k : ℕ} (i : Fin k) :
    Measurable (fun p : (Fin k → Ambient d) × Ambient d => prefixResidual p.1 i p.2) := by
  unfold prefixResidual orthoResidual
  apply measurable_snd.sub
  apply Finset.measurable_sum
  intro j _
  exact (((measurable_gramSchmidtNormed (d := d) j).comp measurable_fst).inner (𝕜 := ℝ) measurable_snd).smul
    ((measurable_gramSchmidtNormed (d := d) j).comp measurable_fst)

lemma exists_greedy_gram_order {d k : ℕ} (f : Fin k → Ambient d) :
    ∃ π : Equiv.Perm (Fin k),Greedy residualScore (f ∘ π) := by
  apply exists_greedy_permutation
  intro f g i hfg x
  exact congrArg norm (prefixResidual_prefix_congr i hfg x)

lemma greedy_lengths_antitone {d k : ℕ} {f : Fin k → Ambient d}
    (hg : Greedy residualScore f) : Antitone (fun i => ‖gramSchmidt ℝ f i‖) := by
  intro i j hij
  calc
    _ = ‖prefixResidual f j (f j)‖ := by rw [prefixResidual_self]
    _ ≤ ‖prefixResidual f i (f j)‖ :=
      orthoResidual_norm_antitone (gramSchmidtNormed_suborthonormal f) (Finset.Iio_subset_Iio hij) _
    _ ≤ ‖prefixResidual f i (f i)‖ := hg i j hij
    _ = _ := by rw [prefixResidual_self]

lemma measurableSet_greedy {d k : ℕ} : MeasurableSet {f : Fin k → Ambient d | Greedy residualScore f} := by
  simp only [Greedy,residualScore,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le
    ((measurable_prefixResidual i).comp (measurable_id.prodMk (measurable_pi_apply j))).norm
    ((measurable_prefixResidual i).comp (measurable_id.prodMk (measurable_pi_apply i))).norm

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_DyadicBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma dyadicRadius_pos (l : ℤ) : 0 < dyadicRadius l := zpow_pos (by norm_num) _
lemma dyadicRadius_antitone : Antitone dyadicRadius := by
  intro l m hlm
  exact zpow_le_zpow_right₀ (by norm_num) (neg_le_neg hlm)
lemma exists_dyadic_bin {x : ℝ} (hx : 0<x) : ∃ l : ℤ,dyadicRadius (l+1)<x ∧ x≤dyadicRadius l := by
  obtain ⟨m,hm,hM⟩ := exists_mem_Ioc_zpow hx (by norm_num : (1:ℝ)<2)
  refine ⟨-m-1,?_,?_⟩
  · simpa [dyadicRadius] using hm
  · simpa [dyadicRadius,add_comm] using hM

lemma exists_bins {d k : ℕ} {ε : ℝ} (hε : 0<ε) (f : Fin k → Ambient d) :
    ∃ l : Fin k → ℤ,InBins ε f l := by
  have hi : ∀ i,∃ l : ℤ,dyadicRadius (l+1)<clippedLength ε f i ∧ clippedLength ε f i≤dyadicRadius l :=
    fun i => exists_dyadic_bin (hε.trans_le (le_max_right _ _))
  exact Classical.skolem.mp hi

lemma bins_monotone {d k : ℕ} {ε : ℝ} {f : Fin k → Ambient d} {l : Fin k → ℤ}
    (hg : Greedy residualScore f) (hl : InBins ε f l) : Monotone l := by
  intro i j hij
  by_contra hn
  have he : l j+1≤l i := by omega
  have hc : clippedLength ε f j≤clippedLength ε f i :=
    max_le_max (greedy_lengths_antitone hg hij) le_rfl
  exact (not_lt_of_ge ((hl i).2.trans (dyadicRadius_antitone he))) ((hl j).1.trans_le hc)

lemma dyadicRadius_sq_gap {a b : ℤ} (hab : b≤a) :
    (dyadicRadius b)^2=(dyadicRadius a)^2*(4:ℝ)^((a-b).toNat) := by
  have hz : (((a-b).toNat:ℕ):ℤ)=a-b := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  have h4 : (4:ℝ)^((a-b).toNat)=(2:ℝ)^(2*(a-b):ℤ) := by
    rw [show (4:ℝ)=2^2 by norm_num,← pow_mul,← zpow_natCast, Nat.cast_mul,hz]
    norm_num
  rw [h4,dyadicRadius,dyadicRadius,← zpow_natCast,← zpow_natCast,← _root_.zpow_mul,← _root_.zpow_mul,
    ← zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  congr 1
  ring

lemma greedy_mem_groupedTube {d k : ℕ} {ε : ℝ} {f : Fin k → Ambient d} {l : Fin k → ℤ}
    (hg : Greedy residualScore f) (hl : InBins ε f l) (i : Fin k) :
    f i∈groupedTube (prefixAxes f i) (binGap l i) (dyadicRadius (l i)) := by
  classical
  have hmono := bins_monotone hg hl
  have he := gramSchmidtNormed_suborthonormal f
  constructor
  · rw [prefixResidual_eq,prefixResidual_self]
    exact (le_max_left _ _).trans (hl i).2
  · intro h
    let s := Finset.univ.filter (fun j => j < i ∧ binGap l i j=h)
    have hsum : ∑ j ∈ Finset.univ.filter (fun j => binGap l i j=h),
        (inner ℝ (prefixAxes f i j) (f i))^2 =
        ∑ j ∈ s,(inner ℝ (gramSchmidtNormed ℝ f j) (f i))^2 := by
      simp only [s,Finset.sum_filter,prefixAxes]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j < i <;> by_cases hh : binGap l i j=h <;> simp [hj,hh]
    rw [hsum]
    by_cases hs : s.Nonempty
    · obtain ⟨b,hbs,hmin⟩ := Finset.exists_min_image s id hs
      have hb := (Finset.mem_filter.mp hbs).2
      have hbj : ∀ j∈s,b≤j := fun j hj => hmin j hj
      have hinner : ∀ j∈s,inner ℝ (gramSchmidtNormed ℝ f j) (prefixResidual f b (f i))=
          inner ℝ (gramSchmidtNormed ℝ f j) (f i) := by
        intro j hj
        rw [prefixResidual,orthoResidual_inner he]
        simp only [Finset.mem_Iio,not_lt_of_ge (hbj j hj),ite_false]
      have hc : ∑ j ∈ s,(inner ℝ (gramSchmidtNormed ℝ f j) (f i))^2 ≤
          ‖prefixResidual f b (f i)‖^2 := by
        convert suborthonormal_bessel he s (prefixResidual f b (f i)) using 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [hinner j hj]
      have hnorm : ‖prefixResidual f b (f i)‖≤dyadicRadius (l b) := by
        calc
          _ ≤ ‖prefixResidual f b (f b)‖ := hg b i hb.1.le
          _ = ‖gramSchmidt ℝ f b‖ := by rw [prefixResidual_self]
          _ ≤ clippedLength ε f b := le_max_left _ _
          _ ≤ _ := (hl b).2
      have hgap : (l i-l b).toNat=h := by simpa only [binGap,ite_eq_left hb.1] using hb.2
      calc
        _ ≤ ‖prefixResidual f b (f i)‖^2 := hc
        _ ≤ (dyadicRadius (l b))^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm _
        _ = _ := by rw [dyadicRadius_sq_gap (hmono hb.1.le),hgap]
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.sum_empty]
      positivity

lemma measurable_snoc_const {α : Type*} [MeasurableSpace α] {k : ℕ} (a : α) :
    Measurable (fun z : Fin k → α => Fin.snoc (α := fun _ : Fin (k+1) => α) z a) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa using (measurable_pi_apply j : Measurable (fun z : Fin k → α => z j))

lemma snoc_update_last {α : Type*} {k : ℕ} (z : Fin k → α) (a x : α) :
    Function.update (Fin.snoc (α := fun _ : Fin (k+1) => α) z a) (Fin.last k) x=Fin.snoc z x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_StageEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma measure_sequential_event_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (a : α) :
    ∀ k : ℕ,∀ (P : Fin k → (Fin k → α) → Prop) (B : Fin k → ℝ≥0∞),
    (∀ i,MeasurableSet {z | P i z}) →
    (∀ i f g,(∀ j,j ≤ i → f j=g j) → (P i f ↔ P i g)) →
    (∀ i f,μ {x | P i (Function.update f i x)} ≤ B i) →
    (Measure.pi (fun _ : Fin k => μ)) {z | ∀ i,P i z} ≤ ∏ i,B i := by
  classical
  intro k
  induction k with
  | zero => intro P B _ _ _; simp
  | succ k ih =>
    intro P B hP hdep hcond
    let P' : Fin k → (Fin k → α) → Prop := fun i z => P i.castSucc (Fin.snoc z a)
    let B' : Fin k → ℝ≥0∞ := fun i => B i.castSucc
    have hP' : ∀ i,MeasurableSet {z | P' i z} := fun i =>
      (hP i.castSucc).preimage (measurable_snoc_const a)
    have hdep' : ∀ i f g,(∀ j,j ≤ i → f j=g j) → (P' i f ↔ P' i g) := by
      intro i f g hfg
      apply hdep
      intro j
      refine Fin.lastCases ?_ (fun l => ?_) j
      · intro hj
        exact (not_le_of_gt (Fin.castSucc_lt_last i) hj).elim
      · intro hj
        simp only [Fin.snoc_castSucc]
        exact hfg l (by simpa only [Fin.castSucc_le_castSucc_iff] using hj)
    have hcond' : ∀ i f,μ {x | P' i (Function.update f i x)} ≤ B' i := by
      intro i f
      simpa only [P',B',Fin.snoc_update] using hcond i.castSucc (Fin.snoc f a)
    have hind := ih P' B' hP' hdep' hcond'
    let E : Set (Fin (k+1) → α) := {z | ∀ i,P i z}
    let E' : Set (Fin k → α) := {z | ∀ i,P' i z}
    have hE : MeasurableSet E := by simpa [E,Set.ofPred_forall] using MeasurableSet.iInter (fun i => hP i)
    have hE' : MeasurableSet E' := by simpa [E',Set.ofPred_forall] using MeasurableSet.iInter (fun i => hP' i)
    have hbefore : ∀ (z : Fin k → α) (x : α) (i : Fin k),
        P i.castSucc (Fin.snoc z x) ↔ P' i z := by
      intro z x i
      apply hdep
      intro j
      refine Fin.lastCases ?_ (fun l => ?_) j
      · intro hj
        exact (not_le_of_gt (Fin.castSucc_lt_last i) hj).elim
      · intro _; simp
    have hleaf : ∀ z : Fin k → α,
        μ {x | Fin.snoc z x ∈ E} ≤ E'.indicator (fun _ => B (Fin.last k)) z := by
      intro z
      by_cases hz : z∈E'
      · rw [indicator_of_mem hz]
        calc
          _ ≤ μ {x | P (Fin.last k) (Fin.snoc z x)} := by
            apply measure_mono
            intro x hx
            change (∀ i,P i (Fin.snoc z x)) at hx
            exact hx (Fin.last k)
          _ ≤ B (Fin.last k) := by simpa only [snoc_update_last] using hcond (Fin.last k) (Fin.snoc z a)
      · rw [indicator_of_notMem hz]
        have hempty : {x | Fin.snoc z x ∈ E}=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          apply hz
          intro i
          exact (hbefore z x i).mp (hx i.castSucc)
        simp [hempty]
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) (Fin.last k)).symm
    have heq : (Measure.pi (fun _ : Fin (k+1) => μ)) E =
        ∫⁻ z : Fin k → α,μ {x | Fin.snoc z x ∈ E} ∂Measure.pi (fun _ => μ) := by
      rw [← hp.measure_preimage hE.nullMeasurableSet,Measure.prod_apply_symm (hE.preimage hp.measurable)]
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
        Fin.insertNth_last]
      rfl
    change (Measure.pi (fun _ : Fin (k+1) => μ)) E ≤ _
    rw [heq]
    calc
      _ ≤ ∫⁻ z : Fin k → α,E'.indicator (fun _ => B (Fin.last k)) z ∂Measure.pi (fun _ => μ) := lintegral_mono hleaf
      _ = B (Fin.last k)*(Measure.pi (fun _ : Fin k => μ)) E' := by
        rw [lintegral_indicator hE',lintegral_const,Measure.restrict_apply_univ]
      _ ≤ B (Fin.last k)*∏ i,B' i := mul_le_mul_right hind _
      _ = ∏ i,B i := by rw [Fin.prod_univ_castSucc]; simp only [B']; ring

lemma measurable_translated {d k : ℕ} (u : Ambient d) : Measurable (translated (k := k) u) :=
  Measurable.of_eval (fun i => (measurable_pi_apply i).sub measurable_const)

lemma measurable_translated_residual {d k : ℕ} (u : Ambient d) (i : Fin k) :
    Measurable (fun z : Fin k → Ambient d => residual (prefixAxes (translated u z) i) (z i-u)) := by
  have hm : Measurable (fun z : Fin k → Ambient d => (translated u z,z i-u)) :=
    (measurable_translated (k := k) u).prodMk ((measurable_pi_apply i).sub measurable_const)
  simpa only [prefixResidual_eq,Function.comp_def] using (measurable_prefixResidual (d := d) i).comp hm

lemma measurable_translated_coefficient {d k : ℕ} (u : Ambient d) (i j : Fin k) :
    Measurable (fun z : Fin k → Ambient d => inner ℝ (prefixAxes (translated u z) i j) (z i-u)) := by
  have ha : Measurable (fun z : Fin k → Ambient d => prefixAxes (translated u z) i j) :=
    (measurable_prefixAxes (d := d) i j).comp (measurable_translated u)
  exact ha.inner (𝕜 := ℝ) ((measurable_pi_apply i).sub measurable_const)

lemma measurableSet_stageEvent {d k : ℕ} (u : Ambient d) (l : Fin k → ℤ) (i : Fin k) :
    MeasurableSet {z | StageEvent u l i z} := by
  classical
  by_cases hi : 0 ≤ l i
  · have hr := measurable_translated_residual u i
    have hs : ∀ h : ℕ,Measurable (fun z : Fin k → Ambient d =>
        ∑ j ∈ Finset.univ.filter (fun j => binGap l i j=h),
          (inner ℝ (prefixAxes (translated u z) i j) (z i-u))^2) := by
      intro h
      apply Finset.measurable_sum
      intro j _
      exact (measurable_translated_coefficient u i j).pow_const _
    simp only [StageEvent,hi,forall_true_left]
    change MeasurableSet {z : Fin k → Ambient d |
      ‖residual (prefixAxes (translated u z) i) (z i-u)‖ ≤ dyadicRadius (l i) ∧
      ∀ h : ℕ,∑ j ∈ Finset.univ.filter (fun j => binGap l i j=h),
        (inner ℝ (prefixAxes (translated u z) i j) (z i-u))^2 ≤ (dyadicRadius (l i))^2*4^h}
    rw [ofPred_and]
    apply MeasurableSet.inter (measurableSet_le hr.norm measurable_const)
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun h => measurableSet_le (hs h) measurable_const)
  · simp [StageEvent,hi]

lemma stageEvent_prefix {d k : ℕ} (u : Ambient d) (l : Fin k → ℤ) (i : Fin k)
    (f g : Fin k → Ambient d) (hfg : ∀ j,j  ≤  i → f j=g j) :
    StageEvent u l i f ↔ StageEvent u l i g := by
  have he : prefixAxes (translated u f) i=prefixAxes (translated u g) i :=
    prefixAxes_prefix_congr i (fun j hj => congrArg (fun x => x-u) (hfg j hj.le))
  simp only [StageEvent,he,hfg i le_rfl]

lemma stageEvent_update {d k : ℕ} (u : Ambient d) (l : Fin k → ℤ) (i : Fin k)
    (f : Fin k → Ambient d) (x : Ambient d) :
    StageEvent u l i (Function.update f i x) ↔
      (0 ≤ l i → x-u∈groupedTube (prefixAxes (translated u f) i) (binGap l i) (dyadicRadius (l i))) := by
  have he : prefixAxes (translated u (Function.update f i x)) i=prefixAxes (translated u f) i := by
    apply prefixAxes_prefix_congr
    intro j hj
    simp only [translated,Function.update_of_ne (ne_of_lt hj)]
  simp only [StageEvent,he,Function.update_self]

lemma greedy_bins_stageEvents {d k : ℕ} {ε : ℝ} (u : Ambient d) {z : Fin k → Ambient d}
    {l : Fin k → ℤ} (hg : Greedy residualScore (translated u z))
    (hl : InBins ε (translated u z) l) : ∀ i,StageEvent u l i z :=
  fun i _ => greedy_mem_groupedTube hg hl i

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_ExponentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma positiveSum_nonneg {k : ℕ} (l : Fin k → ℤ) : 0 ≤ positiveSum l :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
lemma negativeSum_nonneg {k : ℕ} (l : Fin k → ℤ) : 0 ≤ negativeSum l :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
lemma sum_bins {k : ℕ} (l : Fin k → ℤ) : (∑ i,(l i:ℝ))=positiveSum l-negativeSum l := by
  rw [positiveSum,negativeSum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 ≤ (l i:ℝ)
  · simp [max_eq_left hi,max_eq_right (neg_nonpos.mpr hi)]
  · simp [max_eq_right (le_of_not_ge hi),max_eq_left (neg_nonneg.mpr (le_of_not_ge hi))]

lemma binGap_sum_le {k : ℕ} (l : Fin k → ℤ) (i : Fin k) (hl : Monotone l) :
    (∑ j,(binGap l i j:ℝ)) ≤ k*max (l i:ℝ) 0+negativeSum l := by
  calc
    _  ≤  ∑ j : Fin k,(max (l i:ℝ) 0+max (-(l j:ℝ)) 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j < i
      · have hc : ((binGap l i j:ℕ):ℤ)=l i-l j := by
          simp only [binGap,ite_eq_left hj,Int.toNat_of_nonneg (sub_nonneg.mpr (hl hj.le))]
        have hr : (binGap l i j:ℝ)=(l i:ℝ)-(l j:ℝ) := by exact_mod_cast hc
        rw [hr]
        linarith [le_max_left (l i:ℝ) 0,le_max_left (-(l j:ℝ)) 0]
      · simp only [binGap,ite_eq_right hj,Nat.cast_zero]
        positivity
    _ = _ := by simp [Finset.sum_add_distrib,negativeSum]

lemma dyadicRadius_eq_exp (l : ℤ) : dyadicRadius l=Real.exp (-(l:ℝ)*Real.log 2) := by
  rw [dyadicRadius,← Real.rpow_intCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  push_cast
  congr 1
  ring

lemma grouped_bound_eq_exp {d k : ℕ} (l : Fin k → ℤ) (i : Fin k) :
    (5:ℝ)^k*4^(∑ j,binGap l i j)*(3*dyadicRadius (l i))^(((d:ℝ)-1)/2) =
      Real.exp (k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3+
        Real.log 2*(2*(∑ j,(binGap l i j:ℝ))-(((d:ℝ)-1)/2)*(l i:ℝ))) := by
  have h5 : (5:ℝ)^k=Real.exp (k*Real.log 5) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have h4 : (4:ℝ)^(∑ j,binGap l i j)=Real.exp (Real.log 2*(2*∑ j,(binGap l i j:ℝ))) := by
    rw [← Nat.cast_sum,show Real.log 2*(2*(∑ j,binGap l i j:ℕ))=
      (∑ j,binGap l i j:ℕ)*(2*Real.log 2) by ring,Real.exp_nat_mul,
      show 2*Real.log 2=Real.log 2+Real.log 2 by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [h5,h4,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (dyadicRadius_pos _).le,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3),dyadicRadius_eq_exp,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,
    ← Real.exp_add,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

lemma stageExponent_sum {d k : ℕ} (l : Fin k → ℤ) :
    (∑ i,stageExponent (d := d) l i)=totalExponent (d := d) l := by
  simp only [stageExponent,totalExponent,positiveSum,Finset.sum_add_distrib,← Finset.sum_mul,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma measure_stage_le {d k : ℕ} (hd : 1 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (u : Ambient d) (l : Fin k → ℤ) (hl : Monotone l) (i : Fin k)
    (f : Fin k → Ambient d) :
    ν {x | StageEvent u l i (Function.update f i x)}  ≤
      ENNReal.ofReal (Real.exp (stageExponent (d := d) l i)) := by
  have hα : 0 ≤ ((d:ℝ)-1)/2 := by
    have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  simp_rw [stageEvent_update]
  by_cases hi : 0 ≤ l i
  · simp only [hi,forall_true_left]
    have hm := measure_groupedTube_le ν hν u (prefixAxes (translated u f) i)
      (suborthonormal_synth_contraction (prefixAxes_suborthonormal (translated u f) i))
      (binGap l i) (dyadicRadius_pos (l i))
    apply hm.trans
    apply ENNReal.ofReal_le_ofReal
    rw [grouped_bound_eq_exp]
    apply Real.exp_le_exp.mpr
    have hir : 0 ≤ (l i:ℝ) := by exact_mod_cast hi
    unfold stageExponent
    rw [max_eq_left hir]
    have hb := binGap_sum_le l i hl
    rw [max_eq_left hir] at hb
    nlinarith
  · have hir : (l i:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hi)
    simp only [hi,false_implies,ofPred_true,measure_univ]
    have hN := negativeSum_nonneg l
    have hnon : 0 ≤ stageExponent (d := d) l i := by
      unfold stageExponent
      rw [max_eq_right hir,mul_zero,zero_add]
      positivity
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr hnon)

lemma measurableSet_inBins {d k : ℕ} (ε : ℝ) (l : Fin k → ℤ) :
    MeasurableSet {f : Fin k → Ambient d | InBins ε f l} := by
  simp only [InBins,ofPred_forall,ofPred_and]
  apply MeasurableSet.iInter
  intro i
  have hi : Measurable (fun f : Fin k → Ambient d => clippedLength ε f i) :=
    (measurable_gramSchmidt i).norm.max measurable_const
  exact (measurableSet_lt measurable_const hi).inter (measurableSet_le hi measurable_const)

lemma measurableSet_binEvent {d k : ℕ} (ε : ℝ) (u : Ambient d) (l : Fin k → ℤ) :
    MeasurableSet (BinEvent ε u l) :=
  (measurableSet_greedy.inter (measurableSet_inBins ε l)).preimage (measurable_translated u)

lemma measure_binEvent_le {d k : ℕ} (hd : 1 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (ε : ℝ) (u : Ambient d) (l : Fin k → ℤ) :
    (Measure.pi (fun _ : Fin k => ν)) (BinEvent ε u l)  ≤
      ENNReal.ofReal (Real.exp (totalExponent (d := d) l)) := by
  classical
  by_cases hl : Monotone l
  · calc
      _  ≤  (Measure.pi (fun _ : Fin k => ν)) {z | ∀ i,StageEvent u l i z} := by
        apply measure_mono
        intro z hz
        exact greedy_bins_stageEvents u hz.1 hz.2
      _  ≤  ∏ i,ENNReal.ofReal (Real.exp (stageExponent (d := d) l i)) :=
        measure_sequential_event_le ν u k (StageEvent u l) _ (measurableSet_stageEvent u l)
          (stageEvent_prefix u l) (measure_stage_le hd ν hν u l hl)
      _ = ENNReal.ofReal (Real.exp (totalExponent (d := d) l)) := by
        rw [← stageExponent_sum l,Real.exp_sum]
        exact (ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)).symm
  · have he : BinEvent ε u l=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hl (bins_monotone hz.1 hz.2)
    simp [he]

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_ClippedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma tsum_integerWeight : (∑' l : ℤ,integerWeight l)=3 := by
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  simp only [integerWeight,Int.natAbs_natCast,Int.natAbs_neg,
    show ∀ n : ℕ,((n:ℤ)+1).natAbs=n+1 by intro n; omega]
  rw [ENNReal.tsum_geometric,ENNReal.tsum_geometric_add_one]
  norm_num
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  norm_num

lemma tsum_prod_integerWeight : ∀ k : ℕ,(∑' l : Fin k → ℤ,∏ i,integerWeight (l i))=3^k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    let e : (Fin (k+1) → ℤ) ≃ ℤ × (Fin k → ℤ) :=
      { toFun := fun f => (f (Fin.last k),fun i => f i.castSucc)
        invFun := fun p => Fin.snoc p.2 p.1
        left_inv := by
          intro f
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
        right_inv := by intro p; simp }
    rw [← e.symm.tsum_eq]
    change (∑' p : ℤ × (Fin k → ℤ),∏ i,integerWeight (e.symm p i))=3^(k+1)
    have he : ∀ (p : ℤ × (Fin k → ℤ)),
        (∏ i,integerWeight (e.symm p i))=integerWeight p.1*∏ i,integerWeight (p.2 i) := by
      intro p
      simp only [e,Equiv.coe_fn_symm_mk,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
      ring
    simp_rw [he]
    rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin k → ℤ) => integerWeight a*(∏ i,integerWeight (b i)))]
    simp_rw [ENNReal.tsum_mul_left,ih]
    rw [ENNReal.tsum_mul_right,tsum_integerWeight,pow_succ]
    ring

lemma measurable_clippedInverse {d k : ℕ} (ε : ℝ) :
    Measurable (clippedInverse (d := d) (k := k) ε) := by
  apply Finset.measurable_prod
  intro i _
  exact ((measurable_gramSchmidt i).norm.max measurable_const).ennreal_ofReal.inv.pow_const _

lemma clipped_length_inv_le {d k : ℕ} {ε : ℝ} {f : Fin k → Ambient d} {l : Fin k → ℤ}
    (hl : InBins ε f l) (i : Fin k) :
    (ENNReal.ofReal (clippedLength ε f i))⁻¹ ≤
      ENNReal.ofReal (Real.exp (Real.log 2*((l i:ℝ)+1))) := by
  calc
    _ ≤ (ENNReal.ofReal (dyadicRadius (l i+1)))⁻¹ :=
      ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (hl i).1.le)
    _ = _ := by
      rw [← ENNReal.ofReal_inv_of_pos (dyadicRadius_pos _),dyadicRadius_eq_exp,← Real.exp_neg]
      congr 2
      push_cast
      ring

lemma clippedInverse_le_bin {d k : ℕ} {ε : ℝ} {f : Fin k → Ambient d} {l : Fin k → ℤ}
    (hl : InBins ε f l) :
    clippedInverse ε f ≤ ENNReal.ofReal (Real.exp (binInverseExponent l)) := by
  classical
  calc
    _ ≤ ∏ i,ENNReal.ofReal (Real.exp (Real.log 2*((l i:ℝ)+1)))^k :=
      Finset.prod_le_prod' (fun i _ => pow_le_pow_left' (clipped_length_inv_le hl i) k)
    _ = ENNReal.ofReal (Real.exp (∑ i : Fin k,k*(Real.log 2*((l i:ℝ)+1)))) := by
      simp only [Real.exp_sum,Real.exp_nat_mul]
      rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
      apply Finset.prod_congr rfl
      intro i _
      rw [ENNReal.ofReal_pow (by positivity)]
    _ = _ := by
      congr 2
      unfold binInverseExponent
      rw [← sum_bins]
      simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      ring

lemma abs_bins_sum {k : ℕ} (l : Fin k → ℤ) :
    (∑ i,|(l i:ℝ)|)=positiveSum l+negativeSum l := by
  rw [positiveSum,negativeSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (max_zero_add_max_neg_zero_eq_abs_self (l i:ℝ)).symm

lemma integerWeight_eq_exp (l : ℤ) : integerWeight l=
    ENNReal.ofReal (Real.exp (-Real.log 2*|(l:ℝ)|)) := by
  have ha : (l.natAbs:ℝ)=|(l:ℝ)| := by rw [← Int.cast_natCast (R := ℝ),Int.natCast_natAbs,Int.cast_abs]
  have hex : Real.exp (-Real.log 2)=1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  have hhalf : (1/2:ℝ≥0∞)=ENNReal.ofReal (1/2:ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  rw [integerWeight,hhalf]
  rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1
  rw [← hex,← Real.exp_nat_mul,ha]
  congr 1
  ring

lemma prod_integerWeight_eq_exp {k : ℕ} (l : Fin k → ℤ) :
    (∏ i,integerWeight (l i))=ENNReal.ofReal (Real.exp (-Real.log 2*(positiveSum l+negativeSum l))) := by
  simp_rw [integerWeight_eq_exp]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum]
  congr 2
  rw [← Finset.mul_sum,abs_bins_sum]

lemma exponent_small_negative {k : ℕ} {α P N : ℝ} (hk : 3 ≤ k) (hα : 10*k ≤ α)
    (hP : 0 ≤ P) (hN : 0 ≤ N) (hNP : N ≤ 2*P) :
    k*(P-N)+(2*k-α)*P+2*k*N ≤ -(P+N) := by
  have hk' : (3:ℝ) ≤ k := by exact_mod_cast hk
  have h1 := mul_nonneg (sub_nonneg.mpr hα) hP
  have h2 := mul_nonneg (sub_nonneg.mpr hNP) (show 0 ≤ 7*(k:ℝ)-1 by linarith)
  have h3 := mul_nonneg (show 0 ≤ 5*(k:ℝ)-3 by linarith) hN
  nlinarith only [h1,h2,h3]

lemma exponent_large_negative {k : ℕ} {P N : ℝ} (hk : 3 ≤ k)
    (hP : 0 ≤ P) (hNP : 2*P ≤ N) : k*(P-N) ≤ -(P+N) := by
  have hk' : (3:ℝ) ≤ k := by exact_mod_cast hk
  have h1 := mul_nonneg (sub_nonneg.mpr hNP) (show 0 ≤ (k:ℝ)-1 by linarith)
  have h2 := mul_nonneg (show 0 ≤ (k:ℝ)-3 by linarith) hP
  nlinarith

lemma lintegral_bin_clipped_le {d k : ℕ} (hd : 1 ≤ d) (hk : 3 ≤ k)
    (hα : 10*(k:ℝ) ≤ ((d:ℝ)-1)/2) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (ε : ℝ) (u : Ambient d) (l : Fin k → ℤ) :
    (∫⁻ z,(BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z
      ∂Measure.pi (fun _ : Fin k => ν)) ≤
      ENNReal.ofReal (Real.exp (baseExponent d k))*∏ i,integerWeight (l i) := by
  have hfirst : (∫⁻ z,(BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z
      ∂Measure.pi (fun _ : Fin k => ν)) ≤
      ENNReal.ofReal (Real.exp (binInverseExponent l))*(Measure.pi (fun _ : Fin k => ν)) (BinEvent ε u l) := by
    calc
      _ ≤ ∫⁻ z,(BinEvent ε u l).indicator (fun _ => ENNReal.ofReal (Real.exp (binInverseExponent l))) z
          ∂Measure.pi (fun _ : Fin k => ν) := by
        apply lintegral_mono
        intro z
        by_cases hz : z∈BinEvent ε u l
        · simp only [indicator_of_mem hz]
          exact clippedInverse_le_bin hz.2
        · simp only [indicator_of_notMem hz,le_refl]
      _ = _ := by rw [lintegral_indicator (measurableSet_binEvent ε u l),lintegral_const,Measure.restrict_apply_univ]
  have hP := positiveSum_nonneg l
  have hN := negativeSum_nonneg l
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [prod_integerWeight_eq_exp,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  by_cases hNP : negativeSum l ≤ 2*positiveSum l
  · calc
      _ ≤ ENNReal.ofReal (Real.exp (binInverseExponent l))*
          ENNReal.ofReal (Real.exp (totalExponent (d := d) l)) :=
        hfirst.trans (mul_le_mul_right (measure_binEvent_le hd ν hν ε u l) _)
      _ = ENNReal.ofReal (Real.exp (binInverseExponent l+totalExponent (d := d) l)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have he := mul_le_mul_of_nonneg_left (exponent_small_negative hk hα hP hN hNP) hlog
        unfold binInverseExponent totalExponent baseExponent
        nlinarith
  · have hbase : 0 ≤ k*(k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3) := by
      have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
      have ha : 0 ≤ ((d:ℝ)-1)/2 := by linarith
      have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
      positivity
    calc
      _ ≤ ENNReal.ofReal (Real.exp (binInverseExponent l))*1 :=
        hfirst.trans (mul_le_mul_right (prob_le_one (μ := Measure.pi (fun _ : Fin k => ν))) _)
      _ = ENNReal.ofReal (Real.exp (binInverseExponent l)) := mul_one _
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have he := mul_le_mul_of_nonneg_left (exponent_large_negative hk hP (le_of_not_ge hNP)) hlog
        unfold binInverseExponent baseExponent
        nlinarith

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma measurableSet_greedyEvent {d k : ℕ} (u : Ambient d) :
    MeasurableSet (GreedyEvent (k := k) u) := measurableSet_greedy.preimage (measurable_translated u)

lemma lintegral_greedy_clipped_le {d k : ℕ} (hd : 1 ≤ d) (hk : 3 ≤ k)
    (hα : 10*(k:ℝ) ≤ ((d:ℝ)-1)/2) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) {ε : ℝ} (hε : 0 < ε) (u : Ambient d) :
    (∫⁻ z,(GreedyEvent u).indicator (fun z => clippedInverse ε (translated u z)) z
      ∂Measure.pi (fun _ : Fin k => ν)) ≤ ENNReal.ofReal (Real.exp (baseExponent d k))*3^k := by
  classical
  calc
    _ ≤ ∫⁻ z,∑' l : Fin k → ℤ,
        (BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z
        ∂Measure.pi (fun _ : Fin k => ν) := by
      apply lintegral_mono
      intro z
      by_cases hz : z∈GreedyEvent u
      · rw [indicator_of_mem hz]
        obtain ⟨l,hl⟩ := exists_bins hε (translated u z)
        have hzl : z∈BinEvent ε u l := ⟨hz,hl⟩
        have hm := ENNReal.le_tsum (f := fun l : Fin k → ℤ =>
          (BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z) l
        simpa only [indicator_of_mem hzl] using hm
      · simp only [indicator_of_notMem hz]; exact bot_le
    _ = ∑' l : Fin k → ℤ,∫⁻ z,
        (BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z
        ∂Measure.pi (fun _ : Fin k => ν) :=
      lintegral_tsum (fun l => (((measurable_clippedInverse ε).comp (measurable_translated u)).indicator
        (measurableSet_binEvent ε u l)).aemeasurable)
    _ ≤ ∑' l : Fin k → ℤ,ENNReal.ofReal (Real.exp (baseExponent d k))*∏ i,integerWeight (l i) :=
      ENNReal.tsum_le_tsum (lintegral_bin_clipped_le hd hk hα ν hν ε u)
    _ = _ := by rw [ENNReal.tsum_mul_left,tsum_prod_integerWeight]

lemma clippedInverse_eq {d k : ℕ} {ε : ℝ} (hε : 0 < ε) (f : Fin k → Ambient d) :
    clippedInverse ε f=((ENNReal.ofReal (∏ i,clippedLength ε f i))⁻¹)^k := by
  have hi : ∀ i,0 < clippedLength ε f i := fun i => hε.trans_le (le_max_right _ _)
  have hprod : 0 < ∏ i,clippedLength ε f i := Finset.prod_pos (fun i _ => hi i)
  unfold clippedInverse
  simp_rw [← ENNReal.ofReal_inv_of_pos (hi _),← ENNReal.ofReal_pow (inv_nonneg.mpr (hi _).le)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hi i).le) k),Finset.prod_pow,
    Finset.prod_inv_distrib,ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_inv_of_pos hprod]

lemma measurable_rawInverse {d k : ℕ} (u : Ambient d) : Measurable (rawInverse (k := k) u) := by
  have hm : Measurable (fun z : Fin k → Ambient d => ∏ i,‖gramSchmidt ℝ (translated u z) i‖) :=
    Finset.measurable_prod _ (fun i _ => ((measurable_gramSchmidt i).comp (measurable_translated u)).norm)
  change Measurable (fun z : Fin k → Ambient d =>
    ((ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ (translated u z)).det))⁻¹)^k)
  simp_rw [sqrt_gram_det_eq_prod_gramSchmidt]
  exact hm.ennreal_ofReal.inv.pow_const k

lemma tendsto_clippedInverse {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d) :
    Filter.Tendsto (fun L : ℕ => clippedInverse ((1/2:ℝ)^L) (translated u z)) Filter.atTop
      (nhds (rawInverse u z)) := by
  have hε : ∀ L : ℕ,0 < (1/2:ℝ)^L := fun L => pow_pos (by norm_num) _
  have hzero := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  have hi : ∀ i : Fin k,Filter.Tendsto (fun L : ℕ => clippedLength ((1/2:ℝ)^L) (translated u z) i)
      Filter.atTop (nhds ‖gramSchmidt ℝ (translated u z) i‖) := by
    intro i
    have hh := (tendsto_const_nhds (x := ‖gramSchmidt ℝ (translated u z) i‖)).max hzero
    simpa only [clippedLength,max_eq_left (norm_nonneg _)] using hh
  have hp := tendsto_finsetProd Finset.univ (fun i _ => hi i)
  have hinv := (ENNReal.tendsto_ofReal hp).inv
  have hpow := (ENNReal.continuous_pow k).tendsto _ |>.comp hinv
  simpa only [clippedInverse_eq (hε _),rawInverse,sqrt_gram_det_eq_prod_gramSchmidt,Function.comp_def] using hpow

lemma lintegral_greedy_raw_le {d k : ℕ} (hd : 1 ≤ d) (hk : 3 ≤ k)
    (hα : 10*(k:ℝ) ≤ ((d:ℝ)-1)/2) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (u : Ambient d) :
    (∫⁻ z,(GreedyEvent u).indicator (rawInverse u) z ∂Measure.pi (fun _ : Fin k => ν)) ≤
      ENNReal.ofReal (Real.exp (baseExponent d k))*3^k := by
  let F : ℕ → (Fin k → Ambient d) → ℝ≥0∞ := fun L =>
    (GreedyEvent u).indicator (fun z => clippedInverse ((1/2:ℝ)^L) (translated u z))
  have hF : ∀ L,Measurable (F L) := fun L =>
    ((measurable_clippedInverse _).comp (measurable_translated u)).indicator (measurableSet_greedyEvent u)
  have hlim : ∀ z,Filter.Tendsto (fun L => F L z) Filter.atTop
      (nhds ((GreedyEvent u).indicator (rawInverse u) z)) := by
    intro z
    by_cases hz : z∈GreedyEvent u
    · simpa only [F,indicator_of_mem hz] using tendsto_clippedInverse u z
    · simp only [F,indicator_of_notMem hz]
      exact tendsto_const_nhds
  calc
    _ = ∫⁻ z,Filter.liminf (fun L => F L z) Filter.atTop ∂Measure.pi (fun _ : Fin k => ν) :=
      lintegral_congr (fun z => (hlim z).liminf_eq.symm)
    _ ≤ Filter.liminf (fun L => ∫⁻ z,F L z ∂Measure.pi (fun _ : Fin k => ν)) Filter.atTop :=
      lintegral_liminf_le hF
    _ ≤ _ := Filter.liminf_le_of_frequently_le (Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun L => lintegral_greedy_clipped_le hd hk hα ν hν (pow_pos (by norm_num : (0:ℝ)<1/2) L) u)))

lemma rawInverse_perm {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d)
    (π : Equiv.Perm (Fin k)) : rawInverse u (z ∘ π)=rawInverse u z := by
  have hg : Matrix.gram ℝ (translated u (z ∘ π))=
      (Matrix.gram ℝ (translated u z)).submatrix π π := rfl
  unfold rawInverse
  rw [hg,Matrix.det_submatrix_equiv_self]

lemma measurePreserving_permutation {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (π : Equiv.Perm (Fin k)) :
    MeasurePreserving (fun z : Fin k → Ambient d => z ∘ π)
      (Measure.pi (fun _ : Fin k => ν)) (Measure.pi (fun _ : Fin k => ν)) := by
  have hh := MeasurePreserving.symm (MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ambient d) π)
    (measurePreserving_piCongrLeft (fun _ : Fin k => ν) π)
  have he : ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ambient d) π).symm :
      (Fin k → Ambient d) → (Fin k → Ambient d))=(fun z => z ∘ π) := by
    funext z i
    rfl
  simpa only [he] using hh

lemma lintegral_raw_le {d k : ℕ} (hd : 1 ≤ d) (hk : 3 ≤ k)
    (hα : 10*(k:ℝ) ≤ ((d:ℝ)-1)/2) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (u : Ambient d) :
    (∫⁻ z,rawInverse u z ∂Measure.pi (fun _ : Fin k => ν)) ≤
      (k.factorial:ℝ≥0∞)*(ENNReal.ofReal (Real.exp (baseExponent d k))*3^k) := by
  classical
  let F : (Fin k → Ambient d) → ℝ≥0∞ := (GreedyEvent u).indicator (rawInverse u)
  have hF : Measurable F := (measurable_rawInverse u).indicator (measurableSet_greedyEvent u)
  calc
    _ ≤ ∫⁻ z,∑ π : Equiv.Perm (Fin k),F (z ∘ π) ∂Measure.pi (fun _ : Fin k => ν) := by
      apply lintegral_mono
      intro z
      obtain ⟨π,hπ⟩ := exists_greedy_gram_order (translated u z)
      have hz : z ∘ π ∈ GreedyEvent u := hπ
      have he : F (z ∘ π)=rawInverse u z := by
        dsimp only [F]
        rw [indicator_of_mem hz,rawInverse_perm]
      rw [← he]
      exact Finset.single_le_sum (f := fun π : Equiv.Perm (Fin k) => F (z ∘ π)) (fun _ _ => bot_le) (Finset.mem_univ π)
    _ = ∑ π : Equiv.Perm (Fin k),∫⁻ z,F (z ∘ π) ∂Measure.pi (fun _ : Fin k => ν) :=
      lintegral_finsetSum _ (fun π _ => (hF.comp (measurePreserving_permutation ν π).measurable))
    _ = ∑ _π : Equiv.Perm (Fin k),∫⁻ z,F z ∂Measure.pi (fun _ : Fin k => ν) := by
      apply Finset.sum_congr rfl
      intro π _
      exact (measurePreserving_permutation ν π).lintegral_comp hF
    _ ≤ ∑ _π : Equiv.Perm (Fin k),ENNReal.ofReal (Real.exp (baseExponent d k))*3^k :=
      Finset.sum_le_sum (fun _ _ => lintegral_greedy_raw_le hd hk hα ν hν u)
    _ = _ := by simp [Fintype.card_perm,nsmul_eq_mul]

lemma inverse_constants {d k : ℕ} (hd : 1 ≤ d) (hk : k ≤ d) :
    (k.factorial:ℝ≥0∞)*(ENNReal.ofReal (Real.exp (baseExponent d k))*3^k) ≤
      ENNReal.ofReal (Real.exp (20*d*k)) := by
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hkd : (k:ℝ) ≤ d := by exact_mod_cast hk
  have hfact : (k.factorial:ℝ) ≤ Real.exp ((d:ℝ)*k) := by
    calc
      _ ≤ (k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
      _ ≤ (Real.exp (d:ℝ))^k := pow_le_pow_left₀ hk0 (hkd.trans (by linarith [Real.add_one_le_exp (d:ℝ)])) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : (3:ℝ)^k ≤ Real.exp ((2:ℝ)*k) := by
    calc
      _ ≤ (Real.exp 2)^k := pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (2:ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp : (d:ℝ)*k+baseExponent d k+2*k ≤ 20*d*k := by
    have hlog5 : Real.log 5 ≤ 5 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have hlog3 : Real.log 3 ≤ 3 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have hlog2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have ht5 := mul_le_mul_of_nonneg_left hlog5 hk0
    have ht3 := mul_le_mul_of_nonneg_left hlog3 (show 0 ≤ ((d:ℝ)-1)/2 by linarith)
    have ht := mul_le_mul_of_nonneg_left (add_le_add ht5 ht3) hk0
    have ht2 := mul_le_mul_of_nonneg_right hlog2 (sq_nonneg (k:ℝ))
    have hs := mul_le_mul_of_nonneg_right hkd hk0
    have hs1 := mul_le_mul_of_nonneg_right hd1 hk0
    unfold baseExponent
    nlinarith
  have hr : (k.factorial:ℝ)*(Real.exp (baseExponent d k)*3^k) ≤ Real.exp (20*d*k) := by
    calc
      _ ≤ Real.exp ((d:ℝ)*k)*(Real.exp (baseExponent d k)*Real.exp (2*k)) := by
        exact mul_le_mul hfact (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((d:ℝ)*k+baseExponent d k+2*k) := by rw [Real.exp_add,Real.exp_add]; ring
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  have hh := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 3), ENNReal.ofReal_ofNat] using hh

end AllScaleInverseVolume

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Inverse_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem inverse_volume_without_support_oai : InverseVolumeStatement := by
  refine ⟨20,by norm_num,300,?_⟩
  intro d hd ν hprob hν u
  have : IsProbabilityMeasure ν := hprob
  have hd1 : 1 ≤ d := by omega
  have hk3 : 3 ≤ d/100 := by omega
  have hk : d/100 ≤ d := Nat.div_le_self _ _
  have hk100 : 100*(d/100) ≤ d := by omega
  have hα : 10*(d/100:ℕ) ≤ ((d:ℝ)-1)/2 := by
    have hh : 100*(d/100:ℕ) ≤ (d:ℝ) := by exact_mod_cast hk100
    have hd' : (300:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  change (∫⁻ z,rawInverse u z ∂Measure.pi (fun _ : Fin (d/100) => ν)) ≤ _
  exact (lintegral_raw_le hd1 hk3 hα ν hν u).trans (inverse_constants hd1 hk)

end AllScaleInverseVolume

end OAI
end

theorem solution : type_of% @OAI.AllScaleInverseVolume.inverse_volume_without_support_oai := @OAI.AllScaleInverseVolume.inverse_volume_without_support_oai

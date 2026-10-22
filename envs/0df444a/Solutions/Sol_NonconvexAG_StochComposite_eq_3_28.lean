-- Prove2me | solution 1 for NonconvexAG.StochComposite.eq_3_28
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T11:00:56.260443+00:00
-- url     : https://prove2.me/submissions/464946ed-3d69-44ef-8439-8806c1f390a4

/-
Nonexpansiveness of the gradient mapping from the actual convex proximal minimizer property.
Mathematical source: Saeed Ghadimi and Guanghui Lan, arXiv:1310.3787v1, Lemma 4.
Their source credits Proposition 1 of S. Ghadimi, G. Lan and H. Zhang (2013), reference [13].
Platform definitions/statements: mikedeng1; statement review: Shuze Chen.
Alexander Richard Towell (queelius): research direction and contribution stewardship.
OpenAI Codex: substantial formalization, verification and documentation assistance.
Lean/Mathlib contributors: convexity, Euclidean geometry, limits and algebraic tactics.
No claim of new mathematics or independent human review is made.
-/
import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Topology
open Filter GhadimiLan.RSG NonconvexAG.StochComposite

namespace ProxResearch
lemma variational {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    (x y u : E n) (c : ℝ) (hc : 0 < c) (hu : u ∈ K) :
    0 ≤ c * (inner ℝ y (u-P x y c) + X u-X (P x y c)) +
      inner ℝ (P x y c-x) (u-P x y c) := by
  let p := P x y c
  let d := u-p
  let A := c*(inner ℝ y d + X u-X p)+inner ℝ (p-x) d
  let B := ‖d‖^2
  have hp : p ∈ K := (hP x y c hc).1
  have hseg (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : 0 ≤ 2*A+t*B := by
    have hm := (hP x y c hc).2 ((1-t) • p+t • u)
      (hX.1 hp hu (by linarith : 0 ≤ 1-t) ht.le (by ring))
    have hv := hX.2 hp hu (by linarith : 0 ≤ 1-t) ht.le (by ring : (1-t)+t=1)
    have he : (1-t) • p+t • u = p+t • d := by dsimp [d]; module
    have he' : p+t • d-x = (p-x)+t • d := by abel
    rw [he] at hm hv
    simp only [smul_eq_mul] at hv
    rw [he', norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_smul_right, inner_add_right, real_inner_smul_right] at hm
    have hq : 0 ≤ t*(2*A+t*B) := by
      dsimp [A,B]
      field_simp [hc.ne'] at hm
      nlinarith
    exact nonneg_of_mul_nonneg_right hq ht
  have htend : Tendsto (fun t : ℝ => 2*A+t*B) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (2*A)) := by
    have hh : ContinuousAt (fun t : ℝ => 2*A+t*B) 0 := by fun_prop
    simpa using hh.mono_left nhdsWithin_le_nhds
  have hh : 0 ≤ 2*A := ge_of_tendsto htend (by
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1)))] with t ht ht1
    exact hseg t ht ht1)
  change 0 ≤ A
  linarith


lemma prox_lipschitz {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    (x y1 y2 : E n) (c : ℝ) (hc : 0 < c) :
    ‖P x y1 c-P x y2 c‖ ≤ c*‖y1-y2‖ := by
  let p1 := P x y1 c
  let p2 := P x y2 c
  have h1 := variational K X hX P hP x y1 p2 c hc (hP x y2 c hc).1
  have h2 := variational K X hX P hP x y2 p1 c hc (hP x y1 c hc).1
  change 0 ≤ c*(inner ℝ y1 (p2-p1)+X p2-X p1)+inner ℝ (p1-x) (p2-p1) at h1
  change 0 ≤ c*(inner ℝ y2 (p1-p2)+X p1-X p2)+inner ℝ (p2-x) (p1-p2) at h2
  have hf : ‖p1-p2‖^2 ≤ c*inner ℝ (y2-y1) (p1-p2) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at h1 h2 ⊢
    nlinarith [real_inner_comm p1 p2]
  have hcs := real_inner_le_norm (y2-y1) (p1-p2)
  rw [norm_sub_rev y2 y1] at hcs
  have hsq : ‖p1-p2‖^2 ≤ c*‖y1-y2‖*‖p1-p2‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hcs hc.le]
  by_cases he : ‖p1-p2‖=0
  · rw [show P x y1 c-P x y2 c = p1-p2 from rfl,he]; positivity
  · have hp : 0 < ‖p1-p2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    change ‖p1-p2‖ ≤ c*‖y1-y2‖
    nlinarith

end ProxResearch

theorem prior_gradient_mapping {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) :
    ∀ x y1 y2 : E n, ∀ c : ℝ, 0 < c →
      ‖gradMap P x y1 c-gradMap P x y2 c‖ ≤ ‖y1-y2‖ := by
  intro x y1 y2 c hc
  have h := ProxResearch.prox_lipschitz K X hX P hP x y1 y2 c hc
  have he : (x-P x y1 c)-(x-P x y2 c) = -(P x y1 c-P x y2 c) := by abel
  rw [gradMap,gradMap,← smul_sub,he,norm_smul,norm_neg,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1/c)]
  rw [one_div,← div_eq_inv_mul]
  exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using h)
#print axioms ProxResearch.variational
#print axioms ProxResearch.prox_lipschitz
#print axioms prior_gradient_mapping


set_option maxHeartbeats 800000
namespace BatchResearch
lemma prox_joint_lipschitz {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    (x1 y1 x2 y2 : E n) (c : ℝ) (hc : 0 < c) :
    ‖P x1 y1 c-P x2 y2 c‖ ≤ ‖x1-x2‖+c*‖y1-y2‖ := by
  let p1 := P x1 y1 c
  let p2 := P x2 y2 c
  have h1 := ProxResearch.variational K X hX P hP x1 y1 p2 c hc (hP x2 y2 c hc).1
  have h2 := ProxResearch.variational K X hX P hP x2 y2 p1 c hc (hP x1 y1 c hc).1
  change 0 ≤ c*(inner ℝ y1 (p2-p1)+X p2-X p1)+inner ℝ (p1-x1) (p2-p1) at h1
  change 0 ≤ c*(inner ℝ y2 (p1-p2)+X p1-X p2)+inner ℝ (p2-x2) (p1-p2) at h2
  have hf : ‖p1-p2‖^2 ≤ inner ℝ (x1-x2) (p1-p2)+c*inner ℝ (y2-y1) (p1-p2) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at h1 h2 ⊢
    nlinarith [real_inner_comm p1 p2]
  have hx := real_inner_le_norm (x1-x2) (p1-p2)
  have hy := real_inner_le_norm (y2-y1) (p1-p2)
  rw [norm_sub_rev y2 y1] at hy
  by_cases he : ‖p1-p2‖=0
  · change ‖p1-p2‖ ≤ _
    rw [he]; positivity
  · have hp : 0 < ‖p1-p2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    change ‖p1-p2‖ ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hy hc.le]

lemma prox_measurable {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) (c : ℝ) (hc : 0 < c) :
    Measurable (fun p : E n × E n => P p.1 p.2 c) := by
  have hl : LipschitzWith ⟨1+c,by positivity⟩ (fun p : E n × E n => P p.1 p.2 c) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm]
    have h := prox_joint_lipschitz K X hX P hP p.1 p.2 q.1 q.2 c hc
    have hx : ‖p.1-q.1‖ ≤ dist p q := le_max_left _ _
    have hy : ‖p.2-q.2‖ ≤ dist p q := le_max_right _ _
    change ‖P p.1 p.2 c-P q.1 q.2 c‖ ≤ (1+c)*dist p q
    nlinarith [mul_le_mul_of_nonneg_left hy hc.le]
  exact hl.continuous.measurable

lemma batchEnd_mono (m : ℕ → ℕ) : Monotone (batchEnd m) := by
  intro k l h
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl h) (fun _ _ _ => Nat.zero_le _)

lemma batchEnd_succ (m : ℕ → ℕ) (k : ℕ) : batchEnd m (k+1) = batchEnd m k+m (k+1) := by
  unfold batchEnd
  exact Finset.sum_Icc_succ_top (f := m) (a := 1) (b := k) (by omega)

lemma batchOf_index (m : ℕ → ℕ) (k i : ℕ) (hk : 1 ≤ k) (hi : i ∈ Finset.Icc 1 (m k)) :
    batchOf m (batchEnd m (k-1)+i) = k := by
  obtain ⟨hi0,hi1⟩ := Finset.mem_Icc.mp hi
  have he : batchEnd m k = batchEnd m (k-1)+m k := by
    have hk1 : k-1+1=k := by omega
    simpa only [hk1] using batchEnd_succ m (k-1)
  apply IsLeast.csInf_eq
  refine ⟨?_,?_⟩
  · change batchEnd m (k-1)+i ≤ batchEnd m k
    omega
  · intro l hl
    change batchEnd m (k-1)+i ≤ batchEnd m l at hl
    by_contra hh
    have hlk : l ≤ k-1 := by omega
    have hm := batchEnd_mono m hlk
    omega

lemma path_measurable {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → Ξ)
    (hadapt : ∀ s,1 ≤ s → Measurable[ℱ s] (ξ s))
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n) :
    ∀ k, Measurable[ℱ (batchEnd m k)] (fun ω => rsagPath G P α β lam m x0 (fun j => ξ j ω) k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hle := ℱ.mono (batchEnd_mono m (show k ≤ k+1 by omega))
    have hp := ih.mono hle le_rfl
    have hmd : Measurable[ℱ (batchEnd m (k+1))] (fun ω =>
        (1-α (k+1)) • (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).2 +
        α (k+1) • (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).1) :=
      (hp.snd.const_smul (1-α (k+1))).add (hp.fst.const_smul (α (k+1)))
    have hg : Measurable[ℱ (batchEnd m (k+1))] (fun ω =>
        sampleAvg G m (k+1)
          ((1-α (k+1)) • (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).2 +
           α (k+1) • (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).1) (fun j => ξ j ω)) := by
      unfold sampleAvg
      simp only [Nat.add_sub_cancel]
      apply Measurable.const_smul (c := ((m (k+1):ℝ)⁻¹))
      apply Finset.measurable_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hs : batchEnd m k+i ≤ batchEnd m (k+1) := by rw [batchEnd_succ]; omega
      have hx := (hadapt (batchEnd m k+i) (by omega)).mono (ℱ.mono hs) le_rfl
      exact hG.comp (hmd.prodMk hx)
    exact ((prox_measurable K X hX P hP _ (hstep.2.2.2.1 _ (by omega))).comp (hp.fst.prodMk hg)).prodMk
      ((prox_measurable K X hX P hP _ (hstep.2.2.1 _ (by omega))).comp (hmd.prodMk hg))

#print axioms prox_joint_lipschitz
#print axioms batchOf_index
#print axioms path_measurable
end BatchResearch

namespace MartingaleVariance
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma inner_integrable {μ : Measure Ω} {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => ⟪f ω,g ω⟫_ℝ) μ := by
  exact (hf.norm.integrable_mul hg.norm).mono' (hf.1.inner hg.1)
    (Filter.Eventually.of_forall fun ω => norm_inner_le_norm (f ω) (g ω))
lemma orthogonal (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (f g : Ω → E) (hf : StronglyMeasurable[m] f) (hf2 : MemLp f 2 μ)
    (hg2 : MemLp g 2 μ) (hg : Integrable g μ)
    (hz : μ[g|m] =ᵐ[μ] fun _ => 0) : (∫ ω, ⟪f ω,g ω⟫_ℝ ∂μ) = 0 := by
  let : MeasurableSpace Ω := mΩ
  have h := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hf (inner_integrable hf2 hg2) hg
  change μ[fun ω => ⟪f ω,g ω⟫_ℝ|m] =ᵐ[μ] fun ω => ⟪f ω, μ[g|m] ω⟫_ℝ at h
  have he : μ[fun ω => ⟪f ω,g ω⟫_ℝ|m] =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [h,hz] with ω hω hzω
    simpa only [hzω,inner_zero_right] using hω
  rw [← integral_condExp hm, integral_congr_ae he]
  simp
end MartingaleVariance


namespace BatchResearch
lemma batch_moments {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (O : ℕ → Ω → E n) (H : Ω → E n) (S N : ℕ) (hN : 1 ≤ N) (σ : ℝ)
    (hH : StronglyMeasurable[ℱ S] H)
    (hO : ∀ i ∈ Finset.Icc 1 N, StronglyMeasurable[ℱ (S+i)] (O i))
    (hiO : ∀ i ∈ Finset.Icc 1 N, Integrable (O i) μ)
    (hu : ∀ i ∈ Finset.Icc 1 N, μ[O i | ℱ (S+i-1)] =ᵐ[μ] H)
    (hiV : ∀ i ∈ Finset.Icc 1 N, Integrable (fun ω => ‖O i ω-H ω‖^2) μ)
    (hV : ∀ i ∈ Finset.Icc 1 N, (∫ ω, ‖O i ω-H ω‖^2 ∂μ) ≤ σ^2) :
    Integrable (fun ω => (N:ℝ)⁻¹ • ∑ i ∈ Finset.Icc 1 N, O i ω) μ ∧
    μ[(fun ω => (N:ℝ)⁻¹ • ∑ i ∈ Finset.Icc 1 N, O i ω) | ℱ S] =ᵐ[μ] H ∧
    Integrable (fun ω => ‖(N:ℝ)⁻¹ • ∑ i ∈ Finset.Icc 1 N, O i ω-H ω‖^2) μ ∧
    (∫ ω, ‖(N:ℝ)⁻¹ • ∑ i ∈ Finset.Icc 1 N, O i ω-H ω‖^2 ∂μ) ≤ σ^2/(N:ℝ) := by
  classical
  let T := Finset.Icc 1 N
  have h1 : 1 ∈ T := by simp [T,hN]
  have hiH : Integrable H μ := integrable_condExp.congr (hu 1 h1)
  let D : ℕ → Ω → E n := fun i ω => O i ω-H ω
  have hD (i) (hi : i ∈ T) : MemLp (D i) 2 μ :=
    (memLp_two_iff_integrable_sq_norm ((hiO i hi).sub hiH).1).2 (hiV i hi)
  have hz (i) (hi : i ∈ T) : μ[D i | ℱ (S+i-1)] =ᵐ[μ] fun _ => 0 := by
    have hii := (Finset.mem_Icc.mp hi).1
    have hHH := hH.mono (ℱ.mono (show S ≤ S+i-1 by omega))
    have h := condExp_sub (hiO i hi) hiH (ℱ (S+i-1))
    rw [condExp_of_stronglyMeasurable (ℱ.le _) hHH hiH] at h
    filter_upwards [h,hu i hi] with ω hω huω
    change μ[D i | ℱ (S+i-1)] ω = 0
    simpa only [Pi.sub_apply,Pi.sub_def,D,huω,sub_self] using hω
  have hort (i) (hi : i ∈ T) (j) (hj : j ∈ T) (hij : i<j) :
      (∫ ω, inner ℝ (D i ω) (D j ω) ∂μ)=0 := by
    have hh : StronglyMeasurable[ℱ (S+j-1)] (D i) :=
      ((hO i hi).mono (ℱ.mono (by omega))).sub (hH.mono (ℱ.mono (by omega)))
    exact MartingaleVariance.orthogonal μ (ℱ.le _) _ _ hh (hD i hi) (hD j hj)
      ((hiO j hj).sub hiH) (hz j hj)
  have hpair (i) (hi : i ∈ T) (j) (hj : j ∈ T) :=
    MartingaleVariance.inner_integrable (hD i hi) (hD j hj)
  have hsum := memLp_finsetSum T (fun i hi => hD i hi)
  have hsumI : Integrable (fun ω => ‖∑ i ∈ T,D i ω‖^2) μ :=
    hsum.integrable_norm_pow (by decide)
  have hexact : (∫ ω, ‖∑ i ∈ T,D i ω‖^2 ∂μ) = ∑ i ∈ T, ∫ ω, ‖D i ω‖^2 ∂μ := by
    simp_rw [← real_inner_self_eq_norm_sq,sum_inner,inner_sum]
    rw [integral_finsetSum T (fun i hi => integrable_finsetSum T (fun j hj => hpair i hi j hj))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum T (fun j hj => hpair i hi j hj),Finset.sum_eq_single i]
    · intro j hj hji
      rcases lt_or_gt_of_ne hji with h|h
      · convert hort j hj i hi h using 1
        simp only [real_inner_comm]
      · exact hort i hi j hj h
    · intro h
      exact (h hi).elim
  have hvsum : (∫ ω, ‖∑ i ∈ T,D i ω‖^2 ∂μ) ≤ (N:ℝ)*σ^2 := by
    rw [hexact]
    have h := Finset.sum_le_sum (fun i hi => hV i hi)
    simpa [T] using h
  have hnR : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have herr (ω) : (N:ℝ)⁻¹ • ∑ i ∈ T,O i ω-H ω = (N:ℝ)⁻¹ • ∑ i ∈ T,D i ω := by
    simp only [D,Finset.sum_sub_distrib,smul_sub,Finset.sum_const]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    simp [T,smul_smul,hnR]
  have hnorm (ω) : ‖(N:ℝ)⁻¹ • ∑ i ∈ T,O i ω-H ω‖^2 = (N:ℝ)⁻¹^2*‖∑ i ∈ T,D i ω‖^2 := by
    rw [herr,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  refine ⟨(integrable_finsetSum T (fun i hi => hiO i hi)).smul ((N:ℝ)⁻¹),?_,?_,?_⟩
  · have hmean (i) (hi : i ∈ T) : μ[O i|ℱ S] =ᵐ[μ] H := by
      have hii := (Finset.mem_Icc.mp hi).1
      have ht := (condExp_condExp_of_le (μ := μ) (f := O i)
        (ℱ.mono (show S ≤ S+i-1 by omega)) (ℱ.le (S+i-1))).symm
      exact ht.trans ((condExp_congr_ae (hu i hi)).trans (by rw [condExp_of_stronglyMeasurable (ℱ.le S) hH hiH]))
    have hs := condExp_finsetSum (s := T) (fun i hi => hiO i hi) (ℱ S)
    have hh : μ[(∑ i ∈ T,O i)|ℱ S] =ᵐ[μ] ∑ i ∈ T,H := by
      apply hs.trans
      have hall := (Filter.eventually_all_finset T).mpr hmean
      filter_upwards [hall] with ω hω
      simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun i hi => hω i hi)
    have hc := condExp_smul (μ := μ) ((N:ℝ)⁻¹) (∑ i ∈ T,O i) (ℱ S)
    have h := hc.trans (hh.const_smul _)
    simp only [Finset.sum_const,← Nat.cast_smul_eq_nsmul ℝ,smul_smul] at h
    simpa [T,Finset.sum_fn,Pi.smul_def,hnR] using h
  · change Integrable (fun ω => ‖(N:ℝ)⁻¹ • ∑ i ∈ T,O i ω-H ω‖^2) μ
    simp_rw [hnorm]
    exact hsumI.const_mul ((N:ℝ)⁻¹^2)
  · change (∫ ω, ‖(N:ℝ)⁻¹ • ∑ i ∈ T,O i ω-H ω‖^2 ∂μ) ≤ _
    simp_rw [hnorm]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hvsum (sq_nonneg (N:ℝ)⁻¹)
    convert hh using 1 <;> try rfl
    field_simp [hnR]
    <;> ring

#print axioms batch_moments
end BatchResearch

open ConvexOptAlg.SmoothGD

theorem solution {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ gΨ G ξ (querySeq G P α β lam m x0 ξ) σ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let Gb : ℕ → Ω → E n := Gbar G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ k, 1 ≤ k →
      Integrable (Gb k) μ ∧
      μ[Gb k | ℱ (batchEnd m (k - 1))] =ᵐ[μ] (fun ω => gΨ (xmd k ω)) ∧
      Integrable (fun ω => ‖δ k ω‖ ^ 2) μ ∧
      ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ≤ σ ^ 2 / (m k : ℝ) := by
  dsimp only
  intro k hk
  let S := batchEnd m (k-1)
  let H : Ω → E n := fun ω => gΨ (xmdSeq G P α β lam m x0 ξ k ω)
  let O : ℕ → Ω → E n := fun i ω => G (xmdSeq G P α β lam m x0 ξ k ω) (ξ (S+i) ω)
  have hm : 1 ≤ m k := hstep.2.2.2.2 k hk
  have hp := BatchResearch.path_measurable K X hX P hP G hG ℱ ξ hA1.adapted α β lam m hstep x0 (k-1)
  have hmd : Measurable[ℱ S] (xmdSeq G P α β lam m x0 ξ k) :=
    (hp.snd.const_smul (1-α k)).add (hp.fst.const_smul (α k))
  have hgf : LipschitzWith ⟨Lf,hf.1⟩ gf := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gf x-gf y‖ ≤ Lf*‖x-y‖
    exact hf.2.2 x y
  have hgh : LipschitzWith ⟨Lh,hh.1⟩ gh := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gh x-gh y‖ ≤ Lh*‖x-y‖
    exact hh.2.2 x y
  have hgrad : Measurable gΨ := by
    rw [hgΨ]
    exact hgf.continuous.measurable.add hgh.continuous.measurable
  have hH : StronglyMeasurable[ℱ S] H := (hgrad.comp hmd).stronglyMeasurable
  have hidx (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) :
      querySeq G P α β lam m x0 ξ (S+i) = xmdSeq G P α β lam m x0 ξ k := by
    funext ω
    simp only [querySeq,S,BatchResearch.batchOf_index m k i hk hi]
  have hO (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : StronglyMeasurable[ℱ (S+i)] (O i) := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    exact (hG.comp ((hmd.mono (ℱ.mono (Nat.le_add_right S i)) le_rfl).prodMk
      (hA1.adapted (S+i) (by omega)))).stronglyMeasurable
  have hiO (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : Integrable (O i) μ := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    have h := hA1.integrable_oracle (S+i) (by omega)
    simpa only [hidx i hi] using h
  have hu (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : μ[O i | ℱ (S+i-1)] =ᵐ[μ] H := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    have h := hA1.unbiased (S+i) (by omega)
    simpa only [hidx i hi] using h
  have hiV (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : Integrable (fun ω => ‖O i ω-H ω‖^2) μ := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    have h := hA1.integrable_sq_error (S+i) (by omega)
    simpa only [hidx i hi] using h
  have hV (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : (∫ ω, ‖O i ω-H ω‖^2 ∂μ) ≤ σ^2 := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    have h := hA1.variance_bound (S+i) (by omega)
    simpa only [hidx i hi] using h
  have hres := BatchResearch.batch_moments μ ℱ O H S (m k) hm σ hH hO hiO hu hiV hV
  convert hres using 1 <;> rfl

#print axioms solution

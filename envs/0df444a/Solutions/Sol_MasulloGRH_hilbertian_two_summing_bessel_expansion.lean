-- Prove2me | solution 1 for MasulloGRH.hilbertian_two_summing_bessel_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:41:43.227083+00:00
-- url     : https://prove2.me/submissions/26c144c9-4f6d-4f51-8d39-315145428c05

import Definitions.Def_MasulloGRH_LocallyConvex

open MasulloGRH Function Filter Topology UniformSpace Set
open scoped ENNReal
universe u

-- Keep the original topology on E while giving a second copy the pseudonorm p.
private def SeminormModel {E : Type*} [AddCommGroup E] [Module ℂ E] (_ : Seminorm ℂ E) := E

private noncomputable instance modelGroup {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) : SeminormedAddCommGroup (SeminormModel p) := p.toAddGroupSeminorm.toSeminormedAddCommGroup

private noncomputable instance modelSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) : NormedSpace ℂ (SeminormModel p) :=
  { (inferInstance : Module ℂ E) with norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }


-- Control a two-summing operator on finite orthonormal families in a dense completion.
private theorem sum_on_ortho {E K H : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : E →ₗ[ℂ] K) (hd : DenseRange j) (T : K →L[ℂ] H)
    (hs : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ F : StrongDual ℂ K, ‖F‖ ≤ 1 → ∑ i, ‖F (j (x i))‖^2 ≤ c) →
      ∑ i, ‖T (j (x i))‖^2 ≤ c)
    {n : ℕ} (v : Fin n → K) (hv : Orthonormal ℂ v) : ∑ i, ‖T (v i)‖^2 ≤ 1 := by
  let δ (k : ℕ) : ℝ := (1 / 2 : ℝ)^k
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  choose x hx using fun k i => Metric.denseRange_iff.mp hd (v i) (δ k) (hδ k)
  have hxlim (i : Fin n) : Tendsto (fun k => j (x k i)) atTop (𝓝 (v i)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hδlim
    exact (dist_comm _ _).trans_le (hx k i).le
  have hweak (k : ℕ) (F : StrongDual ℂ K) (hF : ‖F‖ ≤ 1) :
      ∑ i, ‖F (j (x k i))‖^2 ≤ 1 + n * (2*δ k+(δ k)^2) := by
    let z := (InnerProductSpace.toDual ℂ K).symm F
    have hsum : ∑ i, ‖F (v i)‖^2 ≤ 1 := by
      have hbess := hv.sum_inner_products_le (s := Finset.univ) z
      have hid (i : Fin n) : ‖inner ℂ (v i) z‖ = ‖F (v i)‖ := by
        rw [norm_inner_symm]; exact congrArg norm InnerProductSpace.toDual_symm_apply
      simp_rw [hid] at hbess
      have hz : ‖z‖ = ‖F‖ := (InnerProductSpace.toDual ℂ K).symm.norm_map F
      rw [hz] at hbess
      exact hbess.trans (by nlinarith [norm_nonneg F])
    have hver (i : Fin n) : ‖F (j (x k i))‖^2 ≤ ‖F (v i)‖^2 + (2*δ k+(δ k)^2) := by
      have hi1 : ‖F (v i)‖ ≤ 1 := by
        simpa [hv.norm_eq_one i] using F.le_of_opNorm_le hF (v i)
      have hi2 : ‖F (j (x k i)) - F (v i)‖ ≤ δ k := by
        rw [← map_sub]
        have h := F.le_of_opNorm_le hF (j (x k i)-v i)
        rw [one_mul] at h
        exact h.trans (by simpa only [← dist_eq_norm,dist_comm] using (hx k i).le)
      have hi3 : ‖F (j (x k i))‖ ≤ ‖F (v i)‖ + δ k :=
        by
        have h := norm_le_norm_add_norm_sub (F (v i)) (F (j (x k i)))
        rw [norm_sub_rev] at h
        linarith
      have hi4 := pow_le_pow_left₀ (norm_nonneg _) hi3 2
      nlinarith [mul_le_mul_of_nonneg_right hi1 (hδ k).le]
    exact (Finset.sum_le_sum (fun i _ => hver i)).trans (by
      rw [Finset.sum_add_distrib, Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      exact add_le_add_left hsum _)
  have hleft : Tendsto (fun k => ∑ i, ‖T (j (x k i))‖^2) atTop (𝓝 (∑ i, ‖T (v i)‖^2)) :=
    tendsto_finsetSum _ (fun i _ => ((T.continuous.tendsto _).comp (hxlim i)).norm.pow 2)
  have hright : Tendsto (fun k => 1 + n * (2*δ k+(δ k)^2)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      (((hδlim.const_mul 2).add (hδlim.pow 2)).const_mul (n : ℝ))
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun k => hs n (x k) _ (hweak k))

private theorem summable_basis_image {E K H ι : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : E →ₗ[ℂ] K) (hd : DenseRange j) (T : K →L[ℂ] H)
    (hs : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ F : StrongDual ℂ K, ‖F‖ ≤ 1 → ∑ i, ‖F (j (x i))‖^2 ≤ c) →
      ∑ i, ‖T (j (x i))‖^2 ≤ c)
    (e : HilbertBasis ι ℂ K) : Summable fun i => ‖T (e i)‖^2 := by
  classical
  apply summable_of_sum_le (fun i => sq_nonneg _) (c := 1)
  intro S
  let b := S.equivFin.symm
  have ho : Orthonormal ℂ (fun k => e (b k : ι)) := e.orthonormal.comp _ (Subtype.val_injective.comp b.injective)
  have h := sum_on_ortho j hd T hs _ ho
  simpa only [← Finset.sum_coe_sort S] using (b.sum_comp (fun i : S => ‖T (e (i : ι))‖^2)).symm.trans_le h
@[instance_reducible] private noncomputable def hilbert_of_seminorm {E : Type*} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E)
    (hpar : ∀ x y, q (x+y)^2 + q (x-y)^2 = 2*q x^2 + 2*q y^2) :
    InnerProductSpace ℂ (Completion (SeminormModel q)) := by
  apply InnerProductSpace.ofNorm
  intro x y
  refine Completion.induction_on₂ (p := fun x y : Completion (SeminormModel q) =>
    ‖x+y‖*‖x+y‖ + ‖x-y‖*‖x-y‖ = 2*(‖x‖*‖x‖ + ‖y‖*‖y‖)) x y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a b
  rw [← Completion.coe_add,← Completion.coe_sub]
  simp only [Completion.norm_coe]
  let forget : SeminormModel q → E := id
  change q (forget a + forget b) * q (forget a + forget b) +
    q (forget a - forget b) * q (forget a - forget b) =
    2 * (q (forget a) * q (forget a) + q (forget b) * q (forget b))
  simpa only [sq,mul_add] using hpar (forget a) (forget b)

private theorem seminorm_le_of_two_summing {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p q : Seminorm ℂ E) (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖^2 ≤ c) → ∑ i, p (x i)^2 ≤ c) :
    ∀ x, p x ≤ q x := by
  intro x
  have h := hAS 1 (fun _ => x) (q x ^ 2) (fun f hf => by simpa using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
  simp only [Fin.sum_univ_one] at h
  nlinarith [apply_nonneg p x,apply_nonneg q x]

private theorem extension_squared_summable {E K H ι : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (p q : Seminorm ℂ E)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖^2 ≤ c) → ∑ i, p (x i)^2 ≤ c)
    (j : E →ₗ[ℂ] K) (hd : DenseRange j) (hj : ∀ x, ‖j x‖ = q x)
    (u : E →ₗ[ℂ] H) (hu : ∀ x, ‖u x‖ ≤ p x) (e : HilbertBasis ι ℂ K) :
    ∃ T : K →L[ℂ] H, (∀ x, T (j x) = u x) ∧ Summable (fun i => ‖T (e i)‖^2) := by
  have hle := seminorm_le_of_two_summing p q hAS
  have hcmp (x : E) : ‖u x‖ ≤ 1 * ‖j x‖ := by rw [one_mul,hj]; exact (hu x).trans (hle x)
  let T := u.extendOfNorm j
  have heq (x : E) : T (j x) = u x := LinearMap.extendOfNorm_eq hd ⟨1,hcmp⟩ x
  refine ⟨T,heq,summable_basis_image j hd T (fun n x c h => ?_) e⟩
  simp only [heq]
  refine (Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hu (x i)) 2)).trans (hAS n x c ?_)
  intro f hf
  have hcmp' (y : E) : ‖f.toLinearMap y‖ ≤ 1 * ‖j y‖ := by rw [one_mul,hj]; exact hf y
  let F := f.toLinearMap.extendOfNorm j
  have hF : ‖F‖ ≤ 1 := LinearMap.opNorm_extendOfNorm_le hd zero_le_one hcmp'
  have hFj (y : E) : F (j y) = f y := LinearMap.extendOfNorm_eq hd ⟨1,hcmp'⟩ y
  simpa only [hFj] using h F hF
private theorem continuous_of_seminorm_bound {E H : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [SeminormedAddCommGroup H] [NormedSpace ℂ H]
    (p : Seminorm ℂ E) (hp : Continuous p) (u : E →ₗ[ℂ] H) (hu : ∀ x, ‖u x‖ ≤ p x) :
    Continuous u := by
  apply continuous_of_continuousAt_zero u
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(hp.tendsto 0).eventually_lt_const (show p 0 < ε by simpa using hε)] with x hx
  simpa using (hu x).trans_lt hx

private theorem reindex_bessel {E ι : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p q : Seminorm ℂ E) (f : ι → StrongDual ℂ E) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable fun i => c i ^ 2)
    (hf : ∀ x, Summable (fun i => ‖f i x‖^2) ∧ ∑' i, ‖f i x‖^2 ≤ q x ^ 2)
    (hd : ∀ x, p x ≤ ∑' i, c i * ‖f i x‖) :
    ∃ (g : ℕ → StrongDual ℂ E) (d : ℕ → ℝ), (∀ n, 0 ≤ d n) ∧ Summable (fun n => d n^2) ∧
      (∀ x, Summable (fun n => ‖g n x‖^2) ∧ ∑' n, ‖g n x‖^2 ≤ q x^2) ∧
      ∀ x, p x ≤ ∑' n, d n * ‖g n x‖ := by
  classical
  let S := Function.support (fun i => c i ^ 2)
  let : Countable S := hs.countable_support
  obtain ⟨j,hj⟩ := exists_injective_nat S
  let d : ℕ → ℝ := Function.extend j (fun a : S => c a) 0
  let g : ℕ → StrongDual ℂ E := Function.extend j (fun a : S => f a) 0
  have dj (a : S) : d (j a) = c a := hj.extend_apply _ _ _
  have gj (a : S) : g (j a) = f a := hj.extend_apply _ _ _
  have d0 {n : ℕ} (hn : n ∉ Set.range j) : d n = 0 := Function.extend_apply' _ _ _ hn
  have g0 {n : ℕ} (hn : n ∉ Set.range j) : g n = 0 := Function.extend_apply' _ _ _ hn
  have hext (z : ℕ → ℝ) (t : S → ℝ) (hin : ∀ i, z (j i) = t i)
      (hout : ∀ n ∉ Set.range j, z n = 0) : z = Function.extend j t 0 := by
    funext n
    by_cases hn : n ∈ Set.range j
    · obtain ⟨a,rfl⟩ := hn; rw [hin,hj.extend_apply]
    · rw [hout n hn,Function.extend_apply' _ _ _ hn]; rfl
  have hd2 := hext (fun n => d n^2) (fun i : S => c i ^ 2)
    (fun i => by rw [dj]) (fun n hn => by rw [d0 hn]; norm_num)
  refine ⟨g,d,fun n => ?_,hd2 ▸ (summable_extend_zero hj).mpr (hs.subtype S),fun x => ?_,fun x => ?_⟩
  · by_cases hn : n ∈ Set.range j
    · obtain ⟨a,rfl⟩ := hn; rw [dj]; exact hc _
    · rw [d0 hn]
  · have hg2 := hext (fun n => ‖g n x‖^2) (fun a : S => ‖f a x‖^2)
      (fun a => by rw [gj]) (fun n hn => by rw [g0 hn]; simp)
    rw [hg2,summable_extend_zero hj,tsum_extend_zero hj]
    refine ⟨(hf x).1.subtype S,?_⟩
    exact ((hf x).1.tsum_subtype_le _ S (fun _ => sq_nonneg _)).trans (hf x).2
  · apply (hd x).trans_eq
    let t (i : ι) := c i * ‖f i x‖
    have ht : Function.support t ⊆ S := by
      intro i hi hzero
      change (c i)^2 = 0 at hzero
      exact hi (by simp [t,show c i=0 by simpa using hzero])
    have he := hext (fun n => d n * ‖g n x‖) (fun a : S => t a)
      (fun a => by rw [dj,gj]) (fun n hn => by rw [d0 hn,zero_mul])
    rw [he,tsum_extend_zero hj]
    exact (tsum_subtype_eq_of_support_subset ht).symm

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (h₁ h₂ h₃ : Seminorm ℂ E) (hc₃ : Continuous h₃) (h₂₃ : ∀ x, h₂ x ≤ h₃ x)
    (hpar₁ : ∀ x y, h₁ (x + y) ^ 2 + h₁ (x - y) ^ 2 = 2 * h₁ x ^ 2 + 2 * h₁ y ^ 2)
    (hpar₂ : ∀ x y, h₂ (x + y) ^ 2 + h₂ (x - y) ^ 2 = 2 * h₂ x ^ 2 + 2 * h₂ y ^ 2)
    (h₁₂ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₂ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₁ (x i) ^ 2 ≤ c) :
    ∃ (g : ℕ → StrongDual ℂ E) (b : ℕ → ℝ), (∀ k, 0 ≤ b k) ∧ Summable (fun k => b k ^ 2) ∧
      (∀ x, Summable (fun k => ‖g k x‖ ^ 2) ∧ ∑' k, ‖g k x‖ ^ 2 ≤ h₂ x ^ 2) ∧
      ∀ x, h₁ x ≤ ∑' k, b k * ‖g k x‖ := by
  obtain ⟨ι,_,P,hP⟩ := hE.1
  let := hP.topologicalAddGroup
  let X := SeminormModel h₂
  let K := Completion X
  let := hilbert_of_seminorm h₂ hpar₂
  let idX : E →ₗ[ℂ] X := LinearMap.id
  let j : E →ₗ[ℂ] K := (Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap.comp idX
  have hj (x : E) : ‖j x‖ = h₂ x := Completion.norm_coe (idX x)
  let J : E →L[ℂ] K := ⟨j,continuous_of_seminorm_bound h₃ hc₃ j (fun x => (hj x).trans_le (h₂₃ x))⟩
  let Y := SeminormModel h₁
  let H := Completion Y
  let idY : E →ₗ[ℂ] Y := LinearMap.id
  let u : E →ₗ[ℂ] H := (Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap.comp idY
  have hu (x : E) : ‖u x‖ = h₁ x := Completion.norm_coe (idY x)
  obtain ⟨ι,e,_⟩ := exists_hilbertBasis ℂ K
  obtain ⟨T,hT,hs⟩ := extension_squared_summable h₁ h₂ h₁₂ j (Completion.denseRange_coe (α := X))
    hj u (fun x => (hu x).le) e
  let g (i : ι) : StrongDual ℂ E := (innerSL ℂ (e i)).comp J
  have hg (i : ι) (x : E) : g i x = e.repr (j x) i := (e.repr_apply_apply _ _).symm
  have hgs (x : E) : HasSum (fun i => ‖g i x‖ ^ 2) ((h₂ x)^2) := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) (e.repr (j x))
    simpa [hg,hj] using h
  refine reindex_bessel h₁ h₂ g (fun i => ‖T (e i)‖) (fun _ => norm_nonneg _) hs
    (fun x => ⟨(hgs x).summable,(hgs x).tsum_eq.le⟩) (fun x => ?_)
  let b (i : ι) := ‖T (e i)‖ * ‖g i x‖
  have hb : Summable b := Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun i => show b i ≤ ‖T (e i)‖^2 + ‖g i x‖^2 by dsimp [b]; nlinarith [sq_nonneg (‖T (e i)‖-‖g i x‖),sq_nonneg ‖T (e i)‖,sq_nonneg ‖g i x‖])
    (hs.add (hgs x).summable)
  rw [← hu,← hT]
  exact (T.hasSum (e.hasSum_repr (j x))).norm_le_of_bounded hb.hasSum (fun i => by
    rw [map_smul,norm_smul]; dsimp [b]; rw [hg,mul_comm])

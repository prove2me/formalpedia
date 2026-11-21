-- Prove2me | solution 1 for MasulloGRH.two_summing_dual_hilbertSchmidt_weights
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:41:19.748678+00:00
-- url     : https://prove2.me/submissions/01a1992b-de95-4dfb-9877-329cc9956de8

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
private noncomputable def ltwo_of_summable {E : Type*} [AddCommGroup E] [Module ℂ E]
    (g : ℕ → E →ₗ[ℂ] ℂ) (hg : ∀ x, Summable fun k => ‖g k x‖^2) :
    E →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  toFun x := ⟨fun k => g k x,memℓp_gen (by simpa using hg x)⟩
  map_add' x y := by ext k; exact map_add (g k) x y
  map_smul' a x := by ext k; exact map_smul (g k) a x

private theorem parseval_functional {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (e : HilbertBasis ι ℂ K) (f : StrongDual ℂ K) :
    HasSum (fun i => ‖f (e i)‖^2) (‖f‖^2) := by
  let z := (InnerProductSpace.toDual ℂ K).symm f
  have h := lp.hasSum_norm (p := 2) (by norm_num) (e.repr z)
  have heq (i : ι) : ‖e.repr z i‖ = ‖f (e i)‖ := by
    rw [e.repr_apply_apply,norm_inner_symm]
    exact congrArg norm InnerProductSpace.toDual_symm_apply
  have hnorm : ‖z‖ = ‖f‖ := (InnerProductSpace.toDual ℂ K).symm.norm_map f
  simpa [heq,hnorm] using h

private theorem summable_coordinate_norm_sq {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (e : HilbertBasis ι ℂ K)
    (A : K →L[ℂ] lp (fun _ : ℕ => ℂ) 2) (hA : Summable (fun i => ‖A (e i)‖^2)) :
    Summable (fun k => ‖(lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 k).comp A‖^2) := by
  let T (k : ℕ) := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 k).comp A
  let m (t : ι × ℕ) := ‖T t.2 (e t.1)‖^2
  have hrow (i : ι) : HasSum (fun k => m (i,k)) (‖A (e i)‖^2) := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) (A (e i))
    change HasSum (fun k => ‖(A (e i)) k‖^2) (‖A (e i)‖^2)
    simpa using h
  have hm : Summable m := (summable_prod_of_nonneg (fun t => sq_nonneg _)).mpr
    ⟨fun i => (hrow i).summable,by
      change Summable (fun i => ∑' k, m (i,k))
      simp_rw [(hrow _).tsum_eq]
      exact hA⟩
  have hcol (k : ℕ) : ∑' i, m (i,k) = ‖T k‖^2 := (parseval_functional e (T k)).tsum_eq
  simpa only [Prod.swap_prod_mk,hcol] using hm.prod_symm.prod

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (h₂ h₃ : Seminorm ℂ E) (hc₃ : Continuous h₃)
    (hpar₂ : ∀ x y, h₂ (x + y) ^ 2 + h₂ (x - y) ^ 2 = 2 * h₂ x ^ 2 + 2 * h₂ y ^ 2)
    (hpar₃ : ∀ x y, h₃ (x + y) ^ 2 + h₃ (x - y) ^ 2 = 2 * h₃ x ^ 2 + 2 * h₃ y ^ 2)
    (h₂₃ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₃ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₂ (x i) ^ 2 ≤ c)
    (g : ℕ → StrongDual ℂ E)
    (hg : ∀ x, Summable (fun k => ‖g k x‖ ^ 2) ∧ ∑' k, ‖g k x‖ ^ 2 ≤ h₂ x ^ 2) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧ Summable (fun k => a k ^ 2) ∧
      ∀ k x, ‖g k x‖ ≤ a k * h₃ x := by
  let X := SeminormModel h₃
  let K := Completion X
  let := hilbert_of_seminorm h₃ hpar₃
  let idX : E →ₗ[ℂ] X := LinearMap.id
  let j : E →ₗ[ℂ] K := (Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap.comp idX
  have hd : DenseRange j := Completion.denseRange_coe (α := X)
  have hj (x : E) : ‖j x‖ = h₃ x := Completion.norm_coe (idX x)
  let u := ltwo_of_summable (fun k => (g k).toLinearMap) (fun x => (hg x).1)
  have hu (x : E) : ‖u x‖ ≤ h₂ x := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) (u x)
    have heq : ∑' k, ‖g k x‖^2 = ‖u x‖^2 := by simpa [u,ltwo_of_summable] using h.tsum_eq
    have hx := (hg x).2
    rw [heq] at hx
    nlinarith [apply_nonneg h₂ x,norm_nonneg (u x)]
  obtain ⟨ι,e,_⟩ := exists_hilbertBasis ℂ K
  obtain ⟨A,hA,hs⟩ := extension_squared_summable h₂ h₃ h₂₃ j hd hj u hu e
  let F (k : ℕ) := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 k).comp A
  refine ⟨fun k => ‖F k‖,fun _ => norm_nonneg _,summable_coordinate_norm_sq e A hs,fun k x => ?_⟩
  have hFk : F k (j x) = g k x := by change (A (j x)) k = _; rw [hA]; rfl
  rw [← hFk,← hj]
  exact (F k).le_opNorm _

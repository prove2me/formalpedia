-- Prove2me | solution 1 for MasulloGRH.schwartz_local_nonarchimedean_structure
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T06:19:47.898429+00:00
-- url     : https://prove2.me/submissions/16cdd21b-7c1c-4138-84dd-6c707496388e

import Definitions.Def_MasulloGRH_AdelicTheta

set_option autoImplicit false

namespace Aux_SLN

open MasulloGRH Topology Filter Bornology TensorProduct Function

universe u

section fsn

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}

noncomputable def fsn (σ : ι → Seminorm ℂ V) (h : ∀ v, (support fun i => σ i v).Finite) :
    Seminorm ℂ V :=
  Seminorm.of (fun v => ∑ᶠ i, σ i v)
    (fun x y => by
      classical
      let s := (h x).toFinset ∪ (h y).toFinset ∪ (h (x + y)).toFinset
      have hx : (support fun i => σ i x) ⊆ ↑s := by
        intro i hi
        simp only [s, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
        tauto
      have hy : (support fun i => σ i y) ⊆ ↑s := by
        intro i hi
        simp only [s, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
        tauto
      have hxy : (support fun i => σ i (x + y)) ⊆ ↑s := by
        intro i hi
        simp only [s, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
        tauto
      show ∑ᶠ i, σ i (x + y) ≤ ∑ᶠ i, σ i x + ∑ᶠ i, σ i y
      rw [finsum_eq_sum_of_support_subset _ hx, finsum_eq_sum_of_support_subset _ hy,
        finsum_eq_sum_of_support_subset _ hxy, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => map_add_le_add _ _ _)
    (fun a x => by
      show ∑ᶠ i, σ i (a • x) = ‖a‖ * ∑ᶠ i, σ i x
      rw [mul_finsum]
      simp only [map_smul_eq_mul])

lemma fsn_apply (σ : ι → Seminorm ℂ V) (h : ∀ v, (support fun i => σ i v).Finite) (v : V) :
    fsn σ h v = ∑ᶠ i, σ i v := rfl

lemma fsn_eq_sum (σ : ι → Seminorm ℂ V) (h : ∀ v, (support fun i => σ i v).Finite) (v : V)
    (s : Finset ι) (hs : ∀ i ∉ s, σ i v = 0) : fsn σ h v = ∑ i ∈ s, σ i v := by
  rw [fsn_apply]
  refine finsum_eq_sum_of_support_subset _ ?_
  intro i hi
  by_contra h'
  exact hi (hs i h')

lemma le_fsn (σ : ι → Seminorm ℂ V) (h : ∀ v, (support fun i => σ i v).Finite) (v : V)
    (i : ι) : σ i v ≤ fsn σ h v :=
  single_le_finsum i (h v) (fun _ => apply_nonneg _ _)

variable (b : Module.Basis ι ℂ V)

lemma wsn_fin (w : ι → NNReal) (v : V) :
    (support fun i => (w i • (normSeminorm ℂ ℂ).comp (b.coord i)) v).Finite := by
  apply (b.repr v).support.finite_toSet.subset
  intro i hi
  by_contra h'
  apply hi
  have : b.repr v i = 0 := Finsupp.notMem_support_iff.1 h'
  simp [this]

noncomputable def wsn (w : ι → NNReal) : Seminorm ℂ V :=
  fsn (fun i => w i • (normSeminorm ℂ ℂ).comp (b.coord i)) (wsn_fin b w)

lemma wsn_term (w : ι → NNReal) (v : V) (i : ι) :
    (w i • (normSeminorm ℂ ℂ).comp (b.coord i)) v = (w i : ℝ) * ‖b.repr v i‖ := by
  simp; rfl

lemma wsn_eq_sum (w : ι → NNReal) (v : V) (s : Finset ι)
    (hs : ∀ i ∉ s, b.repr v i = 0) :
    wsn b w v = ∑ i ∈ s, (w i : ℝ) * ‖b.repr v i‖ := by
  rw [wsn, fsn_eq_sum _ _ v s (fun i hi => by rw [wsn_term, hs i hi]; simp)]
  exact Finset.sum_congr rfl fun i _ => wsn_term b w v i

lemma term_le_wsn (w : ι → NNReal) (v : V) (i : ι) :
    (w i : ℝ) * ‖b.repr v i‖ ≤ wsn b w v := by
  have := le_fsn (fun i => w i • (normSeminorm ℂ ℂ).comp (b.coord i)) (wsn_fin b w) v i
  rw [wsn_term] at this
  exact this

lemma repr_sum (v : V) : ∑ i ∈ (b.repr v).support, b.repr v i • b i = v := by
  have := b.linearCombination_repr v
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at this
  exact this

lemma sum_eq_of_supp (v : V) (s : Finset ι) (hs : ∀ i ∉ s, b.repr v i = 0) :
    ∑ i ∈ s, b.repr v i • b i = v := by
  classical
  have h1 : ∑ i ∈ (b.repr v).support, b.repr v i • b i = ∑ i ∈ s, b.repr v i • b i := by
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      by_contra h'
      exact (Finsupp.mem_support_iff.1 hi) (hs i h')
    · intro i _ hi
      rw [Finsupp.notMem_support_iff.1 hi, zero_smul]
  rw [← h1]; exact repr_sum b v

lemma sum_le_wsn (w : ι → NNReal) (v : V) (s : Finset ι) :
    ∑ i ∈ s, (w i : ℝ) * ‖b.repr v i‖ ≤ wsn b w v := by
  classical
  rw [wsn_eq_sum b w v (s ∪ (b.repr v).support) (fun i hi => by
    simp only [Finset.mem_union, not_or] at hi
    exact Finsupp.notMem_support_iff.1 hi.2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun i _ _ => by positivity)

lemma sn_le_sum (p : Seminorm ℂ V) (v : V) (s : Finset ι) (hs : ∀ i ∉ s, b.repr v i = 0) :
    p v ≤ ∑ i ∈ s, p (b i) * ‖b.repr v i‖ := by
  classical
  have h1 : ∑ i ∈ (b.repr v).support, b.repr v i • b i = ∑ i ∈ s, b.repr v i • b i := by
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      by_contra h'
      exact (Finsupp.mem_support_iff.1 hi) (hs i h')
    · intro i _ hi
      rw [Finsupp.notMem_support_iff.1 hi, zero_smul]
  have hv : ∑ i ∈ s, b.repr v i • b i = v := by
    rw [← h1]; exact repr_sum b v
  calc p v = p (∑ i ∈ s, b.repr v i • b i) := by rw [hv]
    _ ≤ ∑ i ∈ s, p (b.repr v i • b i) :=
        Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
    _ = ∑ i ∈ s, p (b i) * ‖b.repr v i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul_eq_mul, mul_comm]

noncomputable def nnw (p : Seminorm ℂ V) : ι → NNReal := fun i => ⟨p (b i), apply_nonneg _ _⟩

lemma le_wsn (p : Seminorm ℂ V) (v : V) :
    p v ≤ wsn b (nnw b p) v := by
  rw [wsn_eq_sum b _ v (b.repr v).support (fun i hi => Finsupp.notMem_support_iff.1 hi)]
  exact sn_le_sum b p v _ (fun i hi => Finsupp.notMem_support_iff.1 hi)

end fsn

section scale

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If `β y < r → σ y ≤ M` then `σ ≤ (M / r) β`. -/
lemma sn_scale {σ β : Seminorm ℂ V} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (h : ∀ y, β y < r → σ y ≤ M) (y : V) : σ y ≤ M / r * β y := by
  by_contra hcon
  push Not at hcon
  have hβ := apply_nonneg β y
  have hσpos : 0 < σ y := lt_of_le_of_lt (by positivity) hcon
  -- choose t > 0 with t * β y < r and t * σ y > M
  have key : M * β y < r * σ y := by
    have := hcon
    rw [div_mul_eq_mul_div, div_lt_iff₀ hr] at this
    linarith
  obtain ⟨t, ht0, ht1, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t * β y < r ∧ M < t * σ y := by
    by_cases hβ0 : β y = 0
    · refine ⟨(M + 1) / σ y, by positivity, ?_, ?_⟩
      · rw [hβ0, mul_zero]; exact hr
      · rw [div_mul_cancel₀ _ hσpos.ne']; linarith
    · have hβp : 0 < β y := lt_of_le_of_ne hβ (Ne.symm hβ0)
      refine ⟨(M / σ y + r / β y) / 2, by positivity, ?_, ?_⟩
      · have h1 : M / σ y < r / β y := by
          rw [div_lt_div_iff₀ hσpos hβp]; linarith
        have : (M / σ y + r / β y) / 2 < r / β y := by linarith
        calc (M / σ y + r / β y) / 2 * β y < r / β y * β y :=
              mul_lt_mul_of_pos_right this hβp
          _ = r := div_mul_cancel₀ _ hβp.ne'
      · have h1 : M / σ y < r / β y := by
          rw [div_lt_div_iff₀ hσpos hβp]; linarith
        have : M / σ y < (M / σ y + r / β y) / 2 := by linarith
        calc M = M / σ y * σ y := (div_mul_cancel₀ _ hσpos.ne').symm
          _ < (M / σ y + r / β y) / 2 * σ y := mul_lt_mul_of_pos_right this hσpos
  have e1 : β ((t : ℂ) • y) = t * β y := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have e2 : σ ((t : ℂ) • y) = t * σ y := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have := h ((t : ℂ) • y) (by rw [e1]; exact ht1)
  rw [e2] at this
  linarith

end scale

section bdd

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

lemma bdd_of_cont {q : Seminorm ℂ E} (hq : Continuous q) {S : Set E}
    (hS : IsVonNBounded ℂ S) : ∃ R : ℝ, ∀ x ∈ S, q x ≤ R := by
  obtain ⟨a, ha⟩ := (hS (q.ball_mem_nhds hq one_pos)).eventually.exists
  refine ⟨‖a‖, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := ha hx
  rw [map_smul_eq_mul]
  have h1 : q y < 1 := (Seminorm.mem_ball_zero q).1 hy
  exact mul_le_of_le_one_right (norm_nonneg a) h1.le

end bdd

/-! ## The finest locally convex topology -/

section finest

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]

/-- `E` carries the topology of all seminorms. -/
def IsFin (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  WithSeminorms (fun p : Seminorm ℂ E => p)

lemma lc_of_ws {ι : Type u} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    IsLocallyConvexTopology E ‹TopologicalSpace E› :=
  ⟨Finset ι, inferInstance, fun s => s.sup p, hp.finset_sups⟩

variable (hE : IsFin E)
include hE

lemma fin_cont (p : Seminorm ℂ E) : Continuous p := WithSeminorms.continuous_seminorm hE p

lemma fin_tag : IsTopologicalAddGroup E := WithSeminorms.topologicalAddGroup hE

lemma fin_csmul : ContinuousSMul ℂ E := WithSeminorms.continuousSMul hE

noncomputable def fclm (g : E →ₗ[ℂ] ℂ) : StrongDual ℂ E :=
  ⟨g, WithSeminorms.continuous_normedSpace_rng ℂ hE g
    ⟨{(normSeminorm ℂ ℂ).comp g}, 1, by simp⟩⟩

@[simp] lemma fclm_apply (g : E →ₗ[ℂ] ℂ) (x : E) : fclm hE g x = g x := rfl

lemma fin_lin_cont {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    {κ : Type*} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q) (L : E →ₗ[ℂ] F) :
    Continuous L := by
  have := fin_tag hE
  exact WithSeminorms.continuous_of_continuous_comp hq L
    (fun i => fin_cont hE ((q i).comp L))

lemma fin_isLC : IsLocallyConvexTopology E ‹TopologicalSpace E› := lc_of_ws hE

lemma fin_t2 : T2Space E := by
  have := fin_tag hE
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ E) ℂ E) :=
    ⟨Module.Basis.ofVectorSpace ℂ E⟩
  have : T1Space E := WithSeminorms.T1_of_separating hE (fun x hx => by
    have : b.repr x ≠ 0 := fun h => hx (by simpa using congrArg b.repr.symm h)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 this
    refine ⟨(normSeminorm ℂ ℂ).comp (b.coord i), ?_⟩
    simpa using hi)
  infer_instance

lemma fin_hlcs : IsHLCS E := ⟨fin_isLC hE, fin_t2 hE⟩

/-- The topology of all seminorms is the finest locally convex topology. -/
lemma fin_le_lc (t : TopologicalSpace E) (ht : IsLocallyConvexTopology E t) :
    τE ≤ t := by
  obtain ⟨ι, _, p, hp⟩ := ht
  exact (@continuous_id_iff_le E τE t).1 (WithSeminorms.continuous_of_isBounded hE hp LinearMap.id
    (fun i => ⟨{p i}, 1, by simp⟩))

lemma fin_hasFinest : HasFinestLocallyConvexTopology E := by
  unfold HasFinestLocallyConvexTopology
  apply le_antisymm
  · exact le_sInf fun t ht => @fin_le_lc E _ _ τE hE t ht
  · exact sInf_le (fin_isLC hE)

end finest

section basis

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {ι : Type*} (hE : IsFin E) (b : Module.Basis ι ℂ E)
include hE b

lemma coord_cont (i : ι) : Continuous fun x : E => b.repr x i :=
  (fclm hE (b.coord i)).continuous

lemma bdd_basis (enc : ι → ℕ) (henc : Injective enc) {B : Set E} (hB : IsVonNBounded ℂ B) :
    ∃ J : Finset ι, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ B, (∀ i ∉ J, b.repr x i = 0) ∧
      ∀ i, ‖b.repr x i‖ ≤ M := by
  classical
  let I : Set ι := {i | ∃ x ∈ B, b.repr x i ≠ 0}
  let w : ι → NNReal := fun i =>
    if h : ∃ x ∈ B, b.repr x i ≠ 0 then Real.toNNReal (enc i / ‖b.repr h.choose i‖) else 0
  obtain ⟨R, hR⟩ := bdd_of_cont (fin_cont hE (wsn b w)) hB
  have hI : I.Finite := by
    have hsub : I ⊆ enc ⁻¹' (Set.Iic ⌊R⌋₊) := by
      intro i hi
      have h : ∃ x ∈ B, b.repr x i ≠ 0 := hi
      have hn : ‖b.repr h.choose i‖ ≠ 0 := norm_ne_zero_iff.2 h.choose_spec.2
      have h1 := term_le_wsn b w h.choose i
      have hw : (w i : ℝ) = enc i / ‖b.repr h.choose i‖ := by
        simp only [w, dif_pos h]
        exact Real.coe_toNNReal _ (by positivity)
      rw [hw, div_mul_cancel₀ _ hn] at h1
      have h2 := hR _ h.choose_spec.1
      show enc i ∈ Set.Iic ⌊R⌋₊
      rw [Set.mem_Iic]
      exact Nat.le_floor (by linarith)
    exact ((Set.finite_Iic _).preimage henc.injOn).subset hsub
  have hRi : ∀ i, ∃ Ri : ℝ, ∀ x ∈ B, ‖b.repr x i‖ ≤ Ri := by
    intro i
    obtain ⟨Ri, hRi⟩ := bdd_of_cont (fin_cont hE ((normSeminorm ℂ ℂ).comp (b.coord i))) hB
    exact ⟨Ri, fun x hx => by simpa using hRi x hx⟩
  choose Ri hRi using hRi
  refine ⟨hI.toFinset, ∑ i ∈ hI.toFinset, |Ri i|, by positivity, fun x hx => ⟨?_, ?_⟩⟩
  · intro i hi
    by_contra h'
    exact hi (hI.mem_toFinset.2 ⟨x, hx, h'⟩)
  · intro i
    by_cases hi : i ∈ hI.toFinset
    · calc ‖b.repr x i‖ ≤ Ri i := hRi i x hx
        _ ≤ |Ri i| := le_abs_self _
        _ ≤ ∑ i ∈ hI.toFinset, |Ri i| :=
            Finset.single_le_sum (f := fun i => |Ri i|) (fun _ _ => abs_nonneg _) hi
    · have : b.repr x i = 0 := by
        by_contra h'
        exact hi (hI.mem_toFinset.2 ⟨x, hx, h'⟩)
      rw [this, norm_zero]
      positivity

lemma fin_compact (enc : ι → ℕ) (henc : Injective enc) {B : Set E} (hc : IsClosed B)
    (hB : IsVonNBounded ℂ B) : IsCompact B := by
  classical
  have := fin_tag hE
  have := fin_csmul hE
  obtain ⟨J, M, hM, hJ⟩ := bdd_basis hE b enc henc hB
  let Φ : (J → ℂ) → E := fun c => ∑ i : J, c i • b i
  have hΦ : Continuous Φ :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)
  have hK : IsCompact (Φ ⁻¹' B ∩ Metric.closedBall 0 M) :=
    (isCompact_closedBall 0 M).inter_left (hc.preimage hΦ)
  have hB' : B = Φ '' (Φ ⁻¹' B ∩ Metric.closedBall 0 M) := by
    apply Set.Subset.antisymm
    · intro x hx
      refine ⟨fun i => b.repr x i, ⟨?_, ?_⟩, ?_⟩
      · show Φ _ ∈ B
        have : Φ (fun i => b.repr x i) = x := by
          show ∑ i : J, b.repr x i • b i = x
          rw [Finset.sum_coe_sort J (fun i => b.repr x i • b i)]
          exact sum_eq_of_supp b x J (hJ x hx).1
        rw [this]; exact hx
      · rw [mem_closedBall_zero_iff]
        exact (pi_norm_le_iff_of_nonneg hM).2 fun i => (hJ x hx).2 i
      · show ∑ i : J, b.repr x i • b i = x
        rw [Finset.sum_coe_sort J (fun i => b.repr x i • b i)]
        exact sum_eq_of_supp b x J (hJ x hx).1
    · rintro _ ⟨c, hc, rfl⟩
      exact hc.1
  rw [hB']
  exact hK.image hΦ

end basis

section complete

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {ι : Type*} (hE : IsFin E) (b : Module.Basis ι ℂ E)
include hE b

lemma coord_lim {𝓕 : Filter E} (h𝓕 : IsCauchyFilter 𝓕) (i : ι) :
    ∃ l : ℂ, Tendsto (fun x => b.repr x i) 𝓕 (𝓝 l) := by
  obtain ⟨hne, hc⟩ := h𝓕
  have hC : Cauchy (map (fun x => b.repr x i) 𝓕) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hU : {x : E | ‖b.repr x i‖ < ε} ∈ 𝓝 (0 : E) := by
      have h0 : b.repr (0 : E) i = 0 := by simp
      have he : {x : E | ‖b.repr x i‖ < ε} = (fun x => b.repr x i) ⁻¹' Metric.ball 0 ε := by
        ext; simp
      rw [he]
      exact (coord_cont hE b i).continuousAt.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds _ hε)
    obtain ⟨A, hA, hAU⟩ := hc _ hU
    refine ⟨(fun x => b.repr x i) '' A, image_mem_map hA, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [dist_eq_norm, ← Finsupp.sub_apply, ← map_sub]
    exact hAU x hx y hy
  obtain ⟨l, hl⟩ := CompleteSpace.complete hC
  exact ⟨l, hl⟩

lemma fin_complete : IsCompleteTVS E := by
  classical
  refine ⟨fin_t2 hE, fun 𝓕 h𝓕 => ?_⟩
  choose l hl using coord_lim hE b h𝓕
  obtain ⟨hne, hc⟩ := h𝓕
  -- finiteness of the support of the limit
  have hfin : (support l).Finite := by
    by_contra hinf
    let w : ι → NNReal := fun i => if l i = 0 then 0 else Real.toNNReal (2 / ‖l i‖)
    have hU : {x : E | wsn b w x < 1} ∈ 𝓝 (0 : E) := by
      exact (fin_cont hE (wsn b w)).continuousAt.preimage_mem_nhds (x := 0) (t := Set.Iio 1)
        (by rw [map_zero]; exact Iio_mem_nhds one_pos)
    obtain ⟨A, hA, hAU⟩ := hc _ hU
    obtain ⟨x0, hx0⟩ := hne.nonempty_of_mem hA
    obtain ⟨i, hi1, hi2⟩ : ∃ i, l i ≠ 0 ∧ b.repr x0 i = 0 := by
      have : ((support l) \ ((b.repr x0).support : Set ι)).Nonempty :=
        (Set.Infinite.sdiff hinf (b.repr x0).support.finite_toSet).nonempty
      obtain ⟨i, hi, hi'⟩ := this
      exact ⟨i, hi, by simpa using hi'⟩
    have hpos : 0 < ‖l i‖ := norm_pos_iff.2 hi1
    have hev : ∀ᶠ y in 𝓕, ‖b.repr y i - l i‖ < ‖l i‖ / 2 := by
      have := (hl i).eventually (Metric.ball_mem_nhds (l i) (half_pos hpos))
      filter_upwards [this] with y hy
      rwa [dist_eq_norm] at hy
    obtain ⟨y, hyA, hy⟩ := (hne.nonempty_of_mem (inter_mem hA hev))
    have h1 := term_le_wsn b w (y - x0) i
    have h2 := hAU y hyA x0 hx0
    have hw : (w i : ℝ) = 2 / ‖l i‖ := by
      simp only [w, if_neg hi1]
      exact Real.coe_toNNReal _ (by positivity)
    rw [hw, map_sub, Finsupp.sub_apply, hi2, sub_zero] at h1
    have h3 : 2 / ‖l i‖ * ‖b.repr y i‖ < 1 := lt_of_le_of_lt h1 h2
    have hy' : ‖b.repr y i - l i‖ < ‖l i‖ / 2 := hy
    have h4 : ‖l i‖ / 2 < ‖b.repr y i‖ := by
      have := norm_sub_norm_le (l i) (b.repr y i)
      rw [norm_sub_rev] at this
      linarith
    have h5 : 2 / ‖l i‖ * (‖l i‖ / 2) = 1 := by field_simp
    have : 2 / ‖l i‖ * (‖l i‖ / 2) < 2 / ‖l i‖ * ‖b.repr y i‖ :=
      mul_lt_mul_of_pos_left h4 (by positivity)
    linarith
  let x : E := b.repr.symm (Finsupp.ofSupportFinite l hfin)
  have hx : ∀ i, b.repr x i = l i := by
    intro i
    simp [x, Finsupp.ofSupportFinite_coe]
  refine ⟨x, ?_⟩
  have key : Tendsto id 𝓕 (𝓝 x) := by
    rw [WithSeminorms.tendsto_nhds hE id x]
    intro p ε hε
    let W := wsn b (nnw b p)
    have hU : {z : E | W z < ε / 3} ∈ 𝓝 (0 : E) := by
      exact (fin_cont hE W).continuousAt.preimage_mem_nhds (x := 0) (t := Set.Iio (ε / 3))
        (by rw [map_zero]; exact Iio_mem_nhds (by positivity))
    obtain ⟨A, hA, hAU⟩ := hc _ hU
    obtain ⟨x0, hx0⟩ := hne.nonempty_of_mem hA
    let J : Finset ι := (b.repr x0).support ∪ hfin.toFinset
    let S : ℝ := ∑ i ∈ J, p (b i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
    let η : ℝ := ε / (3 * (S + 1))
    have hη : 0 < η := by positivity
    have hev : ∀ᶠ y in 𝓕, ∀ i ∈ J, ‖b.repr y i - l i‖ < η := by
      rw [Filter.eventually_all_finset]
      intro i _
      have := (hl i).eventually (Metric.ball_mem_nhds (l i) hη)
      filter_upwards [this] with y hy
      rwa [dist_eq_norm] at hy
    obtain ⟨ys, hysA, hys⟩ := hne.nonempty_of_mem (inter_mem hA hev)
    filter_upwards [hA] with y hy
    show p (y - x) < ε
    have hpW : ∀ z, p z ≤ W z := fun z => le_wsn b p z
    have e1 : p (y - x) ≤ p (y - ys) + p (ys - x) := by
      have := map_add_le_add p (y - ys) (ys - x)
      rwa [sub_add_sub_cancel] at this
    have e2 : p (y - ys) < ε / 3 := lt_of_le_of_lt (hpW _) (hAU y hy ys hysA)
    -- estimate of W (ys - x)
    let K : Finset ι := J ∪ (b.repr ys).support
    have hK : ∀ i ∉ K, b.repr (ys - x) i = 0 := by
      intro i hi
      simp only [K, J, Finset.mem_union, not_or, Finsupp.notMem_support_iff,
        Set.Finite.mem_toFinset, mem_support, not_not] at hi
      rw [map_sub, Finsupp.sub_apply, hx, hi.1.2, hi.2, sub_zero]
    have e3 : W (ys - x) = ∑ i ∈ K, p (b i) * ‖b.repr (ys - x) i‖ :=
      wsn_eq_sum b _ _ K hK
    have hsplit : ∑ i ∈ K, p (b i) * ‖b.repr (ys - x) i‖ =
        ∑ i ∈ J, p (b i) * ‖b.repr (ys - x) i‖ +
          ∑ i ∈ K \ J, p (b i) * ‖b.repr (ys - x) i‖ := by
      rw [add_comm, Finset.sum_sdiff Finset.subset_union_left]
    have e4 : ∑ i ∈ J, p (b i) * ‖b.repr (ys - x) i‖ ≤ ε / 3 := by
      calc ∑ i ∈ J, p (b i) * ‖b.repr (ys - x) i‖ ≤ ∑ i ∈ J, p (b i) * η := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [map_sub, Finsupp.sub_apply, hx]
            exact mul_le_mul_of_nonneg_left (hys i hi).le (apply_nonneg _ _)
        _ = S * η := by rw [Finset.sum_mul]
        _ ≤ ε / 3 := by
            show S * (ε / (3 * (S + 1))) ≤ ε / 3
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have e5 : ∑ i ∈ K \ J, p (b i) * ‖b.repr (ys - x) i‖ ≤ W (ys - x0) := by
      calc ∑ i ∈ K \ J, p (b i) * ‖b.repr (ys - x) i‖ =
            ∑ i ∈ K \ J, (nnw b p i : ℝ) * ‖b.repr (ys - x0) i‖ := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hiJ : i ∉ J := (Finset.mem_sdiff.1 hi).2
            simp only [J, Finset.mem_union, not_or, Finsupp.notMem_support_iff,
              Set.Finite.mem_toFinset, mem_support, not_not] at hiJ
            rw [map_sub, map_sub, Finsupp.sub_apply, Finsupp.sub_apply, hx, hiJ.1, hiJ.2]
            rfl
        _ ≤ W (ys - x0) := sum_le_wsn b _ _ _
    have e6 : W (ys - x0) < ε / 3 := hAU ys hysA x0 hx0
    have e7 : p (ys - x) ≤ W (ys - x) := hpW _
    linarith
  exact key

end complete

section compl

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable (hE : IsFin E)
include hE

lemma fin_compl (V : Submodule ℂ E) : ∃ W : Submodule ℂ E, IsCompl V W ∧
    Continuous (fun p : V × W => ((p.1 : E) + p.2)) ∧
    IsOpenMap (fun p : V × W => ((p.1 : E) + p.2)) := by
  have := fin_tag hE
  obtain ⟨W, hW⟩ := V.exists_isCompl
  refine ⟨W, hW, ?_, ?_⟩
  · exact (continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)
  · let e := Submodule.prodEquivOfIsCompl V W hW
    have he : (fun p : V × W => ((p.1 : E) + p.2)) = ⇑e := by
      funext p; rfl
    have h1 : Continuous fun x => (e.symm x).1 :=
      (fin_lin_cont hE hE (V.subtype ∘ₗ LinearMap.fst ℂ V W ∘ₗ e.symm.toLinearMap)).subtype_mk _
    have h2 : Continuous fun x => (e.symm x).2 :=
      (fin_lin_cont hE hE (W.subtype ∘ₗ LinearMap.snd ℂ V W ∘ₗ e.symm.toLinearMap)).subtype_mk _
    have hs : Continuous e.symm := h1.prodMk h2
    rw [he]
    intro U hU
    have h : ⇑e '' U = ⇑e.symm ⁻¹' U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨e.symm x, hx, by simp⟩
    rw [h]
    exact hU.preimage hs

end compl

section strictLF

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {ι : Type*} (hE : IsFin E) (b : Module.Basis ι ℂ E) (enc : ι → ℕ) (henc : Injective enc)
include hE b henc

lemma fin_strictLF : IsStrictLF E := by
  classical
  have := fin_tag hE
  have := fin_csmul hE
  have := fin_t2 hE
  let X : ℕ → Submodule ℂ E := fun n => Submodule.span ℂ (b '' {i | enc i < n})
  have hfinX : ∀ n, FiniteDimensional ℂ (X n) := fun n =>
    FiniteDimensional.span_of_finite ℂ
      ((((Set.finite_Iio n).preimage henc.injOn)).image b)
  refine ⟨X, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact Submodule.span_mono (Set.image_mono fun i hi => lt_of_lt_of_le hi hmn)
  · intro x
    refine ⟨(b.repr x).support.sup enc + 1, ?_⟩
    have hmem : ∑ i ∈ (b.repr x).support, b.repr x i • b i ∈ X ((b.repr x).support.sup enc + 1) :=
      Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := enc) hi), rfl⟩)
    rwa [repr_sum] at hmem
  · intro n
    refine ⟨lc_of_ws (LinearMap.withSeminorms_induced hE (X n).subtype), ⟨inferInstance, ?_⟩, ?_⟩
    · intro 𝓕 h𝓕
      obtain ⟨hne, hc⟩ := h𝓕
      have hC : IsCauchyFilter (map (Subtype.val : X n → E) 𝓕) := by
        refine ⟨inferInstance, fun U hU => ?_⟩
        have hU' : (Subtype.val : X n → E) ⁻¹' U ∈ 𝓝 (0 : X n) :=
          continuous_subtype_val.continuousAt.preimage_mem_nhds hU
        obtain ⟨A, hA, hAU⟩ := hc _ hU'
        refine ⟨Subtype.val '' A, image_mem_map hA, ?_⟩
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact hAU x hx y hy
      obtain ⟨x, hx⟩ := (fin_complete hE b).2 _ hC
      have hmem : x ∈ X n := by
        have hcl : IsClosed ((X n : Set E)) := Submodule.closed_of_finiteDimensional _
        have : NeBot (map (Subtype.val : X n → E) 𝓕) := hC.1
        exact hcl.mem_of_tendsto hx
          (Filter.eventually_map.2 (Eventually.of_forall fun (y : X n) => SetLike.mem_coe.2 y.2))
      refine ⟨⟨x, hmem⟩, ?_⟩
      rw [nhds_subtype]
      exact Filter.map_le_iff_le_comap.1 hx
    · have e := (Module.finBasis ℂ (X n)).equivFun.toContinuousLinearEquiv
      exact e.toHomeomorph.isEmbedding.metrizableSpace
  · apply le_antisymm
    · exact le_sInf fun t ht => @fin_le_lc E _ _ τE hE t ht.1
    · exact sInf_le ⟨fin_isLC hE, fun n => continuous_subtype_val⟩

end strictLF

section geo

lemma geo_sum {ι : Type*} (enc : ι → ℕ) (henc : Injective enc) (K : Finset ι) :
    ∑ i ∈ K, ((1 : ℝ) / 2) ^ enc i ≤ 2 := by
  classical
  rw [← Finset.sum_image (f := fun n => ((1 : ℝ) / 2) ^ n) (fun x _ y _ h => henc h)]
  obtain ⟨N, hN⟩ : ∃ N, K.image enc ⊆ Finset.range N :=
    ⟨(K.image enc).sup id + 1, fun n hn => Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))⟩
  calc ∑ n ∈ K.image enc, ((1 : ℝ) / 2) ^ n ≤ ∑ n ∈ Finset.range N, ((1 : ℝ) / 2) ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
    _ ≤ 2 := sum_geometric_two_le N

end geo

section dual

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]

noncomputable def ev (x : E) : StrongDual ℂ E →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma ev_apply (x : E) (f : StrongDual ℂ E) : ev x f = f x := rfl

variable {ι : Type u} (hE : IsFin E) (b : Module.Basis ι ℂ E) (enc : ι → ℕ) (henc : Injective enc)

/-- seminorms of the dual -/
noncomputable def dsn (i : ι) : Seminorm ℂ (StrongDual ℂ E) := (normSeminorm ℂ ℂ).comp (ev (b i))

@[simp] lemma dsn_apply (i : ι) (f : StrongDual ℂ E) : dsn b i f = ‖f (b i)‖ := rfl


include hE b henc

omit henc in
lemma dsn_cont (i : ι) : Continuous (dsn b i) := by
  have := fin_csmul hE
  have := fin_tag hE
  show Continuous fun f : StrongDual ℂ E => ‖f (b i)‖
  exact continuous_norm.comp (continuous_eval_const (b i))

omit hE henc in
lemma clm_eq_sum (f : StrongDual ℂ E) (x : E) (s : Finset ι) (hs : ∀ i ∉ s, b.repr x i = 0) :
    f x = ∑ i ∈ s, b.repr x i * f (b i) := by
  conv_lhs => rw [← sum_eq_of_supp b x s hs]
  rw [map_sum]
  simp [smul_eq_mul]

lemma dual_ws : WithSeminorms (dsn b) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  apply le_antisymm
  · refine le_iInf fun i => ?_
    rw [← tendsto_iff_comap]
    have := (dsn_cont hE b i).tendsto 0
    rwa [map_zero] at this
  · refine (ContinuousLinearMap.hasBasis_nhds_zero).ge_iff.2 ?_
    rintro ⟨B, U⟩ ⟨hB, hU⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨J, M, hM, hJ⟩ := bdd_basis hE b enc henc hB
    let δ : ℝ := ε / (M * J.card + 1)
    have hδ : 0 < δ := by positivity
    have hT : (⋂ i ∈ J, (dsn b i) ⁻¹' Metric.ball 0 δ) ∈ ⨅ i, comap (dsn b i) (𝓝 0) :=
      (Filter.biInter_finset_mem J).2 fun i _ =>
        mem_iInf_of_mem i (preimage_mem_comap (Metric.ball_mem_nhds 0 hδ))
    refine mem_of_superset hT ?_
    intro f hf x hx
    simp only [Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs] at hf
    apply hεU
    rw [Metric.mem_ball, dist_zero_right, clm_eq_sum b f x J (hJ x hx).1]
    calc ‖∑ i ∈ J, b.repr x i * f (b i)‖ ≤ ∑ i ∈ J, ‖b.repr x i * f (b i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ J, M * δ := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul]
          have h1 := hf i hi
          rw [abs_of_nonneg (apply_nonneg _ _), dsn_apply] at h1
          exact mul_le_mul ((hJ x hx).2 i) h1.le (norm_nonneg _) hM
      _ = M * J.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ < ε := by
          show M * J.card * (ε / (M * J.card + 1)) < ε
          rw [mul_div_assoc']
          rw [div_lt_iff₀ (by positivity)]
          nlinarith

lemma dual_isLC : IsLocallyConvexTopology (StrongDual ℂ E) inferInstance :=
  lc_of_ws (dual_ws hE b enc henc)

lemma dual_t2 : T2Space (StrongDual ℂ E) := by
  have hw := dual_ws hE b enc henc
  have : T1Space (StrongDual ℂ E) := WithSeminorms.T1_of_separating hw (fun f hf => by
    by_contra h
    push Not at h
    apply hf
    have : (f : E →ₗ[ℂ] ℂ) = 0 := b.ext fun i => by
      have := h i
      simpa using this
    ext x
    exact LinearMap.congr_fun this x)
  infer_instance

lemma dual_hlcs : IsHLCS (StrongDual ℂ E) := ⟨dual_isLC hE b enc henc, dual_t2 hE b enc henc⟩

lemma dual_complete : IsCompleteTVS (StrongDual ℂ E) := by
  classical
  have hw := dual_ws hE b enc henc
  refine ⟨dual_t2 hE b enc henc, fun 𝓕 h𝓕 => ?_⟩
  obtain ⟨hne, hc⟩ := h𝓕
  have hlim : ∀ i, ∃ l : ℂ, Tendsto (fun f : StrongDual ℂ E => f (b i)) 𝓕 (𝓝 l) := by
    intro i
    have hC : Cauchy (map (fun f : StrongDual ℂ E => f (b i)) 𝓕) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      have hU : (dsn b i) ⁻¹' Set.Iio ε ∈ 𝓝 (0 : StrongDual ℂ E) :=
        (dsn_cont hE b i).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact Iio_mem_nhds hε)
      obtain ⟨A, hA, hAU⟩ := hc _ hU
      refine ⟨(fun f : StrongDual ℂ E => f (b i)) '' A, image_mem_map hA, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [dist_eq_norm]
      have := hAU x hx y hy
      simpa using this
    obtain ⟨l, hl⟩ := CompleteSpace.complete hC
    exact ⟨l, hl⟩
  choose l hl using hlim
  let L : StrongDual ℂ E := fclm hE (b.constr ℂ l)
  have hL : ∀ i, L (b i) = l i := fun i => by simp [L]
  refine ⟨L, ?_⟩
  have : Tendsto id 𝓕 (𝓝 L) := by
    rw [WithSeminorms.tendsto_nhds hw id L]
    intro i ε hε
    have := (hl i).eventually (Metric.ball_mem_nhds (l i) hε)
    filter_upwards [this] with f hf
    rw [dist_eq_norm] at hf
    simpa [hL] using hf
  exact this

lemma dual_metrizable : TopologicalSpace.MetrizableSpace (StrongDual ℂ E) := by
  have hw := dual_ws hE b enc henc
  have : Countable ι := ⟨⟨enc, henc⟩⟩
  have := dual_t2 hE b enc henc
  let _ : UniformSpace (StrongDual ℂ E) := IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup (StrongDual ℂ E) := isUniformAddGroup_of_addCommGroup
  have : (𝓝 (0 : StrongDual ℂ E)).IsCountablyGenerated := by
    rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf (dsn b)).mp hw]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity (StrongDual ℂ E)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.metrizableSpace

lemma dual_frechet : IsFrechet (StrongDual ℂ E) :=
  ⟨dual_isLC hE b enc henc, dual_complete hE b enc henc, dual_metrizable hE b enc henc⟩

/-- the coordinate functionals as elements of the dual -/
noncomputable def cf (i : ι) : StrongDual ℂ E := fclm hE (b.coord i)

omit henc in
@[simp] lemma cf_apply (i : ι) (x : E) : cf hE b i x = b.repr x i := rfl

open Classical in
omit henc in
lemma cf_basis (i j : ι) : cf hE b i (b j) = if j = i then 1 else 0 := by
  rw [cf_apply, Module.Basis.repr_self, Finsupp.single_apply]

lemma fin_reflexive_pt (φ : StrongDual ℂ (StrongDual ℂ E)) :
    ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x := by
  classical
  have hw := dual_ws hE b enc henc
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hw ((normSeminorm ℂ ℂ).comp
    (φ : StrongDual ℂ E →ₗ[ℂ] ℂ)) (continuous_norm.comp φ.continuous)
  let x : E := ∑ i ∈ s, φ (cf hE b i) • b i
  have hx : ∀ f : StrongDual ℂ E, φ f = f x := by
    intro f
    let g : StrongDual ℂ E := f - ∑ i ∈ s, f (b i) • cf hE b i
    have hg : ∀ j ∈ s, g (b j) = 0 := by
      intro j hj
      simp only [g, sub_apply, FunLike.coe_sum,
        Finset.sum_apply, smul_apply, cf_basis, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos hj, sub_self]
    have hφg : φ g = 0 := by
      have h1 := hC g
      have h2 : (s.sup (dsn b)) g ≤ 0 :=
        Seminorm.finset_sup_apply_le le_rfl fun j hj => by simp [hg j hj]
      have h3 : ‖φ g‖ ≤ 0 := by
        have : ‖φ g‖ ≤ (C : ℝ) * (s.sup (dsn b)) g := h1
        nlinarith [C.2]
      exact norm_le_zero_iff.1 h3
    have hf : f = g + ∑ i ∈ s, f (b i) • cf hE b i := (sub_add_cancel f _).symm
    have e1 : φ f = ∑ i ∈ s, f (b i) * φ (cf hE b i) := by
      conv_lhs => rw [hf]
      rw [map_add, hφg, zero_add, map_sum]
      simp [map_smul]
    have e2 : f x = ∑ i ∈ s, φ (cf hE b i) * f (b i) := by simp [x, map_sum]
    rw [e1, e2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨x, hx, fun y hy => ?_⟩
  apply b.repr.injective
  ext i
  have h1 := hy (cf hE b i)
  have h2 := hx (cf hE b i)
  rw [cf_apply] at h1 h2
  rw [← h1, h2]

end dual

section bidual

open scoped UniformConvergence

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {ι : Type u} (hE : IsFin E) (b : Module.Basis ι ℂ E) (enc : ι → ℕ) (henc : Injective enc)
include hE b henc

lemma fin_sb : τE = strongBidualTopology E := by
  classical
  have := fin_tag hE
  have := fin_csmul hE
  have hw := dual_ws hE b enc henc
  let 𝔅 : Set (Set (StrongDual ℂ E)) := {B | IsVonNBounded ℂ B}
  let Ψ : E → (StrongDual ℂ E →ᵤ[𝔅] ℂ) := fun x => UniformOnFun.ofFun 𝔅 (fun f => f x)
  have hsb : strongBidualTopology E = TopologicalSpace.induced Ψ inferInstance := rfl
  apply le_antisymm
  · rw [hsb, ← continuous_iff_le_induced, continuous_iff_continuousAt]
    intro x0
    rw [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    intro B hB
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hM : ∀ i, ∃ M : ℝ, ∀ f ∈ B, dsn b i f ≤ M := fun i =>
      bdd_of_cont (dsn_cont hE b i) hB
    choose M hM using hM
    let W := wsn b (fun i => Real.toNNReal (M i))
    have hev : ∀ᶠ x in 𝓝 x0, W (x - x0) < ε := by
      have h : Tendsto (fun x => W (x - x0)) (𝓝 x0) (𝓝 (W (x0 - x0))) :=
        ((fin_cont hE W).comp (continuous_sub_right x0)).tendsto x0
      rw [sub_self, map_zero] at h
      exact h.eventually (Iio_mem_nhds hε)
    filter_upwards [hev] with x hx f hf
    show dist (f x0) (f x) < ε
    rw [dist_eq_norm, ← map_sub]
    have h1 := sn_le_sum b ((normSeminorm ℂ ℂ).comp (f : E →ₗ[ℂ] ℂ)) (x0 - x)
      (b.repr (x0 - x)).support (fun i hi => Finsupp.notMem_support_iff.1 hi)
    have h2 : ∑ i ∈ (b.repr (x0 - x)).support,
        ((normSeminorm ℂ ℂ).comp (f : E →ₗ[ℂ] ℂ)) (b i) * ‖b.repr (x0 - x) i‖ ≤ W (x0 - x) := by
      rw [wsn_eq_sum b _ _ (b.repr (x0 - x)).support (fun i hi => Finsupp.notMem_support_iff.1 hi)]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := hM i f hf
      rw [dsn_apply] at this
      exact this.trans (Real.le_coe_toNNReal _)
    have h3 : W (x0 - x) = W (x - x0) := map_sub_rev W x0 x
    have h4 : ‖f (x0 - x)‖ = ((normSeminorm ℂ ℂ).comp (f : E →ₗ[ℂ] ℂ)) (x0 - x) := rfl
    linarith
  · refine (@continuous_id_iff_le E (strongBidualTopology E) τE).1 ?_
    rw [@continuous_iff_continuousAt E E (strongBidualTopology E) τE]
    intro x0
    show Tendsto id (@nhds E (strongBidualTopology E) x0) (𝓝 x0)
    rw [WithSeminorms.tendsto_nhds hE id x0]
    intro p ε hε
    let w' : ι → ℝ := fun i => 2 ^ enc i * p (b i)
    let 𝓑 : Set (StrongDual ℂ E) := Set.range fun i => ((w' i : ℂ)) • cf hE b i
    have h𝓑 : 𝓑 ∈ 𝔅 := by
      show IsVonNBounded ℂ 𝓑
      rw [hw.isVonNBounded_iff_seminorm_bounded]
      intro j
      refine ⟨w' j + 1, by positivity, ?_⟩
      rintro _ ⟨i, rfl⟩
      rw [dsn_apply, ContinuousLinearMap.smul_apply, cf_basis, smul_eq_mul]
      by_cases hij : j = i
      · subst hij
        simp only [if_true, mul_one, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        linarith
      · simp only [if_neg hij, mul_zero, norm_zero]
        positivity
    have hT : Tendsto Ψ (@nhds E (strongBidualTopology E) x0) (𝓝 (Ψ x0)) := by
      rw [hsb, nhds_induced]
      exact tendsto_comap
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hT
    have hev := Metric.tendstoUniformlyOn_iff.1 (hT 𝓑 h𝓑) (ε / 3) (by positivity)
    filter_upwards [hev] with x hx
    have hi : ∀ i, w' i * ‖b.repr (x - x0) i‖ < ε / 3 := by
      intro i
      have := hx _ ⟨i, rfl⟩
      change dist (((w' i : ℂ)) • cf hE b i x0) (((w' i : ℂ)) • cf hE b i x) < ε / 3 at this
      rw [dist_eq_norm, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), cf_apply, cf_apply, ← Finsupp.sub_apply, ← map_sub] at this
      have e : ‖b.repr (x0 - x) i‖ = ‖b.repr (x - x0) i‖ := by
        rw [← neg_sub, map_neg, Finsupp.neg_apply, norm_neg]
      rwa [e] at this
    show p (x - x0) < ε
    let K := (b.repr (x - x0)).support
    have h1 := sn_le_sum b p (x - x0) K (fun i hi => Finsupp.notMem_support_iff.1 hi)
    have h2 : ∑ i ∈ K, p (b i) * ‖b.repr (x - x0) i‖ ≤ ∑ i ∈ K, ((1 : ℝ) / 2) ^ enc i * (ε / 3) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have e : p (b i) * ‖b.repr (x - x0) i‖ =
          ((1 : ℝ) / 2) ^ enc i * (w' i * ‖b.repr (x - x0) i‖) := by
        simp only [w']
        rw [one_div, inv_pow]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (hi i).le (by positivity)
    have h3 : ∑ i ∈ K, ((1 : ℝ) / 2) ^ enc i * (ε / 3) ≤ 2 * (ε / 3) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (geo_sum enc henc K) (by positivity)
    linarith

lemma fin_montel : IsMontel E :=
  ⟨fin_hlcs hE, fun _ hc hB => fin_compact hE b enc henc hc hB,
    ⟨fin_reflexive_pt hE b enc henc, fin_sb hE b enc henc⟩⟩

end bidual

section helpers

lemma eqc_bound {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] {κ : Type*}
    {q : SeminormFamily ℂ V κ} (hq : WithSeminorms q) {A : Set (StrongDual ℂ V)}
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ V) : V → ℂ))) :
    ∃ σ : Seminorm ℂ V, Continuous σ ∧ ∀ a ∈ A, ∀ x, ‖a x‖ ≤ σ x := by
  have h0 := hA 0
  rw [Metric.equicontinuousAt_iff_right] at h0
  obtain ⟨s, r, hr, hsr⟩ := (hq.mem_nhds_iff 0 _).1 (h0 1 one_pos)
  refine ⟨(1 / r).toNNReal • s.sup q, ?_, ?_⟩
  · have h := (hq.finset_sups.continuous_seminorm s).const_smul ((1 / r).toNNReal)
    rw [Seminorm.coe_smul]
    exact h
  · intro a ha x
    have key : ∀ y, (s.sup q) y < r → ((normSeminorm ℂ ℂ).comp (a : V →ₗ[ℂ] ℂ)) y ≤ 1 := by
      intro y hy
      have hy' : y ∈ (s.sup q).ball 0 r := by rw [Seminorm.mem_ball_zero]; exact hy
      have h := hsr hy' ⟨a, ha⟩
      simp only [map_zero, dist_zero_left] at h
      exact h.le
    have h := sn_scale hr zero_le_one key x
    have e : ((1 / r).toNNReal • s.sup q) x = 1 / r * (s.sup q) x := by
      rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity)]
    rw [e]
    exact h

lemma eqc_of_bound {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (A : Set (StrongDual ℂ V)) (σ : Seminorm ℂ V) (hσ : Continuous σ)
    (h : ∀ a ∈ A, ∀ x, ‖a x‖ ≤ σ x) :
    Equicontinuous (fun a : A => ((a : StrongDual ℂ V) : V → ℂ)) := by
  apply equicontinuous_of_equicontinuousAt_zero (fun a : A => (a : StrongDual ℂ V))
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hev : ∀ᶠ x in 𝓝 (0 : V), σ x < ε := by
    have := hσ.tendsto 0
    rw [map_zero] at this
    exact this.eventually (Iio_mem_nhds hε)
  filter_upwards [hev] with x hx a
  simp only [Function.comp_apply, map_zero, dist_zero_left]
  exact lt_of_le_of_lt (h a a.2 x) hx

lemma hb_norm {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] {κ : Type*}
    {q : SeminormFamily ℂ V κ} (hq : WithSeminorms q) (β : Seminorm ℂ V) (hβ : Continuous β)
    (y : V) : ∃ g : StrongDual ℂ V, (∀ z, ‖g z‖ ≤ β z) ∧ ‖g y‖ = β y := by
  have : PolynormableSpace ℂ V := hq.toPolynormableSpace
  by_cases hy : y = 0
  · exact ⟨0, fun z => by simp, by simp [hy]⟩
  · let T := LinearEquiv.toSpanNonzeroSingleton ℂ V y hy
    let f : Module.Dual ℂ (ℂ ∙ y) := (β y : ℂ) • (T.symm : (ℂ ∙ y) →ₗ[ℂ] ℂ)
    have hf : ∀ z : (ℂ ∙ y), ‖f z‖ ≤ β z := by
      intro z
      have hz : T.symm z • y = (z : V) := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℂ V y hy z
      rw [← hz, map_smul_eq_mul]
      simp only [f, LinearMap.smul_apply, LinearEquiv.coe_coe, smul_eq_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg β y)]
      rw [mul_comm]
    obtain ⟨g, hg, hgle⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm (ℂ ∙ y) f hβ hf
    refine ⟨g, hgle, ?_⟩
    have h1 := hg ⟨y, Submodule.mem_span_singleton_self y⟩
    have h2 : T.symm ⟨y, Submodule.mem_span_singleton_self y⟩ = 1 := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      simp [T]
    have h3 : g y = (β y : ℂ) := by
      rw [h1]
      simp only [f, LinearMap.smul_apply, LinearEquiv.coe_coe, h2, smul_eq_mul, mul_one]
    rw [h3, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg β y)]

end helpers

section nucphi

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {ι : Type u} (b : Module.Basis ι ℂ E)
variable {F : Type u} [AddCommGroup F] [Module ℂ F]

noncomputable def kapA (a : E →ₗ[ℂ] ℂ) : E ⊗[ℂ] F →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap ∘ₗ TensorProduct.map a LinearMap.id

omit τE in
@[simp] lemma kapA_tmul (a : E →ₗ[ℂ] ℂ) (x : E) (y : F) :
    kapA (F := F) a (x ⊗ₜ y) = a x • y := by
  simp [kapA]

noncomputable def kap (i : ι) : E ⊗[ℂ] F →ₗ[ℂ] F := kapA (b.coord i)

omit τE in
lemma kap_tmul (i : ι) (x : E) (y : F) : kap (F := F) b i (x ⊗ₜ y) = b.repr x i • y := by
  simp [kap]

omit τE in
lemma decomp (w : E ⊗[ℂ] F) : ∃ s : Finset ι, (∀ i ∉ s, kap b i w = 0) ∧
    w = ∑ i ∈ s, b i ⊗ₜ kap b i w := by
  classical
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun i _ => map_zero _, by simp⟩
  | tmul x y =>
    refine ⟨(b.repr x).support, fun i hi => by
      rw [kap_tmul, Finsupp.notMem_support_iff.1 hi, zero_smul], ?_⟩
    simp_rw [kap_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, repr_sum]
  | add u v hu hv =>
    obtain ⟨s, hs, hus⟩ := hu
    obtain ⟨t, ht, hvt⟩ := hv
    refine ⟨s ∪ t, fun i hi => ?_, ?_⟩
    · simp only [Finset.mem_union, not_or] at hi
      rw [map_add, hs i hi.1, ht i hi.2, add_zero]
    · have e1 : ∑ i ∈ s ∪ t, b i ⊗ₜ kap b i u = u := by
        rw [← Finset.sum_subset Finset.subset_union_left (fun i _ hi => by rw [hs i hi, tmul_zero])]
        exact hus.symm
      have e2 : ∑ i ∈ s ∪ t, b i ⊗ₜ kap b i v = v := by
        rw [← Finset.sum_subset Finset.subset_union_right (fun i _ hi => by rw [ht i hi, tmul_zero])]
        exact hvt.symm
      simp_rw [map_add, tmul_add, Finset.sum_add_distrib, e1, e2]

omit τE in
lemma decomp_superset (w : E ⊗[ℂ] F) (s t : Finset ι) (hst : s ⊆ t) (hs : ∀ i ∉ s, kap b i w = 0)
    (hw : w = ∑ i ∈ s, b i ⊗ₜ kap b i w) : w = ∑ i ∈ t, b i ⊗ₜ kap b i w := by
  rw [← Finset.sum_subset hst (fun i _ hi => by rw [hs i hi, tmul_zero])]
  exact hw

lemma tf_sum [TopologicalSpace F] (a : StrongDual ℂ E) (g : StrongDual ℂ F) (w : E ⊗[ℂ] F)
    (s : Finset ι) (hw : w = ∑ i ∈ s, b i ⊗ₜ kap b i w) :
    tensorFunctional E F (a, g) w = ∑ i ∈ s, a (b i) * g (kap b i w) := by
  conv_lhs => rw [hw]
  simp [tensorFunctional, map_sum]

lemma tf_sub [TopologicalSpace F] (ab : StrongDual ℂ E × StrongDual ℂ F) (u v : E ⊗[ℂ] F) :
    tensorFunctional E F ab (u - v) = tensorFunctional E F ab u - tensorFunctional E F ab v := by
  simp [tensorFunctional, map_sub]

noncomputable def Nsn (α : Seminorm ℂ E) (β : Seminorm ℂ F) : Seminorm ℂ (E ⊗[ℂ] F) :=
  fsn (fun i => (nnw b α i) • β.comp (kap b i)) (fun w => by
    obtain ⟨s, hs, -⟩ := decomp b w
    apply s.finite_toSet.subset
    intro i hi
    by_contra h'
    apply hi
    simp [hs i h'])

omit τE in
lemma Nsn_eq (α : Seminorm ℂ E) (β : Seminorm ℂ F) (w : E ⊗[ℂ] F) (s : Finset ι)
    (hs : ∀ i ∉ s, kap b i w = 0) : Nsn b α β w = ∑ i ∈ s, α (b i) * β (kap b i w) := by
  rw [Nsn, fsn_eq_sum _ _ w s (fun i hi => by simp [hs i hi])]
  rfl

omit τE in
lemma Nsn_tmul (α : Seminorm ℂ E) (β : Seminorm ℂ F) (x : E) (y : F) :
    Nsn b α β (x ⊗ₜ y) = wsn b (nnw b α) x * β y := by
  have hs : ∀ i ∉ (b.repr x).support, b.repr x i = 0 := fun i hi => Finsupp.notMem_support_iff.1 hi
  rw [Nsn_eq b α β _ (b.repr x).support (fun i hi => by rw [kap_tmul, hs i hi, zero_smul]),
    wsn_eq_sum b _ x _ hs, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kap_tmul, map_smul_eq_mul, show ((nnw b α i : NNReal) : ℝ) = α (b i) from rfl]
  ring

end nucphi

section nucphi2

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {ι : Type u} (hE : IsFin E) (b : Module.Basis ι ℂ E) (enc : ι → ℕ) (henc : Injective enc)
variable {F : Type u} [AddCommGroup F] [Module ℂ F] [τF : TopologicalSpace F]
variable {κ : Type u} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)

/-- the index type of the seminorms of the tensor topology -/
abbrev TI (E F : Type u) [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] : Type u :=
  Seminorm ℂ E × {β : Seminorm ℂ F // Continuous β}

noncomputable def fam : SeminormFamily ℂ (E ⊗[ℂ] F) (TI E F) := fun ab => Nsn b ab.1 ab.2.1

include hE b hq

lemma tN_tmul_cont [t : TopologicalSpace (E ⊗[ℂ] F)] (ht : WithSeminorms (fam b (F := F))) :
    Continuous (fun p : E × F => p.1 ⊗ₜ[ℂ] p.2) := by
  have := fin_tag hE
  have := hq.topologicalAddGroup
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, y0⟩
  rw [ContinuousAt, ht.tendsto_nhds]
  rintro ⟨α, β, hβ⟩ ε hε
  let W := wsn b (nnw b α)
  have hW := fin_cont hE W
  let g : E × F → ℝ := fun p => W (p.1 - x0) * β (p.2 - y0) + W x0 * β (p.2 - y0) +
    W (p.1 - x0) * β y0
  have hg : Continuous g := by
    have h1 : Continuous fun p : E × F => W (p.1 - x0) :=
      hW.comp (continuous_fst.sub continuous_const)
    have h2 : Continuous fun p : E × F => β (p.2 - y0) :=
      hβ.comp (continuous_snd.sub continuous_const)
    exact ((h1.mul h2).add (continuous_const.mul h2)).add (h1.mul continuous_const)
  have hg0 : g (x0, y0) = 0 := by simp [g]
  have hev := (hg.tendsto (x0, y0)).eventually (Iio_mem_nhds (show g (x0, y0) < ε by rw [hg0]; exact hε))
  filter_upwards [hev] with p hp
  show Nsn b α β (p.1 ⊗ₜ p.2 - x0 ⊗ₜ y0) < ε
  have e : p.1 ⊗ₜ[ℂ] p.2 - x0 ⊗ₜ y0 =
      (p.1 - x0) ⊗ₜ (p.2 - y0) + x0 ⊗ₜ (p.2 - y0) + (p.1 - x0) ⊗ₜ y0 := by
    simp only [sub_tmul, tmul_sub]; abel
  rw [e]
  have h1 := map_add_le_add (Nsn b α β) ((p.1 - x0) ⊗ₜ[ℂ] (p.2 - y0) + x0 ⊗ₜ (p.2 - y0))
    ((p.1 - x0) ⊗ₜ y0)
  have h2 := map_add_le_add (Nsn b α β) ((p.1 - x0) ⊗ₜ[ℂ] (p.2 - y0)) (x0 ⊗ₜ (p.2 - y0))
  rw [Nsn_tmul, Nsn_tmul] at h2
  rw [Nsn_tmul] at h1
  have hp' : g p < ε := hp
  simp only [g] at hp'
  linarith

lemma tN_le_eps [t : TopologicalSpace (E ⊗[ℂ] F)] (ht : WithSeminorms (fam b (F := F))) :
    t ≤ epsTensorTopology E F := by
  have := ht.topologicalAddGroup
  rw [epsTensorTopology, ← continuous_iff_le_induced, continuous_iff_continuousAt]
  intro u0
  rw [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rintro S ⟨A, B, hA, hB, rfl⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨α, -, hα⟩ := eqc_bound hE hA
  obtain ⟨β, hβ, hβB⟩ := eqc_bound hq hB
  have hN := ht.continuous_seminorm ((α, ⟨β, hβ⟩) : TI E F)
  have hev : ∀ᶠ u in 𝓝 u0, Nsn b α β (u - u0) < ε := by
    have h : Tendsto (fun u => Nsn b α β (u - u0)) (𝓝 u0) (𝓝 (Nsn b α β (u0 - u0))) :=
      (hN.comp (continuous_sub_right u0)).tendsto u0
    rw [sub_self, map_zero] at h
    exact h.eventually (Iio_mem_nhds hε)
  filter_upwards [hev] with u hu
  rintro ⟨a, g⟩ ⟨ha, hg⟩
  change dist (tensorFunctional E F (a, g) u0) (tensorFunctional E F (a, g) u) < ε
  rw [dist_eq_norm, norm_sub_rev, ← tf_sub]
  obtain ⟨s, hs, hw⟩ := decomp b (u - u0)
  rw [tf_sum b a g _ s hw]
  calc ‖∑ i ∈ s, a (b i) * g (kap b i (u - u0))‖
      ≤ ∑ i ∈ s, ‖a (b i) * g (kap b i (u - u0))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, α (b i) * β (kap b i (u - u0)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hα a ha _) (hβB g hg _) (norm_nonneg _) (apply_nonneg _ _)
    _ = Nsn b α β (u - u0) := (Nsn_eq b α β _ s hs).symm
    _ < ε := hu

lemma bil_bound [t : TopologicalSpace (E ⊗[ℂ] F)] {ι' : Type*}
    {p : SeminormFamily ℂ (E ⊗[ℂ] F) ι'} (hp : WithSeminorms p)
    (hc : Continuous (fun p : E × F => p.1 ⊗ₜ[ℂ] p.2)) (k : ι') :
    ∃ α0 : Seminorm ℂ E, ∃ β0 : Seminorm ℂ F, Continuous β0 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x y, p k (x ⊗ₜ y) ≤ c * α0 x * β0 y := by
  have h0 : (fun p : E × F => p.1 ⊗ₜ[ℂ] p.2) ⁻¹' {u | p k u < 1} ∈ 𝓝 ((0 : E), (0 : F)) := by
    apply hc.continuousAt.preimage_mem_nhds
    show (p k) ⁻¹' Set.Iio 1 ∈ 𝓝 ((0 : E) ⊗ₜ[ℂ] (0 : F))
    rw [zero_tmul]
    exact (hp.continuous_seminorm k).continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact Iio_mem_nhds one_pos)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at h0
  obtain ⟨U, hU, V, hV, hUV⟩ := h0
  obtain ⟨s, r, hr, hsU⟩ := (WithSeminorms.mem_nhds_iff hE 0 U).1 hU
  obtain ⟨s', r', hr', hsV⟩ := (hq.mem_nhds_iff 0 V).1 hV
  let α0 : Seminorm ℂ E := s.sup (fun p => p)
  let β0 : Seminorm ℂ F := s'.sup q
  have key : ∀ x y, α0 x < r → β0 y < r' → p k (x ⊗ₜ y) < 1 := by
    intro x y hx hy
    have hxU : x ∈ U := hsU (by rw [Seminorm.mem_ball_zero]; exact hx)
    have hyV : y ∈ V := hsV (by rw [Seminorm.mem_ball_zero]; exact hy)
    exact hUV (Set.mk_mem_prod hxU hyV)
  have step1 : ∀ y, β0 y < r' → ∀ x, p k (x ⊗ₜ y) ≤ 1 / r * α0 x := by
    intro y hy x
    have := sn_scale (σ := (p k).comp ((TensorProduct.mk ℂ E F).flip y)) (β := α0) hr zero_le_one
      (fun x hx => by
        show p k (x ⊗ₜ y) ≤ 1
        exact (key x y hx hy).le) x
    exact this
  refine ⟨α0, β0, hq.finset_sups.continuous_seminorm s', 1 / (r * r'), by positivity,
    fun x y => ?_⟩
  have := sn_scale (σ := (p k).comp (TensorProduct.mk ℂ E F x)) (β := β0) hr'
    (M := 1 / r * α0 x) (by positivity) (fun y hy => step1 y hy x) y
  have e : 1 / r * α0 x / r' * β0 y = 1 / (r * r') * α0 x * β0 y := by
    field_simp
  rw [← e]
  exact this

include henc

lemma eps_le_pi (t' : TopologicalSpace (E ⊗[ℂ] F))
    (ht' : t' ∈ {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧
      @Continuous (E × F) (E ⊗[ℂ] F) _ t (fun p => p.1 ⊗ₜ[ℂ] p.2)}) :
    epsTensorTopology E F ≤ t' := by
  classical
  obtain ⟨⟨ι', _, p, hp⟩, hc⟩ := ht'
  have := fin_tag hE
  have := hq.topologicalAddGroup
  refine (@continuous_id_iff_le _ (epsTensorTopology E F) t').1 ?_
  rw [@continuous_iff_continuousAt _ _ (epsTensorTopology E F) t']
  intro u0
  show Tendsto id (@nhds _ (epsTensorTopology E F) u0) (𝓝 u0)
  rw [hp.tendsto_nhds id u0]
  intro k ε hε
  obtain ⟨α0, β0, hβ0, c, hc0, hbil⟩ := bil_bound hE b hq hp hc k
  let w' : ι → ℝ := fun i => 2 ^ enc i * α0 (b i)
  let A : Set (StrongDual ℂ E) := Set.range fun i => ((w' i : ℂ)) • cf hE b i
  let B : Set (StrongDual ℂ F) := {g | ∀ y, ‖g y‖ ≤ β0 y}
  have hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ)) := by
    refine eqc_of_bound A (wsn b (fun i => (w' i).toNNReal)) (fin_cont hE _) ?_
    rintro _ ⟨i, rfl⟩ x
    have h := term_le_wsn b (fun i => (w' i).toNNReal) x i
    rw [Real.coe_toNNReal _ (by positivity)] at h
    rw [smul_apply, cf_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h
  have hB : Equicontinuous (fun g : B => ((g : StrongDual ℂ F) : F → ℂ)) :=
    eqc_of_bound B β0 hβ0 (fun g hg => hg)
  let 𝔖 : Set (Set (StrongDual ℂ E × StrongDual ℂ F)) :=
    {S | ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
      Equicontinuous (fun a : A => (a : E → ℂ)) ∧
      Equicontinuous (fun b : B => (b : F → ℂ)) ∧ S = A ×ˢ B}
  have hS : A ×ˢ B ∈ 𝔖 := ⟨A, B, hA, hB, rfl⟩
  let Φ : E ⊗[ℂ] F → _ := fun u => UniformOnFun.ofFun 𝔖 (fun ab => tensorFunctional E F ab u)
  have hT : Tendsto Φ (@nhds _ (epsTensorTopology E F) u0) (𝓝 (Φ u0)) := by
    show Tendsto Φ (@nhds _ (TopologicalSpace.induced Φ inferInstance) u0) (𝓝 (Φ u0))
    rw [nhds_induced]
    exact tendsto_comap
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hT
  let δ : ℝ := ε / (2 * c + 1)
  have hδ : 0 < δ := by positivity
  have hev := Metric.tendstoUniformlyOn_iff.1 (hT _ hS) δ hδ
  filter_upwards [hev] with u hu
  show p k (id u - u0) < ε
  obtain ⟨s, hs, hw⟩ := decomp b (u - u0)
  have hj : ∀ j, w' j * β0 (kap b j (u - u0)) < δ := by
    intro j
    obtain ⟨g, hgB, hgy⟩ := hb_norm hq β0 hβ0 (kap b j (u - u0))
    have h1 := hu ((w' j : ℂ) • cf hE b j, g) ⟨⟨j, rfl⟩, hgB⟩
    change dist (tensorFunctional E F (((w' j : ℂ)) • cf hE b j, g) u0)
      (tensorFunctional E F (((w' j : ℂ)) • cf hE b j, g) u) < δ at h1
    rw [dist_eq_norm, norm_sub_rev, ← tf_sub] at h1
    have hw' := decomp_superset b (u - u0) s (insert j s) (Finset.subset_insert j s) hs hw
    rw [tf_sum b _ g _ (insert j s) hw'] at h1
    have e : ∑ i ∈ insert j s, (((w' j : ℂ)) • cf hE b j) (b i) * g (kap b i (u - u0)) =
        (w' j : ℂ) * g (kap b j (u - u0)) := by
      simp only [smul_apply, cf_basis, smul_eq_mul, mul_ite, mul_one,
        mul_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' (insert j s) j, if_pos (Finset.mem_insert_self j s)]
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hgy] at h1
    exact h1
  have e1 : p k (u - u0) ≤ ∑ i ∈ s, p k (b i ⊗ₜ kap b i (u - u0)) := by
    conv_lhs => rw [hw]
    exact Finset.le_sum_of_subadditive (p k) (map_zero _).le (map_add_le_add _) _ _
  have e2 : ∑ i ∈ s, p k (b i ⊗ₜ kap b i (u - u0)) ≤ ∑ i ∈ s, ((1 : ℝ) / 2) ^ enc i * (c * δ) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hbil (b i) (kap b i (u - u0))
    have e : c * α0 (b i) * β0 (kap b i (u - u0)) =
        ((1 : ℝ) / 2) ^ enc i * (c * (w' i * β0 (kap b i (u - u0)))) := by
      simp only [w']
      rw [one_div, inv_pow]
      field_simp
    rw [e] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mul_le_mul_of_nonneg_left (hj i).le hc0.le
  have e3 : ∑ i ∈ s, ((1 : ℝ) / 2) ^ enc i * (c * δ) ≤ 2 * (c * δ) := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (geo_sum enc henc s) (by positivity)
  have e4 : 2 * (c * δ) < ε := by
    show 2 * (c * (ε / (2 * c + 1))) < ε
    rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  show p k (u - u0) < ε
  linarith

end nucphi2

section nucphi3

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {ι : Type u} (hE : IsFin E) (b : Module.Basis ι ℂ E) (enc : ι → ℕ) (henc : Injective enc)
include hE b henc

lemma fin_nuclear : IsNuclear E := by
  refine ⟨fin_hlcs hE, fun F _ _ τF hF => ?_⟩
  obtain ⟨⟨κ, _, q, hq⟩, -⟩ := hF
  apply le_antisymm
  · let tN : TopologicalSpace (E ⊗[ℂ] F) := (fam b (F := F)).moduleFilterBasis.topology
    have htN : @WithSeminorms ℂ (E ⊗[ℂ] F) (TI E F) _ _ _ (fam b (F := F)) tN := ⟨rfl⟩
    have hne : Nonempty (TI E F) := ⟨(0, ⟨0, by rw [FunLike.coe_zero]; exact continuous_zero⟩)⟩
    calc projTensorTopology E F ≤ tN :=
          sInf_le ⟨⟨TI E F, hne, fam b, htN⟩, tN_tmul_cont hE b hq (t := tN) htN⟩
      _ ≤ epsTensorTopology E F := tN_le_eps hE b hq (t := tN) htN
  · exact le_sInf fun t ht => eps_le_pi hE b enc henc hq t ht

end nucphi3

section bilgen

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [τV : TopologicalSpace V]
variable {F : Type u} [AddCommGroup F] [Module ℂ F] [τF : TopologicalSpace F]

lemma bilb {κV : Type*} {qV : SeminormFamily ℂ V κV} (hqV : WithSeminorms qV)
    {κ : Type*} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)
    [t : TopologicalSpace (V ⊗[ℂ] F)] {ι' : Type*}
    {p : SeminormFamily ℂ (V ⊗[ℂ] F) ι'} (hp : WithSeminorms p)
    (hc : Continuous (fun p : V × F => p.1 ⊗ₜ[ℂ] p.2)) (k : ι') :
    ∃ s : Finset κV, ∃ β0 : Seminorm ℂ F, Continuous β0 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x y, p k (x ⊗ₜ y) ≤ c * (s.sup qV) x * β0 y := by
  have h0 : (fun p : V × F => p.1 ⊗ₜ[ℂ] p.2) ⁻¹' {u | p k u < 1} ∈ 𝓝 ((0 : V), (0 : F)) := by
    apply hc.continuousAt.preimage_mem_nhds
    show (p k) ⁻¹' Set.Iio 1 ∈ 𝓝 ((0 : V) ⊗ₜ[ℂ] (0 : F))
    rw [zero_tmul]
    exact (hp.continuous_seminorm k).continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact Iio_mem_nhds one_pos)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at h0
  obtain ⟨U, hU, W, hW, hUW⟩ := h0
  obtain ⟨s, r, hr, hsU⟩ := (hqV.mem_nhds_iff 0 U).1 hU
  obtain ⟨s', r', hr', hsW⟩ := (hq.mem_nhds_iff 0 W).1 hW
  let α0 : Seminorm ℂ V := s.sup qV
  let β0 : Seminorm ℂ F := s'.sup q
  have key : ∀ x y, α0 x < r → β0 y < r' → p k (x ⊗ₜ y) < 1 := by
    intro x y hx hy
    have hxU : x ∈ U := hsU (by rw [Seminorm.mem_ball_zero]; exact hx)
    have hyW : y ∈ W := hsW (by rw [Seminorm.mem_ball_zero]; exact hy)
    exact hUW (Set.mk_mem_prod hxU hyW)
  have step1 : ∀ y, β0 y < r' → ∀ x, p k (x ⊗ₜ y) ≤ 1 / r * α0 x := by
    intro y hy x
    exact sn_scale (σ := (p k).comp ((TensorProduct.mk ℂ V F).flip y)) (β := α0) hr zero_le_one
      (fun x hx => by
        show p k (x ⊗ₜ y) ≤ 1
        exact (key x y hx hy).le) x
  refine ⟨s, β0, hq.finset_sups.continuous_seminorm s', 1 / (r * r'), by positivity,
    fun x y => ?_⟩
  have := sn_scale (σ := (p k).comp (TensorProduct.mk ℂ V F x)) (β := β0) hr'
    (M := 1 / r * α0 x) (by positivity) (fun y hy => step1 y hy x) y
  have e : 1 / r * α0 x / r' * β0 y = 1 / (r * r') * α0 x * β0 y := by
    field_simp
  rw [← e]
  exact this

lemma tf_kapA (a : StrongDual ℂ V) (g : StrongDual ℂ F) (w : V ⊗[ℂ] F) :
    tensorFunctional V F (a, g) w = g (kapA (a : V →ₗ[ℂ] ℂ) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul x y => simp [tensorFunctional, kapA_tmul]
  | add u v hu hv =>
    rw [map_add, map_add, ← hu, ← hv]
    simp [tensorFunctional, map_add]

end bilgen

section nucomega

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [τV : TopologicalSpace V]
variable {ι : Type u} (d : ι → V →ₗ[ℂ] ℂ) (e : ι → V)
variable {F : Type u} [AddCommGroup F] [Module ℂ F]

open Classical in
noncomputable def Msn (J : Finset ι) (β : Seminorm ℂ F) : Seminorm ℂ (V ⊗[ℂ] F) :=
  fsn (fun i => (if i ∈ J then (1 : NNReal) else 0) • β.comp (kapA (d i))) (fun w => by
    apply J.finite_toSet.subset
    intro i hi
    by_contra h'
    apply hi
    simp only [Finset.mem_coe] at h'
    simp [h'])

omit τV in
lemma Msn_eq (J : Finset ι) (β : Seminorm ℂ F) (w : V ⊗[ℂ] F) :
    Msn d J β w = ∑ i ∈ J, β (kapA (d i) w) := by
  classical
  rw [Msn, fsn_eq_sum _ _ w J (fun i hi => by simp [if_neg hi])]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [if_pos hi]

omit τV in
lemma Msn_tmul (J : Finset ι) (β : Seminorm ℂ F) (x : V) (y : F) :
    Msn d J β (x ⊗ₜ y) = (∑ i ∈ J, ‖d i x‖) * β y := by
  rw [Msn_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kapA_tmul, map_smul_eq_mul]

abbrev TJ (ι F : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] : Type u :=
  Finset ι × {β : Seminorm ℂ F // Continuous β}

variable [τF : TopologicalSpace F]

noncomputable def famω : SeminormFamily ℂ (V ⊗[ℂ] F) (TJ ι F) := fun Jb => Msn d Jb.1 Jb.2.1

variable [DecidableEq ι] {κ : Type u} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)
variable (hd : ∀ i, Continuous (d i)) (hde : ∀ i j, d i (e j) = if i = j then 1 else 0)
variable (hV : WithSeminorms (fun i => (normSeminorm ℂ ℂ).comp (d i)))

include hq hd hV

lemma tM_tmul_cont [t : TopologicalSpace (V ⊗[ℂ] F)] (ht : WithSeminorms (famω d (F := F))) :
    Continuous (fun p : V × F => p.1 ⊗ₜ[ℂ] p.2) := by
  have := hV.topologicalAddGroup
  have := hq.topologicalAddGroup
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, y0⟩
  rw [ContinuousAt, ht.tendsto_nhds]
  rintro ⟨J, β, hβ⟩ ε hε
  let W : V → ℝ := fun x => ∑ i ∈ J, ‖d i x‖
  have hW : Continuous W := continuous_finsetSum _ fun i _ => continuous_norm.comp (hd i)
  let g : V × F → ℝ := fun p => W (p.1 - x0) * β (p.2 - y0) + W x0 * β (p.2 - y0) +
    W (p.1 - x0) * β y0
  have hg : Continuous g := by
    have h1 : Continuous fun p : V × F => W (p.1 - x0) :=
      hW.comp (continuous_fst.sub continuous_const)
    have h2 : Continuous fun p : V × F => β (p.2 - y0) :=
      hβ.comp (continuous_snd.sub continuous_const)
    exact ((h1.mul h2).add (continuous_const.mul h2)).add (h1.mul continuous_const)
  have hg0 : g (x0, y0) = 0 := by simp [g, W]
  have hev := (hg.tendsto (x0, y0)).eventually
    (Iio_mem_nhds (show g (x0, y0) < ε by rw [hg0]; exact hε))
  filter_upwards [hev] with p hp
  show Msn d J β (p.1 ⊗ₜ p.2 - x0 ⊗ₜ y0) < ε
  have e : p.1 ⊗ₜ[ℂ] p.2 - x0 ⊗ₜ y0 =
      (p.1 - x0) ⊗ₜ (p.2 - y0) + x0 ⊗ₜ (p.2 - y0) + (p.1 - x0) ⊗ₜ y0 := by
    simp only [sub_tmul, tmul_sub]; abel
  rw [e]
  have h1 := map_add_le_add (Msn d J β) ((p.1 - x0) ⊗ₜ[ℂ] (p.2 - y0) + x0 ⊗ₜ (p.2 - y0))
    ((p.1 - x0) ⊗ₜ y0)
  have h2 := map_add_le_add (Msn d J β) ((p.1 - x0) ⊗ₜ[ℂ] (p.2 - y0)) (x0 ⊗ₜ (p.2 - y0))
  rw [Msn_tmul, Msn_tmul] at h2
  rw [Msn_tmul] at h1
  have hp' : g p < ε := hp
  simp only [g, W] at hp'
  linarith

include hde

/-- a functional dominated by finitely many coordinates is a combination of them -/
lemma dom_comb (a : V →ₗ[ℂ] ℂ) (s : Finset ι) (C : ℝ)
    (ha : ∀ v, ‖a v‖ ≤ C * (s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)) v) (v : V) :
    a v = ∑ i ∈ s, a (e i) * d i v := by
  classical
  let v' := v - ∑ i ∈ s, d i v • e i
  have hv' : ∀ j ∈ s, d j v' = 0 := by
    intro j hj
    simp only [v', map_sub, map_sum, map_smul, hde, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos hj, sub_self]
  have h0 : (s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)) v' ≤ 0 :=
    Seminorm.finset_sup_apply_le le_rfl fun j hj => by simp [hv' j hj]
  have hz : (s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)) v' = 0 :=
    le_antisymm h0 (apply_nonneg _ _)
  have h1 : a v' = 0 := by
    have h2 : ‖a v'‖ ≤ 0 := by
      have := ha v'
      rwa [hz, mul_zero] at this
    exact norm_le_zero_iff.1 h2
  have : a v = a v' + ∑ i ∈ s, d i v * a (e i) := by
    simp only [v', map_sub, map_sum, map_smul, smul_eq_mul, sub_add_cancel]
  rw [this, h1, zero_add]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma tM_le_eps [t : TopologicalSpace (V ⊗[ℂ] F)] (ht : WithSeminorms (famω d (F := F))) :
    t ≤ epsTensorTopology V F := by
  classical
  have := ht.topologicalAddGroup
  rw [epsTensorTopology, ← continuous_iff_le_induced, continuous_iff_continuousAt]
  intro u0
  rw [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rintro S ⟨A, B, hA, hB, rfl⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨σ, hσ, hσA⟩ := eqc_bound hV hA
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hV σ hσ
  obtain ⟨β, hβ, hβB⟩ := eqc_bound hq hB
  have haC : ∀ a ∈ A, ∀ v, ‖a v‖ ≤ C * (s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)) v :=
    fun a ha v => (hσA a ha v).trans (hC v)
  have hae : ∀ a ∈ A, ∀ i ∈ s, ‖a (e i)‖ ≤ C := by
    intro a ha i hi
    have h1 := haC a ha (e i)
    have h2 : (s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)) (e i) ≤ 1 :=
      Seminorm.finset_sup_apply_le zero_le_one fun j _ => by
        simp only [Seminorm.comp_apply, coe_normSeminorm, hde]
        split_ifs <;> simp
    calc ‖a (e i)‖ ≤ C * (s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)) (e i) := h1
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left h2 C.2
      _ = C := mul_one _
  have hN := ht.continuous_seminorm ((s, ⟨β, hβ⟩) : TJ ι F)
  have hev : ∀ᶠ u in 𝓝 u0, Msn d s β (u - u0) < ε / (C + 1) := by
    have h : Tendsto (fun u => Msn d s β (u - u0)) (𝓝 u0) (𝓝 (Msn d s β (u0 - u0))) :=
      (hN.comp (continuous_sub_right u0)).tendsto u0
    rw [sub_self, map_zero] at h
    exact h.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hev] with u hu
  rintro ⟨a, g⟩ ⟨ha, hg⟩
  change dist (tensorFunctional V F (a, g) u0) (tensorFunctional V F (a, g) u) < ε
  rw [dist_eq_norm, norm_sub_rev, ← tf_sub]
  have hform : ∀ w, tensorFunctional V F (a, g) w = ∑ i ∈ s, a (e i) * g (kapA (d i) w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp [tensorFunctional]
    | tmul x y =>
      simp only [tensorFunctional, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
        TensorProduct.lid_tmul, smul_eq_mul, kapA_tmul, map_smul]
      have hdc := dom_comb d e hq hd hde hV (a : V →ₗ[ℂ] ℂ) s C (haC a ha) x
      simp only [ContinuousLinearMap.coe_coe] at hdc
      rw [hdc, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    | add w1 w2 h1 h2 =>
      rw [show tensorFunctional V F (a, g) (w1 + w2) =
        tensorFunctional V F (a, g) w1 + tensorFunctional V F (a, g) w2 by
          simp [tensorFunctional, map_add], h1, h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, map_add, mul_add]
  rw [hform]
  calc ‖∑ i ∈ s, a (e i) * g (kapA (d i) (u - u0))‖
      ≤ ∑ i ∈ s, ‖a (e i) * g (kapA (d i) (u - u0))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, C * β (kapA (d i) (u - u0)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (hae a ha i hi) (hβB g hg _) (norm_nonneg _) C.2
    _ = C * Msn d s β (u - u0) := by rw [Msn_eq, Finset.mul_sum]
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hu.le C.2
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [C.2]

lemma eps_le_piω (t' : TopologicalSpace (V ⊗[ℂ] F))
    (ht' : t' ∈ {t | IsLocallyConvexTopology (V ⊗[ℂ] F) t ∧
      @Continuous (V × F) (V ⊗[ℂ] F) _ t (fun p => p.1 ⊗ₜ[ℂ] p.2)}) :
    epsTensorTopology V F ≤ t' := by
  classical
  obtain ⟨⟨ι', _, p, hp⟩, hc⟩ := ht'
  have := hV.topologicalAddGroup
  have := hq.topologicalAddGroup
  refine (@continuous_id_iff_le _ (epsTensorTopology V F) t').1 ?_
  rw [@continuous_iff_continuousAt _ _ (epsTensorTopology V F) t']
  intro u0
  show Tendsto id (@nhds _ (epsTensorTopology V F) u0) (𝓝 u0)
  rw [hp.tendsto_nhds id u0]
  intro k ε hε
  obtain ⟨s, β0, hβ0, c, hc0, hbil⟩ := bilb hV hq hp hc k
  let α0 : Seminorm ℂ V := s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)
  have hα0e : ∀ i ∈ s, α0 (e i) ≤ 1 := fun i _ =>
    Seminorm.finset_sup_apply_le zero_le_one fun j _ => by
      simp only [Seminorm.comp_apply, coe_normSeminorm, hde]
      split_ifs <;> simp
  -- the remainder map
  let R : V ⊗[ℂ] F →ₗ[ℂ] V ⊗[ℂ] F :=
    LinearMap.id - ∑ i ∈ s, (TensorProduct.mk ℂ V F (e i)) ∘ₗ kapA (d i)
  have hR : ∀ w, p k (R w) = 0 := by
    intro w
    refine le_antisymm ?_ (apply_nonneg _ _)
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have eR : R (x ⊗ₜ y) = (x - ∑ i ∈ s, d i x • e i) ⊗ₜ y := by
        simp only [R, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.comp_apply, kapA_tmul, TensorProduct.mk_apply,
          sub_tmul, TensorProduct.sum_tmul, TensorProduct.smul_tmul]
      rw [eR]
      refine (hbil _ y).trans (le_of_eq ?_)
      have h0 : α0 (x - ∑ i ∈ s, d i x • e i) = 0 := by
        refine le_antisymm (Seminorm.finset_sup_apply_le le_rfl fun j hj => ?_) (apply_nonneg _ _)
        simp only [Seminorm.comp_apply, coe_normSeminorm, map_sub, map_sum, map_smul, hde,
          smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq, if_pos hj, sub_self, norm_zero]
      rw [show (s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)) = α0 from rfl, h0]
      ring
    | add w1 w2 h1 h2 =>
      rw [map_add]
      exact (map_add_le_add _ _ _).trans (by linarith)
  let A : Set (StrongDual ℂ V) := (fun i => (⟨d i, hd i⟩ : StrongDual ℂ V)) '' (s : Set ι)
  let B : Set (StrongDual ℂ F) := {g | ∀ y, ‖g y‖ ≤ β0 y}
  have hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ V) : V → ℂ)) := by
    refine eqc_of_bound A α0 (hV.finset_sups.continuous_seminorm s) ?_
    rintro _ ⟨i, hi, rfl⟩ x
    exact Seminorm.le_finset_sup_apply (p := fun i => (normSeminorm ℂ ℂ).comp (d i)) hi
  have hB : Equicontinuous (fun g : B => ((g : StrongDual ℂ F) : F → ℂ)) :=
    eqc_of_bound B β0 hβ0 (fun g hg => hg)
  let 𝔖 : Set (Set (StrongDual ℂ V × StrongDual ℂ F)) :=
    {S | ∃ (A : Set (StrongDual ℂ V)) (B : Set (StrongDual ℂ F)),
      Equicontinuous (fun a : A => (a : V → ℂ)) ∧
      Equicontinuous (fun b : B => (b : F → ℂ)) ∧ S = A ×ˢ B}
  have hS : A ×ˢ B ∈ 𝔖 := ⟨A, B, hA, hB, rfl⟩
  let Φ : V ⊗[ℂ] F → _ := fun u => UniformOnFun.ofFun 𝔖 (fun ab => tensorFunctional V F ab u)
  have hT : Tendsto Φ (@nhds _ (epsTensorTopology V F) u0) (𝓝 (Φ u0)) := by
    show Tendsto Φ (@nhds _ (TopologicalSpace.induced Φ inferInstance) u0) (𝓝 (Φ u0))
    rw [nhds_induced]
    exact tendsto_comap
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hT
  let δ : ℝ := ε / (c * s.card + 1)
  have hδ : 0 < δ := by positivity
  have hev := Metric.tendstoUniformlyOn_iff.1 (hT _ hS) δ hδ
  filter_upwards [hev] with u hu
  show p k (u - u0) < ε
  have hj : ∀ j ∈ s, β0 (kapA (d j) (u - u0)) < δ := by
    intro j hj
    obtain ⟨g, hgB, hgy⟩ := hb_norm hq β0 hβ0 (kapA (d j) (u - u0))
    have h1 := hu (⟨d j, hd j⟩, g) ⟨⟨j, hj, rfl⟩, hgB⟩
    change dist (tensorFunctional V F (⟨d j, hd j⟩, g) u0)
      (tensorFunctional V F (⟨d j, hd j⟩, g) u) < δ at h1
    rw [dist_eq_norm, norm_sub_rev, ← tf_sub, tf_kapA, hgy] at h1
    exact h1
  have hsplit : u - u0 = R (u - u0) + ∑ i ∈ s, e i ⊗ₜ kapA (d i) (u - u0) := by
    simp [R]
  have e1 : p k (u - u0) ≤ ∑ i ∈ s, p k (e i ⊗ₜ kapA (d i) (u - u0)) := by
    conv_lhs => rw [hsplit]
    refine (map_add_le_add _ _ _).trans ?_
    rw [hR, zero_add]
    exact Finset.le_sum_of_subadditive (p k) (map_zero _).le (map_add_le_add _) _ _
  have e2 : ∑ i ∈ s, p k (e i ⊗ₜ kapA (d i) (u - u0)) ≤ ∑ i ∈ s, c * δ := by
    refine Finset.sum_le_sum fun i hi => ?_
    refine (hbil (e i) _).trans ?_
    have h1 := hα0e i hi
    have h2 := (hj i hi).le
    have h3 := apply_nonneg β0 (kapA (d i) (u - u0))
    have h4 := apply_nonneg α0 (e i)
    calc c * (s.sup fun i => (normSeminorm ℂ ℂ).comp (d i)) (e i) * β0 (kapA (d i) (u - u0))
        = c * α0 (e i) * β0 (kapA (d i) (u - u0)) := rfl
      _ ≤ c * 1 * δ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0.le) h2 h3 (by positivity)
      _ = c * δ := by ring
  have e3 : ∑ i ∈ s, c * δ < ε := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hX : (0 : ℝ) < c * s.card + 1 :=
      add_pos_of_nonneg_of_pos (mul_nonneg hc0.le (Nat.cast_nonneg _)) one_pos
    calc (s.card : ℝ) * (c * δ) = (c * s.card) * δ := by ring
      _ < (c * s.card + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
      _ = ε := by
          show (c * s.card + 1) * (ε / (c * s.card + 1)) = ε
          rw [mul_comm]
          exact div_mul_cancel₀ ε (ne_of_gt hX)
  linarith

omit hq in
lemma omega_nuclear (hT2 : T2Space V) : IsNuclear V := by
  refine ⟨⟨lc_of_ws hV, hT2⟩, fun F _ _ τF hF => ?_⟩
  obtain ⟨⟨κ, _, q, hq⟩, -⟩ := hF
  apply le_antisymm
  · let tM : TopologicalSpace (V ⊗[ℂ] F) := (famω d (F := F)).moduleFilterBasis.topology
    have htM : @WithSeminorms ℂ (V ⊗[ℂ] F) (TJ ι F) _ _ _ (famω d (F := F)) tM := ⟨rfl⟩
    have hne : Nonempty (TJ ι F) := ⟨(∅, ⟨0, by rw [FunLike.coe_zero]; exact continuous_zero⟩)⟩
    calc projTensorTopology V F ≤ tM :=
          sInf_le ⟨⟨TJ ι F, hne, famω d, htM⟩, tM_tmul_cont d hq hd hV (t := tM) htM⟩
      _ ≤ epsTensorTopology V F := tM_le_eps d e hq hd hde hV (t := tM) htM
  · exact le_sInf fun t ht => eps_le_piω d e hq hd hde hV t ht

end nucomega

section dualnuc

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {ι : Type u} (hE : IsFin E) (b : Module.Basis ι ℂ E) (enc : ι → ℕ) (henc : Injective enc)
include hE b henc

lemma dual_nuclear : IsNuclear (StrongDual ℂ E) := by
  classical
  have := fin_csmul hE
  have := fin_tag hE
  refine omega_nuclear (fun i => ev (b i)) (fun i => cf hE b i)
    (fun i => continuous_eval_const (b i)) (fun i j => ?_) (dual_ws hE b enc henc)
    (dual_t2 hE b enc henc)
  show cf hE b j (b i) = if i = j then 1 else 0
  rw [cf_basis]

end dualnuc

section assemble

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]

lemma abstract_all (hE : IsFin E) (hrank : Module.rank ℂ E ≤ Cardinal.aleph0) :
    (Module.rank ℂ E ≤ Cardinal.aleph0 ∧ HasFinestLocallyConvexTopology E ∧ IsStrictLF E) ∧
    (IsHLCS E ∧ IsCompleteTVS E ∧ IsNuclear E ∧ IsMontel E ∧ IsFrechet (StrongDual ℂ E) ∧
      IsNuclear (StrongDual ℂ E)) ∧
    (∀ V : Submodule ℂ E, ∃ W : Submodule ℂ E, IsCompl V W ∧
      Continuous (fun p : V × W => ((p.1 : E) + p.2)) ∧
      IsOpenMap (fun p : V × W => ((p.1 : E) + p.2))) := by
  let b := Module.Basis.ofVectorSpace ℂ E
  have hc : Countable (Module.Basis.ofVectorSpaceIndex ℂ E) := by
    rw [← Cardinal.mk_le_aleph0_iff, b.mk_eq_rank'']
    exact hrank
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat (Module.Basis.ofVectorSpaceIndex ℂ E)
  exact ⟨⟨hrank, fin_hasFinest hE, fin_strictLF hE b enc henc⟩,
    ⟨fin_hlcs hE, fin_complete hE b, fin_nuclear hE b enc henc, fin_montel hE b enc henc,
      dual_frechet hE b enc henc, dual_nuclear hE b enc henc⟩, fun V => fin_compl hE V⟩

end assemble

section padic

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

lemma countable_nf : Countable F := by
  let b := Module.finBasis ℚ F
  exact b.equivFun.injective.countable

lemma ultra_lt {a b : v.adicCompletion F} {ε : ℝ} (ha : ‖a‖ < ε) (hb : ‖b‖ < ε) : ‖a + b‖ < ε :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)

/-- open ball subgroup of `Multiplicative K` -/
def ballSub (ε : ℝ) (hε : 0 < ε) : Subgroup (Multiplicative (v.adicCompletion F)) where
  carrier := {x | ‖Multiplicative.toAdd x‖ < ε}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, toAdd_mul] at *
    exact ultra_lt v hx hy
  one_mem' := by simp [hε]
  inv_mem' := by
    intro x hx
    simpa using hx

lemma ballSub_open (ε : ℝ) (hε : 0 < ε) :
    IsOpen ((ballSub v ε hε : Subgroup _) : Set (Multiplicative (v.adicCompletion F))) :=
  isOpen_lt (continuous_norm.comp continuous_toAdd) continuous_const

lemma gamma_compact {Γ : Subgroup (Multiplicative (v.adicCompletion F))}
    (hΓo : IsOpen (Γ : Set (Multiplicative (v.adicCompletion F))))
    (hΓ : IsCompactlyGeneratedSubgroup Γ) :
    IsCompact (Γ : Set (Multiplicative (v.adicCompletion F))) := by
  obtain ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hcl⟩ := hΓ
  have hUn : U ∈ 𝓝 (1 : Multiplicative (v.adicCompletion F)) :=
    mem_of_superset (inter_mem hV (hΓo.mem_nhds Γ.one_mem)) hVU
  have hlc : LocallyCompactSpace (Multiplicative (v.adicCompletion F)) :=
    hUc.locallyCompactSpace_of_mem_nhds_of_group hUn
  have hlcK : LocallyCompactSpace (v.adicCompletion F) := hlc
  have hP : ProperSpace (v.adicCompletion F) :=
    @ProperSpace.of_locallyCompactSpace (v.adicCompletion F)
      (Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
      _ _ _ hlcK
  obtain ⟨R, hR⟩ := (hUc.image continuous_toAdd).isBounded.exists_norm_le
  let R' := max R 0
  let B : Subgroup (Multiplicative (v.adicCompletion F)) :=
    { carrier := {x | ‖Multiplicative.toAdd x‖ ≤ R'}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, toAdd_mul] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      one_mem' := by simp [R']
      inv_mem' := fun {x} hx => by simpa using hx }
  have hΓB : Γ ≤ B := by
    rw [← hcl]
    exact (Subgroup.closure_le B).2 fun x hx => (hR _ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  have hBc : IsCompact (B : Set (Multiplicative (v.adicCompletion F))) := by
    have : (B : Set (Multiplicative (v.adicCompletion F))) =
        Multiplicative.ofAdd '' Metric.closedBall 0 R' := by
      ext x
      constructor
      · intro hx
        have hx' : ‖Multiplicative.toAdd x‖ ≤ R' := hx
        exact ⟨Multiplicative.toAdd x, by simpa [mem_closedBall_zero_iff] using hx', rfl⟩
      · rintro ⟨y, hy, rfl⟩
        show ‖Multiplicative.toAdd (Multiplicative.ofAdd y)‖ ≤ R'
        simpa [mem_closedBall_zero_iff] using hy
    rw [this]
    exact (isCompact_closedBall _ _).image continuous_ofAdd
  exact hBc.of_isClosed_subset (Subgroup.isClosed_of_isOpen Γ hΓo) hΓB

lemma small_ball {Γ : Subgroup (Multiplicative (v.adicCompletion F))} {Y : Type*}
    [TopologicalSpace Y] (f : Γ → Y) (hf : Continuous f) (W : Set Y) (hW : W ∈ 𝓝 (f 1))
    (hΓo : IsOpen (Γ : Set (Multiplicative (v.adicCompletion F)))) :
    ∃ ε > 0, ∀ x : Multiplicative (v.adicCompletion F), ‖Multiplicative.toAdd x‖ < ε →
      ∃ hx : x ∈ Γ, f ⟨x, hx⟩ ∈ W := by
  have h1 : f ⁻¹' W ∈ 𝓝 (1 : Γ) := hf.continuousAt.preimage_mem_nhds hW
  rw [nhds_subtype, Filter.mem_comap] at h1
  obtain ⟨U, hU, hUW⟩ := h1
  have h2 : U ∩ Γ ∈ 𝓝 (1 : Multiplicative (v.adicCompletion F)) :=
    inter_mem hU (hΓo.mem_nhds Γ.one_mem)
  have h3 : Multiplicative.ofAdd ⁻¹' (U ∩ Γ) ∈ 𝓝 (0 : v.adicCompletion F) :=
    continuous_ofAdd.continuousAt.preimage_mem_nhds (by simpa using h2)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h3
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hmem : Multiplicative.toAdd x ∈ Metric.ball (0 : v.adicCompletion F) ε := by
    simpa using hx
  have h4 := hball hmem
  simp only [Set.mem_preimage, ofAdd_toAdd] at h4
  exact ⟨h4.2, hUW (show ((⟨x, h4.2⟩ : Γ) : Multiplicative (v.adicCompletion F)) ∈ U from h4.1)⟩

lemma elem_dims {Γ k : Subgroup (Multiplicative (v.adicCompletion F))} {m n r s : ℕ}
    {d : Fin s → ℕ} {π : Γ →* Multiplicative (ElemGroup m n r s d)}
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) : m = 0 ∧ n = 0 ∧ r = 0 := by
  have hΓc := gamma_compact v hs.1 hs.2.1
  have : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓc
  obtain ⟨-, hcont, hopen, hsurj, -⟩ := hπ
  have himg : IsCompact (Set.univ : Set (Multiplicative (ElemGroup m n r s d))) := by
    rw [← hsurj.range_eq, ← Set.image_univ]
    exact isCompact_univ.image hcont
  refine ⟨?_, ?_, ?_⟩
  · by_contra hm
    let j : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    let pr : Multiplicative (ElemGroup m n r s d) → ℝ := fun e => (Multiplicative.toAdd e).1 j
    have hpr : Continuous pr := (continuous_apply j).comp (continuous_fst.comp continuous_toAdd)
    have hsur : Function.Surjective pr := fun t =>
      ⟨Multiplicative.ofAdd ((fun _ => t), 0, 0, 0), rfl⟩
    have := himg.image hpr
    rw [Set.image_univ, hsur.range_eq] at this
    exact noncompact_univ ℝ this
  · by_contra hn
    let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let ρ : Γ →* Multiplicative UnitAddCircle :=
      { toFun := fun x => Multiplicative.ofAdd ((Multiplicative.toAdd (π x)).2.1 j)
        map_one' := by simp
        map_mul' := by intro x y; simp }
    have hρc : Continuous ρ :=
      continuous_ofAdd.comp ((continuous_apply j).comp
        (continuous_fst.comp (continuous_snd.comp (continuous_toAdd.comp hcont))))
    have hρo : IsOpenMap ρ := by
      have h1 : IsOpenMap (Multiplicative.toAdd : Multiplicative (ElemGroup m n r s d) → _) :=
        fun U hU => by
          rw [Multiplicative.toAdd.image_eq_preimage_symm]
          exact hU.preimage continuous_ofAdd
      have h2 : IsOpenMap (Multiplicative.ofAdd : UnitAddCircle → Multiplicative UnitAddCircle) :=
        fun U hU => by
          rw [Multiplicative.ofAdd.image_eq_preimage_symm]
          exact hU.preimage continuous_toAdd
      exact h2.comp ((isOpenMap_eval j).comp (isOpenMap_fst.comp (isOpenMap_snd.comp
        (h1.comp hopen))))
    let W : Set (Multiplicative UnitAddCircle) := {t | ‖Multiplicative.toAdd t‖ < 1 / 4}
    have hW : W ∈ 𝓝 (ρ 1) := by
      rw [map_one]
      exact (isOpen_lt (continuous_norm.comp continuous_toAdd) continuous_const).mem_nhds
        (by simp [W])
    obtain ⟨ε, hε, hball⟩ := small_ball v ρ hρc W hW hs.1
    let H : Subgroup Γ := (ballSub v ε hε).subgroupOf Γ
    have hHo : IsOpen (H : Set Γ) := (ballSub_open v ε hε).preimage continuous_subtype_val
    let S := H.map ρ
    have hSo : IsOpen (S : Set (Multiplicative UnitAddCircle)) := by
      rw [Subgroup.coe_map]
      exact hρo _ hHo
    have hSc : IsClosed (S : Set (Multiplicative UnitAddCircle)) := Subgroup.isClosed_of_isOpen S hSo
    have : PreconnectedSpace (Multiplicative UnitAddCircle) :=
      inferInstanceAs (PreconnectedSpace UnitAddCircle)
    have hSu : (S : Set (Multiplicative UnitAddCircle)) = Set.univ :=
      IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨1, S.one_mem⟩
    have ht0 : Multiplicative.ofAdd (((1 / 2 : ℝ)) : UnitAddCircle) ∈ (S : Set _) := by
      rw [hSu]; trivial
    obtain ⟨h, hH, hh⟩ := ht0
    have hx : ‖Multiplicative.toAdd (h : Multiplicative (v.adicCompletion F))‖ < ε := hH
    obtain ⟨hxΓ, hxW⟩ := hball _ hx
    have : ρ h ∈ W := hxW
    rw [hh] at this
    simp only [W, Set.mem_ofPred_eq, toAdd_ofAdd] at this
    have h2 := AddCircle.norm_half_period_eq (1 : ℝ)
    norm_num at h2 this <;> linarith
  · by_contra hr
    let j : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    let pr : Multiplicative (ElemGroup m n r s d) → ℤ := fun e => (Multiplicative.toAdd e).2.2.1 j
    have hpr : Continuous pr := (continuous_apply j).comp
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd)))
    have hsur : Function.Surjective pr := fun t =>
      ⟨Multiplicative.ofAdd (0, 0, (fun _ => t), 0), rfl⟩
    have := himg.image hpr
    rw [Set.image_univ, hsur.range_eq] at this
    exact Set.infinite_univ (isCompact_iff_finite.1 this)

end padic

section elem

def allFam (S : Type*) [AddCommGroup S] [Module ℂ S] : SeminormFamily ℂ S (Seminorm ℂ S) :=
  fun p => p

/-- the topology of all seminorms (not an instance) -/
noncomputable def tAllOf (S : Type*) [AddCommGroup S] [Module ℂ S] : TopologicalSpace S :=
  (allFam S).moduleFilterBasis.topology

lemma tAll_ws (S : Type*) [AddCommGroup S] [Module ℂ S] :
    @WithSeminorms ℂ S (Seminorm ℂ S) _ _ _ (allFam S) (tAllOf S) := by
  letI := tAllOf S
  exact ⟨rfl⟩

lemma tAll_tag (S : Type*) [AddCommGroup S] [Module ℂ S] :
    @IsTopologicalAddGroup S (tAllOf S) _ := by
  letI := tAllOf S
  exact (tAll_ws S).topologicalAddGroup

lemma tAll_csmul (S : Type*) [AddCommGroup S] [Module ℂ S] :
    @ContinuousSMul ℂ S _ _ (tAllOf S) := by
  letI := tAllOf S
  exact (tAll_ws S).continuousSMul

variable {s : ℕ} {d : Fin s → ℕ}

lemma elemLift_const (g : ElemGroup 0 0 0 s d → ℂ) (a : Fin 0 → ℤ) (b : (i : Fin s) → ZMod (d i)) :
    elemLift g a b = fun _ => g (0, 0, 0, b) := by
  funext xt
  simp only [elemLift]
  congr 1
  exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _)
    (Prod.ext (Subsingleton.elim _ _) rfl))

lemma all_rapid [Fintype (ElemGroup 0 0 0 s d)] (g : ElemGroup 0 0 0 s d → ℂ) :
    IsRapidDecay g := by
  refine ⟨fun a b => by rw [elemLift_const]; exact contDiff_const,
    fun i j k => ⟨∑ e, ‖g e‖, fun a b xt => ?_⟩⟩
  rw [elemLift_const]
  have ha : ‖a‖ = 0 := by rw [Subsingleton.elim a 0, norm_zero]
  have hx : ‖xt.1‖ = 0 := by rw [Subsingleton.elim xt.1 0, norm_zero]
  rw [ha, hx]
  have h1 : (0 : ℝ) ^ j * 0 ^ i ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ le_rfl zero_le_one) (pow_nonneg le_rfl _)
      (pow_le_one₀ le_rfl zero_le_one)
  have h0 : (0 : ℝ) ≤ 0 ^ j * 0 ^ i := by positivity
  have hS : ‖g (0, 0, 0, b)‖ ≤ ∑ e, ‖g e‖ :=
    Finset.single_le_sum (f := fun e => ‖g e‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  rcases k with _ | k
  · rw [norm_iteratedFDeriv_zero]
    calc (0 : ℝ) ^ j * 0 ^ i * ‖g (0, 0, 0, b)‖ ≤ 1 * ‖g (0, 0, 0, b)‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ ∑ e, ‖g e‖ := by rw [one_mul]; exact hS
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp only [Pi.zero_apply, norm_zero, mul_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

open Classical in
noncomputable def δe [Fintype (ElemGroup 0 0 0 s d)] (e : ElemGroup 0 0 0 s d) :
    ElemSchwartz 0 0 0 s d :=
  ⟨fun x => if x = e then 1 else 0, Submodule.subset_span (all_rapid _)⟩

lemma eval_cont (e : ElemGroup 0 0 0 s d) :
    Continuous fun g : ElemSchwartz 0 0 0 s d => g.toFun e := by
  let q : (Fin 0 → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin 0 → ℝ) × (Fin 0 → ℝ)) :=
    (0, e.2.2.2, 0)
  have h1 : Continuous (fun (g : ElemSchwartz 0 0 0 s d) (p : ℕ × ℕ × ℕ) =>
      UniformFun.ofFun
        (fun q : (Fin 0 → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin 0 → ℝ) × (Fin 0 → ℝ)) =>
          (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)) :=
    continuous_induced_dom
  have h2 := (continuous_apply ((0, 0, 0) : ℕ × ℕ × ℕ)).comp h1
  have h3 := ((UniformFun.uniformContinuous_eval _ q).continuous).comp h2
  have h4 := (continuous_eval_const (fun _ : Fin 0 => (0 : (Fin 0 → ℝ) × (Fin 0 → ℝ)))).comp h3
  convert h4 using 1
  funext g
  simp only [Function.comp_apply, Function.eval, UniformFun.toFun_ofFun, pow_zero, mul_one,
    one_smul, iteratedFDeriv_zero_apply, q, elemLift]
  congr 1
  exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _)
    (Prod.ext (Subsingleton.elim _ _) rfl))

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma ofElem_eq [Fintype (ElemGroup 0 0 0 s d)] {Γ k : Subgroup G}
    {π : Γ →* Multiplicative (ElemGroup 0 0 0 s d)} (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemSchwartz 0 0 0 s d) :
    SchwartzBruhat.ofElem Γ k π hs hπ g =
      ∑ e, g.toFun e • SchwartzBruhat.ofElem Γ k π hs hπ (δe e) := by
  classical
  let valL : SchwartzBruhat G →ₗ[ℂ] (G → ℂ) := (schwartzBruhatSubmodule G).subtype
  apply Subtype.val_injective
  show valL (SchwartzBruhat.ofElem Γ k π hs hπ g) =
    valL (∑ e, g.toFun e • SchwartzBruhat.ofElem Γ k π hs hπ (δe e))
  rw [map_sum]
  funext x
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show extendPullback Γ π g.toFun x = ∑ e, g.toFun e * extendPullback Γ π (δe e).toFun x
  unfold extendPullback
  by_cases hx : x ∈ Γ
  · simp only [dif_pos hx]
    simp only [δe, ElemSchwartz.toFun, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  · simp [dif_neg hx]

lemma cont_sum_smul {X Y : Type*} [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y] {ι : Type*}
    (S : Finset ι) (c : ι → X → ℂ) (hc : ∀ i, Continuous (c i)) (y : ι → Y) :
    Continuous fun x => ∑ i ∈ S, c i x • y i :=
  continuous_finsetSum _ fun i _ => (hc i).smul continuous_const

lemma ofElem_cont_all [Fintype (ElemGroup 0 0 0 s d)] {Γ k : Subgroup G}
    {π : Γ →* Multiplicative (ElemGroup 0 0 0 s d)} (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) :
    @Continuous (ElemSchwartz 0 0 0 s d) (SchwartzBruhat G) _ (tAllOf (SchwartzBruhat G))
      (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  have hfun : (SchwartzBruhat.ofElem Γ k π hs hπ) =
      fun g => ∑ e, g.toFun e • SchwartzBruhat.ofElem Γ k π hs hπ (δe e) :=
    funext fun g => ofElem_eq hs hπ g
  rw [hfun]
  exact @cont_sum_smul _ _ _ _ _ (tAllOf (SchwartzBruhat G))
    (tAll_tag _) (tAll_csmul _) _ Finset.univ
    (fun e (g : ElemSchwartz 0 0 0 s d) => g.toFun e) (fun e => eval_cont e) _

end elem

section final

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

lemma sb_isFin : IsFin (SchwartzBruhat (Multiplicative (v.adicCompletion F))) := by
  have heq : instTopologicalSpaceSchwartzBruhat (Multiplicative (v.adicCompletion F)) =
      tAllOf (SchwartzBruhat (Multiplicative (v.adicCompletion F))) := by
    apply le_antisymm
    · show sInf _ ≤ _
      apply sInf_le
      refine ⟨⟨Seminorm ℂ _, ⟨0⟩, allFam _, tAll_ws _⟩, ?_⟩
      intro Γ k m n r s d π hs hπ
      obtain ⟨rfl, rfl, rfl⟩ := elem_dims v hs hπ
      have : ∀ i, NeZero (d i) := fun i => ⟨hπ.1 i⟩
      have : Fintype (ElemGroup 0 0 0 s d) := Fintype.ofFinite _
      exact ofElem_cont_all hs hπ
    · show _ ≤ sInf _
      apply le_sInf
      intro t ht
      obtain ⟨⟨ι, _, p, hp⟩, -⟩ := ht
      exact (@continuous_id_iff_le _ (tAllOf _) t).1
        (WithSeminorms.continuous_of_isBounded (tAll_ws _) hp
        LinearMap.id (fun i => ⟨{p i}, 1, by simp [allFam]⟩))
  exact ⟨heq⟩

end final

section rank

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

open Classical in
noncomputable def indf (a : v.adicCompletion F) (ε : ℝ) :
    Multiplicative (v.adicCompletion F) → ℂ :=
  fun x => if ‖Multiplicative.toAdd x - a‖ < ε then 1 else 0

lemma indf_inv (a : v.adicCompletion F) {ε : ℝ} (x y : Multiplicative (v.adicCompletion F))
    (hy : ‖Multiplicative.toAdd y‖ < ε) : indf v a ε (x * y) = indf v a ε x := by
  have key : ‖Multiplicative.toAdd (x * y) - a‖ < ε ↔ ‖Multiplicative.toAdd x - a‖ < ε := by
    rw [toAdd_mul]
    constructor
    · intro h
      have := ultra_lt v h (show ‖-Multiplicative.toAdd y‖ < ε by rwa [norm_neg])
      convert this using 2
      abel
    · intro h
      have := ultra_lt v h hy
      convert this using 2
      abel
  unfold indf
  by_cases h : ‖Multiplicative.toAdd x - a‖ < ε
  · rw [if_pos (key.2 h), if_pos h]
  · rw [if_neg (fun h' => h (key.1 h')), if_neg h]

lemma span_ind {ε : ℝ} (L : List (v.adicCompletion F)) :
    ∀ f : Multiplicative (v.adicCompletion F) → ℂ,
      (∀ x y, ‖Multiplicative.toAdd y‖ < ε → f (x * y) = f x) →
      (∀ x, f x ≠ 0 → ∃ a ∈ L, ‖Multiplicative.toAdd x - a‖ < ε) →
      (∀ a ∈ L, a ∈ Set.range (algebraMap F (v.adicCompletion F))) →
      f ∈ Submodule.span ℂ (Set.range fun a : F => indf v (algebraMap F _ a) ε) := by
  induction L with
  | nil =>
    intro f _ hsupp _
    have : f = 0 := funext fun x => by
      by_contra h
      obtain ⟨a, ha, -⟩ := hsupp x h
      simp at ha
    rw [this]
    exact Submodule.zero_mem _
  | cons a L ih =>
    intro f hinv hsupp hL
    obtain ⟨a0, ha0⟩ := hL a List.mem_cons_self
    let A := algebraMap F (v.adicCompletion F) a0
    let c := f (Multiplicative.ofAdd A)
    let g := f - c • indf v A ε
    have hg1 : ∀ x y, ‖Multiplicative.toAdd y‖ < ε → g (x * y) = g x := by
      intro x y hy
      simp only [g, Pi.sub_apply, Pi.smul_apply, hinv x y hy, indf_inv v A x y hy]
    have hg2 : ∀ x, g x ≠ 0 → ∃ a' ∈ L, ‖Multiplicative.toAdd x - a'‖ < ε := by
      intro x hx
      by_cases hxa : ‖Multiplicative.toAdd x - A‖ < ε
      · exfalso
        apply hx
        have hfx : f x = c := by
          have h1 := hinv (Multiplicative.ofAdd A) (Multiplicative.ofAdd (Multiplicative.toAdd x - A))
            (by simpa using hxa)
          have e : Multiplicative.ofAdd A * Multiplicative.ofAdd (Multiplicative.toAdd x - A) = x := by
            rw [← ofAdd_add, add_sub_cancel, ofAdd_toAdd]
          rw [e] at h1
          exact h1
        simp only [g, Pi.sub_apply, Pi.smul_apply, indf, if_pos hxa, smul_eq_mul, mul_one, hfx,
          sub_self]
      · have hfx : f x ≠ 0 := by
          intro h0
          apply hx
          simp only [g, Pi.sub_apply, Pi.smul_apply, indf, if_neg hxa, smul_eq_mul, mul_zero, h0,
            sub_zero]
        obtain ⟨a', ha', hlt⟩ := hsupp x hfx
        rcases List.mem_cons.1 ha' with rfl | h
        · rw [← ha0] at hlt
          exact absurd hlt hxa
        · exact ⟨a', h, hlt⟩
    have hg := ih g hg1 hg2 (fun a' h => hL a' (List.mem_cons_of_mem a h))
    have hf : f = g + c • indf v A ε := by simp [g]
    rw [hf]
    exact Submodule.add_mem _ hg (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a0, rfl⟩))

lemma gen_mem {Γ k : Subgroup (Multiplicative (v.adicCompletion F))} {s : ℕ} {d : Fin s → ℕ}
    {π : Γ →* Multiplicative (ElemGroup 0 0 0 s d)} (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemGroup 0 0 0 s d → ℂ) :
    extendPullback Γ π g ∈ Submodule.span ℂ
      (Set.range (fun p : F × ℕ => indf v (algebraMap F _ p.1) (1 / ((p.2 : ℝ) + 1)))) := by
  classical
  have hΓc := gamma_compact v hs.1 hs.2.1
  have hdisc : DiscreteTopology (Multiplicative (ElemGroup 0 0 0 s d)) :=
    inferInstanceAs (DiscreteTopology (ElemGroup 0 0 0 s d))
  obtain ⟨ε, hε, hball⟩ := small_ball v π hπ.2.1 {1}
    (by rw [map_one]; exact (isOpen_discrete _).mem_nhds rfl) hs.1
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  have hε' : (0 : ℝ) < 1 / ((N : ℝ) + 1) := Nat.one_div_pos_of_nat
  have hinv : ∀ x y, ‖Multiplicative.toAdd y‖ < 1 / ((N : ℝ) + 1) →
      extendPullback Γ π g (x * y) = extendPullback Γ π g x := by
    intro x y hy
    obtain ⟨hyΓ, hy1⟩ := hball y (hy.trans hN)
    unfold extendPullback
    by_cases hx : x ∈ Γ
    · have hxy : x * y ∈ Γ := Γ.mul_mem hx hyΓ
      rw [dif_pos hxy, dif_pos hx]
      have : π ⟨x * y, hxy⟩ = π ⟨x, hx⟩ := by
        have e : (⟨x * y, hxy⟩ : Γ) = ⟨x, hx⟩ * ⟨y, hyΓ⟩ := rfl
        rw [e, map_mul, Set.mem_singleton_iff.1 hy1, mul_one]
      rw [this]
    · have hxy : x * y ∉ Γ := fun h => hx (by simpa using Γ.mul_mem h (Γ.inv_mem hyΓ))
      rw [dif_neg hxy, dif_neg hx]
  have hKc : IsCompact (Multiplicative.toAdd '' (Γ : Set (Multiplicative (v.adicCompletion F)))) :=
    hΓc.image continuous_toAdd
  obtain ⟨t, -, htfin, hcover⟩ := hKc.finite_cover_balls hε'
  have hdense := HeightOneSpectrum.denseRange_algebraMap F v
  choose a ha using fun c : v.adicCompletion F => hdense.exists_dist_lt c hε'
  let L : List (v.adicCompletion F) := (htfin.toFinset.toList).map (fun c => algebraMap F _ (a c))
  have hsub := span_ind v (ε := 1 / ((N : ℝ) + 1)) L (extendPullback Γ π g) hinv (fun x hx => by
      have hxΓ : x ∈ Γ := by
        by_contra h
        apply hx
        unfold extendPullback
        rw [dif_neg h]
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (hcover ⟨x, hxΓ, rfl⟩)
      refine ⟨algebraMap F _ (a c), List.mem_map.2 ⟨c, Finset.mem_toList.2
        (htfin.mem_toFinset.2 hc), rfl⟩, ?_⟩
      have h1 : ‖Multiplicative.toAdd x - c‖ < 1 / ((N : ℝ) + 1) := by
        rw [Metric.mem_ball, dist_eq_norm] at hxc
        exact hxc
      have h2 : ‖c - algebraMap F _ (a c)‖ < 1 / ((N : ℝ) + 1) := by
        have := ha c
        rwa [dist_eq_norm] at this
      have := ultra_lt v h1 h2
      rwa [sub_add_sub_cancel] at this)
    (fun a' ha' => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha'
      exact ⟨a c, rfl⟩)
  refine Submodule.span_mono ?_ hsub
  rintro _ ⟨a0, rfl⟩
  exact ⟨(a0, N), rfl⟩

lemma sb_rank :
    Module.rank ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ≤ Cardinal.aleph0 := by
  have : Countable F := countable_nf
  let T := Set.range (fun p : F × ℕ => indf v (algebraMap F _ p.1) (1 / ((p.2 : ℝ) + 1)))
  have hle : schwartzBruhatSubmodule (Multiplicative (v.adicCompletion F)) ≤
      Submodule.span ℂ T := by
    rw [schwartzBruhatSubmodule, Submodule.span_le]
    rintro f ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := elem_dims v hs hπ
    exact gen_mem v hs hπ g.toFun
  calc Module.rank ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F)))
      = Module.rank ℂ (schwartzBruhatSubmodule (Multiplicative (v.adicCompletion F))) := rfl
    _ ≤ Module.rank ℂ (Submodule.span ℂ T) := Submodule.rank_mono hle
    _ ≤ Cardinal.mk T := rank_span_le T
    _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.2 (Set.countable_range _).to_subtype

end rank


end Aux_SLN

open MasulloGRH NumberField IsDedekindDomain in
theorem solution (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Module.rank ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ≤ Cardinal.aleph0 ∧
      HasFinestLocallyConvexTopology (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsStrictLF (SchwartzBruhat (Multiplicative (v.adicCompletion F)))) ∧
    (IsHLCS (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsCompleteTVS (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsNuclear (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsMontel (SchwartzBruhat (Multiplicative (v.adicCompletion F))) ∧
      IsFrechet (StrongDual ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F)))) ∧
      IsNuclear (StrongDual ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))))) ∧
    (∀ V : Submodule ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))),
      ∃ W : Submodule ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))), IsCompl V W ∧
        Continuous (fun p : V × W =>
          ((p.1 : SchwartzBruhat (Multiplicative (v.adicCompletion F))) + p.2)) ∧
        IsOpenMap (fun p : V × W =>
          ((p.1 : SchwartzBruhat (Multiplicative (v.adicCompletion F))) + p.2))) :=
  Aux_SLN.abstract_all (Aux_SLN.sb_isFin v) (Aux_SLN.sb_rank v)

-- Prove2me | solution 2 for MasulloGRH.strictLF_quotient_weakQ_of_alpha_regular
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:09:53.287259+00:00
-- url     : https://prove2.me/submissions/d5f91ac1-de44-4259-bd91-986ace858ac3

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_frechet_countable_pullback_open_quotient

set_option autoImplicit false

open MasulloGRH Set Filter Topology Bornology

universe u

private theorem complete_of_filters {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] (hC : IsCompleteTVS E) : CompleteSpace E := by
  constructor
  intro f hf
  obtain ⟨hbot, hdiff⟩ := (IsUniformAddGroup.cauchy_iff_tendsto f).1 hf
  refine hC.2 f ⟨hbot, fun U hU => ?_⟩
  obtain ⟨A, hA, B, hB, hsub⟩ := mem_prod_iff.1 (hdiff hU)
  exact ⟨A ∩ B, inter_mem hA hB, fun x hx y hy => hsub (show (x, y) ∈ A ×ˢ B from ⟨hx.1, hy.2⟩)⟩

open scoped Pointwise

private theorem scalar_l1_norm (z : lp (fun _ : ℕ => ℂ) 1) :
    ‖z‖ = ∑' i, ‖z i‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by simp) z

private theorem scalar_l1_summable (z : lp (fun _ : ℕ => ℂ) 1) :
    Summable (fun i => ‖z i‖) := by
  simpa using (memℓp_gen_iff (p := 1) (by simp)).1 z.property

private theorem bounded_sequence_extension {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (y : ℕ → E)
    (hy : IsVonNBounded ℂ (range y)) :
    ∃ L : lp (fun _ : ℕ => ℂ) 1 →L[ℂ] E,
      ∀ z : lp (fun _ : ℕ => ℂ) 1, HasSum (fun i => z i • y i) (L z) := by
  obtain ⟨_, _, P, hP⟩ := hE.1
  let : IsTopologicalAddGroup E := hP.topologicalAddGroup
  let : ContinuousSMul ℂ E := hP.continuousSMul
  let : T2Space E := hE.2.1.1
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := complete_of_filters hE.2.1
  choose M hM hyM using hP.isVonNBounded_iff_seminorm_bounded.1 hy
  have hbound (z : lp (fun _ : ℕ => ℂ) 1) (k : _) (s : Finset ℕ) :
      P k (∑ i ∈ s, z i • y i) ≤ M k * ∑ i ∈ s, ‖z i‖ := by
    rw [Finset.mul_sum]
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine (map_add_le_add (P k) _ _).trans (add_le_add ?_ ih)
      rw [map_smul_eq_mul, mul_comm (M k)]
      exact mul_le_mul_of_nonneg_left (hyM k _ (mem_range_self _)).le (norm_nonneg _)
  have hs (z : lp (fun _ : ℕ => ℂ) 1) : Summable (fun i => z i • y i) := by
    apply summable_iff_cauchySeq_finset.2
    apply cauchySeq_finset_iff_sum_vanishing.2
    intro W hW
    obtain ⟨⟨J, ε⟩, hε, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.1 hW
    let C : ℝ := 1 + ∑ k ∈ J, M k
    have hC : 0 < C := by
      dsimp [C]
      exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun k _ => (hM k).le)
    have hMC (k : _) (hk : k ∈ J) : M k ≤ C :=
      (Finset.single_le_sum (fun j _ => (hM j).le) hk).trans (le_add_of_nonneg_left zero_le_one)
    obtain ⟨t, ht⟩ := summable_iff_vanishing_norm.1 (scalar_l1_summable z) (ε / C) (div_pos hε hC)
    refine ⟨t, fun s hs => hsub ?_⟩
    rw [Seminorm.mem_ball_zero]
    apply Seminorm.finset_sup_apply_lt hε
    intro k hk
    have hsmall : (∑ i ∈ s, ‖z i‖) < ε / C := by
      simpa only [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg (z i))]
        using ht s hs
    refine (hbound z k s).trans_lt ?_
    calc
      M k * ∑ i ∈ s, ‖z i‖ ≤ C * ∑ i ∈ s, ‖z i‖ :=
        mul_le_mul_of_nonneg_right (hMC k hk) (Finset.sum_nonneg fun i _ => norm_nonneg _)
      _ < ε := by
        have heq : C * (ε / C) = ε := by field_simp
        exact (mul_lt_mul_of_pos_left hsmall hC).trans_eq heq
  let L : lp (fun _ : ℕ => ℂ) 1 →ₗ[ℂ] E :=
    { toFun := fun z => ∑' i, z i • y i
      map_add' := fun a b => by
        change (∑' i, (a i + b i) • y i) = _
        simp_rw [add_smul]
        exact (hs a).tsum_add (hs b)
      map_smul' := fun a z => by
        change (∑' i, (a * z i) • y i) = a • (∑' i, z i • y i)
        simp_rw [mul_smul]
        exact ((hs z).hasSum.const_smul a).tsum_eq }
  have hLp (k : _) (z : lp (fun _ : ℕ => ℂ) 1) : P k (L z) ≤ M k * ‖z‖ := by
    apply le_of_tendsto ((hP.continuous_seminorm k).continuousAt.tendsto.comp ((hs z).hasSum))
    refine Eventually.of_forall fun s => (hbound z k s).trans ?_
    rw [scalar_l1_norm]
    exact mul_le_mul_of_nonneg_left
      ((scalar_l1_summable z).sum_le_tsum s (fun i _ => norm_nonneg _)) (hM k).le
  have hLc : Continuous L := by
    apply hP.continuous_of_continuous_comp L
    intro k
    apply Seminorm.continuous' (r := 1)
    rw [Seminorm.closedBall_zero_eq]
    refine mem_of_superset (Metric.ball_mem_nhds (0 : lp (fun _ : ℕ => ℂ) 1)
      (show 0 < 1 / M k from one_div_pos.mpr (hM k))) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact (hLp k z).trans (by
      have h := (lt_div_iff₀ (hM k)).1 hz
      simpa only [mul_comm] using h.le)
  exact ⟨⟨L, hLc⟩, fun z => (hs z).hasSum⟩

private theorem sum_mem_of_sum_norm_le {E : Type*} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E]
    {D : Set E} (h0 : (0 : E) ∈ D) (hbal : Balanced ℂ D) (hconv : Convex ℝ D)
    {I : Type*} (s : Finset I) (a : I → ℂ) (x : I → E)
    (hx : ∀ i ∈ s, x i ∈ D) (h : ∑ i ∈ s, ‖a i‖ ≤ 1) :
    (∑ i ∈ s, a i • x i) ∈ D := by
  let r : ℝ := ∑ i ∈ s, ‖a i‖
  have hr : 0 ≤ r := Finset.sum_nonneg fun _ _ => norm_nonneg _
  by_cases hr0 : r = 0
  · have ha (i : I) (hi : i ∈ s) : a i = 0 := by
      have hri : ‖a i‖ ≤ r := Finset.single_le_sum (fun j _ => norm_nonneg _) hi
      exact norm_eq_zero.1 ((norm_nonneg _).antisymm' (hr0 ▸ hri))
    have he : (∑ i ∈ s, a i • x i) = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [ha i hi]
    exact he ▸ h0
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  let phase (i : I) : ℂ := (‖a i‖ : ℂ)⁻¹ * a i
  have hphase (i : I) : ‖phase i‖ ≤ 1 := by
    by_cases hi : a i = 0
    · simp [phase, hi]
    · change ‖(‖a i‖ : ℂ)⁻¹ * a i‖ ≤ 1
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hi)]
  have hrotation (i : I) : ‖a i‖ • (phase i • x i) = a i • x i := by
    rw [← algebraMap_smul ℂ (‖a i‖), smul_smul]
    change (((‖a i‖ : ℂ) * phase i) • x i) = _
    congr 1
    by_cases hi : a i = 0
    · simp [phase, hi]
    have hc : (‖a i‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hi)
    simp only [phase, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hin : (∑ i ∈ s, (‖a i‖ / r) • (phase i • x i)) ∈ D := by
    apply hconv.sum_mem
    · exact fun i _ => div_nonneg (norm_nonneg _) hr
    · rw [← Finset.sum_div, div_self hr0]
    · exact fun i hi => hbal.smul_mem (hphase i) (hx i hi)
  have hscaled := hbal.smul_mem (a := (r : ℂ))
    (by rwa [Complex.norm_real, Real.norm_of_nonneg hr]) hin
  convert hscaled using 1
  rw [show ((r : ℂ) • ∑ i ∈ s, (‖a i‖ / r) • phase i • x i) =
      r • ∑ i ∈ s, (‖a i‖ / r) • phase i • x i from algebraMap_smul ℂ r _,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have heq : r * (‖a i‖ / r) = ‖a i‖ := by field_simp
  rw [smul_smul, heq, hrotation]

private theorem banach_frechet (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] : IsFrechet F := by
  let : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  refine ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, PolynormableSpace.withSeminorms ℂ F⟩,
    ⟨inferInstance, ?_⟩, inferInstance⟩
  intro f hf
  have hC : Cauchy f := (IsUniformAddGroup.cauchy_iff_tendsto f).2 ⟨hf.1, ?_⟩
  · exact CompleteSpace.complete hC
  · intro U hU
    obtain ⟨A, hA, hclose⟩ := hf.2 U hU
    apply mem_prod_iff.2
    exact ⟨A, hA, A, hA, fun p hp => hclose p.1 hp.1 p.2 hp.2⟩

private theorem single_stage_factor {A E : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    (hA : IsFrechet A) (X : Type*) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hX : IsFrechet X) (p : A →L[ℂ] E) (K : Submodule ℂ X)
    (j : (X ⧸ K) →L[ℂ] E) (hj : Function.Injective j)
    (hcover : ∀ z, p z ∈ range j) :
    ∃ L : A →L[ℂ] X ⧸ K, ∀ z, j (L z) = p z := by
  classical
  let b : X →ₗ[ℂ] E := j.toLinearMap.comp K.mkQ
  have hb : Continuous b := j.continuous.comp K.continuous_mkQ
  -- Use the existing factorization theorem with the target subspace as the codomain.
  let Z := LinearMap.range b
  let π : A →ₗ[ℂ] Z := p.toLinearMap.codRestrict Z (fun a => by
    obtain ⟨z, hz⟩ := hcover a
    obtain ⟨x, rfl⟩ := K.mkQ_surjective z
    exact ⟨x, hz⟩)
  have hπ : Continuous π := p.continuous.subtype_mk _
  let q : X →ₗ[ℂ] Z := b.codRestrict Z (fun x => ⟨x, rfl⟩)
  have hq : Continuous q := hb.subtype_mk _
  have hcover' (z : Z) : ∃ n : ℕ, z ∈ range (fun x : X => q x) := by
    obtain ⟨x, hx⟩ := z.property
    exact ⟨0, x, Subtype.ext hx⟩
  obtain ⟨_, hop⟩ := frechet_countable_pullback_open_quotient A hA
    (fun _ => X) (fun _ => hX) Z π hπ (fun _ => q) (fun _ => hq) hcover'
  let f (z : A) : X ⧸ K := Classical.choose (hcover z)
  have hf (z : A) : j (f z) = p z := Classical.choose_spec (hcover z)
  let L : A →ₗ[ℂ] X ⧸ K :=
    { toFun := f
      map_add' := fun x y => hj (by rw [hf, map_add, ← hf x, ← hf y, map_add])
      map_smul' := fun c x => hj (by simp only [hf, map_smul, RingHom.id_apply]) }
  have hL : Continuous L := by
    apply hop.isQuotientMap.continuous_iff.2
    convert K.continuous_mkQ.comp (continuous_snd.comp continuous_subtype_val) using 1
    funext z
    apply hj
    exact (hf z.1.1).trans (congrArg Subtype.val z.property)
  exact ⟨⟨L, hL⟩, hf⟩

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hα : ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ n : ℕ, B ⊆ Set.range (Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl)) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V := by
  classical
  have hpoly : PolynormableSpace ℂ E := by
    rw [htop]
    apply PolynormableSpace.sInf
    intro t ht
    obtain ⟨_, _, _, h⟩ := ht.1
    exact h.toPolynormableSpace
  let : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  let : IsClosed (V.toAddSubgroup : Set E) := hV
  let : T2Space (E ⧸ V) := QuotientAddGroup.instT2Space
  let b (m : ℕ) : X m →L[ℂ] E ⧸ V :=
    ⟨V.mkQ.comp (X m).subtype, V.continuous_mkQ.comp continuous_subtype_val⟩
  have hmonoRange {i j : ℕ} (hij : i ≤ j) : range (b i) ⊆ range (b j) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨Submodule.inclusion (hmono hij) x, rfl⟩
  have hα' (B : Set (E ⧸ V)) (hB : IsVonNBounded ℂ B) : ∃ m, B ⊆ range (b m) := by
    obtain ⟨m, hm⟩ := hα B hB
    refine ⟨m, fun z hz => ?_⟩
    obtain ⟨x, rfl⟩ := hm hz
    obtain ⟨y, rfl⟩ := (V.comap (X m).subtype).mkQ_surjective x
    exact ⟨y, rfl⟩
  intro n
  -- A diagonal null sequence forces one neighborhood image to close inside a single stage.
  have hloc : ∃ m, n ≤ m ∧ ∃ U ∈ 𝓝 (0 : X n), closure (b n '' U) ⊆ range (b m) := by
    let : TopologicalSpace.MetrizableSpace (X n) := (hX n).2.2
    obtain ⟨A, hA⟩ := (𝓝 (0 : X n)).exists_antitone_basis
    by_contra! hbad
    have hchoose (j : ℕ) := not_subset.1
      (hbad (max n j) (le_max_left n j) (A j) (hA.1.mem_of_mem trivial))
    choose z hz hzbad using hchoose
    have hlim : Tendsto z atTop (𝓝 (0 : E ⧸ V)) := by
      apply (closed_nhds_basis (0 : E ⧸ V)).tendsto_right_iff.2
      rintro W ⟨hW, hclosed⟩
      have hpre : b n ⁻¹' W ∈ 𝓝 (0 : X n) := by
        simpa only [map_zero] using (b n).continuous.continuousAt.preimage_mem_nhds
          (show W ∈ 𝓝 (b n 0) by simpa only [map_zero] using hW)
      obtain ⟨J, _, hJ⟩ := hA.1.mem_iff.1 hpre
      filter_upwards [eventually_ge_atTop J] with j hj
      refine closure_minimal ?_ hclosed (hz j)
      rintro _ ⟨x, hx, rfl⟩
      exact hJ (hA.antitone hj hx)
    obtain ⟨m, hm⟩ := hα' (range z) (hlim.isVonNBounded_range ℂ)
    exact hzbad m (hmonoRange (le_max_right n m) (hm (mem_range_self m)))
  obtain ⟨m, hnm, U₀, hU₀, hUclose⟩ := hloc
  obtain ⟨_, _, P, hP⟩ := (hX n).1
  obtain ⟨⟨s, r⟩, hr, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.1 hU₀
  let U := (s.sup P).ball 0 r
  have hU : U ∈ 𝓝 (0 : X n) := hP.hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr
  have hUbal : Balanced ℂ U := (s.sup P).balanced_ball_zero r
  have hUconv : Convex ℝ U := (s.sup P).convex_ball 0 r
  let D : Set (E ⧸ V) := closure (b n '' U)
  have hD : D ⊆ range (b m) := (closure_mono (image_mono hsub)).trans hUclose
  have hD0 : (0 : E ⧸ V) ∈ D := by
    apply subset_closure
    exact ⟨0, mem_of_mem_nhds hU, map_zero _⟩
  have hDB : Balanced ℂ D := by
    apply Balanced.closure
    rw [balanced_iff_smul_mem]
    rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨a • x, hUbal.smul_mem ha hx, map_smul _ _ _⟩
  let : ContinuousConstSMul ℝ (E ⧸ V) := ⟨fun r => by
    simp_rw [← algebraMap_smul ℂ r]
    exact continuous_const_smul (algebraMap ℝ ℂ r)⟩
  have hDC : Convex ℝ D :=
    (hUconv.linear_image ((b n).toLinearMap.restrictScalars ℝ)).closure
  refine ⟨m, hnm, U, hU, fun k hmk W hW => ?_⟩
  let K := V.comap (X m).subtype
  let j : (X m ⧸ K) →L[ℂ] E ⧸ V :=
    ⟨K.mapQ V (X m).subtype le_rfl, K.isQuotientMap_mkQ.continuous_iff.2 (b m).continuous⟩
  have hj : Function.Injective j := by
    change Function.Injective (K.mapQ V (X m).subtype le_rfl)
    apply LinearMap.ker_eq_bot.1
    rw [Submodule.ker_mapQ]
    exact K.mkQ_map_self
  have hDj : D ⊆ range j := by
    intro z hz
    obtain ⟨x, rfl⟩ := hD hz
    exact ⟨K.mkQ x, rfl⟩
  have hb_eq {i l : ℕ} {x : X i} {y : X l} :
      b i x = b l y ↔ ((x : E) - (y : E)) ∈ V := by
    change V.mkQ (x : E) = V.mkQ (y : E) ↔ _
    rw [← sub_eq_zero, ← map_sub]
    exact Submodule.Quotient.mk_eq_zero V
  by_contra! hbad
  let : TopologicalSpace.MetrizableSpace (X k) := (hX k).2.2
  obtain ⟨A, hA⟩ := (𝓝 (0 : X k)).exists_antitone_basis
  have hcounter (i : ℕ) := hbad (A i) (hA.1.mem_of_mem trivial) ((i : ℝ) + 1) (by positivity)
  choose x hx y hy hxy hbadW using hcounter
  let : PolynormableSpace ℂ (X k) := PolynormableSpace.induced (X k).subtype
  let : IsTopologicalAddGroup (X k) := (PolynormableSpace.withSeminorms ℂ (X k)).topologicalAddGroup
  let : ContinuousSMul ℂ (X k) := (PolynormableSpace.withSeminorms ℂ (X k)).continuousSMul
  have hylim : Tendsto y atTop (𝓝 (0 : X k)) := hA.tendsto (fun i => hy i)
  obtain ⟨L, hL⟩ := bounded_sequence_extension (hX k) y (hylim.isVonNBounded_range ℂ)
  let u := (b k).comp L
  -- The ℓ¹ unit ball acts by absolutely convex combinations of the counterexample sequence.
  have hyD (i : ℕ) : b k (y i) ∈ D := by
    apply subset_closure
    exact ⟨x i, hx i, hb_eq.2 (hxy i)⟩
  have huD (z : lp (fun _ : ℕ => ℂ) 1) (hz : ‖z‖ ≤ 1) : u z ∈ D := by
    have ht := (b k).hasSum (hL z)
    apply (isClosed_closure (s := b n '' U)).mem_of_tendsto ht
    apply Eventually.of_forall
    intro t
    change (∑ i ∈ t, b k (z i • y i)) ∈ D
    simp only [map_smul]
    apply sum_mem_of_sum_norm_le hD0 hDB hDC t (fun i => z i) (fun i => b k (y i))
      (fun i _ => hyD i)
    exact ((scalar_l1_summable z).sum_le_tsum t (fun i _ => norm_nonneg _)).trans
      ((scalar_l1_norm z).ge.trans hz)
  have hurange (z : lp (fun _ : ℕ => ℂ) 1) : u z ∈ range j := by
    let a : ℝ := max 1 ‖z‖
    have ha : 0 < a := zero_lt_one.trans_le (le_max_left _ _)
    have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hunit : ‖(↑a : ℂ)⁻¹ • z‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha.le,
        inv_mul_le_iff₀ ha, mul_one]
      exact le_max_right _ _
    obtain ⟨w, hw⟩ := hDj (huD _ hunit)
    refine ⟨(↑a : ℂ) • w, ?_⟩
    rw [map_smul, hw, ← map_smul, smul_inv_smul₀ hane]
  obtain ⟨Lm, hLm⟩ := single_stage_factor (banach_frechet _) (X m) (hX m) u K j hj hurange
  let B := Lm '' Metric.closedBall 0 1
  have hB : IsVonNBounded ℂ B := (NormedSpace.isVonNBounded_closedBall ℂ _ 1).image Lm
  have hQW : K.mkQ '' W ∈ 𝓝 (0 : X m ⧸ K) := by
    have hopen := K.isOpenMap_mkQ
    simpa only [map_zero] using hopen.image_mem_nhds hW
  obtain ⟨R, hR⟩ := (absorbs_iff_norm.1 (hB hQW))
  obtain ⟨i, hi⟩ := exists_nat_gt R
  let e : lp (fun _ : ℕ => ℂ) 1 := lp.single 1 i (1 : ℂ)
  have he : e ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [show e = lp.single 1 i (1 : ℂ) from rfl, lp.norm_single (by simp : (0 : ENNReal) < 1)]
    simp
  have hLe : L e = y i := by
    rw [← (hL e).tsum_eq, tsum_eq_single i]
    · simp [e]
    · intro a ha
      simp [e, Pi.single_eq_of_ne ha]
  have hnorm : R ≤ ‖((↑((i : ℝ) + 1)) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith only [hi]
  obtain ⟨_, ⟨w, hw, rfl⟩, hw'e⟩ :=
    hR _ hnorm (show Lm e ∈ B from mem_image_of_mem Lm he)
  have hwq := congrArg j hw'e
  have hq : b n (x i) = (↑((i : ℝ) + 1) : ℂ) • b m w := by
    rw [map_smul, hLm, show u e = b k (L e) from rfl, hLe] at hwq
    exact (hb_eq.2 (hxy i)).trans hwq.symm
  refine hbadW i w hw ?_
  apply (hb_eq (i := n) (l := m) (x := x i) (y := (↑((i : ℝ) + 1) : ℂ) • w)).1
  rw [map_smul]
  exact hq

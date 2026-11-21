-- Prove2me | solution 1 for LocallyConvex.frechet_closedDisk_image_absorption
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T00:38:09.62192+00:00
-- url     : https://prove2.me/submissions/cf914a3f-9c93-4c98-94d2-9d87a5c6c66e

/-
The completeness, bounded-family summation, Banach-to-Frechet, and
single-stage factorization helpers adapt Prove2Me contributor marozols's
accepted submission 07895212-fd3d-40f2-8193-6512eb6d0c60 (Apache 2.0),
itself adapted from d5f91ac1-de44-4259-bd91-986ace858ac3.
This proof generalizes the summation construction from sequences to
arbitrary bounded sets and treats real disks by splitting coefficients.
-/
import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_frechet_countable_pullback_open_quotient

set_option autoImplicit false
open MasulloGRH Set Filter Topology Bornology
open scoped Pointwise

private theorem complete_of_filters {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] (hC : IsCompleteTVS E) : CompleteSpace E := by
  constructor
  intro f hf
  obtain ⟨hbot, hdiff⟩ := (IsUniformAddGroup.cauchy_iff_tendsto f).1 hf
  refine hC.2 f ⟨hbot, fun U hU => ?_⟩
  obtain ⟨A, hA, B, hB, hsub⟩ := mem_prod_iff.1 (hdiff hU)
  exact ⟨A ∩ B, inter_mem hA hB, fun x hx y hy => hsub (show (x, y) ∈ A ×ˢ B from ⟨hx.1, hy.2⟩)⟩

open scoped Pointwise

private theorem scalar_l1_norm {I : Type*} (z : lp (fun _ : I => ℂ) 1) :
    ‖z‖ = ∑' i, ‖z i‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by simp) z

private theorem scalar_l1_summable {I : Type*} (z : lp (fun _ : I => ℂ) 1) :
    Summable (fun i => ‖z i‖) := by
  simpa using (memℓp_gen_iff (p := 1) (by simp)).1 z.property

private theorem bounded_family_extension {I : Type*} {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (y : I → E)
    (hy : IsVonNBounded ℂ (range y)) :
    ∃ L : lp (fun _ : I => ℂ) 1 →L[ℂ] E,
      ∀ z : lp (fun _ : I => ℂ) 1, HasSum (fun i => z i • y i) (L z) := by
  obtain ⟨_, _, P, hP⟩ := hE.1
  let : IsTopologicalAddGroup E := hP.topologicalAddGroup
  let : ContinuousSMul ℂ E := hP.continuousSMul
  let : T2Space E := hE.2.1.1
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := complete_of_filters hE.2.1
  choose M hM hyM using hP.isVonNBounded_iff_seminorm_bounded.1 hy
  have hbound (z : lp (fun _ : I => ℂ) 1) (k : _) (s : Finset I) :
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
  have hs (z : lp (fun _ : I => ℂ) 1) : Summable (fun i => z i • y i) := by
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
  let L : lp (fun _ : I => ℂ) 1 →ₗ[ℂ] E :=
    { toFun := fun z => ∑' i, z i • y i
      map_add' := fun a b => by
        change (∑' i, (a i + b i) • y i) = _
        simp_rw [add_smul]
        exact (hs a).tsum_add (hs b)
      map_smul' := fun a z => by
        change (∑' i, (a * z i) • y i) = a • (∑' i, z i • y i)
        simp_rw [mul_smul]
        exact ((hs z).hasSum.const_smul a).tsum_eq }
  have hLp (k : _) (z : lp (fun _ : I => ℂ) 1) : P k (L z) ≤ M k * ‖z‖ := by
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
    refine mem_of_superset (Metric.ball_mem_nhds (0 : lp (fun _ : I => ℂ) 1)
      (show 0 < 1 / M k from one_div_pos.mpr (hM k))) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact (hLp k z).trans (by
      have h := (lt_div_iff₀ (hM k)).1 hz
      simpa only [mul_comm] using h.le)
  exact ⟨⟨L, hLc⟩, fun z => (hs z).hasSum⟩

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

private theorem real_sum_mem_disk {E : Type*} [AddCommGroup E] [Module ℝ E]
    {D : Set E} (h0 : (0 : E) ∈ D) (hD : AbsConvex ℝ D)
    {I : Type*} (s : Finset I) (a : I → ℝ) (x : I → E)
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
  let phase (i : I) : ℝ := ‖a i‖⁻¹ * a i
  have hphase (i : I) : ‖phase i‖ ≤ 1 := by
    by_cases hi : a i = 0
    · simp [phase, hi]
    · simp [phase, norm_mul, norm_inv, hi]
  have hrotation (i : I) : ‖a i‖ • (phase i • x i) = a i • x i := by
    rw [smul_smul]
    congr 1
    by_cases hi : a i = 0
    · simp [phase, hi]
    · dsimp [phase]
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hi), one_mul]
  have hin : (∑ i ∈ s, (‖a i‖ / r) • (phase i • x i)) ∈ D := by
    apply hD.2.sum_mem
    · exact fun i _ => div_nonneg (norm_nonneg _) hr
    · rw [← Finset.sum_div, div_self hr0]
    · exact fun i hi => hD.1.smul_mem (hphase i) (hx i hi)
  have hscaled := hD.1.smul_mem (a := r) (by rwa [Real.norm_of_nonneg hr]) hin
  convert hscaled using 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have heq : r * (‖a i‖ / r) = ‖a i‖ := by field_simp
  rw [smul_smul, heq, hrotation]

theorem solution
    (A : Type*) [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    (B : Type*) [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (Q : Type*) [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
    [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q] [T2Space Q]
    (hA : IsFrechet A) (hB : IsFrechet B)
    (a : A →L[ℂ] Q) (b : B →L[ℂ] Q)
    (C : Set Q) (hCclosed : IsClosed C) (hCdisk : AbsConvex ℝ C)
    (hCimage : C ⊆ Set.range b)
    (S : Set A) (hS : Bornology.IsVonNBounded ℂ S) (hSC : a '' S ⊆ C) :
    ∀ W ∈ nhds (0 : B), ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, R ≤ r → ∀ x ∈ S, ∃ w ∈ W, a x = (r : ℂ) • b w := by
  classical
  obtain ⟨_, _, PA, hPA⟩ := hA.1
  let : IsTopologicalAddGroup A := hPA.topologicalAddGroup
  let : ContinuousSMul ℂ A := hPA.continuousSMul
  let : T2Space A := hA.2.1.1
  obtain ⟨_, _, PB, hPB⟩ := hB.1
  let : IsTopologicalAddGroup B := hPB.topologicalAddGroup
  let : ContinuousSMul ℂ B := hPB.continuousSMul
  by_cases hne : S.Nonempty
  swap
  · intro W hW
    refine ⟨1, zero_lt_one, ?_⟩
    intro r hr x hx
    exact (hne ⟨x, hx⟩).elim
  have hC0 : (0 : Q) ∈ C := by
    obtain ⟨x, hx⟩ := hne
    simpa using hCdisk.1.smul_mem (a := (0 : ℝ)) (by simp) (hSC ⟨x, hx, rfl⟩)
  let y : S → A := Subtype.val
  have hy : IsVonNBounded ℂ (range y) := hS.subset (by rintro _ ⟨x, rfl⟩; exact x.property)
  obtain ⟨L, hL⟩ := bounded_family_extension hA y hy
  let u : lp (fun _ : S => ℂ) 1 →L[ℂ] Q := a.comp L
  have hyC (i : S) : a (y i) ∈ C := hSC ⟨i.val, i.property, rfl⟩
  have hreal (z : lp (fun _ : S => ℂ) 1) (hzreal : ∀ i, (z i).im = 0)
      (hzunit : ‖z‖ ≤ 1) : u z ∈ C := by
    have ht := a.hasSum (hL z)
    apply hCclosed.mem_of_tendsto ht
    apply Eventually.of_forall
    intro t
    change (∑ i ∈ t, a (z i • y i)) ∈ C
    simp only [map_smul]
    have heq (i : S) : z i = ((z i).re : ℂ) := by
      apply Complex.ext <;> simp [hzreal i]
    have hsum : ∑ i ∈ t, ‖(z i).re‖ ≤ 1 := by
      apply (Finset.sum_le_sum (fun i _ => Complex.abs_re_le_norm (z i))).trans
      exact ((scalar_l1_summable z).sum_le_tsum t (fun i _ => norm_nonneg _)).trans
        ((scalar_l1_norm z).ge.trans hzunit)
    convert real_sum_mem_disk hC0 hCdisk t (fun i => (z i).re) (fun i => a (y i))
      (fun i _ => hyC i) hsum using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [heq i]
    exact algebraMap_smul ℂ (z i).re _
  have hrealrange (z : lp (fun _ : S => ℂ) 1) (hzreal : ∀ i, (z i).im = 0) :
      u z ∈ range b := by
    let r : ℝ := max 1 ‖z‖
    have hr : 0 < r := zero_lt_one.trans_le (le_max_left _ _)
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hunit : ‖(r : ℂ)⁻¹ • z‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le,
        inv_mul_le_iff₀ hr, mul_one]
      exact le_max_right _ _
    have him (i : S) : (((r : ℂ)⁻¹ • z) i).im = 0 := by
      change ((r : ℂ)⁻¹ * z i).im = 0
      simp [Complex.mul_im, hzreal i]
    obtain ⟨w, hw⟩ := hCimage (hreal _ him hunit)
    refine ⟨(r : ℂ) • w, ?_⟩
    rw [map_smul, hw, ← map_smul, smul_inv_smul₀ hrne]
  have hurange (z : lp (fun _ : S => ℂ) 1) : u z ∈ range b := by
    have hparts (f : ℂ → ℝ) (hf : ∀ c, ‖f c‖ ≤ ‖c‖) :
        Memℓp (fun i : S => (f (z i) : ℂ)) 1 := by
      apply (memℓp_gen_iff (p := 1) (by simp)).2
      simpa using (scalar_l1_summable z).of_nonneg_of_le (fun i => norm_nonneg (f (z i)))
        (fun i => hf (z i))
    let zr : lp (fun _ : S => ℂ) 1 := ⟨fun i => ((z i).re : ℂ), hparts Complex.re Complex.abs_re_le_norm⟩
    let zi : lp (fun _ : S => ℂ) 1 := ⟨fun i => ((z i).im : ℂ), hparts Complex.im Complex.abs_im_le_norm⟩
    obtain ⟨wr, hwr⟩ := hrealrange zr (fun i => by simp [zr])
    obtain ⟨wi, hwi⟩ := hrealrange zi (fun i => by simp [zi])
    have hsplit : z = zr + Complex.I • zi := by
      ext i
      change z i = ((z i).re : ℂ) + Complex.I * ((z i).im : ℂ)
      apply Complex.ext <;> simp
    refine ⟨wr + Complex.I • wi, ?_⟩
    rw [map_add, map_smul, hwr, hwi, ← map_smul, ← map_add, ← hsplit]
  let K : Submodule ℂ B := LinearMap.ker b.toLinearMap
  let j : (B ⧸ K) →L[ℂ] Q :=
    ⟨K.liftQ b.toLinearMap le_rfl, K.isQuotientMap_mkQ.continuous_iff.2 b.continuous⟩
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.1
    exact K.ker_liftQ_eq_bot b.toLinearMap le_rfl le_rfl
  have huj (z : lp (fun _ : S => ℂ) 1) : u z ∈ range j := by
    obtain ⟨w, hw⟩ := hurange z
    exact ⟨K.mkQ w, hw⟩
  obtain ⟨T, hT⟩ := single_stage_factor (banach_frechet _) B hB u K j hj huj
  let D := T '' Metric.closedBall 0 1
  have hD : IsVonNBounded ℂ D := (NormedSpace.isVonNBounded_closedBall ℂ _ 1).image T
  intro W hW
  have hQW : K.mkQ '' W ∈ 𝓝 (0 : B ⧸ K) := by
    simpa only [map_zero] using K.isOpenMap_mkQ.image_mem_nhds hW
  obtain ⟨R, hR⟩ := absorbs_iff_norm.1 (hD hQW)
  refine ⟨max 1 R, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro r hr x hx
  let i : S := ⟨x, hx⟩
  let e : lp (fun _ : S => ℂ) 1 := lp.single 1 i (1 : ℂ)
  have he : e ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [show e = lp.single 1 i (1 : ℂ) from rfl, lp.norm_single (by norm_num : (0 : ENNReal) < 1)]
    simp
  have hLe : L e = x := by
    rw [← (hL e).tsum_eq, tsum_eq_single i]
    · simp [e, y, i]
    · intro j hj
      simp [e, Pi.single_eq_of_ne hj]
  have hnorm : R ≤ ‖(r : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans ((le_max_left 1 R).trans hr))]
    exact (le_max_right 1 R).trans hr
  obtain ⟨_, ⟨w, hw, rfl⟩, heq⟩ := hR _ hnorm (show T e ∈ D from mem_image_of_mem T he)
  have hwq := congrArg j heq
  rw [map_smul, hT, show u e = a (L e) from rfl, hLe] at hwq
  exact ⟨w, hw, hwq.symm⟩

-- Prove2me | solution 1 for MasulloGRH.quasinuclear_comp_nuclear_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:28:15.266366+00:00
-- url     : https://prove2.me/submissions/018d1b1b-7f68-4902-aa8e-fa56d93e0d3e

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


private noncomputable def weight (k : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ k

private theorem weight_pos (k : ℕ) : 0 < weight k := by unfold weight; positivity

private theorem weight_summable : Summable weight :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left 2

/-- Resolve a unit vector in the completion using normalized vectors in the dense subspace.
The geometric coefficient sequence is independent of the vector and of the two spaces. -/
private theorem dense_unit_series {X H : Type*} [SeminormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (j : X →ₗᵢ[ℂ] H) (hj : DenseRange j)
    (v : H) (hv : ‖v‖ ≤ 1) :
    ∃ y : ℕ → X, (∀ k, ‖y k‖ ≤ 1) ∧ HasSum (fun k => (weight k : ℂ) • j (y k)) v := by
  let e (k : ℕ) := (1 / 2 : ℝ) ^ k
  have he (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  choose a ha using fun k => (Metric.denseRange_iff.mp hj v (e k) (he k))
  let z : ℕ → X := fun k => if k = 0 then 0 else a k
  have hz0 : z 0 = 0 := by simp [z]
  have hz (k : ℕ) : ‖j (z k) - v‖ ≤ e k := by
    by_cases h : k = 0
    · subst k; simpa [hz0,e] using hv
    · simpa [z,h,← dist_eq_norm,dist_comm] using (ha k).le
  have hinc (k : ℕ) : ‖z (k+1) - z k‖ ≤ weight k := by
    calc
      ‖z (k+1) - z k‖ = ‖j (z (k+1)) - j (z k)‖ := by rw [← map_sub, j.norm_map]
      _ ≤ ‖j (z (k+1)) - v‖ + ‖j (z k) - v‖ := by
        simpa only [norm_sub_rev v (j (z k))] using norm_sub_le_norm_sub_add_norm_sub (j (z (k+1))) v (j (z k))
      _ ≤ e (k+1) + e k := add_le_add (hz _) (hz _)
      _ ≤ weight k := by dsimp [e,weight]; rw [pow_succ]; nlinarith [he k]
  let y (k : ℕ) := ((weight k : ℂ)⁻¹) • (z (k+1) - z k)
  have hval (k : ℕ) : (weight k : ℂ) • j (y k) = j (z (k+1)) - j (z k) := by
    have hw : (weight k : ℂ) ≠ 0 := by exact_mod_cast (weight_pos k).ne'
    simp only [y, map_smul, smul_smul, mul_inv_cancel₀ hw, one_smul, map_sub]
  refine ⟨y,fun k => ?_,?_⟩
  · dsimp [y]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (weight_pos k).le,
      inv_mul_le_iff₀ (weight_pos k),mul_one]
    exact hinc k
  · have hs : Summable fun k => ‖(weight k : ℂ) • j (y k)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
        rw [hval,← map_sub,j.norm_map]; exact hinc k) weight_summable
    apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
    have ht : Tendsto (fun k => j (z k)) atTop (𝓝 v) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero (fun k => norm_nonneg _) hz
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    simpa only [hval, Finset.sum_range_sub (fun k => j (z k)), hz0, map_zero,sub_zero] using ht
private noncomputable abbrev SeqOne := lp (fun _ : ℕ => ℂ) 1
private noncomputable abbrev SeqTwo := lp (fun _ : ℕ => ℂ) 2

/-- The weighted coefficient map factors all functionals dominated by the same ℓ¹ estimate. -/
private theorem factor_scalar {E : Type*} [AddCommGroup E] [Module ℂ E]
    (C : E →ₗ[ℂ] SeqOne) (f : E →ₗ[ℂ] ℂ) (h : ∀ x, ‖f x‖ ≤ ‖C x‖) :
    ∃ F : StrongDual ℂ SeqOne, ‖F‖ ≤ 1 ∧ ∀ x, F (C x) = f x := by
  let l := f.compLeftInverse C
  have key (x : E) : l (C.rangeRestrict x) = f x :=
    f.compLeftInverse_apply_of_bdd C ⟨1, fun t => by simpa only [one_mul] using h t⟩ x _ rfl
  have hn : ‖l‖ ≤ 1 := by
    apply l.opNorm_le_bound zero_le_one
    rintro ⟨_,x,rfl⟩
    change ‖l (C.rangeRestrict x)‖ ≤ 1 * ‖C x‖
    rw [key, one_mul]; exact h x
  obtain ⟨F,hF,hFn⟩ := exists_extension_norm_eq (LinearMap.range C) l
  exact ⟨F,hFn.trans_le hn,fun x => (hF (C.rangeRestrict x)).trans (key x)⟩

/-- Orthogonal projection extends a bounded map defined on a subspace of a Hilbert space. -/
private theorem factor_hilbert {E K H : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (j : E →ₗ[ℂ] K) (u : E →ₗ[ℂ] H) (C : ℝ) (hu : ∀ x, ‖u x‖ ≤ C * ‖j x‖) :
    ∃ A : K →L[ℂ] H, ∀ x, A (j x) = u x := by
  let S := (LinearMap.range j).topologicalClosure
  let d : E →ₗ[ℂ] S := j.codRestrict S (fun x => (LinearMap.range j).le_topologicalClosure ⟨x,rfl⟩)
  have hd : DenseRange d := by
    have h := ((denseRange_inclusion_iff (subset_closure (s := Set.range j))).2 Set.Subset.rfl).comp
      (Set.rangeFactorization_surjective (f := (j : E → K))).denseRange (continuous_inclusion subset_closure)
    exact h
  let A := u.extendOfNorm d
  refine ⟨A.comp S.orthogonalProjectionOnto,fun x => ?_⟩
  change A (S.orthogonalProjectionOnto ((d x : S) : K)) = u x
  rw [S.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact LinearMap.extendOfNorm_eq hd ⟨C,hu⟩ x

private noncomputable def sqrtWeight (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hs : Summable a) : SeqTwo :=
  ⟨fun n => (Real.sqrt (a n) : ℂ), memℓp_gen (by
    simpa [Complex.norm_real,Real.norm_of_nonneg, Real.sq_sqrt,ha] using hs)⟩

private noncomputable def weightedCoordinates (w : SeqTwo) (F : ℕ → StrongDual ℂ SeqOne)
    (hF : ∀ i, ‖F i‖ ≤ 1) : SeqOne →L[ℂ] SeqTwo := by
  have hb (x : SeqOne) (n : ℕ) : ‖w n * F n x‖ ≤ ‖((‖x‖ : ℂ) • w : SeqTwo) n‖ := by
    change ‖w n * F n x‖ ≤ ‖(‖x‖ : ℂ) * w n‖
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _), mul_comm ‖x‖]
    exact mul_le_mul_of_nonneg_left (((F n).le_of_opNorm_le (hF n) x).trans_eq (one_mul _)) (norm_nonneg _)
  let L : SeqOne →ₗ[ℂ] SeqTwo := {
    toFun := fun x => ⟨fun n => w n * F n x, (((‖x‖ : ℂ) • w : SeqTwo).2).mono' (hb x)⟩
    map_add' := fun x y => by ext i; change w i * F i (x+y) = w i * F i x + w i * F i y; rw [map_add,mul_add]
    map_smul' := fun c x => by ext i; change w i * F i (c • x) = c * (w i * F i x); rw [map_smul]; ring }
  refine L.mkContinuous ‖w‖ (fun x => ?_)
  calc
    ‖L x‖ ≤ ‖(‖x‖ : ℂ) • w‖ := lp.norm_mono (by norm_num) (hb x)
    _ = ‖w‖ * ‖x‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),mul_comm]

private noncomputable def oneCoordinates {E : Type*} [AddCommGroup E] [Module ℂ E]
    (g : ℕ → E →ₗ[ℂ] ℂ) (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    (s : Seminorm ℂ E) (hg : ∀ n x, ‖g n x‖ ≤ s x) : E →ₗ[ℂ] SeqOne where
  toFun x := ⟨fun k => (b k : ℂ) * g k x, memℓp_gen (by
    simp only [ENNReal.toReal_one,Real.rpow_one,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hb _)]
    exact Summable.of_nonneg_of_le (fun k => mul_nonneg (hb _) (norm_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (hg k x) (hb _)) (hs.mul_right (s x)))⟩
  map_add' x y := by ext i; change (b i : ℂ) * g i (x+y) = (b i : ℂ) * g i x + (b i : ℂ) * g i y; rw [map_add,mul_add]
  map_smul' c x := by ext i; change (b i : ℂ) * g i (c • x) = _; simp [lp.coeFn_smul]; ring

-- Factor a map through ℓ¹ by combining the two domination inequalities.
private theorem compose_factor {E H : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (u : E →ₗ[ℂ] H)
    (f : ℕ → E →ₗ[ℂ] ℂ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (has : Summable a)
    (C : E →ₗ[ℂ] SeqOne) (hf : ∀ i x, ‖f i x‖ ≤ ‖C x‖)
    (hu : ∀ x, ‖u x‖ ≤ ∑' n, a n * ‖f n x‖) :
    ∃ U : SeqOne →L[ℂ] H, ∀ x, U (C x) = u x := by
  choose F hF hFC using fun n => factor_scalar C (f n) (hf n)
  let w := sqrtWeight a ha has
  let D := weightedCoordinates w F hF
  let j := D.toLinearMap.comp C
  have hj (x : E) (n : ℕ) : (j x) n = w n * f n x := by
    change w n * F n (C x) = _
    rw [hFC]
  have hbound (x : E) : ‖u x‖ ≤ ‖w‖ * ‖j x‖ := by
    apply (hu x).trans
    calc
      ∑' n, a n * ‖f n x‖ = ∑' n, ‖w n‖ * ‖(j x) n‖ := by
        apply tsum_congr
        intro n
        rw [hj,norm_mul,← mul_assoc]
        change a n * ‖f n x‖ = (‖(Real.sqrt (a n) : ℂ)‖ * ‖(Real.sqrt (a n) : ℂ)‖) * ‖f n x‖
        rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.mul_self_sqrt (ha n)]
      _ ≤ ‖w‖ * ‖j x‖ := lp.tsum_mul_le_mul_norm' (p := 2) (q := 2)
        (by simpa using Real.HolderConjugate.two_two) w (j x)
  obtain ⟨A,hA⟩ := factor_hilbert j u ‖w‖ hbound
  exact ⟨A.comp D,hA⟩

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (q r s : Seminorm ℂ E)
    (f : ℕ → StrongDual ℂ E) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (has : Summable a)
    (hf : ∀ n x, ‖f n x‖ ≤ r x) (hqr : ∀ x, q x ≤ ∑' n, a n * ‖f n x‖)
    (g : ℕ → StrongDual ℂ E) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hbs : Summable b)
    (hg : ∀ n x, ‖g n x‖ ≤ s x) (hrs : ∀ x, r x ≤ ∑' n, b n * ‖g n x‖) :
    ∃ (h : ℕ → StrongDual ℂ E) (y : ℕ → E) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖h n x‖ ≤ s x) ∧ (∀ n, q (y n) ≤ 1) ∧
      ∀ x, Tendsto (fun N => q (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * h n x) • y n)) atTop (𝓝 0) := by
  classical
  let X := SeminormModel q
  let H := Completion X
  let I : X →ₗᵢ[ℂ] H := Completion.toComplₗᵢ
  let idX : E →ₗ[ℂ] X := LinearMap.id
  let u := I.toLinearMap.comp idX
  let C := oneCoordinates (fun n => (g n).toLinearMap) b hb hbs s hg
  have hC (x : E) : ‖C x‖ = ∑' n, b n * ‖g n x‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num)]
    simp only [ENNReal.toReal_one,Real.rpow_one,div_one]
    apply tsum_congr
    intro n
    change ‖(b n : ℂ) * g n x‖ = b n * ‖g n x‖
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hb _)]
  have hu (x : E) : ‖u x‖ = q x := I.norm_map (idX x)
  obtain ⟨U,hU⟩ := compose_factor u (fun n => (f n).toLinearMap) a ha has C
    (fun n x => (hf n x).trans ((hrs x).trans_eq (hC x).symm)) (fun x => (hu x).trans_le (hqr x))
  let unit (n : ℕ) : SeqOne := lp.single 1 n (1 : ℂ)
  let M := ‖U‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMn : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let v (n : ℕ) := ((M : ℂ)⁻¹) • U (unit n)
  have hv (n : ℕ) : ‖v n‖ ≤ 1 := by
    dsimp [v]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hM.le,inv_mul_le_iff₀ hM,mul_one]
    have hn : ‖unit n‖ = 1 := by simp [unit,lp.norm_single]
    have h := U.le_opNorm (unit n)
    rw [hn,mul_one] at h
    exact h.trans (by dsimp [M]; linarith)
  choose y hy hseries using fun n => dense_unit_series I Completion.denseRange_coe (v n) (hv n)
  let d (t : ℕ × ℕ) := (b t.1 * M) * weight t.2
  let e := Nat.pairEquiv.symm
  have hd0 (t : ℕ × ℕ) : 0 ≤ d t := mul_nonneg (mul_nonneg (hb _) hM.le) (weight_pos _).le
  have hd : Summable d := (hbs.mul_right M).mul_of_nonneg weight_summable
    (fun n => mul_nonneg (hb _) hM.le) (fun k => (weight_pos _).le)
  refine ⟨fun n => g (e n).1, fun n => (y (e n).1 (e n).2 : E),d ∘ e,fun _ => hd0 _,
    e.summable_iff.mpr hd,fun _ => hg _,fun _ => hy _ _,?_⟩
  intro x
  let term (t : ℕ × ℕ) := (((d t : ℝ) : ℂ) * g t.1 x) • I (y t.1 t.2)
  have ht : Summable term := Summable.of_norm <| Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun t => by
      dsimp only [term]
      rw [norm_smul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hd0 _),I.norm_map]
      exact (mul_le_of_le_one_right (mul_nonneg (hd0 _) (norm_nonneg _)) (hy _ _)).trans
        (mul_le_mul_of_nonneg_left (hg _ _) (hd0 _))) (hd.mul_right (s x))
  have hrow (n : ℕ) : HasSum (fun k => term (n,k)) (U (lp.single 1 n ((C x) n))) := by
    have h := (hseries n).const_smul (((b n : ℂ) * g n x) * (M : ℂ))
    have hident (k : ℕ) : (((b n : ℂ) * g n x) * (M : ℂ)) • (weight k : ℂ) • I (y n k) = term (n,k) := by
      change _ = (((b n * M * weight k : ℝ) : ℂ) * g n x) • I (y n k)
      rw [smul_smul]; push_cast; ring_nf
    simp only [hident] at h
    convert h using 1
    change U (lp.single 1 n ((b n : ℂ) * g n x)) = _ • ((M : ℂ)⁻¹) • U (unit n)
    have hsingle (z : ℂ) : lp.single 1 n z = z • unit n := by
      simpa only [smul_eq_mul,mul_one] using lp.single_smul (E := fun _ : ℕ => ℂ) 1 n z (1 : ℂ)
    rw [hsingle,map_smul,smul_smul,mul_assoc,mul_inv_cancel₀ hMn,mul_one]
  have hsum : HasSum term (u x) := by
    have hout := U.hasSum (lp.hasSum_single (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (C x))
    rw [hU] at hout
    exact (ht.hasSum.prod_fiberwise hrow).unique hout ▸ ht.hasSum
  have htend := (e.hasSum_iff.mpr hsum).tendsto_sum_nat
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp htend
  apply hn.congr
  intro N
  rw [← hu,map_sub,map_sum,norm_sub_rev]
  apply congrArg (fun z => ‖u x - z‖)
  apply Finset.sum_congr rfl
  intro n _
  exact (map_smul u (((d (e n) : ℝ) : ℂ) * g (e n).1 x) (show E from y (e n).1 (e n).2)).symm

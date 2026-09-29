-- Prove2me | solution 1 for KannanLattice.Core.closest_point_tail_mem_candidates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:24:06.368611+00:00
-- url     : https://prove2.me/submissions/6109cb7c-aa50-44aa-a7c7-c29a9ce91235

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced



namespace KannanLattice.Core

open InnerProductSpace

lemma lattice_le_span {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    {v : EuclideanSpace ℝ (Fin k)} (hv : v ∈ lattice b) :
    v ∈ Submodule.span ℝ (Set.range b) := by
  unfold lattice at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ hx

lemma inner_gsN_lt {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) {t j : Fin m}
    (h : t < j) : inner ℝ (gramSchmidtNormed ℝ b j) (b t) = 0 := by
  simp [gramSchmidtNormed, inner_smul_left, gramSchmidt_inv_triangular ℝ b h]

lemma inner_gs_self {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (t : Fin m) :
    inner ℝ (gramSchmidt ℝ b t) (b t) = ‖gramSchmidt ℝ b t‖ ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' ℝ b t]
  rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [inner_smul_right, gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.1 hi).ne', mul_zero]

lemma inner_gsN_self {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (t : Fin m) :
    inner ℝ (gramSchmidtNormed ℝ b t) (b t) = gsLen b t := by
  unfold gramSchmidtNormed gsLen
  rw [inner_smul_left, inner_gs_self]
  simp only [RCLike.conj_to_real]
  by_cases h : ‖gramSchmidt ℝ b t‖ = 0
  · simp [h]
  · field_simp
    rfl

lemma gsLen_pos {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (t : Fin m) : 0 < gsLen b t := by
  unfold gsLen
  exact norm_pos_iff.2 (gramSchmidt_ne_zero t hb)

lemma norm_sq_eq_sum_inner {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    (hb : LinearIndependent ℝ b) (w : EuclideanSpace ℝ (Fin k))
    (hw : w ∈ Submodule.span ℝ (Set.range b)) :
    ‖w‖ ^ 2 = ∑ j, (inner ℝ (gramSchmidtNormed ℝ b j) w) ^ 2 := by
  have hu := gramSchmidtNormed_orthonormal (𝕜 := ℝ) hb
  rw [← span_gramSchmidt ℝ b, ← span_gramSchmidtNormed_range] at hw
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
  have hc : ∀ j, inner ℝ (gramSchmidtNormed ℝ b j) (∑ i, a i • gramSchmidtNormed ℝ b i) = a j :=
    fun j => hu.inner_right_fintype a j
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, hc]
  simp [sq]

theorem near_core (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (b₀ : EuclideanSpace ℝ (Fin k)) :
    ∃ v ∈ lattice b,
      ‖v - (Submodule.span ℝ (Set.range b)).starProjection b₀‖ ≤
          (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) ∧
      ∀ i : Fin m, (∀ j : Fin m, gsLen b j ≤ gsLen b i) →
        ‖(Submodule.span ℝ (Set.range b)).starProjection b₀ - v‖ ≤
          Real.sqrt m / 2 * gsLen b i := by
  set S := Submodule.span ℝ (Set.range b) with hS
  set p := S.starProjection b₀ with hp
  set u := gramSchmidtNormed ℝ b with hu
  have key : ∀ s, s ≤ m → ∃ v ∈ lattice b, ∀ j : Fin m, m - s ≤ (j : ℕ) →
      |inner ℝ (u j) (v - p)| ≤ gsLen b j / 2 := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨0, Submodule.zero_mem _, fun j hj => ?_⟩
      exfalso; have := j.2; omega
    | succ s ih =>
      intro hs
      obtain ⟨v, hv, hvj⟩ := ih (by omega)
      set t : Fin m := ⟨m - s - 1, by omega⟩ with ht
      have hpos := gsLen_pos b hb t
      set x := inner ℝ (u t) (v - p) / gsLen b t with hx
      refine ⟨v - round x • b t, ?_, ?_⟩
      · exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩))
      · intro j hj
        have e : v - round x • b t - p = (v - p) - ((round x : ℤ) : ℝ) • b t := by
          rw [Int.cast_smul_eq_zsmul]; abel
        rw [e, inner_sub_right, inner_smul_right]
        rcases (show (j : ℕ) = m - s - 1 ∨ m - s ≤ (j : ℕ) by omega) with h1 | h1
        · have : j = t := Fin.ext h1
          subst this
          rw [hu, inner_gsN_self, ← hu]
          have h2 : inner ℝ (u t) (v - p) = x * gsLen b t := by
            rw [hx]; field_simp
          rw [h2, ← sub_mul, abs_mul, abs_of_pos hpos]
          have := abs_sub_round x
          nlinarith
        · have hlt : t < j := by
            rw [Fin.lt_def]; simp [ht]; omega
          rw [hu, inner_gsN_lt b hlt, ← hu, mul_zero, sub_zero]
          exact hvj j h1
  obtain ⟨v, hv, hvj⟩ := key m le_rfl
  have hvj' : ∀ j, |inner ℝ (u j) (v - p)| ≤ gsLen b j / 2 := fun j => hvj j (by omega)
  have hw : v - p ∈ S := Submodule.sub_mem _ (lattice_le_span b hv) (S.starProjection_apply_mem b₀)
  have hn := norm_sq_eq_sum_inner b hb (v - p) hw
  have hbound : ‖v - p‖ ^ 2 ≤ (1/4 : ℝ) * ∑ j, gsLen b j ^ 2 := by
    rw [hn, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := hvj' j
    have h0 : 0 ≤ gsLen b j := (gsLen_pos b hb j).le
    have : (inner ℝ (u j) (v - p)) ^ 2 ≤ (gsLen b j / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith
  have hfirst : ‖v - p‖ ≤ (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) := by
    have : (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) =
        Real.sqrt ((1/4 : ℝ) * ∑ j, gsLen b j ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), show (1/4 : ℝ) = (1/2)^2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.le_sqrt_of_sq_le hbound
  refine ⟨v, hv, hfirst, fun i hi => ?_⟩
  rw [norm_sub_rev]
  refine hfirst.trans ?_
  have h0 : 0 ≤ gsLen b i := (gsLen_pos b hb i).le
  have hsum : ∑ j, gsLen b j ^ 2 ≤ (m : ℝ) * gsLen b i ^ 2 := by
    calc ∑ j, gsLen b j ^ 2 ≤ ∑ _j : Fin m, gsLen b i ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (gsLen_pos b hb j).le (hi j) 2
      _ = (m : ℝ) * gsLen b i ^ 2 := by simp
  have : Real.sqrt (∑ j, gsLen b j ^ 2) ≤ Real.sqrt m * gsLen b i := by
    calc Real.sqrt (∑ j, gsLen b j ^ 2) ≤ Real.sqrt ((m : ℝ) * gsLen b i ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt m * gsLen b i := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq h0]
  linarith


lemma projOrth_eq_zero_of_mem {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (i : Fin m)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ Submodule.span ℝ (b '' Set.Iio i)) :
    projOrth b i x = 0 := by
  unfold projOrth
  exact Submodule.starProjection_orthogonal_apply_eq_zero hx

lemma projOrth_tail {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (i : Fin m)
    (c : Fin m → ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    projOrth b i ((∑ j : {j : Fin m // i ≤ j}, c j • b j) - y) =
      projOrth b i ((∑ j, c j • b j) - y) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => i ≤ j) (fun j => c j • b j)]
  have hmem : (∑ j : {j : Fin m // ¬ i ≤ j}, c j • b j) ∈ Submodule.span ℝ (b '' Set.Iio i) := by
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨j, Set.mem_Iio.2 (not_le.1 j.2), rfl⟩
  rw [show (∑ j : {j : Fin m // i ≤ j}, c j • b j) + (∑ j : {j : Fin m // ¬ i ≤ j}, c j • b j) - y
      = ((∑ j : {j : Fin m // i ≤ j}, c j • b j) - y) + (∑ j : {j : Fin m // ¬ i ≤ j}, c j • b j)
      by abel, map_add, projOrth_eq_zero_of_mem b i hmem, add_zero]

lemma projOrth_tail_ne_zero {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    (hb : LinearIndependent ℝ b) (i : Fin m) (ν : {j : Fin m // i ≤ j} → ℝ) (hν : ν ≠ 0) :
    projOrth b i (∑ j : {j : Fin m // i ≤ j}, ν j • b j) ≠ 0 := by
  intro h
  unfold projOrth at h
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h
  have h2 : (∑ j : {j : Fin m // i ≤ j}, ν j • b j) ∈ Submodule.span ℝ (b '' Set.Ici i) := by
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨j, Set.mem_Ici.2 j.2, rfl⟩
  have hdisj := hb.disjoint_span_image (s := Set.Iio i) (t := Set.Ici i)
    (Set.disjoint_left.2 fun x hx hx' => absurd (Set.mem_Ici.1 hx') (not_le.2 (Set.mem_Iio.1 hx)))
  have h0 := (Submodule.disjoint_def.1 hdisj) _ h h2
  have hli : LinearIndependent ℝ (fun j : {j : Fin m // i ≤ j} => b j) :=
    hb.comp _ Subtype.val_injective
  apply hν
  funext j
  exact Fintype.linearIndependent_iff.1 hli ν h0 j

theorem cand_core (m k : ℕ) (hm : 2 ≤ m)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) (hred : IsReduced b)
    (b₀ : EuclideanSpace ℝ (Fin k)) (i : Fin m) (hi : ∀ j : Fin m, gsLen b j ≤ gsLen b i) :
    let T : Set ({j : Fin m // i ≤ j} → ℤ) :=
      {μ | ‖projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ j : ℝ) • b j) -
              (Submodule.span ℝ (Set.range b)).starProjection b₀)‖ ≤
            Real.sqrt m / 2 * gsLen b i}
    T.Finite ∧ T.ncard ≤ m ^ (m - (i : ℕ)) ∧
      ∀ lam : Fin m → ℤ,
        (∀ w ∈ lattice b, ‖(∑ j, (lam j : ℝ) • b j) - b₀‖ ≤ ‖w - b₀‖) →
          (fun j : {j : Fin m // i ≤ j} => lam j) ∈ T := by
  classical
  intro T
  set p := (Submodule.span ℝ (Set.range b)).starProjection b₀ with hp
  have hs := gsLen_pos b hb i
  haveI : NeZero m := ⟨by omega⟩
  let f : ({j : Fin m // i ≤ j} → ℤ) → ({j : Fin m // i ≤ j} → ZMod m) :=
    fun μ j => (μ j : ZMod m)
  have hinj : Set.InjOn f T := by
    intro μ hμ μ' hμ' hf
    by_contra hne
    have hdvd : ∀ j, (m : ℤ) ∣ μ j - μ' j := by
      intro j
      have := congrFun hf j
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this.symm
    choose ν hν using hdvd
    have hν0 : (fun j => (ν j : ℝ)) ≠ 0 := by
      intro h0
      apply hne
      funext j
      have := congrFun h0 j
      simp only [Pi.zero_apply, Int.cast_eq_zero] at this
      have := hν j
      rw [‹ν j = 0›, mul_zero, sub_eq_zero] at this
      exact this
    set y := projOrth b i (∑ j : {j : Fin m // i ≤ j}, (ν j : ℝ) • b j) with hy
    have hy0 : y ≠ 0 := projOrth_tail_ne_zero b hb i _ hν0
    have hyL : y ∈ projLattice b i := by
      refine ⟨∑ j : {j : Fin m // i ≤ j}, (ν j : ℝ) • b j, ?_, rfl⟩
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    have hyn : gsLen b i ≤ ‖y‖ := by
      rw [hred.1 i]
      unfold lambdaOne
      refine csInf_le ⟨0, ?_⟩ ⟨y, ⟨hyL, hy0⟩, rfl⟩
      rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _
    have hdiff : projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ j : ℝ) • b j) - p) -
        projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ' j : ℝ) • b j) - p) = (m : ℝ) • y := by
      rw [← map_sub, hy, ← map_smul, Finset.smul_sum]
      congr 1
      rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← sub_smul, smul_smul, ← Int.cast_sub, hν j]
      push_cast; ring_nf
    have hle : (m : ℝ) * ‖y‖ ≤ Real.sqrt m * gsLen b i := by
      have := norm_sub_le (projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ j : ℝ) • b j) - p))
        (projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ' j : ℝ) • b j) - p))
      rw [hdiff, norm_smul, Real.norm_natCast] at this
      have h1 : ‖projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ j : ℝ) • b j) - p)‖ ≤
          Real.sqrt m / 2 * gsLen b i := hμ
      have h2 : ‖projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ' j : ℝ) • b j) - p)‖ ≤
          Real.sqrt m / 2 * gsLen b i := hμ'
      linarith
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
    have hsq0 := Real.sqrt_nonneg (m : ℝ)
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have : (m : ℝ) * gsLen b i ≤ Real.sqrt m * gsLen b i := by nlinarith
    have : (m : ℝ) ≤ Real.sqrt m := le_of_mul_le_mul_right this hs
    nlinarith
  have hfin : T.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  refine ⟨hfin, ?_, ?_⟩
  · have := Set.ncard_le_ncard_of_injOn f (fun a _ => Set.mem_univ (f a)) hinj
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_subtype] at this
    have hc : (Finset.univ.filter fun j : Fin m => i ≤ j).card = m - (i : ℕ) := by
      rw [show (Finset.univ.filter fun j : Fin m => i ≤ j) = Finset.Ici i by ext; simp]
      exact Fin.card_Ici i
    rw [hc] at this
    exact this
  · intro lam hlam
    show ‖projOrth b i ((∑ j : {j : Fin m // i ≤ j}, ((lam j : ℤ) : ℝ) • b j) - p)‖ ≤ _
    rw [projOrth_tail b i (fun j => (lam j : ℝ)) p]
    obtain ⟨v, hv, -, hv2⟩ := near_core m k b hb b₀
    have hv3 : ‖v - p‖ ≤ Real.sqrt m / 2 * gsLen b i := by
      rw [norm_sub_rev]; exact hv2 i hi
    set w := ∑ j, (lam j : ℝ) • b j with hw
    have hwL : w ∈ lattice b := by
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    have hcl := hlam v hv
    -- Pythagoras
    set S := Submodule.span ℝ (Set.range b)
    have hperp : b₀ - p ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal b₀
    have pyth : ∀ x ∈ lattice b, ‖x - b₀‖ ^ 2 = ‖x - p‖ ^ 2 + ‖b₀ - p‖ ^ 2 := by
      intro x hx
      have hxS : x - p ∈ S := Submodule.sub_mem _ (lattice_le_span b hx)
        (S.starProjection_apply_mem b₀)
      have := norm_sub_sq_real (x - p) (b₀ - p)
      rw [Submodule.inner_right_of_mem_orthogonal hxS hperp] at this
      rw [show x - b₀ = (x - p) - (b₀ - p) by abel, this]
      ring
    have h1 := pyth w hwL
    have h2 := pyth v hv
    have hsq : ‖w - b₀‖ ^ 2 ≤ ‖v - b₀‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcl 2
    have hwp : ‖w - p‖ ≤ ‖v - p‖ := by
      have : ‖w - p‖ ^ 2 ≤ ‖v - p‖ ^ 2 := by linarith
      exact le_of_sq_le_sq (by simpa using this) (norm_nonneg _) |>.trans le_rfl
    calc ‖projOrth b i (w - p)‖ ≤ ‖w - p‖ := by
          unfold projOrth; exact Submodule.norm_starProjection_apply_le _ _
      _ ≤ ‖v - p‖ := hwp
      _ ≤ _ := hv3

end KannanLattice.Core

open KannanLattice.Core


theorem solution (m k : ℕ) (hm : 2 ≤ m)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) (hred : IsReduced b)
    (b₀ : EuclideanSpace ℝ (Fin k)) (i : Fin m) (hi : ∀ j : Fin m, gsLen b j ≤ gsLen b i) :
    let T : Set ({j : Fin m // i ≤ j} → ℤ) :=
      {μ | ‖projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ j : ℝ) • b j) -
              (Submodule.span ℝ (Set.range b)).starProjection b₀)‖ ≤
            Real.sqrt m / 2 * gsLen b i}
    T.Finite ∧ T.ncard ≤ m ^ (m - (i : ℕ)) ∧
      ∀ lam : Fin m → ℤ,
        (∀ w ∈ lattice b, ‖(∑ j, (lam j : ℝ) • b j) - b₀‖ ≤ ‖w - b₀‖) →
          (fun j : {j : Fin m // i ≤ j} => lam j) ∈ T := by
  exact cand_core m k hm b hb hred b₀ i hi

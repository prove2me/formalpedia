-- Prove2me | solution 1 for MasulloGRH.prime_sums_converge_on_one_line
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T17:45:06.097153+00:00
-- url     : https://prove2.me/submissions/80af7b8a-da4f-4c15-a0ef-dfa918f1af46

import Definitions.Def_MasulloGRH_IdeleNorm
import Theorems.Thm_MasulloGRH_vonMangoldt_sums_on_one_line

set_option autoImplicit false

/-!
# Corollary B.7.2.3: the prime sums converge on the 1-line

We reduce Corollary B.7.2.3 to Theorem B.7.1.2 (convergence and oscillation of the Dirichlet
polynomials of `L_f'/L_f` on the line `Re s = 1`), following the proofs of Theorem B.7.2.1 and
Corollary B.7.2.3 in the source.

* `T_N(s) = ∑_{N(𝔭^k) ≤ N} χ(𝔭)^k log N(𝔭) N(𝔭)^{-ks}` is the Dirichlet polynomial of `-L_f'/L_f`.
* `D_N(s) = ∑_{N(𝔭^k) ≤ N} χ(𝔭)^k / k · N(𝔭)^{-ks}` is obtained from `T_N` by Abel summation with
  the weights `a_n = 1 / log n`.
* By Theorem B.7.1.2, near every point of the relevant part of the line the `T_N` have uniformly
  bounded oscillation; since `a_n` decreases to `0`, the `D_N` are uniformly Cauchy.
* The terms of `D_N` with `k ≥ 2` are dominated by `N(𝔭)^{-k}`, which is summable; removing them
  leaves the prime sums.
-/

namespace MasulloGRH.PS

open Filter Topology NumberField IsDedekindDomain Complex

/-! ### Abel summation -/

section abelSection

/-- Abel summation, written relative to a base index `M`. -/
lemma abel_identity (D T : ℕ → ℂ) (a : ℕ → ℝ)
    (hstep : ∀ n, D (n + 1) - D n = (a (n + 1) : ℂ) * (T (n + 1) - T n)) (M : ℕ) (k : ℕ) :
    D (M + k) - D M = (a (M + k) : ℂ) * (T (M + k) - T M) -
      ∑ j ∈ Finset.range k, (T (M + j) - T M) * ((a (M + (j + 1)) : ℂ) - (a (M + j) : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hstep (M + k)
    rw [Finset.sum_range_succ]
    have e : D (M + (k + 1)) - D M = (D (M + k + 1) - D (M + k)) + (D (M + k) - D M) := by
      rw [← add_assoc]; ring
    rw [e, h, ih, ← add_assoc]
    ring

/-- If the `T n` stay within `K` of `T M` for `n ≥ M`, and the weights `a n` are nonnegative and
nonincreasing from `M` on, then the Abel transforms `D` stay within `K * a M` of `D M`. -/
lemma abel_bound (D T : ℕ → ℂ) (a : ℕ → ℝ)
    (hstep : ∀ n, D (n + 1) - D n = (a (n + 1) : ℂ) * (T (n + 1) - T n)) (M : ℕ) (K : ℝ)
    (ha : ∀ n, M ≤ n → a (n + 1) ≤ a n) (ha0 : ∀ n, M ≤ n → 0 ≤ a n)
    (hT : ∀ n, M ≤ n → ‖T n - T M‖ ≤ K) (k : ℕ) :
    ‖D (M + k) - D M‖ ≤ K * a M := by
  have hK : 0 ≤ K := by simpa using hT M le_rfl
  rw [abel_identity D T a hstep M k]
  have h1 : ‖(a (M + k) : ℂ) * (T (M + k) - T M)‖ ≤ a (M + k) * K := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha0 _ (Nat.le_add_right _ _))]
    exact mul_le_mul_of_nonneg_left (hT _ (Nat.le_add_right _ _)) (ha0 _ (Nat.le_add_right _ _))
  have h2 : ‖∑ j ∈ Finset.range k,
      (T (M + j) - T M) * ((a (M + (j + 1)) : ℂ) - (a (M + j) : ℂ))‖ ≤
      ∑ j ∈ Finset.range k, K * (a (M + j) - a (M + (j + 1))) := by
    refine norm_sum_le_of_le _ fun j _ => ?_
    have hj : a (M + (j + 1)) ≤ a (M + j) := ha (M + j) (Nat.le_add_right _ _)
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.2 hj), neg_sub]
    exact mul_le_mul_of_nonneg_right (hT _ (Nat.le_add_right _ _)) (sub_nonneg.2 hj)
  have h3 : ∑ j ∈ Finset.range k, K * (a (M + j) - a (M + (j + 1))) = K * (a M - a (M + k)) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub' (fun j => a (M + j))]
    simp
  calc ‖(a (M + k) : ℂ) * (T (M + k) - T M) -
        ∑ j ∈ Finset.range k, (T (M + j) - T M) * ((a (M + (j + 1)) : ℂ) - (a (M + j) : ℂ))‖
      ≤ a (M + k) * K + K * (a M - a (M + k)) := (norm_sub_le _ _).trans (add_le_add h1 (h2.trans h3.le))
    _ = K * a M := by ring

/-- The weights `a n = 1 / log n`. -/
noncomputable def wt (n : ℕ) : ℝ := 1 / Real.log n

lemma wt_nonneg (n : ℕ) : 0 ≤ wt n := by
  unfold wt
  exact div_nonneg zero_le_one (Real.log_natCast_nonneg n)

lemma wt_anti (n : ℕ) (hn : 2 ≤ n) : wt (n + 1) ≤ wt n := by
  unfold wt
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have h2 : 0 < Real.log n := Real.log_pos h1
  refine one_div_le_one_div_of_le h2 (Real.log_le_log (by linarith) ?_)
  push_cast
  linarith

lemma wt_tendsto : Tendsto wt atTop (𝓝 0) := by
  unfold wt
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

end abelSection

/-! ### Places of a number field -/

section hecke

open Ideal

variable {F : Type*} [Field F] [NumberField F]

theorem lseriesSummable_card (σ : ℝ) (hσ : 1 < σ) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 F) // absNorm I = n} : ℝ) : ℂ)) σ := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n => (Nat.card {I : Ideal (𝓞 F) // absNorm I = n} : ℝ)) ?_
    (fun _ => Nat.cast_nonneg _) zero_le_one (by simpa using hσ)
  refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (a := ?_) ?_
  · exact (2 ^ InfinitePlace.nrRealPlaces F * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F *
      Units.regulator F * classNumber F) / (Units.torsionOrder F * Real.sqrt |discr F|)
  have h := ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop)
  simp only [Real.rpow_one]
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 F) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem summable_idealNorm (σ : ℝ) (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 F) => ((absNorm I : ℕ) : ℝ) ^ (-σ) := by
  have hL := lseriesSummable_card (F := F) σ hσ
  rw [LSeriesSummable, ← summable_norm_iff] at hL
  let g : Ideal (𝓞 F) → ℕ := fun I => absNorm I
  rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
  have hnn : ∀ x : (Σ n : ℕ, {I : Ideal (𝓞 F) // g I = n}),
      0 ≤ ((fun I : Ideal (𝓞 F) => ((absNorm I : ℕ) : ℝ) ^ (-σ)) ∘ (Equiv.sigmaFiberEquiv g)) x :=
    fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [summable_sigma_of_nonneg hnn]
  refine ⟨fun n => ?_, ?_⟩
  · have : Finite {I : Ideal (𝓞 F) // g I = n} := Ideal.finite_setOfPred_absNorm_eq n
    exact Summable.of_finite
  · refine hL.congr fun n => ?_
    have : Finite {I : Ideal (𝓞 F) // g I = n} := Ideal.finite_setOfPred_absNorm_eq n
    have h1 : ∀ y : {I : Ideal (𝓞 F) // g I = n},
        ((fun I : Ideal (𝓞 F) => ((absNorm I : ℕ) : ℝ) ^ (-σ)) ∘ (Equiv.sigmaFiberEquiv g)) ⟨n, y⟩
          = (n : ℝ) ^ (-σ) := by
      intro y
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
      rw [show (absNorm y.1 : ℕ) = n from y.2]
    simp_rw [h1]
    rw [tsum_const, nsmul_eq_mul, LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (show -σ ≠ 0 by linarith)]
    · rw [if_neg hn, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _),
        Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

theorem summable_placeNorm (σ : ℝ) (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  (summable_idealNorm (F := F) σ hσ).comp_injective
    (fun _ _ h => HeightOneSpectrum.ext h)

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ absNorm v.asIdeal := by
  have h0 : absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

lemma two_le_natNorm (v : HeightOneSpectrum (𝓞 F)) :
    (2 : ℝ) ≤ ((absNorm v.asIdeal : ℕ) : ℝ) := by
  exact_mod_cast two_le_absNorm v

theorem norm_primeValue_le (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    ‖χ.primeValue v‖ ≤ 1 := by
  unfold HeckeCharacter.primeValue
  split_ifs
  · unfold HeckeCharacter.localComponent
    rw [Circle.norm_coe]
  · simp

lemma summable_two : Summable fun v : HeightOneSpectrum (𝓞 F) =>
    ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-2 : ℝ) :=
  summable_placeNorm (F := F) 2 (by norm_num)

lemma finite_lt (x : ℝ) :
    {v : HeightOneSpectrum (𝓞 F) | ((absNorm v.asIdeal : ℕ) : ℝ) < x}.Finite := by
  have hI := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌈x⌉₊
  refine (hI.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h)).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hv ⊢
  have : ((absNorm v.asIdeal : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) := hv.le.trans (Nat.le_ceil x)
  exact_mod_cast this

/-- The finite set of places `v` with `N(𝔭_v) < x`. -/
noncomputable def normLT (x : ℝ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (finite_lt (F := F) x).toFinset

lemma mem_normLT {x : ℝ} {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ normLT x ↔ ((absNorm v.asIdeal : ℕ) : ℝ) < x := by
  unfold normLT
  rw [Set.Finite.mem_toFinset]
  rfl

lemma finsum_eq (x : ℝ) (f : HeightOneSpectrum (𝓞 F) → ℂ) :
    ∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x), f v =
      ∑ v ∈ normLT x, f v :=
  finsum_cond_eq_sum_of_cond_iff f fun {_} _ => mem_normLT.symm

/-! ### Prime powers of bounded norm -/

/-- The set of pairs `(v, k)`, `k ≥ 1`, with `N(𝔭_v)^k ≤ N`, is finite. -/
lemma finite_pairs (N : ℕ) :
    {p : HeightOneSpectrum (𝓞 F) × ℕ |
      0 < p.2 ∧ ((absNorm p.1.asIdeal : ℕ) : ℝ) ^ p.2 ≤ (N : ℝ)}.Finite := by
  refine ((finite_lt (F := F) ((N : ℝ) + 1)).prod (Set.finite_le_nat N)).subset ?_
  rintro ⟨v, k⟩ ⟨hk, hle⟩
  simp only at hk hle
  have hle' : absNorm v.asIdeal ^ k ≤ N := by exact_mod_cast hle
  have h2 := two_le_absNorm v
  refine Set.mk_mem_prod ?_ ?_
  · have h3 : absNorm v.asIdeal ≤ absNorm v.asIdeal ^ k :=
      Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hk) _
    have h4 : absNorm v.asIdeal ≤ N := h3.trans hle'
    have h5 : ((absNorm v.asIdeal : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h4
    exact lt_of_le_of_lt h5 (lt_add_one _)
  · have h3 : k < 2 ^ k := Nat.lt_two_pow_self
    have h4 : 2 ^ k ≤ absNorm v.asIdeal ^ k := Nat.pow_le_pow_left h2 k
    exact (h3.le.trans h4).trans hle'

/-- The finite set of pairs `(v, k)`, `k ≥ 1`, with `N(𝔭_v)^k ≤ N`. -/
noncomputable def pairs (N : ℕ) : Finset (HeightOneSpectrum (𝓞 F) × ℕ) :=
  (finite_pairs (F := F) N).toFinset

lemma mem_pairs {N : ℕ} {p : HeightOneSpectrum (𝓞 F) × ℕ} :
    p ∈ pairs N ↔ 0 < p.2 ∧ ((absNorm p.1.asIdeal : ℕ) : ℝ) ^ p.2 ≤ (N : ℝ) := by
  unfold pairs
  rw [Set.Finite.mem_toFinset]
  rfl

lemma mem_pairs' {N : ℕ} {p : HeightOneSpectrum (𝓞 F) × ℕ} :
    p ∈ pairs N ↔ 0 < p.2 ∧ absNorm p.1.asIdeal ^ p.2 ≤ N := by
  rw [mem_pairs]
  refine and_congr Iff.rfl ?_
  norm_cast

lemma pairs_mono : Monotone (pairs (F := F)) := fun _ _ hMN _ hp =>
  mem_pairs'.2 ⟨(mem_pairs'.1 hp).1, (mem_pairs'.1 hp).2.trans hMN⟩

open Classical in
/-- `pairs N` enlarged by the pairs `(v, 0)` with `N(𝔭_v) ≤ N`, so as to exhaust all pairs. -/
noncomputable def pairs0 (N : ℕ) : Finset (HeightOneSpectrum (𝓞 F) × ℕ) :=
  pairs N ∪ (normLT ((N : ℝ) + 1)) ×ˢ ({0} : Finset ℕ)

lemma mem_pairs0 {N : ℕ} {p : HeightOneSpectrum (𝓞 F) × ℕ} :
    p ∈ pairs0 N ↔ p ∈ pairs N ∨ (absNorm p.1.asIdeal ≤ N ∧ p.2 = 0) := by
  classical
  unfold pairs0
  rw [Finset.mem_union, Finset.mem_product, mem_normLT, Finset.mem_singleton]
  refine or_congr Iff.rfl (and_congr ?_ Iff.rfl)
  rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, Nat.cast_lt, Nat.lt_succ_iff]

lemma tendsto_pairs0 : Tendsto (pairs0 (F := F)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun M N hMN p hp => ?_) fun p => ?_
  · rcases mem_pairs0.1 hp with h | h
    · exact mem_pairs0.2 (Or.inl (pairs_mono hMN h))
    · exact mem_pairs0.2 (Or.inr ⟨h.1.trans hMN, h.2⟩)
  · rcases Nat.eq_zero_or_pos p.2 with h | h
    · exact ⟨absNorm p.1.asIdeal, mem_pairs0.2 (Or.inr ⟨le_rfl, h⟩)⟩
    · exact ⟨absNorm p.1.asIdeal ^ p.2, mem_pairs0.2 (Or.inl (mem_pairs'.2 ⟨h, le_rfl⟩))⟩

/-! ### The Dirichlet polynomials -/

/-- The term `χ(𝔭)^k log N(𝔭) (N(𝔭)^k)^{-s}` of the Dirichlet series of `-L_f'/L_f`. -/
noncomputable def termL (χ : HeckeCharacter F) (s : ℂ) (p : HeightOneSpectrum (𝓞 F) × ℕ) : ℂ :=
  χ.primeValue p.1 ^ p.2 * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) : ℂ) *
    (primeNorm p.1 ^ p.2) ^ (-s)

/-- The term `χ(𝔭)^k / k · (N(𝔭)^k)^{-s}` of the Dirichlet series of `log L_f`. -/
noncomputable def termD (χ : HeckeCharacter F) (s : ℂ) (p : HeightOneSpectrum (𝓞 F) × ℕ) : ℂ :=
  χ.primeValue p.1 ^ p.2 / (p.2 : ℂ) * (primeNorm p.1 ^ p.2) ^ (-s)

/-- `T_N(s)`, the Dirichlet polynomial of `-L_f'/L_f`. -/
noncomputable def TT (χ : HeckeCharacter F) (s : ℂ) (N : ℕ) : ℂ := ∑ p ∈ pairs N, termL χ s p

/-- `D_N(s)`, the Dirichlet polynomial of `log L_f`. -/
noncomputable def DD (χ : HeckeCharacter F) (s : ℂ) (N : ℕ) : ℂ := ∑ p ∈ pairs N, termD χ s p

/-- The prime sum `∑_{N(𝔭) < N} χ(𝔭) N(𝔭)^{-s}`. -/
noncomputable def QQ (χ : HeckeCharacter F) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ v ∈ normLT (N : ℝ), χ.primeValue v * primeNorm v ^ (-s)

/-- The part of `termD` coming from the proper prime powers. -/
noncomputable def termR (χ : HeckeCharacter F) (p : HeightOneSpectrum (𝓞 F) × ℕ) (s : ℂ) : ℂ :=
  if 2 ≤ p.2 then termD χ s p else 0

lemma TT_eq_finsum (χ : HeckeCharacter F) (s : ℂ) (N : ℕ) :
    ∑ᶠ (p : HeightOneSpectrum (𝓞 F) × ℕ)
        (_ : 0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ (N : ℝ)),
        χ.primeValue p.1 ^ p.2 * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) : ℂ) *
          (primeNorm p.1 ^ p.2) ^ (-s) = TT χ s N :=
  finsum_cond_eq_sum_of_cond_iff _ fun {_} _ => mem_pairs.symm

lemma termD_eq (χ : HeckeCharacter F) (s : ℂ) (p : HeightOneSpectrum (𝓞 F) × ℕ) (hp : 0 < p.2) :
    termD χ s p = (wt (absNorm p.1.asIdeal ^ p.2) : ℂ) * termL χ s p := by
  unfold termD termL wt
  have h2 := two_le_natNorm p.1
  have hlog : Real.log ((absNorm p.1.asIdeal : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by linarith)).ne'
  have hk : (p.2 : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlogC : (Real.log ((absNorm p.1.asIdeal : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  have hkC : (p.2 : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Nat.cast_pow, Real.log_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  field_simp

lemma DD_step (χ : HeckeCharacter F) (s : ℂ) (n : ℕ) :
    DD χ s (n + 1) - DD χ s n = (wt (n + 1) : ℂ) * (TT χ s (n + 1) - TT χ s n) := by
  classical
  unfold DD TT
  have hsub : pairs (F := F) n ⊆ pairs (n + 1) := pairs_mono (Nat.le_succ n)
  rw [← Finset.sum_sdiff_eq_sub hsub, ← Finset.sum_sdiff_eq_sub hsub, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_sdiff, mem_pairs', mem_pairs'] at hp
  have hn : absNorm p.1.asIdeal ^ p.2 = n + 1 := by
    have h1 := hp.1.2
    have h2 : ¬ absNorm p.1.asIdeal ^ p.2 ≤ n := fun h => hp.2 ⟨hp.1.1, h⟩
    omega
  rw [termD_eq χ s p hp.1.1, hn]

lemma norm_cpow_line (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {s : ℂ} (hs : s.re = 1) :
    ‖(primeNorm v ^ k) ^ (-s)‖ = (((absNorm v.asIdeal : ℕ) : ℝ) ^ k)⁻¹ := by
  unfold primeNorm
  have hpos : 0 < absNorm v.asIdeal ^ k := pow_pos (by have := two_le_absNorm v; omega) k
  rw [← Nat.cast_pow, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re, hs,
    Real.rpow_neg_one, Nat.cast_pow]

/-- The majorant `N(𝔭)^{-2} · 4 · 2^{-k}` of the proper prime power terms. -/
noncomputable def maj (p : HeightOneSpectrum (𝓞 F) × ℕ) : ℝ :=
  ((absNorm p.1.asIdeal : ℕ) : ℝ) ^ (-2 : ℝ) * (4 * (1 / 2 : ℝ) ^ p.2)

lemma summable_maj : Summable (maj (F := F)) := by
  unfold maj
  refine Summable.mul_of_nonneg (summable_two (F := F))
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4)
    (fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun k => by positivity)

lemma norm_termR_le (χ : HeckeCharacter F) (p : HeightOneSpectrum (𝓞 F) × ℕ) {s : ℂ}
    (hs : s.re = 1) : ‖termR χ p s‖ ≤ maj p := by
  unfold termR maj
  have h2 := two_le_natNorm p.1
  have hq : (0 : ℝ) < ((absNorm p.1.asIdeal : ℕ) : ℝ) := by linarith
  split_ifs with hk
  · unfold termD
    rw [norm_mul, norm_div, norm_pow, norm_cpow_line p.1 p.2 hs, Complex.norm_natCast]
    have h1 : ‖χ.primeValue p.1‖ ^ p.2 / (p.2 : ℝ) ≤ 1 := by
      have hk1 : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast (by omega : 1 ≤ p.2)
      rw [div_le_one (by linarith)]
      exact (pow_le_one₀ (norm_nonneg _) (norm_primeValue_le χ p.1)).trans hk1
    have h3 : (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ p.2)⁻¹ ≤
        ((absNorm p.1.asIdeal : ℕ) : ℝ) ^ (-2 : ℝ) * (4 * (1 / 2 : ℝ) ^ p.2) := by
      obtain ⟨j, hj⟩ : ∃ j, p.2 = 2 + j := ⟨p.2 - 2, by omega⟩
      rw [hj, Real.rpow_neg hq.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        pow_add, pow_add, mul_inv]
      have h4 : (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ j)⁻¹ ≤ (1 / 2 : ℝ) ^ j := by
        rw [one_div, inv_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h2 j)
      have h5 : (0 : ℝ) ≤ (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
      calc (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ * (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ j)⁻¹
          ≤ (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ * (1 / 2 : ℝ) ^ j :=
            mul_le_mul_of_nonneg_left h4 h5
        _ = (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ * (4 * ((1 / 2 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j)) := by
            ring
    calc ‖χ.primeValue p.1‖ ^ p.2 / (p.2 : ℝ) * (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ p.2)⁻¹
        ≤ 1 * (((absNorm p.1.asIdeal : ℕ) : ℝ) ^ p.2)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := by rw [one_mul]; exact h3
  · rw [norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hq.le _) (by positivity)

/-- The proper prime power part of `D_N`. -/
noncomputable def RR (χ : HeckeCharacter F) (s : ℂ) (N : ℕ) : ℂ := ∑ p ∈ pairs N, termR χ p s

lemma RR_eq (χ : HeckeCharacter F) (s : ℂ) (N : ℕ) : RR χ s N = ∑ p ∈ pairs0 N, termR χ p s := by
  unfold RR
  refine Finset.sum_subset (fun p hp => mem_pairs0.2 (Or.inl hp)) fun p hp hnp => ?_
  rcases mem_pairs0.1 hp with h | h
  · exact absurd h hnp
  · unfold termR
    rw [if_neg (by omega)]

lemma tendstoUniformlyOn_RR (χ : HeckeCharacter F) :
    TendstoUniformlyOn (fun N s => RR χ s N) (fun s => ∑' p, termR χ p s) atTop
      {s : ℂ | s.re = 1} := by
  have h := tendstoUniformlyOn_tsum (f := fun p s => termR χ p s) (summable_maj (F := F))
    (s := {s : ℂ | s.re = 1}) (fun p s hs => norm_termR_le χ p hs)
  intro u hu
  filter_upwards [tendsto_pairs0.eventually (h u hu)] with N hN s hs
  rw [RR_eq]
  exact hN s hs

/-- `D_N = (prime sum up to N) + (proper prime powers up to N)`. -/
lemma DD_eq (χ : HeckeCharacter F) (s : ℂ) (N : ℕ) :
    DD χ s N = QQ χ s (N + 1) + RR χ s N := by
  classical
  unfold DD RR QQ
  rw [← Finset.sum_filter_add_sum_filter_not (pairs N) (fun p => p.2 = 1)]
  congr 1
  · refine Finset.sum_nbij' (fun p => p.1) (fun v => (v, 1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, mem_pairs'] at hp
      rw [mem_normLT]
      have := hp.1.2
      rw [hp.2, pow_one] at this
      exact_mod_cast Nat.lt_succ_of_le this
    · intro v hv
      rw [mem_normLT] at hv
      rw [Finset.mem_filter, mem_pairs']
      have hv' : absNorm v.asIdeal < N + 1 := by exact_mod_cast hv
      refine ⟨⟨one_pos, ?_⟩, rfl⟩
      show absNorm v.asIdeal ^ 1 ≤ N
      rw [pow_one]
      omega
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Prod.ext rfl hp.2.symm
    · intro v _
      rfl
    · intro p hp
      rw [Finset.mem_filter] at hp
      unfold termD
      rw [hp.2]
      simp
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [mem_pairs'] at hp
    unfold termR
    by_cases h1 : p.2 = 1
    · rw [if_neg (by simpa using h1), if_neg (by omega)]
    · rw [if_pos (by simpa using h1), if_pos (by omega)]

/-! ### Uniform Cauchy property of the prime sums -/

/-- If the `T_N` have bounded oscillation on a subset `U` of the 1-line, then the prime sums are
uniformly Cauchy on `U`. -/
theorem ucs_of_bdd (χ : HeckeCharacter F) (U : Set ℂ) (hU : ∀ s ∈ U, s.re = 1) (N₀ : ℕ) (K : ℝ)
    (h : ∀ n, N₀ ≤ n → ∀ s ∈ U, ‖TT χ s n - TT χ s N₀‖ ≤ K) :
    UniformCauchySeqOn (fun N s => QQ χ s (N + 1)) atTop U := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hR := (tendstoUniformlyOn_RR χ).uniformCauchySeqOn
  rw [Metric.uniformCauchySeqOn_iff] at hR
  obtain ⟨N₁, hN₁⟩ := hR (ε / 2) (by linarith)
  have hw : ∀ᶠ n in atTop, (2 * K + 1) * wt n < ε / 4 := by
    have h0 := wt_tendsto.const_mul (2 * K + 1)
    rw [mul_zero] at h0
    exact h0.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hw
  set M := max (max N₀ N₁) (max N₂ 2) with hMdef
  have hM0 : N₀ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM1 : N₁ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM2 : N₂ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM3 : 2 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨M, fun m hm n hn s hs => ?_⟩
  have hs1 : s.re = 1 := hU s hs
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (h N₀ le_rfl s hs)
  have key : ∀ m, M ≤ m → ‖DD χ s m - DD χ s M‖ ≤ 2 * K * wt M := by
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    refine abel_bound (fun N => DD χ s N) (fun N => TT χ s N) wt (fun n => DD_step χ s n) M
      (2 * K) (fun n hn => wt_anti n (hM3.trans hn)) (fun n _ => wt_nonneg n) (fun n hn => ?_) k
    have h1 := h n (hM0.trans hn) s hs
    have h2 := h M hM0 s hs
    calc ‖TT χ s n - TT χ s M‖ = ‖(TT χ s n - TT χ s N₀) - (TT χ s M - TT χ s N₀)‖ := by
          congr 1; ring
      _ ≤ ‖TT χ s n - TT χ s N₀‖ + ‖TT χ s M - TT χ s N₀‖ := norm_sub_le _ _
      _ ≤ 2 * K := by linarith
  have hwM : 2 * K * wt M < ε / 4 := by
    have h3 := hN₂ M hM2
    have h4 := wt_nonneg M
    nlinarith
  have hRmn : ‖RR χ s m - RR χ s n‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hN₁ m (hM1.trans hm) n (hM1.trans hn) s hs1
  have e1 : QQ χ s (m + 1) = DD χ s m - RR χ s m := by rw [DD_eq]; ring
  have e2 : QQ χ s (n + 1) = DD χ s n - RR χ s n := by rw [DD_eq]; ring
  rw [dist_eq_norm, e1, e2]
  calc ‖DD χ s m - RR χ s m - (DD χ s n - RR χ s n)‖
      = ‖(DD χ s m - DD χ s M) - (DD χ s n - DD χ s M) - (RR χ s m - RR χ s n)‖ := by
        congr 1; ring
    _ ≤ ‖DD χ s m - DD χ s M‖ + ‖DD χ s n - DD χ s M‖ + ‖RR χ s m - RR χ s n‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ < ε := by
        have := key m hm
        have := key n hn
        linarith

/-- Bounded oscillation of the `T_N` near every point of `S` gives locally uniform convergence of
the prime sums on `S`. -/
theorem exists_limit (χ : HeckeCharacter F) (S : Set ℂ)
    (H : ∀ s₀ ∈ S, ∃ U ∈ 𝓝[S] s₀, (∀ s ∈ U, s.re = 1) ∧
      ∃ (N₀ : ℕ) (K : ℝ), ∀ n, N₀ ≤ n → ∀ s ∈ U, ‖TT χ s n - TT χ s N₀‖ ≤ K) :
    ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) =>
        ∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
          χ.primeValue v * primeNorm v ^ (-s)) g atTop S := by
  refine ⟨fun s => limUnder atTop (fun N : ℕ => QQ χ s (N + 1)), ?_⟩
  intro u hu s₀ hs₀
  obtain ⟨U, hU, hU1, N₀, K, hK⟩ := H s₀ hs₀
  refine ⟨U, hU, ?_⟩
  have hc := ucs_of_bdd χ U hU1 N₀ K hK
  have ht : TendstoUniformlyOn (fun N s => QQ χ s (N + 1))
      (fun s => limUnder atTop (fun N : ℕ => QQ χ s (N + 1))) atTop U :=
    hc.tendstoUniformlyOn_of_tendsto fun s hs => CauchySeq.tendsto_limUnder (hc.cauchy_map hs)
  have hceil : Tendsto (fun x : ℝ => ⌈x⌉₊ - 1) atTop atTop :=
    tendsto_atTop.2 fun n => (eventually_ge_atTop ((n + 1 : ℕ) : ℝ)).mono fun x hx => by
      have h1 : n + 1 ≤ ⌈x⌉₊ := Nat.cast_le.1 (hx.trans (Nat.le_ceil x))
      omega
  filter_upwards [hceil.eventually (ht u hu), eventually_gt_atTop (0 : ℝ)] with x hx hx0 s hs
  have e : (∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
      χ.primeValue v * primeNorm v ^ (-s)) = QQ χ s (⌈x⌉₊ - 1 + 1) := by
    rw [finsum_eq]
    unfold QQ
    rw [Nat.sub_add_cancel (Nat.ceil_pos.2 hx0)]
    refine Finset.sum_congr (Finset.ext fun v => ?_) fun _ _ => rfl
    rw [mem_normLT, mem_normLT, Nat.cast_lt, Nat.lt_ceil]
  have h3 := hx s hs
  rw [← e] at h3
  exact h3

end hecke

end MasulloGRH.PS

open MasulloGRH MasulloGRH.PS NumberField IsDedekindDomain Filter Topology in
theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (¬ χ.IsTrivialOnNormOne → ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) => ∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        χ.primeValue v * primeNorm v ^ (-s))
      g Filter.atTop {s : ℂ | s.re = 1}) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ → ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) => ∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        χ.primeValue v * primeNorm v ^ (-s))
      g Filter.atTop {s : ℂ | s.re = 1 ∧ s.im ≠ t₀}) := by
  obtain ⟨h2, h1⟩ := MasulloGRH.vonMangoldt_sums_on_one_line F χ
  refine ⟨fun hχ => ?_, fun t₀ ht₀ => ?_⟩
  · refine exists_limit χ _ fun s₀ hs₀ => ?_
    obtain ⟨t, ht, hev⟩ := h2 hχ _ (Metric.dist_mem_uniformity one_pos) s₀ hs₀
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
    refine ⟨t ∩ {s : ℂ | s.re = 1}, inter_mem ht self_mem_nhdsWithin, fun s hs => hs.2,
      ⌈x₀⌉₊, 2, fun n hn s hs => ?_⟩
    have a1 : dist (-(deriv (heckeLFunction χ) s / heckeLFunction χ s)) (TT χ s n) < 1 := by
      rw [← TT_eq_finsum]
      exact hx₀ n ((Nat.le_ceil x₀).trans (Nat.cast_le.2 hn)) s hs.1
    have a2 : dist (-(deriv (heckeLFunction χ) s / heckeLFunction χ s)) (TT χ s ⌈x₀⌉₊) < 1 := by
      rw [← TT_eq_finsum]
      exact hx₀ (⌈x₀⌉₊ : ℕ) (Nat.le_ceil x₀) s hs.1
    rw [← dist_eq_norm]
    exact ((dist_triangle_left _ _ _).trans (add_le_add a1.le a2.le)).trans (by norm_num)
  · refine exists_limit χ _ fun s₀ hs₀ => ?_
    obtain ⟨t, ht, hev⟩ := h1 t₀ ht₀ _ (Metric.dist_mem_uniformity one_pos) s₀ hs₀
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
    have hc0 : (1 + t₀ * Complex.I - s₀) ≠ 0 := by
      intro h
      apply hs₀.2
      have h' := congrArg Complex.im h
      simp at h'
      linarith
    have hδ : 0 < ‖1 + t₀ * Complex.I - s₀‖ / 2 := half_pos (norm_pos_iff.2 hc0)
    have hV : {s : ℂ | ‖1 + t₀ * Complex.I - s₀‖ / 2 < ‖1 + t₀ * Complex.I - s‖} ∈ 𝓝 s₀ :=
      (isOpen_lt continuous_const (by fun_prop)).mem_nhds
        (show ‖1 + t₀ * Complex.I - s₀‖ / 2 < ‖1 + t₀ * Complex.I - s₀‖ from
          half_lt_self (norm_pos_iff.2 hc0))
    refine ⟨(t ∩ {s : ℂ | ‖1 + t₀ * Complex.I - s₀‖ / 2 < ‖1 + t₀ * Complex.I - s‖}) ∩
        {s : ℂ | s.re = 1 ∧ s.im ≠ t₀},
      inter_mem (inter_mem ht (mem_nhdsWithin_of_mem_nhds hV)) self_mem_nhdsWithin,
      fun s hs => hs.2.1, max ⌈x₀⌉₊ 1,
      2 + 2 * (1 / (‖1 + t₀ * Complex.I - s₀‖ / 2)), fun n hn s hs => ?_⟩
    have hn0 : ⌈x₀⌉₊ ≤ n := (le_max_left _ _).trans hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have a1 : dist (-(deriv (heckeLFunction χ) s / heckeLFunction χ s))
        (TT χ s n - ((n : ℝ) : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s)) < 1 := by
      rw [← TT_eq_finsum]
      exact hx₀ n ((Nat.le_ceil x₀).trans (Nat.cast_le.2 hn0)) s hs.1.1
    have a2 : dist (-(deriv (heckeLFunction χ) s / heckeLFunction χ s))
        (TT χ s (max ⌈x₀⌉₊ 1) - (((max ⌈x₀⌉₊ 1 : ℕ) : ℝ) : ℂ) ^ (1 + t₀ * Complex.I - s) /
          (1 + t₀ * Complex.I - s)) < 1 := by
      rw [← TT_eq_finsum]
      exact hx₀ ((max ⌈x₀⌉₊ 1 : ℕ) : ℝ)
        ((Nat.le_ceil x₀).trans (Nat.cast_le.2 (le_max_left _ _))) s hs.1.1
    have hG : ∀ m : ℕ, 1 ≤ m →
        ‖((m : ℝ) : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s)‖ ≤
          1 / (‖1 + t₀ * Complex.I - s₀‖ / 2) := by
      intro m hm
      have hre : (1 + t₀ * Complex.I - s).re = 0 := by simp [hs.2.1]
      rw [norm_div, Complex.ofReal_natCast, Complex.norm_natCast_cpow_of_pos (by omega), hre,
        Real.rpow_zero]
      exact one_div_le_one_div_of_le hδ hs.1.2.le
    have b1 := hG n hn1
    have b2 := hG (max ⌈x₀⌉₊ 1) (le_max_right _ _)
    have b3 := (dist_triangle_left _ _ _).trans (add_le_add a1.le a2.le)
    rw [dist_eq_norm] at b3
    calc ‖TT χ s n - TT χ s (max ⌈x₀⌉₊ 1)‖
        = ‖(TT χ s n - ((n : ℝ) : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s) -
            (TT χ s (max ⌈x₀⌉₊ 1) - (((max ⌈x₀⌉₊ 1 : ℕ) : ℝ) : ℂ) ^ (1 + t₀ * Complex.I - s) /
              (1 + t₀ * Complex.I - s))) +
            (((n : ℝ) : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s) -
              (((max ⌈x₀⌉₊ 1 : ℕ) : ℝ) : ℂ) ^ (1 + t₀ * Complex.I - s) /
                (1 + t₀ * Complex.I - s))‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add b3 (norm_sub_le _ _))
      _ ≤ _ := by linarith

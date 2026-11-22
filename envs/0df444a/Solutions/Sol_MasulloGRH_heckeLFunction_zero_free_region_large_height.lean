-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_zero_free_region_large_height
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T15:28:58.340697+00:00
-- url     : https://prove2.me/submissions/579374a0-3068-4108-9e0c-9003412df7f1

import Definitions.Def_MasulloGRH_HeckeLFunction
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_heckeLFunction_polynomial_growth_on_vertical_strips
import Theorems.Thm_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
set_option linter.all false
set_option autoImplicit false

-- ===== from A1.lean =====

namespace MasulloGRH
namespace Aux_HL
open Filter Topology

/-! ### Abstract Euler product over finitely supported exponent vectors -/

section abstract
variable {ι : Type*}

/-- the monomial `∏ z_v ^ k_v`. -/
noncomputable def mono (z : ι → ℂ) (k : ι →₀ ℕ) : ℂ := k.prod fun v n => z v ^ n

lemma mono_single_add (z : ι → ℂ) (a : ι) (n : ℕ) (k : ι →₀ ℕ) :
    mono z (Finsupp.single a n + k) = z a ^ n * mono z k := by
  classical
  unfold mono
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp [Finsupp.prod_single_index]

lemma norm_mono (z : ι → ℂ) (k : ι →₀ ℕ) : ‖mono z k‖ = mono (fun v => (‖z v‖ : ℂ)) k := by
  classical
  unfold mono Finsupp.prod
  rw [norm_prod]
  push_cast
  simp [norm_pow]

lemma norm_mono' (z : ι → ℂ) (k : ι →₀ ℕ) :
    ‖mono z k‖ = k.prod fun v n => ‖z v‖ ^ n := by
  classical
  unfold mono Finsupp.prod
  rw [norm_prod]
  simp [norm_pow]

/-- the equivalence `ℕ × S_T ≃ S_{insert a T}`. -/
noncomputable def insEquiv [DecidableEq ι] (T : Finset ι) (a : ι) (ha : a ∉ T) :
    ℕ × {k : ι →₀ ℕ // k.support ⊆ T} ≃ {k : ι →₀ ℕ // k.support ⊆ insert a T} where
  toFun p := ⟨Finsupp.single a p.1 + p.2.1, by
    intro x hx
    have := Finsupp.support_add hx
    rcases Finset.mem_union.1 this with h | h
    · exact Finset.mem_insert.2 (Or.inl (Finset.mem_singleton.1 (Finsupp.support_single_subset h)))
    · exact Finset.mem_insert_of_mem (p.2.2 h)⟩
  invFun k := (k.1 a, ⟨k.1.erase a, by
    intro x hx
    rw [Finsupp.support_erase] at hx
    have h1 := Finset.mem_erase.1 hx
    rcases Finset.mem_insert.1 (k.2 h1.2) with h | h
    · exact absurd h h1.1
    · exact h⟩)
  left_inv p := by
    obtain ⟨n, k, hk⟩ := p
    have hka : k a = 0 := by
      by_contra h
      exact ha (hk (Finsupp.mem_support_iff.2 h))
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, hka, add_zero, Prod.mk.injEq,
      true_and]
    apply Subtype.ext
    ext x
    by_cases hx : x = a
    · subst hx; simp [hka]
    · simp [Finsupp.erase_ne hx, Finsupp.single_apply, Ne.symm hx]
  right_inv k := by
    apply Subtype.ext
    exact Finsupp.single_add_erase a k.1

/-- finite Euler products. -/
theorem hasSum_finite (z : ι → ℂ) (hz : ∀ v, ‖z v‖ < 1) (T : Finset ι) :
    Summable (fun k : {k : ι →₀ ℕ // k.support ⊆ T} => ‖mono z k.1‖) ∧
    HasSum (fun k : {k : ι →₀ ℕ // k.support ⊆ T} => mono z k.1) (∏ v ∈ T, (1 - z v)⁻¹) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have hU : ∀ k : {k : ι →₀ ℕ // k.support ⊆ (∅ : Finset ι)}, k = ⟨0, by simp⟩ := by
      intro k; apply Subtype.ext; ext x
      by_contra h
      have := k.2 (Finsupp.mem_support_iff.2 h)
      simp at this
    haveI : Unique {k : ι →₀ ℕ // k.support ⊆ (∅ : Finset ι)} := ⟨⟨⟨0, by simp⟩⟩, hU⟩
    refine ⟨(hasSum_fintype _).summable, ?_⟩
    rw [Finset.prod_empty]
    convert hasSum_fintype (fun k : {k : ι →₀ ℕ // k.support ⊆ (∅ : Finset ι)} => mono z k.1)
    rw [Fintype.sum_unique]
    rw [hU default]
    simp [mono]
  | insert a T ha ih =>
    obtain ⟨hs, hh⟩ := ih
    have hg : HasSum (fun n : ℕ => z a ^ n) (1 - z a)⁻¹ := hasSum_geometric_of_norm_lt_one (hz a)
    have hgn : Summable (fun n : ℕ => ‖z a ^ n‖) := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hz a)
    have hprod := HasSum.mul (f := fun n : ℕ => z a ^ n)
      (g := fun k : {k : ι →₀ ℕ // k.support ⊆ T} => mono z k.1) hg hh
      (summable_mul_of_summable_norm (f := fun n : ℕ => z a ^ n)
        (g := fun k : {k : ι →₀ ℕ // k.support ⊆ T} => mono z k.1) hgn hs)
    have hsprod : Summable (fun p : ℕ × {k : ι →₀ ℕ // k.support ⊆ T} =>
        ‖z a ^ p.1‖ * ‖mono z p.2.1‖) :=
      Summable.mul_of_nonneg (f := fun n : ℕ => ‖z a ^ n‖)
        (g := fun k : {k : ι →₀ ℕ // k.support ⊆ T} => ‖mono z k.1‖) hgn hs
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    rw [Finset.prod_insert ha]
    constructor
    · rw [← (insEquiv T a ha).summable_iff]
      refine hsprod.congr fun p => ?_
      simp [insEquiv, mono_single_add, norm_mul]
    · rw [← (insEquiv T a ha).hasSum_iff]
      refine hprod.congr_fun fun p => ?_
      simp [insEquiv, mono_single_add]

lemma inv_one_sub_le_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hpos : 0 < 1 - x := by linarith
  rw [inv_le_comm₀ hpos (Real.exp_pos _), ← Real.exp_neg]
  have := Real.add_one_le_exp (-(2 * x))
  -- need exp(-2x) ≤ 1 - x  ... use convexity-free bound: exp(-2x) ≤ 1/(1+2x) ≤ 1 - x
  have h2 : Real.exp (-(2 * x)) ≤ (1 + 2 * x)⁻¹ := by
    rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (by linarith)]
    linarith [Real.add_one_le_exp (2 * x)]
  refine h2.trans ?_
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  nlinarith

/-- global summability of monomials. -/
theorem summable_mono (z : ι → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1 / 2) (hs : Summable fun v => ‖z v‖) :
    Summable fun k : ι →₀ ℕ => ‖mono z k‖ := by
  classical
  have hz1 : ∀ v, ‖z v‖ < 1 := fun v => (hz v).trans_lt (by norm_num)
  refine summable_of_sum_le (c := Real.exp (2 * ∑' v, ‖z v‖)) (fun _ => norm_nonneg _) ?_
  intro u
  set T : Finset ι := u.biUnion fun k => k.support
  obtain ⟨hsT, hT⟩ := hasSum_finite z hz1 T
  have hnT := (hasSum_finite (fun v => (‖z v‖ : ℂ)) (by simpa using hz1) T).2
  -- sum over u ≤ sum over S_T of norms = ∏ (1-‖z‖)⁻¹
  have hmem : ∀ k ∈ u, k.support ⊆ T := fun k hk => Finset.subset_biUnion_of_mem _ hk
  let u' : Finset {k : ι →₀ ℕ // k.support ⊆ T} :=
    u.attach.map ⟨fun k => ⟨k.1, hmem k.1 k.2⟩, fun a b h => by
      simp only [Subtype.mk.injEq] at h; exact Subtype.ext h⟩
  have h1 : ∑ x ∈ u, ‖mono z x‖ = ∑ x ∈ u', ‖mono z x.1‖ := by
    simp [u', Finset.sum_map]
    exact (Finset.sum_attach u (fun x => ‖mono z x‖)).symm
  rw [h1]
  refine (hsT.sum_le_tsum u' (fun _ _ => norm_nonneg _)).trans ?_
  have hval : ∑' k : {k : ι →₀ ℕ // k.support ⊆ T}, ‖mono z k.1‖ =
      ∏ v ∈ T, (1 - ‖z v‖)⁻¹ := by
    have := hnT.tsum_eq
    have h2 : ∀ k : {k : ι →₀ ℕ // k.support ⊆ T}, mono (fun v => (‖z v‖ : ℂ)) k.1 =
        ((‖mono z k.1‖ : ℝ) : ℂ) := by
      intro k; rw [norm_mono]
    simp_rw [h2] at this
    rw [← Complex.ofReal_tsum] at this
    have h3 : ((∏ v ∈ T, (1 - ‖z v‖)⁻¹ : ℝ) : ℂ) = ∏ v ∈ T, (1 - (‖z v‖ : ℂ))⁻¹ := by
      push_cast; rfl
    rw [← h3] at this
    exact_mod_cast this
  rw [hval]
  calc ∏ v ∈ T, (1 - ‖z v‖)⁻¹ ≤ ∏ v ∈ T, Real.exp (2 * ‖z v‖) :=
        Finset.prod_le_prod (fun v _ => inv_nonneg.2 (by linarith [hz v]))
          (fun v _ => inv_one_sub_le_exp (norm_nonneg _) (hz v))
    _ = Real.exp (2 * ∑ v ∈ T, ‖z v‖) := by rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (2 * ∑' v, ‖z v‖) := by
        gcongr
        exact hs.sum_le_tsum T (fun _ _ => norm_nonneg _)

/-- the abstract Euler product. -/
theorem hasProd_euler (z : ι → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1 / 2) (hs : Summable fun v => ‖z v‖) :
    HasProd (fun v => (1 - z v)⁻¹) (∑' k : ι →₀ ℕ, mono z k) := by
  classical
  have hz1 : ∀ v, ‖z v‖ < 1 := fun v => (hz v).trans_lt (by norm_num)
  have hS := summable_mono z hz hs
  unfold HasProd
  have key : ∀ T : Finset ι, ∏ v ∈ T, (1 - z v)⁻¹ =
      ∑' k : ι →₀ ℕ, Set.indicator {k | k.support ⊆ T} (mono z) k := by
    intro T
    rw [← tsum_subtype]
    exact ((hasSum_finite z hz1 T).2.tsum_eq).symm
  simp_rw [key]
  refine tendsto_tsum_of_dominated_convergence hS (fun k => ?_) (Eventually.of_forall ?_)
  · apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop k.support] with T hT
    simp [Set.indicator, hT]
  · intro T k
    by_cases h : k.support ⊆ T <;> simp [Set.indicator, h]

end abstract

/-! ### Specialisation to the Hecke Euler product -/

section hecke
open NumberField IsDedekindDomain Ideal

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
  · haveI : Finite {I : Ideal (𝓞 F) // g I = n} := Ideal.finite_setOfPred_absNorm_eq n
    exact Summable.of_finite
  · refine hL.congr fun n => ?_
    haveI : Finite {I : Ideal (𝓞 F) // g I = n} := Ideal.finite_setOfPred_absNorm_eq n
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
    (fun a b h => HeightOneSpectrum.ext h)

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ absNorm v.asIdeal := by
  have h0 : absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem norm_primeValue_le (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    ‖χ.primeValue v‖ ≤ 1 := by
  unfold HeckeCharacter.primeValue
  split_ifs
  · unfold HeckeCharacter.localComponent
    rw [Circle.norm_coe]
  · simp

/-- the Euler variable `χ(𝔭_v) N(𝔭_v)^{-s}`. -/
noncomputable def zv (χ : HeckeCharacter F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  χ.primeValue v * ((absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)

theorem norm_zv_le (χ : HeckeCharacter F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖zv χ s v‖ ≤ ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
  unfold zv
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by have := two_le_absNorm v; omega)]
  simp only [Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (norm_primeValue_le χ v)

theorem norm_zv_le_half (χ : HeckeCharacter F) (s : ℂ) (hs : 1 ≤ s.re)
    (v : HeightOneSpectrum (𝓞 F)) : ‖zv χ s v‖ ≤ 1 / 2 := by
  refine (norm_zv_le χ s v).trans ?_
  have h2 : (2 : ℝ) ≤ ((absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm v
  calc ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) ≤ ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, one_div]
        exact inv_anti₀ (by norm_num) h2

theorem summable_zv (χ : HeckeCharacter F) (s : ℂ) (hs : 1 < s.re) :
    Summable fun v => ‖zv χ s v‖ :=
  (summable_placeNorm (F := F) s.re hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_zv_le χ s)

/-- **Euler product = sum over exponent vectors** for `Re s > 1`. -/
theorem euler_eq (χ : HeckeCharacter F) (s : ℂ) (hs : 1 < s.re) :
    heckeEulerProduct χ s = ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ, mono (zv χ s) k :=
  (hasProd_euler (zv χ s) (norm_zv_le_half χ s hs.le) (summable_zv χ s hs)).tprod_eq

theorem hasProd_eulerProduct (χ : HeckeCharacter F) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun v => (1 - zv χ s v)⁻¹) (heckeEulerProduct χ s) := by
  rw [euler_eq χ s hs]
  exact hasProd_euler (zv χ s) (norm_zv_le_half χ s hs.le) (summable_zv χ s hs)

theorem differentiable_zv (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    Differentiable ℂ fun s => zv χ s v := by
  intro s
  unfold zv
  have hq : ((absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have := two_le_absNorm v; exact_mod_cast (show absNorm v.asIdeal ≠ 0 by omega)
  exact ((differentiableAt_id.neg).const_cpow (Or.inl hq)).const_mul _

theorem differentiable_mono (χ : HeckeCharacter F) (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    Differentiable ℂ fun s => mono (zv χ s) k := by
  unfold mono Finsupp.prod
  exact Differentiable.fun_finset_prod (fun v _ => (differentiable_zv χ v).pow _)

/-- the Euler product is holomorphic on `Re s > 1`. -/
theorem differentiableOn_euler (χ : HeckeCharacter F) :
    DifferentiableOn ℂ (heckeEulerProduct χ) {s | 1 < s.re} := by
  intro s hs
  obtain ⟨a, ha1, has⟩ := exists_between (show (1 : ℝ) < s.re from hs)
  let U : Set ℂ := {w | a < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let za : HeightOneSpectrum (𝓞 F) → ℂ := fun v => (((absNorm v.asIdeal : ℕ) : ℝ) ^ (-a) : ℝ)
  have hza : ∀ v, ‖za v‖ ≤ 1 / 2 := by
    intro v
    have h2 : (2 : ℝ) ≤ ((absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm v
    simp only [za, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    calc ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-a) ≤ ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 1 / 2 := by
          rw [Real.rpow_neg_one, one_div]
          exact inv_anti₀ (by norm_num) h2
  have hzs : Summable fun v => ‖za v‖ := by
    refine (summable_placeNorm (F := F) a ha1).congr fun v => ?_
    simp [za, Complex.norm_real, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hD : DifferentiableOn ℂ (fun w => ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ, mono (zv χ w) k) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_mono za hza hzs)
      (fun k => (differentiable_mono χ k).differentiableOn) hU ?_
    intro k w hw
    rw [norm_mono', norm_mono']
    unfold Finsupp.prod
    refine Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _) (fun v _ => ?_)
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    refine (norm_zv_le χ w v).trans ?_
    simp only [za, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have h2 : (1 : ℝ) ≤ ((absNorm v.asIdeal : ℕ) : ℝ) := by
      have := two_le_absNorm v; exact_mod_cast (show 1 ≤ absNorm v.asIdeal by omega)
    exact Real.rpow_le_rpow_of_exponent_le h2 (by simp only [Set.mem_setOf_eq, U] at hw; linarith)
  have hmem : U ∈ 𝓝 s := hU.mem_nhds has
  have heq : heckeEulerProduct χ =ᶠ[𝓝 s]
      (fun w => ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ, mono (zv χ w) k) := by
    filter_upwards [hmem] with w hw
    exact euler_eq χ w (ha1.trans hw)
  exact ((hD.differentiableAt hmem).congr_of_eventuallyEq heq).differentiableWithinAt

open Classical in
/-- separating finitely many Euler factors. -/
theorem euler_split (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ)
    (hs : 1 < s.re) :
    heckeEulerProduct χ s = (∏ v ∈ S, (1 - zv χ s v)⁻¹) *
      ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ, mono (fun v => if v ∈ S then 0 else zv χ s v) k := by
  classical
  let z' : HeightOneSpectrum (𝓞 F) → ℂ := fun v => if v ∈ S then 0 else zv χ s v
  have hle : ∀ v, ‖z' v‖ ≤ ‖zv χ s v‖ := by
    intro v; by_cases h : v ∈ S <;> simp [z', h]
  have h1 := hasProd_euler z' (fun v => (hle v).trans (norm_zv_le_half χ s hs.le v))
    ((summable_zv χ s hs).of_nonneg_of_le (fun _ => norm_nonneg _) hle)
  have h2 : HasProd (fun v => if v ∈ S then (1 - zv χ s v)⁻¹ else 1)
      (∏ v ∈ S, if v ∈ S then (1 - zv χ s v)⁻¹ else 1) :=
    hasProd_prod_of_ne_finset_one fun v hv => by simp [hv]
  have h3 := h2.mul h1
  have h4 : (fun v => (if v ∈ S then (1 - zv χ s v)⁻¹ else 1) * (1 - z' v)⁻¹) =
      fun v => (1 - zv χ s v)⁻¹ := by
    funext v; by_cases h : v ∈ S <;> simp [z', h]
  rw [h4] at h3
  rw [(hasProd_eulerProduct χ s hs).unique h3, Finset.prod_congr rfl fun v hv => if_pos hv]

end hecke

/-! ### Final assembly: from a meromorphic function agreeing near `Re s > 1` -/

end Aux_HL
end MasulloGRH

-- ===== from D1.lean =====

namespace MasulloGRH
namespace Aux_HL
open Filter Topology NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

/-! ### Exponent vectors ↔ nonzero integral ideals -/

/-- the ideal `∏ 𝔭_v ^ k_v`. -/
noncomputable def idealOf (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) : Ideal (𝓞 F) :=
  k.prod fun v n => v.asIdeal ^ n

/-- the exponent `v_𝔭(I)`. -/
noncomputable def expo (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

theorem count_idealOf (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v ((idealOf k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = k v := by
  have h1 : ((idealOf k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      (k.mapRange (fun n : ℕ => (n : ℤ)) (by simp)).prod
        (fun w (n : ℤ) => (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ n) := by
    unfold idealOf
    rw [show ((k.prod fun v n => v.asIdeal ^ n : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.coeIdealHom (𝓞 F)⁰ F (k.prod fun v n => v.asIdeal ^ n) from rfl,
      map_finsuppProd, Finsupp.prod_mapRange_index (by simp)]
    unfold Finsupp.prod
    refine Finset.prod_congr rfl fun w _ => ?_
    show (FractionalIdeal.coeIdealHom (𝓞 F)⁰ F) (w.asIdeal ^ k w) =
      (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ ((k w : ℕ) : ℤ)
    rw [map_pow, zpow_natCast]; rfl
  rw [h1, FractionalIdeal.count_finsuppProd]
  simp

theorem idealOf_injective : Function.Injective (idealOf (F := F)) := by
  intro k k' h
  ext v
  have := count_idealOf k v
  rw [h, count_idealOf] at this
  exact_mod_cast this.symm

theorem idealOf_ne_zero (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) : idealOf k ≠ 0 := by
  unfold idealOf Finsupp.prod
  rw [Finset.prod_ne_zero_iff]
  intro v _
  exact pow_ne_zero _ v.ne_bot

/-- the exponent vector of a nonzero ideal. -/
noncomputable def expoVec (I : Ideal (𝓞 F)) (hI : I ≠ 0) : HeightOneSpectrum (𝓞 F) →₀ ℕ :=
  Finsupp.ofSupportFinite (expo I) (by
    have := Associates.finite_factors hI
    refine (Filter.eventually_cofinite.1 this).subset fun v hv => ?_
    simp only [Function.mem_support, ne_eq] at hv
    simp only [Set.mem_setOf_eq]
    unfold expo at hv
    exact_mod_cast hv)

theorem expoVec_apply (I : Ideal (𝓞 F)) (hI : I ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    expoVec I hI v = expo I v := rfl

theorem idealOf_expoVec (I : Ideal (𝓞 F)) (hI : I ≠ 0) : idealOf (expoVec I hI) = I := by
  classical
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  unfold idealOf
  rw [Finsupp.prod, finprod_eq_prod_of_mulSupport_subset]
  · rfl
  · intro v hv
    simp only [Function.mem_mulSupport, ne_eq] at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, expoVec_apply]
    intro h0
    apply hv
    unfold HeightOneSpectrum.maxPowDividing
    unfold expo at h0
    rw [h0, pow_zero]

theorem absNorm_idealOf (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    Ideal.absNorm (idealOf k) = k.prod fun v n => Ideal.absNorm v.asIdeal ^ n := by
  unfold idealOf
  rw [map_finsuppProd]
  simp [map_pow]

/-- valuations of integers are given by the exponent vector of the principal ideal. -/
theorem valuation_eq_expo (α : 𝓞 F) (hα : α ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v.valuation F (α : F) = WithZero.exp (-(expo (Ideal.span {α}) v : ℤ)) := by
  rw [show (α : F) = algebraMap (𝓞 F) F α from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ hα]
  rfl

end Aux_HL
end MasulloGRH


namespace MasulloGRH
namespace Aux_HL
open NumberField IsDedekindDomain
variable {F : Type*} [Field F] [NumberField F]

/-- `n ↦ n^{-s}` as a monoid homomorphism. -/
noncomputable def cpowHom (s : ℂ) : ℕ →* ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_one' := by simp
  map_mul' a b := by push_cast; exact Complex.natCast_mul_natCast_cpow a b (-s)

/-- the ideal character of an exponent vector. -/
noncomputable def chiIdeal (χ : HeckeCharacter F) (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) : ℂ :=
  k.prod fun v n => χ.primeValue v ^ n

theorem mono_zv_eq (χ : HeckeCharacter F) (s : ℂ) (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    mono (zv χ s) k = chiIdeal χ k * ((Ideal.absNorm (idealOf k) : ℕ) : ℂ) ^ (-s) := by
  have h : ((Ideal.absNorm (idealOf k) : ℕ) : ℂ) ^ (-s) = cpowHom s (Ideal.absNorm (idealOf k)) := rfl
  rw [h, absNorm_idealOf, map_finsuppProd]
  unfold mono chiIdeal zv
  rw [← Finsupp.prod_mul]
  unfold Finsupp.prod
  refine Finset.prod_congr rfl fun v _ => ?_
  show (χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ k v =
    χ.primeValue v ^ k v * cpowHom s (Ideal.absNorm v.asIdeal ^ k v)
  rw [map_pow, mul_pow]
  rfl

end Aux_HL
end MasulloGRH

-- ===== MQ: uniqueness, 3-4-1, non-vanishing on the 1-line =====

namespace MasulloGRH
namespace Aux_MQ
open Filter Topology NumberField IsDedekindDomain Complex
open MasulloGRH.Aux_HL

variable {F : Type*} [Field F] [NumberField F]

/-- **Uniqueness**: two meromorphic functions in normal form on `ℂ` that agree on `Re s > 1`
coincide. -/
theorem eq_of_mnf {f g : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ)
    (hg : MeromorphicNFOn g Set.univ) (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  set S : Set ℂ := {x | ∀ᶠ y in 𝓝[≠] x, f y = g y} with hSdef
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhdsWithin
  have hSc : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx' : ¬ ∃ᶠ y in 𝓝[≠] x, f y = g y := fun hfr =>
      hx (((hf (Set.mem_univ x)).meromorphicAt.frequently_eq_iff_eventuallyEq
        (hg (Set.mem_univ x)).meromorphicAt).1 hfr)
    rw [Filter.not_frequently, eventually_nhdsWithin_iff] at hx'
    filter_upwards [hx'.eventually_nhds] with y hy
    by_cases hyx : y = x
    · rw [hyx]; exact hx
    · intro hyS
      have h1 : ∀ᶠ z in 𝓝 y, z ≠ x := isOpen_ne.mem_nhds hyx
      have h2 : ∀ᶠ z in 𝓝[≠] y, f z ≠ g z :=
        nhdsWithin_le_nhds ((hy.and h1).mono fun z hz => hz.1 hz.2)
      obtain ⟨z, hz1, hz2⟩ := (h2.and hyS).exists
      exact hz1 hz2
  have h2 : (2 : ℂ) ∈ S := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hm : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := hopen.mem_nhds (by norm_num)
    exact nhdsWithin_le_nhds (Filter.mem_of_superset hm fun s hs => h s hs)
  have hS : S = Set.univ := IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨2, h2⟩
  funext x
  have hx : x ∈ S := hS ▸ Set.mem_univ x
  exact (((hf (Set.mem_univ x)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hg (Set.mem_univ x))).1 hx).eq_of_nhds

theorem heckeL_spec (χ : HeckeCharacter F)
    (hex : ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct χ s) :
    MeromorphicNFOn (heckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → heckeLFunction χ s = heckeEulerProduct χ s := by
  unfold heckeLFunction
  rw [dif_pos hex]
  exact hex.choose_spec

theorem exists_uniformizer (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hne : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v π
    rw [h, map_zero, hπ] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨Units.mk0 _ hne, ?_⟩
  unfold IsUniformizerAt
  simp only [Units.val_mk0]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]

/-! ### The 3-4-1 inequality for Euler factors -/

lemma re_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
      0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

lemma norm_one_sub_pos {a : ℂ} (ha : ‖a‖ < 1) : 0 < ‖1 - a‖ := by
  have : (1 : ℂ) - a ≠ 0 := by
    intro h
    have : a = 1 := (sub_eq_zero.1 h).symm
    rw [this, norm_one] at ha; exact lt_irrefl _ ha
  exact norm_pos_iff.2 this

lemma factor_ineq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖(1 : ℂ) - x‖ ^ 3 * ‖1 - x * w‖ ^ 4 * ‖1 - x * w ^ 2‖ ≤ 1 := by
  have h := re_log_comb_nonneg' hx0 hx1 hw
  simp only [neg_re, log_re] at h
  have n0 : ‖(x : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg hx0]; exact hx1
  have n1 : ‖(x : ℂ) * w‖ < 1 := by rw [norm_mul, hw, mul_one]; exact n0
  have n2 : ‖(x : ℂ) * w ^ 2‖ < 1 := by rw [norm_mul, norm_pow, hw, one_pow, mul_one]; exact n0
  have p0 := norm_one_sub_pos n0
  have p1 := norm_one_sub_pos n1
  have p2 := norm_one_sub_pos n2
  have hP : 0 < ‖(1 : ℂ) - x‖ ^ 3 * ‖1 - x * w‖ ^ 4 * ‖1 - x * w ^ 2‖ := by positivity
  have hlog : Real.log (‖(1 : ℂ) - x‖ ^ 3 * ‖1 - x * w‖ ^ 4 * ‖1 - x * w ^ 2‖) ≤ 0 := by
    rw [Real.log_mul (by positivity) p2.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    linarith
  calc _ = Real.exp (Real.log (‖(1 : ℂ) - x‖ ^ 3 * ‖1 - x * w‖ ^ 4 * ‖1 - x * w ^ 2‖)) :=
        (Real.exp_log hP).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.2 hlog
    _ = 1 := Real.exp_zero

lemma factor_ineq_ram {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 : ℂ) - x‖ ^ 3 * ‖1 - x * w‖ ≤ 1 := by
  have e0 : ‖(1 : ℂ) - x‖ = 1 - x := by
    rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring, Complex.norm_of_nonneg (by linarith)]
  have e1 : ‖1 - (x : ℂ) * w‖ ≤ 1 + x := by
    calc ‖1 - (x : ℂ) * w‖ ≤ ‖(1 : ℂ)‖ + ‖(x : ℂ) * w‖ := norm_sub_le _ _
      _ ≤ 1 + x := by
        rw [norm_one, norm_mul, Complex.norm_of_nonneg hx0]
        nlinarith [norm_nonneg w]
  rw [e0]
  have h3 : 0 ≤ (1 - x) ^ 3 := by have : 0 ≤ 1 - x := by linarith
                                  positivity
  calc (1 - x) ^ 3 * ‖1 - (x : ℂ) * w‖ ≤ (1 - x) ^ 3 * (1 + x) := by gcongr
    _ ≤ 1 := by nlinarith [sq_nonneg x, mul_nonneg hx0 hx0, mul_nonneg (mul_nonneg hx0 hx0) hx0]

lemma lc_mul (χ ψ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x : (v.adicCompletion F)ˣ) :
    (χ * ψ).localComponent v x = χ.localComponent v x * ψ.localComponent v x := by
  unfold HeckeCharacter.localComponent
  rfl

lemma primeValue_mul_self (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (h : χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x) :
    (χ * χ).primeValue v = χ.primeValue v ^ 2 ∧ ‖χ.primeValue v‖ = 1 := by
  have hu : (χ * χ).IsUnramifiedAt v := fun x hx => by
    rw [lc_mul, h.1 x hx, one_mul]
  unfold HeckeCharacter.primeValue
  rw [dif_pos ⟨hu, h.2⟩, dif_pos h, lc_mul, sq]
  refine ⟨rfl, ?_⟩
  unfold HeckeCharacter.localComponent
  exact Circle.norm_coe _

lemma primeValue_ram (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (h : ¬ (χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x)) :
    χ.primeValue v = 0 := by
  unfold HeckeCharacter.primeValue
  rw [dif_neg h]

lemma one_le_of_hasProd {ι : Type*} {f : ι → ℝ} {a : ℝ} (hf : HasProd f a) (h : ∀ i, 1 ≤ f i) :
    1 ≤ a :=
  ge_of_tendsto' hf fun s => Finset.prod_induction _ (fun x => 1 ≤ x)
    (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun i _ => h i)

lemma cpow_split (n : ℕ) (hn : 0 < n) (σ t : ℝ) :
    ((n : ℂ)) ^ (-((σ : ℂ) + t * I)) = ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [neg_add, Complex.cpow_add _ _ hn0, ← Complex.ofReal_neg,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

lemma norm_cpow_imag (n : ℕ) (hn : 0 < n) (t : ℝ) : ‖(n : ℂ) ^ (-((t : ℂ) * I))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- **3-4-1 inequality** for the Euler products, `σ > 1`. -/
theorem three_four_one (χ : HeckeCharacter F) (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖heckeEulerProduct (1 : HeckeCharacter F) σ‖ ^ 3 *
      ‖heckeEulerProduct χ (σ + t * I)‖ ^ 4 *
      ‖heckeEulerProduct (χ * χ) (σ + (2 * t : ℝ) * I)‖ := by
  have hre : ∀ u : ℝ, 1 < ((σ : ℂ) + u * I).re := fun u => by simpa using hσ
  have h0 := (hasProd_eulerProduct (1 : HeckeCharacter F) (σ : ℂ) (by simpa using hσ)).norm
  have h1 := (hasProd_eulerProduct χ ((σ : ℂ) + t * I) (hre t)).norm
  have h2 := (hasProd_eulerProduct (χ * χ) ((σ : ℂ) + (2 * t : ℝ) * I) (hre _)).norm
  have hP := (((h0.mul h0).mul h0).mul (((h1.mul h1).mul h1).mul h1)).mul h2
  refine le_of_le_of_eq (one_le_of_hasProd hP fun v => ?_) (by ring)
  -- the local inequality
  set n : ℕ := Ideal.absNorm v.asIdeal with hn
  have hn2 : 2 ≤ n := two_le_absNorm v
  have hnpos : 0 < n := by omega
  set x : ℝ := (n : ℝ) ^ (-σ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n))
    (by linarith)
  set w : ℂ := (n : ℂ) ^ (-((t : ℂ) * I)) with hw
  have hw1 : ‖w‖ = 1 := norm_cpow_imag n hnpos t
  have hw2 : (n : ℂ) ^ (-(((2 * t : ℝ) : ℂ) * I)) = w ^ 2 := by
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
    rw [hw, sq, ← Complex.cpow_add _ _ hn0]
    congr 1; push_cast; ring
  have z0 : zv (1 : HeckeCharacter F) (σ : ℂ) v = x * (1 : HeckeCharacter F).primeValue v := by
    unfold zv
    have := cpow_split n hnpos σ 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_zero, Complex.cpow_zero, mul_one] at this
    rw [← hn, this]; ring
  have z1 : zv χ ((σ : ℂ) + t * I) v = x * (χ.primeValue v * w) := by
    unfold zv; rw [← hn, cpow_split n hnpos σ t]; ring
  have z2 : zv (χ * χ) ((σ : ℂ) + (2 * t : ℝ) * I) v = x * ((χ * χ).primeValue v * w ^ 2) := by
    unfold zv; rw [← hn, cpow_split n hnpos σ (2 * t), hw2]; ring
  have hone : (1 : HeckeCharacter F).primeValue v = 1 := by
    have hu : (1 : HeckeCharacter F).IsUnramifiedAt v := fun y _ => by
      unfold HeckeCharacter.localComponent; rfl
    obtain ⟨y, hy⟩ := exists_uniformizer v
    unfold HeckeCharacter.primeValue
    rw [dif_pos ⟨hu, y, hy⟩]
    unfold HeckeCharacter.localComponent; rfl
  rw [z0, z1, z2, hone, mul_one]
  have key : ‖(1 : ℂ) - x‖ ^ 3 * ‖1 - x * (χ.primeValue v * w)‖ ^ 4 *
      ‖1 - x * ((χ * χ).primeValue v * w ^ 2)‖ ≤ 1 := by
    by_cases hc : χ.IsUnramifiedAt v ∧ ∃ y : (v.adicCompletion F)ˣ, IsUniformizerAt v y
    · obtain ⟨hsq, hn1⟩ := primeValue_mul_self χ v hc
      rw [hsq, ← mul_pow]
      exact factor_ineq hx0 hx1 (by rw [norm_mul, hn1, hw1, one_mul])
    · rw [primeValue_ram χ v hc, zero_mul, mul_zero, sub_zero, norm_one, one_pow, mul_one]
      refine factor_ineq_ram hx0 hx1 ?_
      rw [norm_mul, norm_pow, hw1, one_pow, mul_one]
      exact norm_primeValue_le _ v
  have p0 : 0 < ‖(1 : ℂ) - x‖ := norm_one_sub_pos (by rw [Complex.norm_of_nonneg hx0]; exact hx1)
  have p1 : 0 < ‖1 - (x : ℂ) * (χ.primeValue v * w)‖ := norm_one_sub_pos (by
    rw [norm_mul, norm_mul, hw1, mul_one, Complex.norm_of_nonneg hx0]
    exact lt_of_le_of_lt (mul_le_of_le_one_right hx0 (norm_primeValue_le χ v)) hx1)
  have p2 : 0 < ‖1 - (x : ℂ) * ((χ * χ).primeValue v * w ^ 2)‖ := norm_one_sub_pos (by
    rw [norm_mul, norm_mul, norm_pow, hw1, one_pow, mul_one, Complex.norm_of_nonneg hx0]
    exact lt_of_le_of_lt (mul_le_of_le_one_right hx0 (norm_primeValue_le _ v)) hx1)
  simp only [norm_inv]
  rw [show ∀ a b c : ℝ, a⁻¹ * a⁻¹ * a⁻¹ * (b⁻¹ * b⁻¹ * b⁻¹ * b⁻¹) * c⁻¹ =
    (a ^ 3 * b ^ 4 * c)⁻¹ from fun a b c => by ring]
  exact one_le_inv₀ (by positivity) |>.2 key

/-! ### The Dedekind-zeta bound near `s = 1` -/

theorem norm_euler_le (χ : HeckeCharacter F) (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    ‖heckeEulerProduct χ (σ + t * I)‖ ≤
      ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  rw [euler_eq χ _ hs]
  have hS := summable_mono (zv χ ((σ : ℂ) + t * I)) (norm_zv_le_half χ _ hs.le) (summable_zv χ _ hs)
  refine (norm_tsum_le_tsum_norm hS).trans ?_
  have hb : ∀ k : HeightOneSpectrum (𝓞 F) →₀ ℕ, ‖mono (zv χ ((σ : ℂ) + t * I)) k‖ ≤
      ((Ideal.absNorm (idealOf k) : ℕ) : ℝ) ^ (-σ) := by
    intro k
    rw [mono_zv_eq, norm_mul]
    have hpos : 0 < Ideal.absNorm (idealOf k) := Nat.pos_of_ne_zero (fun h =>
      idealOf_ne_zero k (Ideal.absNorm_eq_zero_iff.1 h))
    rw [Complex.norm_natCast_cpow_of_pos hpos]
    have hc : ‖chiIdeal χ k‖ ≤ 1 := by
      unfold chiIdeal Finsupp.prod
      rw [norm_prod]
      refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun v _ => ?_
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeValue_le χ v)
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hc
  have hsum := summable_idealNorm (F := F) σ hσ
  have hsum' : Summable fun k : HeightOneSpectrum (𝓞 F) →₀ ℕ =>
      ((Ideal.absNorm (idealOf k) : ℕ) : ℝ) ^ (-σ) := hsum.comp_injective idealOf_injective
  calc ∑' k, ‖mono (zv χ ((σ : ℂ) + t * I)) k‖
      ≤ ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ, ((Ideal.absNorm (idealOf k) : ℕ) : ℝ) ^ (-σ) :=
        hS.tsum_le_tsum hb hsum'
    _ ≤ _ := tsum_comp_le_tsum_of_inj hsum (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        idealOf_injective

theorem dedekindZeta_eq (σ : ℝ) (hσ : 1 < σ) :
    NumberField.dedekindZeta F σ =
      ((∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hsum := summable_idealNorm (F := F) σ hσ
  let g : Ideal (𝓞 F) → ℕ := fun I => Ideal.absNorm I
  have hs' : Summable fun c : (Σ n : ℕ, {x : Ideal (𝓞 F) // g x = n}) =>
      ((Ideal.absNorm ((Equiv.sigmaFiberEquiv g) c) : ℕ) : ℝ) ^ (-σ) :=
    (Equiv.sigmaFiberEquiv g).summable_iff.2 hsum
  rw [← (Equiv.sigmaFiberEquiv g).tsum_eq, hs'.tsum_sigma]
  have hfib : ∀ n : ℕ, ∑' c : {I : Ideal (𝓞 F) // g I = n},
      ((Ideal.absNorm ((Equiv.sigmaFiberEquiv g) ⟨n, c⟩) : ℕ) : ℝ) ^ (-σ) =
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-σ) := by
    intro n
    haveI : Finite {I : Ideal (𝓞 F) // g I = n} := Ideal.finite_setOfPred_absNorm_eq n
    have h1 : ∀ c : {I : Ideal (𝓞 F) // g I = n},
        ((Ideal.absNorm ((Equiv.sigmaFiberEquiv g) ⟨n, c⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := by
      intro c
      simp only [Equiv.sigmaFiberEquiv_apply]
      rw [show (Ideal.absNorm c.1 : ℕ) = n from c.2]
    simp_rw [h1]
    rw [tsum_const, nsmul_eq_mul]
  simp_rw [hfib]
  unfold NumberField.dedekindZeta LSeries
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    simp [Real.zero_rpow (show -σ ≠ 0 by linarith)]
  · rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ, Real.rpow_neg (Nat.cast_nonneg n)]
    push_cast
    rw [div_eq_mul_inv]

theorem zeta_bound : ∃ C : ℝ, ∀ᶠ σ in 𝓝[>] (1 : ℝ),
    ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) ≤ C / (σ - 1) := by
  have ht := (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  set R := ‖((NumberField.dedekindZeta_residue F : ℝ) : ℂ)‖
  refine ⟨R + 1, ?_⟩
  filter_upwards [ht.eventually_lt_const (lt_add_one R), self_mem_nhdsWithin] with σ h1 h2
  have h2' : (0 : ℝ) < σ - 1 := sub_pos.2 h2
  rw [dedekindZeta_eq σ h2] at h1
  have hnn : 0 ≤ ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) :=
    tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
    Complex.norm_of_nonneg (mul_nonneg h2'.le hnn)] at h1
  rw [le_div_iff₀ h2']
  linarith

end Aux_MQ
end MasulloGRH

-- ===== MQ: B.6.1.6 from polynomial growth on vertical strips =====

namespace MasulloGRH
namespace Aux_MQ
open Filter Topology NumberField IsDedekindDomain Complex Metric
open MasulloGRH.Aux_HL

variable {F : Type*} [Field F] [NumberField F]

/-- the growth hypothesis (B.1.1.2). -/
def Growth (F : Type*) [Field F] [NumberField F] : Prop :=
  ∀ (ψ : HeckeCharacter F) (a b : ℝ), a < b → ∃ M : ℝ, 0 < M ∧ ∃ C T : ℝ, ∀ s : ℂ,
    a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖heckeLFunction ψ s‖ ≤ C * |s.im| ^ M

/-- growth with a natural exponent, `C ≥ 0`, `T ≥ 1`. -/
theorem growth_nat (hgr : Growth F) (ψ : HeckeCharacter F) (a b : ℝ) (hab : a < b) :
    ∃ m : ℕ, ∃ C T : ℝ, 0 ≤ C ∧ 1 ≤ T ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
      ‖heckeLFunction ψ s‖ ≤ C * |s.im| ^ m := by
  obtain ⟨M, hM, C, T, h⟩ := hgr ψ a b hab
  refine ⟨⌈M⌉₊, max C 0, max T 1, le_max_right _ _, le_max_right _ _, fun s h1 h2 h3 => ?_⟩
  have hT : T ≤ |s.im| := (le_max_left _ _).trans h3
  have h1' : 1 ≤ |s.im| := (le_max_right _ _).trans h3
  calc ‖heckeLFunction ψ s‖ ≤ C * |s.im| ^ M := h s h1 h2 hT
    _ ≤ max C 0 * |s.im| ^ M := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * |s.im| ^ (⌈M⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1' (Nat.le_ceil M))
          (le_max_right _ _)
    _ = max C 0 * |s.im| ^ ⌈M⌉₊ := by rw [Real.rpow_natCast]

/-- a meromorphic function in normal form which is bounded near a point is analytic there. -/
theorem analyticAt_of_bdd {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicNFAt f x) {B : ℝ}
    (hB : ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ B) : AnalyticAt ℂ f x := by
  rw [← hf.meromorphicOrderAt_nonneg_iff_analyticAt]
  by_contra hneg
  push Not at hneg
  have ht := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  rw [← tendsto_norm_atTop_iff_cobounded] at ht
  obtain ⟨z, hz1, hz2⟩ := ((ht.eventually_gt_atTop B).and (hB.filter_mono nhdsWithin_le_nhds)).exists
  linarith

/-- pole control from growth. -/
theorem analytic_of_growth (hex : ∀ ψ : HeckeCharacter F, ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct ψ s)
    (hgr : Growth F) (ψ : HeckeCharacter F) (a b : ℝ) (hab : a < b) :
    ∃ T : ℝ, ∀ s : ℂ, a < s.re → s.re < b → T ≤ |s.im| →
      AnalyticAt ℂ (heckeLFunction ψ) s := by
  obtain ⟨m, C, T, hC, hT, h⟩ := growth_nat hgr ψ a b hab
  refine ⟨T + 1, fun s h1 h2 h3 => ?_⟩
  have hnf := (heckeL_spec ψ (hex ψ)).1 (Set.mem_univ s)
  refine analyticAt_of_bdd hnf (B := C * (|s.im| + 1) ^ m) ?_
  have hcim : Continuous fun z : ℂ => |z.im| := continuous_abs.comp Complex.continuous_im
  have e1 : ∀ᶠ z in 𝓝 s, a < z.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt h1
  have e2 : ∀ᶠ z in 𝓝 s, z.re < b :=
    Complex.continuous_re.continuousAt.eventually_lt continuousAt_const h2
  have e3 : ∀ᶠ z in 𝓝 s, T < |z.im| :=
    continuousAt_const.eventually_lt hcim.continuousAt (by linarith)
  have e4 : ∀ᶠ z in 𝓝 s, |z.im| < |s.im| + 1 :=
    hcim.continuousAt.eventually_lt continuousAt_const (by linarith)
  filter_upwards [e1, e2, e3, e4] with z z1 z2 z3 z4
  calc ‖heckeLFunction ψ z‖ ≤ C * |z.im| ^ m := h z z1.le z2.le z3.le
    _ ≤ C * (|s.im| + 1) ^ m := by gcongr

end Aux_MQ
end MasulloGRH



/-! Part 1 of the large-height zero-free region: the logarithmic derivative of the Euler
product as a sum over primes, and the 3-4-1 inequality for logarithmic derivatives. -/

namespace MasulloGRH.ZFRLarge

open Filter Topology NumberField IsDedekindDomain Complex Metric
open MasulloGRH.Aux_HL MasulloGRH.Aux_MQ

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary inequalities -/

lemma hasSum_geom_succ {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1)) (z / (1 - z)) := by
  have h := (hasSum_geometric_of_norm_lt_one hz).mul_left z
  rw [show (fun n : ℕ => z ^ (n + 1)) = fun n => z * z ^ n from funext fun n => pow_succ' z n,
    div_eq_mul_inv]
  exact h

lemma re_sq_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) : (u ^ 2).re = 2 * u.re ^ 2 - 1 := by
  have h : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h1 := Complex.normSq_eq_norm_sq u
    rw [hu, Complex.normSq_apply] at h1
    nlinarith
  rw [sq, Complex.mul_re]
  nlinarith

/-- The local 3-4-1 inequality for logarithmic derivatives at an unramified prime. -/
lemma local_341 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {w : ℂ} (hw : ‖w‖ = 1) :
    0 ≤ (3 * ((x : ℂ) / (1 - x)) + 4 * (w * x / (1 - w * x)) +
      w ^ 2 * x / (1 - w ^ 2 * x)).re := by
  have hx : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have hwx : ‖w * x‖ < 1 := by rw [norm_mul, hw, one_mul]; exact hx
  have hw2x : ‖w ^ 2 * x‖ < 1 := by rw [norm_mul, norm_pow, hw, one_pow, one_mul]; exact hx
  have h := (((hasSum_geom_succ hx).mul_left 3).add ((hasSum_geom_succ hwx).mul_left 4)).add
    (hasSum_geom_succ hw2x)
  have hre := Complex.hasSum_re h
  refine hre.nonneg fun n => ?_
  set u := w ^ (n + 1) with hudef
  have hu : ‖u‖ = 1 := by rw [hudef, norm_pow, hw, one_pow]
  have e : (3 * (x : ℂ) ^ (n + 1) + 4 * (w * x) ^ (n + 1) + (w ^ 2 * x) ^ (n + 1))
      = ((x ^ (n + 1) : ℝ) : ℂ) * (3 + 4 * u + u ^ 2) := by
    rw [hudef]; push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  apply mul_nonneg (pow_nonneg hx0 _)
  have : (3 + 4 * u + u ^ 2 : ℂ).re = 3 + 4 * u.re + (u ^ 2).re := by simp
  rw [this, re_sq_of_norm_one hu]
  nlinarith [sq_nonneg (u.re + 1)]

/-- The local inequality at a prime where `χ` is ramified (so only `ζ_F` and `χ²` contribute). -/
lemma local_341_ram {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 ≤ (3 * ((x : ℂ) / (1 - x)) + w * x / (1 - w * x)).re := by
  have hx' : (1 - x) ≠ 0 := by linarith
  have h1 : ((x : ℂ) / (1 - x)).re = x / (1 - x) := by
    rw [show ((x : ℂ) / (1 - x)) = ((x / (1 - x) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  have hwx : ‖w * x‖ ≤ x := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    exact mul_le_of_le_one_left hx0 hw
  have hden : 1 - x ≤ ‖1 - w * x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (w * x)
    rw [norm_one] at this; linarith
  have hb : ‖w * x / (1 - w * x)‖ ≤ x / (1 - x) := by
    rw [norm_div]
    exact div_le_div₀ hx0 hwx (by linarith) hden
  have hre : -(x / (1 - x)) ≤ (w * x / (1 - w * x)).re := by
    have := Complex.abs_re_le_norm (w * x / (1 - w * x))
    linarith [neg_abs_le (w * x / (1 - w * x)).re]
  have h3 : (3 * ((x : ℂ) / (1 - x))).re = 3 * (x / (1 - x)) := by
    rw [show (3 * ((x : ℂ) / (1 - x))) = ((3 * (x / (1 - x)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [Complex.add_re, h3]
  have : 0 ≤ x / (1 - x) := div_nonneg hx0 (by linarith)
  linarith

/-! ### The logarithmic derivative of the Euler product -/

/-- The logarithm of one Euler factor. -/
noncomputable def Gv (ψ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  -Complex.log (1 - zv ψ s v)

/-- `log N(𝔭_v)` as a complex number. -/
noncomputable def lN (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  Complex.log ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm v.asIdeal := by
  have := two_le_absNorm v; omega

lemma absNorm_ne_zero' (v : HeightOneSpectrum (𝓞 F)) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (absNorm_pos v).ne'

lemma hasDerivAt_zv (ψ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    HasDerivAt (fun w => zv ψ w v) (-(lN v) * zv ψ s v) s := by
  have h := ((hasDerivAt_id' s).neg).const_cpow (c := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))
    (Or.inl (absNorm_ne_zero' v))
  have h2 := h.const_mul (ψ.primeValue v)
  unfold zv lN
  exact h2.congr_deriv (by simp only [Pi.neg_apply]; ring)

lemma one_sub_zv_mem_slitPlane (ψ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ}
    (hs : 1 ≤ s.re) : 1 - zv ψ s v ∈ slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have h := norm_zv_le_half ψ s hs v
  have := Complex.re_le_norm (zv ψ s v)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma hasDerivAt_Gv (ψ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ}
    (hs : 1 ≤ s.re) :
    HasDerivAt (Gv ψ v) (-(lN v * zv ψ s v / (1 - zv ψ s v))) s := by
  have h := ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_zv ψ v s)).clog
    (one_sub_zv_mem_slitPlane ψ v hs)
  have h2 := h.neg
  unfold Gv
  exact h2.congr_deriv (by simp only [Pi.sub_apply]; ring)

lemma norm_Gv_le (ψ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖Gv ψ v s‖ ≤ 3 / 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
  unfold Gv
  rw [norm_neg, sub_eq_add_neg]
  have hz : ‖-zv ψ s v‖ ≤ 1 / 2 := by rw [norm_neg]; exact norm_zv_le_half ψ s hs v
  refine (Complex.norm_log_one_add_half_le_self hz).trans ?_
  rw [norm_neg]
  gcongr
  exact norm_zv_le ψ s v

/-- On `Re s > 1` the Euler product is `exp` of the sum of the logarithms of its factors. -/
lemma euler_eq_exp (ψ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    heckeEulerProduct ψ s = Complex.exp (∑' v, Gv ψ v s) := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), (1 - zv ψ s v)⁻¹ ≠ 0 := fun v =>
    inv_ne_zero (Complex.slitPlane_ne_zero (one_sub_zv_mem_slitPlane ψ v hs.le))
  have hlog : ∀ v : HeightOneSpectrum (𝓞 F), Complex.log ((1 - zv ψ s v)⁻¹) = Gv ψ v s := fun v =>
    Complex.log_inv _ (Complex.slitPlane_arg_ne_pi (one_sub_zv_mem_slitPlane ψ v hs.le))
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => Complex.log ((1 - zv ψ s v)⁻¹) := by
    simp_rw [hlog]
    refine Summable.of_norm_bounded ((summable_placeNorm (F := F) s.re hs).mul_left (3 / 2)) ?_
    exact fun v => norm_Gv_le ψ v hs.le
  have := Complex.cexp_tsum_eq_tprod hne hsum
  simp_rw [hlog] at this
  rw [this]
  rfl

/-- **Logarithmic derivative of the Euler product.** For `Re s > 1`,
`-E'(s)/E(s) = ∑_v log N(𝔭_v) z_v/(1 - z_v)` with `z_v = χ(𝔭_v) N(𝔭_v)^{-s}`. -/
theorem neg_logDeriv_euler (ψ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v => lN v * zv ψ s v / (1 - zv ψ s v))
      (-(deriv (heckeEulerProduct ψ) s / heckeEulerProduct ψ s)) := by
  set σ₀ : ℝ := (1 + s.re) / 2 with hσ₀
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; linarith
  have hσ₀s : σ₀ < s.re := by rw [hσ₀]; linarith
  set U : Set ℂ := {w | σ₀ < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hσ₀s
  have hu := (summable_placeNorm (F := F) σ₀ hσ₀1).mul_left (3 / 2)
  have hdiff : ∀ v : HeightOneSpectrum (𝓞 F), DifferentiableOn ℂ (Gv ψ v) U := fun v w hw =>
    (hasDerivAt_Gv ψ v (le_of_lt (lt_trans hσ₀1 hw))).differentiableAt.differentiableWithinAt
  have hle : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : ℂ), w ∈ U →
      ‖Gv ψ v w‖ ≤ 3 / 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀) := by
    intro v w hw
    refine (norm_Gv_le ψ v (le_of_lt (lt_trans hσ₀1 hw))).trans ?_
    gcongr
    · exact_mod_cast (absNorm_pos v)
    · exact le_of_lt hw
  have hD := hasSum_deriv_of_summable_norm hu hdiff hUo hle hsU
  have hGd : DifferentiableOn ℂ (fun w => ∑' v, Gv ψ v w) U :=
    differentiableOn_tsum_of_summable_norm hu hdiff hUo hle
  -- the Euler product equals `exp ∘ G` near `s`
  have hEq : heckeEulerProduct ψ =ᶠ[𝓝 s] fun w => Complex.exp (∑' v, Gv ψ v w) :=
    Filter.mem_of_superset (hUo.mem_nhds hsU) fun w hw =>
      euler_eq_exp ψ (lt_trans hσ₀1 hw)
  have hGs : DifferentiableAt ℂ (fun w => ∑' v, Gv ψ v w) s :=
    hGd.differentiableAt (hUo.mem_nhds hsU)
  have hderivE : deriv (heckeEulerProduct ψ) s =
      Complex.exp (∑' v, Gv ψ v s) * deriv (fun w => ∑' v, Gv ψ v w) s := by
    rw [hEq.deriv_eq]
    exact (hGs.hasDerivAt.cexp).deriv
  have hEs : heckeEulerProduct ψ s = Complex.exp (∑' v, Gv ψ v s) := euler_eq_exp ψ hs
  have hval : -(deriv (heckeEulerProduct ψ) s / heckeEulerProduct ψ s) =
      -deriv (fun w => ∑' v, Gv ψ v w) s := by
    rw [hderivE, hEs, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  rw [hval]
  have hterm : ∀ v : HeightOneSpectrum (𝓞 F),
      deriv (Gv ψ v) s = -(lN v * zv ψ s v / (1 - zv ψ s v)) := fun v =>
    (hasDerivAt_Gv ψ v hs.le).deriv
  simp_rw [hterm] at hD
  -- the sum of the derivatives is the derivative of the sum, with the sign absorbed
  have := hD.neg
  simp only [neg_neg] at this
  exact this

end MasulloGRH.ZFRLarge



/-! Part 2: the 3-4-1 inequality for logarithmic derivatives of Euler products. -/

namespace MasulloGRH.ZFRLarge

open Filter Topology NumberField IsDedekindDomain Complex Metric
open MasulloGRH.Aux_HL MasulloGRH.Aux_MQ

variable {F : Type*} [Field F] [NumberField F]

lemma zv_one' (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    zv (1 : HeckeCharacter F) (σ : ℂ) v = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) : ℝ) := by
  have hu : (1 : HeckeCharacter F).IsUnramifiedAt v := fun y _ => by
    unfold HeckeCharacter.localComponent; rfl
  obtain ⟨y, hy⟩ := exists_uniformizer v
  have hone : (1 : HeckeCharacter F).primeValue v = 1 := by
    unfold HeckeCharacter.primeValue
    rw [dif_pos ⟨hu, y, hy⟩]
    unfold HeckeCharacter.localComponent; rfl
  unfold zv
  rw [hone, one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]

lemma lN_eq (v : HeightOneSpectrum (𝓞 F)) :
    lN v = ((Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold lN
  rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]

lemma log_absNorm_nonneg (v : HeightOneSpectrum (𝓞 F)) :
    0 ≤ Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
  Real.log_nonneg (by exact_mod_cast (absNorm_pos v))

lemma cpow_two_mul (n : ℕ) (t : ℝ) :
    (n : ℂ) ^ (-(((2 * t : ℝ) : ℂ) * I)) = ((n : ℂ) ^ (-((t : ℂ) * I))) ^ 2 := by
  rw [← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

/-- The local term of the 3-4-1 combination is nonnegative. -/
lemma term_341_nonneg (χ : HeckeCharacter F) (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (v : HeightOneSpectrum (𝓞 F)) :
    0 ≤ (3 * (lN v * zv (1 : HeckeCharacter F) (σ : ℂ) v / (1 - zv 1 (σ : ℂ) v)) +
      4 * (lN v * zv χ ((σ : ℂ) + (t : ℂ) * I) v / (1 - zv χ ((σ : ℂ) + (t : ℂ) * I) v)) +
      lN v * zv (χ * χ) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) v /
        (1 - zv (χ * χ) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) v)).re := by
  set n : ℕ := Ideal.absNorm v.asIdeal with hn
  have hn0 : 0 < n := absNorm_pos v
  set x : ℝ := (n : ℝ) ^ (-σ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hx1 : x < 1 := by
    have h := norm_zv_le_half (1 : HeckeCharacter F) (σ : ℂ) (by simpa using hσ.le) v
    rw [zv_one', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] at h
    linarith
  set ℓ : ℝ := Real.log (n : ℝ) with hℓ
  have hℓ0 : 0 ≤ ℓ := log_absNorm_nonneg v
  have h1 : zv (1 : HeckeCharacter F) (σ : ℂ) v = (x : ℂ) := zv_one' σ v
  have hz1 : zv χ ((σ : ℂ) + (t : ℂ) * I) v = (χ.primeValue v * (n : ℂ) ^ (-((t : ℂ) * I))) * x := by
    unfold zv; rw [cpow_split n hn0 σ t]; ring
  have hz2 : zv (χ * χ) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) v =
      ((χ * χ).primeValue v * (n : ℂ) ^ (-(((2 * t : ℝ) : ℂ) * I))) * x := by
    unfold zv; rw [cpow_split n hn0 σ (2 * t)]; ring
  have hfac : ∀ a b c : ℂ, (3 * ((ℓ : ℂ) * a) + 4 * ((ℓ : ℂ) * b) + (ℓ : ℂ) * c) =
      (ℓ : ℂ) * (3 * a + 4 * b + c) := fun a b c => by ring
  rw [lN_eq, ← hn, ← hℓ, h1, hz1, hz2]
  simp only [mul_div_assoc]
  rw [hfac, Complex.re_ofReal_mul]
  apply mul_nonneg hℓ0
  have hc := norm_cpow_imag n hn0 t
  by_cases hun : χ.IsUnramifiedAt v ∧ ∃ y : (v.adicCompletion F)ˣ, IsUniformizerAt v y
  · obtain ⟨hsq, hnorm⟩ := primeValue_mul_self χ v hun
    set w : ℂ := χ.primeValue v * (n : ℂ) ^ (-((t : ℂ) * I)) with hw
    have hw1 : ‖w‖ = 1 := by rw [hw, norm_mul, hnorm, hc, one_mul]
    have hw2 : (χ * χ).primeValue v * (n : ℂ) ^ (-(((2 * t : ℝ) : ℂ) * I)) = w ^ 2 := by
      rw [hsq, cpow_two_mul, hw]; ring
    rw [hw2]
    have := local_341 hx0 hx1 hw1
    simpa only [mul_div_assoc] using this
  · have hram := primeValue_ram χ v hun
    set w' : ℂ := (χ * χ).primeValue v * (n : ℂ) ^ (-(((2 * t : ℝ) : ℂ) * I)) with hw'
    have hw'1 : ‖w'‖ ≤ 1 := by
      rw [hw', norm_mul, Complex.norm_natCast_cpow_of_pos hn0]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero, Real.rpow_zero, mul_one]
      exact norm_primeValue_le _ v
    rw [hram]
    simp only [zero_mul, mul_zero, add_zero, zero_div]
    have := local_341_ram hx0 hx1 hw'1
    simpa only [mul_div_assoc] using this

/-- **3-4-1 inequality for logarithmic derivatives of Euler products**, `σ > 1`. -/
theorem logDeriv_euler_341 (χ : HeckeCharacter F) (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-(deriv (heckeEulerProduct (1 : HeckeCharacter F)) (σ : ℂ) /
          heckeEulerProduct (1 : HeckeCharacter F) (σ : ℂ))).re +
      4 * (-(deriv (heckeEulerProduct χ) ((σ : ℂ) + (t : ℂ) * I) /
          heckeEulerProduct χ ((σ : ℂ) + (t : ℂ) * I))).re +
      (-(deriv (heckeEulerProduct (χ * χ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) /
          heckeEulerProduct (χ * χ) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I))).re := by
  have hre : ∀ u : ℝ, 1 < ((σ : ℂ) + (u : ℂ) * I).re := fun u => by simpa using hσ
  have h1 := neg_logDeriv_euler (1 : HeckeCharacter F) (s := (σ : ℂ)) (by simpa using hσ)
  have h2 := neg_logDeriv_euler χ (hre t)
  have h3 := neg_logDeriv_euler (χ * χ) (hre (2 * t))
  have h := Complex.hasSum_re (((h1.mul_left 3).add (h2.mul_left 4)).add h3)
  have hval := h.nonneg fun v => term_341_nonneg χ σ hσ t v
  have e : ∀ a b c : ℂ, (3 * a + 4 * b + c).re = 3 * a.re + 4 * b.re + c.re := fun a b c => by
    simp [Complex.add_re, Complex.mul_re]
  rw [e] at hval
  exact hval

end MasulloGRH.ZFRLarge



/-! Part 3: the Dedekind zeta log-derivative bound near `s = 1`, and the lower bound for
the Euler product. -/

namespace MasulloGRH.ZFRLarge

open Filter Topology NumberField IsDedekindDomain Complex Metric
open MasulloGRH.Aux_HL MasulloGRH.Aux_MQ

variable {F : Type*} [Field F] [NumberField F]

lemma spec' (χ : HeckeCharacter F) :
    MeromorphicNFOn (heckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → heckeLFunction χ s = heckeEulerProduct χ s :=
  heckeL_spec χ (heckeLFunction_exists_meromorphic_continuation F χ)

/-- the real Dedekind sum. -/
noncomputable def Zr (F : Type*) [Field F] [NumberField F] (σ : ℝ) : ℝ :=
  ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)

theorem Zr_anti {σ₁ σ₂ : ℝ} (h1 : 1 < σ₁) (h12 : σ₁ ≤ σ₂) : Zr F σ₂ ≤ Zr F σ₁ := by
  unfold Zr
  refine (summable_idealNorm (F := F) σ₂ (by linarith)).tsum_le_tsum (fun I => ?_)
    (summable_idealNorm (F := F) σ₁ h1)
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h | h
  · rw [h, Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h) (by linarith)

theorem zeta_bound_global : ∃ C : ℝ, 1 ≤ C ∧ (∀ σ : ℝ, 1 < σ → σ ≤ 2 → Zr F σ ≤ C / (σ - 1)) ∧
    (∀ σ : ℝ, 2 ≤ σ → Zr F σ ≤ C) := by
  obtain ⟨C₀, hC₀⟩ := zeta_bound (F := F)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hC₀)
  set δ := min (δ₀ / 2) (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδh : δ ≤ 1 / 2 := min_le_right _ _
  set Z₁ := Zr F (1 + δ)
  refine ⟨max (max C₀ 0 + 1) (Z₁ + 1), le_trans (by linarith [le_max_right C₀ 0])
    (le_max_left _ _), fun σ h1 h2 => ?_, fun σ h2 => ?_⟩
  · rcases lt_or_ge σ (1 + δ) with h | h
    · have hd : dist σ 1 < δ₀ := by
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith [min_le_left (δ₀ / 2) (1 / 2)]
      have := hδ₀' hd h1
      refine this.trans (div_le_div_of_nonneg_right ?_ (by linarith))
      have : C₀ ≤ max C₀ 0 + 1 := by linarith [le_max_left C₀ 0]
      exact this.trans (le_max_left _ _)
    · have hZ := Zr_anti (F := F) (by linarith) h
      have : Z₁ ≤ max (max C₀ 0 + 1) (Z₁ + 1) := (le_max_right _ _).trans' (by linarith)
      rw [le_div_iff₀ (by linarith)]
      have hnn : 0 ≤ Zr F σ := tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
      calc Zr F σ * (σ - 1) ≤ Zr F σ * 1 := mul_le_mul_of_nonneg_left (by linarith) hnn
        _ ≤ _ := by linarith
  · have hZ := Zr_anti (F := F) (σ₁ := 1 + δ) (by linarith) (by linarith)
    exact hZ.trans ((le_max_right _ _).trans' (by linarith))

/-- lower bound for the Euler product. -/
theorem euler_lower (χ : HeckeCharacter F) (s : ℂ) (hs : 1 < s.re) :
    1 ≤ ‖heckeEulerProduct χ s‖ * Zr F s.re := by
  have h1 := (hasProd_eulerProduct χ s hs).norm
  have h0 := (hasProd_eulerProduct (1 : HeckeCharacter F) (s.re : ℂ) (by simpa using hs)).norm
  have hle : ‖heckeEulerProduct (1 : HeckeCharacter F) (s.re : ℂ)‖ ≤ Zr F s.re := by
    have := norm_euler_le (1 : HeckeCharacter F) s.re hs 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    exact this
  refine le_trans (one_le_of_hasProd (h1.mul h0) fun v => ?_) ?_
  · rw [zv_one', norm_inv, norm_inv]
    set x : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re)
    have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hx1 : x ≤ 1 / 2 := by
      have := norm_zv_le_half (1 : HeckeCharacter F) (s.re : ℂ) (by simpa using hs.le) v
      rw [zv_one', Complex.norm_of_nonneg hx0] at this; exact this
    have hz : ‖zv χ s v‖ ≤ x := norm_zv_le χ s v
    have e0 : ‖(1 : ℂ) - (x : ℂ)‖ = 1 - x := by
      rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_of_nonneg (by linarith)]
    have e1 : ‖1 - zv χ s v‖ ≤ 1 + x := by
      calc ‖1 - zv χ s v‖ ≤ ‖(1 : ℂ)‖ + ‖zv χ s v‖ := norm_sub_le _ _
        _ ≤ 1 + x := by rw [norm_one]; linarith
    have p1 : 0 < ‖1 - zv χ s v‖ := norm_one_sub_pos (by linarith)
    rw [e0, ← mul_inv, one_le_inv₀ (mul_pos p1 (by linarith))]
    calc ‖1 - zv χ s v‖ * (1 - x) ≤ (1 + x) * (1 - x) := by gcongr; linarith
      _ ≤ 1 := by nlinarith
  · exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)

/-- On `Re s > 1`, `L_f(s, χ)` is analytic, nonzero, and agrees with the Euler product near `s`. -/
lemma analytic_ne_zero_re_gt_one (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (heckeLFunction χ) s ∧ heckeLFunction χ s ≠ 0 ∧
      heckeEulerProduct χ =ᶠ[𝓝 s] heckeLFunction χ := by
  have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEA : AnalyticAt ℂ (heckeEulerProduct χ) s :=
    (differentiableOn_euler χ).analyticAt (hU.mem_nhds hs)
  have hev : heckeEulerProduct χ =ᶠ[𝓝 s] heckeLFunction χ :=
    Filter.mem_of_superset (hU.mem_nhds hs) fun z hz => ((spec' χ).2 z hz).symm
  refine ⟨hEA.congr hev, ?_, hev⟩
  rw [(spec' χ).2 s hs]
  intro h0
  have := euler_lower χ s hs
  rw [h0, norm_zero, zero_mul] at this
  linarith

/-- `-L'/L = -E'/E` on `Re s > 1`. -/
lemma logDeriv_eq_euler (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    deriv (heckeLFunction χ) s / heckeLFunction χ s =
      deriv (heckeEulerProduct χ) s / heckeEulerProduct χ s := by
  obtain ⟨-, -, hev⟩ := analytic_ne_zero_re_gt_one χ hs
  rw [hev.deriv_eq, hev.eq_of_nhds]

lemma tendsto_ofReal_nhdsNE :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : σ = 1 := by exact_mod_cast h
    exact absurd this (ne_of_gt hσ)

/-- **Log-derivative of the Dedekind zeta function near `s = 1⁺`.** -/
theorem dedekind_logDeriv_bound : ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r₀ →
      (-(deriv (heckeLFunction (1 : HeckeCharacter F)) (σ : ℂ) /
        heckeLFunction (1 : HeckeCharacter F) (σ : ℂ))).re ≤ 1 / (σ - 1) + C₀ := by
  set ζ := heckeLFunction (1 : HeckeCharacter F) with hζdef
  have hM : MeromorphicAt ζ 1 := ((spec' (1 : HeckeCharacter F)).1 (Set.mem_univ 1)).meromorphicAt
  have hT := tendsto_ofReal_nhdsNE
  have hT' : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    hT.mono_right nhdsWithin_le_nhds
  have hne : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), ζ (σ : ℂ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (analytic_ne_zero_re_gt_one (1 : HeckeCharacter F) (s := (σ : ℂ))
      (by simpa using hσ)).2.1
  -- the order at `1` is finite
  have hfin : meromorphicOrderAt ζ 1 ≠ ⊤ := by
    intro htop
    have h0 := hT.eventually (meromorphicOrderAt_eq_top_iff.1 htop)
    obtain ⟨σ, h1, h2⟩ := (h0.and hne).exists
    exact h2 h1
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hfin
  obtain ⟨g, hgA, hg1, hfac⟩ := (meromorphicOrderAt_eq_int_iff hM).1 hn.symm
  -- `ζ(σ) ≤ C/(σ - 1)` forces `n ≥ -1`
  obtain ⟨C, hC⟩ := zeta_bound (F := F)
  have hCζ : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), ‖ζ (σ : ℂ)‖ ≤ C / (σ - 1) := by
    filter_upwards [hC, self_mem_nhdsWithin] with σ h1 h2
    have hs : 1 < ((σ : ℂ)).re := by simpa using h2
    rw [hζdef, (spec' (1 : HeckeCharacter F)).2 _ hs]
    have := norm_euler_le (1 : HeckeCharacter F) σ h2 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    exact this.trans h1
  have hgc : ∀ᶠ z in 𝓝 (1 : ℂ), ‖g 1‖ / 2 < ‖g z‖ :=
    hgA.continuousAt.norm.eventually (lt_mem_nhds (by
      have := norm_pos_iff.2 hg1; linarith))
  have hσ1 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have := ((continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  have hn1 : -1 ≤ n := by
    by_contra hlt
    push Not at hlt
    have hn2 : n ≤ -2 := by omega
    have hg1pos : 0 < ‖g 1‖ := norm_pos_iff.2 hg1
    have hpos : 0 < min 1 (‖g 1‖ / (2 * (|C| + 1))) := lt_min one_pos (by positivity)
    obtain ⟨σ, h1, h2, h3, h4, h5⟩ := ((hT.eventually hfac).and ((hT'.eventually hgc).and
      (hCζ.and ((hσ1.eventually (gt_mem_nhds hpos)).and self_mem_nhdsWithin)))).exists
    have hσ : 1 < σ := h5
    set a : ℝ := σ - 1 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have ha1 : a < 1 := lt_of_lt_of_le h4 (min_le_left _ _)
    have ha2 : a < ‖g 1‖ / (2 * (|C| + 1)) := lt_of_lt_of_le h4 (min_le_right _ _)
    have hz : ‖ζ (σ : ℂ)‖ ≤ C / a := h3
    have hnorm : ‖(σ : ℂ) - 1‖ = a := by
      rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ha0]
    rw [h1, norm_smul, norm_zpow, hnorm] at hz
    have hapow : a ^ (-2 : ℤ) ≤ a ^ n := zpow_le_zpow_right_of_le_one₀ ha0 ha1.le hn2
    have hm2 : a ^ (-2 : ℤ) = (a ^ 2)⁻¹ := by rw [zpow_neg, zpow_ofNat]
    rw [hm2] at hapow
    have hg2 : ‖g 1‖ / 2 < ‖g (σ : ℂ)‖ := h2
    have hlow : (a ^ 2)⁻¹ * (‖g 1‖ / 2) ≤ a ^ n * ‖g (σ : ℂ)‖ :=
      mul_le_mul hapow hg2.le (by positivity) (by positivity)
    have hCa : C / a ≤ |C| / a := div_le_div_of_nonneg_right (le_abs_self C) ha0.le
    have key : (a ^ 2)⁻¹ * (‖g 1‖ / 2) ≤ |C| / a := hlow.trans (hz.trans hCa)
    rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) ha0] at key
    have : ‖g 1‖ / 2 ≤ |C| * a := by nlinarith
    have h6 : (|C| + 1) * a < ‖g 1‖ / 2 := by
      rw [lt_div_iff₀ (by positivity)] at ha2; nlinarith
    nlinarith [abs_nonneg C]
  -- local data near `1`
  have hgd : ∀ᶠ z in 𝓝 (1 : ℂ), ‖deriv g z / g z‖ < ‖deriv g 1 / g 1‖ + 1 :=
    ((hgA.deriv.continuousAt.div hgA.continuousAt hg1).norm).eventually
      (gt_mem_nhds (lt_add_one _))
  have hfac' : ∀ᶠ z in 𝓝 (1 : ℂ), ∀ᶠ w in 𝓝 z, w ≠ 1 → ζ w = (w - 1) ^ n • g w :=
    (eventually_nhdsWithin_iff.1 hfac).eventually_nhds
  have hP : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      (∀ᶠ w in 𝓝 (σ : ℂ), w ≠ 1 → ζ w = (w - 1) ^ n • g w) ∧ AnalyticAt ℂ g (σ : ℂ) ∧
      ‖g 1‖ / 2 < ‖g (σ : ℂ)‖ ∧ ‖deriv g (σ : ℂ) / g (σ : ℂ)‖ < ‖deriv g 1 / g 1‖ + 1 ∧
      1 < σ :=
    (hT'.eventually hfac').and ((hT'.eventually hgA.eventually_analyticAt).and
      ((hT'.eventually hgc).and ((hT'.eventually hgd).and self_mem_nhdsWithin)))
  obtain ⟨u, hu1, hu⟩ := (nhdsGT_basis (1 : ℝ)).eventually_iff.1 hP
  refine ⟨(u - 1) / 2, by linarith, ‖deriv g 1 / g 1‖ + 1, by positivity, fun σ hσ hσu => ?_⟩
  obtain ⟨E1, E2, E3, E4, -⟩ := hu ⟨hσ, by linarith⟩
  have hσne : (σ : ℂ) ≠ 1 := by
    intro h; have : σ = 1 := by exact_mod_cast h
    linarith
  have ha : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.2 hσne
  have hgσ : g (σ : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at E3
    have := norm_nonneg (g 1); linarith
  have hEq : ζ =ᶠ[𝓝 (σ : ℂ)] fun w => (w - 1) ^ n * g w := by
    filter_upwards [E1, isOpen_ne.mem_nhds hσne] with w hw hw1
    rw [hw hw1, smul_eq_mul]
  have hd1 := (hasDerivAt_zpow n ((σ : ℂ) - 1) (Or.inl ha)).comp (σ : ℂ)
    ((hasDerivAt_id' (σ : ℂ)).sub_const 1)
  have hd := hd1.mul E2.differentiableAt.hasDerivAt
  have hderiv : deriv ζ (σ : ℂ) =
      (n : ℂ) * ((σ : ℂ) - 1) ^ (n - 1) * 1 * g σ + ((σ : ℂ) - 1) ^ n * deriv g σ := by
    rw [hEq.deriv_eq]; exact hd.deriv
  have hval : ζ (σ : ℂ) = ((σ : ℂ) - 1) ^ n * g σ := hEq.eq_of_nhds
  have hratio : -(deriv ζ (σ : ℂ) / ζ (σ : ℂ)) =
      -(((n / (σ - 1) : ℝ) : ℂ)) - deriv g σ / g σ := by
    rw [hderiv, hval, zpow_sub_one₀ ha]
    have hpow : ((σ : ℂ) - 1) ^ n ≠ 0 := zpow_ne_zero _ ha
    push_cast
    field_simp
    ring
  rw [hratio, Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
  have hσ0 : 0 < σ - 1 := by linarith
  have hn1' : (-1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 : -(n / (σ - 1) : ℝ) ≤ 1 / (σ - 1) := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hσ0.le
  have h2 : -(deriv g (σ : ℂ) / g (σ : ℂ)).re ≤ ‖deriv g (σ : ℂ) / g (σ : ℂ)‖ := by
    have h3 := Complex.abs_re_le_norm (deriv g (σ : ℂ) / g (σ : ℂ))
    have h4 := neg_abs_le (deriv g (σ : ℂ) / g (σ : ℂ)).re
    linarith
  linarith

end MasulloGRH.ZFRLarge



/-! Part 4: assembly of the large-height zero-free region. -/

namespace MasulloGRH.ZFRLarge

open Filter Topology NumberField IsDedekindDomain Complex Metric
open MasulloGRH.Aux_HL MasulloGRH.Aux_MQ

variable {F : Type*} [Field F] [NumberField F]

lemma growth_all' : Growth F := fun ψ a b hab =>
  heckeLFunction_polynomial_growth_on_vertical_strips F ψ a b hab

lemma hex' : ∀ ψ : HeckeCharacter F, ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
    ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct ψ s := fun ψ =>
  heckeLFunction_exists_meromorphic_continuation F ψ

lemma order_nonpos_of_analytic_ne_zero {f : ℂ → ℂ} {s : ℂ}
    (hA : AnalyticAt ℂ f s) (h0 : f s ≠ 0) : meromorphicOrderAt f s ≤ 0 := by
  rw [hA.meromorphicOrderAt_eq, (hA.analyticOrderAt_eq_zero).2 h0]
  simp

lemma lower_bound_on_line (ψ : HeckeCharacter F) {CZ : ℝ}
    (hCZ : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → Zr F σ ≤ CZ / (σ - 1)) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (t : ℝ) : (σ - 1) / CZ ≤ ‖heckeLFunction ψ ((σ : ℂ) + (t : ℂ) * I)‖ := by
  have hre : 1 < ((σ : ℂ) + (t : ℂ) * I).re := by simpa using hσ
  have h1 := euler_lower ψ _ hre
  have hre' : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  rw [hre'] at h1
  rw [(spec' ψ).2 _ hre]
  have hZpos : 0 < Zr F σ := by
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h (norm_nonneg (heckeEulerProduct ψ ((σ : ℂ) + (t : ℂ) * I)))
    linarith
  have hZ := hCZ σ hσ hσ2
  have hCZpos : 0 < CZ := by
    have : 0 < CZ / (σ - 1) := lt_of_lt_of_le hZpos hZ
    have hs : 0 < σ - 1 := by linarith
    by_contra h; push Not at h
    have : CZ / (σ - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hs.le
    linarith
  rw [div_le_iff₀ hCZpos]
  have hs : 0 < σ - 1 := by linarith
  have : Zr F σ * (σ - 1) ≤ CZ := by rwa [le_div_iff₀ hs] at hZ
  nlinarith [norm_nonneg (heckeEulerProduct ψ ((σ : ℂ) + (t : ℂ) * I))]

end MasulloGRH.ZFRLarge

set_option maxHeartbeats 2000000 in
open MasulloGRH MasulloGRH.ZFRLarge MasulloGRH.Aux_HL MasulloGRH.Aux_MQ Filter Topology Complex
  Metric in
theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : ℝ, ∀ s : ℂ, T ≤ |s.im| → 1 - c / Real.log |s.im| < s.re →
      meromorphicOrderAt (heckeLFunction χ) s ≤ 0 := by
  -- analyticity and polynomial growth in the strip `-1 < Re s < 4` at large height
  obtain ⟨Ta1, hTa1⟩ := analytic_of_growth hex' growth_all' χ (-1) 4 (by norm_num)
  obtain ⟨Ta2, hTa2⟩ := analytic_of_growth hex' growth_all' (χ * χ) (-1) 4 (by norm_num)
  obtain ⟨m1, C1, T1, hC1, hT1, hg1⟩ := growth_nat growth_all' χ (-1) 4 (by norm_num)
  obtain ⟨m2, C2, T2, hC2, hT2, hg2⟩ := growth_nat growth_all' (χ * χ) (-1) 4 (by norm_num)
  obtain ⟨r₀, hr₀, C₀, hC₀, hDZ⟩ := dedekind_logDeriv_bound (F := F)
  obtain ⟨CZ, hCZ1, hCZ, -⟩ := zeta_bound_global (F := F)
  set r : ℝ := min r₀ (1 / 2) with hr
  have hr0 : 0 < r := lt_min hr₀ (by norm_num)
  have hrh : r ≤ 1 / 2 := min_le_right _ _
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  set M : ℝ := (m1 : ℝ) + m2 with hM
  have hM0 : 0 ≤ M := by positivity
  set A : ℝ := Real.log (C1 + 1) + Real.log (C2 + 1) + Real.log CZ + C₀ + 1 / r with hA
  have hlC1 : 0 ≤ Real.log (C1 + 1) := Real.log_nonneg (by linarith)
  have hlC2 : 0 ≤ Real.log (C2 + 1) := Real.log_nonneg (by linarith)
  have hlCZ : 0 ≤ Real.log CZ := Real.log_nonneg hCZ1
  have hA0 : 1 / r ≤ A := by
    have : 0 ≤ Real.log (C1 + 1) + Real.log (C2 + 1) + Real.log CZ + C₀ := by positivity
    linarith
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hA0
  set K : ℝ := A + 2 * M with hK
  have hKpos : 0 < K := by positivity
  set c : ℝ := r / (20000 * K) with hc
  have hcpos : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    have : r ≤ 1 / 2 := hrh
    have : 1 ≤ A * r := by
      have := mul_le_mul_of_nonneg_right hA0 hr0.le
      rwa [one_div, inv_mul_cancel₀ hr0.ne'] at this
    nlinarith
  set T₀ : ℝ := max (max (max Ta1 Ta2) (max T1 T2)) 2 + 1 with hT₀
  refine ⟨c, hcpos, T₀, fun s hsT hs => ?_⟩
  set γ : ℝ := s.im with hγ
  set β : ℝ := s.re with hβ
  have hγT : T₀ ≤ |γ| := hsT
  have hγ3 : 3 ≤ |γ| := by
    have : (2 : ℝ) ≤ max (max (max Ta1 Ta2) (max T1 T2)) 2 := le_max_right _ _
    linarith
  have hγa1 : Ta1 + 1 ≤ |γ| := by
    have : Ta1 ≤ max (max (max Ta1 Ta2) (max T1 T2)) 2 :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    linarith
  have hγa2 : Ta2 + 1 ≤ |γ| := by
    have : Ta2 ≤ max (max (max Ta1 Ta2) (max T1 T2)) 2 :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    linarith
  have hγ1 : T1 + 1 ≤ |γ| := by
    have : T1 ≤ max (max (max Ta1 Ta2) (max T1 T2)) 2 :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
    linarith
  have hγ2 : T2 + 1 ≤ |γ| := by
    have : T2 ≤ max (max (max Ta1 Ta2) (max T1 T2)) 2 :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
    linarith
  have hlogγ : 1 ≤ Real.log |γ| := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  -- the half-plane `Re s > 1`
  rcases lt_or_ge 1 β with hβ1 | hβ1
  · obtain ⟨hA1, hne, -⟩ := analytic_ne_zero_re_gt_one χ (s := s) hβ1
    exact order_nonpos_of_analytic_ne_zero hA1 hne
  have hcl : c / Real.log |γ| ≤ c := div_le_self hcpos.le hlogγ
  have hβ0 : 0 < β := by linarith
  have hAs : AnalyticAt ℂ (heckeLFunction χ) s :=
    hTa1 s (by rw [← hβ]; linarith) (by rw [← hβ]; linarith) (by linarith)
  by_contra hpos
  rw [not_le] at hpos
  have hzero : heckeLFunction χ s = 0 := by
    rw [hAs.meromorphicOrderAt_eq] at hpos
    apply apply_eq_zero_of_analyticOrderAt_ne_zero
    intro h0
    rw [h0] at hpos
    simp at hpos
  -- the parameter `𝓛`
  set 𝓛 : ℝ := A + M * Real.log (2 * |γ| + 2) with h𝓛def
  have hlog2 : 0 ≤ Real.log (2 * |γ| + 2) := Real.log_nonneg (by linarith [abs_nonneg γ])
  have h𝓛A : A ≤ 𝓛 := by have := mul_nonneg hM0 hlog2; linarith
  have h𝓛pos : 0 < 𝓛 := lt_of_lt_of_le hApos h𝓛A
  have h𝓛K : 𝓛 ≤ K * Real.log |γ| := by
    have h1 : Real.log (2 * |γ| + 2) ≤ 2 * Real.log |γ| := by
      have h := Real.log_le_log (show (0 : ℝ) < 2 * |γ| + 2 by positivity)
        (show 2 * |γ| + 2 ≤ |γ| * |γ| by nlinarith)
      rw [Real.log_mul (by linarith) (by linarith)] at h
      linarith
    have h2 : A ≤ A * Real.log |γ| := le_mul_of_one_le_right hApos.le hlogγ
    have h3 : M * Real.log (2 * |γ| + 2) ≤ M * (2 * Real.log |γ|) :=
      mul_le_mul_of_nonneg_left h1 hM0
    rw [hK]; nlinarith
  -- exponential bounds from growth
  have hexp_bound : ∀ (C : ℝ) (m : ℕ) (x : ℝ), 0 ≤ C → 0 ≤ x → x ≤ 2 * |γ| + 2 →
      Real.log (C + 1) + (m : ℝ) * Real.log (2 * |γ| + 2) ≤ 𝓛 →
      C * x ^ m ≤ Real.exp 𝓛 := by
    intro C m x hC hx hx2 hle
    have hxx : C * x ^ m ≤ (C + 1) * (2 * |γ| + 2) ^ m := by
      gcongr
      linarith
    refine hxx.trans ?_
    rw [← Real.exp_log (show (0 : ℝ) < (C + 1) * (2 * |γ| + 2) ^ m by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    exact Real.exp_le_exp.2 hle
  have hr' : (0 : ℝ) ≤ 1 / r := by positivity
  have hm1M : (m1 : ℝ) ≤ M := by
    rw [hM]; have := Nat.cast_nonneg (α := ℝ) m2; linarith
  have hm2M : (m2 : ℝ) ≤ M := by
    rw [hM]; have := Nat.cast_nonneg (α := ℝ) m1; linarith
  have hlogC1A : Real.log (C1 + 1) ≤ A := by
    rw [hA]; linarith
  have hlogC2A : Real.log (C2 + 1) ≤ A := by
    rw [hA]; linarith
  have hlogCZA : Real.log CZ ≤ A := by
    rw [hA]; linarith
  have hC₀A : C₀ ≤ A := by
    rw [hA]; linarith
  have hL1 : Real.log (C1 + 1) + (m1 : ℝ) * Real.log (2 * |γ| + 2) ≤ 𝓛 := by
    have := mul_le_mul_of_nonneg_right hm1M hlog2
    rw [h𝓛def]; linarith
  have hL2 : Real.log (C2 + 1) + (m2 : ℝ) * Real.log (2 * |γ| + 2) ≤ 𝓛 := by
    have := mul_le_mul_of_nonneg_right hm2M hlog2
    rw [h𝓛def]; linarith
  have hexpCZ : Real.exp (-𝓛) ≤ 1 / CZ := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by linarith)
    rw [← Real.exp_log (show (0 : ℝ) < CZ by linarith)]
    exact Real.exp_le_exp.2 (hlogCZA.trans h𝓛A)
  -- ball geometry
  have hball_re : ∀ (σ : ℝ) (w z : ℂ), 1 < σ → σ ≤ 1 + r → z ∈ closedBall ((σ : ℂ) + w) r →
      w.re = 0 → -1 < z.re ∧ z.re < 4 := by
    intro σ w z h1 h2 hz hw
    have := abs_re_le_norm (z - ((σ : ℂ) + w))
    rw [← dist_eq_norm] at this
    have hd : dist z ((σ : ℂ) + w) ≤ r := hz
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, hw, add_zero] at this
    constructor <;> linarith [neg_abs_le (z.re - σ), le_abs_self (z.re - σ)]
  have hball_im : ∀ (σ : ℝ) (w z : ℂ), z ∈ closedBall ((σ : ℂ) + w) r →
      |w.im| - r ≤ |z.im| ∧ |z.im| ≤ |w.im| + r := by
    intro σ w z hz
    have := abs_im_le_norm (z - ((σ : ℂ) + w))
    rw [← dist_eq_norm] at this
    have hd : dist z ((σ : ℂ) + w) ≤ r := hz
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, zero_add] at this
    constructor
    · have := abs_sub_abs_le_abs_sub w.im z.im
      rw [abs_sub_comm] at this
      linarith
    · have := abs_sub_abs_le_abs_sub z.im w.im
      linarith
  have him1 : ((γ : ℂ) * I).im = γ := by simp
  have him2 : (2 * (γ : ℂ) * I).im = 2 * γ := by simp
  have hre1 : ((γ : ℂ) * I).re = 0 := by simp
  have hre2 : (2 * (γ : ℂ) * I).re = 0 := by simp
  have habs2 : |2 * γ| = 2 * |γ| := by rw [abs_mul]; norm_num
  have e2 : ∀ σ : ℝ, (σ : ℂ) + 2 * (γ : ℂ) * I = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I := fun σ => by
    push_cast; ring
  have hs_eq : s = (β : ℂ) + (γ : ℂ) * I := (Complex.re_add_im s).symm
  have key := Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
    (heckeLFunction χ) (heckeLFunction (χ * χ)) β γ r 𝓛 C₀ hr0 (by linarith)
    (by
      have := mul_le_mul_of_nonneg_left (show 1 / r ≤ 𝓛 from hA0.trans h𝓛A) hr0.le
      rwa [mul_one_div_cancel hr0.ne'] at this)
    hC₀ (hC₀A.trans h𝓛A)
    (by rw [← hs_eq]; exact hzero)
    (fun s hs => (analytic_ne_zero_re_gt_one χ hs).2.1)
    (fun s hs => (analytic_ne_zero_re_gt_one (χ * χ) hs).2.1)
    (fun σ h1 h2 z hz => by
      obtain ⟨hz1, hz2⟩ := hball_re σ _ z h1 h2 hz hre1
      obtain ⟨hz3, -⟩ := hball_im σ _ z hz
      rw [him1] at hz3
      exact hTa1 z hz1 hz2 (by linarith))
    (fun σ h1 h2 z hz => by
      obtain ⟨hz1, hz2⟩ := hball_re σ _ z h1 h2 hz hre2
      obtain ⟨hz3, -⟩ := hball_im σ _ z hz
      rw [him2, habs2] at hz3
      exact hTa2 z hz1 hz2 (by linarith))
    (fun σ h1 h2 z hz => by
      obtain ⟨hz1, hz2⟩ := hball_re σ _ z h1 h2 hz hre1
      obtain ⟨hz3, hz4⟩ := hball_im σ _ z hz
      rw [him1] at hz3 hz4
      exact (hg1 z hz1.le hz2.le (by linarith)).trans
        (hexp_bound C1 m1 |z.im| hC1 (abs_nonneg _) (by linarith [abs_nonneg γ]) hL1))
    (fun σ h1 h2 z hz => by
      obtain ⟨hz1, hz2⟩ := hball_re σ _ z h1 h2 hz hre2
      obtain ⟨hz3, hz4⟩ := hball_im σ _ z hz
      rw [him2, habs2] at hz3 hz4
      exact (hg2 z hz1.le hz2.le (by linarith)).trans
        (hexp_bound C2 m2 |z.im| hC2 (abs_nonneg _) (by linarith) hL2))
    (fun σ h1 h2 => by
      have hlo := lower_bound_on_line χ hCZ h1 (by linarith) γ
      have hs1 : 0 < σ - 1 := by linarith
      calc (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ (σ - 1) * (1 / CZ) := by
            rw [sq, mul_assoc]
            apply mul_le_mul_of_nonneg_left _ hs1.le
            calc (σ - 1) * Real.exp (-𝓛) ≤ 1 * Real.exp (-𝓛) :=
                  mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
              _ ≤ 1 / CZ := by rw [one_mul]; exact hexpCZ
        _ = (σ - 1) / CZ := by ring
        _ ≤ _ := hlo)
    (fun σ h1 h2 => by
      have hlo := lower_bound_on_line (χ * χ) hCZ h1 (by linarith) (2 * γ)
      rw [e2]
      have hs1 : 0 < σ - 1 := by linarith
      calc (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ (σ - 1) * (1 / CZ) := by
            rw [sq, mul_assoc]
            apply mul_le_mul_of_nonneg_left _ hs1.le
            calc (σ - 1) * Real.exp (-𝓛) ≤ 1 * Real.exp (-𝓛) :=
                  mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
              _ ≤ 1 / CZ := by rw [one_mul]; exact hexpCZ
        _ = (σ - 1) / CZ := by ring
        _ ≤ _ := hlo)
    (fun σ h1 h2 => by
      have h341 := logDeriv_euler_341 χ σ h1 γ
      have hre : ∀ u : ℝ, 1 < ((σ : ℂ) + (u : ℂ) * I).re := fun u => by simpa using h1
      rw [← logDeriv_eq_euler (1 : HeckeCharacter F) (s := (σ : ℂ)) (by simpa using h1),
        ← logDeriv_eq_euler χ (hre γ), ← logDeriv_eq_euler (χ * χ) (hre (2 * γ))] at h341
      rw [e2]
      have hdz := hDZ σ h1 (by linarith)
      linarith)
  -- conclusion
  have hfin : c / Real.log |γ| ≤ r / (20000 * 𝓛) := by
    rw [hc, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left h𝓛K (show (0 : ℝ) ≤ r * 20000 by positivity)
    nlinarith
  have : 1 - β < c / Real.log |γ| := by
    have h' : 1 - c / Real.log |s.im| < s.re := hs
    rw [← hγ, ← hβ] at h'
    linarith
  linarith

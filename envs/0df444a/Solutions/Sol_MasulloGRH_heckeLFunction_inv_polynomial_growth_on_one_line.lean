-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_inv_polynomial_growth_on_one_line
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T13:57:24.455294+00:00
-- url     : https://prove2.me/submissions/2b591574-5dd8-40dc-bb10-2fe232ee95be

import Definitions.Def_MasulloGRH_HeckeLFunction
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

-- ===== from B1.lean =====

namespace MasulloGRH
namespace Aux_HL
open Filter Topology NumberField IsDedekindDomain

/-! ### No small subgroups in the circle -/

lemma circle_re_sq (z : Circle) : ((z ^ 2 : Circle) : ℂ).re = 2 * (z : ℂ).re ^ 2 - 1 := by
  have h := Circle.normSq_coe z
  rw [Complex.normSq_apply] at h
  rw [pow_two, Circle.coe_mul, Complex.mul_re]
  nlinarith

lemma circle_re_le_one (z : Circle) : (z : ℂ).re ≤ 1 := by
  have := Complex.re_le_norm (z : ℂ)
  rwa [Circle.norm_coe] at this

/-- if all `2^m`-th powers of `z` have positive real part, `z = 1`. -/
theorem circle_eq_one_of_pow (z : Circle) (h : ∀ m : ℕ, 0 < ((z ^ (2 ^ m) : Circle) : ℂ).re) :
    z = 1 := by
  have key : ∀ m : ℕ, (2 : ℝ) ^ m * (1 - (z : ℂ).re) ≤ 1 - ((z ^ (2 ^ m) : Circle) : ℂ).re := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : z ^ (2 ^ (m + 1)) = (z ^ (2 ^ m)) ^ 2 := by rw [← pow_mul, pow_succ]
      rw [e, circle_re_sq]
      set x := ((z ^ (2 ^ m) : Circle) : ℂ).re
      have hx : 0 < x := h m
      have hx1 : x ≤ 1 := circle_re_le_one _
      rw [pow_succ]
      nlinarith
  have hre : (z : ℂ).re = 1 := by
    by_contra hne
    have hd : 0 < 1 - (z : ℂ).re := by
      have := circle_re_le_one z; exact sub_pos.2 (lt_of_le_of_ne this hne)
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
    have h1 := key m
    have h2 : 1 - ((z ^ (2 ^ m) : Circle) : ℂ).re < 1 := by linarith [h m]
    have : (2 : ℝ) ^ m * (1 - (z : ℂ).re) < 1 := lt_of_le_of_lt h1 h2
    rw [div_lt_iff₀ hd] at hm
    linarith
  have h := Circle.normSq_coe z
  rw [Complex.normSq_apply, hre] at h
  have him : (z : ℂ).im = 0 := by nlinarith
  apply Circle.ext
  apply Complex.ext <;> simp [hre, him]

/-! ### Coordinates of ideles -/

variable {F : Type*} [Field F] [NumberField F]

local notation "A" => AdeleRing (𝓞 F) F

lemma fin_mul (g h : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    ((g * h : IdeleGroup F) : A).2 v = (g : A).2 v * (h : A).2 v := rfl

lemma inf_mul (g h : IdeleGroup F) :
    ((g * h : IdeleGroup F) : A).1 = (g : A).1 * (h : A).1 := rfl

lemma fin_mul_inv' (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : A).2 v * ((g⁻¹ : IdeleGroup F) : A).2 v = 1 := by
  have := congrArg (fun a : A => a.2 v) g.mul_inv
  exact this

lemma inf_mul_inv' (g : IdeleGroup F) :
    (g : A).1 * ((g⁻¹ : IdeleGroup F) : A).1 = 1 := by
  have := congrArg (fun a : A => a.1) g.mul_inv
  exact this

/-- the "level" subsets `U(S, ε)` of the integral units with trivial archimedean part. -/
def levelSet (S : Set (HeightOneSpectrum (𝓞 F))) (ε : HeightOneSpectrum (𝓞 F) → ℝ) :
    Set (IdeleGroup F) :=
  {g | (g : A).1 = 1 ∧ (∀ v, (g : A).2 v ∈ v.adicCompletionIntegers F ∧
      ((g⁻¹ : IdeleGroup F) : A).2 v ∈ v.adicCompletionIntegers F) ∧
    ∀ v ∈ S, ‖(g : A).2 v - 1‖ < ε v}

lemma norm_le_one_of_mem {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr hx

lemma levelSet_mul {S : Set (HeightOneSpectrum (𝓞 F))} {ε : HeightOneSpectrum (𝓞 F) → ℝ}
    {g h : IdeleGroup F} (hg : g ∈ levelSet S ε) (hh : h ∈ levelSet S ε) :
    g * h ∈ levelSet S ε := by
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨h1, h2, h3⟩ := hh
  refine ⟨by rw [inf_mul, g1, h1, one_mul], fun v => ⟨?_, ?_⟩, fun v hv => ?_⟩
  · rw [fin_mul]; exact mul_mem (g2 v).1 (h2 v).1
  · rw [mul_inv_rev, fin_mul]; exact mul_mem (h2 v).2 (g2 v).2
  · rw [fin_mul]
    have e : (g : A).2 v * (h : A).2 v - 1 = (g : A).2 v * ((h : A).2 v - 1) + ((g : A).2 v - 1) := by
      ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ (g3 v hv))
    rw [norm_mul]
    calc ‖(g : A).2 v‖ * ‖(h : A).2 v - 1‖ ≤ 1 * ‖(h : A).2 v - 1‖ :=
          mul_le_mul_of_nonneg_right (norm_le_one_of_mem (g2 v).1) (norm_nonneg _)
      _ < ε v := by rw [one_mul]; exact h3 v hv

lemma levelSet_pow {S : Set (HeightOneSpectrum (𝓞 F))} {ε : HeightOneSpectrum (𝓞 F) → ℝ}
    {g : IdeleGroup F} (hg : g ∈ levelSet S ε) (n : ℕ) (hn : 0 < n) : g ^ n ∈ levelSet S ε := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simpa using hg
    · rw [pow_succ]; exact levelSet_mul (ih hn') hg

/-- **Conductor lemma**: a Hecke character is trivial on some level set. -/
theorem exists_levelSet_trivial (χ : HeckeCharacter F) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (ε : HeightOneSpectrum (𝓞 F) → ℝ), S.Finite ∧
      (∀ v, 0 < ε v) ∧ ∀ g ∈ levelSet S ε, χ (QuotientGroup.mk g) = 1 := by
  classical
  -- the open neighbourhood `V` of `1` where `Re χ > 0`
  let c : IdeleGroup F → Circle := fun g => χ (QuotientGroup.mk g)
  have hc : Continuous c := χ.continuous.comp continuous_quotient_mk'
  let V : Set (IdeleGroup F) := c ⁻¹' {z | 0 < (z : ℂ).re}
  have hV : V ∈ 𝓝 (1 : IdeleGroup F) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    have hO : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (by fun_prop : Continuous (fun z : Circle => (z : ℂ))))
    refine hO.mem_nhds ?_
    show 0 < ((c 1 : Circle) : ℂ).re
    simp [c]
  -- pull back along the embedding into `A × Aᵐᵒᵖ`
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  let P := (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F
  let sm : P → FiniteAdeleRing (𝓞 F) F := RestrictedProduct.structureMap _ _ _
  have hsm : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
  let Ψ : P × P → A × Aᵐᵒᵖ := fun p => ((1, sm p.1), MulOpposite.op (1, sm p.2))
  have hΨ : Continuous Ψ := by
    refine Continuous.prodMk (continuous_const.prodMk (hsm.comp continuous_fst)) ?_
    exact MulOpposite.continuous_op.comp (continuous_const.prodMk (hsm.comp continuous_snd))
  have hΨ1 : Ψ (1, 1) = Units.embedProduct A 1 := by
    simp only [Ψ, Units.embedProduct_apply, Units.val_one, inv_one]
    congr 2 <;> (ext v; rfl)
  have hW' : Ψ ⁻¹' W ∈ 𝓝 ((1 : P), (1 : P)) := hΨ.continuousAt.preimage_mem_nhds (hΨ1 ▸ hW)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hW'
  obtain ⟨t1, ht1, t2, ht2, ht⟩ := hW'
  rw [nhds_pi, Filter.mem_pi] at ht1 ht2
  obtain ⟨I1, hI1, u1, hu1, hIu1⟩ := ht1
  obtain ⟨I2, hI2, u2, hu2, hIu2⟩ := ht2
  -- radii
  have hrad : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Set (v.adicCompletionIntegers F)), u ∈ 𝓝 (1 : v.adicCompletionIntegers F) →
      ∃ r > 0, ∀ x : v.adicCompletionIntegers F, ‖(x : v.adicCompletion F) - 1‖ < r → x ∈ u := by
    intro v u hu
    rw [mem_nhds_subtype] at hu
    obtain ⟨u', hu', hsub⟩ := hu
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hu'
    refine ⟨r, hr, fun x hx => hsub (hball ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact hx
  choose r1 hr1 hr1u using fun v => hrad v (u1 v) (hu1 v)
  choose r2 hr2 hr2u using fun v => hrad v (u2 v) (hu2 v)
  refine ⟨I1 ∪ I2, fun v => min (r1 v) (r2 v), hI1.union hI2, fun v => lt_min (hr1 v) (hr2 v), ?_⟩
  -- every element of the level set lands in `V`
  have hmemV : ∀ g ∈ levelSet (I1 ∪ I2) (fun v => min (r1 v) (r2 v)), g ∈ V := by
    intro g hg
    obtain ⟨g1, g2, g3⟩ := hg
    apply hWV
    let a : P := fun v => ⟨(g : A).2 v, (g2 v).1⟩
    let b : P := fun v => ⟨((g⁻¹ : IdeleGroup F) : A).2 v, (g2 v).2⟩
    have hab : Units.embedProduct A g = Ψ (a, b) := by
      have hinv1 : ((g⁻¹ : IdeleGroup F) : A).1 = 1 := by
        have := inf_mul_inv' g; rwa [g1, one_mul] at this
      simp only [Ψ, Units.embedProduct_apply]
      congr 1
      · apply Prod.ext
        · exact g1
        · ext v; rfl
      · congr 1
        apply Prod.ext
        · exact hinv1
        · ext v; rfl
    rw [Set.mem_preimage, hab]
    apply ht
    refine ⟨hIu1 fun v hv => hr1u v _ ?_, hIu2 fun v hv => hr2u v _ ?_⟩
    · exact (g3 v (Or.inl hv)).trans_le (min_le_left _ _)
    · -- `‖g⁻¹_v - 1‖ = ‖g_v - 1‖`
      have hnorm : ‖(g : A).2 v‖ = 1 := by
        have h1 := norm_le_one_of_mem (g2 v).1
        have h2 := norm_le_one_of_mem (g2 v).2
        have h3 : ‖(g : A).2 v‖ * ‖((g⁻¹ : IdeleGroup F) : A).2 v‖ = 1 := by
          rw [← norm_mul, fin_mul_inv', norm_one]
        nlinarith [norm_nonneg ((g : A).2 v), norm_nonneg (((g⁻¹ : IdeleGroup F) : A).2 v)]
      have e : ((g⁻¹ : IdeleGroup F) : A).2 v - 1 =
          -(((g⁻¹ : IdeleGroup F) : A).2 v * ((g : A).2 v - 1)) := by
        have := fin_mul_inv' g v
        linear_combination this
      have hnorm' : ‖((g⁻¹ : IdeleGroup F) : A).2 v‖ = 1 := by
        have h3 : ‖(g : A).2 v‖ * ‖((g⁻¹ : IdeleGroup F) : A).2 v‖ = 1 := by
          rw [← norm_mul, fin_mul_inv', norm_one]
        rw [hnorm, one_mul] at h3; exact h3
      show ‖((g⁻¹ : IdeleGroup F) : A).2 v - 1‖ < r2 v
      rw [e, norm_neg, norm_mul, hnorm', one_mul]
      exact (g3 v (Or.inr hv)).trans_le (min_le_right _ _)
  intro g hg
  apply circle_eq_one_of_pow
  intro m
  have := hmemV _ (levelSet_pow hg (2 ^ m) (by positivity))
  simpa [V, c, map_pow] using this

lemma ideleSingle_inf (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    (ideleSingle v x : A).1 = 1 := rfl

open Classical in
lemma ideleSingle_fin_raw (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ)
    (w : HeightOneSpectrum (𝓞 F)) :
    (ideleSingle v x : A).2 w =
      ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletion F)ˣ) v x w :
        (w.adicCompletion F)ˣ) : w.adicCompletion F) := by
  rfl

open Classical in
lemma ideleSingle_fin_self (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    (ideleSingle v x : A).2 v = x := by
  rw [ideleSingle_fin_raw, Pi.mulSingle_eq_same]

open Classical in
lemma ideleSingle_fin_ne (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ)
    (w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) :
    (ideleSingle v x : A).2 w = 1 := by
  rw [ideleSingle_fin_raw, Pi.mulSingle_eq_of_ne h, Units.val_one]

lemma fin_inv_eq (g : IdeleGroup F) (w : HeightOneSpectrum (𝓞 F)) :
    ((g⁻¹ : IdeleGroup F) : A).2 w = ((g : A).2 w)⁻¹ := by
  have h := fin_mul_inv' g w
  have h0 : (g : A).2 w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  field_simp
  rw [mul_comm]; exact h

lemma ideleSingle_mem_levelSet {S : Set (HeightOneSpectrum (𝓞 F))}
    {ε : HeightOneSpectrum (𝓞 F) → ℝ} (hε : ∀ v, 0 < ε v)
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ)
    (hx : Valued.v (x : v.adicCompletion F) = 1) (hS : v ∈ S → ‖(x : v.adicCompletion F) - 1‖ < ε v) :
    ideleSingle v x ∈ levelSet S ε := by
  classical
  refine ⟨ideleSingle_inf v x, fun w => ?_, fun w hw => ?_⟩
  · rw [fin_inv_eq]
    by_cases h : w = v
    · subst h
      rw [ideleSingle_fin_self]
      refine ⟨?_, ?_⟩
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hx, inv_one]
    · rw [ideleSingle_fin_ne v x w h, inv_one]
      exact ⟨one_mem _, one_mem _⟩
  · by_cases h : w = v
    · subst h; rw [ideleSingle_fin_self]; exact hS hw
    · rw [ideleSingle_fin_ne v x w h, sub_self, norm_zero]; exact hε w

/-- the data of a conductor: a finite set `S` of places and radii `ε`. -/
theorem exists_conductor (χ : HeckeCharacter F) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (ε : HeightOneSpectrum (𝓞 F) → ℝ), S.Finite ∧
      (∀ v, 0 < ε v) ∧ (∀ g ∈ levelSet S ε, χ (QuotientGroup.mk g) = 1) ∧
      (∀ v, v ∉ S → χ.IsUnramifiedAt v) ∧
      (∀ v (x : (v.adicCompletion F)ˣ), Valued.v (x : v.adicCompletion F) = 1 →
        ‖(x : v.adicCompletion F) - 1‖ < ε v → χ.localComponent v x = 1) := by
  obtain ⟨S, ε, hS, hε, htriv⟩ := exists_levelSet_trivial χ
  refine ⟨S, ε, hS, hε, htriv, fun v hv x hx => ?_, fun v x hx hx1 => ?_⟩
  · unfold HeckeCharacter.localComponent
    rw [htriv _ (ideleSingle_mem_levelSet hε v x hx (fun h => absurd h hv))]
    rfl
  · unfold HeckeCharacter.localComponent
    rw [htriv _ (ideleSingle_mem_levelSet hε v x hx (fun _ => hx1))]
    rfl

/-! ### χ on integral ideles: the ideal character -/

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

/-- the chosen uniformizer used in `primeValue`. -/
noncomputable def unif (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ :=
  (exists_uniformizer v).choose

theorem unif_spec (v : HeightOneSpectrum (𝓞 F)) : IsUniformizerAt v (unif v) :=
  (exists_uniformizer v).choose_spec

theorem primeValue_eq (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hv : χ.IsUnramifiedAt v) : ∃ π : (v.adicCompletion F)ˣ, IsUniformizerAt v π ∧
      χ.primeValue v = χ.localComponent v π := by
  unfold HeckeCharacter.primeValue
  have h : χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x :=
    ⟨hv, exists_uniformizer v⟩
  rw [dif_pos h]
  exact ⟨_, h.2.choose_spec, rfl⟩

/-- coordinate homomorphisms. -/
noncomputable def finCoord (w : HeightOneSpectrum (𝓞 F)) : IdeleGroup F →* w.adicCompletion F where
  toFun g := (g : A).2 w
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def infCoord : IdeleGroup F →* InfiniteAdeleRing F where
  toFun g := (g : A).1
  map_one' := rfl
  map_mul' _ _ := rfl

lemma ideleSingle_mul (v : HeightOneSpectrum (𝓞 F)) (x y : (v.adicCompletion F)ˣ) :
    ideleSingle v (x * y) = ideleSingle v x * ideleSingle v y := by
  apply Units.ext
  apply Prod.ext
  · show (1 : InfiniteAdeleRing F) = 1 * 1
    rw [one_mul]
  · apply RestrictedProduct.ext; intro w
    show (ideleSingle v (x * y) : A).2 w = (ideleSingle v x : A).2 w * (ideleSingle v y : A).2 w
    by_cases h : w = v
    · subst h; rw [ideleSingle_fin_self, ideleSingle_fin_self, ideleSingle_fin_self, Units.val_mul]
    · rw [ideleSingle_fin_ne _ _ _ h, ideleSingle_fin_ne _ _ _ h, ideleSingle_fin_ne _ _ _ h,
        one_mul]

lemma ideleSingle_one (v : HeightOneSpectrum (𝓞 F)) : ideleSingle v 1 = 1 := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext; intro w
    show (ideleSingle v 1 : A).2 w = 1
    by_cases h : w = v
    · subst h; rw [ideleSingle_fin_self, Units.val_one]
    · rw [ideleSingle_fin_ne _ _ _ h]

lemma ideleSingle_pow (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) (n : ℕ) :
    ideleSingle v (x ^ n) = ideleSingle v x ^ n := by
  induction n with
  | zero => simp [ideleSingle_one]
  | succ n ih => rw [pow_succ, ideleSingle_mul, ih, pow_succ]

lemma localComponent_pow (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x : (v.adicCompletion F)ˣ) (n : ℕ) :
    χ.localComponent v (x ^ n) = χ.localComponent v x ^ n := by
  unfold HeckeCharacter.localComponent
  rw [ideleSingle_pow, QuotientGroup.mk_pow, map_pow, Circle.coe_pow]

open Classical in
lemma finCoord_ideleSingle_prod (T : Finset (HeightOneSpectrum (𝓞 F)))
    (f : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    finCoord w (∏ v ∈ T, ideleSingle v (f v)) = if w ∈ T then (f w : w.adicCompletion F) else 1 := by
  classical
  rw [map_prod]
  split_ifs with hw
  · rw [Finset.prod_eq_single w]
    · exact ideleSingle_fin_self w (f w)
    · intro b _ hb; exact ideleSingle_fin_ne b (f b) w (Ne.symm hb)
    · intro h; exact absurd hw h
  · refine Finset.prod_eq_one fun b hb => ?_
    exact ideleSingle_fin_ne b (f b) w (fun h => hw (h ▸ hb))

lemma infCoord_ideleSingle_prod (T : Finset (HeightOneSpectrum (𝓞 F)))
    (f : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) :
    infCoord (∏ v ∈ T, ideleSingle v (f v)) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one fun b _ => rfl

/-- **χ on integral ideles** with trivial archimedean part, congruent to `1` at the conductor:
the value is the monomial in the prime values given by the valuation exponents. -/
theorem chi_integral_idele (χ : HeckeCharacter F) (S : Set (HeightOneSpectrum (𝓞 F)))
    (ε : HeightOneSpectrum (𝓞 F) → ℝ) (htriv : ∀ g ∈ levelSet S ε, χ (QuotientGroup.mk g) = 1)
    (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v)
    (g : IdeleGroup F) (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) (hg1 : (g : A).1 = 1)
    (hgk : ∀ v, Valued.v ((g : A).2 v) = WithZero.exp (-(k v : ℤ)))
    (hS : ∀ v ∈ S, ‖(g : A).2 v - 1‖ < ε v) (hkS : ∀ v ∈ S, k v = 0) :
    ((χ (QuotientGroup.mk g) : Circle) : ℂ) = k.prod fun v n => χ.primeValue v ^ n := by
  classical
  -- uniformizers realising the prime values
  have hπ : ∀ v, ∃ π : (v.adicCompletion F)ˣ, IsUniformizerAt v π ∧
      (v ∉ S → χ.primeValue v = χ.localComponent v π) := by
    intro v
    by_cases hv : v ∈ S
    · exact ⟨unif v, unif_spec v, fun h => absurd hv h⟩
    · obtain ⟨π, h1, h2⟩ := primeValue_eq χ v (hun v hv)
      exact ⟨π, h1, fun _ => h2⟩
  choose π hπu hπv using hπ
  let T := k.support
  let P : IdeleGroup F := ∏ v ∈ T, ideleSingle v (π v ^ k v)
  let u : IdeleGroup F := g * P⁻¹
  have hPw : ∀ w, finCoord w P = if w ∈ T then ((π w ^ k w : (w.adicCompletion F)ˣ) :
      w.adicCompletion F) else 1 :=
    fun w => finCoord_ideleSingle_prod T (fun v => π v ^ k v) w
  have hPinv : ∀ w, finCoord w P⁻¹ * finCoord w P = 1 := by
    intro w; rw [← map_mul, inv_mul_cancel, map_one]
  have hval_pi : ∀ w, Valued.v ((π w ^ k w : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
      WithZero.exp (-(k w : ℤ)) := by
    intro w
    rw [Units.val_pow_eq_pow_val, map_pow, hπu w, ← WithZero.exp_nsmul]
    congr 1
    simp
  -- coordinates of `u` have valuation one
  have hu_val : ∀ w, Valued.v ((u : A).2 w) = 1 := by
    intro w
    have e : (u : A).2 w = finCoord w g * finCoord w P⁻¹ := rfl
    rw [e, map_mul]
    have h2 : Valued.v (finCoord w P⁻¹) * Valued.v (finCoord w P) = 1 := by
      rw [← map_mul, hPinv, map_one]
    rw [hPw] at h2
    show Valued.v ((g : A).2 w) * Valued.v (finCoord w P⁻¹) = 1
    rw [hgk]
    split_ifs at h2 with hw
    · rw [hval_pi] at h2
      calc WithZero.exp (-(k w : ℤ)) * Valued.v (finCoord w P⁻¹)
          = Valued.v (finCoord w P⁻¹) * WithZero.exp (-(k w : ℤ)) := mul_comm _ _
        _ = 1 := h2
    · rw [map_one, mul_one] at h2
      have hk0 : k w = 0 := by simpa [T] using hw
      rw [h2, hk0]; simp
  have hu_S : ∀ w ∈ S, (u : A).2 w = (g : A).2 w := by
    intro w hw
    have hwT : w ∉ T := by simp [T, hkS w hw]
    have e : (u : A).2 w = finCoord w g * finCoord w P⁻¹ := rfl
    have h2 := hPinv w
    rw [hPw, if_neg hwT, mul_one] at h2
    rw [e, h2, mul_one]; rfl
  have hu : u ∈ levelSet S ε := by
    refine ⟨?_, fun w => ⟨?_, ?_⟩, fun w hw => ?_⟩
    · have e : (u : A).1 = infCoord g * infCoord P⁻¹ := rfl
      have h1 : infCoord P⁻¹ * infCoord P = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rw [infCoord_ideleSingle_prod, mul_one] at h1
      rw [e, h1, mul_one]; exact hg1
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu_val]
    · rw [fin_inv_eq, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu_val, inv_one]
    · rw [hu_S w hw]; exact hS w hw
  have hgu : g = u * P := by simp [u]
  rw [hgu, QuotientGroup.mk_mul, map_mul, htriv u hu, one_mul]
  simp only [P, QuotientGroup.mk_prod, map_prod]
  rw [show ((∏ v ∈ T, χ (QuotientGroup.mk (ideleSingle v (π v ^ k v))) : Circle) : ℂ) =
      ∏ v ∈ T, ((χ (QuotientGroup.mk (ideleSingle v (π v ^ k v))) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  unfold Finsupp.prod
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvS : v ∉ S := fun h => (Finsupp.mem_support_iff.1 hv) (hkS v h)
  show _ = χ.primeValue v ^ k v
  rw [hπv v hvS, ← localComponent_pow]
  rfl


/-- archimedean ideles `(x_∞, 1)`. -/
noncomputable def infIdele : (InfiniteAdeleRing F)ˣ →* IdeleGroup F :=
  (MulEquiv.prodUnits.symm : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ ≃* IdeleGroup F).toMonoidHom.comp
    (MonoidHom.inl _ _)

/-- the archimedean component `χ_∞` of a Hecke character, on `F_∞ˣ`. -/
noncomputable def chiInf (χ : HeckeCharacter F) (x : (InfiniteAdeleRing F)ˣ) : ℂ :=
  ((χ (QuotientGroup.mk (infIdele x)) : Circle) : ℂ)

lemma chiInf_mul (χ : HeckeCharacter F) (x y : (InfiniteAdeleRing F)ˣ) :
    chiInf χ (x * y) = chiInf χ x * chiInf χ y := by
  unfold chiInf
  rw [map_mul, QuotientGroup.mk_mul, map_mul, Circle.coe_mul]

/-- the diagonal image of `ξ ∈ Fˣ` in `F_∞ˣ`. -/
noncomputable def diagInf : Fˣ →* (InfiniteAdeleRing F)ˣ :=
  Units.map (algebraMap F (InfiniteAdeleRing F)).toMonoidHom

lemma coe_ne_zero_of_units (v : HeightOneSpectrum (𝓞 F)) (ξ : Fˣ) :
    ((ξ : F) : v.adicCompletion F) ≠ 0 := by
  intro h
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v (ξ : F)
  rw [h, map_zero] at this
  exact (map_ne_zero _).2 ξ.ne_zero this.symm

/-- the image of `ξ ∈ Fˣ` in `F_vˣ`. -/
noncomputable def locUnit (v : HeightOneSpectrum (𝓞 F)) (ξ : Fˣ) : (v.adicCompletion F)ˣ :=
  Units.mk0 _ (coe_ne_zero_of_units v ξ)

/-- **General Hecke relation**: for `ξ ∈ Fˣ` prime to the conductor set `S`,
`χ((ξ)) · χ_∞(ξ) · ∏_{v ∈ S} χ_v(ξ) = 1`. -/
theorem hecke_relation_general (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ε : HeightOneSpectrum (𝓞 F) → ℝ) (hε : ∀ v, 0 < ε v)
    (htriv : ∀ g ∈ levelSet (S : Set (HeightOneSpectrum (𝓞 F))) ε, χ (QuotientGroup.mk g) = 1)
    (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v)
    (ξ : Fˣ) (k : HeightOneSpectrum (𝓞 F) →₀ ℕ)
    (hk : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ : F) = WithZero.exp (-(k v : ℤ)))
    (hkS : ∀ v ∈ S, k v = 0) :
    (k.prod fun v n => χ.primeValue v ^ n) * chiInf χ (diagInf ξ) *
      ∏ v ∈ S, χ.localComponent v (locUnit v ξ) = 1 := by
  classical
  let Q : IdeleGroup F := ∏ v ∈ S, ideleSingle v (locUnit v ξ)
  let g : IdeleGroup F := principalIdele F ξ * (infIdele (diagInf ξ))⁻¹ * Q⁻¹
  have hQinf : infCoord Q = 1 := infCoord_ideleSingle_prod S _
  have hg1 : (g : A).1 = 1 := by
    show infCoord (principalIdele F ξ) * infCoord (infIdele (diagInf ξ))⁻¹ * infCoord Q⁻¹ = 1
    have h1 : infCoord (infIdele (diagInf ξ))⁻¹ * infCoord (infIdele (diagInf ξ)) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : infCoord (infIdele (diagInf ξ)) = infCoord (principalIdele F ξ) := rfl
    have h3 : infCoord Q⁻¹ * infCoord Q = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [hQinf, mul_one] at h3
    rw [h3, mul_one, ← h2, mul_comm]; exact h1
  have hgv : ∀ v, (g : A).2 v = if v ∈ S then 1 else ((ξ : F) : v.adicCompletion F) := by
    intro v
    show finCoord v (principalIdele F ξ) * finCoord v (infIdele (diagInf ξ))⁻¹ * finCoord v Q⁻¹ = _
    have h1 : finCoord v (infIdele (diagInf ξ))⁻¹ * finCoord v (infIdele (diagInf ξ)) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : finCoord v (infIdele (diagInf ξ)) = 1 := rfl
    rw [h2, mul_one] at h1
    have h3 : finCoord v Q⁻¹ * finCoord v Q = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hQ : finCoord v Q = if v ∈ S then ((locUnit v ξ : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) else 1 := finCoord_ideleSingle_prod S _ v
    have hp : finCoord v (principalIdele F ξ) = ((ξ : F) : v.adicCompletion F) := rfl
    rw [h1, mul_one, hp]
    split_ifs at hQ ⊢ with hv
    · rw [hQ] at h3
      have : finCoord v Q⁻¹ = ((ξ : F) : v.adicCompletion F)⁻¹ := eq_inv_of_mul_eq_one_left h3
      rw [this]
      exact mul_inv_cancel₀ (coe_ne_zero_of_units v ξ)
    · rw [hQ, mul_one] at h3; rw [h3, mul_one]
  have hval := chi_integral_idele χ (S : Set _) ε htriv hun g k hg1
    (fun v => by
      rw [hgv]
      split_ifs with hv
      · rw [map_one, hkS v hv]; simp
      · rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hk])
    (fun v hv => by rw [hgv, if_pos (Finset.mem_coe.1 hv), sub_self, norm_zero]; exact hε v)
    (fun v hv => hkS v (Finset.mem_coe.1 hv))
  have hprin : (QuotientGroup.mk (principalIdele F ξ) : IdeleClassGroup F) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨ξ, rfl⟩
  have hQc : ((χ (QuotientGroup.mk Q) : Circle) : ℂ) = ∏ v ∈ S, χ.localComponent v (locUnit v ξ) := by
    simp only [Q, QuotientGroup.mk_prod, map_prod]
    exact map_prod Circle.coeHom _ _
  rw [← hval, ← hQc]
  unfold chiInf
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  simp [g, hprin]

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

namespace MasulloGRH
namespace Aux_HL

section PoissonPart
open MeasureTheory Real Complex Set Filter Topology
open scoped FourierTransform SchwartzMap

namespace AuxP

variable {ι : Type*} [Fintype ι]

/-- integer point of EuclideanSpace -/
noncomputable def zpt (m : ι → ℤ) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (m i : ℝ))

omit [Fintype ι] in
lemma zpt_injective : Function.Injective (zpt (ι := ι)) := by
  intro a b h
  funext i
  have := congrArg (fun v : EuclideanSpace ℝ ι => v i) h
  simpa [zpt] using this

lemma summable_zpt_rpow (k : ℝ) (hk : (Fintype.card ι : ℝ) < k) :
    Summable (fun m : ι → ℤ => ((1 + ‖zpt m‖) ^ k)⁻¹) := by
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let L : Submodule ℤ (EuclideanSpace ℝ ι) := Submodule.span ℤ (Set.range b)
  have hmem : ∀ m : ι → ℤ, zpt m ∈ L := by
    intro m
    rw [Module.Basis.mem_span_iff_repr_mem]
    intro i
    exact ⟨m i, by simp [b, zpt]⟩
  have hrank : Module.finrank ℤ L = Fintype.card ι := by
    rw [Module.finrank_eq_card_basis (b.restrictScalars ℤ)]
  have hs := ZLattice.summable_norm_rpow L (-k) (by rw [hrank]; linarith)
  let j : (ι → ℤ) → L := fun m => ⟨zpt m, hmem m⟩
  have hj : Function.Injective j := by
    intro a c h
    exact zpt_injective (congrArg Subtype.val h)
  have hs' := hs.comp_injective hj
  refine Summable.of_norm_bounded_eventually hs' ?_
  have hfin : {m : ι → ℤ | zpt m = 0}.Finite := by
    refine Set.Finite.subset (Set.finite_singleton 0) ?_
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm
    simp only [Set.mem_singleton_iff]
    exact zpt_injective (by rw [hm]; ext i; simp [zpt])
  filter_upwards [hfin.compl_mem_cofinite] with m hm
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hm
  have hpos : 0 < ‖zpt m‖ := norm_pos_iff.mpr hm
  have hn : ‖j m‖ = ‖zpt m‖ := rfl
  simp only [Function.comp_apply, hn]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (norm_nonneg _)]
  exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (norm_nonneg _) (by linarith) (by linarith))

lemma schwartz_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝓢(E, ℂ)) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, (1 + ‖x‖) ^ k * ‖f x‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f,
    by positivity, fun x => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl f x
  simpa [norm_iteratedFDeriv_zero] using this

lemma one_add_norm_le (u v : EuclideanSpace ℝ ι) :
    1 + ‖u‖ ≤ (1 + ‖u + v‖) * (1 + ‖v‖) := by
  have : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc ‖u‖ = ‖(u + v) - v‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le _ _
  nlinarith [norm_nonneg (u + v), norm_nonneg v]

/-- uniform bound on translates -/
lemma schwartz_translate_bound (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : EuclideanSpace ℝ ι) (v : EuclideanSpace ℝ ι),
      ‖f (m + v)‖ ≤ C * (1 + ‖v‖) ^ k * ((1 + ‖m‖) ^ k)⁻¹ := by
  obtain ⟨C, hC, h⟩ := schwartz_decay f k
  refine ⟨C, hC, fun m v => ?_⟩
  have h1 := h (m + v)
  have h2 : (1 + ‖m‖) ^ k ≤ (1 + ‖m + v‖) ^ k * (1 + ‖v‖) ^ k := by
    rw [← mul_pow]; gcongr; exact one_add_norm_le m v
  have hp : 0 < (1 + ‖m‖) ^ k := by positivity
  rw [le_mul_inv_iff₀ hp]
  calc ‖f (m + v)‖ * (1 + ‖m‖) ^ k ≤ ‖f (m + v)‖ * ((1 + ‖m + v‖) ^ k * (1 + ‖v‖) ^ k) := by
        gcongr
    _ = ((1 + ‖m + v‖) ^ k * ‖f (m + v)‖) * (1 + ‖v‖) ^ k := by ring
    _ ≤ C * (1 + ‖v‖) ^ k := by gcongr

lemma summable_schwartz_zpt (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (v : EuclideanSpace ℝ ι) :
    Summable (fun m : ι → ℤ => ‖f (zpt m + v)‖) := by
  obtain ⟨C, hC, h⟩ := schwartz_translate_bound f (Fintype.card ι + 1)
  have hs := summable_zpt_rpow (ι := ι) ((Fintype.card ι + 1 : ℕ) : ℝ) (by push_cast; linarith)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (hs.mul_left (C * (1 + ‖v‖) ^ (Fintype.card ι + 1)))
  rw [Real.rpow_natCast]
  exact h _ v


/-- complex exponential phase -/
noncomputable def ex (t : ℝ) : ℂ := Complex.exp (↑(2 * π * t) * Complex.I)

lemma fourierChar_smul (t : ℝ) (z : ℂ) : (𝐞 t) • z = ex t * z := by
  rw [Circle.smul_def, Real.fourierChar_apply]; rfl

lemma ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  simp only [ex, ← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_int (z : ℤ) : ex z = 1 := by
  simp only [ex]
  have : (↑(2 * π * (z : ℝ)) * Complex.I : ℂ) = (z : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  simp only [ex]; exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_ex : Continuous ex := by
  unfold ex; fun_prop

/-- real-valued integer coordinates -/
def mR (m : ι → ℤ) : ι → ℝ := fun i => (m i : ℝ)

lemma toLp_add_mR (m : ι → ℤ) (x : ι → ℝ) :
    WithLp.toLp 2 (mR m + x) = zpt m + WithLp.toLp 2 x := by
  rfl

lemma inner_zpt (x : ι → ℝ) (n : ι → ℤ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (zpt n) = ∑ i, x i * (n i : ℝ) := by
  simp [zpt, PiLp.inner_apply, mul_comm]

/-- periodization -/
noncomputable def per (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : ι → ℝ) : ℂ :=
  ∑' m : ι → ℤ, Φ (zpt m + WithLp.toLp 2 x)

lemma per_continuous (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) : Continuous (per Φ) := by
  obtain ⟨C, hC, h⟩ := schwartz_translate_bound Φ (Fintype.card ι + 1)
  have hs := summable_zpt_rpow (ι := ι) ((Fintype.card ι + 1 : ℕ) : ℝ) (by push_cast; linarith)
  rw [continuous_iff_continuousAt]
  intro x0
  set R := ‖(WithLp.toLp 2 x0 : EuclideanSpace ℝ ι)‖ + 1
  let s : Set (ι → ℝ) := {x | ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ < R}
  have hso : IsOpen s := isOpen_lt (by fun_prop) continuous_const
  have hx0 : x0 ∈ s := by simp [s, R]
  have hcont : ContinuousOn (per Φ) s := by
    refine continuousOn_tsum (u := fun m => C * (1 + R) ^ (Fintype.card ι + 1) *
      ((1 + ‖zpt m‖) ^ ((Fintype.card ι + 1 : ℕ) : ℝ))⁻¹) (fun m => ?_) (hs.mul_left _) ?_
    · exact (Φ.continuous.comp (continuous_const.add (by fun_prop))).continuousOn
    · intro m x hx
      have h1 := h (zpt m) (WithLp.toLp 2 x)
      rw [Real.rpow_natCast]
      refine h1.trans ?_
      have : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ≤ R := le_of_lt hx
      gcongr
  exact hcont.continuousAt (hso.mem_nhds hx0)

lemma per_periodic (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m0 : ι → ℤ) (x : ι → ℝ) :
    per Φ (mR m0 + x) = per Φ x := by
  unfold per
  conv_rhs => rw [← (Equiv.addRight m0).tsum_eq]
  congr 1; funext m
  congr 1
  rw [toLp_add_mR, ← add_assoc]
  congr 1
  ext i; simp [zpt]

/-- the quotient map to the torus -/
noncomputable def qT (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

lemma qT_isQuotientMap : Topology.IsQuotientMap (qT (ι := ι)) :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

lemma per_factors (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) : Function.FactorsThrough (per Φ) qT := by
  intro a b hab
  have hi : ∀ i, ∃ k : ℤ, b i = (k : ℝ) + a i := by
    intro i
    have h1 := congrFun hab i
    simp only [qT] at h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
    exact ⟨k, by simp at hk; linarith⟩
  choose k hk using hi
  have : b = mR k + a := by funext i; simp [mR, hk i]
  rw [this, per_periodic]

/-- the periodization as a function on the torus -/
noncomputable def perT (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) : C(UnitAddTorus ι, ℂ) :=
  Topology.IsQuotientMap.lift (f := ⟨qT, qT_isQuotientMap.continuous⟩) (qT_isQuotientMap (ι := ι)) ⟨per Φ, per_continuous Φ⟩ (per_factors Φ)

lemma perT_qT (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : ι → ℝ) : perT Φ (qT x) = per Φ x :=
  DFunLike.congr_fun (Topology.IsQuotientMap.lift_comp (f := ⟨qT, qT_isQuotientMap.continuous⟩)
    (qT_isQuotientMap (ι := ι)) ⟨per Φ, per_continuous Φ⟩ (per_factors Φ)) x

lemma mFourier_qT (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier (-n) (qT x) = ex (-(∑ i, x i * (n i : ℝ))) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, qT, Pi.neg_apply, fourier_coe_apply]
  rw [← Complex.exp_sum]
  simp only [ex]
  congr 1
  push_cast
  rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


omit [Fintype ι] in
lemma mem_span_mR (m : ι → ℤ) [Finite ι] :
    mR m ∈ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro i
  exact ⟨m i, by simp [mR]⟩

/-- the integer lattice equivalence -/
noncomputable def eL : (ι → ℤ) ≃ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup :=
  Equiv.ofBijective (fun m => ⟨mR m, mem_span_mR m⟩) (by
    constructor
    · intro a b h
      funext i
      have := congrFun (congrArg Subtype.val h) i
      simpa [mR] using this
    · rintro ⟨γ, hγ⟩
      have h := (Module.Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ ι) γ).mp hγ
      choose m hm using h
      refine ⟨m, ?_⟩
      apply Subtype.ext
      funext i
      simpa [mR] using hm i)

lemma eL_coe (m : ι → ℤ) : ((eL m : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup) :
    ι → ℝ) = mR m := rfl

lemma integrable_comp_toLp (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    Integrable (fun y : ι → ℝ => Φ (WithLp.toLp 2 y)) :=
  ((PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding).mpr Φ.integrable

lemma fourier_zpt (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (n : ι → ℤ) :
    𝓕 (⇑Φ) (zpt n) = ∫ y : ι → ℝ, ex (-(∑ i, y i * (n i : ℝ))) * Φ (WithLp.toLp 2 y) := by
  rw [Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  congr 1; funext y
  rw [fourierChar_smul, inner_zpt]

lemma ex_shift (m n : ι → ℤ) (x : ι → ℝ) :
    ex (-(∑ i, (mR m + x) i * (n i : ℝ))) = ex (-(∑ i, x i * (n i : ℝ))) := by
  have : -(∑ i, (mR m + x) i * (n i : ℝ)) = ((-(∑ i, m i * n i) : ℤ) : ℝ) +
      (-(∑ i, x i * (n i : ℝ))) := by
    simp only [Pi.add_apply, mR, add_mul, Finset.sum_add_distrib]; push_cast; ring
  rw [this, ex_add, ex_int, one_mul]

lemma fourier_zpt_tsum (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (n : ι → ℤ) :
    𝓕 (⇑Φ) (zpt n) = ∑' m : ι → ℤ, ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1),
      ex (-(∑ i, x i * (n i : ℝ))) * Φ (zpt m + WithLp.toLp 2 x) := by
  have hFD := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  rw [ZSpan.fundamentalDomain_pi_basisFun] at hFD
  have hg : Integrable (fun y : ι → ℝ => ex (-(∑ i, y i * (n i : ℝ))) * Φ (WithLp.toLp 2 y)) := by
    refine (integrable_comp_toLp Φ).bdd_mul (c := 1) ?_ ?_
    · exact (continuous_ex.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => (norm_ex _).le
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup :=
    Function.Injective.countable (eL (ι := ι)).symm.injective
  rw [fourier_zpt, hFD.integral_eq_tsum'' _ hg, ← (eL (ι := ι)).tsum_eq]
  congr 1; funext m
  congr 1; funext x
  rw [AddSubgroup.vadd_def, vadd_eq_add, eL_coe, ex_shift, toLp_add_mR]


lemma cube_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1),
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ≤ B := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : ι → ℝ => ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖) (by fun_prop)
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  have := hB x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
  exact this.trans (le_max_left _ _)

lemma coeff_eq (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (perT Φ) n = 𝓕 (⇑Φ) (zpt n) := by
  rw [fourier_zpt_tsum, UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
  have hS : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [hS]
  have hae : (Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1)) =ᵐ[volume]
      (Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1)) :=
    (Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : ι => (volume : Measure ℝ))).trans
      (Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ : ι => (volume : Measure ℝ))).symm
  rw [setIntegral_congr_set hae]
  set S := Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1)
  have hSK : S ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hvol : volume S = 1 := by
    simp [S, volume_pi_pi, Real.volume_Ico]
  have hvol' : volume S < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  let F : (ι → ℤ) → (ι → ℝ) → ℂ := fun m x =>
    ex (-(∑ i, x i * (n i : ℝ))) * Φ (zpt m + WithLp.toLp 2 x)
  have hFc : ∀ m, Continuous (F m) := fun m =>
    (continuous_ex.comp (by fun_prop)).mul (Φ.continuous.comp (continuous_const.add (by fun_prop)))
  have hint : ∀ m, Integrable (F m) (volume.restrict S) := fun m =>
    ((hFc m).continuousOn.integrableOn_compact hK).mono_set hSK
  obtain ⟨C, hC, h⟩ := schwartz_translate_bound Φ (Fintype.card ι + 1)
  obtain ⟨B, hB0, hB⟩ := cube_bound (ι := ι)
  have hs := summable_zpt_rpow (ι := ι) ((Fintype.card ι + 1 : ℕ) : ℝ) (by push_cast; linarith)
  have hbd : ∀ m, ∀ x ∈ S, ‖F m x‖ ≤ C * (1 + B) ^ (Fintype.card ι + 1) *
      ((1 + ‖zpt m‖) ^ ((Fintype.card ι + 1 : ℕ) : ℝ))⁻¹ := by
    intro m x hx
    simp only [F, norm_mul, norm_ex, one_mul]
    rw [Real.rpow_natCast]
    refine (h (zpt m) (WithLp.toLp 2 x)).trans ?_
    have := hB x (hSK hx)
    gcongr
  have hsum : Summable fun m => ∫ x, ‖F m x‖ ∂(volume.restrict S) := by
    refine Summable.of_norm_bounded (hs.mul_left (C * (1 + B) ^ (Fintype.card ι + 1))) ?_
    intro m
    have := norm_setIntegral_le_of_norm_le_const (f := fun x => ‖F m x‖) hvol'
      (fun x hx => by rw [norm_norm]; exact hbd m x hx)
    simp only [Measure.real, hvol, ENNReal.toReal_one, mul_one] at this
    simpa using this
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  refine setIntegral_congr_fun (measurableSet_pi Set.countable_univ.to_subtype |>.mpr
    (Or.inl fun _ _ => measurableSet_Ico)) ?_
  intro x _
  simp only [F]
  rw [show (fun i => ((x i : ℝ) : UnitAddCircle)) = qT x from rfl, mFourier_qT, perT_qT, per,
    smul_eq_mul, ← tsum_mul_left]

theorem poisson (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    Summable (fun m : ι → ℤ => Φ (zpt m)) ∧ Summable (fun n : ι → ℤ => 𝓕 (⇑Φ) (zpt n)) ∧
    ∑' m : ι → ℤ, Φ (zpt m) = ∑' n : ι → ℤ, 𝓕 (⇑Φ) (zpt n) := by
  have h1 : Summable (fun m : ι → ℤ => Φ (zpt m)) :=
    Summable.of_norm (by simpa using summable_schwartz_zpt Φ 0)
  have h2 : Summable (fun n : ι → ℤ => 𝓕 (⇑Φ) (zpt n)) := by
    have := summable_schwartz_zpt (𝓕 Φ) 0
    simp only [add_zero, SchwartzMap.fourier_coe] at this
    exact Summable.of_norm this
  refine ⟨h1, h2, ?_⟩
  have hc : Summable (UnitAddTorus.mFourierCoeff (perT Φ)) := by
    have : UnitAddTorus.mFourierCoeff (perT Φ) = fun n => 𝓕 (⇑Φ) (zpt n) := funext (coeff_eq Φ)
    rw [this]; exact h2
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hc 0
  have h0 : (0 : UnitAddTorus ι) = qT 0 := by funext i; simp [qT]
  rw [h0, perT_qT] at this
  simp only [per] at this
  have hz : (WithLp.toLp 2 (0 : ι → ℝ) : EuclideanSpace ℝ ι) = 0 := rfl
  simp only [hz, add_zero] at this
  rw [← this.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [coeff_eq]
  simp [UnitAddTorus.mFourier, qT, fourier_eval_zero]

end AuxP

end PoissonPart

section PoissonGen
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open AuxP

theorem integral_comp_clequiv (L : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (G : EuclideanSpace ℝ ι → ℂ) :
    ∫ x, G (L x) = ((|LinearMap.det (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|)⁻¹ : ℝ) •
      ∫ x, G x := by
  have hdet : LinearMap.det (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ ι))) hdet
  have hT : MeasurableEmbedding (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) :=
    L.toHomeomorph.measurableEmbedding
  calc ∫ x, G (L x) = ∫ x, G ((L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) x) := rfl
    _ = ∫ y, G y ∂(Measure.map (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) volume) :=
        (hT.integral_map G).symm
    _ = _ := by rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

theorem fourier_affine (H : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (L : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) (c ξ : EuclideanSpace ℝ ι) :
    ‖𝓕 (fun x => H (L x + c)) ξ‖ =
      (|LinearMap.det (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|)⁻¹ *
        ‖𝓕 (⇑H) (ContinuousLinearMap.adjoint
          (L.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ξ)‖ := by
  set η := ContinuousLinearMap.adjoint (L.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ξ
  rw [Real.fourier_eq, Real.fourier_eq]
  let G : EuclideanSpace ℝ ι → ℂ := fun u => ex (-⟪L.symm (u - c), ξ⟫) * H u
  have h1 : ∀ x, 𝐞 (-⟪x, ξ⟫) • H (L x + c) = (fun u => G (u + c)) (L x) := by
    intro x
    simp only [G, add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply, fourierChar_smul]
  simp_rw [h1]
  rw [integral_comp_clequiv L (fun u => G (u + c)), integral_add_right_eq_self G c]
  have h2 : ∀ u, G u = ex (⟪c, η⟫) * (ex (-⟪u, η⟫) * H u) := by
    intro u
    simp only [G]
    have h3 : ⟪η, u - c⟫ = ⟪ξ, L.symm (u - c)⟫ :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    have : ⟪L.symm (u - c), ξ⟫ = ⟪u, η⟫ - ⟪c, η⟫ := by
      calc ⟪L.symm (u - c), ξ⟫ = ⟪ξ, L.symm (u - c)⟫ := real_inner_comm _ _
        _ = ⟪η, u - c⟫ := h3.symm
        _ = ⟪u - c, η⟫ := real_inner_comm _ _
        _ = ⟪u, η⟫ - ⟪c, η⟫ := inner_sub_left _ _ _
    rw [this, ← mul_assoc, ← ex_add]; congr 2; ring
  simp_rw [h2, fourierChar_smul]
  rw [integral_const_mul, norm_smul, norm_mul, norm_ex, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (abs_nonneg _))]

theorem zpt_add_smul (r k : ι → ℤ) (m : ℤ) :
    zpt (r + m • k) = zpt r + (m : ℝ) • zpt k := by
  ext i; simp [zpt]

theorem one_le_norm_zpt (k : ι → ℤ) (hk : k ≠ 0) : 1 ≤ ‖zpt k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push_neg at h; exact hk (funext h)
  have h1 : (1:ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
  have h2 := PiLp.norm_apply_le (zpt k) i
  simp only [zpt, Real.norm_eq_abs] at h2
  exact h1.trans h2

theorem tsum_residues (m : ℕ) [NeZero m] (g : (ι → ℤ) → ℂ) (hg : Summable g) :
    ∑' n, g n = ∑ r : ι → Fin m, ∑' k : ι → ℤ, g (fun i => ((r i : ℕ) : ℤ) + (m : ℤ) * k i) := by
  let E0 : (ι → ℤ) ≃ (ι → Fin m) × (ι → ℤ) :=
    (Equiv.piCongrRight fun _ => Int.divModEquiv m).trans
      ((Equiv.arrowProdEquivProdArrow _ _ _).trans (Equiv.prodComm _ _))
  have hE0 : ∀ p : (ι → Fin m) × (ι → ℤ),
      E0.symm p = fun i => ((p.1 i : ℕ) : ℤ) + (m : ℤ) * p.2 i := by
    rintro ⟨r, k⟩; funext i
    simp [E0, Int.divModEquiv, Equiv.arrowProdEquivProdArrow]; ring
  have hs : Summable (fun p => g (E0.symm p)) := E0.symm.summable_iff.2 hg
  rw [← E0.symm.tsum_eq g, hs.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => tsum_congr fun k => ?_
  rw [hE0]

theorem fourier_err (H : 𝓢(EuclideanSpace ℝ ι, ℂ)) (M : ℕ) (CF : ℝ)
    (hCF : ∀ x, (1 + ‖x‖) ^ M * ‖𝓕 (⇑H) x‖ ≤ CF)
    (L' : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι) (k : ι → ℤ)
    (hk : k ≠ 0) :
    ‖𝓕 (fun x => H (L' x + c)) (zpt k)‖ ≤
      (|LinearMap.det (L' : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|)⁻¹ * CF *
        (2 * ‖(L' : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖) ^ M *
          ((1 + ‖zpt k‖) ^ (M : ℝ))⁻¹ := by
  rw [fourier_affine H L' c (zpt k)]
  set η := ContinuousLinearMap.adjoint (L'.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (zpt k)
  have hdec := hCF η
  have hback : zpt k = ContinuousLinearMap.adjoint
      (L' : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) η := by
    simp only [η]
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
      ContinuousLinearEquiv.coe_symm_comp_coe, ContinuousLinearMap.adjoint_id]
    rfl
  set NL := ‖(L' : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖
  have hkη : ‖zpt k‖ ≤ NL * ‖η‖ := by
    rw [hback]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
  have hk1 := one_le_norm_zpt k hk
  have hkey : 1 + ‖zpt k‖ ≤ 2 * NL * (1 + ‖η‖) := by
    have : NL * ‖η‖ ≤ NL * (1 + ‖η‖) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg η]) (norm_nonneg _)
    nlinarith [norm_nonneg η]
  have hF : ‖𝓕 (⇑H) η‖ ≤ CF * ((1 + ‖η‖) ^ M)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), mul_comm]; exact hdec
  have hNL : 0 ≤ NL := norm_nonneg _
  have hpow : ((1 + ‖η‖) ^ M)⁻¹ ≤ (2 * NL) ^ M * ((1 + ‖zpt k‖) ^ (M : ℝ))⁻¹ := by
    rw [Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
      inv_mul_le_iff₀ (by positivity)]
    calc (1 + ‖zpt k‖) ^ M ≤ (2 * NL * (1 + ‖η‖)) ^ M := pow_le_pow_left₀ (by positivity) hkey M
      _ = _ := by rw [mul_pow, mul_comm]
  have hCF0 : 0 ≤ CF := le_trans (by positivity) (hCF 0)
  calc (|LinearMap.det (L' : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|)⁻¹ * ‖𝓕 (⇑H) η‖
      ≤ (|LinearMap.det (L' : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|)⁻¹ *
          (CF * ((2 * NL) ^ M * ((1 + ‖zpt k‖) ^ (M : ℝ))⁻¹)) := by
        gcongr
        exact hF.trans (mul_le_mul_of_nonneg_left hpow hCF0)
    _ = _ := by ring
set_option maxHeartbeats 1600000 in
theorem poisson_periodic' (H : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m : ℕ) (hm : 0 < m)
    (φ : (ι → ℤ) → ℂ) (hper : ∀ n k, φ (n + (m : ℤ) • k) = φ n) (hb : ∀ n, ‖φ n‖ ≤ 1)
    (M : ℕ) (hM : Fintype.card ι < M) (CF : ℝ)
    (hCF : ∀ x, (1 + ‖x‖) ^ M * ‖𝓕 (⇑H) x‖ ≤ CF)
    (L : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) :
      Summable (fun n => φ n * H (L (zpt n))) ∧
      ‖∑' n, φ n * H (L (zpt n)) -
          ((∑ r : ι → Fin m, φ (fun i => ((r i : ℕ) : ℤ))) * ((m : ℂ) ^ Fintype.card ι)⁻¹ *
            ∫ x, H x) *
            ((|LinearMap.det (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|)⁻¹ : ℝ)‖ ≤
        CF * (2 * m) ^ M * (∑' k : ι → ℤ, ((1 + ‖zpt k‖) ^ (M : ℝ))⁻¹) *
          |LinearMap.det (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹ *
          ‖(L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ^ M := by
  have hCF0 : 0 ≤ CF := le_trans (by positivity) (hCF 0)
  haveI : NeZero m := ⟨hm.ne'⟩
  set d := Fintype.card ι
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  let rr : (ι → Fin m) → (ι → ℤ) := fun r i => ((r i : ℕ) : ℤ)
  have hZ := summable_zpt_rpow (ι := ι) (M : ℝ) (by exact_mod_cast hM)
  set ZM := ∑' k : ι → ℤ, ((1 + ‖zpt k‖) ^ (M : ℝ))⁻¹
  have hZM0 : 0 ≤ ZM := tsum_nonneg fun _ => by positivity
  set NL := ‖(L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖
  let sm : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ ι) (m : ℝ) hmR.ne').toContinuousLinearEquiv
  let L' : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι := L.trans sm
  have hL'apply : ∀ x, L' x = (m : ℝ) • L x := fun x => rfl
  set δ := |LinearMap.det (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|
  have hδ : 0 < δ := abs_pos.2 (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  have hdet' : |LinearMap.det (L' : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)| =
      (m:ℝ) ^ d * δ := by
    have : (L' : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) =
        (m : ℝ) • (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) := by
      ext x; rfl
    rw [this, LinearMap.det_smul, finrank_euclideanSpace, abs_mul, abs_pow, abs_of_pos hmR]
  have hnorm' : ‖(L' : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ m * NL := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [show (L' : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) x = (m:ℝ) • L x from rfl,
      norm_smul, Real.norm_eq_abs, abs_of_pos hmR, mul_assoc]
    gcongr
    exact ContinuousLinearMap.le_opNorm (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) x
  let cr : (ι → Fin m) → EuclideanSpace ℝ ι := fun r => L (zpt (rr r))
  let Φ : (ι → Fin m) → 𝓢(EuclideanSpace ℝ ι, ℂ) := fun r =>
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L' (SchwartzMap.compSubConstCLM ℂ (-cr r) H)
  have hΦfun : ∀ r, (⇑(Φ r)) = fun x => H (L' x + cr r) := by
    intro r; funext x
    simp only [Φ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  let g : (ι → ℤ) → ℂ := fun n => φ n * H (L (zpt n))
  have hg : Summable g := by
    let HL := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L H
    have := summable_schwartz_zpt HL 0
    refine Summable.of_norm_bounded this fun n => ?_
    simp only [add_zero, HL, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, g]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb n)
  have hgE : ∀ r k, g (fun i => ((r i : ℕ) : ℤ) + (m : ℤ) * k i) = φ (rr r) * Φ r (zpt k) := by
    intro r k
    have h1 : (fun i => ((r i : ℕ) : ℤ) + (m : ℤ) * k i) = rr r + (m : ℤ) • k := by
      funext i; simp [rr]
    rw [h1, hΦfun]
    simp only [g, hper, hL'apply]
    congr 2
    rw [zpt_add_smul, map_add, map_smul]
    simp only [cr]
    push_cast
    abel
  refine ⟨hg, ?_⟩
  set a : ℂ := ((((m:ℝ) ^ d * δ)⁻¹ : ℝ) : ℂ) * ∫ x, H x
  let E : (ι → Fin m) → ℂ := fun r =>
    (∑' k, 𝓕 (⇑(Φ r)) (zpt k)) - 𝓕 (⇑(Φ r)) (zpt 0)
  have hP : ∀ r, ∑' k, Φ r (zpt k) = a + E r := by
    intro r
    obtain ⟨-, -, heq⟩ := poisson (Φ r)
    have h0val : 𝓕 (⇑(Φ r)) (zpt 0) = a := by
      have hz : (zpt (0 : ι → ℤ)) = 0 := by ext i; simp [zpt]
      rw [hz, Real.fourier_eq, hΦfun]
      simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
      rw [integral_comp_clequiv L' (fun u => H (u + cr r)), integral_add_right_eq_self, hdet',
        Complex.real_smul]
    simp only [E]
    rw [heq, h0val]; ring
  have herr : ∀ r, ‖E r‖ ≤ ((m:ℝ) ^ d * δ)⁻¹ * CF * (2 * (m * NL)) ^ M * ZM := by
    intro r
    obtain ⟨-, hs2, -⟩ := poisson (Φ r)
    simp only [E]
    rw [hs2.tsum_eq_add_tsum_ite 0, add_sub_cancel_left]
    refine tsum_of_norm_bounded ((hZ.hasSum).mul_left
      (((m:ℝ) ^ d * δ)⁻¹ * CF * (2 * (m * NL)) ^ M)) fun k => ?_
    split_ifs with hk
    · rw [norm_zero]; positivity
    have hfe := fourier_err H M CF hCF L' (cr r) k hk
    rw [← hΦfun, hdet'] at hfe
    refine hfe.trans ?_
    gcongr
  have hsplit := tsum_residues m g hg
  show ‖∑' n, g n - _‖ ≤ _
  rw [hsplit]
  simp only [hgE, tsum_mul_left, hP]
  have e1 : (∑ r, φ (rr r) * (a + E r)) -
      (∑ r, φ (rr r)) * ((m:ℂ) ^ d)⁻¹ * (∫ x, H x) * ((δ⁻¹ : ℝ) : ℂ) = ∑ r, φ (rr r) * E r := by
    have : (∑ r, φ (rr r)) * ((m:ℂ) ^ d)⁻¹ * (∫ x, H x) * ((δ⁻¹ : ℝ) : ℂ) =
        ∑ r, φ (rr r) * a := by
      rw [← Finset.sum_mul]; simp only [a]; push_cast; ring
    simp only [mul_add, Finset.sum_add_distrib]; rw [this]; ring
  rw [e1]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ r ∈ Finset.univ, ‖φ (rr r) * E r‖ ≤
      ((m:ℝ) ^ d * δ)⁻¹ * CF * (2 * (m * NL)) ^ M * ZM := by
    intro r _
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hb _)).trans (herr r)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
  push_cast
  field_simp
  ring

end PoissonGen
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform Classical ContDiff

/-! ## The mixed space -/
section Mixed
variable {K : Type*} [Field K] [NumberField K]

/-- `N(x)^s` (for `N(x) > 0`). -/
noncomputable def npow (x : mixedSpace K) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log (mixedEmbedding.norm x) : ℂ))

theorem abs_det_mulLeft (a : mixedSpace K) :
    |LinearMap.det (LinearMap.mulLeft ℝ a)| = mixedEmbedding.norm a := by
  have h1 : LinearMap.mulLeft ℝ a =
      LinearMap.prodMap (LinearMap.mulLeft ℝ a.1) (LinearMap.mulLeft ℝ a.2) :=
    LinearMap.ext fun x => rfl
  have h2 : LinearMap.mulLeft ℝ a.1 =
      LinearMap.pi (fun i => (LinearMap.mulLeft ℝ (a.1 i)).comp (LinearMap.proj i)) :=
    LinearMap.ext fun x => rfl
  have h3 : LinearMap.mulLeft ℝ a.2 =
      LinearMap.pi (fun i => (LinearMap.mulLeft ℝ (a.2 i)).comp (LinearMap.proj i)) :=
    LinearMap.ext fun x => rfl
  have hC : ∀ z : ℂ, LinearMap.det (LinearMap.mulLeft ℝ z) = Complex.normSq z := fun z => by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]; rfl
  rw [h1, LinearMap.det_prodMap, h2, h3, LinearMap.det_pi, LinearMap.det_pi]
  simp only [LinearMap.det_mulLeft, hC]
  rw [mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod, abs_mul, Finset.abs_prod,
    Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal w, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex w, normAtPlace_apply_of_isComplex w.2, Complex.normSq_eq_norm_sq,
      abs_of_nonneg (sq_nonneg _)]

theorem integral_comp_mul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : mixedSpace K → G) (a : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) :
    ∫ y, g (a * y) = (mixedEmbedding.norm a)⁻¹ • ∫ y, g y := by
  set T : mixedSpace K →ₗ[ℝ] mixedSpace K := LinearMap.mulLeft ℝ a
  have hdet : LinearMap.det T ≠ 0 := by
    intro h; apply ha; rw [← abs_det_mulLeft a]; simp [T, h]
  have hT : MeasurableEmbedding T :=
    (LinearMap.equivOfDetNeZero T hdet).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (mixedSpace K)))
    hdet
  calc ∫ y, g (a * y) = ∫ y, g (T y) := rfl
    _ = ∫ y, g y ∂(Measure.map T volume) := (hT.integral_map g).symm
    _ = _ := by
      rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
        abs_det_mulLeft a]

theorem cone_bound : ∃ κ : ℝ, 0 < κ ∧ ∀ y ∈ fundamentalCone K,
    ‖y‖ ≤ κ * mixedEmbedding.norm y ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨R, hR⟩ := (fundamentalCone.isBounded_normLeOne K).exists_norm_le
  refine ⟨max R 1, by positivity, fun y hy => ?_⟩
  set d := Module.finrank ℚ K
  have hN : 0 < mixedEmbedding.norm y := fundamentalCone.norm_pos_of_mem hy
  have hd : (0:ℝ) < d := by exact_mod_cast Module.finrank_pos
  set t : ℝ := mixedEmbedding.norm y ^ (-(d:ℝ)⁻¹)
  have ht : 0 < t := Real.rpow_pos_of_pos hN _
  have hty : t • y ∈ fundamentalCone.normLeOne K := by
    refine ⟨fundamentalCone.smul_mem_of_mem hy ht.ne', ?_⟩
    show mixedEmbedding.norm (t • y) ≤ 1
    rw [mixedEmbedding.norm_smul, abs_of_pos ht, ← Real.rpow_natCast, ← Real.rpow_mul hN.le,
      show -(d:ℝ)⁻¹ * (d:ℝ) = -1 by field_simp, Real.rpow_neg_one, inv_mul_cancel₀ hN.ne']
  have h1 := hR _ hty
  rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h1
  have ht' : t * mixedEmbedding.norm y ^ ((d:ℝ)⁻¹) = 1 := by
    rw [← Real.rpow_add hN]; simp
  have : ‖y‖ ≤ R * mixedEmbedding.norm y ^ ((d:ℝ)⁻¹) := by
    calc ‖y‖ = (t * ‖y‖) * mixedEmbedding.norm y ^ ((d:ℝ)⁻¹) := by
          rw [mul_comm t, mul_assoc, ht', mul_one]
      _ ≤ R * _ := by gcongr
  exact this.trans (by gcongr; exact le_max_left _ _)

theorem cone_trunc_finite (T : ℝ) :
    volume (fundamentalCone K ∩ {y | mixedEmbedding.norm y ≤ T}) < ⊤ := by
  obtain ⟨κ, hκ, hb⟩ := cone_bound (K := K)
  refine Bornology.IsBounded.measure_lt_top ?_
  refine isBounded_iff_forall_norm_le.2 ⟨κ * |T| ^ ((Module.finrank ℚ K : ℝ)⁻¹), ?_⟩
  rintro y ⟨hy, hyT⟩
  refine (hb y hy).trans ?_
  gcongr
  · exact mixedEmbedding.norm_nonneg y
  · exact hyT.trans (le_abs_self T)

instance countable_O : Countable (𝓞 K) :=
  (NumberField.RingOfIntegers.basis K).equivFun.injective.countable

/-- the free part of the unit group. -/
noncomputable def uE (e : Fin (rank K) → ℤ) : (𝓞 K)ˣ := ∏ i, fundSystem K i ^ e i

theorem uE_add (e e' : Fin (rank K) → ℤ) : uE (e + e') = uE e * uE e' := by
  unfold uE; rw [← Finset.prod_mul_distrib]; congr 1; funext i; rw [Pi.add_apply, zpow_add]

theorem uE_zero : uE (0 : Fin (rank K) → ℤ) = 1 := by unfold uE; simp

theorem uE_neg (e : Fin (rank K) → ℤ) : uE (-e) = (uE e)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← uE_add, neg_add_cancel, uE_zero]

theorem uE_torsion (e : Fin (rank K) → ℤ) (h : uE e ∈ torsion K) : e = 0 := by
  obtain ⟨p, -, huniq⟩ := exist_unique_eq_mul_prod K (uE e)
  have h1 := huniq (⟨uE e, h⟩, 0) (by simp)
  have h2 := huniq (1, e) (by simp [uE])
  exact (congrArg Prod.snd (h1.trans h2.symm)).symm

theorem uniq_cone (x : mixedSpace K) (hx : x ∈ fundamentalCone K) (e : Fin (rank K) → ℤ)
    (h : uE e • x ∈ fundamentalCone K) : e = 0 :=
  uE_torsion e ((fundamentalCone.unit_smul_mem_iff_mem_torsion hx (uE e)).1 h)

theorem cover (z : mixedSpace K) (hz : mixedEmbedding.norm z ≠ 0) :
    ∃ k : Fin (rank K) → ℤ, uE k • z ∈ fundamentalCone K := by
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem hz
  obtain ⟨⟨ζ, k⟩, hp, -⟩ := exist_unique_eq_mul_prod K u
  refine ⟨k, ?_⟩
  have : ((ζ : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) • u • z = uE k • z := by
    rw [smul_smul, hp]; simp [uE]
  rw [← this]
  exact fundamentalCone.torsion_smul_mem_of_mem hu (inv_mem ζ.2)

theorem one_le_norm_emb (α : 𝓞 K) (h : α ≠ 0) :
    1 ≤ mixedEmbedding.norm (mixedEmbedding K (α : K)) := by
  rw [mixedEmbedding.norm_eq_norm, ← Algebra.coe_norm_int]
  have h1 : Algebra.norm ℤ α ≠ 0 := by rwa [Ne, Algebra.norm_eq_zero_iff]
  have h2 : (1:ℤ) ≤ |Algebra.norm ℤ α| := Int.one_le_abs h1
  have h4 : (1:ℚ) ≤ |((Algebra.norm ℤ α : ℤ) : ℚ)| := by exact_mod_cast h2
  exact_mod_cast h4

theorem memb_mul (a : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) :
    MeasurableEmbedding (fun y : mixedSpace K => a * y) ∧
      Measure.map (fun y : mixedSpace K => a * y) volume =
        ENNReal.ofReal (mixedEmbedding.norm a)⁻¹ • volume := by
  set T : mixedSpace K →ₗ[ℝ] mixedSpace K := LinearMap.mulLeft ℝ a
  have hdet : LinearMap.det T ≠ 0 := by
    intro h; apply ha; rw [← abs_det_mulLeft a]; simp [T, h]
  refine ⟨(LinearMap.equivOfDetNeZero T hdet).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding, ?_⟩
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (mixedSpace K)))
    hdet
  rw [show (fun y : mixedSpace K => a * y) = T from rfl, hmap, abs_inv, abs_det_mulLeft a]

theorem integrable_comp_mul' {G : Type*} [NormedAddCommGroup G]
    (g : mixedSpace K → G) (hg : Integrable g) (a : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) :
    Integrable (fun y => g (a * y)) := by
  obtain ⟨hT, hmap⟩ := memb_mul a ha
  have : Integrable g (Measure.map (fun y : mixedSpace K => a * y) volume) := by
    rw [hmap]; exact hg.smul_measure ENNReal.ofReal_ne_top
  exact (hT.integrable_map_iff.1 this)

theorem mp_unit (u : (𝓞 K)ˣ) : MeasurePreserving (fun y : mixedSpace K => u • y) volume volume ∧
    MeasurableEmbedding (fun y : mixedSpace K => u • y) := by
  have hN : mixedEmbedding.norm (mixedEmbedding K ((u : 𝓞 K) : K)) = 1 := norm_unit u
  obtain ⟨hT, hmap⟩ := memb_mul (mixedEmbedding K ((u : 𝓞 K) : K)) (by rw [hN]; exact one_ne_zero)
  refine ⟨⟨hT.measurable, ?_⟩, hT⟩
  rw [show (fun y : mixedSpace K => u • y) = fun y => mixedEmbedding K ((u : 𝓞 K) : K) * y from rfl,
    hmap, hN, inv_one, ENNReal.ofReal_one, one_smul]

theorem fold {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (g : mixedSpace K → G) (hg : Integrable g)
    (h0 : ∀ y, mixedEmbedding.norm y = 0 → g y = 0) :
    HasSum (fun e : Fin (rank K) → ℤ => ∫ y in fundamentalCone K, g (uE e • y)) (∫ y, g y) := by
  set B : (Fin (rank K) → ℤ) → Set (mixedSpace K) :=
    fun e => (fun z => (uE e)⁻¹ • z) ⁻¹' fundamentalCone K
  have hBm : ∀ e, MeasurableSet (B e) := fun e =>
    (mp_unit (uE e)⁻¹).2.measurable (measurableSet_fundamentalCone K)
  have hBd : Pairwise (Function.onFun Disjoint B) := by
    intro e e' hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    apply hne
    have h1 : uE (e - e') • ((uE e)⁻¹ • z) = (uE e')⁻¹ • z := by
      rw [smul_smul, sub_eq_add_neg, uE_add, uE_neg]
      congr 1; rw [mul_right_comm, mul_inv_cancel, one_mul]
    have := uniq_cone _ hz (e - e') (by rw [h1]; exact hz')
    exact sub_eq_zero.1 this
  have hBU : (⋃ e, B e) = {z | mixedEmbedding.norm z ≠ 0} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, B, Set.mem_preimage]
    constructor
    · rintro ⟨e, he⟩
      have := (fundamentalCone.norm_pos_of_mem he).ne'
      rwa [norm_unit_smul] at this
    · intro hz
      obtain ⟨k, hk⟩ := cover z hz
      exact ⟨-k, by rwa [uE_neg, inv_inv]⟩
  have hs := hasSum_integral_iUnion hBm hBd hg.integrableOn
  rw [hBU, setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => h0 y (by simpa using hy))]
    at hs
  convert hs using 1
  funext e
  have hpre : (fun y : mixedSpace K => uE e • y) ⁻¹' B e = fundamentalCone K := by
    ext x; simp only [B, Set.mem_preimage, smul_smul, inv_mul_cancel, one_smul]
  rw [← (mp_unit (uE e)).1.setIntegral_preimage_emb (mp_unit (uE e)).2 g (B e), hpre]

/-- `(a, e) ↦ u_e · a`. -/
noncomputable def pmap (p : fundamentalCone.integerSet K × (Fin (rank K) → ℤ)) : 𝓞 K :=
  (uE p.2 : 𝓞 K) * (fundamentalCone.preimageOfMemIntegerSet p.1 : 𝓞 K)

theorem pmap_emb (p : fundamentalCone.integerSet K × (Fin (rank K) → ℤ)) :
    mixedEmbedding K ((pmap p : 𝓞 K) : K) = uE p.2 • (p.1 : mixedSpace K) := by
  rw [unitSMul_smul, ← fundamentalCone.mixedEmbedding_preimageOfMemIntegerSet p.1, ← map_mul]
  simp [pmap]

theorem pmap_injective : Function.Injective (pmap (K := K)) := by
  rintro ⟨a, e⟩ ⟨a', e'⟩ h
  have h1 : uE e • (a : mixedSpace K) = uE e' • (a' : mixedSpace K) := by
    rw [← pmap_emb (a, e), ← pmap_emb (a', e'), h]
  have ha := a.2.1
  have ha' := a'.2.1
  have h2 : uE (e - e') • (a : mixedSpace K) = (a' : mixedSpace K) := by
    rw [sub_eq_add_neg, uE_add, uE_neg, mul_comm, mul_smul, h1, ← mul_smul, inv_mul_cancel,
      one_smul]
  have he : e - e' = 0 := uniq_cone _ ha _ (by rw [h2]; exact ha')
  have hee : e = e' := sub_eq_zero.1 he
  subst hee
  have : (a : mixedSpace K) = a' := by rw [← h2, sub_self, uE_zero, one_smul]
  exact Prod.ext (Subtype.ext this) rfl

theorem pmap_range : Set.range (pmap (K := K)) = {α | α ≠ 0} := by
  ext α
  constructor
  · rintro ⟨⟨a, e⟩, rfl⟩
    simp only [pmap, Set.mem_setOf_eq]
    exact mul_ne_zero (Units.ne_zero _) (nonZeroDivisors.coe_ne_zero _)
  · intro hα
    have hz : mixedEmbedding.norm (mixedEmbedding K (α : K)) ≠ 0 :=
      (lt_of_lt_of_le one_pos (one_le_norm_emb α hα)).ne'
    obtain ⟨k, hk⟩ := cover _ hz
    set x : 𝓞 K := (uE k : 𝓞 K) * α
    have hxe : mixedEmbedding K (x : K) = uE k • mixedEmbedding K (α : K) := by
      rw [unitSMul_smul, ← map_mul]; simp [x]
    have hxmem : mixedEmbedding K (x : K) ∈ fundamentalCone.integerSet K := by
      rw [fundamentalCone.mem_integerSet]
      exact ⟨by rw [hxe]; exact hk, x, rfl⟩
    refine ⟨(⟨_, hxmem⟩, -k), ?_⟩
    simp only [pmap]
    rw [fundamentalCone.preimageOfMemIntegerSet_mixedEmbedding]
    simp only [x, uE_neg, ← mul_assoc]
    simp

/-- the ideal-norm summability (copied from the library). -/
theorem summable_idealNorm' (σ : ℝ) (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
  exact summable_idealNorm (F := K) σ hσ

theorem summable_integerSet (σ : ℝ) (hσ : 1 < σ) :
    Summable fun a : fundamentalCone.integerSet K =>
      mixedEmbedding.norm (a : mixedSpace K) ^ (-σ) := by
  have hI := summable_idealNorm' (K := K) σ hσ
  set e := fundamentalCone.integerSetEquiv K
  have hfun : ∀ a : fundamentalCone.integerSet K, mixedEmbedding.norm (a : mixedSpace K) ^ (-σ) =
      ((Ideal.absNorm ((e a).1.1.1 : Ideal (𝓞 K)) : ℕ) : ℝ) ^ (-σ) := by
    intro a
    rw [← fundamentalCone.intNorm_coe]
    congr 2
    rw [fundamentalCone.integerSetEquiv_apply_fst, Ideal.absNorm_span_singleton]
    rfl
  rw [← e.symm.summable_iff]
  have : (fun a : fundamentalCone.integerSet K => mixedEmbedding.norm (a : mixedSpace K) ^ (-σ)) ∘
      e.symm = fun p => ((Ideal.absNorm (p.1.1.1 : Ideal (𝓞 K)) : ℕ) : ℝ) ^ (-σ) := by
    funext p; rw [Function.comp_apply, hfun, Equiv.apply_symm_apply]
  rw [this]
  refine (summable_prod_of_nonneg (fun _ => by positivity)).2 ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_const, nsmul_eq_mul]
  refine Summable.mul_left _ ?_
  refine hI.comp_injective ?_
  intro p q h
  exact Subtype.ext (Subtype.ext h)

theorem entire_of_bound (S : Set (mixedSpace K)) (hS : MeasurableSet S) (hfin : volume S < ⊤)
    (g : mixedSpace K → ℂ) (hg : AEStronglyMeasurable g (volume.restrict S))
    (hpos : ∀ y ∈ S, 0 < mixedEmbedding.norm y)
    (hb : ∀ σ : ℝ, ∃ C : ℝ, ∀ y ∈ S, ‖g y‖ * mixedEmbedding.norm y ^ σ ≤ C) :
    (∀ s, IntegrableOn (fun y => g y * npow y s) S) ∧
      Differentiable ℂ (fun s => ∫ y in S, g y * npow y s) := by
  have hmeas : ∀ s, Measurable (fun y : mixedSpace K => npow y s) := fun s =>
    (measurable_const.mul (Complex.measurable_ofReal.comp
      (Real.measurable_log.comp (mixedEmbedding.continuous_norm K).measurable))).cexp
  have hmeasL : Measurable (fun y : mixedSpace K => ((Real.log (mixedEmbedding.norm y) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_log.comp (mixedEmbedding.continuous_norm K).measurable)
  -- uniform bound for `|Re s| ≤ σ`
  have hub : ∀ σ : ℝ, ∃ B : ℝ, ∀ y ∈ S, ∀ t : ℝ, |t| ≤ σ →
      ‖g y‖ * mixedEmbedding.norm y ^ t ≤ B := by
    intro σ
    obtain ⟨C1, hC1⟩ := hb σ
    obtain ⟨C2, hC2⟩ := hb (-σ)
    refine ⟨C1 + C2, fun y hy t ht => ?_⟩
    have hN := hpos y hy
    have hle : mixedEmbedding.norm y ^ t ≤
        mixedEmbedding.norm y ^ σ + mixedEmbedding.norm y ^ (-σ) := by
      rcases le_total 1 (mixedEmbedding.norm y) with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h (abs_le.1 ht).2
        have := Real.rpow_nonneg hN.le (-σ)
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge hN h (abs_le.1 ht).1
        have := Real.rpow_nonneg hN.le σ
        linarith
    calc ‖g y‖ * mixedEmbedding.norm y ^ t
        ≤ ‖g y‖ * (mixedEmbedding.norm y ^ σ + mixedEmbedding.norm y ^ (-σ)) := by gcongr
      _ = ‖g y‖ * mixedEmbedding.norm y ^ σ + ‖g y‖ * mixedEmbedding.norm y ^ (-σ) := by ring
      _ ≤ C1 + C2 := add_le_add (hC1 y hy) (hC2 y hy)
  have hnp : ∀ y ∈ S, ∀ s : ℂ, ‖npow y s‖ = mixedEmbedding.norm y ^ s.re := by
    intro y hy s
    unfold npow
    rw [Complex.norm_exp, Real.rpow_def_of_pos (hpos y hy)]
    congr 1
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hint : ∀ s, IntegrableOn (fun y => g y * npow y s) S := by
    intro s
    obtain ⟨B, hB⟩ := hub |s.re|
    refine IntegrableOn.of_bound hfin (hg.mul (hmeas s).aestronglyMeasurable) B ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun y hy => ?_)
    rw [norm_mul, hnp y hy]
    exact hB y hy _ le_rfl
  refine ⟨hint, fun s0 => ?_⟩
  obtain ⟨B, hB⟩ := hub (|s0.re| + 2)
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hlog : ∀ y ∈ S, |Real.log (mixedEmbedding.norm y)| ≤
      mixedEmbedding.norm y ^ (1:ℝ) + mixedEmbedding.norm y ^ (-1:ℝ) := by
    intro y hy
    have hN := hpos y hy
    rw [Real.rpow_one, Real.rpow_neg_one]
    have h1 := Real.log_le_sub_one_of_pos hN
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hN)
    rw [Real.log_inv] at h2
    have h3 := inv_pos.2 hN
    rw [abs_le]; constructor <;> linarith
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun s y => g y * npow y s)
    (F' := fun s y => g y * (((Real.log (mixedEmbedding.norm y) : ℝ) : ℂ) * npow y s))
    (x₀ := s0) (bound := fun _ => 2 * B) (s := Metric.ball s0 1) (Metric.ball_mem_nhds s0 one_pos)
    (Eventually.of_forall fun s => (hint s).aestronglyMeasurable) (hint s0)
    (hg.mul (hmeasL.mul (hmeas s0)).aestronglyMeasurable)
    ((ae_restrict_iff' hS).2 (Eventually.of_forall fun y hy s hs => ?_))
    (integrable_const _)
    (Eventually.of_forall fun y s _ => ?_)
  · exact hderiv.2.differentiableAt
  · have hN := hpos y hy
    have hs' : |s.re - s0.re| < 1 := by
      have h := Metric.mem_ball.1 hs
      rw [Complex.dist_eq] at h
      calc |s.re - s0.re| = |(s - s0).re| := by simp
        _ ≤ ‖s - s0‖ := Complex.abs_re_le_norm _
        _ < 1 := h
    rw [norm_mul, norm_mul, hnp y hy, Complex.norm_real, Real.norm_eq_abs]
    have e1 : |s.re + 1| ≤ |s0.re| + 2 := by
      have := abs_sub_abs_le_abs_sub s.re s0.re
      have := abs_add_le s.re 1
      have := abs_sub_lt_iff.1 hs'
      rw [abs_le]; constructor <;> cases abs_cases s0.re <;> linarith [abs_nonneg s.re]
    have e2 : |s.re + -1| ≤ |s0.re| + 2 := by
      have := abs_sub_lt_iff.1 hs'
      rw [abs_le]; constructor <;> cases abs_cases s0.re <;> linarith
    have hb1 := hB y hy _ e1
    have hb2 := hB y hy _ e2
    rw [Real.rpow_add hN] at hb1 hb2
    calc ‖g y‖ * (|Real.log (mixedEmbedding.norm y)| * mixedEmbedding.norm y ^ s.re)
        ≤ ‖g y‖ * ((mixedEmbedding.norm y ^ (1:ℝ) + mixedEmbedding.norm y ^ (-1:ℝ)) *
            mixedEmbedding.norm y ^ s.re) := by
          gcongr
          exact hlog y hy
      _ = ‖g y‖ * (mixedEmbedding.norm y ^ s.re * mixedEmbedding.norm y ^ (1:ℝ)) +
          ‖g y‖ * (mixedEmbedding.norm y ^ s.re * mixedEmbedding.norm y ^ (-1:ℝ)) := by ring
      _ ≤ B + B := add_le_add (by simpa [mul_assoc] using hb1) (by simpa [mul_assoc] using hb2)
      _ = 2 * B := by ring
  · show HasDerivAt (fun s => g y * npow y s)
      (g y * (((Real.log (mixedEmbedding.norm y) : ℝ) : ℂ) * npow y s)) s
    unfold npow
    have := ((hasDerivAt_id s).mul_const (((Real.log (mixedEmbedding.norm y) : ℝ) : ℂ))).cexp
    simp only [id, one_mul] at this
    rw [mul_comm (((Real.log (mixedEmbedding.norm y) : ℝ) : ℂ))]
    exact this.const_mul (g y)

end Mixed

/-! ## The analytic core -/

structure CData (K : Type*) [Field K] [NumberField K] where
  c : mixedSpace K → ℂ
  mul : ∀ x y, mixedEmbedding.norm x ≠ 0 → mixedEmbedding.norm y ≠ 0 → c (x * y) = c x * c y
  norm1 : ∀ x, mixedEmbedding.norm x ≠ 0 → ‖c x‖ = 1
  cont : ContinuousOn c {x | mixedEmbedding.norm x ≠ 0}
  φ : 𝓞 K → ℂ
  bd : ∀ α, ‖φ α‖ ≤ 1
  unit : ∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), α ≠ 0 → φ (u * α) = c (mixedEmbedding K ((u : 𝓞 K) : K)) * φ α

namespace CData
variable {K : Type*} [Field K] [NumberField K] (D : CData K)

/-- the partial Dirichlet series. -/
noncomputable def G (s : ℂ) : ℂ :=
  ∑' a : fundamentalCone.integerSet K, D.φ (fundamentalCone.preimageOfMemIntegerSet a) *
    (D.c a)⁻¹ * npow (a : mixedSpace K) (-s)

theorem c_one : D.c 1 = 1 := by
  have hN1 : mixedEmbedding.norm (1 : mixedSpace K) ≠ 0 := by rw [map_one]; exact one_ne_zero
  have h := D.mul 1 1 hN1 hN1
  rw [one_mul] at h
  have hn := D.norm1 1 hN1
  have hne : D.c 1 ≠ 0 := by intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)

theorem exists_rho : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧
    ∀ y ∈ Metric.ball (1 : mixedSpace K) ρ, 1 / 2 < (D.c y).re := by
  have hN1 : mixedEmbedding.norm (1 : mixedSpace K) ≠ 0 := by rw [map_one]; exact one_ne_zero
  have hopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
  have hca : ContinuousAt D.c 1 := D.cont.continuousAt (hopen.mem_nhds hN1)
  have hU : {z : ℂ | 1/2 < z.re} ∈ 𝓝 (D.c 1) := by
    rw [D.c_one]
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hca.preimage_mem_nhds hU)
  exact ⟨min ε (1/2), by positivity, min_le_right _ _,
    fun y hy => hball (Metric.ball_subset_ball (min_le_left _ _) hy)⟩

noncomputable def ρ : ℝ := D.exists_rho.choose

noncomputable def bump : ContDiffBump (1 : mixedSpace K) where
  rIn := D.ρ / 2
  rOut := D.ρ
  rIn_pos := by have := D.exists_rho.choose_spec.1; unfold ρ; linarith
  rIn_lt_rOut := by have := D.exists_rho.choose_spec.1; unfold ρ; linarith

/-- the test function. -/
noncomputable def f (y : mixedSpace K) : ℝ := D.bump y

theorem norm_bounds_ball (y : mixedSpace K) (hy : y ∈ Metric.ball (1 : mixedSpace K) D.ρ) :
    (1 / 2 : ℝ) ^ Module.finrank ℚ K ≤ mixedEmbedding.norm y ∧
      mixedEmbedding.norm y ≤ 2 ^ Module.finrank ℚ K := by
  have hρ := D.exists_rho.choose_spec.2.1
  have hy' : ‖y - 1‖ < 1/2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.trans_le hρ
  have hw : ∀ w, 1/2 ≤ normAtPlace w y ∧ normAtPlace w y ≤ 2 := by
    intro w
    have h1 : normAtPlace w (y - 1) ≤ ‖y - 1‖ := by
      rw [norm_eq_sup'_normAtPlace]
      exact Finset.le_sup' (fun w => normAtPlace w (y - 1)) (Finset.mem_univ w)
    have h2 := normAtPlace_add_le w (y - 1) 1
    rw [sub_add_cancel, map_one] at h2
    have h3 : normAtPlace w (1 : mixedSpace K) ≤ normAtPlace w y + normAtPlace w (-(y - 1)) := by
      have := normAtPlace_add_le w y (-(y - 1))
      rwa [show y + -(y - 1) = 1 by ring] at this
    rw [map_one, normAtPlace_neg] at h3
    constructor <;> linarith
  rw [mixedEmbedding.norm_apply]
  have hsum := InfinitePlace.sum_mult_eq (K := K)
  constructor
  · calc (1/2:ℝ) ^ Module.finrank ℚ K = ∏ w, (1/2:ℝ) ^ (mult w) := by
          rw [Finset.prod_pow_eq_pow_sum, hsum]
      _ ≤ ∏ w, normAtPlace w y ^ mult w := Finset.prod_le_prod (fun w _ => by positivity)
          (fun w _ => pow_le_pow_left₀ (by norm_num) (hw w).1 _)
  · calc ∏ w, normAtPlace w y ^ mult w ≤ ∏ w, (2:ℝ) ^ (mult w) :=
          Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg _ _) _)
            (fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg _ _) (hw w).2 _)
      _ = 2 ^ Module.finrank ℚ K := by rw [Finset.prod_pow_eq_pow_sum, hsum]

/-- the archimedean zeta integral. -/
noncomputable def Z (s : ℂ) : ℂ := ∫ y, (D.f y : ℂ) * D.c y * npow y (s - 1)

theorem f_nonneg (y : mixedSpace K) : 0 ≤ D.f y := D.bump.nonneg
theorem f_le_one (y : mixedSpace K) : D.f y ≤ 1 := D.bump.le_one
theorem f_cont : Continuous D.f := D.bump.continuous
theorem f_supp (y : mixedSpace K) (hy : D.f y ≠ 0) : y ∈ Metric.ball (1 : mixedSpace K) D.ρ := by
  have : y ∈ Function.support D.bump := hy
  rwa [D.bump.support_eq] at this

theorem ball_pos (y : mixedSpace K) (hy : y ∈ Metric.ball (1 : mixedSpace K) D.ρ) :
    0 < mixedEmbedding.norm y :=
  lt_of_lt_of_le (by positivity) (D.norm_bounds_ball y hy).1

theorem npow_add (y : mixedSpace K) (s t : ℂ) : npow y s * npow y t = npow y (s + t) := by
  unfold npow; rw [← Complex.exp_add]; congr 1; ring

theorem npow_mul (x y : mixedSpace K) (hx : 0 < mixedEmbedding.norm x)
    (hy : 0 < mixedEmbedding.norm y) (s : ℂ) : npow (x * y) s = npow x s * npow y s := by
  unfold npow
  rw [map_mul, Real.log_mul hx.ne' hy.ne', ← Complex.exp_add]; congr 1; push_cast; ring

theorem npow_neg_one (y : mixedSpace K) (hy : 0 < mixedEmbedding.norm y) :
    npow y (-1) = (((mixedEmbedding.norm y)⁻¹ : ℝ) : ℂ) := by
  unfold npow
  rw [neg_one_mul, ← Complex.ofReal_neg, ← Real.log_inv, ← Complex.ofReal_exp,
    Real.exp_log (inv_pos.mpr hy)]

theorem one_le_norm_emb (α : 𝓞 K) (h : α ≠ 0) :
    1 ≤ mixedEmbedding.norm (mixedEmbedding K (α : K)) := by
  rw [mixedEmbedding.norm_eq_norm, ← Algebra.coe_norm_int]
  have h1 : Algebra.norm ℤ α ≠ 0 := by rwa [Ne, Algebra.norm_eq_zero_iff]
  have h2 : (1:ℤ) ≤ |Algebra.norm ℤ α| := Int.one_le_abs h1
  have h3 : ((|Algebra.norm ℤ α| : ℤ) : ℝ) = |((Algebra.norm ℤ α : ℚ) : ℝ)| := by push_cast; rfl
  have h4 : (1:ℚ) ≤ |((Algebra.norm ℤ α : ℤ) : ℚ)| := by exact_mod_cast h2
  exact_mod_cast h4

theorem Z_aux : (∀ s, IntegrableOn (fun y => (D.f y : ℂ) * D.c y * npow y s)
      (Metric.ball (1 : mixedSpace K) D.ρ)) ∧
    Differentiable ℂ (fun s => ∫ y in Metric.ball (1 : mixedSpace K) D.ρ,
      (D.f y : ℂ) * D.c y * npow y s) := by
  set d := Module.finrank ℚ K
  refine entire_of_bound _ measurableSet_ball measure_ball_lt_top (fun y => (D.f y : ℂ) * D.c y)
    ?_ D.ball_pos ?_
  · refine (Complex.continuous_ofReal.comp D.f_cont).aestronglyMeasurable.mul ?_
    exact (D.cont.mono fun y hy => (D.ball_pos y hy).ne').aestronglyMeasurable measurableSet_ball
  · intro σ
    refine ⟨((2:ℝ) ^ d) ^ |σ|, fun y hy => ?_⟩
    have hb := D.norm_bounds_ball y hy
    have hN := D.ball_pos y hy
    have hg : ‖(D.f y : ℂ) * D.c y‖ ≤ 1 := by
      rw [norm_mul, D.norm1 y hN.ne', mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (D.f_nonneg y)]
      exact D.f_le_one y
    have hp : mixedEmbedding.norm y ^ σ ≤ ((2:ℝ) ^ d) ^ |σ| := by
      rcases le_total 0 σ with hσ | hσ
      · rw [abs_of_nonneg hσ]; exact Real.rpow_le_rpow hN.le hb.2 hσ
      · rw [abs_of_nonpos hσ]
        have h1 : ((1/2:ℝ) ^ d) = ((2:ℝ) ^ d)⁻¹ := by rw [div_pow, one_pow, one_div]
        rw [h1] at hb
        calc mixedEmbedding.norm y ^ σ ≤ (((2:ℝ) ^ d)⁻¹) ^ σ :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hb.1 hσ
          _ = ((2:ℝ) ^ d) ^ (-σ) := by rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
    calc ‖(D.f y : ℂ) * D.c y‖ * mixedEmbedding.norm y ^ σ ≤ 1 * ((2:ℝ) ^ d) ^ |σ| := by
          gcongr
      _ = _ := one_mul _

theorem Z_eq (s : ℂ) : D.Z s = ∫ y in Metric.ball (1 : mixedSpace K) D.ρ,
    (D.f y : ℂ) * D.c y * npow y (s - 1) := by
  unfold Z
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
  have : D.f y = 0 := by by_contra h; exact hy (D.f_supp y h)
  rw [this]; simp

theorem Z_differentiable : Differentiable ℂ D.Z := by
  have h := D.Z_aux.2.comp (differentiable_id.sub_const 1)
  have : D.Z = (fun s => ∫ y in Metric.ball (1 : mixedSpace K) D.ρ,
      (D.f y : ℂ) * D.c y * npow y s) ∘ (fun s => id s - 1) := funext D.Z_eq
  rw [this]; exact h

theorem Z_zero_ne : D.Z 0 ≠ 0 := by
  set d := Module.finrank ℚ K
  have hint0 : Integrable (fun y => (D.f y : ℂ) * D.c y * npow y (0 - 1)) := by
    refine (D.Z_aux.1 (0 - 1)).integrable_of_forall_notMem_eq_zero fun y hy => ?_
    have : D.f y = 0 := by by_contra h; exact hy (D.f_supp y h)
    rw [this]; simp
  have hre := integral_re hint0
  have hlow : ∀ y, D.f y * ((1/2) * ((2:ℝ) ^ d)⁻¹) ≤
      ((D.f y : ℂ) * D.c y * npow y (0 - 1)).re := by
    intro y
    by_cases hf : D.f y = 0
    · simp [hf]
    have hy := D.f_supp y hf
    have hN := D.ball_pos y hy
    have hb := D.norm_bounds_ball y hy
    have hc := D.exists_rho.choose_spec.2.2 y hy
    rw [zero_sub, npow_neg_one y hN]
    have e : (D.f y : ℂ) * D.c y * (((mixedEmbedding.norm y)⁻¹ : ℝ) : ℂ) =
        (((D.f y) * (mixedEmbedding.norm y)⁻¹ : ℝ) : ℂ) * D.c y := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (D.f_nonneg y)
    have h1 : ((2:ℝ) ^ d)⁻¹ ≤ (mixedEmbedding.norm y)⁻¹ := inv_anti₀ hN hb.2
    have h2 : (1/2 : ℝ) ≤ (D.c y).re := hc.le
    rw [mul_comm]
    exact mul_le_mul h1 h2 (by norm_num) (by positivity)
  have hmono := integral_mono ((D.bump.integrable (μ := volume)).mul_const
    ((1/2) * ((2:ℝ) ^ d)⁻¹)) hint0.re hlow
  rw [integral_mul_const, hre] at hmono
  have hpos : 0 < (∫ y, D.bump y) * ((1/2) * ((2:ℝ) ^ d)⁻¹) :=
    mul_pos D.bump.integral_pos (by positivity)
  intro h
  have h0 : (D.Z 0).re = 0 := by rw [h]; rfl
  unfold Z at h0
  have h2 : RCLike.re (∫ x, (D.f x : ℂ) * D.c x * npow x (0 - 1)) = 0 := h0
  have := lt_of_lt_of_le hpos hmono
  linarith

/-- the theta function. -/
noncomputable def Θ (y : mixedSpace K) : ℂ :=
  ∑' α : 𝓞 K, D.φ α * (D.f (mixedEmbedding K (α : K) * y) : ℂ)

theorem npow_norm (y : mixedSpace K) (hy : 0 < mixedEmbedding.norm y) (s : ℂ) :
    ‖npow y s‖ = mixedEmbedding.norm y ^ s.re := by
  unfold npow
  rw [Complex.norm_exp, Real.rpow_def_of_pos hy]
  congr 1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- the archimedean integrand. -/
noncomputable def F0 (s : ℂ) (z : mixedSpace K) : ℂ := (D.f z : ℂ) * D.c z * npow z (s - 1)

theorem f_zero_of_norm (y : mixedSpace K) (hy : mixedEmbedding.norm y = 0) : D.f y = 0 := by
  by_contra h; exact (D.ball_pos y (D.f_supp y h)).ne' hy

theorem f_zero : D.f 0 = 0 := D.f_zero_of_norm 0 (map_zero _)

theorem F0_int (s : ℂ) : Integrable (D.F0 s) := by
  refine (D.Z_aux.1 (s - 1)).integrable_of_forall_notMem_eq_zero fun y hy => ?_
  have : D.f y = 0 := by by_contra h; exact hy (D.f_supp y h)
  simp [F0, this]

theorem term_factor (α : 𝓞 K) (hα : α ≠ 0) (s : ℂ) : ∃ C : ℂ,
    (∀ y, (D.f (mixedEmbedding K (α : K) * y) : ℂ) * D.c y * npow y (s - 1) =
      C * D.F0 s (mixedEmbedding K (α : K) * y)) ∧
    C * (((mixedEmbedding.norm (mixedEmbedding K (α : K)))⁻¹ : ℝ) : ℂ) =
      (D.c (mixedEmbedding K (α : K)))⁻¹ * npow (mixedEmbedding K (α : K)) (-s) ∧
    ‖C‖ * (mixedEmbedding.norm (mixedEmbedding K (α : K)))⁻¹ =
      mixedEmbedding.norm (mixedEmbedding K (α : K)) ^ (-s.re) := by
  set a := mixedEmbedding K (α : K)
  set a' := mixedEmbedding K ((α : K)⁻¹)
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  have haa : a' * a = 1 := by rw [← map_mul, inv_mul_cancel₀ hαK, map_one]
  have hNa : 0 < mixedEmbedding.norm a := lt_of_lt_of_le one_pos (one_le_norm_emb α hα)
  have hNaa : mixedEmbedding.norm a' * mixedEmbedding.norm a = 1 := by
    rw [← map_mul, haa, map_one]
  have hNa' : 0 < mixedEmbedding.norm a' := by
    by_contra h
    nlinarith [mixedEmbedding.norm_nonneg a']
  have hca : D.c a' = (D.c a)⁻¹ := by
    have h1 := D.mul a' a hNa'.ne' hNa.ne'
    rw [haa, D.c_one] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hnpa : ∀ t, npow a' t = npow a (-t) := by
    intro t; unfold npow
    rw [eq_inv_of_mul_eq_one_left hNaa, Real.log_inv]; push_cast; ring_nf
  refine ⟨D.c a' * npow a' (s - 1), fun y => ?_, ?_, ?_⟩
  · by_cases hf : D.f (a * y) = 0
    · simp [F0, hf]
    have hN := D.ball_pos _ (D.f_supp _ hf)
    have hy : 0 < mixedEmbedding.norm y := by
      rw [map_mul] at hN
      exact pos_of_mul_pos_right hN hNa.le
    have hc : D.c y = D.c a' * D.c (a * y) := by
      rw [← D.mul a' (a * y) hNa'.ne' hN.ne', ← mul_assoc, haa, one_mul]
    have hn : npow y (s - 1) = npow a' (s - 1) * npow (a * y) (s - 1) := by
      rw [← npow_mul a' (a * y) hNa' hN, ← mul_assoc, haa, one_mul]
    unfold F0; rw [hc, hn]; ring
  · rw [← npow_neg_one a hNa, hca, hnpa,
      show npow a (-s) = npow a (-(s - 1)) * npow a (-1) by rw [npow_add]; congr 1; ring]
    ring
  · rw [norm_mul, D.norm1 a' hNa'.ne', one_mul, hnpa, npow_norm a hNa, ← Real.rpow_neg_one,
      ← Real.rpow_add hNa]
    congr 1; simp; ring

theorem termwise (α : 𝓞 K) (hα : α ≠ 0) (s : ℂ) :
    ∫ y, (D.f (mixedEmbedding K (α : K) * y) : ℂ) * D.c y * npow y (s - 1) =
      (D.c (mixedEmbedding K (α : K)))⁻¹ * npow (mixedEmbedding K (α : K)) (-s) * D.Z s := by
  obtain ⟨C, h1, h2, -⟩ := D.term_factor α hα s
  have hN : mixedEmbedding.norm (mixedEmbedding K (α : K)) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_norm_emb α hα)).ne'
  simp only [h1]
  rw [integral_const_mul, integral_comp_mul _ _ hN, Complex.real_smul, ← h2]
  unfold Z F0; ring

theorem termwise_norm (α : 𝓞 K) (hα : α ≠ 0) (s : ℂ) :
    ∫ y, ‖(D.f (mixedEmbedding K (α : K) * y) : ℂ) * D.c y * npow y (s - 1)‖ =
      mixedEmbedding.norm (mixedEmbedding K (α : K)) ^ (-s.re) * ∫ z, ‖D.F0 s z‖ := by
  obtain ⟨C, h1, -, h3⟩ := D.term_factor α hα s
  have hN : mixedEmbedding.norm (mixedEmbedding K (α : K)) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_norm_emb α hα)).ne'
  simp only [h1, norm_mul]
  rw [integral_const_mul, integral_comp_mul (fun z => ‖D.F0 s z‖) _ hN, smul_eq_mul, ← h3]; ring

theorem integrable_term (α : 𝓞 K) (hα : α ≠ 0) (s : ℂ) :
    Integrable (fun y => (D.f (mixedEmbedding K (α : K) * y) : ℂ) * D.c y * npow y (s - 1)) := by
  obtain ⟨C, h1, -, -⟩ := D.term_factor α hα s
  have hN : mixedEmbedding.norm (mixedEmbedding K (α : K)) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_norm_emb α hα)).ne'
  simp only [h1]
  exact (integrable_comp_mul' _ (D.F0_int s) _ hN).const_mul C

theorem npow_unit (u : (𝓞 K)ˣ) (y : mixedSpace K) (hy : 0 < mixedEmbedding.norm y) (t : ℂ) :
    npow (u • y) t = npow y t := by
  have hN : mixedEmbedding.norm (mixedEmbedding K ((u : 𝓞 K) : K)) = 1 := norm_unit u
  rw [unitSMul_smul, npow_mul _ _ (by rw [hN]; exact one_pos) hy]
  unfold npow; rw [hN, Real.log_one]; simp

theorem unfold (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y => D.Θ y * D.c y * npow y (s - 1)) (fundamentalCone K) ∧
      D.Z s * D.G s = ∫ y in fundamentalCone K, D.Θ y * D.c y * npow y (s - 1) := by
  set σ := s.re
  let F : 𝓞 K → mixedSpace K → ℂ := fun β y =>
    D.φ β * ((D.f (mixedEmbedding K (β : K) * y) : ℂ) * D.c y * npow y (s - 1))
  have hF0 : ∀ y, F 0 y = 0 := by intro y; simp [F, D.f_zero]
  have hFint : ∀ β, Integrable (F β) := by
    intro β
    by_cases hβ : β = 0
    · have : F β = fun _ => 0 := by funext y; rw [hβ, hF0]
      rw [this]; exact integrable_zero _ _ _
    · exact (D.integrable_term β hβ s).const_mul _
  have hFn0 : ∀ β y, mixedEmbedding.norm y = 0 → F β y = 0 := by
    intro β y hy
    have : D.f (mixedEmbedding K (β : K) * y) = 0 :=
      D.f_zero_of_norm _ (by rw [map_mul, hy, mul_zero])
    simp [F, this]
  -- the unit substitution
  have hunit : ∀ (a : fundamentalCone.integerSet K) (e : Fin (rank K) → ℤ) (y : mixedSpace K),
      y ∈ fundamentalCone K →
      F (fundamentalCone.preimageOfMemIntegerSet a) (uE e • y) = F (pmap (a, e)) y := by
    intro a e y hy
    have hNy := fundamentalCone.norm_pos_of_mem hy
    have hNu : mixedEmbedding.norm (mixedEmbedding K ((uE e : 𝓞 K) : K)) = 1 := norm_unit _
    have h1 : mixedEmbedding K (((fundamentalCone.preimageOfMemIntegerSet a : 𝓞 K) : K)) *
        (uE e • y) = mixedEmbedding K ((pmap (a, e) : 𝓞 K) : K) * y := by
      rw [pmap_emb, unitSMul_smul, unitSMul_smul,
        fundamentalCone.mixedEmbedding_preimageOfMemIntegerSet]; ring
    have h2 : D.c (uE e • y) = D.c (mixedEmbedding K ((uE e : 𝓞 K) : K)) * D.c y := by
      rw [unitSMul_smul]; exact D.mul _ _ (by rw [hNu]; exact one_ne_zero) hNy.ne'
    have h3 : D.φ (pmap (a, e)) = D.c (mixedEmbedding K ((uE e : 𝓞 K) : K)) *
        D.φ (fundamentalCone.preimageOfMemIntegerSet a) :=
      D.unit _ _ (nonZeroDivisors.coe_ne_zero _)
    simp only [F]
    rw [h1, h2, npow_unit _ _ hNy, h3]; ring
  -- folding, for each `a`
  set T : fundamentalCone.integerSet K → ℂ := fun a =>
    D.φ (fundamentalCone.preimageOfMemIntegerSet a) * (D.c a)⁻¹ * npow (a : mixedSpace K) (-s)
  have hα0 : ∀ a : fundamentalCone.integerSet K,
      (fundamentalCone.preimageOfMemIntegerSet a : 𝓞 K) ≠ 0 :=
    fun a => nonZeroDivisors.coe_ne_zero _
  have hfold : ∀ a : fundamentalCone.integerSet K,
      HasSum (fun e => ∫ y in fundamentalCone K, F (pmap (a, e)) y) (D.Z s * T a) := by
    intro a
    have h := fold (F (fundamentalCone.preimageOfMemIntegerSet a)) (hFint _) (hFn0 _)
    have hI : ∫ y, F (fundamentalCone.preimageOfMemIntegerSet a) y = D.Z s * T a := by
      simp only [F]
      rw [integral_const_mul, D.termwise _ (hα0 a),
        fundamentalCone.mixedEmbedding_preimageOfMemIntegerSet]
      simp only [T]; ring
    rw [hI] at h
    have : (fun e => ∫ y in fundamentalCone K, F (pmap (a, e)) y) = (fun e =>
        ∫ y in fundamentalCone K, F (fundamentalCone.preimageOfMemIntegerSet a) (uE e • y)) :=
      funext fun e => setIntegral_congr_fun (measurableSet_fundamentalCone K)
        (fun y hy => (hunit a e y hy).symm)
    rw [this]; exact h
  set Zn := ∫ z, ‖D.F0 s z‖
  have hZn : 0 ≤ Zn := integral_nonneg fun _ => norm_nonneg _
  have hfoldn : ∀ a : fundamentalCone.integerSet K,
      HasSum (fun e => ∫ y in fundamentalCone K, ‖F (pmap (a, e)) y‖)
        (‖D.φ (fundamentalCone.preimageOfMemIntegerSet a)‖ *
          (mixedEmbedding.norm (a : mixedSpace K) ^ (-σ) * Zn)) := by
    intro a
    have h := fold (fun y => ‖F (fundamentalCone.preimageOfMemIntegerSet a) y‖) (hFint _).norm
      (fun y hy => by simp [hFn0 _ y hy])
    have hI : ∫ y, ‖F (fundamentalCone.preimageOfMemIntegerSet a) y‖ =
        ‖D.φ (fundamentalCone.preimageOfMemIntegerSet a)‖ *
          (mixedEmbedding.norm (a : mixedSpace K) ^ (-σ) * Zn) := by
      simp only [F, norm_mul]
      rw [integral_const_mul]
      have := D.termwise_norm _ (hα0 a) s
      simp only [norm_mul] at this
      rw [this, fundamentalCone.mixedEmbedding_preimageOfMemIntegerSet]
    rw [hI] at h
    have : (fun e => ∫ y in fundamentalCone K, ‖F (pmap (a, e)) y‖) = (fun e =>
        ∫ y in fundamentalCone K, ‖F (fundamentalCone.preimageOfMemIntegerSet a) (uE e • y)‖) :=
      funext fun e => setIntegral_congr_fun (measurableSet_fundamentalCone K)
        (fun y hy => by rw [hunit a e y hy])
    rw [this]; exact h
  -- summability on the product
  let Ψ : fundamentalCone.integerSet K × (Fin (rank K) → ℤ) → ℝ := fun p =>
    ∫ y in fundamentalCone K, ‖F (pmap p) y‖
  have hΨ0 : ∀ p, 0 ≤ Ψ p := fun p => integral_nonneg fun _ => norm_nonneg _
  have hΨ : Summable Ψ := by
    refine (summable_prod_of_nonneg (fun p => hΨ0 p)).2 ⟨fun a => (hfoldn a).summable, ?_⟩
    have : (fun a => ∑' e, Ψ (a, e)) = fun a =>
        ‖D.φ (fundamentalCone.preimageOfMemIntegerSet a)‖ *
          (mixedEmbedding.norm (a : mixedSpace K) ^ (-σ) * Zn) := funext fun a => (hfoldn a).tsum_eq
    rw [this]
    refine Summable.of_nonneg_of_le (fun a => mul_nonneg (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) hZn)) (fun a => ?_)
      ((summable_integerSet σ hs).mul_right Zn)
    calc ‖D.φ (fundamentalCone.preimageOfMemIntegerSet a)‖ *
          (mixedEmbedding.norm (a : mixedSpace K) ^ (-σ) * Zn)
        ≤ 1 * (mixedEmbedding.norm (a : mixedSpace K) ^ (-σ) * Zn) := by
          gcongr
          · exact mul_nonneg (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) hZn
          · exact D.bd _
      _ = _ := one_mul _
  -- transfer to `𝓞 K`
  have hsupp : ∀ β ∉ Set.range (pmap (K := K)), β = 0 := by
    intro β hβ; by_contra h; exact hβ (by rw [pmap_range]; exact h)
  let Ψβ : 𝓞 K → ℝ := fun β => ∫ y in fundamentalCone K, ‖F β y‖
  have hΨβ : Summable Ψβ := by
    rw [← pmap_injective.summable_iff (fun β hβ => by
      simp only [Ψβ, hsupp β hβ, hF0, norm_zero, integral_zero])]
    exact hΨ
  let Φβ : 𝓞 K → ℂ := fun β => ∫ y in fundamentalCone K, F β y
  have hΦβ : Summable Φβ :=
    Summable.of_norm_bounded hΨβ (fun β => norm_integral_le_integral_norm _)
  have hΦ : Summable (Φβ ∘ pmap) := by
    rw [pmap_injective.summable_iff (fun β hβ => by
      simp only [Φβ, hsupp β hβ, hF0, integral_zero])]
    exact hΦβ
  -- the pointwise sum
  have hpt : ∀ y, ∑' β, F β y = D.Θ y * D.c y * npow y (s - 1) := by
    intro y
    simp only [F, Θ]
    rw [← tsum_mul_right, ← tsum_mul_right]
    congr 1; funext β; ring
  -- lintegral control
  have hlin : ∀ β, ∫⁻ y in fundamentalCone K, ‖F β y‖ₑ = ENNReal.ofReal (Ψβ β) := by
    intro β
    rw [ofReal_integral_norm_eq_lintegral_enorm (hFint β).integrableOn]
  have hfin : ∑' β, ∫⁻ y in fundamentalCone K, ‖F β y‖ₑ ≠ ⊤ := by
    simp only [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun β => integral_nonneg fun _ => norm_nonneg _) hΨβ]
    exact ENNReal.ofReal_ne_top
  have hmeasF : ∀ β, AEStronglyMeasurable (F β) (volume.restrict (fundamentalCone K)) :=
    fun β => (hFint β).aestronglyMeasurable.restrict
  constructor
  · refine ⟨?_, ?_⟩
    · have := AEStronglyMeasurable.tsum (L := SummationFilter.unconditional _) hmeasF
      exact this.congr (Eventually.of_forall fun y => hpt y)
    · unfold HasFiniteIntegral
      calc ∫⁻ y in fundamentalCone K, ‖D.Θ y * D.c y * npow y (s - 1)‖ₑ
          = ∫⁻ y in fundamentalCone K, ‖∑' β, F β y‖ₑ := by simp only [hpt]
        _ ≤ ∫⁻ y in fundamentalCone K, ∑' β, ‖F β y‖ₑ :=
            lintegral_mono fun y => enorm_tsum_le_tsum_enorm
        _ = ∑' β, ∫⁻ y in fundamentalCone K, ‖F β y‖ₑ :=
            lintegral_tsum fun β => (hmeasF β).enorm
        _ < ⊤ := lt_top_iff_ne_top.2 hfin
  · calc D.Z s * D.G s = ∑' a, D.Z s * T a := by
          unfold G; rw [← tsum_mul_left]
      _ = ∑' a, ∑' e, Φβ (pmap (a, e)) := tsum_congr fun a => (hfold a).tsum_eq.symm
      _ = ∑' p, Φβ (pmap p) := (hΦ.tsum_prod).symm
      _ = ∑' β, Φβ β := pmap_injective.tsum_eq (fun β hβ => by
          by_contra h
          exact hβ (by simp only [Φβ, hsupp β h, hF0, integral_zero]))
      _ = ∫ y in fundamentalCone K, ∑' β, F β y := (integral_tsum hmeasF hfin).symm
      _ = _ := by simp only [hpt]

theorem npow_smul (t : ℝ) (ht : t ≠ 0) (z : mixedSpace K) (hz : mixedEmbedding.norm z ≠ 0)
    (s : ℂ) : npow (t • z) s =
      npow z s * Complex.exp (s * ((Module.finrank ℚ K : ℝ) * Real.log |t| : ℝ)) := by
  unfold npow
  rw [mixedEmbedding.norm_smul, Real.log_mul (by positivity) hz, Real.log_pow, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem npow_shift (y : mixedSpace K) (hy : 0 < mixedEmbedding.norm y) (s : ℂ) :
    (((mixedEmbedding.norm y)⁻¹ : ℝ) : ℂ) * npow y (s - 1) = npow y (s - 2) := by
  unfold npow
  have : (((mixedEmbedding.norm y)⁻¹ : ℝ) : ℂ) =
      Complex.exp (-1 * (Real.log (mixedEmbedding.norm y) : ℂ)) := by
    rw [neg_one_mul, ← Complex.ofReal_neg, ← Real.log_inv, ← Complex.ofReal_exp,
      Real.exp_log (inv_pos.mpr hy)]
  rw [this, ← Complex.exp_add]; congr 1; ring
end CData

end Aux_HL
end MasulloGRH

/-! ## The Hecke side -/

namespace MasulloGRH
namespace Aux_HL
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
open Filter Topology MeasureTheory
open scoped Classical

variable {F : Type*} [Field F] [NumberField F]

open InfinitePlace InfinitePlace.Completion in
/-- `F_∞ ≅ ℝ^{r₁} × ℂ^{r₂}` as a homeomorphism -/
noncomputable def eH : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => IsReal v)
      (fun v : InfinitePlace F => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v => (isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v => (isometryEquivComplexOfIsComplex
          ((not_isReal_iff_isComplex.1 v.2))).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex)))))

omit [NumberField F] in
lemma eH_apply (y : InfiniteAdeleRing F) :
    eH y = InfiniteAdeleRing.ringEquiv_mixedSpace F y := rfl

lemma eH_symm_apply (z : mixedEmbedding.mixedSpace F) :
    eH.symm z = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z := by
  apply eH.injective
  rw [Homeomorph.apply_symm_apply, eH_apply, RingEquiv.apply_symm_apply]

theorem isUnit_iff_norm (y : mixedSpace F) : IsUnit y ↔ mixedEmbedding.norm y ≠ 0 := by
  rw [mixedEmbedding.norm_ne_zero_iff, Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  simp only [isUnit_iff_ne_zero]
  constructor
  · rintro ⟨h1, h2⟩ w
    by_cases hw : IsReal w
    · rw [normAtPlace_apply_of_isReal hw, _root_.norm_ne_zero_iff]; exact h1 ⟨w, hw⟩
    · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.1 hw),
        _root_.norm_ne_zero_iff]; exact h2 _
  · intro h
    refine ⟨fun w => ?_, fun w => ?_⟩
    · have := h w.1; rwa [normAtPlace_apply_of_isReal w.2, _root_.norm_ne_zero_iff] at this
    · have := h w.1; rwa [normAtPlace_apply_of_isComplex w.2, _root_.norm_ne_zero_iff] at this

/-- the archimedean component of `χ` on the mixed space. -/
noncomputable def cE (χ : HeckeCharacter F) (y : mixedSpace F) : ℂ :=
  if h : IsUnit y then
    chiInf χ (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toMonoidHom h.unit)
  else 0

theorem cE_mul (χ : HeckeCharacter F) (x y : mixedSpace F) (hx : mixedEmbedding.norm x ≠ 0)
    (hy : mixedEmbedding.norm y ≠ 0) : cE χ (x * y) = cE χ x * cE χ y := by
  have hx' := (isUnit_iff_norm x).2 hx
  have hy' := (isUnit_iff_norm y).2 hy
  rw [cE, dif_pos (hx'.mul hy'), cE, dif_pos hx', cE, dif_pos hy', IsUnit.unit_mul, map_mul,
    chiInf_mul]

theorem cE_norm (χ : HeckeCharacter F) (x : mixedSpace F) (hx : mixedEmbedding.norm x ≠ 0) :
    ‖cE χ x‖ = 1 := by
  rw [cE, dif_pos ((isUnit_iff_norm x).2 hx)]; unfold chiInf; exact Circle.norm_coe _

theorem cE_emb (χ : HeckeCharacter F) (ξ : Fˣ) :
    cE χ (mixedEmbedding F (ξ : F)) = chiInf χ (diagInf ξ) := by
  have h : IsUnit (mixedEmbedding F (ξ : F)) := ξ.isUnit.map _
  rw [cE, dif_pos h]
  congr 1
  apply Units.ext
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (mixedEmbedding F (ξ : F)) =
    algebraMap F (InfiniteAdeleRing F) ξ
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]

theorem continuous_chiInf (χ : HeckeCharacter F) : Continuous (chiInf χ) := by
  have h1 : Continuous (infIdele (F := F)) := by
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_val).prodMk continuous_const
    · exact (Units.continuous_coe_inv).prodMk continuous_const
  unfold chiInf
  exact (by fun_prop : Continuous (fun z : Circle => (z : ℂ))).comp
    (χ.continuous.comp (continuous_quotient_mk'.comp h1))

theorem cE_cont (χ : HeckeCharacter F) :
    ContinuousOn (cE χ) {x : mixedSpace F | mixedEmbedding.norm x ≠ 0} := by
  have hset : {x : mixedSpace F | mixedEmbedding.norm x ≠ 0} = {x | IsUnit x} := by
    ext x; exact (isUnit_iff_norm x).symm
  rw [hset, continuousOn_iff_continuous_restrict]
  let ι : {x : mixedSpace F | IsUnit x} → (InfiniteAdeleRing F)ˣ := fun y =>
    Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toMonoidHom y.2.unit
  have hι : Continuous ι := by
    rw [Units.continuous_iff]
    constructor
    · have : (Units.val ∘ ι) = fun y => eH.symm (y.1 : mixedSpace F) := by
        funext y; simp [ι, eH_symm_apply]
      rw [this]; exact eH.symm.continuous.comp continuous_subtype_val
    · have : (fun y => ((ι y)⁻¹ : (InfiniteAdeleRing F)ˣ).val) =
          fun y => eH.symm (Ring.inverse (y.1 : mixedSpace F)) := by
        funext y
        simp only [ι, eH_symm_apply]
        rw [← map_inv, Units.coe_map, ← Ring.inverse_unit, IsUnit.unit_spec]; rfl
      rw [this]
      refine eH.symm.continuous.comp ?_
      refine continuous_iff_continuousAt.2 fun y => ?_
      have := NormedRing.inverse_continuousAt y.2.unit
      rw [IsUnit.unit_spec] at this
      exact this.comp continuous_subtype_val.continuousAt
  have : (fun y : {x : mixedSpace F | IsUnit x} => cE χ y) = chiInf χ ∘ ι := by
    funext y
    show cE χ y.1 = chiInf χ (ι y)
    rw [cE, dif_pos (show IsUnit (y : mixedSpace F) from y.2)]
  show Continuous (fun y : {x : mixedSpace F | IsUnit x} => cE χ y)
  rw [this]
  exact (continuous_chiInf χ).comp hι

end Aux_HL
end MasulloGRH

namespace MasulloGRH
namespace Aux_HL
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
open Filter Topology MeasureTheory
open scoped Classical

variable {F : Type*} [Field F] [NumberField F]

/-! ### local norms of integers -/

theorem val_alg (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem norm_eq_one_of_val (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : Valued.v x = 1) : ‖x‖ = 1 := by
  have h1 : ‖x‖ ≤ ‖(1 : v.adicCompletion F)‖ := Valued.toNormedField.norm_le_iff.2 (by rw [h, map_one])
  have h2 : ‖(1 : v.adicCompletion F)‖ ≤ ‖x‖ := Valued.toNormedField.norm_le_iff.2 (by rw [h, map_one])
  rw [norm_one] at h1 h2; linarith

theorem val_int_eq_one (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (h : r ∉ v.asIdeal) :
    Valued.v (algebraMap F (v.adicCompletion F) (r : F)) = 1 := by
  rw [val_alg]; exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 h

theorem norm_int_le_one (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    ‖algebraMap F (v.adicCompletion F) (r : F)‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, val_alg]; exact v.valuation_le_one r

theorem norm_int_lt_one (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (h : r ∈ v.asIdeal) :
    ‖algebraMap F (v.adicCompletion F) (r : F)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, val_alg]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v r).2 h

theorem localComponent_mul (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x y : (v.adicCompletion F)ˣ) :
    χ.localComponent v (x * y) = χ.localComponent v x * χ.localComponent v y := by
  unfold HeckeCharacter.localComponent
  rw [ideleSingle_mul, QuotientGroup.mk_mul, map_mul, Circle.coe_mul]

/-! ### the finite-part coefficient -/

/-- `ψ(α) = ∏_{v ∈ S} χ_v(α)⁻¹` for `α` prime to `S`, else `0`. -/
noncomputable def psi (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F))) (α : 𝓞 F) : ℂ :=
  if h : α ≠ 0 ∧ ∀ v ∈ S, α ∉ v.asIdeal then
    (∏ v ∈ S, χ.localComponent v
      (locUnit v (Units.mk0 (algebraMap (𝓞 F) F α) (RingOfIntegers.coe_ne_zero_iff.2 h.1))))⁻¹
  else 0

/-- the masked monomial. -/
noncomputable def Wk (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ)
    (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) : ℂ :=
  mono (fun v => if v ∈ S then 0 else zv χ s v) k

theorem span_ne_zero (α : 𝓞 F) (hα : α ≠ 0) : Ideal.span {α} ≠ 0 :=
  fun h => hα (Ideal.span_singleton_eq_bot.1 h)

/-- exponent vector of `(α)`. -/
noncomputable def kvec (α : 𝓞 F) (hα : α ≠ 0) : HeightOneSpectrum (𝓞 F) →₀ ℕ :=
  expoVec (Ideal.span {α}) (span_ne_zero α hα)

theorem kvec_zero_iff (α : 𝓞 F) (hα : α ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    kvec α hα v = 0 ↔ α ∉ v.asIdeal := by
  have h := valuation_eq_expo α hα v
  rw [kvec, expoVec_apply]
  have h1 : v.valuation F (α : F) = 1 ↔ α ∉ v.asIdeal :=
    HeightOneSpectrum.valuation_eq_one_iff_notMem v
  rw [← h1, h]
  constructor
  · intro h0; rw [h0]; simp
  · intro h0
    have : (-(expo (Ideal.span {α}) v : ℤ)) = 0 :=
      WithZero.exp_injective (h0.trans WithZero.exp_zero.symm)
    omega

theorem npow_absNorm (α : 𝓞 F) (hα : α ≠ 0) (s : ℂ) :
    ((Ideal.absNorm (idealOf (kvec α hα)) : ℕ) : ℂ) ^ (-s) =
      npow (mixedEmbedding F (α : F)) (-s) := by
  rw [kvec, idealOf_expoVec, Ideal.absNorm_span_singleton]
  have hN : (((Algebra.norm ℤ α).natAbs : ℕ) : ℝ) = mixedEmbedding.norm (mixedEmbedding F (α : F)) := by
    rw [mixedEmbedding.norm_eq_norm, ← Algebra.coe_norm_int, Rat.cast_abs, Rat.cast_intCast, Nat.cast_natAbs, Int.cast_abs]
  have hne : (((Algebra.norm ℤ α).natAbs : ℕ) : ℂ) ≠ 0 := by
    have : Algebra.norm ℤ α ≠ 0 := by rwa [Ne, Algebra.norm_eq_zero_iff]
    exact_mod_cast Int.natAbs_ne_zero.2 this
  unfold npow
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.natCast_log, hN, mul_comm]

theorem hecke_W (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ε : HeightOneSpectrum (𝓞 F) → ℝ) (hε : ∀ v, 0 < ε v)
    (htriv : ∀ g ∈ levelSet (S : Set (HeightOneSpectrum (𝓞 F))) ε, χ (QuotientGroup.mk g) = 1)
    (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (α : 𝓞 F) (hα : α ≠ 0) (s : ℂ) :
    Wk χ S s (kvec α hα) =
      psi χ S α * (cE χ (mixedEmbedding F (α : F)))⁻¹ * npow (mixedEmbedding F (α : F)) (-s) := by
  set k := kvec α hα
  by_cases hS : ∀ v ∈ S, α ∉ v.asIdeal
  · have hkS : ∀ v ∈ S, k v = 0 := fun v hv => (kvec_zero_iff α hα v).2 (hS v hv)
    have hmono : Wk χ S s k = mono (zv χ s) k := by
      unfold Wk mono
      refine Finsupp.prod_congr fun v hv => ?_
      show (if v ∈ S then 0 else zv χ s v) ^ k v = zv χ s v ^ k v
      rw [if_neg fun hvS => (Finsupp.mem_support_iff.1 hv) (hkS v hvS)]
    rw [hmono, mono_zv_eq, npow_absNorm]
    set ξ : Fˣ := Units.mk0 (algebraMap (𝓞 F) F α) (RingOfIntegers.coe_ne_zero_iff.2 hα)
    have hrel := hecke_relation_general χ S ε hε htriv hun ξ k
      (fun v => by
        have := valuation_eq_expo α hα v
        simpa [k, kvec, expoVec_apply, ξ] using this) hkS
    have hcE : cE χ (mixedEmbedding F (α : F)) = chiInf χ (diagInf ξ) := cE_emb χ ξ
    rw [psi, dif_pos ⟨hα, hS⟩, hcE]
    have hchi : chiIdeal χ k = (chiInf χ (diagInf ξ) *
        ∏ v ∈ S, χ.localComponent v (locUnit v ξ))⁻¹ := by
      rw [mul_assoc] at hrel
      exact eq_inv_of_mul_eq_one_left hrel
    unfold chiIdeal at hchi ⊢
    rw [hchi, mul_inv]
    ring
  · push_neg at hS
    obtain ⟨v, hv, hαv⟩ := hS
    have hkv : k v ≠ 0 := by rw [Ne, kvec_zero_iff]; simpa using hαv
    have : Wk χ S s k = 0 := by
      unfold Wk mono Finsupp.prod
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hkv) (by
        show (if v ∈ S then 0 else zv χ s v) ^ k v = 0
        rw [if_pos hv, zero_pow hkv])
    rw [this, psi, dif_neg (fun h => h.2 v hv hαv), zero_mul, zero_mul]

theorem psi_bd (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F))) (α : 𝓞 F) :
    ‖psi χ S α‖ ≤ 1 := by
  unfold psi
  split_ifs
  · rw [norm_inv, norm_prod]
    simp only [HeckeCharacter.localComponent, Circle.norm_coe, Finset.prod_const_one, inv_one,
      le_refl]
  · simp

theorem kvec_unit (u : (𝓞 F)ˣ) (α : 𝓞 F) (hα : α ≠ 0) (huα : (u : 𝓞 F) * α ≠ 0) :
    kvec ((u : 𝓞 F) * α) huα = kvec α hα := by
  unfold kvec
  congr 1
  exact Ideal.span_singleton_mul_left_unit u.isUnit α

theorem psi_unit (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ε : HeightOneSpectrum (𝓞 F) → ℝ) (hε : ∀ v, 0 < ε v)
    (htriv : ∀ g ∈ levelSet (S : Set (HeightOneSpectrum (𝓞 F))) ε, χ (QuotientGroup.mk g) = 1)
    (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (u : (𝓞 F)ˣ) (α : 𝓞 F) :
    psi χ S ((u : 𝓞 F) * α) = cE χ (mixedEmbedding F ((u : 𝓞 F) : F)) * psi χ S α := by
  by_cases hα : α = 0
  · subst hα
    simp [psi]
  have huα : (u : 𝓞 F) * α ≠ 0 := mul_ne_zero u.ne_zero hα
  have h1 := hecke_W χ S ε hε htriv hun _ huα 0
  have h2 := hecke_W χ S ε hε htriv hun α hα 0
  rw [kvec_unit u α hα huα, h2] at h1
  have hNu : mixedEmbedding.norm (mixedEmbedding F ((u : 𝓞 F) : F)) ≠ 0 := by
    rw [norm_unit u]; exact one_ne_zero
  have hNα : mixedEmbedding.norm (mixedEmbedding F (α : F)) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_norm_emb α hα)).ne'
  have hemb : mixedEmbedding F (((u : 𝓞 F) * α : 𝓞 F) : F) =
      mixedEmbedding F ((u : 𝓞 F) : F) * mixedEmbedding F (α : F) := by
    push_cast; rw [map_mul]
  have hc := cE_mul χ _ _ hNu hNα
  simp only [neg_zero] at h1
  have hnp : ∀ y : mixedSpace F, npow y 0 = 1 := fun y => by simp [npow]
  rw [hnp, hnp, mul_one, mul_one, hemb, hc] at h1
  have hcu : cE χ (mixedEmbedding F ((u : 𝓞 F) : F)) ≠ 0 := by
    intro h; have := cE_norm χ _ hNu; rw [h, norm_zero] at this; exact zero_ne_one this
  have hcα : cE χ (mixedEmbedding F (α : F)) ≠ 0 := by
    intro h; have := cE_norm χ _ hNα; rw [h, norm_zero] at this; exact zero_ne_one this
  field_simp at h1
  rw [← h1]; ring

end Aux_HL
end MasulloGRH

namespace MasulloGRH
namespace Aux_HL
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
open Filter Topology MeasureTheory
open scoped Classical nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

theorem exists_m0 (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : HeightOneSpectrum (𝓞 F) → ℝ)
    (hε : ∀ v, 0 < ε v) : ∃ m0 : ℕ, 0 < m0 ∧ ∀ v ∈ S, (m0 : 𝓞 F) ∈ v.asIdeal ∧
      ‖algebraMap F (v.adicCompletion F) (m0 : F)‖ < ε v := by
  set P : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal
  have hP0 : 0 < P := Finset.prod_pos fun v _ => by have := two_le_absNorm v; omega
  have hPmem : ∀ v ∈ S, (P : 𝓞 F) ∈ v.asIdeal := fun v hv => by
    simp only [P]
    rw [Nat.cast_prod, ← Finset.mul_prod_erase S _ hv]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hPlt : ∀ v ∈ S, ‖algebraMap F (v.adicCompletion F) (P : F)‖ < 1 := fun v hv => by
    have := norm_int_lt_one v (P : 𝓞 F) (hPmem v hv); simpa using this
  have hev : ∀ᶠ j in atTop, ∀ v ∈ S, ‖algebraMap F (v.adicCompletion F) (P : F)‖ ^ j < ε v :=
    (eventually_all_finset S).2 fun v hv =>
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hPlt v hv)).eventually
        (gt_mem_nhds (hε v))
  obtain ⟨j, hj, hj1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  refine ⟨P ^ j, pow_pos hP0 j, fun v hv => ⟨?_, ?_⟩⟩
  · push_cast; exact Ideal.pow_mem_of_mem _ (hPmem v hv) j hj1
  · rw [Nat.cast_pow, map_pow, norm_pow]; exact hj v hv

theorem psi_per_nz (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ε : HeightOneSpectrum (𝓞 F) → ℝ)
    (hloc : ∀ v (x : (v.adicCompletion F)ˣ), Valued.v (x : v.adicCompletion F) = 1 →
        ‖(x : v.adicCompletion F) - 1‖ < ε v → χ.localComponent v x = 1)
    (m0 : ℕ) (hm0 : ∀ v ∈ S, (m0 : 𝓞 F) ∈ v.asIdeal ∧
      ‖algebraMap F (v.adicCompletion F) (m0 : F)‖ < ε v) (α β : 𝓞 F)
    (hα0 : α ≠ 0) (hα1 : α + (m0 : 𝓞 F) * β ≠ 0) :
    psi χ S (α + (m0 : 𝓞 F) * β) = psi χ S α := by
  set α' := α + (m0 : 𝓞 F) * β
  have hiff : ∀ v ∈ S, (α' ∈ v.asIdeal ↔ α ∈ v.asIdeal) := fun v hv =>
    Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (hm0 v hv).1)
  have hcond : (α' ≠ 0 ∧ ∀ v ∈ S, α' ∉ v.asIdeal) ↔ (α ≠ 0 ∧ ∀ v ∈ S, α ∉ v.asIdeal) := by
    constructor
    · rintro ⟨-, h⟩
      exact ⟨hα0, fun v hv hα => h v hv ((hiff v hv).2 hα)⟩
    · rintro ⟨-, h⟩
      exact ⟨hα1, fun v hv hα => h v hv ((hiff v hv).1 hα)⟩
  unfold psi
  by_cases h : α ≠ 0 ∧ ∀ v ∈ S, α ∉ v.asIdeal
  · have h2 := hcond.2 h
    rw [dif_pos h2, dif_pos h]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    set a := locUnit v (Units.mk0 (algebraMap (𝓞 F) F α) (RingOfIntegers.coe_ne_zero_iff.2 h.1))
    set a' := locUnit v (Units.mk0 (algebraMap (𝓞 F) F α') (RingOfIntegers.coe_ne_zero_iff.2 h2.1))
    have ha : (a : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (α : F) := rfl
    have ha' : (a' : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (α' : F) := rfl
    have hva : Valued.v (a : v.adicCompletion F) = 1 := by rw [ha]; exact val_int_eq_one v α (h.2 v hv)
    have hva' : Valued.v (a' : v.adicCompletion F) = 1 := by
      rw [ha']; exact val_int_eq_one v α' (h2.2 v hv)
    have hx : a' = (a' * a⁻¹) * a := by rw [inv_mul_cancel_right]
    rw [hx, localComponent_mul, hloc v (a' * a⁻¹) ?_ ?_, one_mul]
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hva, hva', inv_one, one_mul]
    · have hna : ‖(a : v.adicCompletion F)‖ = 1 := norm_eq_one_of_val v _ hva
      have hane : (a : v.adicCompletion F) ≠ 0 := a.ne_zero
      have hdiff : (a' : v.adicCompletion F) - a =
          algebraMap F (v.adicCompletion F) (m0 : F) * algebraMap F (v.adicCompletion F) (β : F) := by
        rw [ha, ha', ← map_sub, ← map_mul]
        congr 1
        simp [α']
      have : ((a' * a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
          ((a' : v.adicCompletion F) - a) * (a : v.adicCompletion F)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ hane]
      rw [this, hdiff, norm_mul, norm_mul, norm_inv, hna, inv_one, mul_one]
      calc ‖algebraMap F (v.adicCompletion F) (m0 : F)‖ * ‖algebraMap F (v.adicCompletion F) (β : F)‖
          ≤ ‖algebraMap F (v.adicCompletion F) (m0 : F)‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_int_le_one v β) (norm_nonneg _)
        _ < ε v := by rw [mul_one]; exact (hm0 v hv).2
  · rw [dif_neg (fun h' => h (hcond.1 h')), dif_neg h]

theorem idealOf_le (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : k v ≠ 0) :
    idealOf k ≤ v.asIdeal := by
  unfold idealOf Finsupp.prod
  rw [← Finset.mul_prod_erase _ _ (Finsupp.mem_support_iff.2 h)]
  exact Ideal.mul_le_left.trans (Ideal.pow_le_self h)

theorem idealOf_add (k k' : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    idealOf (k + k') = idealOf k * idealOf k' := by
  unfold idealOf
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/-- the ideal class of an exponent vector. -/
noncomputable def cls (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) : ClassGroup (𝓞 F) :=
  ClassGroup.mk0 ⟨idealOf k, mem_nonZeroDivisors_of_ne_zero (idealOf_ne_zero k)⟩

theorem cls_add (k k' : HeightOneSpectrum (𝓞 F) →₀ ℕ) : cls (k + k') = cls k * cls k' := by
  unfold cls
  rw [← map_mul]
  congr 1
  exact Subtype.ext (idealOf_add k k')

theorem exists_rep (S : Finset (HeightOneSpectrum (𝓞 F))) (hSne : S.Nonempty)
    (c : ClassGroup (𝓞 F)) :
    ∃ k : HeightOneSpectrum (𝓞 F) →₀ ℕ, cls k = c⁻¹ ∧ ∀ v ∈ S, k v = 0 := by
  obtain ⟨I0, hI0⟩ := ClassGroup.mk0_surjective c
  set 𝔪 : Ideal (𝓞 F) := ∏ v ∈ S, v.asIdeal
  have h𝔪 : 𝔪 ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => v.ne_bot
  have hI00 : (I0 : Ideal (𝓞 F)) ≠ 0 := nonZeroDivisors.coe_ne_zero I0
  have hle : (I0 : Ideal (𝓞 F)) * 𝔪 ≤ I0 := Ideal.mul_le_left
  have hne : (I0 : Ideal (𝓞 F)) * 𝔪 ≠ 0 := mul_ne_zero hI00 h𝔪
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
  have hgI : Ideal.span {g} ≤ (I0 : Ideal (𝓞 F)) := hg ▸ le_sup_right
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.2 hgI
  obtain ⟨v0, hv0⟩ := hSne
  have h𝔪v : ∀ v ∈ S, 𝔪 ≤ v.asIdeal := fun v hv => by
    simp only [𝔪]; rw [← Finset.mul_prod_erase S _ hv]; exact Ideal.mul_le_left
  have hcop : 𝔪 ⊔ J' = ⊤ := by
    have h1 : (I0 : Ideal (𝓞 F)) * (𝔪 ⊔ J') = (I0 : Ideal (𝓞 F)) * ⊤ := by
      rw [Ideal.mul_sup, ← hJ', hg, Ideal.mul_top]
    exact mul_left_cancel₀ hI00 h1
  have hJ'0 : J' ≠ 0 := by
    intro h0
    rw [h0, Submodule.zero_eq_bot, sup_bot_eq] at hcop
    exact v0.isPrime.ne_top (top_le_iff.1 (hcop ▸ h𝔪v v0 hv0))
  refine ⟨expoVec J' hJ'0, ?_, fun v hv => ?_⟩
  · have hprin : ClassGroup.mk0 ⟨Ideal.span {g}, mem_nonZeroDivisors_of_ne_zero (by
        rw [hJ']; exact mul_ne_zero hI00 hJ'0)⟩ = 1 :=
      (ClassGroup.mk0_eq_one_iff _).2 ⟨g, rfl⟩
    have hsplit : (⟨Ideal.span {g}, mem_nonZeroDivisors_of_ne_zero (by
        rw [hJ']; exact mul_ne_zero hI00 hJ'0)⟩ : (Ideal (𝓞 F))⁰) =
        I0 * ⟨J', mem_nonZeroDivisors_of_ne_zero hJ'0⟩ := Subtype.ext hJ'
    rw [hsplit, map_mul, hI0] at hprin
    unfold cls
    have : (⟨idealOf (expoVec J' hJ'0), mem_nonZeroDivisors_of_ne_zero (idealOf_ne_zero _)⟩ :
        (Ideal (𝓞 F))⁰) = ⟨J', mem_nonZeroDivisors_of_ne_zero hJ'0⟩ :=
      Subtype.ext (idealOf_expoVec J' hJ'0)
    rw [this]
    exact eq_inv_of_mul_eq_one_right hprin
  · by_contra hk
    have h1 : J' ≤ v.asIdeal := by
      have := idealOf_le (expoVec J' hJ'0) v hk
      rwa [idealOf_expoVec] at this
    exact v.isPrime.ne_top (top_le_iff.1 (hcop ▸ sup_le (h𝔪v v hv) h1))

end Aux_HL
end MasulloGRH

namespace MasulloGRH
namespace Aux_HL
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
open Filter Topology MeasureTheory
open scoped Classical nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

theorem expoVec_congr (I I' : Ideal (𝓞 F)) (hI : I ≠ 0) (hI' : I' ≠ 0) (h : I = I') :
    expoVec I hI = expoVec I' hI' := by subst h; rfl

theorem expoVec_idealOf (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    expoVec (idealOf k) (idealOf_ne_zero k) = k :=
  idealOf_injective (idealOf_expoVec _ _)

theorem le_expoVec_iff (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) (I : Ideal (𝓞 F)) (hI : I ≠ 0) :
    k ≤ expoVec I hI ↔ I ≤ idealOf k := by
  constructor
  · intro h
    have : I = idealOf k * idealOf (expoVec I hI - k) := by
      rw [← idealOf_add, add_tsub_cancel_of_le h, idealOf_expoVec]
    rw [this]; exact Ideal.mul_le_left
  · intro h
    obtain ⟨K', hK'⟩ := Ideal.dvd_iff_le.2 h
    have hK'0 : K' ≠ 0 := by rintro rfl; rw [mul_zero] at hK'; exact hI hK'
    have : I = idealOf (k + expoVec K' hK'0) := by rw [idealOf_add, idealOf_expoVec, hK']
    rw [expoVec_congr I _ hI (idealOf_ne_zero _) this, expoVec_idealOf]
    exact le_self_add

variable (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem Wk_add (s : ℂ) (k k' : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    Wk χ S s (k + k') = Wk χ S s k * Wk χ S s k' := by
  unfold Wk mono
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem Wk_ne_zero (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (s : ℂ)
    (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) (hk : ∀ v ∈ S, k v = 0) : Wk χ S s k ≠ 0 := by
  unfold Wk mono Finsupp.prod
  refine Finset.prod_ne_zero_iff.2 fun v hv => ?_
  have hvS : v ∉ S := fun h => (Finsupp.mem_support_iff.1 hv) (hk v h)
  show (if v ∈ S then 0 else zv χ s v) ^ k v ≠ 0
  rw [if_neg hvS]
  refine pow_ne_zero _ ?_
  unfold zv
  obtain ⟨π, -, hπ⟩ := primeValue_eq χ v (hun v hvS)
  refine mul_ne_zero ?_ ?_
  · rw [hπ]; intro h
    have := Circle.norm_coe (χ (QuotientGroup.mk (ideleSingle v π)))
    unfold HeckeCharacter.localComponent at h
    rw [h, norm_zero] at this; exact zero_ne_one this
  · have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      have := two_le_absNorm v; exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
    rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _

theorem Wk_differentiable (k : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    Differentiable ℂ (fun s => Wk χ S s k) := by
  have hz : ∀ v, Differentiable ℂ (fun z => if v ∈ S then 0 else zv χ z v) := fun v => by
    by_cases hv : v ∈ S
    · simp only [hv, if_true]; exact differentiable_const 0
    · simp only [hv, if_false]; exact differentiable_zv χ v
  unfold Wk mono Finsupp.prod
  exact Differentiable.fun_finset_prod (fun v _ => (hz v).pow _)

theorem Wk_summable (s : ℂ) (hs : 1 < s.re) : Summable fun k => ‖Wk χ S s k‖ := by
  have hle : ∀ v, ‖(if v ∈ S then 0 else zv χ s v)‖ ≤ ‖zv χ s v‖ := by
    intro v; by_cases h : v ∈ S <;> simp [h]
  exact summable_mono _ (fun v => (hle v).trans (norm_zv_le_half χ s hs.le v))
    ((summable_zv χ s hs).of_nonneg_of_le (fun _ => norm_nonneg _) hle)

end Aux_HL
end MasulloGRH

namespace MasulloGRH
namespace Aux_HL
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open IsDedekindDomain Filter Topology MeasureTheory
open scoped Classical nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]
variable (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- the lattice series attached to an integral ideal `J`. -/
noncomputable def GJ (J : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  ∑' a : fundamentalCone.integerSet F,
    (if (fundamentalCone.preimageOfMemIntegerSet a : 𝓞 F) ∈ J then
      psi χ S (fundamentalCone.preimageOfMemIntegerSet a) else 0) *
      (cE χ a)⁻¹ * npow (a : mixedSpace F) (-s)

theorem GJ_summable (J : Ideal (𝓞 F)) (s : ℂ) (hs : 1 < s.re) :
    Summable fun a : fundamentalCone.integerSet F =>
    (if (fundamentalCone.preimageOfMemIntegerSet a : 𝓞 F) ∈ J then
      psi χ S (fundamentalCone.preimageOfMemIntegerSet a) else 0) *
      (cE χ a)⁻¹ * npow (a : mixedSpace F) (-s) := by
  refine Summable.of_norm_bounded (summable_integerSet s.re hs) fun a => ?_
  have hN := fundamentalCone.norm_pos_of_mem a.2.1
  rw [norm_mul, norm_mul, norm_inv, cE_norm χ _ hN.ne', inv_one, mul_one,
    CData.npow_norm _ hN, Complex.neg_re]
  refine mul_le_of_le_one_left (Real.rpow_nonneg hN.le _) ?_
  split_ifs
  · exact psi_bd χ S _
  · simp

theorem GJ_term (ε : HeightOneSpectrum (𝓞 F) → ℝ) (hε : ∀ v, 0 < ε v)
    (htriv : ∀ g ∈ levelSet (S : Set (HeightOneSpectrum (𝓞 F))) ε, χ (QuotientGroup.mk g) = 1)
    (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (J : Ideal (𝓞 F)) (s : ℂ)
    (a : fundamentalCone.integerSet F) :
    (if (fundamentalCone.preimageOfMemIntegerSet a : 𝓞 F) ∈ J then
      psi χ S (fundamentalCone.preimageOfMemIntegerSet a) else 0) *
      (cE χ a)⁻¹ * npow (a : mixedSpace F) (-s) =
    if (fundamentalCone.preimageOfMemIntegerSet a : 𝓞 F) ∈ J then
      Wk χ S s (kvec _ (nonZeroDivisors.coe_ne_zero (fundamentalCone.preimageOfMemIntegerSet a)))
    else 0 := by
  split_ifs
  · rw [hecke_W χ S ε hε htriv hun, fundamentalCone.mixedEmbedding_preimageOfMemIntegerSet]
  · simp

theorem principal_part (ε : HeightOneSpectrum (𝓞 F) → ℝ) (hε : ∀ v, 0 < ε v)
    (htriv : ∀ g ∈ levelSet (S : Set (HeightOneSpectrum (𝓞 F))) ε, χ (QuotientGroup.mk g) = 1)
    (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (s : ℂ) (hs : 1 < s.re)
    (k0 : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    ∑' k, (if cls k = 1 ∧ k0 ≤ k then Wk χ S s k else 0) =
      ((Nat.card (torsion F) : ℂ))⁻¹ * GJ χ S (idealOf k0) s := by
  set J := idealOf k0
  set e := fundamentalCone.integerSetEquiv F
  let h : {I : (Ideal (𝓞 F))⁰ // Submodule.IsPrincipal I.1} → ℂ := fun P =>
    if (P.1 : Ideal (𝓞 F)) ≤ J then
      Wk χ S s (expoVec P.1.1 (nonZeroDivisors.coe_ne_zero P.1)) else 0
  -- the integer-set sum in terms of principal ideals
  let f : fundamentalCone.integerSet F → ℂ := fun a =>
    if (fundamentalCone.preimageOfMemIntegerSet a : 𝓞 F) ∈ J then
      Wk χ S s (kvec _ (nonZeroDivisors.coe_ne_zero (fundamentalCone.preimageOfMemIntegerSet a)))
    else 0
  have hGf : GJ χ S J s = ∑' a, f a := by
    unfold GJ; exact tsum_congr fun a => GJ_term χ S ε hε htriv hun J s a
  have hfs : Summable f := by
    have := GJ_summable χ S J s hs
    refine this.congr fun a => GJ_term χ S ε hε htriv hun J s a
  have hfe : ∀ p, f (e.symm p) = h p.1 := by
    intro p
    have hsp : Ideal.span {(fundamentalCone.preimageOfMemIntegerSet (e.symm p) : 𝓞 F)} =
        (p.1.1 : Ideal (𝓞 F)) := by
      have := fundamentalCone.integerSetEquiv_apply_fst (e.symm p)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    simp only [f, h]
    rw [← Ideal.span_singleton_le_iff_mem, hsp]
    split_ifs
    · congr 1
      exact expoVec_congr _ _ _ _ hsp
    · rfl
  have hGh : GJ χ S J s = (Nat.card (torsion F) : ℂ) * ∑' P, h P := by
    rw [hGf, ← e.symm.tsum_eq]
    simp only [hfe]
    have hs2 : Summable fun p : {I : (Ideal (𝓞 F))⁰ // Submodule.IsPrincipal I.1} × torsion F =>
        h p.1 := by
      have := e.symm.summable_iff.2 hfs
      exact this.congr fun p => hfe p
    rw [hs2.tsum_prod]
    simp only [tsum_const, nsmul_eq_mul]
    rw [tsum_mul_left]
  -- principal ideals vs exponent vectors
  let g : {I : (Ideal (𝓞 F))⁰ // Submodule.IsPrincipal I.1} → (HeightOneSpectrum (𝓞 F) →₀ ℕ) :=
    fun P => expoVec P.1.1 (nonZeroDivisors.coe_ne_zero P.1)
  have hg : Function.Injective g := by
    intro P Q hPQ
    have h1 := congrArg idealOf hPQ
    simp only [g, idealOf_expoVec] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hfg : ∀ P, (fun k => if cls k = 1 ∧ k0 ≤ k then Wk χ S s k else 0) (g P) = h P := by
    intro P
    have hc : cls (g P) = 1 := by
      unfold cls
      have : (⟨idealOf (g P), mem_nonZeroDivisors_of_ne_zero (idealOf_ne_zero _)⟩ :
          (Ideal (𝓞 F))⁰) = P.1 := Subtype.ext (idealOf_expoVec _ _)
      rw [this]
      have h2 := (ClassGroup.mk0_eq_one_iff P.1.2).2 P.2
      exact h2
    simp only [h, hc, true_and]
    by_cases hP : (P.1 : Ideal (𝓞 F)) ≤ J
    · rw [if_pos ((le_expoVec_iff _ _ _).2 hP), if_pos hP]
    · rw [if_neg (fun h' => hP ((le_expoVec_iff _ _ _).1 h')), if_neg hP]
  have hsupp : Function.support (fun k => if cls k = 1 ∧ k0 ≤ k then Wk χ S s k else 0) ⊆
      Set.range g := by
    intro k hk
    have hk1 : cls k = 1 := by
      by_contra hc; apply hk; simp [hc]
    have hprin : Submodule.IsPrincipal (idealOf k) :=
      (ClassGroup.mk0_eq_one_iff _).1 hk1
    refine ⟨⟨⟨idealOf k, mem_nonZeroDivisors_of_ne_zero (idealOf_ne_zero k)⟩, hprin⟩, ?_⟩
    exact expoVec_idealOf k
  rw [← hg.tsum_eq hsupp]
  simp only [hfg]
  rw [hGh, ← mul_assoc, inv_mul_cancel₀ (by
    have : 0 < Nat.card (torsion F) := Nat.card_pos
    exact_mod_cast this.ne'), one_mul]

theorem fiber (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (s : ℂ) (c : ClassGroup (𝓞 F))
    (kc : HeightOneSpectrum (𝓞 F) →₀ ℕ) (hkc : cls kc = c⁻¹) (hkcS : ∀ v ∈ S, kc v = 0) :
    ∑' k, (if cls k = c then Wk χ S s k else 0) =
      (Wk χ S s kc)⁻¹ * ∑' k, (if cls k = 1 ∧ kc ≤ k then Wk χ S s k else 0) := by
  have hne := Wk_ne_zero χ S hun s kc hkcS
  have hsupp : Function.support (fun k => if cls k = 1 ∧ kc ≤ k then Wk χ S s k else 0) ⊆
      Set.range (fun k => k + kc) := by
    intro k hk
    have hle : kc ≤ k := by by_contra h; apply hk; simp [h]
    exact ⟨k - kc, tsub_add_cancel_of_le hle⟩
  have h1 : ∑' k, (if cls k = 1 ∧ kc ≤ k then Wk χ S s k else 0) =
      (∑' k, (if cls k = c then Wk χ S s k else 0)) * Wk χ S s kc := by
    rw [← (add_left_injective kc).tsum_eq hsupp, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    have : cls (k + kc) = 1 ↔ cls k = c := by
      rw [cls_add, hkc, mul_inv_eq_one]
    simp only [this, le_add_self, and_true, Wk_add, ite_mul, zero_mul]
  rw [h1, ← mul_assoc, mul_comm (Wk χ S s kc)⁻¹, mul_assoc, inv_mul_cancel₀ hne, mul_one]

theorem decomp (ε : HeightOneSpectrum (𝓞 F) → ℝ) (hε : ∀ v, 0 < ε v)
    (htriv : ∀ g ∈ levelSet (S : Set (HeightOneSpectrum (𝓞 F))) ε, χ (QuotientGroup.mk g) = 1)
    (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (s : ℂ) (hs : 1 < s.re)
    (kc : ClassGroup (𝓞 F) → (HeightOneSpectrum (𝓞 F) →₀ ℕ))
    (hkc : ∀ c, cls (kc c) = c⁻¹ ∧ ∀ v ∈ S, kc c v = 0) :
    ∑' k, Wk χ S s k = ∑ c, (Wk χ S s (kc c))⁻¹ *
      (((Nat.card (torsion F) : ℂ))⁻¹ * GJ χ S (idealOf (kc c)) s) := by
  have h1 : ∀ k, Wk χ S s k = ∑ c, if cls k = c then Wk χ S s k else 0 := fun k => by
    rw [Finset.sum_ite_eq]; simp
  rw [tsum_congr h1, Summable.tsum_finsetSum (fun c _ => ?_)]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [fiber χ S hun s c (kc c) (hkc c).1 (hkc c).2,
      principal_part χ S ε hε htriv hun s hs (kc c)]
  · refine Summable.of_norm_bounded (Wk_summable χ S s hs) fun k => ?_
    split_ifs <;> simp

end Aux_HL
end MasulloGRH



namespace MasulloGRH
namespace Aux_MR
open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

section FD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iteratedDeriv_expI (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (c * t)) = fun t : ℝ => c ^ n * Complex.exp (c * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c)
    have h : HasDerivAt (fun t : ℝ => c ^ n * Complex.exp (c * t))
        (c ^ n * (Complex.exp (c * t) * c)) t := (h1.cexp).const_mul _
    rw [h.deriv, pow_succ]; ring

lemma norm_iteratedFDeriv_expI (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n (fun t : ℝ => Complex.exp (-Complex.I * t)) t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expI]
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul, Complex.norm_exp]
  simp

lemma contDiff_expI : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (-Complex.I * t)) := by
  have : ContDiff ℝ ∞ (fun t : ℝ => -Complex.I * (t : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  exact this.cexp

/-- derivative bound for `u · exp(-iτh)`, polynomial in `τ`. -/
theorem deriv_bound_mod (u h : E → ℝ) (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h)
    (hub : ∀ i, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i u x‖ ≤ C)
    (hhb : ∀ i, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i h x‖ ≤ C) (n : ℕ) :
    ∃ C, ∀ (τ : ℝ) x, ‖iteratedFDeriv ℝ n
      (fun x => (u x : ℂ) * Complex.exp (-Complex.I * ((τ * h x : ℝ) : ℂ))) x‖ ≤
        C * (1 + |τ|) ^ n := by
  choose Cu hCu using hub
  choose Ch hCh using hhb
  set Hm : ℝ := ∑ i ∈ Finset.range (n + 1), |Ch i| with hHm
  set Um : ℝ := ∑ i ∈ Finset.range (n + 1), |Cu i| with hUm
  have hHm0 : 0 ≤ Hm := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hUm0 : 0 ≤ Um := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hChle : ∀ i ≤ n, |Ch i| ≤ Hm := fun i hi =>
    Finset.single_le_sum (f := fun i => |Ch i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  have hCule : ∀ i ≤ n, |Cu i| ≤ Um := fun i hi =>
    Finset.single_le_sum (f := fun i => |Cu i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Um *
    ((n - i).factorial * (1 + Hm) ^ (n - i)), fun τ x => ?_⟩
  set U : E → ℂ := fun x => (u x : ℂ)
  set g : ℝ → ℂ := fun t => Complex.exp (-Complex.I * t)
  set f : E → ℝ := fun x => τ * h x
  have hU : ContDiff ℝ ∞ U := Complex.ofRealCLM.contDiff.comp hu
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul hh
  have hW : ContDiff ℝ ∞ (g ∘ f) := contDiff_expI.comp hf
  have hfun : (fun x => (u x : ℂ) * Complex.exp (-Complex.I * ((τ * h x : ℝ) : ℂ))) =
      fun x => U x * (g ∘ f) x := rfl
  rw [hfun]
  have hUn : ∀ i, ‖iteratedFDeriv ℝ i U x‖ = ‖iteratedFDeriv ℝ i u x‖ := fun i =>
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hu.contDiffAt (x := x)) (by exact_mod_cast le_top)
  set Dτ : ℝ := (1 + |τ|) * (1 + Hm)
  have hDτ1 : 1 ≤ Dτ := by
    have : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    have : 1 ≤ 1 + Hm := by linarith
    nlinarith
  have hfD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ Dτ ^ i := by
    intro i hi1 hin
    have e : iteratedFDeriv ℝ i f x = τ • iteratedFDeriv ℝ i h x :=
      iteratedFDeriv_const_smul_apply' (a := τ) ((hh.of_le (by exact_mod_cast le_top)).contDiffAt)
    rw [e, norm_smul, Real.norm_eq_abs]
    calc |τ| * ‖iteratedFDeriv ℝ i h x‖ ≤ (1 + |τ|) * (1 + Hm) := by
          have h1 : ‖iteratedFDeriv ℝ i h x‖ ≤ 1 + Hm :=
            (hCh i x).trans ((le_abs_self _).trans ((hChle i hin).trans (by linarith)))
          have h2 : |τ| ≤ 1 + |τ| := by linarith
          exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = Dτ ^ 1 := (pow_one _).symm
      _ ≤ Dτ ^ i := pow_le_pow_right₀ hDτ1 hi1
  have hWb : ∀ m ≤ n, ‖iteratedFDeriv ℝ m (g ∘ f) x‖ ≤ m.factorial * 1 * Dτ ^ m := by
    intro m hm
    exact norm_iteratedFDeriv_comp_le contDiff_expI hf (by exact_mod_cast le_top) x
      (fun i _ => (norm_iteratedFDeriv_expI i (f x)).le)
      (fun i hi1 hi2 => hfD i hi1 (hi2.trans hm))
  refine (norm_iteratedFDeriv_mul_le hU hW x (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [hUn i]
  have h1 : ‖iteratedFDeriv ℝ i u x‖ ≤ Um := (hCu i x).trans ((le_abs_self _).trans (hCule i hi'))
  have h2 := hWb (n - i) (Nat.sub_le n i)
  have h3 : Dτ ^ (n - i) ≤ (1 + |τ|) ^ n * (1 + Hm) ^ (n - i) := by
    rw [mul_pow]
    have : (1:ℝ) ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ this (Nat.sub_le n i)) (by positivity)
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (n - i) (g ∘ f) x‖
      ≤ (n.choose i : ℝ) * Um * ((n - i).factorial * 1 * Dτ ^ (n - i)) := by gcongr
    _ ≤ (n.choose i : ℝ) * Um * ((n - i).factorial * ((1 + |τ|) ^ n * (1 + Hm) ^ (n - i))) := by
        rw [mul_one]; gcongr
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

/-- **Fourier decay of a family**, uniformly polynomial in the parameter. -/
theorem fourier_decay_family (G : ℝ → EuclideanSpace ℝ ι → ℂ) (R : ℝ)
    (hR : ∀ τ x, R < ‖x‖ → G τ x = 0)
    (hder : ∀ n, ∃ C, ∀ τ x, ‖iteratedFDeriv ℝ n (G τ) x‖ ≤ C * (1 + |τ|) ^ n) (M : ℕ) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ (τ : ℝ) (H : 𝓢(EuclideanSpace ℝ ι, ℂ)), (⇑H = G τ) → ∀ ξ,
      (1 + ‖ξ‖) ^ M * ‖𝓕 (⇑H) ξ‖ ≤ K * (1 + |τ|) ^ N := by
  set V := EuclideanSpace ℝ ι
  have hp := schwartz_withSeminorms ℂ V ℂ
  set I0 : Finset (ℕ × ℕ) := Finset.Iic (M, 0)
  have hq : ∀ m : ℕ × ℕ, ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      (SchwartzMap.seminorm ℂ m.1 m.2).comp
        ((SchwartzMap.fourierTransformCLM ℂ : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
        ≤ C • s.sup (schwartzSeminormFamily ℂ V ℂ) := by
    intro m
    refine Seminorm.bound_of_continuous hp _ ?_
    exact (hp.continuous_seminorm m).comp (SchwartzMap.fourierTransformCLM ℂ).continuous
  choose s C hC0 hCb using hq
  choose CG hCG using hder
  set S : Finset (ℕ × ℕ) := I0.biUnion s
  set Nm : ℕ := S.sup (fun j => j.2)
  set R' : ℝ := max R 0
  set Kall : ℝ := ∑ j ∈ S, R' ^ j.1 * |CG j.2|
  set Call : ℝ := ∑ m ∈ I0, (C m : ℝ)
  have hKall0 : 0 ≤ Kall := Finset.sum_nonneg fun _ _ => by positivity
  have hCall0 : 0 ≤ Call := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  refine ⟨2 ^ M * (Call * (Kall * 1)), Nm, fun τ H hH ξ => ?_⟩
  have hτ1 : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  -- seminorms of `H`
  have hsem : ∀ j ∈ S, schwartzSeminormFamily ℂ V ℂ j H ≤ Kall * (1 + |τ|) ^ Nm := by
    intro j hj
    have hj2 : j.2 ≤ Nm := Finset.le_sup (f := fun j : ℕ × ℕ => j.2) hj
    have hle : R' ^ j.1 * |CG j.2| ≤ Kall :=
      Finset.single_le_sum (f := fun j : ℕ × ℕ => R' ^ j.1 * |CG j.2|)
        (fun _ _ => by positivity) hj
    refine SchwartzMap.seminorm_le_bound ℂ j.1 j.2 H (by positivity) fun x => ?_
    by_cases hx : R < ‖x‖
    · have h0 : iteratedFDeriv ℝ j.2 (⇑H) x = 0 := by
        have hns : x ∉ tsupport (⇑H) := by
          intro hx'
          have hsub : tsupport (⇑H) ⊆ Metric.closedBall 0 R := by
            refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
            rw [Metric.mem_closedBall, dist_zero_right]
            by_contra hy'
            exact hy (by rw [hH]; exact hR τ y (lt_of_not_ge hy'))
          have := hsub hx'
          rw [Metric.mem_closedBall, dist_zero_right] at this
          linarith
        exact Function.notMem_support.1 fun h => hns (support_iteratedFDeriv_subset j.2 h)
      rw [h0, norm_zero, mul_zero]; positivity
    · push Not at hx
      have hxR : ‖x‖ ≤ R' := hx.trans (le_max_left _ _)
      have h1 : ‖x‖ ^ j.1 ≤ R' ^ j.1 := pow_le_pow_left₀ (norm_nonneg _) hxR _
      have h2 : ‖iteratedFDeriv ℝ j.2 (⇑H) x‖ ≤ |CG j.2| * (1 + |τ|) ^ Nm := by
        rw [hH]
        refine (hCG j.2 τ x).trans ?_
        gcongr
        exact le_abs_self _
      calc ‖x‖ ^ j.1 * ‖iteratedFDeriv ℝ j.2 (⇑H) x‖
          ≤ R' ^ j.1 * (|CG j.2| * (1 + |τ|) ^ Nm) := by gcongr
        _ = (R' ^ j.1 * |CG j.2|) * (1 + |τ|) ^ Nm := by ring
        _ ≤ Kall * (1 + |τ|) ^ Nm := by gcongr
  have hsup : ∀ m ∈ I0, SchwartzMap.seminorm ℂ m.1 m.2 (𝓕 H) ≤
      (C m : ℝ) * (Kall * (1 + |τ|) ^ Nm) := by
    intro m hm
    have h1 := hCb m H
    simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe,
      SchwartzMap.fourierTransformCLM_apply, Seminorm.smul_apply, NNReal.smul_def,
      smul_eq_mul] at h1
    refine h1.trans ?_
    gcongr
    refine Seminorm.finset_sup_apply_le (by positivity) fun j hj => ?_
    exact hsem j (Finset.mem_biUnion.2 ⟨m, hm, hj⟩)
  have hmain := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0)) (k := M) (n := 0)
    le_rfl le_rfl (𝓕 H) ξ
  rw [norm_iteratedFDeriv_zero, SchwartzMap.fourier_coe] at hmain
  have hfin : ((Finset.Iic (M, 0)).sup fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) (𝓕 H) ≤
      Call * (Kall * (1 + |τ|) ^ Nm) := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun m hm => (hsup m hm).trans ?_
    have hCm : (C m : ℝ) ≤ Call :=
      Finset.single_le_sum (f := fun m => (C m : ℝ)) (fun _ _ => NNReal.coe_nonneg _) hm
    gcongr
  calc (1 + ‖ξ‖) ^ M * ‖𝓕 (⇑H) ξ‖ ≤ 2 ^ M * (Call * (Kall * (1 + |τ|) ^ Nm)) :=
        hmain.trans (mul_le_mul_of_nonneg_left hfin (by positivity))
    _ = 2 ^ M * (Call * (Kall * 1)) * (1 + |τ|) ^ Nm := by ring

end FD
end Aux_MR
end MasulloGRH


/-! ## MR: modulated test functions -/

namespace MasulloGRH
namespace Aux_HL
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform Classical ContDiff

section Smooth
variable {K : Type*} [Field K] [NumberField K]

/-- `Σ_w mult(w) log |x_w|`. -/
noncomputable def hlog (y : mixedSpace K) : ℝ := ∑ w, (mult w : ℝ) * Real.log (normAtPlace w y)

theorem hlog_eq (y : mixedSpace K) (hy : mixedEmbedding.norm y ≠ 0) :
    hlog y = Real.log (mixedEmbedding.norm y) := by
  have hw := mixedEmbedding.norm_ne_zero_iff.1 hy
  rw [mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hw w))]
  unfold hlog
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Real.log_pow]

theorem contDiffAt_log_normAtPlace (w : InfinitePlace K) (y : mixedSpace K)
    (hy : normAtPlace w y ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (normAtPlace w y)) y := by
  by_cases hw : IsReal w
  · have e : (fun y : mixedSpace K => Real.log (normAtPlace w y)) =
        fun y => Real.log ‖y.1 ⟨w, hw⟩‖ := by
      funext y; rw [normAtPlace_apply_of_isReal hw]
    rw [normAtPlace_apply_of_isReal hw] at hy
    rw [e]
    have h1 : ContDiff ℝ ∞ (fun y : mixedSpace K => y.1 ⟨w, hw⟩) :=
      (contDiff_apply ℝ ℝ _).comp contDiff_fst
    have h2 : ContDiffAt ℝ ∞ (fun y : mixedSpace K => ‖y.1 ⟨w, hw⟩‖) y :=
      (contDiffAt_norm ℝ (norm_ne_zero_iff.1 hy)).comp y h1.contDiffAt
    exact (Real.contDiffAt_log.2 hy).comp y h2
  · have hc : IsComplex w := not_isReal_iff_isComplex.1 hw
    have e : (fun y : mixedSpace K => Real.log (normAtPlace w y)) =
        fun y => Real.log ‖y.2 ⟨w, hc⟩‖ := by
      funext y; rw [normAtPlace_apply_of_isComplex hc]
    rw [normAtPlace_apply_of_isComplex hc] at hy
    rw [e]
    have h1 : ContDiff ℝ ∞ (fun y : mixedSpace K => y.2 ⟨w, hc⟩) :=
      (contDiff_apply ℝ ℂ _).comp contDiff_snd
    have h2 : ContDiffAt ℝ ∞ (fun y : mixedSpace K => ‖y.2 ⟨w, hc⟩‖) y :=
      (contDiffAt_norm ℝ (norm_ne_zero_iff.1 hy)).comp y h1.contDiffAt
    exact (Real.contDiffAt_log.2 hy).comp y h2

theorem contDiffAt_hlog (y : mixedSpace K) (hy : mixedEmbedding.norm y ≠ 0) :
    ContDiffAt ℝ ∞ (hlog (K := K)) y := by
  have hw := mixedEmbedding.norm_ne_zero_iff.1 hy
  show ContDiffAt ℝ ∞ (fun y => ∑ w, (mult w : ℝ) * Real.log (normAtPlace w y)) y
  exact ContDiffAt.sum fun w _ => contDiffAt_const.mul (contDiffAt_log_normAtPlace w y (hw w))

/-- the auxiliary bump, `= 1` on the ball of radius `1/2`. -/
noncomputable def bump2 : ContDiffBump (1 : mixedSpace K) where
  rIn := 1 / 2
  rOut := 3 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- a smooth compactly supported function equal to `log N` near `1`. -/
noncomputable def htil (y : mixedSpace K) : ℝ := (bump2 : ContDiffBump (1 : mixedSpace K)) y * hlog y

theorem norm_ne_zero_of_dist (y : mixedSpace K) (h : dist y 1 < 1) :
    mixedEmbedding.norm y ≠ 0 := by
  rw [mixedEmbedding.norm_ne_zero_iff]
  intro w
  have h1 : normAtPlace w (y - 1) ≤ ‖y - 1‖ := by
    rw [norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (fun w => normAtPlace w (y - 1)) (Finset.mem_univ w)
  rw [dist_eq_norm] at h
  have h3 : normAtPlace w (1 : mixedSpace K) ≤ normAtPlace w y + normAtPlace w (-(y - 1)) := by
    have := normAtPlace_add_le w y (-(y - 1))
    rwa [show y + -(y - 1) = 1 by ring] at this
  rw [map_one, normAtPlace_neg] at h3
  intro h0; linarith

theorem contDiff_htil : ContDiff ℝ ∞ (htil (K := K)) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : dist y 1 < 1
  · exact ((bump2 : ContDiffBump (1 : mixedSpace K)).contDiff.contDiffAt).mul
      (contDiffAt_hlog y (norm_ne_zero_of_dist y hy))
  · have hns : y ∉ tsupport ((bump2 : ContDiffBump (1 : mixedSpace K)) : mixedSpace K → ℝ) := by
      rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall]
      intro h'
      have : (bump2 : ContDiffBump (1 : mixedSpace K)).rOut = 3 / 4 := rfl
      rw [this] at h'
      exact hy (by linarith)
    have hev := notMem_tsupport_iff_eventuallyEq.1 hns
    have : htil =ᶠ[𝓝 y] fun _ => (0 : ℝ) := hev.mono fun z hz => by
      simp only [htil]; rw [hz]; simp
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem htil_hasCompactSupport : HasCompactSupport (htil (K := K)) :=
  (bump2 : ContDiffBump (1 : mixedSpace K)).hasCompactSupport.mul_right

theorem htil_eq (y : mixedSpace K) (hy : dist y 1 ≤ 1 / 2) :
    htil y = Real.log (mixedEmbedding.norm y) := by
  have h1 : (bump2 : ContDiffBump (1 : mixedSpace K)) y = 1 :=
    ContDiffBump.one_of_mem_closedBall _ (Metric.mem_closedBall.2 hy)
  unfold htil
  rw [h1, one_mul, hlog_eq y (norm_ne_zero_of_dist y (by linarith))]

end Smooth

namespace CData
variable {K : Type*} [Field K] [NumberField K] (D : CData K)

/-- the modulated test function `f · N^{-iτ}`. -/
noncomputable def gm (τ : ℝ) (z : mixedSpace K) : ℂ := (D.f z : ℂ) * npow z (-(τ * Complex.I))

theorem gm_eq (τ : ℝ) (z : mixedSpace K) :
    D.gm τ z = (D.f z : ℂ) * Complex.exp (-Complex.I * ((τ * htil z : ℝ) : ℂ)) := by
  by_cases hf : D.f z = 0
  · simp [gm, hf]
  have hz := D.f_supp z hf
  have hρ : D.ρ ≤ 1 / 2 := D.exists_rho.choose_spec.2.1
  have hd : dist z 1 ≤ 1 / 2 := (le_of_lt (Metric.mem_ball.1 hz)).trans hρ
  unfold gm npow
  rw [htil_eq z hd]
  congr 2
  push_cast; ring

theorem norm_npow_I (z : mixedSpace K) (τ : ℝ) : ‖npow z (-(τ * Complex.I))‖ = 1 := by
  unfold npow
  rw [Complex.norm_exp]
  simp

theorem norm_gm (τ : ℝ) (z : mixedSpace K) : ‖D.gm τ z‖ = D.f z := by
  unfold gm
  rw [norm_mul, norm_npow_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (D.f_nonneg z)]

/-- the modulated theta function. -/
noncomputable def Θm (τ : ℝ) (y : mixedSpace K) : ℂ :=
  ∑' α : 𝓞 K, D.φ α * D.gm τ (mixedEmbedding K (α : K) * y)

theorem theta_expand_mod (m : ℕ) (hm : 0 < m)
    (per : ∀ α β : 𝓞 K, D.φ (α + (m : 𝓞 K) * β) = D.φ α)
    : ∃ A0 : ℝ, ∃ Af : ℝ → ℂ, (∀ τ, ‖Af τ‖ ≤ A0) ∧ ∀ M : ℕ, Module.finrank ℚ K < M →
      ∃ K0 : ℝ, ∃ N : ℕ, ∀ (τ : ℝ) (y : mixedSpace K), mixedEmbedding.norm y ≠ 0 →
      ‖D.Θm τ y - Af τ * ((mixedEmbedding.norm y)⁻¹ : ℝ)‖ ≤
        K0 * (1 + |τ|) ^ N * (mixedEmbedding.norm y)⁻¹ * ‖y‖ ^ M := by
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  let bO := NumberField.RingOfIntegers.basis K
  let B : EuclideanSpace ℝ ι ≃L[ℝ] mixedSpace K :=
    (EuclideanSpace.equiv ι ℝ).trans (latticeBasis K).equivFun.symm.toContinuousLinearEquiv
  let elt : (ι → ℤ) ≃ 𝓞 K := bO.equivFun.symm.toEquiv
  have hB : ∀ n : ι → ℤ, B (AuxP.zpt n) = mixedEmbedding K ((elt n : 𝓞 K) : K) := by
    intro n
    simp only [B, elt, ContinuousLinearEquiv.trans_apply, LinearEquiv.coe_toContinuousLinearEquiv',
      Module.Basis.equivFun_symm_apply, LinearEquiv.coe_toEquiv]
    have hc : ((∑ i, n i • bO i : 𝓞 K) : K) = ∑ i, n i • ((bO i : 𝓞 K) : K) := by
      simp
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, latticeBasis_apply, integralBasis_apply]
    simp [AuxP.zpt, EuclideanSpace.equiv, bO, Int.cast_smul_eq_zsmul]
  have hcard : Fintype.card ι = Module.finrank ℚ K := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank]
  -- the family of test functions
  let u : EuclideanSpace ℝ ι → ℝ := fun x => D.f (B x)
  let h : EuclideanSpace ℝ ι → ℝ := fun x => htil (B x)
  let G : ℝ → EuclideanSpace ℝ ι → ℂ := fun τ x => D.gm τ (B x)
  have hGeq : ∀ τ, G τ = fun x => (u x : ℂ) * Complex.exp (-Complex.I * ((τ * h x : ℝ) : ℂ)) :=
    fun τ => funext fun x => D.gm_eq τ (B x)
  have hu : ContDiff ℝ ∞ u := (D.bump.contDiff (n := ⊤)).comp B.contDiff
  have hh : ContDiff ℝ ∞ h := contDiff_htil.comp B.contDiff
  have hucs : HasCompactSupport u := D.bump.hasCompactSupport.comp_homeomorph B.toHomeomorph
  have hhcs : HasCompactSupport h := htil_hasCompactSupport.comp_homeomorph B.toHomeomorph
  have hbd : ∀ (g : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∀ i, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C := fun g h1 h2 i =>
    (h1.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (h2.iteratedFDeriv i)
  have hder : ∀ n, ∃ C, ∀ τ x, ‖iteratedFDeriv ℝ n (G τ) x‖ ≤ C * (1 + |τ|) ^ n := by
    intro n
    obtain ⟨C, hC⟩ := Aux_MR.deriv_bound_mod u h hu hh (hbd u hu hucs) (hbd h hh hhcs) n
    exact ⟨C, fun τ x => by rw [hGeq τ]; exact hC τ x⟩
  have hGsm : ∀ τ, ContDiff ℝ ∞ (G τ) := by
    intro τ
    rw [hGeq τ]
    exact (Complex.ofRealCLM.contDiff.comp hu).mul
      (Aux_MR.contDiff_expI.comp (contDiff_const.mul hh))
  have hGcs : ∀ τ, HasCompactSupport (G τ) := by
    intro τ
    rw [hGeq τ]
    exact (hucs.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero).mul_right
  set R : ℝ := ‖(B.symm : mixedSpace K →L[ℝ] EuclideanSpace ℝ ι)‖ * (1 + ‖(1 : mixedSpace K)‖)
  have hR : ∀ τ x, R < ‖x‖ → G τ x = 0 := by
    intro τ x hx
    by_contra hne
    have hf : D.f (B x) ≠ 0 := by
      intro h0; apply hne; show D.gm τ (B x) = 0; simp [gm, h0]
    have hball := D.f_supp _ hf
    have hρ : D.ρ ≤ 1 / 2 := D.exists_rho.choose_spec.2.1
    have h1 : ‖B x‖ ≤ 1 + ‖(1 : mixedSpace K)‖ := by
      have := norm_le_norm_add_norm_sub' (B x) 1
      rw [Metric.mem_ball, dist_eq_norm] at hball
      linarith
    have h2 : ‖x‖ ≤ R := by
      calc ‖x‖ = ‖B.symm (B x)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
        _ ≤ ‖(B.symm : mixedSpace K →L[ℝ] EuclideanSpace ℝ ι)‖ * ‖B x‖ :=
            ContinuousLinearMap.le_opNorm (B.symm : mixedSpace K →L[ℝ] EuclideanSpace ℝ ι) _
        _ ≤ R := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    linarith
  -- the periodic coefficients
  let φt : (ι → ℤ) → ℂ := fun n => D.φ (elt n)
  have hper : ∀ n k, φt (n + (m : ℤ) • k) = φt n := by
    intro n k
    simp only [φt]
    have : elt (n + (m : ℤ) • k) = elt n + (m : 𝓞 K) * elt k := by
      show bO.equivFun.symm (n + (m : ℤ) • k) =
        bO.equivFun.symm n + (m : 𝓞 K) * bO.equivFun.symm k
      rw [map_add, map_zsmul, zsmul_eq_mul, Int.cast_natCast]
    rw [this, per]
  set κB := ‖(B.symm : mixedSpace K →L[ℝ] EuclideanSpace ℝ ι)‖ *
    ‖(B : EuclideanSpace ℝ ι →L[ℝ] mixedSpace K)‖
  set A0 : ℝ := ∫ x, u x
  let H : ℝ → 𝓢(EuclideanSpace ℝ ι, ℂ) := fun τ => (hGcs τ).toSchwartzMap (hGsm τ)
  let Af : ℝ → ℂ := fun τ => (∑ r : ι → Fin m, φt (fun i => ((r i : ℕ) : ℤ))) *
    ((m : ℂ) ^ Fintype.card ι)⁻¹ * ∫ x, H τ x
  refine ⟨A0, Af, fun τ => ?_, fun M hM => ?_⟩
  · -- the size of the constant
    have h1 : ‖∑ r : ι → Fin m, φt (fun i => ((r i : ℕ) : ℤ))‖ ≤ (m : ℝ) ^ Fintype.card ι := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun r _ => D.bd (elt _)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
        Fintype.card_fin]; push_cast; rfl
    have h2 : ‖∫ x, H τ x‖ ≤ A0 := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ‖D.gm τ (B x)‖ = D.f (B x)
      exact D.norm_gm τ (B x)
    have hm' : (0:ℝ) < (m : ℝ) ^ Fintype.card ι := by positivity
    simp only [Af]
    rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    calc ‖∑ r : ι → Fin m, φt (fun i => ((r i : ℕ) : ℤ))‖ * ((m : ℝ) ^ Fintype.card ι)⁻¹ *
          ‖∫ x, H τ x‖ ≤ (m : ℝ) ^ Fintype.card ι * ((m : ℝ) ^ Fintype.card ι)⁻¹ * A0 := by
          gcongr
      _ = A0 := by rw [mul_inv_cancel₀ hm'.ne', one_mul]
  obtain ⟨Kf, Nf, hKf⟩ := Aux_MR.fourier_decay_family G R hR hder M
  set ZM := ∑' k : ι → ℤ, ((1 + ‖AuxP.zpt k‖) ^ (M : ℝ))⁻¹
  have hZM0 : 0 ≤ ZM := tsum_nonneg fun _ => by positivity
  set K0 : ℝ := max Kf 0 * (2 * m) ^ M * ZM * κB ^ M
  refine ⟨K0, Nf, fun τ y hy => ?_⟩
  have hH : ⇑(H τ) = G τ := rfl
  have hCF : ∀ ξ, (1 + ‖ξ‖) ^ M * ‖𝓕 (⇑(H τ)) ξ‖ ≤ max Kf 0 * (1 + |τ|) ^ Nf := fun ξ =>
    (hKf τ (H τ) hH ξ).trans (by gcongr; exact le_max_left _ _)
  have hdetM : LinearMap.det (LinearMap.mulLeft ℝ y) ≠ 0 := by
    intro h0; apply hy; rw [← abs_det_mulLeft y, h0, abs_zero]
  let My : mixedSpace K ≃L[ℝ] mixedSpace K :=
    (LinearMap.equivOfDetNeZero (LinearMap.mulLeft ℝ y) hdetM).toContinuousLinearEquiv
  let Ay : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι := B.trans (My.trans B.symm)
  have hAy : ∀ x, Ay x = B.symm (y * B x) := fun x => rfl
  have hdetA : |LinearMap.det (Ay : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)| =
      mixedEmbedding.norm y := by
    have : (Ay : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) =
        (B.symm.toLinearEquiv : mixedSpace K →ₗ[ℝ] EuclideanSpace ℝ ι) ∘ₗ
          (LinearMap.mulLeft ℝ y) ∘ₗ (B.symm.toLinearEquiv.symm : EuclideanSpace ℝ ι →ₗ[ℝ] mixedSpace K) :=
      LinearMap.ext fun x => rfl
    rw [this, LinearMap.det_conj, abs_det_mulLeft]
  have hnormA : ‖(Ay : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ κB * ‖y‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [show (Ay : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) x = B.symm (y * B x) from rfl]
    calc ‖B.symm (y * B x)‖
        ≤ ‖(B.symm : mixedSpace K →L[ℝ] EuclideanSpace ℝ ι)‖ * ‖y * B x‖ :=
          ContinuousLinearMap.le_opNorm (B.symm : mixedSpace K →L[ℝ] EuclideanSpace ℝ ι) _
      _ ≤ ‖(B.symm : mixedSpace K →L[ℝ] EuclideanSpace ℝ ι)‖ * (‖y‖ * ‖B x‖) := by
          gcongr; exact norm_mul_le _ _
      _ ≤ ‖(B.symm : mixedSpace K →L[ℝ] EuclideanSpace ℝ ι)‖ * (‖y‖ *
            (‖(B : EuclideanSpace ℝ ι →L[ℝ] mixedSpace K)‖ * ‖x‖)) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm (B : EuclideanSpace ℝ ι →L[ℝ] mixedSpace K) x
      _ = κB * ‖y‖ * ‖x‖ := by simp only [κB]; ring
  obtain ⟨-, hbound⟩ := poisson_periodic' (H τ) m hm φt hper (fun n => D.bd _) M
    (by rw [hcard]; exact hM) _ hCF Ay
  have hΘ : D.Θm τ y = ∑' n, φt n * H τ (Ay (AuxP.zpt n)) := by
    unfold Θm
    rw [← elt.tsum_eq]
    refine tsum_congr fun n => ?_
    show D.φ (elt n) * D.gm τ (mixedEmbedding K ((elt n : 𝓞 K) : K) * y) =
      D.φ (elt n) * D.gm τ (B (Ay (AuxP.zpt n)))
    rw [hAy, ContinuousLinearEquiv.apply_symm_apply, hB, mul_comm y]
  rw [hΘ, ← hdetA]
  refine hbound.trans ?_
  rw [hdetA]
  have hNpos : 0 < (mixedEmbedding.norm y)⁻¹ :=
    inv_pos.2 (lt_of_le_of_ne (mixedEmbedding.norm_nonneg y) (Ne.symm hy))
  have hKf0 : 0 ≤ max Kf 0 := le_max_right _ _
  calc max Kf 0 * (1 + |τ|) ^ Nf * (2 * m) ^ M * ZM * (mixedEmbedding.norm y)⁻¹ *
        ‖(Ay : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ^ M
      ≤ max Kf 0 * (1 + |τ|) ^ Nf * (2 * m) ^ M * ZM * (mixedEmbedding.norm y)⁻¹ *
          (κB * ‖y‖) ^ M := by gcongr
    _ = _ := by simp only [K0]; rw [mul_pow]; ring

theorem theta_mod_zero (τ : ℝ) (y : mixedSpace K)
    (hy : 2 ^ Module.finrank ℚ K < mixedEmbedding.norm y) : D.Θm τ y = 0 := by
  unfold Θm
  have : ∀ α : 𝓞 K, D.φ α * D.gm τ (mixedEmbedding K (α : K) * y) = 0 := by
    intro α
    by_cases hf : D.f (mixedEmbedding K (α : K) * y) = 0
    · simp [gm, hf]
    exfalso
    have hb := D.norm_bounds_ball _ (D.f_supp _ hf)
    rw [map_mul] at hb
    by_cases hα : α = 0
    · have h0 : (0:ℝ) < (1/2) ^ Module.finrank ℚ K := by positivity
      rw [hα] at hb
      simp only [ZeroMemClass.coe_zero, map_zero, zero_mul] at hb
      linarith [hb.1]
    · have h1 := one_le_norm_emb α hα
      have : mixedEmbedding.norm y ≤ mixedEmbedding.norm (mixedEmbedding K (α : K)) *
          mixedEmbedding.norm y := le_mul_of_one_le_left (mixedEmbedding.norm_nonneg _) h1
      linarith [hb.2]
  simp [this]

theorem gm_cont (τ : ℝ) : Continuous (D.gm τ) := by
  have : D.gm τ = fun z => (D.f z : ℂ) * Complex.exp (-Complex.I * ((τ * htil z : ℝ) : ℂ)) :=
    funext (D.gm_eq τ)
  rw [this]
  exact (Complex.continuous_ofReal.comp D.f_cont).mul (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul contDiff_htil.continuous))))

theorem theta_mod_meas (τ : ℝ) : AEStronglyMeasurable (D.Θm τ) volume := by
  unfold Θm
  refine AEStronglyMeasurable.tsum (L := SummationFilter.unconditional _) fun α => ?_
  exact (continuous_const.mul ((D.gm_cont τ).comp
    (continuous_const.mul continuous_id))).aestronglyMeasurable

theorem unfold_mod (τ : ℝ) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y => D.Θm τ y * D.c y * npow y (s - 1)) (fundamentalCone K) ∧
      D.Z (s - τ * Complex.I) * D.G s =
        ∫ y in fundamentalCone K, D.Θm τ y * D.c y * npow y (s - 1) := by
  let D' : CData K :=
    { c := D.c
      mul := D.mul
      norm1 := D.norm1
      cont := D.cont
      φ := fun α => D.φ α * npow (mixedEmbedding K (α : K)) (-(τ * Complex.I))
      bd := fun α => by rw [norm_mul, norm_npow_I, mul_one]; exact D.bd α
      unit := fun u α hα => by
        have hN : 0 < mixedEmbedding.norm (mixedEmbedding K (α : K)) :=
          lt_of_lt_of_le one_pos (one_le_norm_emb α hα)
        show D.φ (u * α) * npow (mixedEmbedding K (((u : 𝓞 K) * α : 𝓞 K) : K)) _ =
          D.c _ * (D.φ α * npow _ _)
        rw [D.unit u α hα]
        have : mixedEmbedding K (((u : 𝓞 K) * α : 𝓞 K) : K) = u • mixedEmbedding K (α : K) := by
          rw [unitSMul_smul, ← map_mul]; simp
        rw [this, npow_unit u _ hN]; ring }
  have hs' : 1 < (s - τ * Complex.I).re := by simpa using hs
  obtain ⟨hint, heq⟩ := D'.unfold (s - τ * Complex.I) hs'
  have hZ : D'.Z = D.Z := rfl
  have hG : D'.G (s - τ * Complex.I) = D.G s := by
    unfold G
    refine tsum_congr fun a => ?_
    show D.φ _ * npow (mixedEmbedding K (((fundamentalCone.preimageOfMemIntegerSet a : 𝓞 K)) : K))
        (-(τ * Complex.I)) * (D.c a)⁻¹ * npow (a : mixedSpace K) (-(s - τ * Complex.I)) =
      D.φ _ * (D.c a)⁻¹ * npow (a : mixedSpace K) (-s)
    rw [fundamentalCone.mixedEmbedding_preimageOfMemIntegerSet]
    have : npow (a : mixedSpace K) (-(τ * Complex.I)) *
        npow (a : mixedSpace K) (-(s - τ * Complex.I)) = npow (a : mixedSpace K) (-s) := by
      rw [npow_add]; congr 1; ring
    rw [← this]; ring
  have hpt : ∀ y ∈ fundamentalCone K, D'.Θ y * D'.c y * npow y (s - τ * Complex.I - 1) =
      D.Θm τ y * D.c y * npow y (s - 1) := by
    intro y hy
    have hNy := fundamentalCone.norm_pos_of_mem hy
    have hΘ : D.Θm τ y = npow y (-(τ * Complex.I)) * D'.Θ y := by
      unfold Θm Θ
      rw [← tsum_mul_left]
      refine tsum_congr fun α => ?_
      show D.φ α * D.gm τ (mixedEmbedding K (α : K) * y) = npow y (-(τ * Complex.I)) *
        (D.φ α * npow (mixedEmbedding K (α : K)) (-(τ * Complex.I)) *
          (D.f (mixedEmbedding K (α : K) * y) : ℂ))
      by_cases hα : α = 0
      · simp [hα, gm, D.f_zero]
      have hNa : 0 < mixedEmbedding.norm (mixedEmbedding K (α : K)) :=
        lt_of_lt_of_le one_pos (one_le_norm_emb α hα)
      unfold gm; rw [npow_mul _ _ hNa hNy]; ring
    rw [hΘ]
    show D'.Θ y * D.c y * npow y (s - τ * Complex.I - 1) = _
    have : npow y (s - τ * Complex.I - 1) = npow y (-(τ * Complex.I)) * npow y (s - 1) := by
      rw [npow_add]; congr 1; ring
    rw [this]; ring
  constructor
  · exact hint.congr_fun hpt (measurableSet_fundamentalCone K)
  · rw [← hZ, ← hG, heq]
    exact setIntegral_congr_fun (measurableSet_fundamentalCone K) hpt

theorem Z_lower (a b : ℝ) : ∃ z0 : ℝ, 0 < z0 ∧ ∀ σ : ℝ, a ≤ σ → σ ≤ b → z0 ≤ ‖D.Z σ‖ := by
  set d := Module.finrank ℚ K
  set L : ℝ := Real.exp (-((|a| + |b| + 1) * ((d : ℝ) * Real.log 2)))
  refine ⟨(∫ y, D.bump y) * ((1/2) * L), mul_pos D.bump.integral_pos (by positivity),
    fun σ ha hb => ?_⟩
  have hint0 : Integrable (fun y => (D.f y : ℂ) * D.c y * npow y ((σ : ℂ) - 1)) := D.F0_int σ
  have hre := integral_re hint0
  have hlow : ∀ y, D.f y * ((1/2) * L) ≤
      ((D.f y : ℂ) * D.c y * npow y ((σ : ℂ) - 1)).re := by
    intro y
    by_cases hf : D.f y = 0
    · simp [hf]
    have hy := D.f_supp y hf
    have hN := D.ball_pos y hy
    have hb' := D.norm_bounds_ball y hy
    have hc := D.exists_rho.choose_spec.2.2 y hy
    set lN := Real.log (mixedEmbedding.norm y)
    have hnp : npow y ((σ : ℂ) - 1) = ((Real.exp ((σ - 1) * lN) : ℝ) : ℂ) := by
      unfold npow; rw [Complex.ofReal_exp]; push_cast; ring_nf <;> rfl
    rw [hnp]
    have e : (D.f y : ℂ) * D.c y * ((Real.exp ((σ - 1) * lN) : ℝ) : ℂ) =
        ((D.f y * Real.exp ((σ - 1) * lN) : ℝ) : ℂ) * D.c y := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (D.f_nonneg y)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogb : |lN| ≤ d * Real.log 2 := by
      have h1 : lN ≤ d * Real.log 2 := by
        have := Real.log_le_log hN hb'.2
        rwa [Real.log_pow] at this
      have h2 : -(d * Real.log 2) ≤ lN := by
        have := Real.log_le_log (by positivity) hb'.1
        rw [Real.log_pow, one_div, Real.log_inv] at this
        linarith
      exact abs_le.2 ⟨h2, h1⟩
    have hs1 : |σ - 1| ≤ |a| + |b| + 1 := by
      rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
    have hE : L ≤ Real.exp ((σ - 1) * lN) := by
      refine Real.exp_le_exp.2 ?_
      have h3 : |(σ - 1) * lN| ≤ (|a| + |b| + 1) * (d * Real.log 2) := by
        rw [abs_mul]; exact mul_le_mul hs1 hlogb (abs_nonneg _) (by positivity)
      linarith [neg_abs_le ((σ - 1) * lN)]
    have hcre : (1/2 : ℝ) ≤ (D.c y).re := hc.le
    calc (1/2) * L = L * (1/2) := by ring
      _ ≤ Real.exp ((σ - 1) * lN) * (D.c y).re :=
          mul_le_mul hE hcre (by norm_num) (Real.exp_pos _).le
  have hmono := integral_mono ((D.bump.integrable (μ := volume)).mul_const
    ((1/2) * L)) hint0.re hlow
  rw [integral_mul_const, hre] at hmono
  calc (∫ y, D.bump y) * ((1/2) * L)
      ≤ RCLike.re (∫ y, (D.f y : ℂ) * D.c y * npow y ((σ : ℂ) - 1)) := hmono
    _ = (D.Z σ).re := rfl
    _ ≤ ‖D.Z σ‖ := Complex.re_le_norm _

/-- the shell ratio for a general scale `t`. -/
noncomputable def qt (t : ℝ) (s : ℂ) : ℂ :=
  D.c (t • (1 : mixedSpace K)) * Complex.exp ((s - 1) * ((Module.finrank ℚ K : ℝ) * Real.log t : ℝ))

theorem lower_scale_gen (t : ℝ) (ht : 0 < t) (s : ℂ) :
    ∫ y in fundamentalCone K ∩ {y | mixedEmbedding.norm y ≤ t ^ Module.finrank ℚ K *
        2 ^ Module.finrank ℚ K}, D.c y * npow y (s - 2) =
      D.qt t s * ∫ y in fundamentalCone K ∩ {y | mixedEmbedding.norm y ≤ 2 ^ Module.finrank ℚ K},
        D.c y * npow y (s - 2) := by
  set d := Module.finrank ℚ K
  set Lo : Set (mixedSpace K) := fundamentalCone K ∩ {y | mixedEmbedding.norm y ≤ t ^ d * 2 ^ d}
  set Db : Set (mixedSpace K) := fundamentalCone K ∩ {y | mixedEmbedding.norm y ≤ 2 ^ d}
  have htd : 0 < t ^ d := pow_pos ht d
  have hmem : ∀ z : mixedSpace K, t • z ∈ Lo ↔ z ∈ Db := by
    intro z
    simp only [Lo, Db, Set.mem_inter_iff, Set.mem_setOf_eq,
      fundamentalCone.smul_mem_iff_mem ht.ne', mixedEmbedding.norm_smul, abs_of_pos ht]
    rw [mul_le_mul_iff_right₀ htd]
  have hLo : MeasurableSet Lo := (measurableSet_fundamentalCone K).inter
    (measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const)
  have hDb : MeasurableSet Db := (measurableSet_fundamentalCone K).inter
    (measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const)
  let h : mixedSpace K → ℂ := Lo.indicator (fun y => D.c y * npow y (s - 2))
  have key := Measure.integral_comp_smul (μ := (volume : Measure (mixedSpace K))) h t
  have hrank : Module.finrank ℝ (mixedSpace K) = d := mixedEmbedding.finrank K
  rw [hrank] at key
  have ht1 : mixedEmbedding.norm (t • (1 : mixedSpace K)) ≠ 0 := by
    rw [mixedEmbedding.norm_smul, map_one, mul_one]; positivity
  have hexp : (((t ^ d)⁻¹ : ℝ) : ℂ) = Complex.exp (-(((d : ℝ) * Real.log t : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, ← Real.log_pow,
      Real.exp_log htd]
  have hleft : (fun z => h (t • z)) = Db.indicator (fun z =>
      D.qt t s * (((t ^ d)⁻¹ : ℝ) : ℂ) * (D.c z * npow z (s - 2))) := by
    funext z
    by_cases hz : z ∈ Db
    · rw [Set.indicator_of_mem hz]
      simp only [h, Set.indicator_of_mem ((hmem z).2 hz)]
      have hN : mixedEmbedding.norm z ≠ 0 := hz.1.2
      have hc : D.c (t • z) = D.c (t • (1 : mixedSpace K)) * D.c z := by
        rw [← D.mul _ _ ht1 hN, smul_mul_assoc, one_mul]
      rw [hc, npow_smul t ht.ne' z hN, abs_of_pos ht, hexp]
      unfold qt
      have e1 : Complex.exp ((s - 2) * (((d : ℝ) * Real.log t : ℝ) : ℂ)) =
          Complex.exp ((s - 1) * (((d : ℝ) * Real.log t : ℝ) : ℂ)) *
            Complex.exp (-(((d : ℝ) * Real.log t : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [e1]; ring
    · rw [Set.indicator_of_notMem hz]
      simp only [h, Set.indicator_of_notMem (fun h' => hz ((hmem z).1 h'))]
  rw [hleft, integral_indicator hDb, integral_const_mul] at key
  rw [← integral_indicator hLo]
  rw [abs_of_pos (inv_pos.2 htd), Complex.real_smul] at key
  have hne : (((t ^ d)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 htd).ne'
  apply mul_left_cancel₀ hne
  rw [← key]
  ring

/-- **local representation with polynomial control**. -/
theorem main_rep (m : ℕ) (hm : 0 < m) (per : ∀ α β : 𝓞 K, D.φ (α + (m : 𝓞 K) * β) = D.φ α)
    (a b : ℝ) : ∃ T Cb : ℝ, ∃ N : ℕ, ∀ s0 : ℂ, a ≤ s0.re → s0.re ≤ b → T ≤ |s0.im| →
      ∃ Num : ℂ → ℂ, MeromorphicOn Num Set.univ ∧ AnalyticAt ℂ Num s0 ∧
        ‖Num s0‖ ≤ Cb * (1 + |s0.im|) ^ N ∧
        ∀ s : ℂ, 1 < s.re → D.Z (s - s0.im * Complex.I) * D.G s = Num s := by
  set d := Module.finrank ℚ K with hd
  set T' : ℝ := (2:ℝ) ^ d with hT'
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd1
  have hT1 : 1 ≤ T' := one_le_pow₀ (by norm_num)
  obtain ⟨A0, Af, hAf, hth⟩ := D.theta_expand_mod m hm per
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ, d < M ∧ (d : ℝ) * (2 + |a|) ≤ M := by
    obtain ⟨M, hM⟩ := exists_nat_ge ((d : ℝ) * (2 + |a|))
    exact ⟨M + d + 1, by omega, by push_cast; linarith⟩
  obtain ⟨K0, N, hK0⟩ := hth M hM1
  obtain ⟨κ, hκ, hκb⟩ := cone_bound (K := K)
  set Db : Set (mixedSpace K) := fundamentalCone K ∩ {y | mixedEmbedding.norm y ≤ T'} with hDb_def
  have hmeasN : ∀ t : ℝ, MeasurableSet {y : mixedSpace K | mixedEmbedding.norm y ≤ t} := fun t =>
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const
  have hDbm : MeasurableSet Db := (measurableSet_fundamentalCone K).inter (hmeasN T')
  have hDbfin : volume Db < ⊤ := cone_trunc_finite T'
  have hpos : ∀ y ∈ Db, 0 < mixedEmbedding.norm y := fun y hy =>
    fundamentalCone.norm_pos_of_mem hy.1
  have hcont : ContinuousOn D.c Db := D.cont.mono fun y hy => (hpos y hy).ne'
  set V : ℝ := (volume Db).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  -- continuity of `c` along the scalars at `1`
  have hc1 : ∃ η : ℝ, 0 < η ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ η →
      0 ≤ (D.c (Real.exp (-θ) • (1 : mixedSpace K))).re := by
    have hopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
      isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
    have h1n : mixedEmbedding.norm ((1:ℝ) • (1 : mixedSpace K)) ≠ 0 := by
      rw [one_smul, map_one]; exact one_ne_zero
    have hcont1 : ContinuousAt (fun r : ℝ => D.c (r • (1 : mixedSpace K))) 1 := by
      have h1 : ContinuousAt D.c ((1:ℝ) • (1 : mixedSpace K)) :=
        D.cont.continuousAt (hopen.mem_nhds h1n)
      exact ContinuousAt.comp (g := D.c) h1
        ((continuous_id.smul continuous_const :
          Continuous fun r : ℝ => r • (1 : mixedSpace K)).continuousAt)
    have hU : {z : ℂ | 0 < z.re} ∈ 𝓝 (D.c ((1:ℝ) • (1 : mixedSpace K))) := by
      rw [one_smul, D.c_one]
      exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcont1.preimage_mem_nhds hU)
    refine ⟨ε / 2, half_pos hε, fun θ h0 h1 => ?_⟩
    have hmem : Real.exp (-θ) ∈ Metric.ball (1:ℝ) ε := by
      have h2 : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have h3 := Real.add_one_le_exp (-θ)
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    exact (hball hmem).le
  obtain ⟨η, hη, hcη⟩ := hc1
  set η' : ℝ := min η (Real.log 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hη' : 0 < η' := lt_min hη hl2
  set T : ℝ := Real.pi / (d * η')
  set E : ℝ := (M : ℝ) / d + |b|
  set B1 : ℝ := T' ^ (2 + |a| + |b|)
  set K0' : ℝ := max K0 0
  set Cb : ℝ := A0 * (B1 * V) + K0' * κ ^ M * T' ^ E * V
  refine ⟨T, Cb, N, fun s0 ha0 hb0 hT0 => ?_⟩
  set τ0 := s0.im
  have hτpos : 0 < |τ0| := lt_of_lt_of_le (div_pos Real.pi_pos (mul_pos hdpos hη')) hT0
  set θ : ℝ := Real.pi / (d * |τ0|)
  have hθ0 : 0 < θ := div_pos Real.pi_pos (mul_pos hdpos hτpos)
  have hθη : θ ≤ η' := by
    have h1 : Real.pi ≤ d * η' * |τ0| := by
      have := mul_le_mul_of_nonneg_left hT0 (mul_pos hdpos hη').le
      have e : d * η' * T = Real.pi := by simp only [T]; field_simp
      linarith
    rw [div_le_iff₀ (mul_pos hdpos hτpos)]; linarith
  set t : ℝ := Real.exp (-θ)
  have ht0 : 0 < t := Real.exp_pos _
  have hlogt : Real.log t = -θ := Real.log_exp _
  have ht1 : t < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hthalf : 1 / 2 ≤ t := by
    have : -Real.log 2 ≤ -θ := by linarith [min_le_right η (Real.log 2)]
    calc (1:ℝ) / 2 = Real.exp (-Real.log 2) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      _ ≤ t := Real.exp_le_exp.2 this
  have htd1 : 1 ≤ t ^ d * T' := by
    rw [hT', ← mul_pow]
    exact one_le_pow₀ (by linarith)
  have htd2 : t ^ d ≤ 1 := pow_le_one₀ ht0.le ht1.le
  set A := Af τ0
  have hA0 : ‖A‖ ≤ A0 := hAf τ0
  set Lo : Set (mixedSpace K) := fundamentalCone K ∩ {y | mixedEmbedding.norm y ≤ t ^ d * T'}
  set Sh : Set (mixedSpace K) := fundamentalCone K ∩ ({y | mixedEmbedding.norm y ≤ T'} \
    {y | mixedEmbedding.norm y ≤ t ^ d * T'})
  have hShm : MeasurableSet Sh :=
    (measurableSet_fundamentalCone K).inter ((hmeasN T').diff (hmeasN _))
  have hLom : MeasurableSet Lo := (measurableSet_fundamentalCone K).inter (hmeasN _)
  have hShsub : Sh ⊆ Db := fun y hy => ⟨hy.1, hy.2.1⟩
  have hShfin : volume Sh < ⊤ := lt_of_le_of_lt (measure_mono hShsub) hDbfin
  -- the remainder
  let R : mixedSpace K → ℂ := fun y => D.Θm τ0 y - A * ((mixedEmbedding.norm y)⁻¹ : ℝ)
  have hRm : AEStronglyMeasurable (fun y => R y * D.c y) (volume.restrict Db) := by
    refine AEStronglyMeasurable.mul ?_ (hcont.aestronglyMeasurable hDbm)
    refine ((D.theta_mod_meas τ0).restrict).sub (AEStronglyMeasurable.const_mul ?_ _)
    exact (Complex.measurable_ofReal.comp
      ((mixedEmbedding.continuous_norm K).measurable.inv)).aestronglyMeasurable
  have hRpt : ∀ M' : ℕ, d < M' → ∃ C : ℝ, ∀ y ∈ Db,
      ‖R y‖ ≤ C * (mixedEmbedding.norm y)⁻¹ * ‖y‖ ^ M' := by
    intro M' hM'
    obtain ⟨K1, N1, hK1⟩ := hth M' hM'
    refine ⟨K1 * (1 + |τ0|) ^ N1, fun y hy => ?_⟩
    have hA' : Af τ0 = A := rfl
    have := hK1 τ0 y (hpos y hy).ne'
    rw [hA'] at this
    exact this
  have hRb : ∀ σ : ℝ, ∃ C : ℝ, ∀ y ∈ Db, ‖R y * D.c y‖ * mixedEmbedding.norm y ^ σ ≤ C := by
    intro σ
    obtain ⟨M', hM'1, hM'2⟩ : ∃ M' : ℕ, d < M' ∧ (d : ℝ) * (1 + |σ|) ≤ M' := by
      obtain ⟨M', hM'⟩ := exists_nat_ge ((d : ℝ) * (1 + |σ|))
      exact ⟨M' + d + 1, by omega, by push_cast; linarith⟩
    obtain ⟨C, hC⟩ := hRpt M' hM'1
    set e : ℝ := (M' : ℝ) / d - 1 + σ
    have he : 0 ≤ e := by
      have : (d : ℝ) * (1 + |σ|) / d ≤ M' / d := div_le_div_of_nonneg_right hM'2 hdpos.le
      rw [mul_div_cancel_left₀ _ hdpos.ne'] at this
      have := neg_abs_le σ
      simp only [e]; linarith
    refine ⟨max C 0 * κ ^ M' * T' ^ e, fun y hy => ?_⟩
    have hN := hpos y hy
    have hcy : ‖D.c y‖ = 1 := D.norm1 y hN.ne'
    rw [norm_mul, hcy, mul_one]
    have h1 := hC y hy
    have h2 : ‖y‖ ^ M' ≤ (κ * mixedEmbedding.norm y ^ ((d : ℝ)⁻¹)) ^ M' :=
      pow_le_pow_left₀ (norm_nonneg _) (hκb y hy.1) M'
    have h3 : (κ * mixedEmbedding.norm y ^ ((d : ℝ)⁻¹)) ^ M' * (mixedEmbedding.norm y)⁻¹ *
        mixedEmbedding.norm y ^ σ = κ ^ M' * mixedEmbedding.norm y ^ e := by
      have hpowM : (mixedEmbedding.norm y ^ ((d:ℝ)⁻¹)) ^ M' =
          mixedEmbedding.norm y ^ ((M':ℝ) / d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; field_simp
      have hcomb : (mixedEmbedding.norm y)⁻¹ * mixedEmbedding.norm y ^ σ *
          mixedEmbedding.norm y ^ ((M':ℝ) / d) = mixedEmbedding.norm y ^ e := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hN, ← Real.rpow_add hN]
        congr 1; simp only [e]; ring
      rw [mul_pow, hpowM, ← hcomb]; ring
    have h4 : mixedEmbedding.norm y ^ e ≤ T' ^ e :=
      Real.rpow_le_rpow hN.le hy.2 he
    have hR0 : ‖R y‖ ≤ max C 0 * (mixedEmbedding.norm y)⁻¹ * ‖y‖ ^ M' :=
      h1.trans (by gcongr; exact le_max_left _ _)
    calc ‖R y‖ * mixedEmbedding.norm y ^ σ
        ≤ (max C 0 * (mixedEmbedding.norm y)⁻¹ * ‖y‖ ^ M') * mixedEmbedding.norm y ^ σ := by
          gcongr
      _ ≤ (max C 0 * (mixedEmbedding.norm y)⁻¹ *
            (κ * mixedEmbedding.norm y ^ ((d : ℝ)⁻¹)) ^ M') * mixedEmbedding.norm y ^ σ := by
          gcongr
      _ = max C 0 * (κ ^ M' * mixedEmbedding.norm y ^ e) := by rw [← h3]; ring
      _ ≤ max C 0 * (κ ^ M' * T' ^ e) := by gcongr
      _ = max C 0 * κ ^ M' * T' ^ e := by ring
  obtain ⟨hRint, hRdiff⟩ := entire_of_bound Db hDbm hDbfin _ hRm hpos hRb
  -- the shell integral
  have hShN : ∀ y ∈ Sh, 1 < mixedEmbedding.norm y ∧ mixedEmbedding.norm y ≤ T' := by
    intro y hy
    exact ⟨lt_of_le_of_lt htd1 (lt_of_not_ge hy.2.2), hy.2.1⟩
  have hcb : ∀ σ : ℝ, ∃ C : ℝ, ∀ y ∈ Sh, ‖D.c y‖ * mixedEmbedding.norm y ^ σ ≤ C := by
    intro σ
    refine ⟨max 1 (T' ^ σ), fun y hy => ?_⟩
    have hN : 0 < mixedEmbedding.norm y := hpos y (hShsub hy)
    rw [D.norm1 y hN.ne', one_mul]
    have hy1 := hShN y hy
    rcases le_total 0 σ with hσ | hσ
    · exact (Real.rpow_le_rpow hN.le hy1.2 hσ).trans (le_max_right _ _)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hy1.1.le hσ).trans (le_max_left _ _)
  obtain ⟨hcint, hcdiff⟩ := entire_of_bound Sh hShm hShfin D.c
    ((hcont.mono hShsub).aestronglyMeasurable hShm) (fun y hy => hpos y (hShsub hy)) hcb
  have hqdiff : Differentiable ℂ (D.qt t) := by
    unfold qt; fun_prop
  -- the numerator
  let Num : ℂ → ℂ := fun s => A * (∫ y in Sh, D.c y * npow y (s - 2)) / (1 - D.qt t s) +
    ∫ y in Db, R y * D.c y * npow y (s - 1)
  -- the value of the shell ratio at `s0`
  have hq0 : 1 ≤ (1 - D.qt t s0).re := by
    have hct := hcη θ hθ0.le (hθη.trans (min_le_left _ _))
    set r : ℝ := Real.exp (-(s0.re - 1) * (d * θ))
    have hsplit : (s0 - 1) * (((d : ℝ) * Real.log t : ℝ) : ℂ) =
        ((-(s0.re - 1) * (d * θ) : ℝ) : ℂ) + ((-(τ0 * (d * θ)) : ℝ) : ℂ) * Complex.I := by
      rw [hlogt]
      apply Complex.ext <;> simp [τ0] <;> ring
    have hang : Real.cos (-(τ0 * (d * θ))) = -1 := by
      have : τ0 * (d * θ) = Real.pi * (τ0 / |τ0|) := by
        simp only [θ]; field_simp
      rw [Real.cos_neg, this]
      rcases lt_or_gt_of_ne (show τ0 ≠ 0 from abs_pos.1 hτpos) with hneg | hposτ
      · rw [abs_of_neg hneg, div_neg, div_self hneg.ne, mul_neg, mul_one, Real.cos_neg,
          Real.cos_pi] <;> simp
      · rw [abs_of_pos hposτ, div_self hposτ.ne', mul_one, Real.cos_pi] <;> simp
    have hang2 : Real.sin (-(τ0 * (d * θ))) = 0 := by
      have : τ0 * (d * θ) = Real.pi * (τ0 / |τ0|) := by
        simp only [θ]; field_simp
      rw [Real.sin_neg, this]
      rcases lt_or_gt_of_ne (show τ0 ≠ 0 from abs_pos.1 hτpos) with hneg | hposτ
      · rw [abs_of_neg hneg, div_neg, div_self hneg.ne, mul_neg, mul_one, Real.sin_neg,
          Real.sin_pi] <;> simp
      · rw [abs_of_pos hposτ, div_self hposτ.ne', mul_one, Real.sin_pi] <;> simp
    have hexp : Complex.exp ((s0 - 1) * (((d : ℝ) * Real.log t : ℝ) : ℂ)) = -(r : ℂ) := by
      rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, hang, hang2]
      simp [r]
    unfold qt
    rw [hexp]
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have : (1 - D.c (t • (1 : mixedSpace K)) * -(r : ℂ)).re =
        1 + r * (D.c (t • (1 : mixedSpace K))).re := by
      simp [Complex.mul_re]; ring
    rw [this]
    have := mul_nonneg hr0 hct
    linarith
  have hq0' : 1 - D.qt t s0 ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hq0; linarith
  refine ⟨Num, ?_, ?_, ?_, ?_⟩
  · -- meromorphic
    have h1 : MeromorphicOn (fun s => ∫ y in Sh, D.c y * npow y (s - 2)) Set.univ :=
      fun z _ => ((hcdiff.comp (differentiable_id.sub_const 2)).analyticAt z).meromorphicAt
    have h2 : MeromorphicOn (fun s => 1 - D.qt t s) Set.univ :=
      fun z _ => (((differentiable_const 1).sub hqdiff).analyticAt z).meromorphicAt
    have h3 : MeromorphicOn (fun s => ∫ y in Db, R y * D.c y * npow y (s - 1)) Set.univ :=
      fun z _ => ((hRdiff.comp (differentiable_id.sub_const 1)).analyticAt z).meromorphicAt
    exact ((MeromorphicOn.const A).mul h1 |>.div h2).add h3
  · -- analytic at s0
    have h1 : AnalyticAt ℂ (fun s => A * ∫ y in Sh, D.c y * npow y (s - 2)) s0 :=
      (((hcdiff.comp (differentiable_id.sub_const 2)).const_mul A).analyticAt s0)
    have h2 : AnalyticAt ℂ (fun s => 1 - D.qt t s) s0 :=
      (((differentiable_const 1).sub hqdiff).analyticAt s0)
    have h3 : AnalyticAt ℂ (fun s => ∫ y in Db, R y * D.c y * npow y (s - 1)) s0 :=
      ((hRdiff.comp (differentiable_id.sub_const 1)).analyticAt s0)
    exact (h1.div h2 hq0').add h3
  · -- the bound
    have hτ1 : 1 ≤ (1 + |τ0|) ^ N := one_le_pow₀ (by linarith [abs_nonneg τ0])
    have hP : ‖∫ y in Sh, D.c y * npow y (s0 - 2)‖ ≤ B1 * V := by
      have hb : ∀ y ∈ Sh, ‖D.c y * npow y (s0 - 2)‖ ≤ B1 := by
        intro y hy
        have hN : 0 < mixedEmbedding.norm y := hpos y (hShsub hy)
        have hy1 := hShN y hy
        rw [norm_mul, D.norm1 y hN.ne', one_mul, npow_norm y hN]
        have hre : (s0 - 2).re ≤ 2 + |a| + |b| := by
          simp; linarith [le_abs_self b, abs_nonneg a]
        calc mixedEmbedding.norm y ^ (s0 - 2).re ≤ mixedEmbedding.norm y ^ (2 + |a| + |b|) :=
              Real.rpow_le_rpow_of_exponent_le hy1.1.le hre
          _ ≤ B1 := Real.rpow_le_rpow hN.le hy1.2 (by linarith [abs_nonneg a, abs_nonneg b])
      refine (norm_setIntegral_le_of_norm_le_const hShfin hb).trans ?_
      exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hDbfin.ne (measure_mono hShsub))
        (Real.rpow_nonneg (le_trans zero_le_one hT1) _)
    have hRI : ‖∫ y in Db, R y * D.c y * npow y (s0 - 1)‖ ≤
        K0' * (1 + |τ0|) ^ N * κ ^ M * T' ^ E * V := by
      have hb : ∀ y ∈ Db, ‖R y * D.c y * npow y (s0 - 1)‖ ≤
          K0' * (1 + |τ0|) ^ N * κ ^ M * T' ^ E := by
        intro y hy
        have hN := hpos y hy
        rw [norm_mul, norm_mul, D.norm1 y hN.ne', mul_one, npow_norm y hN]
        have h1 : ‖R y‖ ≤ K0' * (1 + |τ0|) ^ N * (mixedEmbedding.norm y)⁻¹ * ‖y‖ ^ M :=
          (hK0 τ0 y hN.ne').trans (by gcongr; exact le_max_left _ _)
        have h2 : ‖y‖ ^ M ≤ (κ * mixedEmbedding.norm y ^ ((d : ℝ)⁻¹)) ^ M :=
          pow_le_pow_left₀ (norm_nonneg _) (hκb y hy.1) M
        set e : ℝ := (M : ℝ) / d - 2 + s0.re
        have he : 0 ≤ e := by
          have : (d : ℝ) * (2 + |a|) / d ≤ M / d := div_le_div_of_nonneg_right hM2 hdpos.le
          rw [mul_div_cancel_left₀ _ hdpos.ne'] at this
          have := neg_abs_le a
          simp only [e]; linarith
        have heE : e ≤ E := by simp only [e, E]; linarith [le_abs_self b]
        have h3 : (κ * mixedEmbedding.norm y ^ ((d : ℝ)⁻¹)) ^ M * (mixedEmbedding.norm y)⁻¹ *
            mixedEmbedding.norm y ^ (s0 - 1).re = κ ^ M * mixedEmbedding.norm y ^ e := by
          have hpowM : (mixedEmbedding.norm y ^ ((d:ℝ)⁻¹)) ^ M =
              mixedEmbedding.norm y ^ ((M:ℝ) / d) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; field_simp
          have hcomb : (mixedEmbedding.norm y)⁻¹ * mixedEmbedding.norm y ^ (s0 - 1).re *
              mixedEmbedding.norm y ^ ((M:ℝ) / d) = mixedEmbedding.norm y ^ e := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hN, ← Real.rpow_add hN]
            congr 1; simp only [e, Complex.sub_re, Complex.one_re]; ring
          rw [mul_pow, hpowM, ← hcomb]; ring
        have h4 : mixedEmbedding.norm y ^ e ≤ T' ^ E :=
          (Real.rpow_le_rpow hN.le hy.2 he).trans (Real.rpow_le_rpow_of_exponent_le hT1 heE)
        have hK0' : 0 ≤ K0' := le_max_right _ _
        calc ‖R y‖ * mixedEmbedding.norm y ^ (s0 - 1).re
            ≤ (K0' * (1 + |τ0|) ^ N * (mixedEmbedding.norm y)⁻¹ *
                (κ * mixedEmbedding.norm y ^ ((d : ℝ)⁻¹)) ^ M) *
                mixedEmbedding.norm y ^ (s0 - 1).re := by gcongr; exact h1.trans (by gcongr)
          _ = K0' * (1 + |τ0|) ^ N * (κ ^ M * mixedEmbedding.norm y ^ e) := by rw [← h3]; ring
          _ ≤ K0' * (1 + |τ0|) ^ N * (κ ^ M * T' ^ E) := by gcongr
          _ = _ := by ring
      refine (norm_setIntegral_le_of_norm_le_const hDbfin hb).trans (le_of_eq ?_)
      rfl
    have hdiv : ‖A * (∫ y in Sh, D.c y * npow y (s0 - 2)) / (1 - D.qt t s0)‖ ≤
        A0 * (B1 * V) := by
      have h1 : 1 ≤ ‖1 - D.qt t s0‖ := hq0.trans (Complex.re_le_norm _)
      rw [norm_div, norm_mul]
      calc ‖A‖ * ‖∫ y in Sh, D.c y * npow y (s0 - 2)‖ / ‖1 - D.qt t s0‖
          ≤ ‖A‖ * ‖∫ y in Sh, D.c y * npow y (s0 - 2)‖ := div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h1
        _ ≤ A0 * (B1 * V) := mul_le_mul hA0 hP (norm_nonneg _) ((norm_nonneg _).trans hA0)
    show ‖Num s0‖ ≤ Cb * (1 + |τ0|) ^ N
    have hA00 : 0 ≤ A0 := (norm_nonneg _).trans hA0
    calc ‖Num s0‖ ≤ A0 * (B1 * V) + K0' * (1 + |τ0|) ^ N * κ ^ M * T' ^ E * V :=
          (norm_add_le _ _).trans (add_le_add hdiv hRI)
      _ ≤ A0 * (B1 * V) * (1 + |τ0|) ^ N + K0' * (1 + |τ0|) ^ N * κ ^ M * T' ^ E * V :=
          add_le_add (le_mul_of_one_le_right (mul_nonneg hA00 (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one hT1) _) hV0))
            hτ1) le_rfl
      _ = Cb * (1 + |τ0|) ^ N := by simp only [Cb]; ring
  · -- the identity on `Re s > 1`
    intro s hs
    obtain ⟨hint, hunf⟩ := D.unfold_mod τ0 s hs
    rw [hunf]
    have hzero : ∀ y ∈ fundamentalCone K, y ∉ Db →
        D.Θm τ0 y * D.c y * npow y (s - 1) = 0 := by
      intro y hy hy'
      have : T' < mixedEmbedding.norm y := lt_of_not_ge fun h => hy' ⟨hy, h⟩
      rw [D.theta_mod_zero τ0 y this]; ring
    have e1 : ∫ y in fundamentalCone K, D.Θm τ0 y * D.c y * npow y (s - 1) =
        ∫ y in Db, D.Θm τ0 y * D.c y * npow y (s - 1) := by
      rw [← integral_inter_add_diff hDbm hint]
      have hin : fundamentalCone K ∩ Db = Db := Set.inter_eq_right.2 Set.inter_subset_left
      rw [hin]
      have : ∫ y in fundamentalCone K \ Db, D.Θm τ0 y * D.c y * npow y (s - 1) = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun y hy => hzero y hy.1 hy.2
      rw [this, add_zero]
    rw [e1]
    have hsplit : ∀ y ∈ Db, D.Θm τ0 y * D.c y * npow y (s - 1) =
        A * (D.c y * npow y (s - 2)) + R y * D.c y * npow y (s - 1) := by
      intro y hy
      rw [← npow_shift y (hpos y hy) s]
      simp only [R]; ring
    have hint2 : IntegrableOn (fun y => R y * D.c y * npow y (s - 1)) Db := hRint (s - 1)
    have hintA : IntegrableOn (fun y => A * (D.c y * npow y (s - 2))) Db := by
      have h1 : IntegrableOn (fun y => D.Θm τ0 y * D.c y * npow y (s - 1)) Db :=
        hint.mono_set Set.inter_subset_left
      refine (h1.sub hint2).congr_fun (fun y hy => ?_) hDbm
      rw [Pi.sub_apply, hsplit y hy]; ring
    rw [setIntegral_congr_fun hDbm hsplit, integral_add hintA hint2, integral_const_mul]
    change _ = A * (∫ y in Sh, D.c y * npow y (s - 2)) / (1 - D.qt t s) +
      ∫ y in Db, R y * D.c y * npow y (s - 1)
    congr 1
    by_cases hA0' : A = 0
    · rw [hA0', zero_mul, zero_mul, zero_div]
    have hP : IntegrableOn (fun y => D.c y * npow y (s - 2)) Db := by
      have h2 : IntegrableOn (fun y => A⁻¹ * (A * (D.c y * npow y (s - 2)))) Db :=
        hintA.const_mul A⁻¹
      refine h2.congr_fun (fun y _ => ?_) hDbm
      show A⁻¹ * (A * (D.c y * npow y (s - 2))) = _
      rw [← mul_assoc, inv_mul_cancel₀ hA0', one_mul]
    have hqlt : ‖D.qt t s‖ < 1 := by
      have h1n : mixedEmbedding.norm (t • (1 : mixedSpace K)) ≠ 0 := by
        rw [mixedEmbedding.norm_smul, map_one, mul_one]
        exact (pow_pos (abs_pos.2 ht0.ne') _).ne'
      unfold qt
      rw [norm_mul, D.norm1 _ h1n, one_mul, Complex.norm_exp, Real.exp_lt_one_iff, hlogt]
      have : ((s - 1) * (((d : ℝ) * -θ : ℝ) : ℂ)).re = -((s.re - 1) * (d * θ)) := by
        simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.sub_im, Complex.one_im, mul_zero, sub_zero]
        ring
      rw [this]
      have : 0 < (s.re - 1) * (d * θ) := by
        have : 0 < s.re - 1 := by linarith
        exact mul_pos this (mul_pos hdpos hθ0)
      linarith
    have hq1 : 1 - D.qt t s ≠ 0 := by
      intro h
      have h' : D.qt t s = 1 := (sub_eq_zero.mp h).symm
      rw [h', norm_one] at hqlt; exact lt_irrefl _ hqlt
    have hDbsplit : Db = Sh ∪ Lo := by
      ext y
      simp only [Db, Sh, Lo, Set.mem_union, Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h3 : mixedEmbedding.norm y ≤ t ^ d * T'
        · exact Or.inr ⟨h1, h3⟩
        · exact Or.inl ⟨h1, h2, h3⟩
      · rintro (⟨h1, h2, _⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h2⟩
        · have : t ^ d * T' ≤ 1 * T' := mul_le_mul_of_nonneg_right htd2 (le_trans zero_le_one hT1)
          exact ⟨h1, h2.trans (by linarith)⟩
    have hdisj : Disjoint Sh Lo := by
      rw [Set.disjoint_left]
      intro y hy hy'
      exact hy.2.2 hy'.2
    have hPeq : ∫ y in Db, D.c y * npow y (s - 2) =
        (∫ y in Sh, D.c y * npow y (s - 2)) + D.qt t s * ∫ y in Db, D.c y * npow y (s - 2) := by
      have hP' := hP
      rw [hDbsplit] at hP'
      have := setIntegral_union hdisj hLom (hP'.mono_set Set.subset_union_left)
        (hP'.mono_set Set.subset_union_right)
      rw [← hDbsplit] at this
      calc _ = _ := this
        _ = _ := by rw [D.lower_scale_gen t ht0 s]
    rw [mul_div_assoc]
    congr 1
    rw [eq_div_iff hq1]
    linear_combination hPeq

end CData
end Aux_HL
end MasulloGRH


/-! ## MR: Hecke side, polynomial growth -/

namespace MasulloGRH
namespace Aux_HL
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open IsDedekindDomain Filter Topology MeasureTheory
open scoped Classical nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

local notation "A" => AdeleRing (𝓞 F) F

/-- triviality on the level set of the ramified places only. -/
theorem htriv_ram (χ : HeckeCharacter F) (S0 : Set (HeightOneSpectrum (𝓞 F)))
    (ε : HeightOneSpectrum (𝓞 F) → ℝ) (hε : ∀ v, 0 < ε v) (hS0f : S0.Finite)
    (htriv0 : ∀ g ∈ levelSet S0 ε, χ (QuotientGroup.mk g) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S0, ¬ χ.IsUnramifiedAt v → v ∈ S) :
    ∀ g ∈ levelSet (S : Set (HeightOneSpectrum (𝓞 F))) ε, χ (QuotientGroup.mk g) = 1 := by
  intro g hg
  obtain ⟨hg1, hg2, hg3⟩ := hg
  set U : Finset (HeightOneSpectrum (𝓞 F)) := hS0f.toFinset.filter (fun v => v ∉ S)
  have hne : ∀ v, (g : A).2 v ≠ 0 := by
    intro v h0
    have := fin_mul_inv' g v
    rw [h0, zero_mul] at this; exact zero_ne_one this
  let u : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ := fun v => Units.mk0 _ (hne v)
  have hval : ∀ v, Valued.v ((u v : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    intro v
    have h1 := (hg2 v).1
    have h2 := (hg2 v).2
    rw [fin_inv_eq, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
    have hpos : Valued.v ((g : A).2 v) ≠ 0 := (map_ne_zero _).2 (hne v)
    have h3 : 1 ≤ Valued.v ((g : A).2 v) := by
      rw [inv_le_one₀ (zero_lt_iff.2 hpos)] at h2; exact h2
    exact le_antisymm h1 h3
  set P : IdeleGroup F := ∏ v ∈ U, ideleSingle v (u v)
  set g' : IdeleGroup F := g * P⁻¹
  have hPinf : infCoord P = 1 := infCoord_ideleSingle_prod U u
  have hPfin : ∀ w, finCoord w P = if w ∈ U then (g : A).2 w else 1 := fun w => by
    rw [finCoord_ideleSingle_prod U u w]; rfl
  have hPinv : ∀ w, finCoord w P⁻¹ = (finCoord w P)⁻¹ := by
    intro w
    have h := congrArg (finCoord w) (mul_inv_cancel P)
    rw [map_mul, map_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hg'fin : ∀ w, (g' : A).2 w = if w ∈ U then 1 else (g : A).2 w := by
    intro w
    show finCoord w (g * P⁻¹) = _
    rw [map_mul, hPinv, hPfin]
    show (g : A).2 w * _ = _
    split_ifs
    · exact mul_inv_cancel₀ (hne w)
    · rw [inv_one, mul_one]
  have hg'inv : ∀ w, ((g'⁻¹ : IdeleGroup F) : A).2 w = if w ∈ U then 1 else ((g⁻¹ : IdeleGroup F) : A).2 w := by
    intro w
    rw [fin_inv_eq, hg'fin, fin_inv_eq]
    split_ifs <;> simp
  have hg'mem : g' ∈ levelSet S0 ε := by
    refine ⟨?_, fun w => ?_, fun w hw => ?_⟩
    · show infCoord (g * P⁻¹) = 1
      have h := congrArg infCoord (mul_inv_cancel P)
      rw [map_mul, map_one, hPinf, one_mul] at h
      rw [map_mul, h, mul_one]; exact hg1
    · rw [hg'fin, hg'inv]
      split_ifs
      · exact ⟨one_mem _, one_mem _⟩
      · exact hg2 w
    · rw [hg'fin]
      split_ifs with hwU
      · rw [sub_self, norm_zero]; exact hε w
      · have hwS : w ∈ S := by
          simp only [U, Finset.mem_filter, Set.Finite.mem_toFinset, not_and, not_not] at hwU
          exact hwU hw
        exact hg3 w hwS
  have hgP : g = g' * P := by simp [g']
  have hχP : χ (QuotientGroup.mk P) = 1 := by
    simp only [P]
    rw [QuotientGroup.mk_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    have hvS0 : v ∈ S0 := by
      simp only [U, Finset.mem_filter, Set.Finite.mem_toFinset] at hv; exact hv.1
    have hvS : v ∉ S := by
      simp only [U, Finset.mem_filter] at hv; exact hv.2
    have hunr : χ.IsUnramifiedAt v := by
      by_contra h; exact hvS (hS v hvS0 h)
    have := hunr (u v) (hval v)
    unfold HeckeCharacter.localComponent at this
    exact Circle.ext (by simpa using this)
  rw [hgP, QuotientGroup.mk_mul, map_mul, htriv0 g' hg'mem, hχP, one_mul]

/-- the coefficient, with a harmless value at `0`. -/
noncomputable def psiZ (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F))) (m0 : ℕ)
    (α : 𝓞 F) : ℂ :=
  if α = 0 then psi χ S (m0 : 𝓞 F) else psi χ S α

theorem psiZ_per (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ε : HeightOneSpectrum (𝓞 F) → ℝ)
    (hloc : ∀ v (x : (v.adicCompletion F)ˣ), Valued.v (x : v.adicCompletion F) = 1 →
        ‖(x : v.adicCompletion F) - 1‖ < ε v → χ.localComponent v x = 1)
    (m0 : ℕ) (hm0pos : 0 < m0) (hm0 : ∀ v ∈ S, (m0 : 𝓞 F) ∈ v.asIdeal ∧
      ‖algebraMap F (v.adicCompletion F) (m0 : F)‖ < ε v) (α β : 𝓞 F) :
    psiZ χ S m0 (α + (m0 : 𝓞 F) * β) = psiZ χ S m0 α := by
  have key : ∀ γ δ : 𝓞 F, γ ≠ 0 → γ + (m0 : 𝓞 F) * δ ≠ 0 →
      psi χ S (γ + (m0 : 𝓞 F) * δ) = psi χ S γ :=
    fun γ δ h1 h2 => psi_per_nz χ S ε hloc m0 hm0 γ δ h1 h2
  have hm0ne : (m0 : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hm0pos.ne'
  have hmul : ∀ δ : 𝓞 F, (m0 : 𝓞 F) * δ ≠ 0 → psi χ S ((m0 : 𝓞 F) * δ) = psi χ S (m0 : 𝓞 F) := by
    intro δ h
    have e : (m0 : 𝓞 F) + (m0 : 𝓞 F) * (δ - 1) = (m0 : 𝓞 F) * δ := by ring
    have := key (m0 : 𝓞 F) (δ - 1) hm0ne (by rw [e]; exact h)
    rwa [e] at this
  unfold psiZ
  by_cases hα : α = 0
  · subst hα
    rw [zero_add]
    by_cases hb : (m0 : 𝓞 F) * β = 0
    · rw [if_pos hb, if_pos rfl]
    · rw [if_neg hb, if_pos rfl, hmul β hb]
  · by_cases hb : α + (m0 : 𝓞 F) * β = 0
    · rw [if_pos hb, if_neg hα]
      have e : α = (m0 : 𝓞 F) * (-β) := by linear_combination hb
      rw [e, hmul (-β) (by rw [← e]; exact hα)]
    · rw [if_neg hb, if_neg hα, key α β hα hb]

theorem exists_rep' (S : Finset (HeightOneSpectrum (𝓞 F))) (c : ClassGroup (𝓞 F)) :
    ∃ k : HeightOneSpectrum (𝓞 F) →₀ ℕ, cls k = c⁻¹ ∧ ∀ v ∈ S, k v = 0 := by
  by_cases hS : S.Nonempty
  · exact exists_rep S hS c
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c⁻¹
    refine ⟨expoVec (I : Ideal (𝓞 F)) (nonZeroDivisors.coe_ne_zero I), ?_,
      fun v hv => absurd ⟨v, hv⟩ hS⟩
    unfold cls
    have : (⟨idealOf (expoVec (I : Ideal (𝓞 F)) (nonZeroDivisors.coe_ne_zero I)),
        mem_nonZeroDivisors_of_ne_zero (idealOf_ne_zero _)⟩ : (Ideal (𝓞 F))⁰) = I :=
      Subtype.ext (idealOf_expoVec _ _)
    rw [this, hI]

theorem Wk_inv_bound (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (k : HeightOneSpectrum (𝓞 F) →₀ ℕ)
    (hk : ∀ v ∈ S, k v = 0) (a b : ℝ) :
    ∃ W : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖(Wk χ S s k)⁻¹‖ ≤ W := by
  have hnorm : ∀ s : ℂ, ‖Wk χ S s k‖ = ‖Wk χ S (s.re : ℂ) k‖ := by
    intro s
    unfold Wk
    rw [norm_mono', norm_mono']
    refine Finsupp.prod_congr fun v _ => ?_
    congr 1
    by_cases hv : v ∈ S
    · simp [hv]
    · simp only [hv, if_false, zv, norm_mul]
      have hN : 0 < (Ideal.absNorm v.asIdeal : ℕ) := by have := two_le_absNorm v; omega
      rw [Complex.norm_natCast_cpow_of_pos hN, Complex.norm_natCast_cpow_of_pos hN]
      simp
  have hcont : ContinuousOn (fun σ : ℝ => ‖(Wk χ S (σ : ℂ) k)⁻¹‖) (Set.Icc a b) := by
    refine (Continuous.continuousOn ?_)
    have h1 : Continuous fun σ : ℝ => Wk χ S (σ : ℂ) k :=
      (Wk_differentiable χ S k).continuous.comp Complex.continuous_ofReal
    exact (h1.inv₀ fun σ => Wk_ne_zero χ S hun _ k hk).norm
  obtain ⟨W, hW⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨W, fun s ha hb => ?_⟩
  have := hW s.re ⟨ha, hb⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
  rw [norm_inv, hnorm s, ← norm_inv]
  exact this

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

theorem heckeL_spec' (χ : HeckeCharacter F)
    (hex : ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct χ s) :
    MeromorphicNFOn (heckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → heckeLFunction χ s = heckeEulerProduct χ s := by
  unfold heckeLFunction
  rw [dif_pos hex]
  exact hex.choose_spec

theorem heckeL_eq' (χ : HeckeCharacter F) (L : ℂ → ℂ) (hL : MeromorphicNFOn L Set.univ)
    (hLe : ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct χ s) : heckeLFunction χ = L := by
  have h := heckeL_spec' χ ⟨L, hL, hLe⟩
  exact eq_of_mnf h.1 hL fun s hs => (h.2 s hs).trans (hLe s hs).symm

/-- **local representations with polynomial control**. -/
theorem rep_main (χ : HeckeCharacter F) (a b : ℝ) :
    ∃ C T : ℝ, ∃ N : ℕ, ∀ s0 : ℂ, a ≤ s0.re → s0.re ≤ b → T ≤ |s0.im| →
      ∃ Φ : ℂ → ℂ, MeromorphicOn Φ Set.univ ∧
        (∀ s : ℂ, 1 < s.re → Φ =ᶠ[𝓝[≠] s] heckeEulerProduct χ) ∧ AnalyticAt ℂ Φ s0 ∧
        ‖Φ s0‖ ≤ C * (1 + |s0.im|) ^ N := by
  obtain ⟨S0, ε, hS0f, hε, htriv0, hun0, hloc⟩ := exists_conductor χ
  set S : Finset (HeightOneSpectrum (𝓞 F)) :=
    hS0f.toFinset.filter (fun v => ¬ χ.IsUnramifiedAt v) with hSdef
  have hun : ∀ v, v ∉ S → χ.IsUnramifiedAt v := by
    intro v hv
    by_contra h
    apply hv
    have hv0 : v ∈ S0 := by by_contra h'; exact h (hun0 v h')
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hv0, h⟩
  have htriv : ∀ g ∈ levelSet (S : Set (HeightOneSpectrum (𝓞 F))) ε,
      χ (QuotientGroup.mk g) = 1 :=
    htriv_ram χ S0 ε hε hS0f htriv0 S fun v hv h => by
      simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hv, h⟩
  have hzS : ∀ (z : ℂ), ∀ v ∈ S, zv χ z v = 0 := by
    intro z v hv
    have hr : ¬ χ.IsUnramifiedAt v := by
      simp only [S, Finset.mem_filter] at hv; exact hv.2
    unfold zv HeckeCharacter.primeValue
    rw [dif_neg (fun h => hr h.1), zero_mul]
  obtain ⟨m0, hm0pos, hm0⟩ := exists_m0 S ε hε
  choose kc hkc using exists_rep' (F := F) S
  -- the analytic data of each class
  have hD : ∀ c : ClassGroup (𝓞 F), ∃ D : CData F, ∃ m : ℕ, 0 < m ∧
      (∀ α β : 𝓞 F, D.φ (α + (m : 𝓞 F) * β) = D.φ α) ∧
      ∀ s, D.G s = GJ χ S (idealOf (kc c)) s := by
    intro c
    set J := idealOf (kc c)
    have hNJ : 0 < Ideal.absNorm J := Nat.pos_of_ne_zero (fun h =>
      idealOf_ne_zero (kc c) (Ideal.absNorm_eq_zero_iff.1 h))
    let D : CData F :=
      { c := cE χ
        mul := cE_mul χ
        norm1 := cE_norm χ
        cont := cE_cont χ
        φ := fun α => if α ∈ J then psiZ χ S m0 α else 0
        bd := fun α => by
          by_cases hα : α ∈ J
          · rw [if_pos hα]; unfold psiZ; split_ifs <;> exact psi_bd χ S _
          · rw [if_neg hα, norm_zero]; exact zero_le_one
        unit := fun u α hα0 => by
          have huα : (u : 𝓞 F) * α ≠ 0 := mul_ne_zero (Units.ne_zero u) hα0
          by_cases hα : α ∈ J
          · rw [if_pos ((Ideal.unit_mul_mem_iff_mem _ u.isUnit).2 hα), if_pos hα]
            unfold psiZ
            rw [if_neg huα, if_neg hα0]
            exact psi_unit χ S ε hε htriv hun u α
          · rw [if_neg (fun h => hα ((Ideal.unit_mul_mem_iff_mem _ u.isUnit).1 h)), if_neg hα,
              mul_zero] }
    refine ⟨D, m0 * Ideal.absNorm J, Nat.mul_pos hm0pos hNJ, fun α β => ?_, fun s => ?_⟩
    · show (if α + ((m0 * Ideal.absNorm J : ℕ) : 𝓞 F) * β ∈ J then psiZ χ S m0 _ else 0) =
        (if α ∈ J then psiZ χ S m0 α else 0)
      have hmem : ((m0 * Ideal.absNorm J : ℕ) : 𝓞 F) * β ∈ J := by
        push_cast
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem J))
      have hiff : α + ((m0 * Ideal.absNorm J : ℕ) : 𝓞 F) * β ∈ J ↔ α ∈ J :=
        Ideal.add_mem_iff_left _ hmem
      have e1 : α + ((m0 * Ideal.absNorm J : ℕ) : 𝓞 F) * β =
          α + (m0 : 𝓞 F) * ((Ideal.absNorm J : 𝓞 F) * β) := by push_cast; ring
      by_cases hα : α ∈ J
      · rw [if_pos (hiff.2 hα), if_pos hα, e1, psiZ_per χ S ε hloc m0 hm0pos hm0]
      · rw [if_neg (fun h => hα (hiff.1 h)), if_neg hα]
    · unfold CData.G GJ
      refine tsum_congr fun a => ?_
      have ha0 : (fundamentalCone.preimageOfMemIntegerSet a : 𝓞 F) ≠ 0 :=
        nonZeroDivisors.coe_ne_zero _
      show (if _ ∈ J then psiZ χ S m0 _ else 0) * _ * _ = _
      unfold psiZ
      rw [if_neg ha0]
  choose D m hm hper hDG using hD
  choose Tc Cc Nc hc using fun c => (D c).main_rep (m c) (hm c) (hper c) a b
  choose z0 hz0 hz0b using fun c => (D c).Z_lower a b
  choose W hWb using fun c => Wk_inv_bound χ S hun (kc c) (hkc c).2 a b
  set T : ℝ := ∑ c, |Tc c|
  set N : ℕ := ∑ c, Nc c
  set Tt : ℂ := ((Nat.card (torsion F) : ℂ))⁻¹
  set C : ℝ := ∑ c, |W c| * ‖Tt‖ * (|Cc c| / z0 c)
  refine ⟨C, T, N, fun s0 ha0 hb0 hT0 => ?_⟩
  have hTc : ∀ c, Tc c ≤ |s0.im| := fun c =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun c => |Tc c|)
      (fun c _ => abs_nonneg (Tc c)) (Finset.mem_univ c)).trans hT0)
  choose Num hNm hNa hNb hNid using fun c => hc c s0 ha0 hb0 (hTc c)
  set τ0 := s0.im
  let Φ : ℂ → ℂ := fun s => ∑ c, (Wk χ S s (kc c))⁻¹ *
    (Tt * (Num c s / (D c).Z (s - τ0 * Complex.I)))
  have hZd : ∀ c, Differentiable ℂ (fun s => (D c).Z (s - τ0 * Complex.I)) := fun c =>
    (D c).Z_differentiable.comp (differentiable_id.sub_const _)
  have hWm : ∀ c, MeromorphicOn (fun s => Wk χ S s (kc c)) Set.univ := fun c z _ =>
    ((Wk_differentiable χ S (kc c)).analyticAt z).meromorphicAt
  have hΦm : MeromorphicOn Φ Set.univ := by
    refine MeromorphicOn.fun_sum fun c => ?_
    have hZm : MeromorphicOn (fun s => (D c).Z (s - τ0 * Complex.I)) Set.univ := fun z _ =>
      ((hZd c).analyticAt z).meromorphicAt
    exact (hWm c).inv.mul ((MeromorphicOn.const Tt).mul ((hNm c).div hZm))
  have hZev : ∀ c (s : ℂ), ∀ᶠ z in 𝓝[≠] s, (D c).Z (z - τ0 * Complex.I) ≠ 0 := by
    intro c s
    have hZan : AnalyticOnNhd ℂ (fun z => (D c).Z (z - τ0 * Complex.I)) Set.univ :=
      fun z _ => (hZd c).analyticAt z
    rcases (hZan s (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hZan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ s) h (Set.mem_univ (τ0 * Complex.I))
      simp only [sub_self, Pi.zero_apply] at this
      exact (D c).Z_zero_ne this
    · exact h
  have hEq : ∀ s : ℂ, 1 < s.re → Φ =ᶠ[𝓝[≠] s] heckeEulerProduct χ := by
    intro s hs
    have hev : ∀ᶠ z in 𝓝[≠] s, ∀ c, (D c).Z (z - τ0 * Complex.I) ≠ 0 :=
      Filter.eventually_all.2 fun c => hZev c s
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hev, nhdsWithin_le_nhds (hopen.mem_nhds hs)] with z hz hz1
    show Φ z = heckeEulerProduct χ z
    rw [euler_split χ S z hz1]
    have hE : ∏ v ∈ S, (1 - zv χ z v)⁻¹ = 1 :=
      Finset.prod_eq_one fun v hv => by rw [hzS z v hv, sub_zero, inv_one]
    rw [hE, one_mul]
    change _ = ∑' k, Wk χ S z k
    rw [decomp χ S ε hε htriv hun z hz1 kc hkc]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hDG c z, ← hNid c z hz1, mul_div_cancel_left₀ _ (hz c)]
  -- `Φ` is analytic at `s0`
  have hs0Z : s0 - τ0 * Complex.I = ((s0.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [τ0]
  have hZ0 : ∀ c, z0 c ≤ ‖(D c).Z (s0 - τ0 * Complex.I)‖ := fun c => by
    rw [hs0Z]; exact hz0b c s0.re ha0 hb0
  have hZne : ∀ c, (D c).Z (s0 - τ0 * Complex.I) ≠ 0 := fun c h => by
    have := hZ0 c; rw [h, norm_zero] at this; linarith [hz0 c]
  have hΦa : AnalyticAt ℂ Φ s0 := by
    have : ∀ c ∈ Finset.univ, AnalyticAt ℂ (fun s => (Wk χ S s (kc c))⁻¹ *
        (Tt * (Num c s / (D c).Z (s - τ0 * Complex.I)))) s0 := by
      intro c _
      have hW : AnalyticAt ℂ (fun s => Wk χ S s (kc c)) s0 :=
        (Wk_differentiable χ S (kc c)).analyticAt s0
      exact (hW.inv (Wk_ne_zero χ S hun s0 (kc c) (hkc c).2)).mul
        (analyticAt_const.mul ((hNa c).div ((hZd c).analyticAt s0) (hZne c)))
    have h := Finset.analyticAt_fun_sum Finset.univ this
    exact h
  refine ⟨Φ, hΦm, hEq, hΦa, ?_⟩
  have hτ1 : (1:ℝ) ≤ 1 + |τ0| := by linarith [abs_nonneg τ0]
  calc ‖Φ s0‖ ≤ ∑ c, ‖(Wk χ S s0 (kc c))⁻¹ *
        (Tt * (Num c s0 / (D c).Z (s0 - τ0 * Complex.I)))‖ := norm_sum_le _ _
    _ ≤ ∑ c, |W c| * ‖Tt‖ * (|Cc c| / z0 c) * (1 + |τ0|) ^ N := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul, norm_mul, norm_div]
        have h1 : ‖(Wk χ S s0 (kc c))⁻¹‖ ≤ |W c| := (hWb c s0 ha0 hb0).trans (le_abs_self _)
        have h2 : ‖Num c s0‖ ≤ |Cc c| * (1 + |τ0|) ^ N :=
          (hNb c).trans (mul_le_mul (le_abs_self _)
            (pow_le_pow_right₀ hτ1 (Finset.single_le_sum (f := fun c => Nc c)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)))
            (by positivity) (abs_nonneg _))
        have h3 : ‖Num c s0‖ / ‖(D c).Z (s0 - τ0 * Complex.I)‖ ≤
            |Cc c| * (1 + |τ0|) ^ N / z0 c :=
          div_le_div₀ (by positivity) h2 (hz0 c) (hZ0 c)
        calc ‖(Wk χ S s0 (kc c))⁻¹‖ * (‖Tt‖ * (‖Num c s0‖ / ‖(D c).Z (s0 - τ0 * Complex.I)‖))
            ≤ |W c| * (‖Tt‖ * (|Cc c| * (1 + |τ0|) ^ N / z0 c)) := by gcongr
          _ = _ := by ring
    _ = C * (1 + |τ0|) ^ N := by rw [← Finset.sum_mul]

theorem nf_of_rep (χ : HeckeCharacter F) (Φ : ℂ → ℂ) (hΦm : MeromorphicOn Φ Set.univ)
    (hEq : ∀ s : ℂ, 1 < s.re → Φ =ᶠ[𝓝[≠] s] heckeEulerProduct χ) :
    MeromorphicNFOn (toMeromorphicNFOn Φ Set.univ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → toMeromorphicNFOn Φ Set.univ s = heckeEulerProduct χ s := by
  have hL'nf := meromorphicNFOn_toMeromorphicNFOn Φ Set.univ
  refine ⟨hL'nf, fun s hs => ?_⟩
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLa : AnalyticAt ℂ (heckeEulerProduct χ) s :=
    (differentiableOn_euler χ).analyticAt (hopen.mem_nhds hs)
  have h1 : toMeromorphicNFOn Φ Set.univ =ᶠ[𝓝[≠] s] heckeEulerProduct χ :=
    (hΦm.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ s)).trans (hEq s hs)
  have h2 := (hL'nf (Set.mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    hLa.meromorphicNFAt
  exact (h2.1 h1).eq_of_nhds

/-- the meromorphic continuation (replaces the keystone's `reduction`). -/
theorem reduction (χ : HeckeCharacter F) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct χ s := by
  obtain ⟨C, T, N, h⟩ := rep_main χ 0 0
  obtain ⟨Φ, hm, hE, -, -⟩ := h (((|T| : ℝ) : ℂ) * Complex.I) (by simp) (by simp)
    (by simp [le_abs_self])
  exact ⟨_, nf_of_rep χ Φ hm hE⟩

/-- **polynomial growth in vertical strips**. -/
theorem growth_main (χ : HeckeCharacter F) (a b : ℝ) :
    ∃ C T : ℝ, ∃ N : ℕ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
      ‖heckeLFunction χ s‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨C, T, N, h⟩ := rep_main χ a b
  refine ⟨C, T, N, fun s0 ha hb hT => ?_⟩
  obtain ⟨Φ, hm, hE, hΦa, hb'⟩ := h s0 ha hb hT
  obtain ⟨hnf, heq⟩ := nf_of_rep χ Φ hm hE
  have hL : heckeLFunction χ = toMeromorphicNFOn Φ Set.univ := heckeL_eq' χ _ hnf heq
  have hval : heckeLFunction χ s0 = Φ s0 := by
    rw [hL]
    have h1 : toMeromorphicNFOn Φ Set.univ =ᶠ[𝓝[≠] s0] Φ :=
      hm.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ s0)
    have h2 := (hnf (Set.mem_univ s0)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      hΦa.meromorphicNFAt
    exact (h2.1 h1).eq_of_nhds
  rw [hval]; exact hb'

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

/-- Cauchy bound for the derivative near the line `Re s ∈ [1, 2]`. -/
theorem deriv_growth (hex : ∀ ψ : HeckeCharacter F, ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct ψ s)
    (hgr : Growth F) (ψ : HeckeCharacter F) :
    ∃ m : ℕ, ∃ C T : ℝ, 0 ≤ C ∧ 1 ≤ T ∧ ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| →
      AnalyticAt ℂ (heckeLFunction ψ) z ∧ ‖deriv (heckeLFunction ψ) z‖ ≤ C * |z.im| ^ m := by
  obtain ⟨m, C, T, hC, hT, h⟩ := growth_nat hgr ψ 0 3 (by norm_num)
  obtain ⟨Ta, hTa⟩ := analytic_of_growth hex hgr ψ 0 3 (by norm_num)
  refine ⟨m, 2 * C * 2 ^ m, max (max T Ta) 1 + 1, by positivity,
    le_trans (le_max_right _ _) (by linarith), fun z h1 h2 h3 => ?_⟩
  have hz1 : 1 ≤ |z.im| := by
    have := le_max_right (max T Ta) 1; linarith
  -- points within distance `1/2` of `z`
  have hnear : ∀ w : ℂ, dist w z ≤ 1 / 2 → 0 < w.re ∧ w.re < 3 ∧
      max T Ta ≤ |w.im| ∧ |w.im| ≤ 2 * |z.im| := by
    intro w hw
    have hre : |w.re - z.re| ≤ 1 / 2 := by
      have := Complex.abs_re_le_norm (w - z)
      rw [← dist_eq_norm] at this
      simpa using this.trans hw
    have him : |w.im - z.im| ≤ 1 / 2 := by
      have := Complex.abs_im_le_norm (w - z)
      rw [← dist_eq_norm] at this
      simpa using this.trans hw
    have hmT := le_max_left (max T Ta) 1
    have a1 := abs_sub_abs_le_abs_sub w.im z.im
    have a2 := abs_sub_abs_le_abs_sub z.im w.im
    rw [abs_sub_comm] at a2
    rw [abs_le] at hre
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have han : ∀ w ∈ closedBall z (1 / 2), AnalyticAt ℂ (heckeLFunction ψ) w := by
    intro w hw
    obtain ⟨a1, a2, a3, _⟩ := hnear w (mem_closedBall.1 hw)
    exact hTa w a1 a2 ((le_max_right _ _).trans a3)
  refine ⟨han z (mem_closedBall_self (by norm_num)), ?_⟩
  have hd : DiffContOnCl ℂ (heckeLFunction ψ) (ball z (1 / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z (by norm_num)]
    exact fun w hw => (han w hw).differentiableAt.differentiableWithinAt
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 2) hd
    (C := C * (2 * |z.im|) ^ m) (fun w hw => by
      obtain ⟨a1, a2, a3, a4⟩ := hnear w (le_of_eq (mem_sphere.1 hw))
      calc ‖heckeLFunction ψ w‖ ≤ C * |w.im| ^ m :=
            h w a1.le a2.le ((le_max_left _ _).trans a3)
        _ ≤ C * (2 * |z.im|) ^ m := by gcongr)
  calc ‖deriv (heckeLFunction ψ) z‖ ≤ C * (2 * |z.im|) ^ m / (1 / 2) := hb
    _ = 2 * C * 2 ^ m * |z.im| ^ m := by rw [mul_pow]; ring

/-- mean value inequality along a horizontal segment. -/
theorem horiz_mvt {f : ℂ → ℂ} {t D : ℝ} {σ : ℝ} (hσ : 1 ≤ σ)
    (hf : ∀ u : ℝ, 1 ≤ u → u ≤ σ → DifferentiableAt ℂ f (u + t * I))
    (hD : ∀ u : ℝ, 1 ≤ u → u ≤ σ → ‖deriv f (u + t * I)‖ ≤ D) :
    ‖f (σ + t * I) - f (1 + t * I)‖ ≤ D * (σ - 1) := by
  let g : ℝ → ℂ := fun u => f (u + t * I)
  have hg : ∀ u ∈ Set.Icc 1 σ, HasDerivWithinAt g (deriv f (u + t * I)) (Set.Icc 1 σ) u := by
    intro u hu
    have h1 : HasDerivAt (fun w : ℂ => f (w + t * I)) (deriv f (u + t * I)) (u : ℂ) :=
      (hf u hu.1 hu.2).hasDerivAt.comp_add_const (u : ℂ) (t * I)
    exact h1.comp_ofReal.hasDerivWithinAt
  have := norm_image_sub_le_of_norm_deriv_le_segment' hg
    (fun u hu => hD u hu.1 hu.2.le) σ ⟨hσ, le_rfl⟩
  simpa [g] using this

lemma final_bound {δ P D A B X : ℝ} (hX : 1 ≤ X) (hδ : 0 < δ) (hPD : (P + 1) * D ^ 4 ≤ A * B * X) :
    2 / δ + 32 * (P + 1) * D ^ 4 ≤ (2 / δ + 32 * A * B) * X := by
  have h1 : 0 ≤ 2 / δ := by positivity
  have h2 : 2 / δ ≤ 2 / δ * X := le_mul_of_one_le_right h1 hX
  have h3 : (2 / δ + 32 * A * B) * X = 2 / δ * X + 32 * (A * B * X) := by ring
  rw [h3]
  linarith

set_option maxHeartbeats 1000000 in
/-- **B.6.1.6 from growth on vertical strips.** -/
theorem inv_poly_growth (hex : ∀ ψ : HeckeCharacter F, ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct ψ s)
    (hgr : Growth F) (χ : HeckeCharacter F) :
    ∃ N : ℕ, 0 < N ∧ ∃ C T : ℝ, ∀ t : ℝ, T ≤ |t| →
      heckeLFunction χ (1 + t * Complex.I) ≠ 0 ∧
      ‖(heckeLFunction χ (1 + t * Complex.I))⁻¹‖ ≤ C * |t| ^ N := by
  -- zeta bound near 1
  obtain ⟨C₀, hC₀⟩ := zeta_bound (F := F)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hC₀)
  set δ := min δ₀ 1 with hδ
  have hδpos : 0 < δ := lt_min hδ₀ one_pos
  have hzb : ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) ≤ max C₀ 0 / (σ - 1) := by
    intro σ h1 h2
    have hd : dist σ 1 < δ₀ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [min_le_left δ₀ 1]
    exact (hδ₀' hd h1).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith))
  -- growth of L(χ²) on [1, 2]
  obtain ⟨m₂, C₂, T₂, hC₂, hT₂, h₂⟩ := growth_nat hgr (χ * χ) 1 2 (by norm_num)
  -- derivative growth of L(χ)
  obtain ⟨md, Cd, Td, hCd, hTd, hd⟩ := deriv_growth hex hgr χ
  have hs1 := (heckeL_spec (1 : HeckeCharacter F) (hex 1)).2
  have hsχ := (heckeL_spec χ (hex χ)).2
  have hsχ2 := (heckeL_spec (χ * χ) (hex (χ * χ))).2
  set C₀' := max C₀ 0
  set K : ℝ := 2 / δ + 32 * (C₀' ^ 3 * C₂ * 2 ^ m₂ + 1) * (Cd + 1) ^ 4 with hK
  refine ⟨m₂ + 4 * md + 1, by omega, K, max (max T₂ Td) 1, fun t ht => ?_⟩
  have ht1 : 1 ≤ |t| := (le_max_right _ _).trans ht
  have htd : Td ≤ |t| := ((le_max_right _ _).trans (le_max_left _ _)).trans ht
  have ht2 : T₂ ≤ |2 * t| := by
    rw [abs_mul, abs_two]
    have := ((le_max_left _ _).trans (le_max_left _ _)).trans ht
    linarith
  set P : ℝ := C₀' ^ 3 * (C₂ * |2 * t| ^ m₂) with hP
  set D : ℝ := Cd * |t| ^ md + 1 with hD
  have hP0 : 0 ≤ P := by positivity
  have hD1 : 1 ≤ D := by have : 0 ≤ Cd * |t| ^ md := by positivity
                         linarith
  set ε : ℝ := min (δ / 2) (1 / (32 * (P + 1) * D ^ 4)) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε1 : ε ≤ 1 := by
    have : δ ≤ 1 := min_le_right _ _
    linarith [min_le_left (δ / 2) (1 / (32 * (P + 1) * D ^ 4))]
  set σ : ℝ := 1 + ε with hσ
  have hσ1 : 1 < σ := by linarith
  have hre : ∀ u : ℝ, 1 < ((σ : ℂ) + u * I).re := fun u => by simpa using hσ1
  -- the 3-4-1 inequality
  have h341 := three_four_one χ σ hσ1 t
  rw [← hs1 σ (by simpa using hσ1), ← hsχ _ (hre t), ← hsχ2 _ (hre _)] at h341
  set x := ‖heckeLFunction χ (σ + t * I)‖
  set y := ‖heckeLFunction χ (1 + t * I)‖
  have hzeta : ‖heckeLFunction (1 : HeckeCharacter F) σ‖ ≤ C₀' / ε := by
    rw [hs1 σ (by simpa using hσ1)]
    have := norm_euler_le (1 : HeckeCharacter F) σ hσ1 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    refine this.trans ((hzb σ hσ1 (by linarith)).trans (le_of_eq ?_))
    simp [σ]
  have hL2 : ‖heckeLFunction (χ * χ) (σ + (2 * t : ℝ) * I)‖ ≤ C₂ * |2 * t| ^ m₂ := by
    have := h₂ ((σ : ℂ) + (2 * t : ℝ) * I) (by simp; linarith) (by simp; linarith)
      (by simpa using ht2)
    simpa using this
  have hA : ε ^ 3 ≤ P * x ^ 4 := by
    have h3 : ‖heckeLFunction (1 : HeckeCharacter F) σ‖ ^ 3 ≤ (C₀' / ε) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hzeta 3
    have : 1 ≤ (C₀' / ε) ^ 3 * x ^ 4 * (C₂ * |2 * t| ^ m₂) := by
      refine h341.trans ?_
      gcongr
    rw [div_pow] at this
    have hε3 : 0 < ε ^ 3 := by positivity
    have : ε ^ 3 ≤ C₀' ^ 3 * x ^ 4 * (C₂ * |2 * t| ^ m₂) := by
      have h := mul_le_mul_of_nonneg_left this hε3.le
      rw [mul_one] at h
      refine h.trans (le_of_eq ?_)
      field_simp
    rw [hP]; linarith [this]
  -- mean value inequality
  have hmv : x ≤ y + D * ε := by
    have := horiz_mvt (f := heckeLFunction χ) (t := t) (D := D) hσ1.le
      (fun u hu1 hu2 => (hd (u + t * I) (by simpa using hu1) (by simp; linarith)
        (by simpa using htd)).1.differentiableAt)
      (fun u hu1 hu2 => by
        have := (hd (u + t * I) (by simpa using hu1) (by simp; linarith) (by simpa using htd)).2
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
          add_zero, zero_add] at this
        linarith)
    have h2 : σ - 1 = ε := by simp [σ]
    rw [h2] at this
    have := norm_sub_norm_le (heckeLFunction χ (σ + t * I)) (heckeLFunction χ (1 + t * I))
    linarith
  -- lower bound
  have hy : D * ε ≤ y := by
    by_contra hlt
    push Not at hlt
    have hx0 : 0 ≤ x := norm_nonneg _
    have hx : x ≤ 2 * (D * ε) := by linarith
    have hx4 : x ^ 4 ≤ (2 * (D * ε)) ^ 4 := pow_le_pow_left₀ hx0 hx 4
    have h1 : ε ^ 3 ≤ (P + 1) * (16 * D ^ 4 * ε ^ 4) := by
      calc ε ^ 3 ≤ P * x ^ 4 := hA
        _ ≤ (P + 1) * x ^ 4 := by gcongr; linarith
        _ ≤ (P + 1) * (2 * (D * ε)) ^ 4 := by gcongr
        _ = (P + 1) * (16 * D ^ 4 * ε ^ 4) := by ring
    have h2 : 1 ≤ 16 * (P + 1) * D ^ 4 * ε := by
      have hε3 : 0 < ε ^ 3 := by positivity
      have : ε ^ 3 * 1 ≤ ε ^ 3 * (16 * (P + 1) * D ^ 4 * ε) := by
        refine (mul_one _).le.trans (h1.trans (le_of_eq ?_)); ring
      exact le_of_mul_le_mul_left this hε3
    have h3 : ε ≤ 1 / (32 * (P + 1) * D ^ 4) := min_le_right _ _
    have h4 : 16 * (P + 1) * D ^ 4 * ε ≤ 1 / 2 := by
      have hpos : 0 < 32 * (P + 1) * D ^ 4 := by positivity
      calc 16 * (P + 1) * D ^ 4 * ε ≤ 16 * (P + 1) * D ^ 4 * (1 / (32 * (P + 1) * D ^ 4)) := by
            gcongr
        _ = 1 / 2 := by field_simp; ring
    linarith
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
  refine ⟨fun h0 => by simp [y, h0] at hypos, ?_⟩
  rw [norm_inv]
  -- 1/y ≤ 1/ε ≤ K |t|^N
  have hinv : y⁻¹ ≤ ε⁻¹ := by
    rw [inv_le_inv₀ hypos hεpos]
    have : ε ≤ D * ε := le_mul_of_one_le_left hεpos.le hD1
    linarith
  have hεinv : ε⁻¹ ≤ 2 / δ + 32 * (P + 1) * D ^ 4 := by
    rcases min_choice (δ / 2) (1 / (32 * (P + 1) * D ^ 4)) with h | h
    · rw [hε, h]
      have : 0 ≤ 32 * (P + 1) * D ^ 4 := by positivity
      rw [inv_div]; linarith
    · rw [hε, h, one_div, inv_inv]
      have : 0 ≤ 2 / δ := by positivity
      linarith
  have hPb : P + 1 ≤ (C₀' ^ 3 * C₂ * 2 ^ m₂ + 1) * |t| ^ m₂ := by
    have : 1 ≤ |t| ^ m₂ := one_le_pow₀ ht1
    rw [hP, abs_mul, abs_two, mul_pow]
    have e : C₀' ^ 3 * (C₂ * (2 ^ m₂ * |t| ^ m₂)) + 1 + (|t| ^ m₂ - 1) =
        (C₀' ^ 3 * C₂ * 2 ^ m₂ + 1) * |t| ^ m₂ := by ring
    linarith
  have hDb : D ≤ (Cd + 1) * |t| ^ md := by
    have : 1 ≤ |t| ^ md := one_le_pow₀ ht1
    rw [hD]
    have e : Cd * |t| ^ md + 1 + (|t| ^ md - 1) = (Cd + 1) * |t| ^ md := by ring
    linarith
  have hD4 : D ^ 4 ≤ (Cd + 1) ^ 4 * |t| ^ (4 * md) := by
    calc D ^ 4 ≤ ((Cd + 1) * |t| ^ md) ^ 4 := pow_le_pow_left₀ (by linarith) hDb 4
      _ = (Cd + 1) ^ 4 * |t| ^ (4 * md) := by rw [mul_pow, ← pow_mul, mul_comm md 4]
  have htN : ∀ k : ℕ, k ≤ m₂ + 4 * md + 1 → |t| ^ k ≤ |t| ^ (m₂ + 4 * md + 1) :=
    fun k hk => pow_le_pow_right₀ ht1 hk
  have hfin : 2 / δ + 32 * (P + 1) * D ^ 4 ≤ K * |t| ^ (m₂ + 4 * md + 1) := by
    have e2 : (P + 1) * D ^ 4 ≤ (C₀' ^ 3 * C₂ * 2 ^ m₂ + 1) * (Cd + 1) ^ 4 *
        |t| ^ (m₂ + 4 * md + 1) := by
      calc (P + 1) * D ^ 4 ≤ ((C₀' ^ 3 * C₂ * 2 ^ m₂ + 1) * |t| ^ m₂) *
            ((Cd + 1) ^ 4 * |t| ^ (4 * md)) :=
            mul_le_mul hPb hD4 (by positivity) (by positivity)
        _ = (C₀' ^ 3 * C₂ * 2 ^ m₂ + 1) * (Cd + 1) ^ 4 * (|t| ^ m₂ * |t| ^ (4 * md)) := by
            ring
        _ = (C₀' ^ 3 * C₂ * 2 ^ m₂ + 1) * (Cd + 1) ^ 4 * |t| ^ (m₂ + 4 * md) := by
            rw [pow_add]
        _ ≤ _ := mul_le_mul_of_nonneg_left (htN _ (by omega)) (by positivity)
    exact final_bound (one_le_pow₀ ht1) hδpos e2
  linarith

end Aux_MQ
end MasulloGRH


namespace MasulloGRH
namespace Aux_MQ
theorem growth_all {F : Type*} [Field F] [NumberField F] : Growth F := by
  intro χ a b _
  obtain ⟨C, T, N, h⟩ := MasulloGRH.Aux_HL.growth_main χ a b
  refine ⟨(N : ℝ) + 1, by positivity, |C| * 2 ^ N, max T 1, fun s ha hb hT => ?_⟩
  have hT1 : 1 ≤ |s.im| := (le_max_right _ _).trans hT
  have h1 := h s ha hb ((le_max_left _ _).trans hT)
  have h2 : (1 + |s.im|) ^ N ≤ 2 ^ N * |s.im| ^ ((N : ℝ) + 1) := by
    have e1 : (1 + |s.im|) ^ N ≤ (2 * |s.im|) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    have e2 : |s.im| ^ N ≤ |s.im| ^ ((N : ℝ) + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    calc (1 + |s.im|) ^ N ≤ (2 * |s.im|) ^ N := e1
      _ = 2 ^ N * |s.im| ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * |s.im| ^ ((N : ℝ) + 1) := by gcongr
  calc ‖heckeLFunction χ s‖ ≤ C * (1 + |s.im|) ^ N := h1
    _ ≤ |C| * (1 + |s.im|) ^ N := by gcongr; exact le_abs_self _
    _ ≤ |C| * (2 ^ N * |s.im| ^ ((N : ℝ) + 1)) := by gcongr
    _ = |C| * 2 ^ N * |s.im| ^ ((N : ℝ) + 1) := by ring

end Aux_MQ
end MasulloGRH


theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F) :
    ∃ N : ℕ, 0 < N ∧ ∃ C T : ℝ, ∀ t : ℝ, T ≤ |t| →
      MasulloGRH.heckeLFunction χ (1 + t * Complex.I) ≠ 0 ∧
      ‖(MasulloGRH.heckeLFunction χ (1 + t * Complex.I))⁻¹‖ ≤ C * |t| ^ N :=
  MasulloGRH.Aux_MQ.inv_poly_growth (fun ψ => MasulloGRH.Aux_HL.reduction ψ)
    MasulloGRH.Aux_MQ.growth_all χ

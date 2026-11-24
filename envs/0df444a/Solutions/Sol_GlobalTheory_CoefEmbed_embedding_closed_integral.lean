-- Prove2me | solution 1 for GlobalTheory.CoefEmbed.embedding_closed_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:51.621625+00:00
-- url     : https://prove2.me/submissions/3eaa25c0-8908-4152-a270-ca0eec7d328a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EmbeddingClosedIntegral
import Theorems.Thm_GlobalTheory_CoefEmbed_norm_le_one
import Theorems.Thm_GlobalTheory_CoefEmbed_norm_prime_lt_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.CoefEmbed
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
open IsLocalRing Topology in
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
private lemma norm_le_one_of_monic_root_lemma {R F : Type*} [CommRing R] [NormedField F]
    [IsUltrametricDist F] (f : R →+* F) (hf : ∀ r, ‖f r‖ ≤ 1) {P : Polynomial R}
    (hP : P.Monic) {y : F} (hy : P.eval₂ f y = 0) : ‖y‖ ≤ 1 := by
  by_contra h
  push_neg at h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, map_one,
    one_mul] at hy
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := by
    refine ⟨P.natDegree - 1, ?_⟩
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · rw [h0] at hy
      simp at hy
    · omega
  rw [hk] at hy
  have hsum : ‖∑ i ∈ Finset.range (k + 1), f (P.coeff i) * y ^ i‖ ≤ ‖y‖ ^ k := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    calc ‖f (P.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ k :=
          mul_le_mul (hf _) (pow_le_pow_right₀ h.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
            (by positivity) zero_le_one
      _ = ‖y‖ ^ k := one_mul _
  have heq : y ^ (k + 1) = -∑ i ∈ Finset.range (k + 1), f (P.coeff i) * y ^ i := by
    linear_combination hy
  have h1 : ‖y‖ ^ (k + 1) ≤ ‖y‖ ^ k := by
    rw [← norm_pow, heq, norm_neg]
    exact hsum
  have h2 : ‖y‖ ^ k < ‖y‖ ^ (k + 1) := pow_lt_pow_right₀ h (Nat.lt_succ_self k)
  linarith
end GlobalTheory.CoefEmbed
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.CoefEmbed
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
namespace GlobalTheory.CoefEmbed
namespace _root_.GlobalTheory.CoefEmbed
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ κ : FractionRing O →+* PadicAlgCl l, (∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → Topology.IsEmbedding (fun x : O => κ (algebraMap O (FractionRing O) x)) ∧ IsClosed (Set.range κ) ∧ (∀ x : FractionRing O, ‖κ x‖ ≤ 1 → ∃ y : O, algebraMap O (FractionRing O) y = x) ∧ ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
  intro l _ O _ _ _ _ _ _ _ hO κ hκ
  set g : O →+* PadicAlgCl l := κ.comp (algebraMap O (FractionRing O)) with hg
  have hgz : ∀ z : ℤ_[l], g (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]) :=
    hκ
  have hgnat : g ((l : ℕ) : O) = ((l : ℕ) : PadicAlgCl l) := map_natCast g l
  have hl_lt : ‖g ((l : ℕ) : O)‖ < 1 := hgnat ▸ _root_.GlobalTheory.CoefEmbed.norm_prime_lt_one (l := l)
  have hl_pos : 0 < ‖g ((l : ℕ) : O)‖ := by
    have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [hgnat, h, norm_algebraMap', Padic.norm_p]
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  have hint : ∀ x : O, ‖g x‖ ≤ 1 := by
    intro x
    obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x
    refine norm_le_one_of_monic_root_lemma (g.comp (algebraMap ℤ_[l] O)) (fun z => ?_) hPm ?_
    · rw [RingHom.comp_apply, hgz, norm_algebraMap']
      exact PadicInt.norm_le_one z
    · rw [← Polynomial.hom_eval₂, hP, map_zero]
  have hunit : ∀ u : Oˣ, ‖g u‖ = 1 := by
    intro u
    have h1 := hint u
    have h2 := hint ↑u⁻¹
    have h3 : ‖g u‖ * ‖g ↑u⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (g u))
    linarith
  have hmax : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have := hunit u
    rw [hu] at this
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hl_pos
    exact lt_irrefl _ hl_pos
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have he : e ≠ 0 := by
    rintro rfl
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmax) (by rw [hw, pow_zero, mul_one]; exact w.isUnit)
  have hϖlt : ‖g ϖ‖ < 1 := by
    have h : ‖g ((l : ℕ) : O)‖ = ‖g ϖ‖ ^ e := by
      rw [hw, map_mul, norm_mul, hunit, one_mul, map_pow, norm_pow]
    by_contra h'
    push_neg at h'
    have := one_le_pow₀ (n := e) h'
    linarith
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hginj : Function.Injective g :=
    κ.injective.comp (IsFractionRing.injective O (FractionRing O))
  have hϖpos : 0 < ‖g ϖ‖ := norm_pos_iff.mpr ((map_ne_zero_iff g hginj).mpr hϖ0)
  have hm : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O → ‖g y‖ ≤ ‖g ϖ‖ := by
    intro y hy
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [map_mul, norm_mul]
    calc ‖g ϖ‖ * ‖g c‖ ≤ ‖g ϖ‖ * 1 := mul_le_mul_of_nonneg_left (hint c) (norm_nonneg _)
      _ = ‖g ϖ‖ := mul_one _
  have hintc : ∀ x : FractionRing O, ‖κ x‖ ≤ 1 → ∃ y : O, algebraMap O (FractionRing O) y = x := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, by rw [hx0, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger O x with h | h
    · exact h
    · obtain ⟨y, hy⟩ := h
      by_cases hyu : IsUnit y
      · obtain ⟨u, rfl⟩ := hyu
        refine ⟨↑u⁻¹, ?_⟩
        have h1 : algebraMap O (FractionRing O) ↑u⁻¹ * algebraMap O (FractionRing O) ↑u = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [hy] at h1
        exact (mul_inv_eq_one₀ hx0).mp h1
      · exfalso
        have hym : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hyu
        have h1 : ‖κ x⁻¹‖ ≤ ‖g ϖ‖ := by
          rw [← hy]
          exact hm y hym
        have h2 : ‖κ x‖ * ‖κ x⁻¹‖ = 1 := by
          rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
        have h3 := mul_le_mul_of_nonneg_right hx (norm_nonneg (κ x⁻¹))
        linarith
  have hdiv : ∀ b : O, b ≠ 0 → ∃ (n : ℕ) (c : O), b * c = ((l : ℕ) : O) ^ n := by
    intro b hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    refine ⟨n, ↑u⁻¹ * ↑w ^ n * ϖ ^ (e' * n), ?_⟩
    rw [hw]
    have := u.mul_inv
    linear_combination (↑w ^ n * ϖ ^ (n + e' * n)) * this
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  set V : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (g '' (s : Set O)) with hV
  have hgV : ∀ x : O, g x ∈ V := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact V.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact V.add_mem hy hz
    | smul z y _ hy =>
      rw [Algebra.smul_def, map_mul, hgz, ← Algebra.smul_def]
      exact V.smul_mem _ hy
  have hrange : Set.range κ = (V : Set (PadicAlgCl l)) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective O x
      obtain ⟨n, c, hc⟩ := hdiv b (nonZeroDivisors.ne_zero hb)
      have hb' : g b ≠ 0 := (map_ne_zero_iff g hginj).mpr (nonZeroDivisors.ne_zero hb)
      have hln : g (((l : ℕ) : O) ^ n) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (norm_pos_iff.mp hl_pos)
      have hc' : g c ≠ 0 := by
        intro h
        apply hln
        rw [← hc, map_mul, h, mul_zero]
      have key : κ (algebraMap O (FractionRing O) a / algebraMap O (FractionRing O) b) =
          ((l : ℚ_[l]) ^ n)⁻¹ • g (a * c) := by
        rw [map_div₀, Algebra.smul_def, map_inv₀, map_pow, map_natCast]
        change g a / g b = _
        rw [← map_natCast g, ← map_pow, ← hc, map_mul, map_mul]
        field_simp
      rw [SetLike.mem_coe, key]
      exact V.smul_mem _ (hgV _)
    · intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, _, rfl⟩ := hy
        exact ⟨_, rfl⟩
      | zero => exact ⟨0, map_zero κ⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, rfl⟩ := hy
        obtain ⟨b, rfl⟩ := hz
        exact ⟨a + b, map_add κ a b⟩
      | smul q y _ hy =>
        obtain ⟨x, rfl⟩ := hy
        obtain ⟨z1, z2, -, rfl⟩ := IsFractionRing.div_surjective ℤ_[l] q
        refine ⟨algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z1) /
          algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z2) * x, ?_⟩
        rw [map_mul, map_div₀, hκ, hκ, Algebra.smul_def, map_div₀]
        rfl
  have hclosed : IsClosed (Set.range κ) := by
    rw [hrange]
    haveI : FiniteDimensional ℚ_[l] V :=
      FiniteDimensional.span_of_finite ℚ_[l] ((s.finite_toSet).image g)
    exact V.closed_of_finiteDimensional
  obtain ⟨hopen, hsmall⟩ := isAdic_iff.mp hO
  have hemb : Topology.IsEmbedding g := by
    refine ⟨(IsTopologicalAddGroup.isInducing_iff_nhds_zero).mpr ?_, hginj⟩
    apply le_antisymm
    · rw [(Metric.nhds_basis_ball.comap g).ge_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖlt
      refine Filter.mem_of_superset ((hopen n).mem_nhds (IsLocalRing.maximalIdeal O ^ n).zero_mem) ?_
      intro x hx
      simp only [Set.mem_preimage, mem_ball_zero_iff]
      rw [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_mul, norm_mul, map_pow, norm_pow]
      calc ‖g ϖ‖ ^ n * ‖g c‖ ≤ ‖g ϖ‖ ^ n * 1 :=
            mul_le_mul_of_nonneg_left (hint c) (by positivity)
        _ < ε := by rw [mul_one]; exact hn
    · intro t ht
      obtain ⟨n, hn⟩ := hsmall t ht
      rw [(Metric.nhds_basis_ball.comap g).mem_iff]
      refine ⟨‖g ϖ‖ ^ n, by positivity, ?_⟩
      intro x hx
      simp only [Set.mem_preimage, mem_ball_zero_iff] at hx
      apply hn
      rw [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have hϖn : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr (pow_ne_zero _ hϖ0)
      have hgϖn : 0 < ‖g (ϖ ^ n)‖ :=
        norm_pos_iff.mpr ((map_ne_zero_iff g hginj).mpr (pow_ne_zero _ hϖ0))
      obtain ⟨y, hy⟩ := hintc (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) (ϖ ^ n))
        (by
          rw [map_div₀, norm_div]
          change ‖g x‖ / ‖g (ϖ ^ n)‖ ≤ 1
          rw [div_le_one hgϖn, map_pow, norm_pow]
          exact hx.le)
      refine ⟨y, ?_⟩
      apply IsFractionRing.injective O (FractionRing O)
      rw [map_mul, hy]
      field_simp
  exact ⟨hemb, hclosed, hintc, hmax⟩
end _root_.GlobalTheory.CoefEmbed
end GlobalTheory.CoefEmbed

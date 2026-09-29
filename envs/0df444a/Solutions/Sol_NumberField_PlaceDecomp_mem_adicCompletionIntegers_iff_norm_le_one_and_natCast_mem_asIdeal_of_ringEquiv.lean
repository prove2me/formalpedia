-- Prove2me | solution 1 for NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/24e3ea51-325a-553d-af71-db48b5148857

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
set_option autoImplicit false
p2m_open "NumberField P2MW.S_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv.NumberField IsDedekindDomain"

namespace NumberField
p2m_export "NumberField" "place RingOfIntegers RingOfIntegers.coe_eq_algebraMap"
namespace PlaceDecomp
namespace BridgeVal
p2m_open "NumberField.PlaceDecomp NumberField"

theorem padicInt_exists_pow_eq (q : ℕ) [Fact q.Prime] {m : ℕ} (hm : q.Coprime m)
    {a : ℤ_[q]} (ha : ‖a - 1‖ < 1) : ∃ z : ℤ_[q], z ^ m = a := by
  set P : Polynomial ℤ_[q] := Polynomial.X ^ m - Polynomial.C a with hP
  have hder : Polynomial.derivative P = Polynomial.C (m : ℤ_[q]) * Polynomial.X ^ (m - 1) := by
    rw [hP, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero]
  have heval : P.aeval (1 : ℤ_[q]) = -(a - 1) := by
    rw [hP, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, one_pow]
    simp
  have hevald : (Polynomial.derivative P).aeval (1 : ℤ_[q]) = (m : ℤ_[q]) := by
    rw [hder, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, one_pow, mul_one]
    simp
  have hnorm : ‖P.aeval (1 : ℤ_[q])‖ < ‖(Polynomial.derivative P).aeval (1 : ℤ_[q])‖ ^ 2 := by
    rw [heval, hevald, norm_neg, PadicInt.norm_natCast_eq_one_iff.mpr hm, one_pow]
    exact ha
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  rw [hP, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hz
  simpa using hz

theorem padicInt_norm_pow_sub_one_lt (q : ℕ) [Fact q.Prime] {u : ℤ_[q]} (hu : ‖u‖ = 1) :
    ‖u ^ (q - 1) - 1‖ < 1 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_one, sub_eq_zero]
  have hu' : IsUnit (PadicInt.toZMod u) := by
    apply IsUnit.map
    exact PadicInt.isUnit_iff.mpr hu
  have hne : PadicInt.toZMod u ≠ 0 := hu'.ne_zero
  have h := ZMod.pow_card_sub_one_eq_one hne
  exact h

section Valued

variable {K : Type*} [Field K] [hv : Valued K (WithZero (Multiplicative ℤ))]

local notation "v" => (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))

theorem valued_eq_one_of_forall_exists_pow_eq (q : ℕ) (hq : 0 < q) {x : K} (hx : x ≠ 0)
    (h : ∀ k : ℕ, ∃ y : K, y ^ (q * k + 1) = x) : v x = 1 := by
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, v x = WithZero.exp n := ⟨WithZero.log (v x), (WithZero.exp_log hvx).symm⟩

  obtain ⟨y, hy⟩ := h n.natAbs
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hy; exact hx hy.symm
  have hvy : v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, v y = WithZero.exp b := ⟨WithZero.log (v y), (WithZero.exp_log hvy).symm⟩
  have h1 : v x = v y ^ (q * n.natAbs + 1) := by rw [← map_pow, hy]
  rw [hn, hb, ← WithZero.exp_nsmul, WithZero.exp_inj] at h1

  rw [hn, ← WithZero.exp_zero, WithZero.exp_inj]
  rw [nsmul_eq_mul] at h1
  push_cast at h1
  rcases eq_or_ne b 0 with hb0 | hb0
  · rw [hb0, mul_zero] at h1; exact h1
  · exfalso
    have h3 : |n| = ((q : ℤ) * |n| + 1) * |b| := by
      conv_lhs => rw [h1]
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (q : ℤ) * |n| + 1)]
    have hb1 : 1 ≤ |b| := Int.one_le_abs hb0
    have h4 : ((q : ℤ) * |n| + 1) * 1 ≤ ((q : ℤ) * |n| + 1) * |b| :=
      mul_le_mul_of_nonneg_left hb1 (by positivity)
    have h5 : (|n| : ℤ) ≤ (q : ℤ) * |n| := le_mul_of_one_le_left (abs_nonneg n) (by exact_mod_cast hq)
    linarith

theorem valued_eq_one_of_pow {y : K} {n : ℕ} (hn : n ≠ 0) (h : v (y ^ n) = 1) : v y = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (v y) 1 with hy | hy | hy
  · exact absurd h (pow_lt_one₀ zero_le' hy hn).ne
  · exact hy
  · exact absurd h (one_lt_pow₀ hy hn).ne'

theorem valued_pow_sub_pow_le {y a : K} (hy : v y ≤ 1) (ha : v a ≤ 1) (n : ℕ) :
    v (y ^ n - a ^ n) ≤ v (y - a) := by
  rw [← geom_sum₂_mul, map_mul]
  refine mul_le_of_le_one_left' ?_
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, map_pow, map_pow]
  exact mul_le_one' (pow_le_one' hy _) (pow_le_one' ha _)

theorem valued_le_one_of_eval₂_eq_zero {R : Type*} [CommRing R] (θ : R →+* K) (G : Polynomial R) (hG : G.Monic)
    (hθ : ∀ i, v (θ (G.coeff i)) ≤ 1) (y : K) (hy : Polynomial.eval₂ θ y G = 0) : v y ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hy0 : v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one h)
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hy

  have htop : v (θ (G.coeff G.natDegree) * y ^ G.natDegree) = v y ^ G.natDegree := by
    rw [Polynomial.Monic.coeff_natDegree hG, map_one, one_mul, map_pow]
  have hlow : v ((Finset.range G.natDegree).sum fun i => θ (G.coeff i) * y ^ i) < v y ^ G.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc v (θ (G.coeff i)) * v y ^ i ≤ 1 * v y ^ i := mul_le_mul' (hθ i) le_rfl
      _ = v y ^ i := one_mul _
      _ < v y ^ G.natDegree := pow_lt_pow_right₀ h hi
  have hsum := Valuation.map_add_eq_of_lt_left v (x := θ (G.coeff G.natDegree) * y ^ G.natDegree)
    (y := (Finset.range G.natDegree).sum fun i => θ (G.coeff i) * y ^ i) (by rw [htop]; exact hlow)
  rw [add_comm, hy, map_zero, htop] at hsum
  exact pow_ne_zero _ hy0 hsum.symm

end Valued

section Completion

variable (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

local notation "K_w" => HeightOneSpectrum.adicCompletion F w
local notation "v" => (Valued.v : Valuation (HeightOneSpectrum.adicCompletion F w) (WithZero (Multiplicative ℤ)))
local notation "ι" => algebraMap F (HeightOneSpectrum.adicCompletion F w)

theorem valued_algebraMap (x : F) : v (ι x) = w.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem valued_algebraMap_coe_le_one (r : 𝓞 F) : v (ι (r : F)) ≤ 1 := by
  rw [valued_algebraMap]
  exact HeightOneSpectrum.valuation_le_one w r

theorem valued_algebraMap_coe_lt_one_iff (r : 𝓞 F) : v (ι (r : F)) < 1 ↔ r ∈ w.asIdeal := by
  rw [valued_algebraMap]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem w r

theorem valued_algebraMap_coe_eq_one_iff (r : 𝓞 F) : v (ι (r : F)) = 1 ↔ r ∉ w.asIdeal := by
  rw [← valued_algebraMap_coe_lt_one_iff F w r]
  constructor
  · intro h; rw [h]; exact lt_irrefl 1
  · intro h; exact le_antisymm (valued_algebraMap_coe_le_one F w r) (not_lt.mp h)

theorem natCast_eq_algebraMap (n : ℕ) : ((n : ℕ) : K_w) = ι ((n : 𝓞 F) : F) := by
  rw [show ((n : 𝓞 F) : F) = (n : F) from map_natCast (algebraMap (𝓞 F) F) n, map_natCast]

theorem valued_natCast_lt_one_iff (n : ℕ) : v ((n : ℕ) : K_w) < 1 ↔ (n : 𝓞 F) ∈ w.asIdeal := by
  rw [natCast_eq_algebraMap, valued_algebraMap_coe_lt_one_iff]

theorem valued_natCast_le_one (n : ℕ) : v ((n : ℕ) : K_w) ≤ 1 := by
  rw [natCast_eq_algebraMap]; exact valued_algebraMap_coe_le_one F w _

theorem pow_card_sub_one_sub_one_mem (e : 𝓞 F) (he : e ∉ w.asIdeal) :
    e ^ (Nat.card (𝓞 F ⧸ w.asIdeal) - 1) - 1 ∈ w.asIdeal := by
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI := w.isMaximal
  letI : Field (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (𝓞 F ⧸ w.asIdeal) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_pow, sub_eq_zero, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ (mt (Ideal.Quotient.eq_zero_iff_mem).mp he)

theorem one_le_card_quotient_sub_one : 1 ≤ Nat.card (𝓞 F ⧸ w.asIdeal) - 1 := by
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI := w.isMaximal
  letI : Field (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  have : 1 < Nat.card (𝓞 F ⧸ w.asIdeal) := Finite.one_lt_card
  omega

theorem valued_pow_card_sub_one_sub_one_lt_one (y : K_w) (hy : v y = 1) :
    v (y ^ (Nat.card (𝓞 F ⧸ w.asIdeal) - 1) - 1) < 1 := by
  set M := Nat.card (𝓞 F ⧸ w.asIdeal) - 1 with hM

  have hnhds : {z : K_w | v (z - y) < 1} ∈ nhds y := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun z hz => ?_⟩
    rw [Set.mem_setOf_eq, Units.val_one] at hz
    exact (Valuation.restrict_lt_one_iff _).mp hz
  obtain ⟨_, ⟨a', rfl⟩, ha'⟩ :=
    ((HeightOneSpectrum.adicCompletion.ofCompletion_surjective F w).denseRange.comp
      (UniformSpace.Completion.denseRange_coe (α := WithVal (w.valuation F)))
      (HeightOneSpectrum.adicCompletion.continuous_ofCompletion F w)).inter_nhds_nonempty hnhds
  set a : F := WithVal.equiv (w.valuation F) a' with hadef
  have haa' : ι a = (a' : K_w) := by rw [hadef]; rfl
  have ha : v (ι a - y) < 1 := by rw [haa']; exact ha'
  have hva : v (ι a) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left v (x := y) (y := ι a - y) (by rw [hy]; exact ha)
    rw [add_sub_cancel, hy] at h
    exact h
  have hva' : w.valuation F a = 1 := by rw [← valued_algebraMap F w a]; exact hva

  obtain ⟨e₁, e₂, he₁, he₂, hae⟩ : ∃ e₁ e₂ : 𝓞 F, e₁ ∉ w.asIdeal ∧ e₂ ∉ w.asIdeal ∧ a * (e₁ : F) = (e₂ : F) := by
    obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq w a
    · refine ⟨d, n, d.2, fun hn => ?_, h⟩
      have h1 : w.valuation F (n : F) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w n).mpr hn
      have h2 : w.valuation F ((d : 𝓞 F) : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr d.2
      have h3 := congrArg (w.valuation F) h
      rw [map_mul, hva', one_mul, h2] at h3
      rw [← h3] at h1
      exact lt_irrefl _ h1
    · refine ⟨n, d, fun hn => ?_, d.2, h⟩
      have h1 : w.valuation F (n : F) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w n).mpr hn
      have h2 : w.valuation F ((d : 𝓞 F) : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr d.2
      have h3 := congrArg (w.valuation F) h
      rw [map_mul, hva', one_mul, h2] at h3
      rw [h3] at h1
      exact lt_irrefl _ h1

  set A : K_w := ι a with hA
  set E₁ : K_w := ι (e₁ : F) with hE₁
  set E₂ : K_w := ι (e₂ : F) with hE₂
  have hAE : A * E₁ = E₂ := by rw [hA, hE₁, hE₂, ← map_mul, hae]
  have hvE₁ : v E₁ = 1 := (valued_algebraMap_coe_eq_one_iff F w e₁).mpr he₁
  have hE₁M : v (E₁ ^ M - 1) < 1 := by
    have h := (valued_algebraMap_coe_lt_one_iff F w (e₁ ^ M - 1)).mpr (pow_card_sub_one_sub_one_mem F w e₁ he₁)
    have hc : ((e₁ ^ M - 1 : 𝓞 F) : F) = (e₁ : F) ^ M - 1 := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_pow, map_one]
    rw [hc, map_sub, map_pow, map_one] at h
    rw [hE₁]
    exact h
  have hE₂M : v (E₂ ^ M - 1) < 1 := by
    have h := (valued_algebraMap_coe_lt_one_iff F w (e₂ ^ M - 1)).mpr (pow_card_sub_one_sub_one_mem F w e₂ he₂)
    have hc : ((e₂ ^ M - 1 : 𝓞 F) : F) = (e₂ : F) ^ M - 1 := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_pow, map_one]
    rw [hc, map_sub, map_pow, map_one] at h
    rw [hE₂]
    exact h
  have hAM : v (A ^ M - 1) < 1 := by
    have h1 : (A ^ M - 1) * E₁ ^ M = (E₂ ^ M - 1) - (E₁ ^ M - 1) := by
      rw [sub_mul, ← mul_pow, hAE]; ring
    have h2 : v ((A ^ M - 1) * E₁ ^ M) < 1 := by
      rw [h1]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt hE₂M hE₁M)
    rwa [map_mul, map_pow, hvE₁, one_pow, mul_one] at h2
  have hyA : v (y ^ M - A ^ M) < 1 := by
    refine (valued_pow_sub_pow_le hy.le hva.le M).trans_lt ?_
    rw [Valuation.map_sub_swap]; exact ha
  have h : y ^ M - 1 = (y ^ M - A ^ M) + (A ^ M - 1) := by ring
  rw [h]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt hyA hAM)

end Completion

section Ball

variable (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] (Ψ : K →+* PadicAlgCl q)

noncomputable def normBall : ValuationSubring K where
  carrier := {y | ‖Ψ y‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at ha hb ⊢
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (PadicAlgCl.isNonarchimedean q _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [map_neg, norm_neg] using ha
  mem_or_inv_mem' y := by
    by_cases h : ‖Ψ y‖ ≤ 1
    · exact Or.inl h
    · refine Or.inr ?_
      rw [not_le] at h
      show ‖Ψ y⁻¹‖ ≤ 1
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ h.le

theorem mem_normBall_iff (y : K) : y ∈ normBall q Ψ ↔ ‖Ψ y‖ ≤ 1 := Iff.rfl

end Ball

theorem exists_monic_eval₂_eq_zero_of_norm_le_one (q : ℕ) [Fact q.Prime]
    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    (z : L') (hz : ‖((z : L') : PadicAlgCl q)‖ ≤ 1) :
    ∃ G : Polynomial ℤ_[q], G.Monic ∧
      Polynomial.eval₂ ((algebraMap ℚ_[q] L').comp (algebraMap ℤ_[q] ℚ_[q])) z G = 0 := by
  have hint : IsIntegral ℚ_[q] z := Algebra.IsIntegral.isIntegral z
  set g := minpoly ℚ_[q] z with hg
  have hgmonic : g.Monic := minpoly.monic hint
  have hg' : minpoly ℚ_[q] ((z : L') : PadicAlgCl q) = g :=
    minpoly.algebraMap_eq (algebraMap L' (PadicAlgCl q)).injective z
  have hcoeff : ∀ n, ‖g.coeff n‖ ≤ 1 := by
    have h1 : spectralValue g ≤ 1 := by
      rw [← hg']
      show spectralNorm ℚ_[q] (PadicAlgCl q) ((z : L') : PadicAlgCl q) ≤ 1
      rw [PadicAlgCl.spectralNorm_eq]
      exact hz
    exact (spectralValue_le_one_iff hgmonic).mp h1
  have hlifts : g ∈ Polynomial.lifts (algebraMap ℤ_[q] ℚ_[q]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨g.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨G, hGmap, -, hGmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hgmonic
  refine ⟨G, hGmonic, ?_⟩
  rw [← Polynomial.eval₂_map, hGmap, ← Polynomial.aeval_def]
  exact minpoly.aeval ℚ_[q] z

section Theta

variable (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
  (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q))
  (Φ : w.adicCompletion F ≃+* L')

local notation "K_w" => HeightOneSpectrum.adicCompletion F w
local notation "v" => (Valued.v : Valuation (HeightOneSpectrum.adicCompletion F w) (WithZero (Multiplicative ℤ)))

theorem valued_symm_unit_eq_one (u : ℤ_[q]) (hu : ‖u‖ = 1) :
    v (Φ.symm (algebraMap ℚ_[q] L' (algebraMap ℤ_[q] ℚ_[q] u))) = 1 := by
  have hqP : q.Prime := Fact.out
  have hq1 : q - 1 ≠ 0 := by have := hqP.two_le; omega
  apply valued_eq_one_of_pow hq1
  rw [← map_pow, ← map_pow, ← map_pow]
  have hinj : Function.Injective (fun c : ℤ_[q] => Φ.symm (algebraMap ℚ_[q] L' (algebraMap ℤ_[q] ℚ_[q] c))) :=
    Φ.symm.injective.comp ((algebraMap ℚ_[q] L').injective.comp (IsFractionRing.injective ℤ_[q] ℚ_[q]))
  have hu0 : u ^ (q - 1) ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hu)
  have hx0 : Φ.symm (algebraMap ℚ_[q] L' (algebraMap ℤ_[q] ℚ_[q] (u ^ (q - 1)))) ≠ 0 := by
    intro h
    apply hu0
    apply hinj
    simpa using h
  apply valued_eq_one_of_forall_exists_pow_eq q hqP.pos hx0
  intro k
  have hcop : q.Coprime (q * k + 1) := (Nat.coprime_mul_left_add_right q 1 k).mpr (Nat.coprime_one_right q)
  obtain ⟨zz, hzz⟩ := padicInt_exists_pow_eq q hcop (padicInt_norm_pow_sub_one_lt q hu)
  exact ⟨Φ.symm (algebraMap ℚ_[q] L' (algebraMap ℤ_[q] ℚ_[q] zz)), by rw [← map_pow, ← map_pow, ← map_pow, hzz]⟩

theorem valued_symm_le_one (c : ℤ_[q]) :
    v (Φ.symm (algebraMap ℚ_[q] L' (algebraMap ℤ_[q] ℚ_[q] c))) ≤ 1 := by
  by_cases hc : ‖c‖ = 1
  · exact (valued_symm_unit_eq_one F w q L' Φ c hc).le
  · have hc1 : ‖c‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one c) hc
    have h1c : ‖1 + c‖ = 1 := by
      rw [PadicInt.norm_add_eq_max_of_ne (by rw [norm_one]; exact hc1.ne'), norm_one, max_eq_left hc1.le]
    have h := valued_symm_unit_eq_one F w q L' Φ (1 + c) h1c
    rw [map_add, map_add, map_add, map_one, map_one, map_one] at h
    have h2 := Valuation.map_sub v (1 + Φ.symm (algebraMap ℚ_[q] L' (algebraMap ℤ_[q] ℚ_[q] c))) 1
    rw [add_sub_cancel_left, h, map_one, max_self] at h2
    exact h2

end Theta

end NumberField.PlaceDecomp.BridgeVal

open NumberField.PlaceDecomp.BridgeVal

theorem solution
    (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    (Φ : w.adicCompletion F ≃+* L') :
    (∀ y : w.adicCompletion F, y ∈ w.adicCompletionIntegers F ↔ ‖((Φ y : ↥L') : PadicAlgCl q)‖ ≤ 1) ∧
      ((q : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hqP : q.Prime := Fact.out
  haveI : CharZero (w.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (w.adicCompletion F)).injective

  let ψ : ℤ_[q] →+* L' := (algebraMap ℚ_[q] L').comp (algebraMap ℤ_[q] ℚ_[q])
  let Ψ : w.adicCompletion F →+* PadicAlgCl q := (algebraMap L' (PadicAlgCl q)).comp Φ.toRingHom
  have hΨ : ∀ y, ‖((Φ y : ↥L') : PadicAlgCl q)‖ = ‖Ψ y‖ := fun y => rfl
  let S : ValuationSubring (w.adicCompletion F) := normBall q Ψ

  have hSO : ∀ y : w.adicCompletion F, ‖Ψ y‖ ≤ 1 → Valued.v y ≤ 1 := by
    intro y hy
    obtain ⟨G, hGm, hG0⟩ := exists_monic_eval₂_eq_zero_of_norm_le_one q L' (Φ y) hy
    have hroot : Polynomial.eval₂ (Φ.symm.toRingHom.comp ψ) y G = 0 := by
      have h2 := Polynomial.hom_eval₂ G ψ Φ.symm.toRingHom (Φ y)
      have h3 : (Φ.symm.toRingHom) (Φ y) = y := Φ.symm_apply_apply y
      rw [h3] at h2
      rw [← h2]
      have h4 : Polynomial.eval₂ ψ (Φ y) G = 0 := hG0
      rw [h4, map_zero]
    refine valued_le_one_of_eval₂_eq_zero _ G hGm (fun i => ?_) y hroot
    exact valued_symm_le_one F w q L' Φ (G.coeff i)

  have hmS : ∀ x : w.adicCompletion F, Valued.v x < 1 → ‖Ψ x‖ ≤ 1 := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, map_zero, norm_zero]; exact zero_le_one
    rcases S.mem_or_inv_mem x with h | h
    · exact h
    · exfalso
      have h1 : Valued.v x⁻¹ ≤ 1 := hSO x⁻¹ h
      rw [map_inv₀] at h1
      have h2 : 1 < (Valued.v x)⁻¹ := one_lt_inv_iff₀.mpr ⟨(Valuation.pos_iff _).mpr hx0, hx⟩
      exact absurd h1 (not_le.mpr h2)

  have hUS : ∀ y : w.adicCompletion F, Valued.v y = 1 → ‖Ψ y‖ ≤ 1 := by
    intro y hy
    set M := Nat.card (𝓞 F ⧸ w.asIdeal) - 1 with hMdef
    have hM : 1 ≤ M := one_le_card_quotient_sub_one F w
    have hyM : y ^ M ∈ S := by
      have h1 : y ^ M - 1 ∈ S := hmS _ (valued_pow_card_sub_one_sub_one_lt_one F w y hy)
      have h2 := add_mem h1 (one_mem S)
      rwa [sub_add_cancel] at h2
    rcases S.mem_or_inv_mem y with h | h
    · exact h
    · have hy0 : y ≠ 0 := fun h0 => by rw [h0, map_zero] at hy; exact zero_ne_one hy
      have h2 : y = y ^ M * (y⁻¹) ^ (M - 1) := by
        rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hy0), ← pow_succ', Nat.sub_add_cancel hM]
      show y ∈ S
      rw [h2]
      exact mul_mem hyM (pow_mem h _)

  have hOS : ∀ y : w.adicCompletion F, Valued.v y ≤ 1 → ‖Ψ y‖ ≤ 1 := fun y hy =>
    (lt_or_eq_of_le hy).elim (hmS y) (hUS y)
  refine ⟨fun y => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hΨ]
    exact ⟨hOS y, hSO y⟩
  ·
    rw [← valued_natCast_lt_one_iff F w q]
    by_contra hvq
    have hvq1 : Valued.v ((q : ℕ) : w.adicCompletion F) = 1 :=
      le_antisymm (valued_natCast_le_one F w q) (not_lt.mp hvq)
    have h1 : Valued.v ((q : ℕ) : w.adicCompletion F)⁻¹ ≤ 1 := by rw [map_inv₀, hvq1, inv_one]
    have h2 := hOS _ h1
    rw [map_inv₀, norm_inv, map_natCast] at h2
    have hnq : ‖((q : ℕ) : PadicAlgCl q)‖ = (q : ℝ)⁻¹ := by
      rw [← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)) q]
      show ‖((q : ℚ_[q]) : PadicAlgCl q)‖ = (q : ℝ)⁻¹
      rw [PadicAlgCl.norm_extends, Padic.norm_p]
    rw [hnq, inv_inv] at h2
    have h3 : (1 : ℝ) < q := by exact_mod_cast hqP.one_lt
    linarith

end S_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
end P2MW
export P2MW.S_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv (solution)

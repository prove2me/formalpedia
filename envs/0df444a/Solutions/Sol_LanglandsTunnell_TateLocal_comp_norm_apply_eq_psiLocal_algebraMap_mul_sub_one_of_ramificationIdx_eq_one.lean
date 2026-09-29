-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/412a91aa-3f92-5778-8a15-08af740b2486

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one.LanglandsTunnell.TateLocal"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one.LanglandsTunnell"

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "higherUnitsAt HasConductorExponentAt"
namespace CompNormPin
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K))

private theorem valued_algebraMap_eq_of_ramificationIdx_eq_one (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (x : v.adicCompletion ℚ) :
    Valued.v (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) x) = Valued.v x := by
  have h := w.valued_adicCompletionSemialgHom ℚ K x
  have hv : w.1.under (𝓞 ℚ) = v := w.2
  rw [hv] at h
  have h2 : Valued.v x ^ v.asIdeal.ramificationIdx' w.1.asIdeal = Valued.v x := by
    rw [he, pow_one]
  exact h.trans h2

private theorem isIntegral_of_valued_le_one (x : w.1.adicCompletion K) (hx : Valued.v x ≤ 1) :
    IsIntegral (v.adicCompletionIntegers ℚ) x := by
  have hmem : x ∈ w.1.adicCompletionIntegers K := hx
  have hint : IsIntegral (v.adicCompletionIntegers ℚ) (⟨x, hmem⟩ : w.1.adicCompletionIntegers K) :=
    Algebra.IsIntegral.isIntegral _
  haveI : IsScalarTower (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers K) (w.1.adicCompletion K) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h := hint.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers K)
    (w.1.adicCompletion K))
  simpa using h

private theorem valued_le_one_of_isIntegral (q : v.adicCompletion ℚ)
    (hq : IsIntegral (v.adicCompletionIntegers ℚ) q) : Valued.v q ≤ 1 :=
  (Valuation.valuationSubring.integers
    (v := (Valued.v : Valuation (v.adicCompletion ℚ) _))).isIntegral_iff_v_le_one.mp hq

private theorem valued_norm_le_one_of_valued_le_one (x : w.1.adicCompletion K) (hx : Valued.v x ≤ 1) :
    Valued.v (Algebra.norm (v.adicCompletion ℚ) x) ≤ 1 :=
  valued_le_one_of_isIntegral v _
    (Algebra.isIntegral_norm (v.adicCompletion ℚ) (isIntegral_of_valued_le_one K v w x hx))

private theorem valued_norm_eq_one_of_valued_eq_one (u : (w.1.adicCompletion K)ˣ)
    (hu : Valued.v (u : w.1.adicCompletion K) = 1) :
    Valued.v ((Units.map (Algebra.norm (v.adicCompletion ℚ)) u : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  have h1 : Valued.v (Algebra.norm (v.adicCompletion ℚ) (u : w.1.adicCompletion K)) ≤ 1 :=
    valued_norm_le_one_of_valued_le_one K v w _ hu.le
  have hinv : Valued.v ((u⁻¹ : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have h2 : Valued.v (Algebra.norm (v.adicCompletion ℚ)
      ((u⁻¹ : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K)) ≤ 1 :=
    valued_norm_le_one_of_valued_le_one K v w _ hinv.le
  have hmul : Valued.v (Algebra.norm (v.adicCompletion ℚ) (u : w.1.adicCompletion K)) *
      Valued.v (Algebra.norm (v.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h3 := mul_le_of_le_one_right' (a := Valued.v (Algebra.norm (v.adicCompletion ℚ) (u : w.1.adicCompletion K))) h2
  rw [hmul] at h3
  exact le_antisymm h1 h3

private theorem isIntegral_trace_of_valued_le_one (z : w.1.adicCompletion K) (hz : Valued.v z ≤ 1) :
    IsIntegral (v.adicCompletionIntegers ℚ) (Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) z) :=
  Algebra.isIntegral_trace (isIntegral_of_valued_le_one K v w z hz)

private theorem exists_isIntegral_prod_one_add_mul_eq_add {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {ι : Type*} (s : Finset ι) (c : B) (hc : IsIntegral R c) (a : ι → B) (ha : ∀ i, IsIntegral R (a i)) :
    ∃ S : B, IsIntegral R S ∧ ∏ i ∈ s, (1 + c * a i) = 1 + c * ∑ i ∈ s, a i + c ^ 2 * S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert j s hj ih =>
    obtain ⟨S, hS, hprod⟩ := ih
    have hsum : IsIntegral R (∑ i ∈ s, a i) := IsIntegral.sum a fun i _ => ha i
    refine ⟨S + a j * ∑ i ∈ s, a i + c * a j * S, ?_, ?_⟩
    · exact (hS.add ((ha j).mul hsum)).add ((hc.mul (ha j)).mul hS)
    · rw [Finset.prod_insert hj, Finset.sum_insert hj, hprod]
      ring

private theorem exists_isIntegral_norm_one_add_smul_eq (c : v.adicCompletion ℚ) (hc : Valued.v c ≤ 1)
    (z : w.1.adicCompletion K) (hz : Valued.v z ≤ 1) :
    ∃ S : v.adicCompletion ℚ, IsIntegral (v.adicCompletionIntegers ℚ) S ∧
      Algebra.norm (v.adicCompletion ℚ) (1 + c • z) =
        1 + c * Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) z + c ^ 2 * S := by
  by_cases hc0 : c = 0
  · exact ⟨0, isIntegral_zero, by simp [hc0]⟩
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have hcint : IsIntegral (v.adicCompletionIntegers ℚ)
      (algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) c) := by
    have hcQ : c = algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ⟨c, hc⟩ := rfl
    rw [hcQ, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have hzint : IsIntegral (v.adicCompletionIntegers ℚ) z := isIntegral_of_valued_le_one K v w z hz
  have hσ : ∀ σ : w.1.adicCompletion K →ₐ[v.adicCompletion ℚ] AlgebraicClosure (v.adicCompletion ℚ),
      IsIntegral (v.adicCompletionIntegers ℚ) (σ z) :=
    fun σ => hzint.map (σ.restrictScalars (v.adicCompletionIntegers ℚ))
  obtain ⟨SE, hSE, hprod⟩ := exists_isIntegral_prod_one_add_mul_eq_add (R := v.adicCompletionIntegers ℚ)
    (Finset.univ : Finset (w.1.adicCompletion K →ₐ[v.adicCompletion ℚ] AlgebraicClosure (v.adicCompletion ℚ)))
    (algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) c) hcint (fun σ => σ z) hσ
  have hnorm : algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ))
      (Algebra.norm (v.adicCompletion ℚ) (1 + c • z)) =
        1 + algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) c *
            ∑ σ : w.1.adicCompletion K →ₐ[v.adicCompletion ℚ] AlgebraicClosure (v.adicCompletion ℚ), σ z +
          algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) c ^ 2 * SE := by
    rw [Algebra.norm_eq_prod_embeddings]
    calc (∏ σ : w.1.adicCompletion K →ₐ[v.adicCompletion ℚ] AlgebraicClosure (v.adicCompletion ℚ), σ (1 + c • z))
        = ∏ σ : w.1.adicCompletion K →ₐ[v.adicCompletion ℚ] AlgebraicClosure (v.adicCompletion ℚ),
            (1 + algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) c * σ z) :=
          Finset.prod_congr rfl fun σ _ => by rw [map_add, map_one, Algebra.smul_def, map_mul, σ.commutes]
      _ = _ := hprod
  have htrace : algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ))
      (Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) z) =
        ∑ σ : w.1.adicCompletion K →ₐ[v.adicCompletion ℚ] AlgebraicClosure (v.adicCompletion ℚ), σ z :=
    trace_eq_sum_embeddings _
  have hc' : algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) c ≠ 0 :=
    (map_ne_zero _).mpr hc0
  refine ⟨(Algebra.norm (v.adicCompletion ℚ) (1 + c • z) - 1 -
      c * Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) z) / c ^ 2, ?_, ?_⟩
  · have hS' : algebraMap (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ))
        ((Algebra.norm (v.adicCompletion ℚ) (1 + c • z) - 1 -
          c * Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) z) / c ^ 2) = SE := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hc')
      rw [← map_pow, ← map_mul, mul_div_cancel₀ _ (pow_ne_zero 2 hc0), map_sub, map_sub, map_one, map_mul, hnorm,
        htrace, map_pow]
      ring
    have hSint : IsIntegral (v.adicCompletionIntegers ℚ)
        ((IsScalarTower.toAlgHom (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
          (AlgebraicClosure (v.adicCompletion ℚ))) ((Algebra.norm (v.adicCompletion ℚ) (1 + c • z) - 1 -
            c * Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) z) / c ^ 2)) := by
      rw [IsScalarTower.coe_toAlgHom', hS']
      exact hSE
    exact (isIntegral_algHom_iff _ (algebraMap (v.adicCompletion ℚ)
      (AlgebraicClosure (v.adicCompletion ℚ))).injective).mp hSint
  · rw [mul_div_cancel₀ _ (pow_ne_zero 2 hc0)]
    ring

private theorem valued_norm_one_add_sub_one_sub_trace_le (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (n : ℕ)
    (x : w.1.adicCompletion K) (hx : Valued.v x ≤ WithZero.exp (-(n : ℤ))) :
    ∃ E : v.adicCompletion ℚ,
      Algebra.norm (v.adicCompletion ℚ) (1 + x) =
          1 + Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) x + E ∧
        Valued.v E ≤ WithZero.exp (-(2 * (n : ℤ))) ∧
          Valued.v (Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) x) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨c₁, hc₁⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp (-(n : ℤ)))
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc₁
    exact WithZero.exp_ne_zero hc₁.symm
  have hc₁1 : Valued.v c₁ ≤ 1 := by
    rw [hc₁, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hcw : Valued.v (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) c₁) = WithZero.exp (-(n : ℤ)) := by
    rw [valued_algebraMap_eq_of_ramificationIdx_eq_one K v w he, hc₁]
  have hcw0 : algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) c₁ ≠ 0 := (map_ne_zero _).mpr hc₁0
  have hcwpos : (0 : WithZero (Multiplicative ℤ)) <
      Valued.v (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) c₁) := by
    rw [hcw]
    exact WithZero.exp_pos
  have hz1 : Valued.v (x / algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) c₁) ≤ 1 := by
    rw [map_div₀, div_le_one₀ hcwpos, hcw]
    exact hx
  have hx_eq : c₁ • (x / algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) c₁) = x := by
    rw [Algebra.smul_def, mul_div_cancel₀ _ hcw0]
  obtain ⟨S, hS, hN⟩ := exists_isIntegral_norm_one_add_smul_eq K v w c₁ hc₁1 _ hz1
  have htr : Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K)
      (c₁ • (x / algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) c₁)) =
        c₁ * Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K)
          (x / algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) c₁) := by
    rw [LinearMap.map_smul, smul_eq_mul]
  rw [hx_eq] at hN htr
  refine ⟨c₁ ^ 2 * S, ?_, ?_, ?_⟩
  · rw [hN, htr]
  · have h1 : Valued.v (c₁ ^ 2 * S) ≤ Valued.v c₁ ^ 2 := by
      rw [Valuation.map_mul, Valuation.map_pow]
      exact mul_le_of_le_one_right' (valued_le_one_of_isIntegral v S hS)
    refine h1.trans (le_of_eq ?_)
    rw [hc₁, ← WithZero.exp_nsmul]
    congr 1
    ring
  · rw [htr, Valuation.map_mul, hc₁]
    exact mul_le_of_le_one_right'
      (valued_le_one_of_isIntegral v _ (isIntegral_trace_of_valued_le_one K v w _ hz1))

private theorem norm_mem_higherUnitsAt_of_mem_of_ramificationIdx_eq_one
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (n : ℕ) (u : (w.1.adicCompletion K)ˣ)
    (hu : u ∈ higherUnitsAt K w.1 n) :
    Units.map (Algebra.norm (v.adicCompletion ℚ)) u ∈ higherUnitsAt ℚ v n := by
  obtain ⟨hval, hball⟩ := hu
  refine ⟨valued_norm_eq_one_of_valued_eq_one K v w u hval, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact Or.inl hn
  right
  have hx : Valued.v ((u : w.1.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    rcases hball with h0 | h
    · exact absurd h0 hn.ne'
    · exact h
  obtain ⟨E, hNE, hE, htrx⟩ := valued_norm_one_add_sub_one_sub_trace_le K v w he n _ hx
  have hu1 : (1 : w.1.adicCompletion K) + ((u : w.1.adicCompletion K) - 1) = u := by ring
  rw [hu1] at hNE
  show Valued.v (Algebra.norm (v.adicCompletion ℚ) (u : w.1.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))
  have hre : Algebra.norm (v.adicCompletion ℚ) (u : w.1.adicCompletion K) - 1 =
      Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) ((u : w.1.adicCompletion K) - 1) + E := by
    rw [hNE]
    ring
  rw [hre]
  refine (Valuation.map_add _ _ _).trans (max_le htrx (hE.trans ?_))
  rw [WithZero.exp_le_exp]
  omega

private theorem psiLocal_mul_eq_one_of_mem_higherUnitsAt (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ)
    (hχ : HasConductorExponentAt ℚ v χ a) (c : (v.adicCompletion ℚ)ˣ)
    (hc : ∀ u ∈ higherUnitsAt ℚ v ((a - 1) / 2 + 1),
      (χ u : ℂ) =
        NumberField.StandardAddChar.psiLocal ℚ v ((c : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1)))
    (E : v.adicCompletion ℚ) (hE : Valued.v E ≤ WithZero.exp (-(2 * (((a - 1) / 2 + 1 : ℕ) : ℤ)))) :
    NumberField.StandardAddChar.psiLocal ℚ v ((c : v.adicCompletion ℚ) * E) = 1 := by
  have hElt : Valued.v E < 1 := by
    refine hE.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu1 : Valued.v ((1 : v.adicCompletion ℚ) + E) = 1 :=
    (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).map_one_add_of_lt hElt
  have hne : (1 : v.adicCompletion ℚ) + E ≠ 0 := by
    intro h
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  have h1E : ((1 : v.adicCompletion ℚ) + E) - 1 = E := by ring
  have hmem_m : Units.mk0 _ hne ∈ higherUnitsAt ℚ v ((a - 1) / 2 + 1) := by
    refine ⟨hu1, Or.inr ?_⟩
    show Valued.v (((1 : v.adicCompletion ℚ) + E) - 1) ≤ _
    rw [h1E]
    refine hE.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  have hmem_a : Units.mk0 _ hne ∈ higherUnitsAt ℚ v a := by
    refine ⟨hu1, ?_⟩
    rcases Nat.eq_zero_or_pos a with h0 | _
    · exact Or.inl h0
    right
    show Valued.v (((1 : v.adicCompletion ℚ) + E) - 1) ≤ _
    rw [h1E]
    refine hE.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  have h := hc _ hmem_m
  rw [hχ.1 _ hmem_a, Units.val_one] at h
  have hcoe : ((Units.mk0 _ hne : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 + E := rfl
  rw [hcoe, h1E] at h
  exact h.symm

private theorem psiLocal_algebraMap_mul_eq_psiLocal_mul_trace (c : v.adicCompletion ℚ) (x : w.1.adicCompletion K) :
    NumberField.StandardAddChar.psiLocal K w.1 (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) c * x) =
      NumberField.StandardAddChar.psiLocal ℚ v
        (c * Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) x) := by
  rw [NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace ℚ K v w, ← Algebra.smul_def, LinearMap.map_smul,
    smul_eq_mul]

end LanglandsTunnell.TateLocal.CompNormPin

theorem solution
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (hχ : HasConductorExponentAt ℚ v χ a)
    (c : (v.adicCompletion ℚ)ˣ)
    (hc : ∀ u ∈ higherUnitsAt ℚ v ((a - 1) / 2 + 1),
      (χ u : ℂ) =
        NumberField.StandardAddChar.psiLocal ℚ v ((c : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1))) :
    ∀ u ∈ higherUnitsAt K w.1 ((a - 1) / 2 + 1),
      ((χ.comp (Units.map (Algebra.norm (v.adicCompletion ℚ)))) u : ℂ) =
        NumberField.StandardAddChar.psiLocal K w.1
          (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) (c : v.adicCompletion ℚ) *
            ((u : w.1.adicCompletion K) - 1)) := by
  intro u hu
  have hmem : Units.map (Algebra.norm (v.adicCompletion ℚ)) u ∈ higherUnitsAt ℚ v ((a - 1) / 2 + 1) :=
    LanglandsTunnell.TateLocal.CompNormPin.norm_mem_higherUnitsAt_of_mem_of_ramificationIdx_eq_one K v w he _ u hu
  obtain ⟨-, hball⟩ := hu
  have hx : Valued.v ((u : w.1.adicCompletion K) - 1) ≤ WithZero.exp (-(((a - 1) / 2 + 1 : ℕ) : ℤ)) := by
    rcases hball with h0 | h
    · exact absurd h0 (Nat.succ_ne_zero _)
    · exact h
  obtain ⟨E, hNE, hE, -⟩ :=
    LanglandsTunnell.TateLocal.CompNormPin.valued_norm_one_add_sub_one_sub_trace_le K v w he _ _ hx
  have hu1 : (1 : w.1.adicCompletion K) + ((u : w.1.adicCompletion K) - 1) = u := by ring
  rw [hu1] at hNE
  rw [MonoidHom.comp_apply, hc _ hmem]
  show NumberField.StandardAddChar.psiLocal ℚ v
      ((c : v.adicCompletion ℚ) * (Algebra.norm (v.adicCompletion ℚ) (u : w.1.adicCompletion K) - 1)) = _
  have hre : (c : v.adicCompletion ℚ) * (Algebra.norm (v.adicCompletion ℚ) (u : w.1.adicCompletion K) - 1) =
      (c : v.adicCompletion ℚ) *
          Algebra.trace (v.adicCompletion ℚ) (w.1.adicCompletion K) ((u : w.1.adicCompletion K) - 1) +
        (c : v.adicCompletion ℚ) * E := by
    rw [hNE]
    ring
  rw [hre, AddChar.map_add_eq_mul,
    LanglandsTunnell.TateLocal.CompNormPin.psiLocal_mul_eq_one_of_mem_higherUnitsAt v χ a hχ c hc E hE, mul_one,
    LanglandsTunnell.TateLocal.CompNormPin.psiLocal_algebraMap_mul_eq_psiLocal_mul_trace K v w]

end S_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one (solution)

-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b6e5a91e-7036-5167-ba79-5968be18a298

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul.LanglandsTunnell LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.HasConductorExponentAt"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "higherUnitsAt HasConductorExponentAt conductorExponentAt conductorExponentAt_eq_of_hasConductorExponentAt"
namespace NormBound
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))

private theorem valued_algebraMap_eq_pow (x : v.adicCompletion E) :
    Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.1.asIdeal := by
  have h := w.valued_adicCompletionSemialgHom E M x
  have hv : w.1.under (𝓞 E) = v := w.2
  rw [hv] at h
  exact h

private theorem ramificationIdx_pos : v.asIdeal.ramificationIdx' w.1.asIdeal ≠ 0 := by
  have h := ramificationIdx_ne_zero (𝓞 E) (𝓞 M) (algebraMap_injective_of_field_isFractionRing (𝓞 E) (𝓞 M) E M) w.1
  have hv : w.1.under (𝓞 E) = v := w.2
  rw [hv] at h
  exact h

private theorem isIntegral_of_valued_le_one (x : w.1.adicCompletion M) (hx : Valued.v x ≤ 1) :
    IsIntegral (v.adicCompletionIntegers E) x := by
  have hmem : x ∈ w.1.adicCompletionIntegers M := hx
  have hint : IsIntegral (v.adicCompletionIntegers E) (⟨x, hmem⟩ : w.1.adicCompletionIntegers M) :=
    Algebra.IsIntegral.isIntegral _
  haveI : IsScalarTower (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) (w.1.adicCompletion M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h := hint.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M)
    (w.1.adicCompletion M))
  simpa using h

private theorem valued_norm_le_one_of_valued_le_one (x : w.1.adicCompletion M) (hx : Valued.v x ≤ 1) :
    Valued.v (Algebra.norm (v.adicCompletion E) x) ≤ 1 := by
  have hint : IsIntegral (v.adicCompletionIntegers E) (Algebra.norm (v.adicCompletion E) x) :=
    Algebra.isIntegral_norm (v.adicCompletion E) (isIntegral_of_valued_le_one E M v w x hx)
  have hO := Valuation.valuationSubring.integers (v := (Valued.v : Valuation (v.adicCompletion E) _))
  exact hO.isIntegral_iff_v_le_one.mp hint

private theorem valued_norm_eq_one_of_valued_eq_one (u : (w.1.adicCompletion M)ˣ)
    (hu : Valued.v (u : w.1.adicCompletion M) = 1) :
    Valued.v ((Units.map (Algebra.norm (v.adicCompletion E)) u : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 := by
  have h1 : Valued.v (Algebra.norm (v.adicCompletion E) (u : w.1.adicCompletion M)) ≤ 1 :=
    valued_norm_le_one_of_valued_le_one E M v w _ hu.le
  have hinv : Valued.v ((u⁻¹ : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have h2 : Valued.v (Algebra.norm (v.adicCompletion E)
      ((u⁻¹ : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M)) ≤ 1 :=
    valued_norm_le_one_of_valued_le_one E M v w _ hinv.le
  have hmul : Valued.v (Algebra.norm (v.adicCompletion E) (u : w.1.adicCompletion M)) *
      Valued.v (Algebra.norm (v.adicCompletion E) ((u⁻¹ : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h3 := mul_le_of_le_one_right' (a := Valued.v (Algebra.norm (v.adicCompletion E) (u : w.1.adicCompletion M))) h2
  rw [hmul] at h3
  exact le_antisymm h1 h3

private theorem exists_isIntegral_prod_one_add_mul_eq {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {ι : Type*} (s : Finset ι) (c : B) (hc : IsIntegral R c) (a : ι → B) (ha : ∀ i, IsIntegral R (a i)) :
    ∃ S : B, IsIntegral R S ∧ ∏ i ∈ s, (1 + c * a i) = 1 + c * S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert j s hj ih =>
    obtain ⟨S, hS, hprod⟩ := ih
    refine ⟨S + a j + c * S * a j, ?_, ?_⟩
    · exact (hS.add (ha j)).add ((hc.mul hS).mul (ha j))
    · rw [Finset.prod_insert hj, hprod]
      ring

private theorem valued_le_one_of_isIntegral (q : v.adicCompletion E)
    (hq : IsIntegral (v.adicCompletionIntegers E) q) : Valued.v q ≤ 1 :=
  (Valuation.valuationSubring.integers
    (v := (Valued.v : Valuation (v.adicCompletion E) _))).isIntegral_iff_v_le_one.mp hq

private theorem exists_isIntegral_norm_one_add_smul_sub_one_eq (c : v.adicCompletion E) (hc : Valued.v c ≤ 1)
    (z : w.1.adicCompletion M) (hz : Valued.v z ≤ 1) :
    ∃ S : v.adicCompletion E, IsIntegral (v.adicCompletionIntegers E) S ∧
      Algebra.norm (v.adicCompletion E) (1 + c • z) - 1 = c * S := by
  by_cases hc0 : c = 0
  · exact ⟨0, isIntegral_zero, by simp [hc0]⟩
  haveI : CharZero (v.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (v.adicCompletion E)).injective
  have hcint : IsIntegral (v.adicCompletionIntegers E)
      (algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E)) c) := by
    have hcE : c = algebraMap (v.adicCompletionIntegers E) (v.adicCompletion E) ⟨c, hc⟩ := rfl
    rw [hcE, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have hzint : IsIntegral (v.adicCompletionIntegers E) z := isIntegral_of_valued_le_one E M v w z hz
  have hσ : ∀ σ : w.1.adicCompletion M →ₐ[v.adicCompletion E] AlgebraicClosure (v.adicCompletion E),
      IsIntegral (v.adicCompletionIntegers E) (σ z) :=
    fun σ => hzint.map (σ.restrictScalars (v.adicCompletionIntegers E))
  obtain ⟨SE, hSE, hprod⟩ := exists_isIntegral_prod_one_add_mul_eq (R := v.adicCompletionIntegers E)
    (Finset.univ : Finset (w.1.adicCompletion M →ₐ[v.adicCompletion E] AlgebraicClosure (v.adicCompletion E)))
    (algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E)) c) hcint (fun σ => σ z) hσ
  have hnorm : algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E))
      (Algebra.norm (v.adicCompletion E) (1 + c • z)) =
        1 + algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E)) c * SE := by
    rw [Algebra.norm_eq_prod_embeddings]
    calc (∏ σ : w.1.adicCompletion M →ₐ[v.adicCompletion E] AlgebraicClosure (v.adicCompletion E), σ (1 + c • z))
        = ∏ σ : w.1.adicCompletion M →ₐ[v.adicCompletion E] AlgebraicClosure (v.adicCompletion E),
            (1 + algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E)) c * σ z) :=
          Finset.prod_congr rfl fun σ _ => by rw [map_add, map_one, Algebra.smul_def, map_mul, σ.commutes]
      _ = 1 + algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E)) c * SE := by
          convert hprod using 2
  refine ⟨(Algebra.norm (v.adicCompletion E) (1 + c • z) - 1) / c, ?_, by field_simp⟩
  have hdiv : algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E))
      ((Algebra.norm (v.adicCompletion E) (1 + c • z) - 1) / c) = SE := by
    have hc' : algebraMap (v.adicCompletion E) (AlgebraicClosure (v.adicCompletion E)) c ≠ 0 :=
      (map_ne_zero _).mpr hc0
    rw [map_div₀, map_sub, map_one, hnorm]
    field_simp
    ring
  have hSint : IsIntegral (v.adicCompletionIntegers E)
      ((IsScalarTower.toAlgHom (v.adicCompletionIntegers E) (v.adicCompletion E)
        (AlgebraicClosure (v.adicCompletion E))) ((Algebra.norm (v.adicCompletion E) (1 + c • z) - 1) / c)) := by
    rw [IsScalarTower.coe_toAlgHom', hdiv]
    exact hSE
  exact (isIntegral_algHom_iff _ (algebraMap (v.adicCompletion E)
    (AlgebraicClosure (v.adicCompletion E))).injective).mp hSint

private theorem valued_norm_one_add_smul_sub_one_le (c : v.adicCompletion E) (hc : Valued.v c ≤ 1)
    (z : w.1.adicCompletion M) (hz : Valued.v z ≤ 1) :
    Valued.v (Algebra.norm (v.adicCompletion E) (1 + c • z) - 1) ≤ Valued.v c := by
  obtain ⟨S, hS, hEq⟩ := exists_isIntegral_norm_one_add_smul_sub_one_eq E M v w c hc z hz
  rw [hEq, Valuation.map_mul]
  exact mul_le_of_le_one_right' (valued_le_one_of_isIntegral E v S hS)

private theorem norm_mem_higherUnitsAt_of_mem_higherUnitsAt_mul (n : ℕ)
    (u : (w.1.adicCompletion M)ˣ)
    (hu : u ∈ higherUnitsAt M w.1 (v.asIdeal.ramificationIdx' w.1.asIdeal * n)) :
    Units.map (Algebra.norm (v.adicCompletion E)) u ∈ higherUnitsAt E v n := by
  obtain ⟨hval, hball⟩ := hu
  refine ⟨valued_norm_eq_one_of_valued_eq_one E M v w u hval, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact Or.inl hn
  right
  have hen : v.asIdeal.ramificationIdx' w.1.asIdeal * n ≠ 0 := Nat.mul_ne_zero (ramificationIdx_pos E M v w) hn.ne'
  have hball' : Valued.v ((u : w.1.adicCompletion M) - 1) ≤
      WithZero.exp (-((v.asIdeal.ramificationIdx' w.1.asIdeal * n : ℕ) : ℤ)) := by
    rcases hball with h0 | h
    · exact absurd h0 hen
    · exact h
  obtain ⟨c, hc⟩ := v.valuedAdicCompletion_surjective E (WithZero.exp (-(n : ℤ)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have hc1 : Valued.v c ≤ 1 := by
    rw [hc, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hcw : Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) =
      WithZero.exp (-((v.asIdeal.ramificationIdx' w.1.asIdeal * n : ℕ) : ℤ)) := by
    rw [valued_algebraMap_eq_pow E M v w c, hc, ← WithZero.exp_nsmul]
    congr 1
    push_cast
    ring
  have hcw0 : algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c ≠ 0 := (map_ne_zero _).mpr hc0
  have hcwpos : (0 : WithZero (Multiplicative ℤ)) <
      Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) := by
    rw [hcw]
    exact WithZero.exp_pos
  have hz1 : Valued.v (((u : w.1.adicCompletion M) - 1) / algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) ≤
      1 := by
    rw [map_div₀, div_le_one₀ hcwpos, hcw]
    exact hball'
  have hu_eq : (1 : w.1.adicCompletion M) +
      c • (((u : w.1.adicCompletion M) - 1) / algebraMap (v.adicCompletion E) (w.1.adicCompletion M) c) =
        (u : w.1.adicCompletion M) := by
    rw [Algebra.smul_def, mul_div_cancel₀ _ hcw0]
    ring
  have key := valued_norm_one_add_smul_sub_one_le E M v w c hc1 _ hz1
  rw [hu_eq, hc] at key
  exact key

private theorem exists_hasConductorExponentAt_comp_norm_le (η : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ)
    (hη : HasConductorExponentAt E v η a) :
    ∃ b : ℕ, HasConductorExponentAt M w.1 (η.comp (Units.map (Algebra.norm (v.adicCompletion E)))) b ∧
      b ≤ v.asIdeal.ramificationIdx' w.1.asIdeal * a := by
  classical
  have htriv : ∀ u ∈ higherUnitsAt M w.1 (v.asIdeal.ramificationIdx' w.1.asIdeal * a),
      (η.comp (Units.map (Algebra.norm (v.adicCompletion E)))) u = 1 := fun u hu =>
    hη.1 _ (norm_mem_higherUnitsAt_of_mem_higherUnitsAt_mul E M v w a u hu)
  have hex : ∃ m : ℕ, ∀ u ∈ higherUnitsAt M w.1 m,
      (η.comp (Units.map (Algebra.norm (v.adicCompletion E)))) u = 1 := ⟨_, htriv⟩
  refine ⟨Nat.find hex, ⟨Nat.find_spec hex, fun m hm => ?_⟩, Nat.find_min' hex htriv⟩
  by_contra hcon
  exact Nat.find_min hex hm fun u hu => Classical.byContradiction fun hne => hcon ⟨u, hu, hne⟩

private theorem conductorExponentAt_comp_norm_le (η : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ)
    (hη : HasConductorExponentAt E v η a) :
    conductorExponentAt M w.1 (η.comp (Units.map (Algebra.norm (v.adicCompletion E)))) ≤
      v.asIdeal.ramificationIdx' w.1.asIdeal * a := by
  obtain ⟨b, hb, hle⟩ := exists_hasConductorExponentAt_comp_norm_le E M v w η a hη
  rw [conductorExponentAt_eq_of_hasConductorExponentAt M w.1 hb]
  exact hle

end LanglandsTunnell.TateLocal.NormBound

theorem solution
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (μ : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ) (ha : LanglandsTunnell.TateLocal.HasConductorExponentAt E v μ a) :
    ∃ b' : ℕ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt M w.1
        (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) b' ∧
      b' ≤ v.asIdeal.ramificationIdx' w.1.asIdeal * a := by
  exact LanglandsTunnell.TateLocal.NormBound.exists_hasConductorExponentAt_comp_norm_le E M v w μ a ha

end S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul (solution)

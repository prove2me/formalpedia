-- Prove2me | solution 1 for LocalGL2.sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/63ba276a-cee8-583a-9e06-e9b755b89178

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
import Theorems.Thm_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount

set_option autoImplicit false

open LocalGL2 HeckePair

namespace P2mC0bLocDock

section Generic

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

abbrev sc (K : Type*) [Field K] : Kˣ →* GL (Fin 2) K :=
  Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom

theorem coe_sc (t : Kˣ) :
    ((sc K t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (t : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.coe_map]
  show Matrix.scalar (Fin 2) (t : K) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem central_of_coe_eq_smul {z : GL (Fin 2) K} {a : K}
    (hz : (z : Matrix (Fin 2) (Fin 2) K) = a • (1 : Matrix (Fin 2) (Fin 2) K)) (g : GL (Fin 2) K) :
    Commute z g := by
  show z * g = g * z
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

theorem coe_diagPi_mul_localRepInf :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem commute_diagPi_localRepInf : Commute (diagPi ϖ hϖ0) (localRepInf ϖ hϖ0 : GL (Fin 2) K) := by
  show diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 = localRepInf ϖ hϖ0 * diagPi ϖ hϖ0
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_diagPi, coe_localRepInf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_diagPi_mul_localRepInf_of_coe {z : GL (Fin 2) K}
    (hz : (z : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    z = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 :=
  Units.ext (hz.trans (coe_diagPi_mul_localRepInf ϖ hϖ0).symm)

theorem sc_mk0_eq_of_coe {z : GL (Fin 2) K}
    (hz : (z : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    sc K (Units.mk0 (algebraMap R K ϖ) hϖ0) = z :=
  Units.ext (by rw [coe_sc, hz]; rfl)

theorem sc_mem_integralSubgroup_of_eq {e : Rˣ} {t : Kˣ} (he : algebraMap R K (e : R) = (t : K)) :
    sc K t ∈ integralSubgroup R K := by
  refine ⟨Units.map (Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom e, ?_⟩
  apply Units.ext
  rw [coe_sc]
  show (algebraMap R K).mapMatrix (Matrix.scalar (Fin 2) (e : R)) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, he]

theorem mul_zpow_mul_mem_doubleCoset {G : Type*} [Group G] (U : Subgroup G) {P Q c e x : G}
    (hc : ∀ g : G, Commute c g) (hPQ : Commute P Q) (hcPQ : c = P * Q) (he : e ∈ U)
    (s a b : ℤ) (hx : x ∈ doubleCoset U (P ^ a * Q ^ b)) :
    e * c ^ s * x ∈ doubleCoset U (P ^ (s + a) * Q ^ (s + b)) := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_doubleCoset_iff.mp hx
  refine mem_doubleCoset_iff.mpr ⟨e * u₁, mul_mem he hu₁, u₂, hu₂, ?_⟩
  have h1 : c ^ s * u₁ = u₁ * c ^ s := ((hc u₁).zpow_left s).eq
  have h2 : P ^ (s + a) * Q ^ (s + b) = c ^ s * (P ^ a * Q ^ b) := by
    have h3 : P ^ a * Q ^ s = Q ^ s * P ^ a := (hPQ.zpow_zpow a s).eq
    rw [hcPQ, hPQ.mul_zpow, zpow_add, zpow_add]
    calc P ^ s * P ^ a * (Q ^ s * Q ^ b) = P ^ s * (P ^ a * Q ^ s) * Q ^ b := by simp only [mul_assoc]
      _ = P ^ s * Q ^ s * (P ^ a * Q ^ b) := by rw [h3]; simp only [mul_assoc]
  calc e * u₁ * (P ^ (s + a) * Q ^ (s + b)) * u₂
      = e * (u₁ * c ^ s) * (P ^ a * Q ^ b) * u₂ := by rw [h2]; simp only [mul_assoc]
    _ = e * c ^ s * (u₁ * (P ^ a * Q ^ b) * u₂) := by rw [← h1]; simp only [mul_assoc]

end Generic

section NumberFieldPlace

open NumberField IsDedekindDomain AutomorphicForm

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem valued_uniformiser {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := by

  obtain ⟨p, hp⟩ := HeightOneSpectrum.intValuation_exists_uniformizer u
  have hpv : Valued.v ((p : 𝓞 F) : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hp]

  set p' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) p with hp'
  have hp'v : Valued.v (p' : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := hpv
  have hp'max : p' ∈ IsLocalRing.maximalIdeal (u.adicCompletionIntegers F) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 F) F u, hp'v, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hp'max
  obtain ⟨a, ha⟩ := hp'max
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) := by
    rw [← hp'v, ← ha]
    push_cast
    rw [map_mul]
    calc Valued.v (a : u.adicCompletion F) * Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F)
        ≤ 1 * Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) :=
          mul_le_mul_of_nonneg_right a.2 zero_le'
      _ = Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) := one_mul _

  have hlt : Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have hne : Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (fun h => hϖ.ne_zero (by exact_mod_cast h))
  refine le_antisymm ?_ hle
  rw [← WithZero.log_le_iff_le_exp hne]
  have h0 : WithZero.log (Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]; exact hlt
  omega

theorem finite_quotient_span {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Finite (u.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) :=
  Finite.of_equiv (IsLocalRing.ResidueField (u.adicCompletionIntegers F))
    (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).toEquiv

theorem natCard_quotient_span_uniformiser {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Nat.card (u.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm u.asIdeal := by
  classical

  have e1 : (u.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) ≃
      IsLocalRing.ResidueField (u.adicCompletionIntegers F) :=
    (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).symm.toEquiv

  set f : 𝓞 F →+* IsLocalRing.ResidueField (u.adicCompletionIntegers F) :=
    (IsLocalRing.residue (u.adicCompletionIntegers F)).comp (algebraMap (𝓞 F) (u.adicCompletionIntegers F))
    with hf
  have hfs : Function.Surjective f := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 F) F u
  have hker : RingHom.ker f = u.asIdeal := by
    refine (Ideal.IsMaximal.eq_of_le u.isMaximal (RingHom.ker_ne_top f) fun a ha => ?_).symm
    rw [RingHom.mem_ker]
    exact NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 F) F u ha
  have e2 : (𝓞 F ⧸ u.asIdeal) ≃+* IsLocalRing.ResidueField (u.adicCompletionIntegers F) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hfs)
  rw [Nat.card_congr e1, ← Nat.card_congr e2.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem coe_integralSubgroup_eq_localIntegralSet :
    ((integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F) :
        Subgroup (GL (Fin 2) (u.adicCompletion F))) : Set (GL (Fin 2) (u.adicCompletion F))) =
      localIntegralSet F u := by
  ext g
  have hinj : Function.Injective
      (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)) := Subtype.val_injective
  have hrange : Set.range (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)) =
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := Subtype.range_val
  rw [SetLike.mem_coe, FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj, mem_localIntegralSet]
  simp only [hrange, SetLike.mem_coe]

theorem exists_units_coe_eq_mul_zpow_log {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    {x : u.adicCompletion F} (hx : x ≠ 0) :
    ∃ e : (u.adicCompletionIntegers F)ˣ,
      ((e : u.adicCompletionIntegers F) : u.adicCompletion F) =
        x * ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ WithZero.log (Valued.v x) := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hπ := valued_uniformiser F u hϖ
  set L : ℤ := WithZero.log (Valued.v x) with hL
  have hx' : Valued.v x = WithZero.exp L := (WithZero.exp_log hvx).symm
  have hval : Valued.v (x * ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ L) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hx', ← WithZero.exp_zsmul, zsmul_eq_mul, Int.cast_id, mul_neg_one,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hmem : x * ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ L ∈ u.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hval.le
  obtain ⟨e, he⟩ := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    (a := (⟨_, hmem⟩ : u.adicCompletionIntegers F))).2 hval
  exact ⟨e, congrArg Subtype.val he⟩

theorem main
    (ϖ : u.adicCompletionIntegers F) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (u.adicCompletion F))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (u.adicCompletion F))
    (hz : (z : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm u.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm u.asIdeal * W k (d + 2))
    (k j : ℕ) (t : (u.adicCompletion F)ˣ) (y : u.adicCompletion F)
    (ht : Valued.v (t : u.adicCompletion F) ^ 2 =
      Valued.v (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ) ^ (k + 2 * j)) :
    ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ *
          (Units.map (Matrix.scalar (Fin 2) :
              u.adicCompletion F →+* Matrix (Fin 2) (Fin 2) (u.adicCompletion F)).toMonoidHom t *
            AutomorphicForm.unipotentGL2 y)) =
      (W k (2 * (WithZero.log (Valued.v y)).toNat) : ℂ) := by
  classical

  have hπ0 : ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ≠ 0 := hϖ0
  have hvπ : Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    valued_uniformiser F u hϖ
  haveI : Finite (u.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) := finite_quotient_span F u hϖ
  have hq := natCard_quotient_span_uniformiser F u hϖ

  have hzc : ∀ g : GL (Fin 2) (u.adicCompletion F), Commute z g := central_of_coe_eq_smul hz
  have hzPQ : z = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 := eq_diagPi_mul_localRepInf_of_coe ϖ hϖ0 hz
  have hscπ : sc (u.adicCompletion F) (Units.mk0 _ hϖ0) = z := sc_mk0_eq_of_coe ϖ hϖ0 hz
  have hPQ := commute_diagPi_localRepInf ϖ hϖ0 (K := u.adicCompletion F)

  have ht0 : (t : u.adicCompletion F) ≠ 0 := t.ne_zero
  have hvt0 : Valued.v (t : u.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).2 ht0
  set m : ℤ := WithZero.log (Valued.v (t : u.adicCompletion F)) with hm
  obtain ⟨e, he⟩ := exists_units_coe_eq_mul_zpow_log F u hϖ ht0

  have hk : 2 * (-(j : ℤ) - m) = (k : ℤ) := by
    have h1 : Valued.v (t : u.adicCompletion F) = WithZero.exp m := (WithZero.exp_log hvt0).symm
    have ht' : WithZero.exp m ^ 2 = WithZero.exp (-1 : ℤ) ^ (k + 2 * j) := by
      rw [← h1, ← hvπ]; exact ht
    rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul, nsmul_eq_mul] at ht'
    push_cast at ht'
    omega
  set s : ℤ := -(j : ℤ) - m with hs

  set eK : (u.adicCompletion F)ˣ := t * (Units.mk0 _ hϖ0) ^ m with heK
  have heK' : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) (e : u.adicCompletionIntegers F) =
      (eK : u.adicCompletion F) := by
    show ((e : u.adicCompletionIntegers F) : u.adicCompletion F) = _
    rw [he, heK, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rfl
  have hemem : sc (u.adicCompletion F) eK ∈
      integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F) :=
    sc_mem_integralSubgroup_of_eq heK'
  have hsct : sc (u.adicCompletion F) t = sc (u.adicCompletion F) eK * z ^ (-m) := by
    rw [← hscπ, ← map_zpow, ← map_mul, heK, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

  set y' : GL (Fin 2) (u.adicCompletion F) :=
    (z ^ j)⁻¹ * (sc (u.adicCompletion F) t * unipotentGL2 y) with hy'
  have hy'eq : y' = sc (u.adicCompletion F) eK * z ^ s * unipotentGL2 y := by
    rw [hy', hsct, ← zpow_natCast, ← zpow_neg, ← mul_assoc, ← mul_assoc,
      ((hzc (sc (u.adicCompletion F) eK)).zpow_left (-(j : ℤ))).eq, mul_assoc (sc (u.adicCompletion F) eK),
      ← zpow_add, hs, sub_eq_add_neg]

  have hcart := LocalGL2.unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow ϖ hϖ0
    (K := u.adicCompletion F)
  obtain ⟨a, b, hab, habs, hmem⟩ : ∃ a b : ℤ, a + b = (k : ℤ) ∧
      (a - b).natAbs = 2 * (WithZero.log (Valued.v y)).toNat ∧
      y' ∈ doubleCoset (integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F))
        (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ b) := by
    by_cases hy : Valued.v y ≤ 1
    ·
      have hlog : WithZero.log (Valued.v y) ≤ 0 := by
        by_cases hy0 : y = 0
        · simp [hy0]
        · rwa [WithZero.log_le_iff_le_exp ((Valuation.ne_zero_iff _).2 hy0), WithZero.exp_zero]
      have h1 : unipotentGL2 y ∈
          doubleCoset (integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F))
            (diagPi ϖ hϖ0 ^ (0 : ℤ) * localRepInf ϖ hϖ0 ^ (0 : ℤ)) :=
        hcart.1 ⟨y, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hy⟩
      have h2 := mul_zpow_mul_mem_doubleCoset
        (integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F)) hzc hPQ hzPQ hemem s 0 0 h1
      rw [add_zero] at h2
      refine ⟨s, s, by omega, by omega, ?_⟩
      rw [hy'eq]; exact h2
    ·
      push Not at hy
      have hy0 : y ≠ 0 := by rintro rfl; simp at hy
      have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
      have hlogpos : 0 < WithZero.log (Valued.v y) := by
        rwa [WithZero.lt_log_iff_exp_lt hvy0, WithZero.exp_zero]
      set r : ℕ := (WithZero.log (Valued.v y)).toNat with hr
      have hrz : (r : ℤ) = WithZero.log (Valued.v y) := Int.toNat_of_nonneg hlogpos.le
      obtain ⟨e', he'⟩ := exists_units_coe_eq_mul_zpow_log F u hϖ hy0
      have hyeq : y = algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) (e' : u.adicCompletionIntegers F) *
          (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ)⁻¹ ^ r := by
        show y = ((e' : u.adicCompletionIntegers F) : u.adicCompletion F) *
          ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F)⁻¹ ^ r
        rw [he', ← hrz, zpow_natCast, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero r hπ0), mul_one]
      have h1 := hcart.2 e' r
      rw [← hyeq] at h1
      have h2 := mul_zpow_mul_mem_doubleCoset
        (integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F)) hzc hPQ hzPQ hemem s (-(r : ℤ)) r h1
      refine ⟨s + -(r : ℤ), s + r, by omega, by omega, ?_⟩
      rw [hy'eq]; exact h2

  have hgen := LocalGL2.sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
    ϖ hϖ0 hϖ rT hrT W h00 h0s (fun k => by rw [hq]; exact hroot k) (fun k d => by rw [hq]; exact hstep k d)
    k a b y' hmem
  rw [if_pos hab, habs] at hgen
  rw [← hgen, Nat.cast_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_

  have hg : ((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (sc (u.adicCompletion F) t * unipotentGL2 y) =
      ((List.ofFn fun i => rT (ι i)).prod)⁻¹ * y' := by
    rw [mul_inv_rev, hy', ((hzc _).pow_left j).inv_inv.eq, mul_assoc]
  show (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
      (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (sc (u.adicCompletion F) t * unipotentGL2 y)) = _
  rw [hg, ← coe_integralSubgroup_eq_localIntegralSet]
  by_cases hU : ((List.ofFn fun i => rT (ι i)).prod)⁻¹ * y' ∈
      ((integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F) :
        Subgroup (GL (Fin 2) (u.adicCompletion F))) : Set (GL (Fin 2) (u.adicCompletion F)))
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, Nat.cast_one]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU, Nat.cast_zero]

end NumberFieldPlace

end P2mC0bLocDock

open NumberField IsDedekindDomain

theorem solution
    (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (ϖ : u.adicCompletionIntegers F) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (u.adicCompletion F))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (u.adicCompletion F))
    (hz : (z : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm u.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm u.asIdeal * W k (d + 2))
    (k j : ℕ) (t : (u.adicCompletion F)ˣ) (y : u.adicCompletion F)
    (ht : Valued.v (t : u.adicCompletion F) ^ 2 =
      Valued.v (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ) ^ (k + 2 * j)) :
    ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ *
          (Units.map (Matrix.scalar (Fin 2) :
              u.adicCompletion F →+* Matrix (Fin 2) (Fin 2) (u.adicCompletion F)).toMonoidHom t *
            AutomorphicForm.unipotentGL2 y)) =
      (W k (2 * (WithZero.log (Valued.v y)).toNat) : ℂ) :=
  P2mC0bLocDock.main F u ϖ hϖ hϖ0 n rT hrT z hz W h00 h0s hroot hstep k j t y ht

end S_LocalGL2_sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount
end P2MW
export P2MW.S_LocalGL2_sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount (solution)

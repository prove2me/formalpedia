-- Prove2me | solution 1 for HeckeCharacter.exists_forall_dvd_valued_mul_inv_eq_one_and_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c3aee7f1-e15b-5616-a2e0-2c19b6050457

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_exists_forall_dvd_valued_mul_inv_eq_one_and_le

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

namespace WAfinAux

variable (K : Type*) [Field K] [NumberField K]

theorem exists_valued_sub_lt (v : HeightOneSpectrum (𝓞 K)) (a w : v.adicCompletion K) (hw : w ≠ 0) :
    ∃ t : K, Valued.v (algebraMap K (v.adicCompletion K) t - a) < Valued.v w := by
  have hopen : IsOpen {z : v.adicCompletion K | Valued.v.restrict (z - a) < Valued.v.restrict w} :=
    (Valued.isOpen_ball (v.adicCompletion K) (Valued.v.restrict w)).preimage (continuous_sub_right a)
  obtain ⟨t, ht⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open hopen
    ⟨a, by
      simp only [Set.mem_setOf_eq, sub_self, Valuation.restrict_lt_iff, map_zero]
      exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hw)⟩
  exact ⟨t, (Valuation.restrict_lt_iff _).mp ht⟩

theorem exists_forall_valuation_sub_lt (S : Finset (HeightOneSpectrum (𝓞 K))) (t : HeightOneSpectrum (𝓞 K) → K)
    (γ : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ)) (hγ : ∀ v, γ v ≠ 0) :
    ∃ z : K, ∀ v ∈ S, v.valuation K (z - t v) < γ v := by
  classical

  choose p q hq hpq using fun v => IsFractionRing.div_surjective (A := 𝓞 K) (t v)
  set d : 𝓞 K := ∏ v ∈ S, q v with hd_def
  have hq0 : ∀ v, (q v : 𝓞 K) ≠ 0 := fun v => nonZeroDivisors.ne_zero (hq v)
  have hqK : ∀ v, ((q v : 𝓞 K) : K) ≠ 0 := fun v h => hq0 v (by exact_mod_cast h)
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hq0 v
  have hdK : (d : K) ≠ 0 := fun h => hd (by exact_mod_cast h)
  let e : HeightOneSpectrum (𝓞 K) → 𝓞 K := fun v => p v * ∏ w ∈ S.erase v, q w
  have he : ∀ v ∈ S, ((e v : 𝓞 K) : K) = (d : K) * t v := by
    intro v hv
    simp only [e, hd_def]
    rw [← Finset.mul_prod_erase S q hv, ← hpq v]
    have h1 := hqK v
    push_cast
    field_simp

  have hvd : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (d : K) ≠ 0 := fun v =>
    (Valuation.ne_zero_iff _).mpr hdK
  let N : HeightOneSpectrum (𝓞 K) → ℕ := fun v => Int.toNat (-(WithZero.log (γ v * v.valuation K (d : K)))) + 1
  have hN : ∀ v, WithZero.exp (-(N v : ℤ)) < γ v * v.valuation K (d : K) := by
    intro v
    have hne : γ v * v.valuation K (d : K) ≠ 0 := mul_ne_zero (hγ v) (hvd v)
    conv_rhs => rw [← WithZero.exp_log hne]
    rw [WithZero.exp_lt_exp]
    simp only [N]
    have := Int.self_le_toNat (-(WithZero.log (γ v * v.valuation K (d : K))))
    omega

  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) N
    (fun v _ => v.prime) (fun v _ w _ hvw => fun h => hvw (HeightOneSpectrum.ext h)) (fun v => e v.1)
  refine ⟨(y : K) / d, fun v hv => ?_⟩
  have hsub : (y : K) / d - t v = algebraMap (𝓞 K) K (y - e v) / d := by
    rw [eq_div_iff hdK, map_sub]
    change _ = (y : K) - (e v : K)
    rw [he v hv]
    field_simp
  rw [hsub, map_div₀, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 : v.intValuation (y - e v) ≤ WithZero.exp (-(N v : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ _).mpr (hy v hv)
  have h2 : v.intValuation (y - e v) < γ v * v.valuation K (d : K) := lt_of_le_of_lt h1 (hN v)
  rwa [div_lt_iff₀ (zero_lt_iff.mpr (hvd v))]

end WAfinAux

open WAfinAux in
theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α₀ : Kˣ, ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α₀)⁻¹ :
          (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
      Valued.v ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α₀)⁻¹ :
          (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) := by
  classical
  have h𝔣0 : 𝔣 ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  set S : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors h𝔣0).toFinset with hS

  let a : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v => ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
  have ha : ∀ v, Valued.v (a v) ≠ 0 := fun v => valued_ne_zero_of_unit K (projFin K u) v
  let n : HeightOneSpectrum (𝓞 K) → ℕ := fun v => (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors
  have hr : ∀ v, Valued.v (a v) * WithZero.exp (-(n v : ℤ)) ≠ 0 := fun v => mul_ne_zero (ha v) WithZero.exp_ne_zero

  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.valuation_exists_uniformizer K
  let w : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v => a v * algebraMap K (v.adicCompletion K) (π v ^ n v)
  have hwv : ∀ v, Valued.v (w v) = Valued.v (a v) * WithZero.exp (-(n v : ℤ)) := by
    intro v
    simp only [w, map_mul, map_pow]
    rw [show algebraMap K (v.adicCompletion K) (π v) = ((WithVal.equiv (v.valuation K)).symm (π v) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul, mul_one]
  have hw0 : ∀ v, w v ≠ 0 := fun v h => hr v (by rw [← hwv, h, map_zero])

  choose t ht' using fun v => exists_valued_sub_lt K v (a v) (w v) (hw0 v)
  have ht : ∀ v, Valued.v (algebraMap K (v.adicCompletion K) (t v) - a v) < Valued.v (a v) * WithZero.exp (-(n v : ℤ)) :=
    fun v => (hwv v) ▸ ht' v
  obtain ⟨z, hz⟩ := exists_forall_valuation_sub_lt K S t (fun v => Valued.v (a v) * WithZero.exp (-(n v : ℤ))) hr

  have hclose : ∀ v ∈ S, Valued.v (algebraMap K (v.adicCompletion K) z - a v) <
      Valued.v (a v) * WithZero.exp (-(n v : ℤ)) := by
    intro v hv
    have h1 := ht v
    have h2 : Valued.v (algebraMap K (v.adicCompletion K) (z - t v)) < Valued.v (a v) * WithZero.exp (-(n v : ℤ)) := by
      rw [show algebraMap K (v.adicCompletion K) (z - t v) = ((WithVal.equiv (v.valuation K)).symm (z - t v) : v.adicCompletion K)
        from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hz v hv
    rw [map_sub] at h2
    have : algebraMap K (v.adicCompletion K) z - a v =
        (algebraMap K (v.adicCompletion K) z - algebraMap K (v.adicCompletion K) (t v)) +
          (algebraMap K (v.adicCompletion K) (t v) - a v) := by ring
    rw [this]
    exact Valuation.map_add_lt _ h2 h1
  have hle1 : ∀ v, Valued.v (a v) * WithZero.exp (-(n v : ℤ)) ≤ Valued.v (a v) := fun v => by
    conv_rhs => rw [← mul_one (Valued.v (a v))]
    exact mul_le_mul_right (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) _

  by_cases hz0 : z = 0
  · refine ⟨1, fun v hv => ?_⟩
    have hvS : v ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hv
    have h := lt_of_lt_of_le (hclose v hvS) (hle1 v)
    rw [hz0, map_zero, zero_sub, Valuation.map_neg] at h
    exact absurd h (lt_irrefl _)
  refine ⟨Units.mk0 z hz0, fun v hv => ?_⟩
  have hvS : v ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hv
  set c : v.adicCompletion K := algebraMap K (v.adicCompletion K) z with hc_def
  have hca : Valued.v c = Valued.v (a v) := Valuation.map_eq_of_sub_lt _ (lt_of_lt_of_le (hclose v hvS) (hle1 v))
  have hc0 : c ≠ 0 := fun h => ha v (by rw [← hca, h, map_zero])

  have hcomp : ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 z hz0))⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = a v * c⁻¹ := by
    rw [← map_inv, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, Units.val_mk0]
    change a v * algebraMap K (v.adicCompletion K) z⁻¹ = a v * c⁻¹
    rw [map_inv₀]
  rw [hcomp]
  constructor
  · rw [map_mul, map_inv₀, hca, mul_inv_cancel₀ (ha v)]
  · have : a v * c⁻¹ - 1 = (a v - c) * c⁻¹ := by field_simp
    rw [this, map_mul, map_inv₀, hca, Valuation.map_sub_swap]
    have h := hclose v hvS
    rw [mul_comm (Valued.v (a v))] at h
    exact le_of_lt ((mul_inv_lt_iff₀ (zero_lt_iff.mpr (ha v))).mpr h)

end S_HeckeCharacter_exists_forall_dvd_valued_mul_inv_eq_one_and_le
end P2MW
export P2MW.S_HeckeCharacter_exists_forall_dvd_valued_mul_inv_eq_one_and_le (solution)

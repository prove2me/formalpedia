-- Prove2me | solution 1 for OAI.DimensionTen.root_action_full_symmetric_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:42:04.786201+00:00
-- url     : https://prove2.me/submissions/62fc4388-6b2b-48e2-ade3-428ffc684b8e

import Mathlib
import Definitions.Def_OAIQ057D011
import Theorems.Thm_OAI_DimensionTen_fixed_mod131_s2
import Theorems.Thm_OAI_DimensionTen_fixed_mod139_s2
import Theorems.Thm_OAI_DimensionTen_pow_mod139_s2

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_RootReduction
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma map_eq_prod_rootInteger {K : Type*} [Field K] [CharZero K]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) :
    f.map (algebraMap ℤ (𝓞 K)) = ∏ x : f.rootSet K, (X - C (rootInteger f hm x)) := by
  classical
  apply Polynomial.map_injective _ (RingOfIntegers.coe_injective (K := K))
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ (𝓞 K) K]
  exact map_eq_prod_rootSet f hm hs hsp

lemma reduction_factorization {K k : Type*} [Field K] [CharZero K] [Field k]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) (ρ : 𝓞 K →+* k) :
    f.map (Int.castRingHom k) = ∏ x : f.rootSet K, (X - C (ρ (rootInteger f hm x))) := by
  classical
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_map, RingHom.eq_intCast'] using
      congrArg (Polynomial.map ρ) (map_eq_prod_rootInteger f hm hs hsp)

lemma reduction_injective {K k : Type*} [Field K] [CharZero K] [Field k]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) (ρ : 𝓞 K →+* k)
    (hred : (f.map (Int.castRingHom k)).Separable) :
    Function.Injective (fun x : f.rootSet K => ρ (rootInteger f hm x)) := by
  rw [reduction_factorization f hm hs hsp ρ] at hred
  exact hred.injective_of_prod_X_sub_C

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_FrobeniusRoots
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen




theorem numberField_frobenius (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (p : ℕ) [Fact p.Prime] :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : Gal(K/ℚ), ∀ x : 𝓞 K,
        Ideal.Quotient.mk P (((galRestrict ℤ ℚ K (𝓞 K)) σ) x) =
          (Ideal.Quotient.mk P x) ^ p := by
  let := IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)
  let := Algebra.isInvariant_of_isGalois ℤ ℚ K (𝓞 K)
  obtain ⟨P, hP, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  let := hP
  let := hOver
  let : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.IsMaximal.ne_bot_of_isIntegral_int P)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  refine ⟨P, hP, hOver, σ, ?_⟩
  intro x
  have h := hσ.mk_apply x
  rw [← Ideal.over_def P (Ideal.span {(p : ℤ)}), Int.card_ideal_quot] at h
  exact h

end DimensionTen

end
end

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma quotient_charP {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : CharP (𝓞 K ⧸ P) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  have hp : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P :=
    (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.subset_span (by simp))
  simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hp)

lemma rootInteger_gal {K : Type*} [Field K] [NumberField K]
    (f : ℤ[X]) (hm : f.Monic) (σ : Gal(K/ℚ)) (x : f.rootSet K) :
    rootInteger f hm (σ • x) = (galRestrict ℤ ℚ K (𝓞 K) σ) (rootInteger f hm x) := by
  apply RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply]
  rfl

lemma root_reduction_frobenius {K : Type*} [Field K] [NumberField K]
    (f : ℤ[X]) (hm : f.Monic) (p : ℕ) (P : Ideal (𝓞 K)) (σ : Gal(K/ℚ))
    (hσ : ∀ x : 𝓞 K, Ideal.Quotient.mk P ((galRestrict ℤ ℚ K (𝓞 K) σ) x) =
        (Ideal.Quotient.mk P x) ^ p) (x : f.rootSet K) :
    Ideal.Quotient.mk P (rootInteger f hm (σ • x)) =
        (Ideal.Quotient.mk P (rootInteger f hm x)) ^ p := by
  rw [rootInteger_gal, hσ]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Result
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

theorem separable_bezout_integer {R : Type*} [CommRing R] (z : R) :
    da z * f z + db z * df z = 1 + (131 : R) * separable_bezout_t z := by
  simp only [da, db, df, f, separable_bezout_t]
  
  ring

theorem separable_bezout {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    da z * f z + db z * df z = 1 := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using separable_bezout_integer z

end DimensionTen.Mod131

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod131

lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by
  simp only [f, map_add, map_mul, map_ofNat, map_one]

lemma derivative_identity {R : Type*} [CommRing R] :
    Polynomial.derivative (f (X : R[X])) = df X + (131 : R[X]) * derivative_extra X := by
  simp only [f, df, derivative_extra, derivative_add, derivative_mul, derivative_X,
    derivative_ofNat, derivative_one]
  ring

lemma separable_f {k : Type*} [Field k] [CharP k 131] :
    (f (X : k[X])).Separable := by
  change IsCoprime _ _
  have h : (131 : k[X]) = 0 := CharP.cast_eq_zero _ 131
  rw [derivative_identity, h, zero_mul, add_zero]
  exact ⟨da X, db X, separable_bezout _⟩

end DimensionTen.Mod131

end
end

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Result
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem separable_bezout_integer {R : Type*} [CommRing R] (z : R) :
    da z * f z + db z * df z = 1 + (139 : R) * separable_bezout_t z := by
  simp only [da, db, df, f, separable_bezout_t]
  
  ring

theorem separable_bezout {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    da z * f z + db z * df z = 1 := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using separable_bezout_integer z

end DimensionTen.Mod139

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod139

lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by
  simp only [f, map_add, map_mul, map_ofNat, map_one, map_zero]

lemma derivative_identity {R : Type*} [CommRing R] :
    Polynomial.derivative (f (X : R[X])) = df X + (139 : R[X]) * derivative_extra X := by
  simp only [f, df, derivative_extra, derivative_add, derivative_mul, derivative_X,
    derivative_ofNat, derivative_one, derivative_zero]
  ring

lemma separable_f {k : Type*} [Field k] [CharP k 139] :
    (f (X : k[X])).Separable := by
  change IsCoprime _ _
  have h : (139 : k[X]) = 0 := CharP.cast_eq_zero _ 139
  rw [derivative_identity, h, zero_mul, add_zero]
  exact ⟨da X, db X, separable_bezout _⟩

end DimensionTen.Mod139

end
end

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_RootPermutation
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen


lemma swap_of_card_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 20) (σ : Equiv.Perm ι)
    (hfix : Fintype.card {i : ι // σ i = i} = 18) : σ.IsSwap := by
  have hc : σ.support.card = 2 := by
    have h := Fintype.card_subtype_compl (fun i => σ i = i)
    rw [hcard, hfix] at h
    simpa only [Fintype.card_subtype, Equiv.Perm.support] using h
  exact Equiv.Perm.card_support_eq_two.mp hc

lemma cycle_of_pow_eq_one_card_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 20) (σ : Equiv.Perm ι)
    (hpow : σ ^ 19 = 1) (hfix : Fintype.card {i : ι // σ i = i} = 1) :
    σ.IsCycle ∧ σ.support.card = 19 := by
  have hc : σ.support.card = 19 := by
    have h := Fintype.card_subtype_compl (fun i => σ i = i)
    rw [hcard, hfix] at h
    simpa only [Fintype.card_subtype, Equiv.Perm.support] using h
  have hne : σ ≠ 1 := by intro h; simp [h] at hc
  have hord : orderOf σ = 19 := by
    have hd := orderOf_dvd_of_pow_eq_one hpow
    have hp : Nat.Prime 19 := by decide
    exact (hp.eq_one_or_self_of_dvd _ hd).resolve_left (by simpa using hne)
  exact ⟨Equiv.Perm.isCycle_of_prime_order (by rw [hord]; decide) (by rw [hc, hord]; omega), hc⟩

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ModularPermutations
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Equiv Equiv.Perm MulAction
namespace DimensionTen


theorem full_symmetric_of_nineteen_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (H : Subgroup (Perm α)) (hc : Fintype.card α = 20)
    [IsPretransitive H α]
    (σ : Perm α) (hσ : σ ∈ H) (hcycle : σ.IsCycle) (hs : σ.support.card = 19)
    (τ : Perm α) (hτ : τ ∈ H) (hswap : τ.IsSwap) : H = ⊤ := by
  classical
  have ht : (σ.supportᶜ).card = 1 := by rw [Finset.card_compl, hs, hc]
  obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp ht
  have hm (a : α) : σ a ≠ a ↔ a ≠ a₀ := by
    have h := congrArg (fun s : Finset α => a ∈ s) ha₀
    simpa only [Finset.mem_compl, mem_support, not_not, Finset.mem_singleton] using not_congr (iff_of_eq h)
  have hfix : σ a₀ = a₀ := not_ne_iff.mp ((hm a₀).not.mpr (by simp))
  have htwo : IsMultiplyPretransitive H α 2 := by
    rw [is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg⟩ := exists_smul_eq (M := H) a a₀
    obtain ⟨h, hh⟩ := exists_smul_eq (M := H) c a₀
    have hgb : σ (g • b) ≠ g • b := (hm _).mpr (by
      intro hb; exact hab ((MulAction.injective g) (hg.trans hb.symm)))
    have hhd : σ (h • d) ≠ h • d := (hm _).mpr (by
      intro hd; exact hcd ((MulAction.injective h) (hh.trans hd.symm)))
    obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hgb hhd
    refine ⟨h⁻¹ * (⟨σ, hσ⟩ : H) ^ n * g, ?_, ?_⟩
    · simp only [mul_smul, hg]
      have hhfix : ((⟨σ, hσ⟩ : H) ^ n) • a₀ = a₀ := by
        exact pow_apply_eq_self_of_apply_eq_self hfix n
      rw [hhfix, ← hh, inv_smul_smul]
    · simp only [mul_smul]
      change h⁻¹ • ((σ ^ n) (g • b)) = d
      rw [hn, inv_smul_smul]
  exact subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (isPreprimitive_of_is_two_pretransitive htwo) τ hswap hτ

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_GaloisCertificate
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma reduction_eq_131 {k : Type*} [Field k] [CharP k 131]
    (f : ℤ[X]) (h : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X) :
    f.map (Int.castRingHom k) = Mod131.f X := by
  let φ := ZMod.castHom (dvd_refl 131) k
  have hmap : map φ (Mod131.f X) = Mod131.f X := by
    change mapRingHom φ (Mod131.f X) = _
    exact (Mod131.map_f (mapRingHom φ) X).trans (congrArg Mod131.f (map_X φ))
  have := congrArg (map φ) h
  rw [map_map] at this
  have he : φ.comp (Int.castRingHom (ZMod _)) = Int.castRingHom k := RingHom.eq_intCast' _
  rw [he] at this
  exact this.trans hmap

lemma reduction_eq_139 {k : Type*} [Field k] [CharP k 139]
    (f : ℤ[X]) (h : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    f.map (Int.castRingHom k) = Mod139.f X := by
  let φ := ZMod.castHom (dvd_refl 139) k
  have hmap : map φ (Mod139.f X) = Mod139.f X := by
    change mapRingHom φ (Mod139.f X) = _
    exact (Mod139.map_f (mapRingHom φ) X).trans (congrArg Mod139.f (map_X φ))
  have := congrArg (map φ) h
  rw [map_map] at this
  have he : φ.comp (Int.castRingHom (ZMod _)) = Int.castRingHom k := RingHom.eq_intCast' _
  rw [he] at this
  exact this.trans hmap

lemma irr_rational_of_mod41 (f : ℤ[X]) (hm : f.Monic)
    (h : f.map (Int.castRingHom (ZMod 41)) = Mod41.f X) :
    Irreducible (f.map (algebraMap ℤ ℚ)) := by
  apply hm.irreducible_iff_irreducible_map_fraction_map.mp
  apply Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 41)) f hm
  rw [h]
  exact Mod41.irreducible_f

section Roots
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [DecidableEq K]
variable (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hp : (f.map (algebraMap ℤ K)).Splits)
    (hc : Fintype.card (f.rootSet K) = 20)

include hm hs hp hc in
lemma exists_swap_of_mod131
    (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X) :
    ∃ σ : Gal(K/ℚ), (MulAction.toPerm (σ ^ 17) : Equiv.Perm (f.rootSet K)).IsSwap := by
  classical
  let : Fact (Nat.Prime 131) := ⟨by decide⟩
  obtain ⟨P, hP, hOver, σ, hσ⟩ := numberField_frobenius K 131
  let := hP
  let := hOver
  let k := 𝓞 K ⧸ P
  let : Field k := Ideal.Quotient.field P
  let : CharP k 131 := quotient_charP 131 P
  let ρ := Ideal.Quotient.mk P
  let r : f.rootSet K → k := fun x => ρ (rootInteger f hm x)
  let π : Equiv.Perm (f.rootSet K) := MulAction.toPerm σ
  have hred := reduction_eq_131 (k := k) f h131
  have hsep : (f.map (Int.castRingHom k)).Separable := by
    rw [hred]; exact Mod131.separable_f
  have hinj : Function.Injective r := reduction_injective f hm hs hp ρ hsep
  have hfact : f.map (Int.castRingHom k) = ∏ i, (X - C (r i)) :=
    reduction_factorization f hm hs hp ρ
  have h18 : Fintype.card {i : f.rootSet K // (π ^ 17) i = i} = 18 :=
    fixed_mod131_s2 r hinj π (hred ▸ hfact) (fun i => root_reduction_frobenius f hm 131 P σ hσ i)
  refine ⟨σ, ?_⟩
  have ht := swap_of_card_fixed hc (π ^ 17) h18
  simpa only [π, ← MulAction.toPermHom_apply, ← map_pow] using ht

include hm hs hp hc in
lemma exists_nineteen_cycle_of_mod139
    (h139 : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    ∃ σ : Gal(K/ℚ), (MulAction.toPerm σ : Equiv.Perm (f.rootSet K)).IsCycle ∧
      (MulAction.toPerm σ : Equiv.Perm (f.rootSet K)).support.card = 19 := by
  classical
  let : Fact (Nat.Prime 139) := ⟨by decide⟩
  obtain ⟨P, hP, hOver, σ, hσ⟩ := numberField_frobenius K 139
  let := hP
  let := hOver
  let k := 𝓞 K ⧸ P
  let : Field k := Ideal.Quotient.field P
  let : CharP k 139 := quotient_charP 139 P
  let ρ := Ideal.Quotient.mk P
  let r : f.rootSet K → k := fun x => ρ (rootInteger f hm x)
  let π : Equiv.Perm (f.rootSet K) := MulAction.toPerm σ
  have hred := reduction_eq_139 (k := k) f h139
  have hsep : (f.map (Int.castRingHom k)).Separable := by
    rw [hred]; exact Mod139.separable_f
  have hinj : Function.Injective r := reduction_injective f hm hs hp ρ hsep
  have hfact : Mod139.f X = ∏ i, (X - C (r i)) :=
    hred ▸ reduction_factorization f hm hs hp ρ
  have hfrob (i : f.rootSet K) : r (π i) = r i ^ 139 :=
    root_reduction_frobenius f hm 139 P σ hσ i
  have h1 : Fintype.card {i : f.rootSet K // π i = i} = 1 := by
    simpa only [pow_one] using fixed_mod139_s2 r hinj π hfact hfrob
  exact ⟨σ, cycle_of_pow_eq_one_card_fixed hc π (pow_mod139_s2 r hinj π hfact hfrob) h1⟩

include hm in
omit [IsGalois ℚ K] [DecidableEq K] in
lemma root_minpoly (hirr : Irreducible (f.map (algebraMap ℤ ℚ))) (x : f.rootSet K) :
    minpoly ℚ (x : K) = f.map (algebraMap ℤ ℚ) := by
  have hx : (aeval (x : K)) (f.map (algebraMap ℤ ℚ)) = 0 := by
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq ℤ ℚ K]
    exact (mem_rootSet.mp x.property).2
  have he := minpoly.eq_of_irreducible hirr hx
  simpa only [(hm.map (algebraMap ℤ ℚ)).leadingCoeff, inv_one, C_1, mul_one] using he.symm

include hm in
omit [DecidableEq K] in
lemma root_action_pretransitive (hirr : Irreducible (f.map (algebraMap ℤ ℚ))) :
    MulAction.IsPretransitive Gal(K/ℚ) (f.rootSet K) := by
  constructor
  intro x y
  have hh : minpoly ℚ (y : K) = minpoly ℚ (x : K) :=
    (root_minpoly f hm hirr y).trans (root_minpoly f hm hirr x).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit K).mp hh
  exact ⟨σ, Subtype.ext hσ⟩

include hm hs hp hc in
lemma root_action_full_symmetric_s2_oai
    (h41 : f.map (Int.castRingHom (ZMod 41)) = Mod41.f X)
    (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X)
    (h139 : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    Function.Surjective (MulAction.toPermHom Gal(K/ℚ) (f.rootSet K)) := by
  classical
  let φ := MulAction.toPermHom Gal(K/ℚ) (f.rootSet K)
  let H := φ.range
  let : MulAction.IsPretransitive Gal(K/ℚ) (f.rootSet K) :=
    root_action_pretransitive f hm (irr_rational_of_mod41 f hm h41)
  let : MulAction.IsPretransitive H (f.rootSet K) := by
    constructor
    intro a b
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (M := Gal(K/ℚ)) a b
    exact ⟨⟨φ σ, ⟨σ, rfl⟩⟩, hσ⟩
  obtain ⟨σ, hσ, hcσ⟩ := exists_nineteen_cycle_of_mod139 f hm hs hp hc h139
  obtain ⟨τ, hτ⟩ := exists_swap_of_mod131 f hm hs hp hc h131
  have htop : H = ⊤ := full_symmetric_of_nineteen_cycle H hc (φ σ) ⟨σ, rfl⟩ hσ hcσ
    (φ (τ ^ 17)) ⟨τ ^ 17, rfl⟩ hτ
  exact MonoidHom.range_eq_top.mp htop

end Roots
end DimensionTen

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.root_action_full_symmetric_s2_oai.{u_1} := @OAI.DimensionTen.root_action_full_symmetric_s2_oai.{u_1}

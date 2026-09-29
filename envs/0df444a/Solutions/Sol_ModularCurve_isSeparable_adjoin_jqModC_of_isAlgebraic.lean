-- Prove2me | solution 1 for ModularCurve.isSeparable_adjoin_jqModC_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1e395a3c-52e6-5690-a9e4-8ad5655837c6

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic

set_option autoImplicit false

open ModularCurve Polynomial IntermediateField

namespace W5Aux1
namespace SepJ

section Laurent

variable {R : Type*} [CommRing R]

theorem coeffMap_ofPowerSeries_aux {S : Type*} [CommRing S] (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R u) = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f u) := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  · lift k to ℕ using hk with k
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

variable (p : ℕ)

theorem qExpand_ofPowerSeries_aux [NeZero p] (u : PowerSeries R) :
    qExpand R p (HahnSeries.ofPowerSeries ℤ R u)
      = HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand p (NeZero.ne p) u) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  ext k
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · have hpm : (p : ℤ) * m < 0 := mul_neg_of_pos_of_neg hp0 hm
      rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ hpm]
    · lift m to ℕ using hm with m
      have hcast : ((p : ℤ) * (m : ℤ)) = ((p * m : ℕ) : ℤ) := by push_cast; ring
      rw [HahnSeries.ofPowerSeries_apply_coeff, hcast, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hpk]
    rcases lt_or_ge k 0 with hk | hk
    · exact (ofPowerSeries_coeff_of_neg _ hk).symm
    · lift k to ℕ using hk with k
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_of_not_dvd p (NeZero.ne p) u
          (fun ⟨m, hm⟩ => hpk ⟨m, by exact_mod_cast hm⟩)]

variable [Fact p.Prime] [CharP R p]

theorem pow_char_single_one_aux (n : ℤ) :
    (HahnSeries.single n (1 : R)) ^ p
      = coeffMap (frobenius R p) (qExpand R p (HahnSeries.single n (1 : R))) := by
  rw [HahnSeries.single_pow, one_pow, show (p • n : ℤ) = (p : ℤ) * n from nsmul_eq_mul p n,
    qExpand_single, coeffMap_single, show frobenius R p 1 = 1 from map_one _]

theorem pow_char_ofPowerSeries_aux (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u) ^ p
      = coeffMap (frobenius R p) (qExpand R p (HahnSeries.ofPowerSeries ℤ R u)) := by
  haveI : ExpChar R p := ExpChar.prime (Fact.out : p.Prime)
  rw [qExpand_ofPowerSeries_aux p u, coeffMap_ofPowerSeries_aux, ← map_pow]
  congr 1
  exact (MvPowerSeries.map_frobenius_expand p (NeZero.ne p) (f := u)).symm

theorem pow_char_eq_aux (s : LaurentSeries R) :
    s ^ p = coeffMap (frobenius R p) (qExpand R p s) := by
  conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  conv_rhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  rw [mul_pow, map_mul, map_mul, pow_char_single_one_aux p s.order]
  congr 1
  exact pow_char_ofPowerSeries_aux p s.powerSeriesPart

theorem coeff_pow_char_of_not_dvd (s : LaurentSeries R) {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) :
    (s ^ p).coeff k = 0 := by
  rw [pow_char_eq_aux p s, coeffMap_coeff, qExpand_coeff_of_not_dvd p _ hk, map_zero]

end Laurent

section Main

variable (K : Type*) [Field K]

theorem jqModC_not_mem_of_forall_pow (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : Subfield (LaurentSeries K)) (hM : ∀ s ∈ M, ∃ t : LaurentSeries K, t ^ p = s) :
    jqModC K ∉ M := by
  haveI : CharP (LaurentSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective p
  have hpr : p.Prime := Fact.out
  intro h
  obtain ⟨t, ht⟩ := hM _ h
  have hp1 : ¬ ((p : ℤ) ∣ (-1 : ℤ)) := by
    intro hd
    have h1 : (p : ℤ) ∣ 1 := (dvd_neg).mp hd
    have h2 : p ∣ 1 := by exact_mod_cast h1
    exact hpr.one_lt.ne' (Nat.dvd_one.mp h2)
  have hcoeff := coeff_pow_char_of_not_dvd p t hp1
  rw [ht, coeff_jqModC_neg_one] at hcoeff
  exact one_ne_zero hcoeff

theorem mem_adjoin_pair_pow (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : LaurentSeries K) (hx : IsIntegral K⟮jqModC K⟯ x) :
    x ∈ K⟮jqModC K, x ^ p⟯ := by
  have hpr : p.Prime := Fact.out
  haveI : ExpChar K p := ExpChar.prime hpr
  haveI : CharP (LaurentSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective p
  haveI : ExpChar (LaurentSeries K) p := ExpChar.prime hpr
  set j : LaurentSeries K := jqModC K with hjdef
  set φ : LaurentSeries K →+* LaurentSeries K := frobenius (LaurentSeries K) p with hφ
  have hφj : φ j = j ^ p := rfl
  have hφx : φ x = x ^ p := rfl

  have hconst : φ '' Set.range (algebraMap K (LaurentSeries K))
      = Set.range (algebraMap K (LaurentSeries K)) := by
    ext s
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r ^ p, by rw [map_pow]; rfl⟩
    · rintro ⟨r, rfl⟩
      obtain ⟨r', rfl⟩ := surjective_frobenius K p r
      refine ⟨algebraMap K _ r', ⟨r', rfl⟩, ?_⟩
      show algebraMap K (LaurentSeries K) r' ^ p = _
      rw [← map_pow]
      rfl

  have hmapE : (K⟮j⟯).toSubfield.map φ = (K⟮j ^ p⟯).toSubfield := by
    rw [adjoin_toSubfield, adjoin_toSubfield, RingHom.map_field_closure, Set.image_union, hconst,
      Set.image_singleton, hφj]
  have hmapA : (K⟮j, x⟯).toSubfield.map φ = (K⟮j ^ p, x ^ p⟯).toSubfield := by
    rw [adjoin_toSubfield, adjoin_toSubfield, RingHom.map_field_closure, Set.image_union, hconst,
      Set.image_pair, hφj, hφx]

  have hjE : j ∈ K⟮j⟯ := mem_adjoin_simple_self K j
  have hE'E : K⟮j ^ p⟯ ≤ K⟮j⟯ := adjoin_simple_le_iff.mpr (pow_mem hjE p)
  have hjA : j ∈ K⟮j, x⟯ := subset_adjoin K _ (Set.mem_insert j {x})
  have hxA : x ∈ K⟮j, x⟯ := subset_adjoin K _ (Set.mem_insert_of_mem j rfl)
  have hEA : K⟮j⟯ ≤ K⟮j, x⟯ := adjoin_simple_le_iff.mpr hjA
  have hBA : K⟮j ^ p, x ^ p⟯ ≤ K⟮j, x⟯ := adjoin_le_iff.mpr
    (Set.insert_subset_iff.mpr ⟨pow_mem hjA p, Set.singleton_subset_iff.mpr (pow_mem hxA p)⟩)
  have hjA' : j ∈ K⟮j, x ^ p⟯ := subset_adjoin K _ (Set.mem_insert j _)
  have hxpA' : x ^ p ∈ K⟮j, x ^ p⟯ := subset_adjoin K _ (Set.mem_insert_of_mem j rfl)
  have hBA' : K⟮j ^ p, x ^ p⟯ ≤ K⟮j, x ^ p⟯ := adjoin_le_iff.mpr
    (Set.insert_subset_iff.mpr ⟨pow_mem hjA' p, Set.singleton_subset_iff.mpr hxpA'⟩)
  have hA'A : K⟮j, x ^ p⟯ ≤ K⟮j, x⟯ := adjoin_le_iff.mpr
    (Set.insert_subset_iff.mpr ⟨hjA, Set.singleton_subset_iff.mpr (pow_mem hxA p)⟩)
  have hE'B : K⟮j ^ p⟯ ≤ K⟮j ^ p, x ^ p⟯ :=
    adjoin_simple_le_iff.mpr (subset_adjoin K _ (Set.mem_insert _ _))

  have hpow : ∀ (M : Subfield (LaurentSeries K)), ∀ s ∈ M.map φ, ∃ t : LaurentSeries K, t ^ p = s :=
    fun M s hs => by
      obtain ⟨t, -, rfl⟩ := Subfield.mem_map.mp hs
      exact ⟨t, rfl⟩
  have hjE' : j ∉ K⟮j ^ p⟯ := fun h =>
    jqModC_not_mem_of_forall_pow K p ((K⟮j⟯).toSubfield.map φ) (hpow _) (by rw [hmapE]; exact h)
  have hjB : j ∉ K⟮j ^ p, x ^ p⟯ := fun h =>
    jqModC_not_mem_of_forall_pow K p ((K⟮j, x⟯).toSubfield.map φ) (hpow _) (by rw [hmapA]; exact h)

  have hext : extendScalars hEA = (↥K⟮j⟯)⟮x⟯ := restrictScalars_injective K
    (show K⟮j, x⟯ = ((↥K⟮j⟯)⟮x⟯).restrictScalars K from (adjoin_simple_adjoin_simple K j x).symm)
  have hn : IntermediateField.relfinrank K⟮j⟯ K⟮j, x⟯ = (minpoly K⟮j⟯ x).natDegree := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hEA, (equivOfEq hext).toLinearEquiv.finrank_eq,
      adjoin.finrank hx]
  have hn0 : IntermediateField.relfinrank K⟮j⟯ K⟮j, x⟯ ≠ 0 := by
    rw [hn]; exact (minpoly.natDegree_pos hx).ne'

  have hjpE' : j ^ p ∈ K⟮j ^ p⟯ := mem_adjoin_simple_self K (j ^ p)
  have hirr : Irreducible (X ^ p - C (⟨j ^ p, hjpE'⟩ : K⟮j ^ p⟯)) := by
    rw [X_pow_sub_C_irreducible_iff_of_prime hpr]
    intro b hb
    apply hjE'
    have hb' : ((b : LaurentSeries K)) ^ p = j ^ p := by
      have := congrArg (fun e : K⟮j ^ p⟯ => (e : LaurentSeries K)) hb
      simpa using this
    have hbj : (b : LaurentSeries K) = j := frobenius_inj (LaurentSeries K) p hb'
    have hb2 : (b : LaurentSeries K) ∈ K⟮j ^ p⟯ := b.2
    rw [hbj] at hb2
    exact hb2
  have haev : aeval j (X ^ p - C (⟨j ^ p, hjpE'⟩ : K⟮j ^ p⟯)) = 0 := by
    rw [map_sub, aeval_X_pow, aeval_C]
    exact sub_self _
  have hjint : IsIntegral K⟮j ^ p⟯ j := ⟨_, monic_X_pow_sub_C _ hpr.ne_zero, haev⟩
  have hminj : minpoly K⟮j ^ p⟯ j = X ^ p - C (⟨j ^ p, hjpE'⟩ : K⟮j ^ p⟯) :=
    (minpoly.eq_of_irreducible_of_monic hirr haev (monic_X_pow_sub_C _ hpr.ne_zero)).symm
  have hEE : K⟮j⟯ = K⟮j ^ p, j⟯ := by
    refine le_antisymm ?_ ?_
    · exact adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
    · exact adjoin_le_iff.mpr
        (Set.insert_subset_iff.mpr ⟨pow_mem hjE p, Set.singleton_subset_iff.mpr hjE⟩)
  have hextE : extendScalars hE'E = (↥K⟮j ^ p⟯)⟮j⟯ := restrictScalars_injective K
    (show K⟮j⟯ = ((↥K⟮j ^ p⟯)⟮j⟯).restrictScalars K from
      hEE.trans (adjoin_simple_adjoin_simple K (j ^ p) j).symm)
  have hpE : IntermediateField.relfinrank K⟮j ^ p⟯ K⟮j⟯ = p := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hE'E, (equivOfEq hextE).toLinearEquiv.finrank_eq,
      adjoin.finrank hjint, hminj, natDegree_X_pow_sub_C]

  have htrans : IntermediateField.relfinrank K⟮j ^ p⟯ K⟮j ^ p, x ^ p⟯
      = IntermediateField.relfinrank K⟮j⟯ K⟮j, x⟯ := by
    show Subfield.relfinrank (K⟮j ^ p⟯).toSubfield (K⟮j ^ p, x ^ p⟯).toSubfield
      = Subfield.relfinrank (K⟮j⟯).toSubfield (K⟮j, x⟯).toSubfield
    rw [← hmapE, ← hmapA, Subfield.relfinrank_map_map]

  have ht1 := IntermediateField.relfinrank_mul_relfinrank hE'E hEA
  have ht2 := IntermediateField.relfinrank_mul_relfinrank hE'B hBA
  rw [hpE] at ht1
  rw [htrans] at ht2
  have hs : IntermediateField.relfinrank K⟮j ^ p, x ^ p⟯ K⟮j, x⟯ = p := by
    have h := ht2.trans ht1.symm
    rw [mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn0) h
  have ht3 := IntermediateField.relfinrank_mul_relfinrank hBA' hA'A
  rw [hs] at ht3
  have hne1 : IntermediateField.relfinrank K⟮j ^ p, x ^ p⟯ K⟮j, x ^ p⟯ ≠ 1 := by
    rw [Ne, IntermediateField.relfinrank_eq_one_iff]
    exact fun h => hjB (h hjA')
  have hA'A1 : IntermediateField.relfinrank K⟮j, x ^ p⟯ K⟮j, x⟯ = 1 := by
    rcases hpr.eq_one_or_self_of_dvd _ (Dvd.intro _ ht3) with h | h
    · exact absurd h hne1
    · rw [h] at ht3
      exact (Nat.mul_right_inj hpr.ne_zero).mp (ht3.trans (mul_one p).symm)
  exact (IntermediateField.relfinrank_eq_one_iff.mp hA'A1) hxA

end Main

theorem isSeparable_of_mem_adjoin_pow {F L : Type*} [Field F] [Field L] [Algebra F L] (p : ℕ)
    [Fact p.Prime] [CharP F p] {a : L} (ha : IsIntegral F a) (hmem : a ∈ F⟮a ^ p⟯) :
    IsSeparable F a := by
  have hpr : p.Prime := Fact.out
  rcases separable_or p (minpoly.irreducible ha) with h | ⟨-, g, hg, hge⟩
  · exact h
  · exfalso
    have hap : IsIntegral F (a ^ p) := ha.pow p
    have hg0 : aeval (a ^ p) g = 0 := by rw [← expand_aeval p g a, hge, minpoly.aeval]
    have h1 : Module.finrank F F⟮a ^ p⟯ ≤ g.natDegree := by
      rw [adjoin.finrank hap]
      exact natDegree_le_of_dvd (minpoly.dvd F (a ^ p) hg0) hg.ne_zero
    haveI : FiniteDimensional F F⟮a ^ p⟯ := adjoin.finiteDimensional hap
    have hle : F⟮a⟯ ≤ F⟮a ^ p⟯ := adjoin_simple_le_iff.mpr hmem
    have h2 : Module.finrank F F⟮a⟯ ≤ Module.finrank F F⟮a ^ p⟯ :=
      LinearMap.finrank_le_finrank_of_injective (f := (inclusion hle).toLinearMap)
        (inclusion_injective hle)
    rw [adjoin.finrank ha, ← hge, natDegree_expand] at h2
    have hgpos : 0 < g.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hg)
    have h3 : g.natDegree * p ≤ g.natDegree := h2.trans h1
    nlinarith [hpr.two_le]

end W5Aux1.SepJ

open W5Aux1.SepJ in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (K : Type*) [Field K] [PerfectField K] (F : IntermediateField K (LaurentSeries K))
    (hj : jqModC K ∈ F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({⟨jqModC K, hj⟩} : Set F)) F] :
    Algebra.IsSeparable (IntermediateField.adjoin K ({⟨jqModC K, hj⟩} : Set F)) F := by
  obtain ⟨p, hchar⟩ := ExpChar.exists K
  cases hchar with
  | zero => infer_instance
  | prime hprime =>
    haveI : Fact p.Prime := ⟨hprime⟩
    refine ⟨fun y => ?_⟩
    have hyint : IsIntegral K⟮(⟨jqModC K, hj⟩ : F)⟯ y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral

    have hιj : F.val (⟨jqModC K, hj⟩ : F) = jqModC K := rfl
    haveI : CharP K⟮(⟨jqModC K, hj⟩ : F)⟯ p := IntermediateField.charP _ p
    have hinj : Function.Injective (F.val : F → LaurentSeries K) := F.val.toRingHom.injective
    have hEmap : (K⟮(⟨jqModC K, hj⟩ : F)⟯).map F.val = K⟮jqModC K⟯ :=
      (adjoin_map K ({(⟨jqModC K, hj⟩ : F)} : Set F) F.val).trans (by rw [Set.image_singleton, hιj])

    let ψ : K⟮(⟨jqModC K, hj⟩ : F)⟯ →+* K⟮jqModC K⟯ :=
      ((equivOfEq hEmap).toAlgHom.comp ((K⟮(⟨jqModC K, hj⟩ : F)⟯).equivMap F.val).toAlgHom).toRingHom
    have hcomp : (algebraMap K⟮jqModC K⟯ (LaurentSeries K)).comp ψ
        = F.val.toRingHom.comp (algebraMap K⟮(⟨jqModC K, hj⟩ : F)⟯ F) := RingHom.ext fun _ => rfl
    have hyint' : IsIntegral K⟮jqModC K⟯ (y : LaurentSeries K) :=
      hyint.map_of_comp_eq ψ F.val.toRingHom hcomp

    have hmemΛ := mem_adjoin_pair_pow K p (y : LaurentSeries K) hyint'

    have hmap : (K⟮(⟨jqModC K, hj⟩ : F), y ^ p⟯).map F.val = K⟮jqModC K, (y : LaurentSeries K) ^ p⟯ :=
      (adjoin_map K ({(⟨jqModC K, hj⟩ : F), y ^ p} : Set F) F.val).trans
        (by rw [Set.image_pair, hιj]; rfl)
    have hmemF : y ∈ K⟮(⟨jqModC K, hj⟩ : F), y ^ p⟯ := by
      have h : F.val y ∈ ((K⟮(⟨jqModC K, hj⟩ : F), y ^ p⟯).map F.val : Set (LaurentSeries K)) := by
        rw [hmap]; exact hmemΛ
      have h' : F.val y ∈ (F.val '' (K⟮(⟨jqModC K, hj⟩ : F), y ^ p⟯ : Set F)) := by
        simpa only [coe_map] using h
      exact hinj.mem_set_image.mp h'
    have hmem : y ∈ (↥K⟮(⟨jqModC K, hj⟩ : F)⟯)⟮y ^ p⟯ := by
      rw [← mem_restrictScalars K, adjoin_simple_adjoin_simple]
      exact hmemF
    exact isSeparable_of_mem_adjoin_pow p hyint hmem

#print axioms solution

end S_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
end P2MW
export P2MW.S_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic (solution)

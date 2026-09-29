-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1922f1a9-bcf0-5298-bb4e-d96cbd6e855b

import Mathlib
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem

set_option autoImplicit false

open ModularCurve Polynomial

universe u

namespace KummerQ

variable {κ : Type u} [Field κ]

theorem qTwist_pow_succ (ζ : κˣ) (k : ℕ) (f : LaurentSeries κ) :
    qTwist (ζ ^ (k + 1)) f = qTwist ζ (qTwist (ζ ^ k) f) := by
  rw [qTwist_qTwist, pow_succ']

theorem qTwist_pow_eq_self_of {ζ : κˣ} {f : LaurentSeries κ} (h : qTwist ζ f = f) (k : ℕ) : qTwist (ζ ^ k) f = f := by
  induction k with
  | zero => rw [pow_zero, qTwist_one_apply]
  | succ k ih => rw [qTwist_pow_succ, ih, h]

theorem units_pow_eq_one {ℓ : ℕ} {ζ : κˣ} (hζ : IsPrimitiveRoot (ζ : κ) ℓ) : ζ ^ ℓ = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one])

theorem qTwist_eq_self_of_pow {ℓ : ℕ} (hℓ : ℓ.Prime) {ζ : κˣ} (hζ : IsPrimitiveRoot (ζ : κ) ℓ) {x : LaurentSeries κ}
    {e : ℕ} (he : ¬ ℓ ∣ e) (h : qTwist (ζ ^ e) x = x) : qTwist ζ x = x := by
  have hcop : Nat.Coprime e ℓ := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr he)
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓ.one_lt
  have hζ1 : (ζ ^ e) ^ a = ζ := by
    rw [← pow_mul]
    conv_lhs => rw [← Nat.mod_add_div (e * a) ℓ]
    rw [pow_add, pow_mul, units_pow_eq_one hζ, one_pow, mul_one, ha, pow_one]
  rw [← hζ1]
  exact qTwist_pow_eq_self_of h a

theorem qTwist_pow_injOn {ℓ : ℕ} (hℓ : ℓ.Prime) {ζ : κˣ} (hζ : IsPrimitiveRoot (ζ : κ) ℓ) {x : LaurentSeries κ}
    (hx : qTwist ζ x ≠ x) : Set.InjOn (fun k : ℕ => qTwist (ζ ^ k) x) (Finset.range ℓ : Set ℕ) := by
  intro k₁ hk₁ k₂ hk₂ h
  rw [Finset.coe_range, Set.mem_Iio] at hk₁ hk₂
  simp only at h
  by_contra hne
  wlog hlt : k₁ < k₂ generalizing k₁ k₂
  · exact this hk₂ hk₁ h.symm (fun e => hne e.symm) (by omega)
  apply hx
  refine qTwist_eq_self_of_pow hℓ hζ (e := k₂ - k₁) (fun hd => ?_) ?_
  · have := Nat.le_of_dvd (by omega) hd; omega
  · apply qTwist_injective (ζ ^ k₁)
    rw [qTwist_qTwist, ← pow_add, Nat.add_sub_cancel' hlt.le]
    exact h.symm

theorem qTwist_pow_mod {ℓ : ℕ} {ζ : κˣ} (hζ : IsPrimitiveRoot (ζ : κ) ℓ) (k : ℕ) (f : LaurentSeries κ) :
    qTwist (ζ ^ k) f = qTwist (ζ ^ (k % ℓ)) f := by
  conv_lhs => rw [← Nat.mod_add_div k ℓ, pow_add, pow_mul, units_pow_eq_one hζ, one_pow, mul_one]

end KummerQ

open KummerQ in
theorem solution
    (κ : Type u) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] (ζ : κˣ) (hζ : IsPrimitiveRoot (ζ : κ) ℓ)
    (F : IntermediateField κ (LaurentSeries κ))
    (hF : ∀ f : LaurentSeries κ, f ∈ F → ModularCurve.qTwist ζ f = f)
    (x y : LaurentSeries κ) (hy : ModularCurve.qTwist ζ y ≠ y) (hxσ : ModularCurve.qTwist ζ x = x) (hx : x ∉ F)
    (P : Polynomial ↥F)
    (hP : P.map (algebraMap ↥F (LaurentSeries κ)) =
      (∏ k ∈ Finset.range ℓ, (Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ k) y))) *
        (Polynomial.X - Polynomial.C x)) :
    Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = ℓ + 1 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set ι : ↥F →+* LaurentSeries κ := algebraMap ↥F (LaurentSeries κ) with hι
  have hιinj : Function.Injective ι := (algebraMap ↥F (LaurentSeries κ)).injective
  have hιapp : ∀ f : ↥F, ι f = (f : LaurentSeries κ) := fun f => rfl
  have hFk : ∀ (k : ℕ) (f : ↥F), qTwist (ζ ^ k) (f : LaurentSeries κ) = f := fun k f =>
    qTwist_pow_eq_self_of (hF f f.2) k
  let σ : ℕ → (LaurentSeries κ →ₐ[↥F] LaurentSeries κ) := fun k =>
    { qTwist (ζ ^ k) with commutes' := fun f => hFk k f }
  have hσ : ∀ (k : ℕ) (z : LaurentSeries κ), σ k z = qTwist (ζ ^ k) z := fun k z => rfl

  set PP : Polynomial (LaurentSeries κ) := ∏ k ∈ Finset.range ℓ, (X - C (qTwist (ζ ^ k) y)) with hPP
  have hPPmonic : PP.Monic := monic_prod_X_sub_C _ _
  have hPPdeg : PP.natDegree = ℓ := by
    rw [hPP, natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]
    simp
  have hPP0 : PP ≠ 0 := hPPmonic.ne_zero
  have hPmap0 : P.map ι ≠ 0 := by rw [hP]; exact mul_ne_zero hPP0 (X_sub_C_ne_zero x)
  have hP0 : P ≠ 0 := fun h => hPmap0 (by rw [h, Polynomial.map_zero])
  have hPdeg : P.natDegree = ℓ + 1 := by
    rw [← natDegree_map_eq_of_injective hιinj, hP, natDegree_mul hPP0 (X_sub_C_ne_zero x), hPPdeg, natDegree_X_sub_C]

  have haeval : aeval x P = 0 := by
    rw [aeval_def, ← eval_map, hP, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero]
  have hint : IsIntegral (↥F) x := (show IsAlgebraic (↥F) x from ⟨P, hP0, haeval⟩).isIntegral
  set m := minpoly (↥F) x with hm
  have hmdvd : m ∣ P := minpoly.dvd (↥F) x haeval
  have hm0 : m ≠ 0 := minpoly.ne_zero hint
  have hmmap0 : m.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hm0
  have hfin : Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = m.natDegree :=
    IntermediateField.adjoin.finrank hint
  have hupp : m.natDegree ≤ ℓ + 1 := hPdeg ▸ natDegree_le_of_dvd hmdvd hP0

  have hstab : ∀ (k : ℕ) (z : LaurentSeries κ), z ∈ (m.map ι).roots → qTwist (ζ ^ k) z ∈ (m.map ι).roots := by
    intro k z hz
    rw [mem_roots hmmap0, IsRoot.def, eval_map, ← aeval_def] at hz ⊢
    rw [← hσ k z, aeval_algHom_apply, hz, map_zero]
  have hxroot : x ∈ (m.map ι).roots := by
    rw [mem_roots hmmap0, IsRoot.def, eval_map, ← aeval_def, minpoly.aeval]

  have hdeg2 : 2 ≤ m.natDegree := by
    by_contra hlt
    have h1 : m.natDegree = 1 := by
      have h0 : 0 < m.natDegree := minpoly.natDegree_pos hint
      omega
    apply hx
    have hdeg1 : m.degree = 1 := by rw [degree_eq_natDegree hm0, h1]; rfl
    obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one (↥F) x hdeg1
    rw [← ha]; exact (a : ↥F).2

  have hProots : (P.map ι).roots = (Finset.range ℓ).val.map (fun k => qTwist (ζ ^ k) y) + {x} := by
    rw [hP, roots_mul (by rw [← hP]; exact hPmap0), roots_X_sub_C, hPP, Finset.prod_eq_multiset_prod]
    have hmm : (Multiset.map (fun k => X - C (qTwist (ζ ^ k) y)) (Finset.range ℓ).val) =
        ((Finset.range ℓ).val.map (fun k => qTwist (ζ ^ k) y)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hmm, roots_multiset_prod_X_sub_C]
  have horb : ∃ k : ℕ, qTwist (ζ ^ k) y ∈ (m.map ι).roots := by
    by_contra hno
    push Not at hno

    have hall : ∀ z ∈ (m.map ι).roots, z = x := by
      intro z hz
      have hz' : z ∈ (P.map ι).roots := Multiset.mem_of_le (roots.le_of_dvd hPmap0 (Polynomial.map_dvd ι hmdvd)) hz
      rw [hProots, Multiset.mem_add, Multiset.mem_map, Multiset.mem_singleton] at hz'
      rcases hz' with ⟨k, -, rfl⟩ | rfl
      · exact absurd hz (hno k)
      · rfl

    have hcount : (m.map ι).roots.count x ≤ 1 := by
      have h1 : (m.map ι).roots.count x ≤ (P.map ι).roots.count x :=
        Multiset.count_le_of_le x (roots.le_of_dvd hPmap0 (Polynomial.map_dvd ι hmdvd))
      have h2 : (P.map ι).roots.count x = 1 := by
        rw [hProots, Multiset.count_add, Multiset.count_singleton_self, Multiset.count_eq_zero_of_notMem, zero_add]
        rw [Multiset.mem_map]
        rintro ⟨k, -, hk⟩
        apply hy

        have h3 : qTwist ζ (qTwist (ζ ^ k) y) = qTwist (ζ ^ k) y := by rw [hk, hxσ]
        rw [qTwist_qTwist, mul_comm, ← qTwist_qTwist] at h3
        exact qTwist_injective (ζ ^ k) h3
      omega
    have hcard : Multiset.card (m.map ι).roots ≤ 1 := by
      rw [Multiset.eq_replicate_card.mpr hall, Multiset.card_replicate]
      rw [Multiset.eq_replicate_card.mpr hall, Multiset.count_replicate_self] at hcount
      exact hcount

    have hsplitP : (P.map ι).Splits := by
      rw [hP]
      exact (Splits.prod fun k _ => Splits.X_sub_C _).mul (Splits.X_sub_C _)
    have hsplit : (m.map ι).Splits := hsplitP.of_dvd hPmap0 (Polynomial.map_dvd ι hmdvd)
    have hcard' : Multiset.card (m.map ι).roots = m.natDegree := by
      rw [← hsplit.natDegree_eq_card_roots, natDegree_map_eq_of_injective hιinj]
    omega
  obtain ⟨k₀, hk₀⟩ := horb

  have hallroots : ∀ k : ℕ, qTwist (ζ ^ k) y ∈ (m.map ι).roots := by
    intro k

    have h := hstab (k + (ℓ - k₀ % ℓ)) _ hk₀
    rw [qTwist_qTwist, ← pow_add, qTwist_pow_mod hζ] at h
    rw [qTwist_pow_mod hζ k]
    have hmod : (k + (ℓ - k₀ % ℓ) + k₀) % ℓ = k % ℓ := by
      have h1 := Nat.mod_add_div k₀ ℓ
      have h2 := Nat.mod_lt k₀ hℓ.pos
      have h4 : k + (ℓ - k₀ % ℓ) + k₀ = k + ℓ * (1 + k₀ / ℓ) := by
        have h5 : ℓ * (1 + k₀ / ℓ) = ℓ + ℓ * (k₀ / ℓ) := by ring
        omega
      rw [h4, Nat.add_mul_mod_self_left]
    rwa [hmod] at h
  set Z : Finset (LaurentSeries κ) := (Finset.range ℓ).image fun k => qTwist (ζ ^ k) y with hZ
  have hZcard : Z.card = ℓ := by
    rw [hZ, Finset.card_image_of_injOn (qTwist_pow_injOn hℓ hζ hy), Finset.card_range]
  have hxZ : x ∉ Z := by
    rw [hZ, Finset.mem_image]
    rintro ⟨k, -, hk⟩
    apply hy
    have h3 : qTwist ζ (qTwist (ζ ^ k) y) = qTwist (ζ ^ k) y := by rw [hk, hxσ]
    rw [qTwist_qTwist, mul_comm, ← qTwist_qTwist] at h3
    exact qTwist_injective (ζ ^ k) h3
  have hsub : (insert x Z).val ⊆ (m.map ι).roots := by
    intro z hz
    rw [Finset.mem_val, Finset.mem_insert, hZ, Finset.mem_image] at hz
    rcases hz with rfl | ⟨k, -, rfl⟩
    · exact hxroot
    · exact hallroots k
  have hlow : ℓ + 1 ≤ m.natDegree := by
    have h := card_le_degree_of_subset_roots hsub
    rwa [Finset.card_insert_of_notMem hxZ, hZcard, natDegree_map_eq_of_injective hιinj] at h
  rw [hfin]
  omega

end S_ModularCurve_finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem (solution)

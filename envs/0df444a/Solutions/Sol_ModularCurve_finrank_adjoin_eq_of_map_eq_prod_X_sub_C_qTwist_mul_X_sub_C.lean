-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6ae909ab-f6cd-532c-aca6-4bfb1d91032a

import Mathlib
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C

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

end KummerQ

open KummerQ in
theorem solution
    (κ : Type u) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] (ζ : κˣ) (hζ : IsPrimitiveRoot (ζ : κ) ℓ)
    (F : IntermediateField κ (LaurentSeries κ))
    (hF : ∀ f : LaurentSeries κ, f ∈ F → ModularCurve.qTwist ζ f = f)
    (x r : LaurentSeries κ) (hx : ModularCurve.qTwist ζ x ≠ x)
    (P : Polynomial ↥F)
    (hP : P.map (algebraMap ↥F (LaurentSeries κ)) =
      (∏ k ∈ Finset.range ℓ, (Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ k) x))) *
        (Polynomial.X - Polynomial.C r)) :
    (r ∉ F → Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = ℓ + 1) ∧
    (r ∈ F → Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = ℓ) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set ι : ↥F →+* LaurentSeries κ := algebraMap ↥F (LaurentSeries κ) with hι
  have hιinj : Function.Injective ι := (algebraMap ↥F (LaurentSeries κ)).injective
  have hιapp : ∀ f : ↥F, ι f = (f : LaurentSeries κ) := fun f => rfl

  have hFk : ∀ (k : ℕ) (f : ↥F), qTwist (ζ ^ k) (f : LaurentSeries κ) = f := fun k f =>
    qTwist_pow_eq_self_of (hF f f.2) k
  let σ : ℕ → (LaurentSeries κ →ₐ[↥F] LaurentSeries κ) := fun k =>
    { qTwist (ζ ^ k) with commutes' := fun f => hFk k f }
  have hσ : ∀ (k : ℕ) (y : LaurentSeries κ), σ k y = qTwist (ζ ^ k) y := fun k y => rfl

  set PP : Polynomial (LaurentSeries κ) := ∏ k ∈ Finset.range ℓ, (X - C (qTwist (ζ ^ k) x)) with hPP
  have hPPmonic : PP.Monic := monic_prod_X_sub_C _ _
  have hPPdeg : PP.natDegree = ℓ := by
    rw [hPP, natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]
    simp
  have hPP0 : PP ≠ 0 := hPPmonic.ne_zero
  have hPmap0 : P.map ι ≠ 0 := by rw [hP]; exact mul_ne_zero hPP0 (X_sub_C_ne_zero r)
  have hP0 : P ≠ 0 := fun h => hPmap0 (by rw [h, Polynomial.map_zero])
  have hPdeg : P.natDegree = ℓ + 1 := by
    rw [← natDegree_map_eq_of_injective hιinj, hP, natDegree_mul hPP0 (X_sub_C_ne_zero r), hPPdeg, natDegree_X_sub_C]

  have hx0 : eval x (P.map ι) = 0 := by
    rw [hP, eval_mul, eval_prod]
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hℓ.pos)
    rw [pow_zero, qTwist_one_apply, eval_sub, eval_X, eval_C, sub_self]
  have haeval : aeval x P = 0 := by rwa [aeval_def, ← eval_map]
  have hint : IsIntegral (↥F) x := (show IsAlgebraic (↥F) x from ⟨P, hP0, haeval⟩).isIntegral

  set m := minpoly (↥F) x with hm
  have hmdvd : m ∣ P := minpoly.dvd (↥F) x haeval
  have hm0 : m ≠ 0 := minpoly.ne_zero hint
  have hmmap0 : m.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hm0
  have hfin : Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = m.natDegree :=
    IntermediateField.adjoin.finrank hint

  have hroots : ∀ k : ℕ, qTwist (ζ ^ k) x ∈ (m.map ι).roots := by
    intro k
    rw [mem_roots hmmap0, IsRoot.def, eval_map, ← aeval_def, ← hσ k x, aeval_algHom_apply, minpoly.aeval, map_zero]
  set Z : Finset (LaurentSeries κ) := (Finset.range ℓ).image fun k => qTwist (ζ ^ k) x with hZ
  have hZcard : Z.card = ℓ := by
    rw [hZ, Finset.card_image_of_injOn (qTwist_pow_injOn hℓ hζ hx), Finset.card_range]
  have hZsub : Z.val ⊆ (m.map ι).roots := by
    intro z hz
    rw [Finset.mem_val, hZ, Finset.mem_image] at hz
    obtain ⟨k, -, rfl⟩ := hz
    exact hroots k
  have hlow : ℓ ≤ m.natDegree := by
    have h := card_le_degree_of_subset_roots hZsub
    rwa [hZcard, natDegree_map_eq_of_injective hιinj] at h
  have hupp : m.natDegree ≤ ℓ + 1 := hPdeg ▸ natDegree_le_of_dvd hmdvd hP0

  have hPPeq : PP = (Z.val.map fun a => X - C a).prod := by
    rw [hZ, Finset.image_val_of_injOn (qTwist_pow_injOn hℓ hζ hx), Multiset.map_map, Function.comp_def,
      hPP, Finset.prod_eq_multiset_prod]
  have hPPdvd : PP ∣ m.map ι := by
    rw [hPPeq, Multiset.prod_X_sub_C_dvd_iff_le_roots hmmap0]
    exact (Multiset.le_iff_subset Z.nodup).mpr hZsub
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  ·
    rw [hfin]
    by_contra hne
    have hdeg : m.natDegree = ℓ := by omega
    have hmeq : m.map ι = PP :=
      eq_of_monic_of_dvd_of_natDegree_le hPPmonic ((minpoly.monic hint).map ι) hPPdvd
        (by rw [natDegree_map_eq_of_injective hιinj, hdeg, hPPdeg])
    obtain ⟨Q, hQ⟩ := hmdvd
    have h1 : m.map ι * Q.map ι = PP * (X - C r) := by
      rw [← Polynomial.map_mul, ← hQ, hP]
    rw [hmeq] at h1
    have hQr : Q.map ι = X - C r := mul_left_cancel₀ hPP0 h1
    apply hr
    have h2 : ι (-(Q.coeff 0)) = r := by
      have := congrArg (fun p : Polynomial (LaurentSeries κ) => p.coeff 0) hQr
      simp only [coeff_map, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at this
      rw [map_neg, this, neg_neg]
    rw [← h2, hιapp]
    exact (-(Q.coeff 0)).2
  ·
    rw [hfin]
    set r' : ↥F := ⟨r, hr⟩ with hr'
    have hroot : P.IsRoot r' := by
      apply hιinj
      rw [map_zero, ← eval₂_hom, ← eval_map, hP, eval_mul, eval_sub, eval_X, eval_C, hιapp, sub_self, mul_zero]
    have hPfac : (X - C r') * (P /ₘ (X - C r')) = P := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hxr : x ≠ r := fun h => hx (by rw [h, hF r hr])
    have hQ : aeval x (P /ₘ (X - C r')) = 0 := by
      have h := haeval
      rw [← hPfac, map_mul, map_sub, aeval_X, aeval_C, hιapp] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hxr)
    have hQ0 : P /ₘ (X - C r') ≠ 0 := fun h => hP0 (by rw [← hPfac, h, mul_zero])
    have hQdeg : (P /ₘ (X - C r')).natDegree = ℓ := by
      have h := congrArg natDegree hPfac
      rw [natDegree_mul (X_sub_C_ne_zero r') hQ0, natDegree_X_sub_C, hPdeg] at h
      omega
    have h5 : m.natDegree ≤ (P /ₘ (X - C r')).natDegree := natDegree_le_of_dvd (minpoly.dvd (↥F) x hQ) hQ0
    omega

end S_ModularCurve_finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C (solution)

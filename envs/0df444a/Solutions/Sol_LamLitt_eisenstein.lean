-- Prove2me | solution 1 for LamLitt.eisenstein
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T07:40:23.739877+00:00
-- url     : https://prove2.me/submissions/d6c619e8-1cab-494b-9f38-b0d8ad683290

import Mathlib
import Definitions.Def_LamLitt_Defs


namespace EISAux
open PowerSeries

/-- Power series over `ℚ` with all coefficients in the subring `S`. -/
def T (S : Subring ℚ) : Subring ℚ⟦X⟧ where
  carrier := {φ | ∀ n, coeff n φ ∈ S}
  mul_mem' {a b} ha hb n := by
    rw [coeff_mul]
    exact Subring.sum_mem _ fun x _ => S.mul_mem (ha _) (hb _)
  one_mem' n := by
    rw [coeff_one]; split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  add_mem' {a b} ha hb n := by
    rw [map_add]; exact S.add_mem (ha n) (hb n)
  zero_mem' n := by simp
  neg_mem' {a} ha n := by
    rw [map_neg]; exact S.neg_mem (ha n)

lemma mem_T {S : Subring ℚ} {φ : ℚ⟦X⟧} : φ ∈ T S ↔ ∀ n, coeff n φ ∈ S := Iff.rfl

lemma X_mem (S : Subring ℚ) : (X : ℚ⟦X⟧) ∈ T S := by
  intro n; rw [coeff_X]; split_ifs
  · exact S.one_mem
  · exact S.zero_mem

lemma eval_mem (S : Subring ℚ) (P : Polynomial ℚ⟦X⟧) (hP : ∀ i, P.coeff i ∈ T S)
    {φ : ℚ⟦X⟧} (hφ : φ ∈ T S) : P.eval φ ∈ T S := by
  rw [Polynomial.eval_eq_sum_range]
  exact Subring.sum_mem _ fun i _ => (T S).mul_mem (hP i) ((T S).pow_mem hφ i)

lemma taylor_mem (S : Subring ℚ) (P : Polynomial ℚ⟦X⟧) (hP : ∀ i, P.coeff i ∈ T S)
    {φ : ℚ⟦X⟧} (hφ : φ ∈ T S) (n : ℕ) : (Polynomial.taylor φ P).coeff n ∈ T S := by
  rw [Polynomial.taylor_coeff]
  refine eval_mem S _ (fun i => ?_) hφ
  rw [Polynomial.hasseDeriv_coeff]
  exact (T S).mul_mem (natCast_mem (T S) _) (hP _)

lemma trunc_mem (S : Subring ℚ) (φ : ℚ⟦X⟧) (k : ℕ) (h : ∀ j < k, coeff j φ ∈ S) :
    ((trunc k φ : Polynomial ℚ) : ℚ⟦X⟧) ∈ T S := by
  intro n
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with hn
  · exact h n hn
  · exact S.zero_mem

lemma X_pow_dvd_sub_trunc (φ : ℚ⟦X⟧) (k : ℕ) :
    (X : ℚ⟦X⟧) ^ k ∣ φ - ((trunc k φ : Polynomial ℚ) : ℚ⟦X⟧) := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self]

/-- Hensel-type recursion: the coefficients of a solution `h` of
`c + w h + X Σ aᵢ h^(i+2) = 0` lie in `S` once `c, w, aᵢ` do and `w(0)⁻¹ ∈ S`. -/
lemma rec (S : Subring ℚ) (c w h : ℚ⟦X⟧) (M : ℕ) (a : ℕ → ℚ⟦X⟧)
    (hc : c ∈ T S) (hw : w ∈ T S) (ha : ∀ i, a i ∈ T S)
    (hw0 : coeff 0 w ≠ 0) (hu : (coeff 0 w)⁻¹ ∈ S)
    (heq : c + w * h + X * ∑ i ∈ Finset.range M, a i * h ^ (i + 2) = 0) : h ∈ T S := by
  have key : ∀ n, ∀ j < n, coeff j h ∈ S := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ih j hj
      set H : ℚ⟦X⟧ := ((trunc j h : Polynomial ℚ) : ℚ⟦X⟧) with hH
      have hHT : H ∈ T S := trunc_mem S h j ih
      obtain ⟨e, he⟩ := X_pow_dvd_sub_trunc h j
      rw [← hH] at he
      have hhe : h = H + X ^ j * e := by rw [← he]; ring
      have hF : (X : ℚ⟦X⟧) ^ (j + 1) ∣ X * ∑ i ∈ Finset.range M, a i * h ^ (i + 2)
          - X * ∑ i ∈ Finset.range M, a i * H ^ (i + 2) := by
        rw [← mul_sub, pow_succ, mul_comm (X ^ j)]
        refine mul_dvd_mul_left X ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.dvd_sum fun i _ => ?_
        rw [← mul_sub]
        refine Dvd.dvd.mul_left ?_ _
        exact dvd_trans (⟨e, he⟩ : (X : ℚ⟦X⟧) ^ j ∣ h - H) (sub_dvd_pow_sub_pow _ _ _)
      obtain ⟨r, hr⟩ := hF
      set K := c + w * H + X * ∑ i ∈ Finset.range M, a i * H ^ (i + 2) with hK
      have hKT : K ∈ T S := by
        refine (T S).add_mem ((T S).add_mem hc ((T S).mul_mem hw hHT)) ((T S).mul_mem (X_mem S) ?_)
        exact Subring.sum_mem _ fun i _ => (T S).mul_mem (ha i) ((T S).pow_mem hHT _)
      have h2 : K + X ^ j * (w * e) + X ^ (j + 1) * r = 0 := by
        rw [← heq, hK, sub_eq_iff_eq_add.mp hr, hhe]; ring
      have h3 := congrArg (coeff j) h2
      rw [map_add, map_add, coeff_X_pow_mul', if_pos le_rfl, coeff_X_pow_mul', if_neg (by omega),
        Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_mul, map_zero, add_zero,
        ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply] at h3
      have h4 : coeff j h = coeff 0 e := by
        rw [hhe, map_add, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, hH, Polynomial.coeff_coe,
          coeff_trunc, if_neg (lt_irrefl _), zero_add]
      have h5 : coeff 0 e = -(coeff j K) * (coeff 0 w)⁻¹ := by
        field_simp; linear_combination h3
      rw [h4, h5]
      exact S.mul_mem (S.neg_mem (hKT j)) hu
  intro n
  exact key (n + 1) n (Nat.lt_succ_self n)

end EISAux

namespace EISAux
open PowerSeries

lemma algebraMap_eq (q : Polynomial ℚ) : algebraMap (Polynomial ℚ) ℚ⟦X⟧ q = (q : ℚ⟦X⟧) := by
  rw [algebraMap_apply', Algebra.algebraMap_self, map_id]; rfl

lemma exists_sep (f : ℚ⟦X⟧) (hAlg : IsAlgebraic (Polynomial ℚ) f) :
    ∃ p : Polynomial (Polynomial ℚ), Polynomial.aeval f p = 0 ∧
      Polynomial.aeval f (Polynomial.derivative p) ≠ 0 := by
  classical
  have hex : ∃ n, ∃ p : Polynomial (Polynomial ℚ), p ≠ 0 ∧ Polynomial.aeval f p = 0 ∧
      p.natDegree = n := by
    obtain ⟨p, hp, h⟩ := hAlg; exact ⟨_, p, hp, h, rfl⟩
  obtain ⟨p, hp, h, hd⟩ := Nat.find_spec hex
  refine ⟨p, h, fun h' => ?_⟩
  have hinj : Function.Injective (algebraMap (Polynomial ℚ) ℚ⟦X⟧) := by
    intro a b hab; rw [algebraMap_eq, algebraMap_eq] at hab; exact (Polynomial.coe_injective ℚ) hab
  have hn : p.natDegree ≠ 0 := by
    intro h0
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.aeval_C] at h
    apply hp
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hinj (h.trans (map_zero _).symm), map_zero]
  have hder : Polynomial.derivative p ≠ 0 := fun h0 => hn (Polynomial.derivative_eq_zero.mp h0)
  have hlt := Polynomial.natDegree_derivative_lt hn
  rw [hd] at hlt
  exact Nat.find_min hex hlt ⟨_, hder, h', rfl⟩

lemma fin_adjoin (E : Finset ℚ) : ∃ N : ℕ, ∀ r ∈ E, r ∈ LamLitt.ℤAdjoinInvNat N := by
  classical
  refine ⟨∏ r ∈ E, r.den, fun r hr => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun r : ℚ => r.den) hr
  have hN : ((∏ r ∈ E, r.den : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Finset.prod_ne_zero_iff.mpr fun r _ => r.den_ne_zero
  have hmem : (1 / ((∏ r ∈ E, r.den : ℕ) : ℚ)) ∈ LamLitt.ℤAdjoinInvNat (∏ r ∈ E, r.den) :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  have hr' : r = ((r.num * q : ℤ) : ℚ) * (1 / ((∏ r ∈ E, r.den : ℕ) : ℚ)) := by
    rw [hq] at hN ⊢
    have hd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    have hq0 : (q : ℚ) ≠ 0 := by
      intro h0; apply hN; push_cast; rw [h0, mul_zero]
    push_cast
    field_simp
    nth_rewrite 1 [← Rat.num_div_den r]
    field_simp
  rw [hr']
  exact Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) hmem

theorem eisenstein (f : ℚ⟦X⟧) (hAlg : IsAlgebraic (Polynomial ℚ) f) :
    ∃ N : ℕ, LamLitt.IsCoeffIntegralAdjointInvNat f N := by
  classical
  obtain ⟨p, hp0, hp1⟩ := exists_sep f hAlg
  set P : Polynomial ℚ⟦X⟧ := p.map (algebraMap (Polynomial ℚ) ℚ⟦X⟧) with hPdef
  have hPf : P.eval f = 0 := by rw [hPdef, Polynomial.eval_map, ← Polynomial.aeval_def, hp0]
  set D := (Polynomial.derivative P).eval f with hD
  have hD0 : D ≠ 0 := by
    rw [hD, hPdef, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hp1
  set m := D.order.toNat with hm
  obtain ⟨w, hw⟩ : X ^ m ∣ D := X_pow_order_dvd
  have hw0 : coeff 0 w ≠ 0 := by
    have := coeff_order hD0
    rwa [← hm, hw, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at this
  -- the finite set of rationals that must lie in `ℤ[1/N]`
  set EP : Finset ℚ := p.support.biUnion
    (fun i => (p.coeff i).support.image (fun n => (p.coeff i).coeff n)) with hEP
  set E : Finset ℚ := EP ∪ (Finset.range (m + 1)).image (fun n => coeff n f) ∪ {(coeff 0 w)⁻¹}
  obtain ⟨N, hN⟩ := fin_adjoin E
  refine ⟨N, ?_⟩
  set S : Subring ℚ := (LamLitt.ℤAdjoinInvNat N).toSubring
  have hS : ∀ r ∈ E, r ∈ S := hN
  have hPT : ∀ i, P.coeff i ∈ T S := by
    intro i n
    rw [hPdef, Polynomial.coeff_map, algebraMap_eq, Polynomial.coeff_coe]
    by_cases h : (p.coeff i).coeff n = 0
    · rw [h]; exact S.zero_mem
    · apply hS
      have hi : i ∈ p.support := by
        rw [Polynomial.mem_support_iff]; intro h'; rw [h', Polynomial.coeff_zero] at h; exact h rfl
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      rw [hEP, Finset.mem_biUnion]
      exact ⟨i, hi, Finset.mem_image.mpr ⟨n, Polynomial.mem_support_iff.mpr h, rfl⟩⟩
  have hu : (coeff 0 w)⁻¹ ∈ S := hS _ (by simp [E])
  set g : ℚ⟦X⟧ := ((trunc (m + 1) f : Polynomial ℚ) : ℚ⟦X⟧) with hg
  have hgT : g ∈ T S := trunc_mem S f (m + 1) fun j hj =>
    hS _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)))
  obtain ⟨h, hh⟩ := X_pow_dvd_sub_trunc f (m + 1)
  rw [← hg] at hh
  have hfgh : f = X ^ (m + 1) * h + g := by rw [← hh]; ring
  set tP := Polynomial.taylor g P with htP
  have htT : ∀ i, tP.coeff i ∈ T S := taylor_mem S P hPT hgT
  set Q := Polynomial.divX (Polynomial.divX tP) with hQ
  set b0 := tP.coeff 0
  set b1 := tP.coeff 1
  set z : ℚ⟦X⟧ := X ^ (m + 1) * h with hz
  have hdecomp : tP.eval z = (Q.eval z * z + b1) * z + b0 := by
    have e1 := Polynomial.divX_mul_X_add tP
    have e2 := Polynomial.divX_mul_X_add (Polynomial.divX tP)
    rw [Polynomial.coeff_divX, zero_add] at e2
    conv_lhs => rw [← e1, ← e2]
    simp [hQ]
    rfl
  have hmain : (Q.eval z * z + b1) * z + b0 = 0 := by
    rw [← hdecomp, htP, Polynomial.taylor_eval, ← hfgh, hPf]
  -- `b1 = P'(g) = X^m w'`
  obtain ⟨s, hs⟩ := Polynomial.sub_dvd_eval_sub f g (Polynomial.derivative P)
  have hb1 : b1 = (Polynomial.derivative P).eval g := Polynomial.taylor_coeff_one _ _
  set w' := w - X * h * s with hw'
  have hb1w : b1 = X ^ m * w' := by
    rw [hb1, hw']
    have : (Polynomial.derivative P).eval g = D - (f - g) * s := by
      linear_combination -hs
    rw [this, hh, hw]; ring
  have hw'0 : coeff 0 w' = coeff 0 w := by
    rw [hw', map_sub, mul_assoc, coeff_zero_X_mul, sub_zero]
  have hw'T : w' ∈ T S := by
    intro n
    have := htT 1 (n + m)
    rwa [← show b1 = tP.coeff 1 from rfl, hb1w, coeff_X_pow_mul] at this
  set M := Q.natDegree + 1
  set a : ℕ → ℚ⟦X⟧ := fun i => Q.coeff i * (X ^ (m + 1)) ^ i with ha
  have haT : ∀ i, a i ∈ T S := by
    intro i
    refine (T S).mul_mem ?_ ((T S).pow_mem ((T S).pow_mem (X_mem S) _) _)
    rw [hQ, Polynomial.coeff_divX, Polynomial.coeff_divX]
    exact htT _
  set F := ∑ i ∈ Finset.range M, a i * h ^ (i + 2) with hF
  have hQz : Q.eval z * z ^ 2 = X ^ (m + (m + 1)) * (X * F) := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, hF, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha, hz]; ring
  set c := -(w' * h + X * F) with hc
  have hb0 : b0 = X ^ (m + (m + 1)) * c := by
    rw [hc]; linear_combination hmain - hQz - z * hb1w + (X ^ m * w') * hz
  have hcT : c ∈ T S := by
    intro n
    have := htT 0 (n + (m + (m + 1)))
    rwa [← show b0 = tP.coeff 0 from rfl, hb0, coeff_X_pow_mul] at this
  have hheq : c + w' * h + X * F = 0 := by rw [hc]; ring
  have hhT : h ∈ T S := rec S c w' h M a hcT hw'T haT (hw'0 ▸ hw0) (hw'0 ▸ hu) hheq
  have hfT : f ∈ T S := by
    rw [hfgh]; exact (T S).add_mem ((T S).mul_mem ((T S).pow_mem (X_mem S) _) hhT) hgT
  exact hfT

end EISAux

open PowerSeries in
theorem solution (f : PowerSeries ℚ) (hAlg : IsAlgebraic (Polynomial ℚ) f) :
    ∃ N : ℕ, LamLitt.IsCoeffIntegralAdjointInvNat f N :=
  EISAux.eisenstein f hAlg

-- Prove2me | solution 1 for MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ae676132-33fa-5fb9-906d-12ff986aaa3a

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add

set_option autoImplicit false

universe u

open MvPowerSeries

namespace L2aLogIntegrality

variable {R : Type*} [CommRing R] {d : ℕ}

private noncomputable def zfam (d : ℕ) (R : Type*) [CommRing R] :
    Fin d ⊕ Fin d → MvPowerSeries (Fin d) R :=
  Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) fun _ => 0

private theorem constantCoeff_zfam (s : Fin d ⊕ Fin d) : (zfam d R s).constantCoeff = 0 := by
  rcases s with l | l
  · exact constantCoeff_X l
  · exact map_zero _

private theorem hasSubst_zfam : HasSubst (zfam d R) :=
  hasSubst_of_constantCoeff_zero constantCoeff_zfam

private noncomputable def P0 (d : ℕ) (R : Type*) [CommRing R] :
    MvPowerSeries (Fin d ⊕ Fin d) R →ₐ[R] MvPowerSeries (Fin d) R :=
  substAlgHom (hasSubst_zfam (d := d) (R := R))

private theorem P0_apply (g : MvPowerSeries (Fin d ⊕ Fin d) R) :
    P0 d R g = subst (zfam d R) g := by
  rw [P0, coe_substAlgHom]

private theorem prod_pow_comp_inl :
    ((fun (s : Fin d ⊕ Fin d) (e : ℕ) => zfam d R s ^ e) ∘ Sum.inl)
      = fun (l : Fin d) (e : ℕ) => (X l : MvPowerSeries (Fin d) R) ^ e := by
  funext l e
  rfl

private theorem prod_pow_comp_inr :
    ((fun (s : Fin d ⊕ Fin d) (e : ℕ) => zfam d R s ^ e) ∘ Sum.inr)
      = fun (_ : Fin d) (e : ℕ) => (0 : MvPowerSeries (Fin d) R) ^ e := by
  funext l e
  rfl

private theorem coeff_P0 (g : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d →₀ ℕ) :
    coeff m (P0 d R g) = coeff (m.sumElim 0) g := by
  classical
  rw [P0_apply, coeff_subst hasSubst_zfam, finsum_eq_single _ (m.sumElim (0 : Fin d →₀ ℕ))]
  · rw [Finsupp.prod_sumElim, prod_pow_comp_inl, Finsupp.prod_zero_index, mul_one,
      ← MvPowerSeries.monomial_one_eq, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro n hn
    obtain ⟨a, b, rfl⟩ : ∃ a b : Fin d →₀ ℕ, n = a.sumElim b :=
      ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain n).symm⟩
    rw [Finsupp.prod_sumElim, prod_pow_comp_inl, prod_pow_comp_inr]
    by_cases hb : b = 0
    · subst hb
      have hab : m ≠ a := fun h => hn (by rw [h])
      rw [Finsupp.prod_zero_index, mul_one, ← MvPowerSeries.monomial_one_eq,
        coeff_monomial_ne hab, smul_zero]
    · obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
        by_contra h
        push Not at h
        exact hb (Finsupp.ext h)
      have hz : (b.prod fun (_ : Fin d) (e : ℕ) => (0 : MvPowerSeries (Fin d) R) ^ e) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr ht) (zero_pow ht)
      rw [hz, mul_zero, map_zero, smul_zero]

private noncomputable def linB (j : Fin d) (g : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  fun m => coeff (m.sumElim (Finsupp.single j 1)) g

private theorem coeff_linB (j : Fin d) (g : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d →₀ ℕ) :
    coeff m (linB j g) = coeff (m.sumElim (Finsupp.single j 1)) g :=
  rfl

private theorem sumElim_quad_injective :
    Function.Injective
      (fun (q : ((Fin d →₀ ℕ) × (Fin d →₀ ℕ)) × (Fin d →₀ ℕ) × (Fin d →₀ ℕ)) =>
        (q.1.1.sumElim q.2.1, q.1.2.sumElim q.2.2)) := by
  rintro ⟨⟨x, y⟩, z, w⟩ ⟨⟨x', y'⟩, z', w'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : ((x, z) : (Fin d →₀ ℕ) × (Fin d →₀ ℕ)) = (x', z') :=
    Finsupp.sumFinsuppEquivProdFinsupp.symm.injective h1
  have e2 : ((y, w) : (Fin d →₀ ℕ) × (Fin d →₀ ℕ)) = (y', w') :=
    Finsupp.sumFinsuppEquivProdFinsupp.symm.injective h2
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  rfl

private theorem antidiagonal_one_eq :
    Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (0 : ℕ))} := by
  ext ⟨a, b⟩
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

private theorem sum_antidiagonal_single_one {M : Type*} [AddCommMonoid M] (j : Fin d)
    (G : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) → M) :
    ∑ y ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.single j 1), G y =
      G (0, Finsupp.single j 1) + G (Finsupp.single j 1, 0) := by
  classical
  rw [Finsupp.antidiagonal_single, Finset.sum_map, antidiagonal_one_eq,
    Finset.sum_pair (by simp)]
  simp

private theorem linB_mul (j : Fin d) (g h : MvPowerSeries (Fin d ⊕ Fin d) R) :
    linB j (g * h) = linB j g * P0 d R h + P0 d R g * linB j h := by
  classical
  ext m
  rw [coeff_linB, coeff_mul, ← Finsupp.image_sumElim_product_antidiagonal,
    Finset.sum_image fun a _ b _ hab => sumElim_quad_injective hab, Finset.sum_product,
    map_add, coeff_mul, coeff_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_antidiagonal_single_one]
  simp only [coeff_linB, coeff_P0]
  ring

private theorem linB_one (j : Fin d) : linB j (1 : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 := by
  classical
  ext m
  rw [coeff_linB, coeff_one, if_neg, map_zero]
  intro h
  have := DFunLike.congr_fun h (Sum.inr j)
  simp at this

private theorem linB_pow_succ (j : Fin d) (g : MvPowerSeries (Fin d ⊕ Fin d) R) (c : ℕ) :
    linB j (g ^ (c + 1)) =
      ((c + 1 : ℕ) : MvPowerSeries (Fin d) R) * ((P0 d R g) ^ c * linB j g) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ, linB_mul, ih, map_pow]
    push_cast
    ring

private theorem linB_prod {ι : Type*} [DecidableEq ι] (j : Fin d) (s : Finset ι)
    (f : ι → MvPowerSeries (Fin d ⊕ Fin d) R) :
    linB j (∏ k ∈ s, f k) = ∑ k ∈ s, (∏ l ∈ s.erase k, P0 d R (f l)) * linB j (f k) := by
  induction s using Finset.induction_on with
  | empty => simp [linB_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, linB_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      map_prod, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hka : a ≠ k := fun h => ha (h ▸ hk)
      rw [Finset.erase_insert_of_ne hka,
        Finset.prod_insert fun h => ha (Finset.mem_of_mem_erase h), mul_assoc]

private theorem degree_sumElim (a b : Fin d →₀ ℕ) : (a.sumElim b).degree = a.degree + b.degree := by
  rw [Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]

section Rescale

variable {p : ℕ} {F : MvFormalGroup d R} {Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}

private theorem coeff_Fp (hp : (p : R) ∈ nonZeroDivisors R)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : R) = (p : R) ^ m.degree * (F.toPowerSeries i).coeff m)
    (k : Fin d) {E : (Fin d ⊕ Fin d) →₀ ℕ} (hE : E ≠ 0) :
    coeff E (Fp k) = (p : R) ^ (E.degree - 1) * coeff E (F.toPowerSeries k) := by
  have hdeg : E.degree ≠ 0 := fun h => hE ((Finsupp.degree_eq_zero_iff E).mp h)
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hdeg
  have h := hFp k E hE
  rw [hr, pow_succ] at h
  have h2 : (coeff E (Fp k) - (p : R) ^ r * coeff E (F.toPowerSeries k)) * p = 0 := by
    rw [sub_mul, h]
    ring
  rw [hr, Nat.succ_sub_one]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hp).2 _ h2)

private theorem P0_F (F : MvFormalGroup d R) (k : Fin d) : P0 d R (F.toPowerSeries k) = X k := by
  rw [P0_apply]
  exact MvFormalGroup.subst_elim_X_zero F k

private theorem P0_Fp (hp : (p : R) ∈ nonZeroDivisors R)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : R) = (p : R) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0) (k : Fin d) :
    P0 d R (Fp k) = X k := by
  classical
  ext m
  rw [coeff_P0]
  by_cases hm : m = 0
  · subst hm
    rw [Finsupp.sumElim_zero_zero, coeff_zero_eq_constantCoeff_apply, hFp0, coeff_zero_X]
  · have hE : m.sumElim (0 : Fin d →₀ ℕ) ≠ 0 := by
      intro h
      apply hm
      ext l
      have := DFunLike.congr_fun h (Sum.inl l)
      simpa using this
    rw [coeff_Fp hp hFp k hE, ← coeff_P0, P0_F, coeff_X, degree_sumElim, map_zero, add_zero]
    split_ifs with h
    · subst h
      simp
    · simp

private theorem coeff_linB_Fp (hp : (p : R) ∈ nonZeroDivisors R)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : R) = (p : R) ^ m.degree * (F.toPowerSeries i).coeff m)
    (j k : Fin d) (m : Fin d →₀ ℕ) :
    coeff m (linB j (Fp k)) =
      (p : R) ^ m.degree * coeff (m.sumElim (Finsupp.single j 1)) (F.toPowerSeries k) := by
  have hE : m.sumElim (Finsupp.single j 1) ≠ 0 := by
    intro h
    have := DFunLike.congr_fun h (Sum.inr j)
    simp at this
  rw [coeff_linB, coeff_Fp hp hFp k hE, degree_sumElim, Finsupp.degree_single, Nat.add_sub_cancel]

private theorem coeff_zero_linB_Fp (hp : (p : R) ∈ nonZeroDivisors R)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : R) = (p : R) ^ m.degree * (F.toPowerSeries i).coeff m)
    (j k : Fin d) :
    coeff (0 : Fin d →₀ ℕ) (linB j (Fp k)) = if k = j then 1 else 0 := by
  rw [coeff_linB_Fp hp hFp, map_zero, pow_zero, one_mul, Finsupp.sumElim_zero_single,
    F.coeff_single_inr k j]

private theorem prod_erase_X_pow_mul (n : Fin d →₀ ℕ) (k : Fin d) {c : ℕ} (hc : n k = c + 1) :
    (∏ l ∈ Finset.univ.erase k, (X l : MvPowerSeries (Fin d) R) ^ n l) * X k ^ c =
      monomial (n - Finsupp.single k 1) 1 := by
  classical
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_pow,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    have hlk : l ≠ k := Finset.ne_of_mem_erase hl
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hlk), Nat.sub_zero]
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_same, hc, Nat.add_sub_cancel]

private theorem coeff_linB_prod_pow (hp : (p : R) ∈ nonZeroDivisors R)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : R) = (p : R) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0) (j : Fin d) (n m : Fin d →₀ ℕ) :
    coeff m (linB j (n.prod fun l e => Fp l ^ e)) =
      ∑ k : Fin d, (n k : R) * (if n - Finsupp.single k 1 ≤ m then
        coeff (m - (n - Finsupp.single k 1)) (linB j (Fp k)) else 0) := by
  classical
  rw [Finsupp.prod_pow, linB_prod, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hP : ∀ l, P0 d R (Fp l ^ n l) = (X l : MvPowerSeries (Fin d) R) ^ n l := fun l => by
    rw [map_pow, P0_Fp hp hFp hFp0]
  simp only [hP]
  rcases hnk : n k with _ | c
  · rw [pow_zero, linB_one, mul_zero, map_zero, Nat.cast_zero, zero_mul]
  · rw [linB_pow_succ, P0_Fp hp hFp hFp0,
      show (∏ l ∈ Finset.univ.erase k, (X l : MvPowerSeries (Fin d) R) ^ n l) *
          (((c + 1 : ℕ) : MvPowerSeries (Fin d) R) * (X k ^ c * linB j (Fp k)))
        = (c + 1 : ℕ) • (((∏ l ∈ Finset.univ.erase k, (X l : MvPowerSeries (Fin d) R) ^ n l)
            * X k ^ c) * linB j (Fp k)) by rw [nsmul_eq_mul]; ring,
      prod_erase_X_pow_mul n k hnk, map_nsmul, coeff_monomial_mul, one_mul, nsmul_eq_mul]

variable (φ : Fin d → MvPowerSeries (Fin d) R)

private theorem key_identity (hp : (p : R) ∈ nonZeroDivisors R)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : R) = (p : R) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (φ i))
    (i j : Fin d) {m : Fin d →₀ ℕ} (hm : m ≠ 0) :
    ∑ k : Fin d, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
      coeff (x.1 + Finsupp.single k 1) (φ i) *
        (((x.1 k + 1 : ℕ) : R) * coeff x.2 (linB j (Fp k))) = 0 := by
  classical
  have hFs : HasSubst Fp := hasSubst_of_constantCoeff_zero hFp0

  have hR : coeff (m.sumElim (Finsupp.single j 1)) (subst Fp (φ i)) = 0 := by
    rw [hφF i, map_add]
    have h1 : subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (φ i)
        = rename Sum.inl (φ i) := (rename_eq_subst Sum.inl (φ i)).symm
    have h2 : subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (φ i)
        = rename Sum.inr (φ i) := (rename_eq_subst Sum.inr (φ i)).symm
    rw [h1, h2, coeff_rename_eq_zero, coeff_rename_eq_zero, add_zero]
    · rintro ⟨x, hx⟩
      obtain ⟨l, hl⟩ : ∃ l, m l ≠ 0 := by
        by_contra h
        push Not at h
        exact hm (Finsupp.ext h)
      have := DFunLike.congr_fun hx (Sum.inl l)
      rw [Finsupp.mapDomain_notin_range _ _ (by simp), Finsupp.sumElim_inl] at this
      exact hl this.symm
    · rintro ⟨x, hx⟩
      have := DFunLike.congr_fun hx (Sum.inr j)
      rw [Finsupp.mapDomain_notin_range _ _ (by simp), Finsupp.sumElim_inr,
        Finsupp.single_eq_same] at this
      exact zero_ne_one this

  rw [coeff_subst hFs] at hR
  have hsummand : ∀ n : Fin d →₀ ℕ,
      coeff n (φ i) • coeff (m.sumElim (Finsupp.single j 1)) (n.prod fun l e => Fp l ^ e)
        = ∑ k : Fin d, coeff n (φ i) * ((n k : R) * (if n - Finsupp.single k 1 ≤ m then
            coeff (m - (n - Finsupp.single k 1)) (linB j (Fp k)) else 0)) := by
    intro n
    rw [← coeff_linB, coeff_linB_prod_pow hp hFp hFp0, smul_eq_mul, Finset.mul_sum]
  rw [finsum_congr hsummand] at hR

  let Sk : Fin d → Finset (Fin d →₀ ℕ) := fun k =>
    (Finset.HasAntidiagonal.antidiagonal m).image fun x => x.1 + Finsupp.single k 1
  have hvan : ∀ (k : Fin d) (n : Fin d →₀ ℕ), n ∉ Sk k →
      coeff n (φ i) * ((n k : R) * (if n - Finsupp.single k 1 ≤ m then
        coeff (m - (n - Finsupp.single k 1)) (linB j (Fp k)) else 0)) = 0 := by
    intro k n hn
    by_cases hk : n k = 0
    · rw [hk, Nat.cast_zero, zero_mul, mul_zero]
    · rw [if_neg, mul_zero, mul_zero]
      intro hle
      apply hn
      rw [Finset.mem_image]
      refine ⟨(n - Finsupp.single k 1, m - (n - Finsupp.single k 1)), ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
        exact add_tsub_cancel_of_le hle
      · exact tsub_add_cancel_of_le
          (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hk))
  have hsupp : (Function.support fun n : Fin d →₀ ℕ =>
      ∑ k : Fin d, coeff n (φ i) * ((n k : R) * (if n - Finsupp.single k 1 ≤ m then
        coeff (m - (n - Finsupp.single k 1)) (linB j (Fp k)) else 0)))
      ⊆ ((Finset.univ.biUnion Sk : Finset (Fin d →₀ ℕ)) : Set (Fin d →₀ ℕ)) := by
    intro n hn
    rw [Function.mem_support] at hn
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨k, Finset.mem_univ k, by_contra fun h => hk (hvan k n h)⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_comm] at hR
  rw [← hR]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsub : Sk k ⊆ Finset.univ.biUnion Sk := Finset.subset_biUnion_of_mem Sk (Finset.mem_univ k)
  rw [← Finset.sum_subset hsub fun n _ hn => hvan k n hn]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hle : x.1 ≤ m := le_iff_exists_add.mpr ⟨x.2, hx.symm⟩
    rw [add_tsub_cancel_right, if_pos hle, Finsupp.add_apply, Finsupp.single_eq_same,
      show m - x.1 = x.2 by rw [← hx, add_tsub_cancel_left]]
  · intro x hx y hy hxy
    have h1 : x.1 = y.1 := add_right_cancel hxy
    rw [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    have h2 : x.2 = y.2 := by
      apply add_left_cancel (a := x.1)
      rw [hx, h1, hy]
    exact Prod.ext h1 h2

end Rescale

end L2aLogIntegrality

open L2aLogIntegrality in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i j : Fin d) (m : Fin d →₀ ℕ) :
    ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree} := by
  classical
  suffices H : ∀ N : ℕ, ∀ u : Fin d →₀ ℕ, u.degree = N → ∀ k : Fin d,
      (φ i).coeff (u + Finsupp.single k 1) * ((u k + 1 : ℕ) : 𝓞) ∈
        Ideal.span {(p : 𝓞) ^ N} by
    rw [mul_comm]
    exact H m.degree m rfl j
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro u hu k
    by_cases hu0 : u = 0
    · subst hu0
      rw [map_zero] at hu
      subst hu
      simp
    · have hkey := key_identity (R := 𝓞) φ hp hFp hFp0 hφF i k hu0
      rw [Finset.sum_comm, ← Finset.add_sum_erase _ _
        (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero u) : (u, (0 : Fin d →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal u)]
        at hkey
      have hdiag : ∑ k' : Fin d, (φ i).coeff (u + Finsupp.single k' 1) *
          (((u k' + 1 : ℕ) : 𝓞) * coeff (0 : Fin d →₀ ℕ) (linB k (Fp k')))
          = (φ i).coeff (u + Finsupp.single k 1) * ((u k + 1 : ℕ) : 𝓞) := by
        simp only [coeff_zero_linB_Fp hp hFp, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
      rw [hdiag] at hkey
      rw [eq_neg_of_add_eq_zero_left hkey]
      refine neg_mem (Ideal.sum_mem _ fun x hx => Ideal.sum_mem _ fun k' _ => ?_)
      obtain ⟨hx0, hx⟩ := Finset.mem_erase.mp hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hx2 : x.2 ≠ 0 := by
        intro h
        apply hx0
        have h1 : x.1 = u := by rw [← hx, h, add_zero]
        exact Prod.ext h1 h
      have hdeg : x.1.degree + x.2.degree = N := by rw [← map_add, hx, hu]
      have hdeg2 : x.2.degree ≠ 0 := fun h => hx2 ((Finsupp.degree_eq_zero_iff x.2).mp h)
      have hlt : x.1.degree < N := by omega
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (IH x.1.degree hlt x.1 rfl k')
      rw [← mul_assoc, ← hc, coeff_linB_Fp hp hFp, ← hdeg, pow_add]
      exact Ideal.mem_span_singleton'.mpr ⟨c *
        (F.toPowerSeries k').coeff (x.2.sumElim (Finsupp.single k 1)), by ring⟩

end S_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
end P2MW
export P2MW.S_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add (solution)

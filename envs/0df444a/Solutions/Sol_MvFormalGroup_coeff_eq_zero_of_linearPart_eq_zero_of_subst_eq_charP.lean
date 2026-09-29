-- Prove2me | solution 1 for MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/81da22c7-469c-5760-810a-94d4a66e5036

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP

set_option autoImplicit false

open MvPowerSeries

universe u

namespace FrobFactor

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

private theorem coeff_Fp {p : ℕ} (hp : (p : R) ∈ nonZeroDivisors R) {F : MvFormalGroup d R}
    {Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : R) = (p : R) ^ m.degree * (F.toPowerSeries i).coeff m)
    (k : Fin d) {E : (Fin d ⊕ Fin d) →₀ ℕ} (hE : E ≠ 0) :
    coeff E (Fp k) = (p : R) ^ (E.degree - 1) * coeff E (F.toPowerSeries k) := by
  have h1 : 1 ≤ E.degree := by
    rcases Nat.eq_zero_or_pos E.degree with h | h
    · exact absurd ((Finsupp.degree_eq_zero_iff E).mp h) hE
    · exact h
  have h := hFp k E hE
  rw [show E.degree = (E.degree - 1) + 1 by omega, pow_succ, mul_assoc, mul_comm (p : R),
    ← mul_assoc] at h
  exact (mul_cancel_right_mem_nonZeroDivisors hp).mp h

private noncomputable abbrev inlX (d : ℕ) (R : Type*) [CommRing R] :
    Fin d → MvPowerSeries (Fin d ⊕ Fin d) R := fun j => X (Sum.inl j)

private noncomputable abbrev inrX (d : ℕ) (R : Type*) [CommRing R] :
    Fin d → MvPowerSeries (Fin d ⊕ Fin d) R := fun j => X (Sum.inr j)

private theorem hasSubst_inlX : HasSubst (inlX d R) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

private theorem hasSubst_inrX : HasSubst (inrX d R) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

private theorem coeff_sumElim_subst_inlX (g : MvPowerSeries (Fin d) R) (m n : Fin d →₀ ℕ) :
    coeff (m.sumElim n) (subst (inlX d R) g) = if n = 0 then coeff m g else 0 := by
  have hre : subst (inlX d R) g = rename Sum.inl g := (rename_eq_subst Sum.inl g).symm
  rw [hre]
  split_ifs with hn
  · subst hn
    rw [← Finsupp.embDomain_inl]
    exact coeff_embDomain_rename Function.Embedding.inl g m
  · apply coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ : ∃ t, n t ≠ 0 := by
      by_contra h
      push Not at h
      exact hn (Finsupp.ext h)
    have h := DFunLike.congr_fun hx (Sum.inr t)
    rw [Finsupp.mapDomain_notin_range, Finsupp.sumElim_inr] at h
    · exact ht h.symm
    · rintro ⟨y, hy⟩
      cases hy

private theorem coeff_sumElim_subst_inrX (g : MvPowerSeries (Fin d) R) (m n : Fin d →₀ ℕ) :
    coeff (m.sumElim n) (subst (inrX d R) g) = if m = 0 then coeff n g else 0 := by
  have hre : subst (inrX d R) g = rename Sum.inr g := (rename_eq_subst Sum.inr g).symm
  rw [hre]
  split_ifs with hm
  · subst hm
    rw [← Finsupp.embDomain_inr]
    exact coeff_embDomain_rename Function.Embedding.inr g n
  · apply coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ : ∃ t, m t ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (Finsupp.ext h)
    have h := DFunLike.congr_fun hx (Sum.inl t)
    rw [Finsupp.mapDomain_notin_range, Finsupp.sumElim_inl] at h
    · exact ht h.symm
    · rintro ⟨y, hy⟩
      cases hy

private theorem P0_subst_inlX (g : MvPowerSeries (Fin d) R) : P0 d R (subst (inlX d R) g) = g := by
  ext m
  rw [coeff_P0, coeff_sumElim_subst_inlX, if_pos rfl]

private theorem P0_subst_inrX (g : MvPowerSeries (Fin d) R) (hg : g.constantCoeff = 0) :
    P0 d R (subst (inrX d R) g) = 0 := by
  ext m
  rw [coeff_P0, coeff_sumElim_subst_inrX, map_zero]
  split_ifs with h
  · rw [coeff_zero_eq_constantCoeff_apply, hg]
  · rfl

private theorem linB_subst_inlX (j : Fin d) (g : MvPowerSeries (Fin d) R) :
    linB j (subst (inlX d R) g) = 0 := by
  ext m
  rw [coeff_linB, coeff_sumElim_subst_inlX, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero),
    map_zero]

private theorem linB_subst_inrX (j : Fin d) (g : MvPowerSeries (Fin d) R) :
    linB j (subst (inrX d R) g) = coeff (Finsupp.single j 1) g • (1 : MvPowerSeries (Fin d) R) := by
  ext m
  rw [coeff_linB, coeff_sumElim_subst_inrX, map_smul, coeff_one, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

private theorem X_inl_eq (i : Fin d) :
    (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) =
      subst (inlX d R) (X i : MvPowerSeries (Fin d) R) := by
  rw [subst_X hasSubst_inlX]

private theorem X_inr_eq (i : Fin d) :
    (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) =
      subst (inrX d R) (X i : MvPowerSeries (Fin d) R) := by
  rw [subst_X hasSubst_inrX]

private theorem P0_addXY (i : Fin d) :
    P0 d R (X (Sum.inl i) + X (Sum.inr i)) = X i := by
  rw [map_add, X_inl_eq, X_inr_eq, P0_subst_inlX, P0_subst_inrX _ (constantCoeff_X i), add_zero]

private theorem linB_addXY (j i : Fin d) :
    linB j (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) =
      (if j = i then 1 else 0 : R) • (1 : MvPowerSeries (Fin d) R) := by
  have hadd : linB j (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) =
      linB j (X (Sum.inl i)) + linB j (X (Sum.inr i)) := by
    ext m; simp only [coeff_linB, map_add]
  rw [hadd, X_inl_eq, X_inr_eq, linB_subst_inlX, linB_subst_inrX, zero_add, coeff_index_single_X]

private theorem coeff_sumElim_subst_inlX_mul_subst_inrX (f g : MvPowerSeries (Fin d) R)
    (m n : Fin d →₀ ℕ) :
    coeff (m.sumElim n) (subst (inlX d R) f * subst (inrX d R) g) = coeff m f * coeff n g := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (m.sumElim 0, (0 : Fin d →₀ ℕ).sumElim n)]
  · rw [coeff_sumElim_subst_inlX, if_pos rfl, coeff_sumElim_subst_inrX, if_pos rfl]
  · rintro ⟨x, y⟩ hxy hne
    obtain ⟨a, b, rfl⟩ : ∃ a b : Fin d →₀ ℕ, x = a.sumElim b :=
      ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain x).symm⟩
    obtain ⟨a', b', rfl⟩ : ∃ a' b' : Fin d →₀ ℕ, y = a'.sumElim b' :=
      ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain y).symm⟩
    rw [coeff_sumElim_subst_inlX, coeff_sumElim_subst_inrX]
    split_ifs with hb ha'
    · exfalso
      subst hb; subst ha'
      apply hne
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
      rw [← Finsupp.sumElim_add, add_zero, zero_add] at hxy
      have h1 := congrArg (Finsupp.comapDomain Sum.inl · Sum.inl_injective.injOn) hxy
      have h2 := congrArg (Finsupp.comapDomain Sum.inr · Sum.inr_injective.injOn) hxy
      have e1 : ∀ u v : Fin d →₀ ℕ,
          Finsupp.comapDomain Sum.inl (u.sumElim v) Sum.inl_injective.injOn = u := fun u v => by
        ext t; rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inl]
      have e2 : ∀ u v : Fin d →₀ ℕ,
          Finsupp.comapDomain Sum.inr (u.sumElim v) Sum.inr_injective.injOn = v := fun u v => by
        ext t; rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inr]
      rw [e1, e1] at h1
      rw [e2, e2] at h2
      rw [h1, h2]
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _
  · intro h
    exfalso
    apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal, ← Finsupp.sumElim_add, add_zero, zero_add]

private theorem P0_F (F : MvFormalGroup d R) (k : Fin d) : P0 d R (F.toPowerSeries k) = X k := by
  rw [P0_apply]
  exact MvFormalGroup.subst_elim_X_zero F k

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

private theorem coeff_linB_prod_pow (G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hG : ∀ l, P0 d R (G l) = X l) (j : Fin d) (n m : Fin d →₀ ℕ) :
    coeff m (linB j (n.prod fun l e => G l ^ e)) =
      ∑ k : Fin d, (n k : R) * (if n - Finsupp.single k 1 ≤ m then
        coeff (m - (n - Finsupp.single k 1)) (linB j (G k)) else 0) := by
  classical
  rw [Finsupp.prod_pow, linB_prod, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hP : ∀ l, P0 d R (G l ^ n l) = (X l : MvPowerSeries (Fin d) R) ^ n l := fun l => by
    rw [map_pow, hG]
  simp only [hP]
  rcases hnk : n k with _ | c
  · rw [pow_zero, linB_one, mul_zero, map_zero, Nat.cast_zero, zero_mul]
  · rw [linB_pow_succ, hG,
      show (∏ l ∈ Finset.univ.erase k, (X l : MvPowerSeries (Fin d) R) ^ n l) *
          (((c + 1 : ℕ) : MvPowerSeries (Fin d) R) * (X k ^ c * linB j (G k)))
        = (c + 1 : ℕ) • (((∏ l ∈ Finset.univ.erase k, (X l : MvPowerSeries (Fin d) R) ^ n l)
            * X k ^ c) * linB j (G k)) by rw [nsmul_eq_mul]; ring,
      prod_erase_X_pow_mul n k hnk, map_nsmul, coeff_monomial_mul, one_mul, nsmul_eq_mul]

private theorem coeff_zero_linB_F (F : MvFormalGroup d R) (j k : Fin d) :
    coeff (0 : Fin d →₀ ℕ) (linB j (F.toPowerSeries k)) = if k = j then 1 else 0 := by
  rw [coeff_linB, ← Finsupp.embDomain_inr, Finsupp.embDomain_single]
  exact F.coeff_single_inr k j

section Key

variable {h : ℕ} (F : MvFormalGroup d R) (G : MvFormalGroup h R) (θ : Fin h → MvPowerSeries (Fin d) R)

private theorem coeff_single_finsuppProd_pow_eq_zero (hθ0 : ∀ i, (θ i).constantCoeff = 0)
    (hθ1 : MvFormalGroup.linearPart θ = 0) (b : Fin h →₀ ℕ) (j : Fin d) :
    coeff (Finsupp.single j 1) (b.prod fun l e => θ l ^ e) = 0 := by
  classical
  rcases Nat.lt_or_ge b.degree 1 with h0 | h1
  · have hb : b = 0 := (Finsupp.degree_eq_zero_iff b).mp (by omega)
    subst hb
    rw [Finsupp.prod_zero_index, coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]
  rcases Nat.lt_or_ge 1 b.degree with h2 | h2
  · exact MvFormalGroup.coeff_finsuppProd_pow_eq_zero_of_degree_lt hθ0
      (by rw [Finsupp.degree_single]; exact h2)
  · have hb1 : b.degree = 1 := le_antisymm h2 h1
    have hne : b ≠ 0 := fun hb => by rw [hb, map_zero] at hb1; omega
    obtain ⟨l, hl⟩ : ∃ l, b l ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (Finsupp.ext hcon)
    have hle : Finsupp.single l 1 ≤ b := by rw [Finsupp.single_le_iff]; omega
    obtain ⟨e', he'⟩ := exists_add_of_le hle
    have hdeg : e'.degree = 0 := by
      have := congrArg Finsupp.degree he'
      rw [map_add, Finsupp.degree_single] at this
      omega
    rw [(Finsupp.degree_eq_zero_iff _).mp hdeg, add_zero] at he'
    subst he'
    rw [Finsupp.prod_single_index (h := fun l e => θ l ^ e) (pow_zero _), pow_one]
    have := congrFun (congrFun hθ1 l) j
    simpa [MvFormalGroup.linearPart] using this

private theorem key_identity (hθ0 : ∀ i, (θ i).constantCoeff = 0)
    (hθ1 : MvFormalGroup.linearPart θ = 0)
    (hθF : ∀ i, subst F.toPowerSeries (θ i) =
      subst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j)))
        (G.toPowerSeries i))
    (i : Fin h) (j : Fin d) (m : Fin d →₀ ℕ) :
    ∑ k : Fin d, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
      coeff (x.1 + Finsupp.single k 1) (θ i) *
        (((x.1 k + 1 : ℕ) : R) * coeff x.2 (linB j (F.toPowerSeries k))) = 0 := by
  classical
  have hFs : HasSubst F.toPowerSeries := hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero

  have hσ0 : ∀ s, (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j)) s
        ).constantCoeff = 0 := by
    rintro (l | l)
    · exact constantCoeff_subst_eq_zero hasSubst_inlX (fun _ => constantCoeff_X _) (hθ0 l)
    · exact constantCoeff_subst_eq_zero hasSubst_inrX (fun _ => constantCoeff_X _) (hθ0 l)
  have hR : coeff (m.sumElim (Finsupp.single j 1)) (subst F.toPowerSeries (θ i)) = 0 := by
    rw [hθF i, coeff_subst (hasSubst_of_constantCoeff_zero hσ0)]
    refine finsum_eq_zero_of_forall_eq_zero fun E => ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : Fin h →₀ ℕ, E = a.sumElim b :=
      ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain E).symm⟩
    rw [Finsupp.prod_sumElim]
    have h1 : (a.prod fun l e => ((fun s e => (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j)) s) ^ e)
          ∘ Sum.inl) l e) = subst (inlX d R) (a.prod fun l e => θ l ^ e) := by
      rw [← coe_substAlgHom hasSubst_inlX, map_finsuppProd]
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [Function.comp_apply, map_pow, coe_substAlgHom, Sum.elim_inl]
    have h2 : (b.prod fun l e => ((fun s e => (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j)) s) ^ e)
          ∘ Sum.inr) l e) = subst (inrX d R) (b.prod fun l e => θ l ^ e) := by
      rw [← coe_substAlgHom hasSubst_inrX, map_finsuppProd]
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [Function.comp_apply, map_pow, coe_substAlgHom, Sum.elim_inr]
    rw [h1, h2, coeff_sumElim_subst_inlX_mul_subst_inrX,
      coeff_single_finsuppProd_pow_eq_zero θ hθ0 hθ1, mul_zero, smul_zero]

  rw [coeff_subst hFs] at hR
  have hsummand : ∀ n : Fin d →₀ ℕ,
      coeff n (θ i) • coeff (m.sumElim (Finsupp.single j 1)) (n.prod fun l e => F.toPowerSeries l ^ e)
        = ∑ k : Fin d, coeff n (θ i) * ((n k : R) * (if n - Finsupp.single k 1 ≤ m then
            coeff (m - (n - Finsupp.single k 1)) (linB j (F.toPowerSeries k)) else 0)) := by
    intro n
    rw [← coeff_linB, coeff_linB_prod_pow _ (P0_F F), smul_eq_mul, Finset.mul_sum]
  rw [finsum_congr hsummand] at hR

  let Sk : Fin d → Finset (Fin d →₀ ℕ) := fun k =>
    (Finset.HasAntidiagonal.antidiagonal m).image fun x => x.1 + Finsupp.single k 1
  have hvan : ∀ (k : Fin d) (n : Fin d →₀ ℕ), n ∉ Sk k →
      coeff n (θ i) * ((n k : R) * (if n - Finsupp.single k 1 ≤ m then
        coeff (m - (n - Finsupp.single k 1)) (linB j (F.toPowerSeries k)) else 0)) = 0 := by
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
      ∑ k : Fin d, coeff n (θ i) * ((n k : R) * (if n - Finsupp.single k 1 ≤ m then
        coeff (m - (n - Finsupp.single k 1)) (linB j (F.toPowerSeries k)) else 0)))
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

end Key

end FrobFactor

open FrobFactor in
theorem solution
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    {g h : ℕ} (F : MvFormalGroup g S) (G : MvFormalGroup h S)
    (θ : Fin h → MvPowerSeries (Fin g) S)
    (hθ0 : ∀ i, (θ i).constantCoeff = 0)
    (hθ1 : MvFormalGroup.linearPart θ = 0)
    (hθF : ∀ i, subst F.toPowerSeries (θ i) =
      subst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) S)) (θ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) S)) (θ j)))
        (G.toPowerSeries i))
    (i : Fin h) (m : Fin g →₀ ℕ) (hm : ∃ j, ¬ p ∣ m j) :
    (θ i).coeff m = 0 := by
  classical

  have hD : ∀ N : ℕ, ∀ u : Fin g →₀ ℕ, u.degree = N → ∀ k : Fin g,
      (θ i).coeff (u + Finsupp.single k 1) * ((u k + 1 : ℕ) : S) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro u hu k
      have hkey := FrobFactor.key_identity F G θ hθ0 hθ1 hθF i k u
      rw [Finset.sum_comm, ← Finset.add_sum_erase _ _
        (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero u) : (u, (0 : Fin g →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal u)]
        at hkey
      have hdiag : ∑ k' : Fin g, (θ i).coeff (u + Finsupp.single k' 1) *
          (((u k' + 1 : ℕ) : S) * coeff (0 : Fin g →₀ ℕ) (FrobFactor.linB k (F.toPowerSeries k')))
          = (θ i).coeff (u + Finsupp.single k 1) * ((u k + 1 : ℕ) : S) := by
        simp only [FrobFactor.coeff_zero_linB_F, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
      rw [hdiag] at hkey
      rw [eq_neg_of_add_eq_zero_left hkey, neg_eq_zero]
      refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun k' _ => ?_
      obtain ⟨hx0, hx⟩ := Finset.mem_erase.mp hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hx2 : x.2 ≠ 0 := by
        intro h0
        apply hx0
        have h1 : x.1 = u := by rw [← hx, h0, add_zero]
        exact Prod.ext h1 h0
      have hdeg : x.1.degree + x.2.degree = N := by rw [← map_add, hx, hu]
      have hdeg2 : x.2.degree ≠ 0 := fun h0 => hx2 ((Finsupp.degree_eq_zero_iff x.2).mp h0)
      have hlt : x.1.degree < N := by omega
      rw [← mul_assoc, IH x.1.degree hlt x.1 rfl k', zero_mul]

  obtain ⟨j, hj⟩ := hm
  have hmj : m j ≠ 0 := fun h0 => hj (by rw [h0]; exact dvd_zero p)
  set u := m - Finsupp.single j 1 with hu
  have hmu : m = u + Finsupp.single j 1 := by
    rw [hu, tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]; omega
  have h := hD u.degree u rfl j
  rw [← hmu, show u j + 1 = m j by rw [hmu, Finsupp.add_apply, Finsupp.single_eq_same]] at h
  have hunit : IsUnit ((m j : ℕ) : S) := by
    have hz : ((m j : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hj
    have := (isUnit_iff_ne_zero.mpr hz).map (ZMod.castHom (dvd_refl p) S)
    rwa [map_natCast] at this
  exact (hunit.mul_left_eq_zero).mp h

end S_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
end P2MW
export P2MW.S_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP (solution)

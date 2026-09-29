-- Prove2me | solution 1 for MvFormalGroup.adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3879e727-41c7-58af-b12c-9c5bc7b62cd1

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq

set_option autoImplicit false

open MvPowerSeries

universe u v

namespace TaylorEval

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
      beta_reduce at h1 h2
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

private theorem hasSubst_addXY :
    HasSubst (fun i => (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun i => by rw [map_add, constantCoeff_X, constantCoeff_X, add_zero]

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

private theorem coeff_sumElim_single_subst_addXY (j : Fin d) (g : MvPowerSeries (Fin d) R)
    (m : Fin d →₀ ℕ) :
    coeff (m.sumElim (Finsupp.single j 1))
        (subst (fun i => (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) g) =
      ((m j + 1 : ℕ) : R) * coeff (m + Finsupp.single j 1) g := by
  classical
  rw [coeff_subst hasSubst_addXY]
  have hterm : ∀ n : Fin d →₀ ℕ,
      coeff n g • coeff (m.sumElim (Finsupp.single j 1))
          (n.prod fun i e => (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) ^ e)
        = coeff n g * ((n j : R) * if n - Finsupp.single j 1 = m then 1 else 0) := by
    intro n
    rw [smul_eq_mul, ← coeff_linB, coeff_linB_prod_pow _ P0_addXY,
      Finset.sum_eq_single j]
    · congr 1
      rw [linB_addXY, if_pos rfl]
      by_cases h1 : n - Finsupp.single j 1 ≤ m
      · rw [if_pos h1, map_smul, coeff_one, smul_eq_mul, one_mul]
        by_cases h2 : n - Finsupp.single j 1 = m
        · rw [if_pos h2, h2, tsub_self, if_pos rfl]
        · rw [if_neg h2, if_neg]
          intro h3
          exact h2 (le_antisymm h1 (tsub_eq_zero_iff_le.mp h3))
      · rw [if_neg h1, if_neg]
        intro h2
        exact h1 (le_of_eq h2)
    · intro k _ hkj
      rw [linB_addXY, if_neg (Ne.symm hkj), zero_smul, map_zero]
      split_ifs <;> simp
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp_rw [hterm]
  rw [finsum_eq_single _ (m + Finsupp.single j 1)]
  · rw [add_tsub_cancel_right, if_pos rfl, mul_one, Finsupp.add_apply, Finsupp.single_eq_same,
      mul_comm]
  · intro n hn
    by_cases hnj : n j = 0
    · rw [hnj, Nat.cast_zero, zero_mul, mul_zero]
    · rw [if_neg, mul_zero, mul_zero]
      intro h
      apply hn
      rw [← h, tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      omega

private noncomputable abbrev inlPart (E : (Fin d ⊕ Fin d) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.comapDomain Sum.inl E Sum.inl_injective.injOn

private noncomputable abbrev inrPart (E : (Fin d ⊕ Fin d) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.comapDomain Sum.inr E Sum.inr_injective.injOn

private theorem inlPart_sumElim (a b : Fin d →₀ ℕ) : inlPart (a.sumElim b) = a := by
  ext t; rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inl]

private theorem inrPart_sumElim (a b : Fin d →₀ ℕ) : inrPart (a.sumElim b) = b := by
  ext t; rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inr]

private theorem sumElim_inlPart_inrPart (E : (Fin d ⊕ Fin d) →₀ ℕ) :
    (inlPart E).sumElim (inrPart E) = E :=
  Finsupp.comapDomain_sumElim_comapDomain E

private noncomputable def bquot (g : MvPowerSeries (Fin d ⊕ Fin d) R) (j : Fin d) :
    MvPowerSeries (Fin d ⊕ Fin d) R :=
  fun E => if (inrPart E + Finsupp.single j 1).support.min'
      ⟨j, by rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]; omega⟩ = j
    then coeff ((inlPart E).sumElim (inrPart E + Finsupp.single j 1)) g else 0

private theorem coeff_bquot (g : MvPowerSeries (Fin d ⊕ Fin d) R) (j : Fin d) (m n : Fin d →₀ ℕ) :
    coeff (m.sumElim n) (bquot g j) = if (n + Finsupp.single j 1).support.min'
      ⟨j, by rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]; omega⟩ = j
    then coeff (m.sumElim (n + Finsupp.single j 1)) g else 0 := by
  show (if _ then _ else _) = _
  simp only [inlPart_sumElim, inrPart_sumElim]

private theorem coeff_sumElim_X_inr_mul (j : Fin d) (h : MvPowerSeries (Fin d ⊕ Fin d) R)
    (m n : Fin d →₀ ℕ) :
    coeff (m.sumElim n) (X (Sum.inr j) * h) =
      if n j ≠ 0 then coeff (m.sumElim (n - Finsupp.single j 1)) h else 0 := by
  classical
  rw [X_def, coeff_monomial_mul, one_mul]
  by_cases hj : n j ≠ 0
  · have hle : Finsupp.single (Sum.inr j) 1 ≤ m.sumElim n := by
      rw [Finsupp.single_le_iff, Finsupp.sumElim_inr]; omega
    have hsub : m.sumElim n - Finsupp.single (Sum.inr j) 1 = m.sumElim (n - Finsupp.single j 1) := by
      ext s; rcases s with t | t
      · rw [Finsupp.tsub_apply, Finsupp.sumElim_inl, Finsupp.sumElim_inl, Finsupp.single_apply,
          if_neg (by simp), Nat.sub_zero]
      · rw [Finsupp.tsub_apply, Finsupp.sumElim_inr, Finsupp.sumElim_inr, Finsupp.tsub_apply,
          Finsupp.single_apply, Finsupp.single_apply]
        by_cases ht : j = t
        · subst ht; simp
        · rw [if_neg (by simpa using ht), if_neg ht]
    rw [if_pos hle, if_pos hj, hsub]
  · rw [if_neg, if_neg hj]
    intro hle
    apply hj
    have := hle (Sum.inr j)
    rw [Finsupp.single_eq_same, Finsupp.sumElim_inr] at this
    omega

private theorem eq_sum_X_inr_mul_bquot (g : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hg : ∀ m : Fin d →₀ ℕ, coeff (m.sumElim 0) g = 0) :
    g = ∑ j : Fin d, X (Sum.inr j) * bquot g j := by
  classical
  ext E
  obtain ⟨m, n, rfl⟩ : ∃ m n : Fin d →₀ ℕ, E = m.sumElim n := ⟨_, _, (sumElim_inlPart_inrPart E).symm⟩
  rw [map_sum]
  have hterm : ∀ j : Fin d, coeff (m.sumElim n) (X (Sum.inr j) * bquot g j) =
      if h : n j ≠ 0 then (if n.support.min' ⟨j, Finsupp.mem_support_iff.mpr h⟩ = j
        then coeff (m.sumElim n) g else 0) else 0 := by
    intro j
    rw [coeff_sumElim_X_inr_mul]
    by_cases hj : n j ≠ 0
    · rw [if_pos hj, dif_pos hj, coeff_bquot]
      have heq : n - Finsupp.single j 1 + Finsupp.single j 1 = n :=
        tsub_add_cancel_of_le (by rw [Finsupp.single_le_iff]; omega)
      simp only [heq]
    · rw [if_neg hj, dif_neg hj]
  simp only [hterm]
  by_cases hn : n = 0
  · subst hn
    rw [hg]
    simp
  · have hne : n.support.Nonempty := by rw [Finsupp.support_nonempty_iff]; exact hn
    set j₀ := n.support.min' hne with hj₀
    have hj₀mem : n j₀ ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
    rw [Finset.sum_eq_single j₀]
    · rw [dif_pos hj₀mem, if_pos rfl]
    · intro j _ hj
      by_cases h : n j ≠ 0
      · rw [dif_pos h, if_neg]
        intro h'
        exact hj h'.symm
      · rw [dif_neg h]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem coeff_sumElim_zero_bquot (g : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hg1 : ∀ (m : Fin d →₀ ℕ) (j : Fin d), coeff (m.sumElim (Finsupp.single j 1)) g = 0)
    (j : Fin d) (m : Fin d →₀ ℕ) : coeff (m.sumElim 0) (bquot g j) = 0 := by
  rw [coeff_bquot]
  split_ifs
  · rw [zero_add, hg1]
  · rfl

end TaylorEval

open TaylorEval in
theorem solution
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (J : Ideal S) [IsAdicComplete J S] {d : ℕ}
    (f : MvPowerSeries (Fin d) R) (Df : Fin d → MvPowerSeries (Fin d) R)
    (hDf : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      (Df j).coeff m = ((m j + 1 : ℕ) : R) * f.coeff (m + Finsupp.single j 1))
    (x z : Fin d → S) (hx : ∀ s, x s ∈ J.radical) (hz : ∀ s, z s ∈ J.radical) :
    MvFormalGroup.adicEval J (x + z) f - MvFormalGroup.adicEval J x f
        - ∑ j, MvFormalGroup.adicEval J x (Df j) * z j ∈ (Ideal.span (Set.range z)) ^ 2 := by
  classical

  let w : Fin d ⊕ Fin d → S := Sum.elim x z
  have hw : ∀ s, w s ∈ J.radical := by rintro (s | s); exacts [hx s, hz s]
  let φ : MvPowerSeries (Fin d ⊕ Fin d) R →ₐ[R] S := MvFormalGroup.adicEvalAlgHom J hw
  have hφ : ∀ g, φ g = MvFormalGroup.adicEval J w g := fun g =>
    congrFun (MvFormalGroup.coe_adicEvalAlgHom (R := R) J hw) g

  let addXZ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R := fun i => X (Sum.inl i) + X (Sum.inr i)
  let g₀ : MvPowerSeries (Fin d ⊕ Fin d) R :=
    subst addXZ f - subst (TaylorEval.inlX d R) f -
      ∑ j, subst (TaylorEval.inlX d R) (Df j) * X (Sum.inr j)

  have hP0f : TaylorEval.P0 d R (subst addXZ f) = f := by
    rw [TaylorEval.P0_apply, subst_comp_subst_apply TaylorEval.hasSubst_addXY TaylorEval.hasSubst_zfam]
    have : (fun s => subst (TaylorEval.zfam d R) (addXZ s)) = (X : Fin d → MvPowerSeries (Fin d) R) := by
      funext s
      rw [← TaylorEval.P0_apply, TaylorEval.P0_addXY]
    rw [this, subst_self]
    rfl
  have hdeg0 : ∀ m : Fin d →₀ ℕ, coeff (m.sumElim 0) g₀ = 0 := by
    intro m
    simp only [g₀, map_sub, map_sum]
    rw [← TaylorEval.coeff_P0, hP0f, TaylorEval.coeff_sumElim_subst_inlX, if_pos rfl, sub_self, zero_sub,
      neg_eq_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [TaylorEval.X_inr_eq, TaylorEval.coeff_sumElim_subst_inlX_mul_subst_inrX,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_X, mul_zero]

  have hdeg1 : ∀ (m : Fin d →₀ ℕ) (j : Fin d), coeff (m.sumElim (Finsupp.single j 1)) g₀ = 0 := by
    intro m j
    simp only [g₀, map_sub, map_sum]
    rw [TaylorEval.coeff_sumElim_single_subst_addXY, TaylorEval.coeff_sumElim_subst_inlX,
      if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), sub_zero]
    have hsum : ∑ j' : Fin d, coeff (m.sumElim (Finsupp.single j 1))
        (subst (TaylorEval.inlX d R) (Df j') * X (Sum.inr j')) = coeff m (Df j) := by
      rw [Finset.sum_eq_single j]
      · rw [TaylorEval.X_inr_eq, TaylorEval.coeff_sumElim_subst_inlX_mul_subst_inrX,
          coeff_index_single_X, if_pos rfl, mul_one]
      · intro j' _ hj'
        rw [TaylorEval.X_inr_eq, TaylorEval.coeff_sumElim_subst_inlX_mul_subst_inrX,
          coeff_index_single_X, if_neg (Ne.symm hj'), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsum, hDf, sub_self]

  have hdec : g₀ = ∑ j : Fin d, X (Sum.inr j) *
      ∑ j' : Fin d, X (Sum.inr j') * TaylorEval.bquot (TaylorEval.bquot g₀ j) j' := by
    conv_lhs => rw [TaylorEval.eq_sum_X_inr_mul_bquot g₀ hdeg0]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact TaylorEval.eq_sum_X_inr_mul_bquot _ (TaylorEval.coeff_sumElim_zero_bquot g₀ hdeg1 j)

  have hmem : φ g₀ ∈ (Ideal.span (Set.range z)) ^ 2 := by
    rw [hdec, map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul, map_sum, Finset.mul_sum]
    refine Ideal.sum_mem _ fun j' _ => ?_
    rw [map_mul, ← mul_assoc, pow_two]
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul ?_ ?_)
    · rw [hφ, MvFormalGroup.adicEval_X]; exact Ideal.subset_span ⟨j, rfl⟩
    · rw [hφ, MvFormalGroup.adicEval_X]; exact Ideal.subset_span ⟨j', rfl⟩

  have hXl : (fun s => MvFormalGroup.adicEval J w (TaylorEval.inlX d R s)) = x := by
    funext s; exact MvFormalGroup.adicEval_X J w (Sum.inl s)
  have hinl : ∀ h : MvPowerSeries (Fin d) R, φ (subst (TaylorEval.inlX d R) h) =
      MvFormalGroup.adicEval J x h := by
    intro h
    rw [hφ, MvFormalGroup.adicEval_subst J hw TaylorEval.hasSubst_inlX, hXl]
  have hadd : φ (subst addXZ f) = MvFormalGroup.adicEval J (x + z) f := by
    rw [hφ, MvFormalGroup.adicEval_subst J hw TaylorEval.hasSubst_addXY]
    congr 1
    funext s
    show MvFormalGroup.adicEval J w (X (Sum.inl s) + X (Sum.inr s)) = x s + z s
    rw [← hφ, map_add, hφ, hφ, MvFormalGroup.adicEval_X, MvFormalGroup.adicEval_X]
    rfl
  have hval : φ g₀ = MvFormalGroup.adicEval J (x + z) f - MvFormalGroup.adicEval J x f
      - ∑ j, MvFormalGroup.adicEval J x (Df j) * z j := by
    simp only [g₀, map_sub, map_sum, map_mul, hadd, hinl]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hφ, MvFormalGroup.adicEval_X]
    rfl
  rw [← hval]
  exact hmem

end S_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq
end P2MW
export P2MW.S_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq (solution)

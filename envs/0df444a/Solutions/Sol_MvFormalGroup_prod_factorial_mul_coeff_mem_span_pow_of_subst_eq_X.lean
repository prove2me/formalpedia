-- Prove2me | solution 1 for MvFormalGroup.prod_factorial_mul_coeff_mem_span_pow_of_subst_eq_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1f7f5c9f-47ed-583b-b93e-ef45dc5fddd1

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_prod_factorial_mul_coeff_mem_span_pow_of_subst_eq_X

set_option autoImplicit false

open MvPowerSeries

universe u

namespace ExpDenom

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

section Hom

variable {F : MvFormalGroup d R} {Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
  {φ ψ : Fin d → MvPowerSeries (Fin d) R}

private noncomputable def σfam (ψ : Fin d → MvPowerSeries (Fin d) R) :
    Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) R :=
  Sum.elim (fun l => subst (inlX d R) (ψ l)) fun l => subst (inrX d R) (ψ l)

private theorem constantCoeff_σfam (hψ0 : ∀ i, (ψ i).constantCoeff = 0) (s : Fin d ⊕ Fin d) :
    (σfam ψ s).constantCoeff = 0 := by
  rcases s with l | l
  · show (subst (inlX d R) (ψ l)).constantCoeff = 0
    rw [constantCoeff_subst_eq_zero hasSubst_inlX (fun j => constantCoeff_X _) (hψ0 l)]
  · show (subst (inrX d R) (ψ l)).constantCoeff = 0
    rw [constantCoeff_subst_eq_zero hasSubst_inrX (fun j => constantCoeff_X _) (hψ0 l)]

private theorem hasSubst_σfam (hψ0 : ∀ i, (ψ i).constantCoeff = 0) : HasSubst (σfam ψ) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_σfam hψ0)

private theorem hasSubst_addXY :
    HasSubst (fun i => (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun i => by rw [map_add, constantCoeff_X, constantCoeff_X, add_zero]

private theorem hom_identity (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (φ i))
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i) (k : Fin d) :
    subst (fun i => (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) (ψ k) =
      subst (σfam ψ) (Fp k) := by
  have hσ := hasSubst_σfam (R := R) hψ0
  have hFpS := hasSubst_of_constantCoeff_zero hFp0
  have hφS := hasSubst_of_constantCoeff_zero hφ0
  have hψS := hasSubst_of_constantCoeff_zero hψ0

  have key : ∀ i, subst (fun s => subst (σfam ψ) (Fp s)) (φ i) =
      (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) := by
    intro i
    rw [← subst_comp_subst_apply hFpS hσ, hφF i, subst_add hσ,
      subst_comp_subst_apply hasSubst_inlX hσ, subst_comp_subst_apply hasSubst_inrX hσ]
    have e1 : (fun j => subst (σfam ψ) (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) R)) =
        fun j => subst (inlX d R) (ψ j) := by
      funext j; rw [subst_X hσ]; rfl
    have e2 : (fun j => subst (σfam ψ) (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) =
        fun j => subst (inrX d R) (ψ j) := by
      funext j; rw [subst_X hσ]; rfl
    rw [e1, e2, ← subst_comp_subst_apply hψS hasSubst_inlX, ← subst_comp_subst_apply hψS hasSubst_inrX,
      hφψ i, subst_X hasSubst_inlX, subst_X hasSubst_inrX]

  have hS2 : HasSubst (fun s => subst (σfam ψ) (Fp s)) :=
    hasSubst_of_constantCoeff_zero fun s =>
      constantCoeff_subst_eq_zero hσ (constantCoeff_σfam hψ0) (hFp0 s)
  calc subst (fun i => (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) (ψ k)
      = subst (fun i => subst (fun s => subst (σfam ψ) (Fp s)) (φ i)) (ψ k) := by
        congr 1; funext i; rw [key]
    _ = subst (fun s => subst (σfam ψ) (Fp s)) (subst φ (ψ k)) := by
        rw [subst_comp_subst_apply hφS hS2]
    _ = subst (σfam ψ) (Fp k) := by rw [hψφ k, subst_X hS2]

end Hom

section Star

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

variable {ψ : Fin d → MvPowerSeries (Fin d) R}

private noncomputable abbrev inlPart (E : (Fin d ⊕ Fin d) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.comapDomain Sum.inl E Sum.inl_injective.injOn

private noncomputable abbrev inrPart (E : (Fin d ⊕ Fin d) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.comapDomain Sum.inr E Sum.inr_injective.injOn

private theorem inlPart_sumElim (a b : Fin d →₀ ℕ) : inlPart (a.sumElim b) = a := by
  ext t; rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inl]

private theorem inrPart_sumElim (a b : Fin d →₀ ℕ) : inrPart (a.sumElim b) = b := by
  ext t; rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inr]

private theorem coeff_single_finsuppProd_pow (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hψ1 : ∀ l j, coeff (Finsupp.single j 1) (ψ l) = if l = j then 1 else 0)
    (b : Fin d →₀ ℕ) (j : Fin d) :
    coeff (Finsupp.single j 1) (b.prod fun l e => ψ l ^ e) = if b = Finsupp.single j 1 then 1 else 0 := by
  classical
  rcases Nat.lt_or_ge b.degree 1 with h0 | h1
  · have hb : b = 0 := (Finsupp.degree_eq_zero_iff b).mp (by omega)
    subst hb
    rw [Finsupp.prod_zero_index, coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero),
      if_neg (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero))]
  rcases Nat.lt_or_ge 1 b.degree with h2 | h2
  · rw [MvFormalGroup.coeff_finsuppProd_pow_eq_zero_of_degree_lt hψ0
      (by rw [Finsupp.degree_single]; exact h2), if_neg]
    intro h
    rw [h, Finsupp.degree_single] at h2
    omega
  ·
    have hb1 : b.degree = 1 := le_antisymm h2 h1
    have hne : b ≠ 0 := fun h => by rw [h, map_zero] at hb1; omega
    obtain ⟨l, hl⟩ : ∃ l, b l ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Finsupp.ext h)
    have hle : Finsupp.single l 1 ≤ b := by rw [Finsupp.single_le_iff]; omega
    obtain ⟨e', he'⟩ := exists_add_of_le hle
    have hdeg : e'.degree = 0 := by
      have := congrArg Finsupp.degree he'
      rw [map_add, Finsupp.degree_single] at this
      omega
    rw [(Finsupp.degree_eq_zero_iff _).mp hdeg, add_zero] at he'
    subst he'
    rw [Finsupp.prod_single_index (h := fun l e => ψ l ^ e) (pow_zero _), pow_one, hψ1]
    by_cases hlj : l = j
    · subst hlj; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hlj, if_neg]
      intro h
      exact hlj (Finsupp.single_left_injective one_ne_zero h)

private theorem coeff_sumElim_single_prod_σfam (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hψ1 : ∀ l j, coeff (Finsupp.single j 1) (ψ l) = if l = j then 1 else 0)
    (j : Fin d) (m : Fin d →₀ ℕ) (E : (Fin d ⊕ Fin d) →₀ ℕ) :
    coeff (m.sumElim (Finsupp.single j 1)) (E.prod fun s e => σfam ψ s ^ e) =
      if inrPart E = Finsupp.single j 1 then coeff m ((inlPart E).prod fun l e => ψ l ^ e)
      else 0 := by
  classical
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin d →₀ ℕ, E = a.sumElim b :=
    ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain E).symm⟩
  rw [inlPart_sumElim, inrPart_sumElim, Finsupp.prod_sumElim]
  have h1 : (a.prod fun l e => ((fun s e => σfam ψ s ^ e) ∘ Sum.inl) l e) =
      subst (inlX d R) (a.prod fun l e => ψ l ^ e) := by
    rw [← coe_substAlgHom hasSubst_inlX, map_finsuppProd]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [Function.comp_apply, map_pow, coe_substAlgHom]
    rfl
  have h2 : (b.prod fun l e => ((fun s e => σfam ψ s ^ e) ∘ Sum.inr) l e) =
      subst (inrX d R) (b.prod fun l e => ψ l ^ e) := by
    rw [← coe_substAlgHom hasSubst_inrX, map_finsuppProd]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [Function.comp_apply, map_pow, coe_substAlgHom]
    rfl
  rw [h1, h2, coeff_sumElim_subst_inlX_mul_subst_inrX, coeff_single_finsuppProd_pow hψ0 hψ1,
    mul_ite, mul_one, mul_zero]

end Star

section Induction

private theorem fac_eq_prod (m : Fin d →₀ ℕ) :
    (m.prod fun _ k => k.factorial) = ∏ i : Fin d, (m i).factorial :=
  Finsupp.prod_fintype _ _ fun _ => Nat.factorial_zero

private theorem fac_add_single (m : Fin d →₀ ℕ) (j : Fin d) :
    ((m + Finsupp.single j 1).prod fun _ k => k.factorial) =
      (m.prod fun _ k => k.factorial) * (m j + 1) := by
  classical
  rw [fac_eq_prod, fac_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => (m i).factorial) (Finset.mem_univ j),
    Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  have h : ∏ i ∈ Finset.univ.erase j, ((m + Finsupp.single j 1 : Fin d →₀ ℕ) i).factorial =
      ∏ i ∈ Finset.univ.erase j, (m i).factorial := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hi).symm, add_zero]
  rw [h]
  ring

private theorem prod_fac_dvd_fac {ι : Type*} (s : Finset ι) (v : ι → (Fin d →₀ ℕ))
    (m : Fin d →₀ ℕ) (hv : ∑ x ∈ s, v x = m) :
    (∏ x ∈ s, (v x).prod fun _ k => k.factorial) ∣ m.prod fun _ k => k.factorial := by
  classical
  simp_rw [fac_eq_prod]
  rw [Finset.prod_comm]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  have h : (∑ x ∈ s, v x) i = m i := by rw [hv]
  rw [Finsupp.finsetSum_apply] at h
  rw [← h]
  exact Nat.prod_factorial_dvd_factorial_sum _ _

variable {ψ : Fin d → MvPowerSeries (Fin d) R} (p : ℕ)

private theorem fac_mul_coeff_prod_mem {ι : Type*} [DecidableEq ι] (s : Finset ι) (l : ι → Fin d)
    (m' : Fin d →₀ ℕ) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (IH : ∀ m'' : Fin d →₀ ℕ, m''.degree ≤ m'.degree → m'' ≠ 0 → ∀ k,
      ((m''.prod fun _ n => n.factorial : ℕ) : R) * coeff m'' (ψ k) ∈
        Ideal.span {(p : R) ^ (m''.degree - 1)}) :
    ((m'.prod fun _ n => n.factorial : ℕ) : R) * coeff m' (∏ x ∈ s, ψ (l x)) ∈
      Ideal.span {(p : R) ^ (m'.degree - s.card)} := by
  classical
  rw [coeff_prod, Finset.mul_sum]
  refine Ideal.sum_mem _ fun v hv => ?_
  rw [Finset.mem_finsuppAntidiag] at hv
  obtain ⟨hsum, hsupp⟩ := hv
  by_cases hz : ∃ x ∈ s, v x = 0
  · obtain ⟨x, hx, hx0⟩ := hz
    rw [Finset.prod_eq_zero hx (by rw [hx0, coeff_zero_eq_constantCoeff_apply, hψ0]), mul_zero]
    exact Ideal.zero_mem _
  push Not at hz

  have hfac : ∀ x ∈ s, ∃ y : R, ((((v x).prod fun _ n => n.factorial : ℕ) : R)) * coeff (v x) (ψ (l x))
      = (p : R) ^ ((v x).degree - 1) * y := by
    intro x hx
    have hdeg : (v x).degree ≤ m'.degree := by
      rw [← hsum, map_sum]
      exact Finset.single_le_sum (f := fun x => (v x).degree) (fun _ _ => Nat.zero_le _) hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (IH (v x) hdeg (hz x hx) (l x))
    exact ⟨y, by rw [← hy, mul_comm]⟩
  choose! y hy using hfac
  obtain ⟨q, hq⟩ := prod_fac_dvd_fac s v m' hsum
  rw [hq, Nat.cast_mul, Nat.cast_prod, mul_assoc, mul_left_comm, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl hy, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hexp : ∑ x ∈ s, ((v x).degree - 1) = m'.degree - s.card := by
    rw [Finset.sum_tsub_distrib _ (fun x hx => ?_), ← map_sum, hsum, Finset.card_eq_sum_ones]
    rcases Nat.eq_zero_or_pos (v x).degree with h | h
    · exact absurd ((Finsupp.degree_eq_zero_iff _).mp h) (hz x hx)
    · exact h
  rw [hexp]
  exact Ideal.mem_span_singleton'.mpr ⟨(q : R) * ∏ x ∈ s, y x, by ring⟩

private theorem finsuppProd_pow_eq_prod_sigma (a : Fin d →₀ ℕ) :
    (a.prod fun l e => ψ l ^ e) = ∏ x ∈ a.support.sigma fun l => Finset.range (a l), ψ x.1 := by
  rw [Finset.prod_sigma]
  refine Finset.prod_congr rfl fun l _ => ?_
  dsimp only
  rw [Finset.prod_const, Finset.card_range]

private theorem card_sigma_range (a : Fin d →₀ ℕ) :
    (a.support.sigma fun l => Finset.range (a l)).card = a.degree := by
  rw [Finset.card_sigma, Finsupp.degree_apply]
  exact Finset.sum_congr rfl fun l _ => Finset.card_range _

end Induction

end ExpDenom

open ExpDenom in
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
    (ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hψφ : ∀ i, subst φ (ψ i) = X i)
    (hφψ : ∀ i, subst ψ (φ i) = X i)
    (i : Fin d) (m : Fin d →₀ ℕ) (hm : m ≠ 0) :
    ((m.prod fun _ k => k.factorial : ℕ) : 𝓞) * (ψ i).coeff m ∈
      Ideal.span {(p : 𝓞) ^ (m.degree - 1)} := by
  classical

  have hψ1 : ∀ l j, coeff (Finsupp.single j 1) (ψ l) = if l = j then 1 else 0 := by
    intro l j
    have h := congrArg (coeff (Finsupp.single j 1)) (hψφ l)
    rw [MvFormalGroup.coeff_single_subst hφ0 (ψ l) j] at h
    have hφlin : ∀ s, coeff (Finsupp.single j 1) (φ s) = if s = j then 1 else 0 := fun s => by
      have := congrFun (congrFun hφ1 s) j
      simpa [MvFormalGroup.linearPart, Matrix.one_apply] using this
    simp only [hφlin, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      coeff_index_single_X] at h
    rw [h]
    by_cases hlj : l = j
    · subst hlj; simp
    · simp [hlj, Ne.symm hlj]

  have star : ∀ (k j : Fin d) (m' : Fin d →₀ ℕ),
      ((m' j + 1 : ℕ) : 𝓞) * coeff (m' + Finsupp.single j 1) (ψ k) =
        ∑ᶠ E : (Fin d ⊕ Fin d) →₀ ℕ, coeff E (Fp k) •
          coeff (m'.sumElim (Finsupp.single j 1)) (E.prod fun s e => ExpDenom.σfam ψ s ^ e) := by
    intro k j m'
    rw [← ExpDenom.coeff_sumElim_single_subst_addXY,
      ExpDenom.hom_identity hFp0 hφ0 hφF hψ0 hψφ hφψ k,
      coeff_subst (ExpDenom.hasSubst_σfam hψ0)]

  suffices main : ∀ N : ℕ, ∀ m : Fin d →₀ ℕ, m.degree = N → m ≠ 0 → ∀ k : Fin d,
      ((m.prod fun _ n => n.factorial : ℕ) : 𝓞) * coeff m (ψ k) ∈
        Ideal.span {(p : 𝓞) ^ (N - 1)} by
    exact main m.degree m rfl hm i
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHN =>
  intro m hmN hm0 k

  obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
    by_contra h
    push Not at h
    exact hm0 (Finsupp.ext h)
  set m' := m - Finsupp.single j 1 with hm'
  have hmm' : m = m' + Finsupp.single j 1 := by
    rw [hm', tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]; omega
  have hdeg' : m'.degree = N - 1 := by
    have := congrArg Finsupp.degree hmm'
    rw [map_add, Finsupp.degree_single, hmN] at this
    omega
  have IH : ∀ m'' : Fin d →₀ ℕ, m''.degree ≤ m'.degree → m'' ≠ 0 → ∀ k,
      ((m''.prod fun _ n => n.factorial : ℕ) : 𝓞) * coeff m'' (ψ k) ∈
        Ideal.span {(p : 𝓞) ^ (m''.degree - 1)} := by
    intro m'' hle hne k'
    have hlt : m''.degree < N := by
      have h1 : 1 ≤ N := by
        rw [← hmN]
        rcases Nat.eq_zero_or_pos m.degree with h | h
        · exact absurd ((Finsupp.degree_eq_zero_iff m).mp h) hm0
        · exact h
      omega
    exact IHN m''.degree hlt m'' rfl hne k'
  rw [hmm', ExpDenom.fac_add_single, Nat.cast_mul, mul_assoc, star k j m']

  have hfin := coeff_subst_finite (ExpDenom.hasSubst_σfam hψ0) (Fp k)
    (m'.sumElim (Finsupp.single j 1))
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp), Finset.mul_sum]
  refine Ideal.sum_mem _ fun E _ => ?_
  rw [ExpDenom.coeff_sumElim_single_prod_σfam hψ0 hψ1, smul_eq_mul]
  split_ifs with hE
  ·
    have hEeq : E = (ExpDenom.inlPart E).sumElim (Finsupp.single j 1) := by
      rw [← hE]; exact (Finsupp.comapDomain_sumElim_comapDomain E).symm
    set a := ExpDenom.inlPart E with ha
    have hE0 : E ≠ 0 := by
      intro h
      have := congrArg ExpDenom.inrPart h
      rw [hE] at this
      exact Finsupp.single_ne_zero.mpr one_ne_zero (by
        rw [this]; ext t; rw [Finsupp.comapDomain_apply]; rfl)
    have hEdeg : E.degree = a.degree + 1 := by
      rw [hEeq, ExpDenom.degree_sumElim, Finsupp.degree_single]
    rw [ExpDenom.coeff_Fp hp hFp k hE0, hEdeg, Nat.add_sub_cancel]
    rcases Nat.lt_or_ge m'.degree a.degree with hlt | hge
    · rw [MvFormalGroup.coeff_finsuppProd_pow_eq_zero_of_degree_lt hψ0 hlt, mul_zero, mul_zero]
      exact Ideal.zero_mem _
    · have hQ := ExpDenom.fac_mul_coeff_prod_mem p (a.support.sigma fun l => Finset.range (a l))
        (fun x => x.1) m' hψ0 IH
      rw [← ExpDenom.finsuppProd_pow_eq_prod_sigma, ExpDenom.card_sigma_range] at hQ
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hQ
      rw [hdeg'] at hy
      refine Ideal.mem_span_singleton'.mpr ⟨coeff E (F.toPowerSeries k) * y, ?_⟩
      have hre : ((m'.prod fun _ n => n.factorial : ℕ) : 𝓞) *
          ((p : 𝓞) ^ a.degree * coeff E (F.toPowerSeries k) * coeff m' (a.prod fun l e => ψ l ^ e))
          = (p : 𝓞) ^ a.degree * coeff E (F.toPowerSeries k) *
            (((m'.prod fun _ n => n.factorial : ℕ) : 𝓞) * coeff m' (a.prod fun l e => ψ l ^ e)) := by
        ring
      rw [hre, ← hy,
        show (p : 𝓞) ^ (N - 1) = (p : 𝓞) ^ a.degree * (p : 𝓞) ^ (N - 1 - a.degree) by
          rw [← pow_add]; congr 1; omega]
      ring
  · rw [mul_zero, mul_zero]
    exact Ideal.zero_mem _

end S_MvFormalGroup_prod_factorial_mul_coeff_mem_span_pow_of_subst_eq_X
end P2MW
export P2MW.S_MvFormalGroup_prod_factorial_mul_coeff_mem_span_pow_of_subst_eq_X (solution)

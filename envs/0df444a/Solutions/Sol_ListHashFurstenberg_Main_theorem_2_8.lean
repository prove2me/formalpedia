-- Prove2me | solution 1 for ListHashFurstenberg.Main.theorem_2_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:17:39.540999+00:00
-- url     : https://prove2.me/submissions/0f6e7d29-74ec-40df-95ff-a147cf05bfc2

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg
section
set_option autoImplicit false

namespace ListHashFurstenberg.Main.Dev.GLTool

open Module

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

set_option linter.unusedSectionVars false

instance finite_submodule : Finite (Submodule F (Fin n → F)) :=
  Finite.of_injective (fun U : Submodule F (Fin n → F) => (U : Set (Fin n → F)))
    SetLike.coe_injective

instance finite_linearEquiv : Finite ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
  Finite.of_injective
    (fun g : (Fin n → F) ≃ₗ[F] (Fin n → F) => (g : (Fin n → F) → (Fin n → F)))
    (fun _ _ e => LinearEquiv.ext (congrFun e))

noncomputable instance fintype_submodule : Fintype (Submodule F (Fin n → F)) :=
  Fintype.ofFinite _

noncomputable instance fintype_linearEquiv : Fintype ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
  Fintype.ofFinite _

open Classical in
/-- `U` has a translate meeting `S` in at least `T` points. -/
def Rich (T : ℝ) (S : Finset (Fin n → F)) (U : Submodule F (Fin n → F)) : Prop :=
  ∃ x : Fin n → F, T ≤ ((S.filter fun s => s - x ∈ U).card : ℝ)

/-- The `r`-dimensional subspaces of `F^n`. -/
noncomputable def Gr (F : Type*) [Field F] [Fintype F] (n r : ℕ) :
    Finset (Submodule F (Fin n → F)) :=
  Finset.univ.filter (fun U => finrank F U = r)

theorem mem_Gr {r : ℕ} {U : Submodule F (Fin n → F)} : U ∈ Gr F n r ↔ finrank F U = r := by
  simp [Gr]

open Classical in
theorem richFraction_eq (r : ℕ) (T : ℝ) (S : Finset (Fin n → F)) :
    richFraction n r T S =
      (((Gr F n r).filter (Rich T S)).card : ℝ) / ((Gr F n r).card : ℝ) := by
  have e : richFraction n r T S =
      (Nat.card {U : Submodule F (Fin n → F) // finrank F U = r ∧ Rich T S U} : ℝ) /
        (Nat.card {U : Submodule F (Fin n → F) // finrank F U = r} : ℝ) := rfl
  rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype, Gr, Finset.filter_filter]

theorem richFraction_eq_zero (r : ℕ) (T : ℝ) (S : Finset (Fin n → F))
    (h : (Gr F n r).card = 0) : richFraction n r T S = 0 := by
  classical
  rw [richFraction_eq, h, Nat.cast_zero, div_zero]

theorem map_trans (W : Submodule F (Fin n → F)) (g h : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    W.map (g.trans h).toLinearMap = (W.map g.toLinearMap).map h.toLinearMap := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem map_refl (W : Submodule F (Fin n → F)) :
    W.map (LinearEquiv.refl F (Fin n → F)).toLinearMap = W := by
  ext x
  simp

theorem map_map_symm (W : Submodule F (Fin n → F)) (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    (W.map g.toLinearMap).map g.symm.toLinearMap = W := by
  rw [← map_trans, LinearEquiv.self_trans_symm, map_refl]

/-- Transitivity of `GL_n` on subspaces of equal dimension. -/
theorem exists_map_eq {W U : Submodule F (Fin n → F)} (h : finrank F W = finrank F U) :
    ∃ g : (Fin n → F) ≃ₗ[F] (Fin n → F), W.map g.toLinearMap = U := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl U
  have h1 := Submodule.finrank_add_eq_of_isCompl hC
  have h2 := Submodule.finrank_add_eq_of_isCompl hD
  have hCD : finrank F C = finrank F D := by omega
  let e1 : W ≃ₗ[F] U := LinearEquiv.ofFinrankEq W U h
  let e2 : C ≃ₗ[F] D := LinearEquiv.ofFinrankEq C D hCD
  let g : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (Submodule.prodEquivOfIsCompl W C hC).symm.trans
      ((e1.prodCongr e2).trans (Submodule.prodEquivOfIsCompl U D hD))
  refine ⟨g, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ W := hw
    have e : (g : (Fin n → F) →ₗ[F] (Fin n → F)) w = (e1 ⟨w, hw'⟩ : Fin n → F) := by
      change (Submodule.prodEquivOfIsCompl U D hD) ((e1.prodCongr e2)
        ((Submodule.prodEquivOfIsCompl W C hC).symm ((⟨w, hw'⟩ : ↥W) : Fin n → F))) = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left (h := hC) (x := (⟨w, hw'⟩ : ↥W))]
      simp
    rw [e]
    exact (e1 ⟨w, hw'⟩).2
  · rw [LinearEquiv.finrank_map_eq, h]

theorem card_fiber_eq {r : ℕ} {W U : Submodule F (Fin n → F)} (hW : finrank F W = r)
    (hU : finrank F U = r) :
    (Finset.univ.filter fun g : (Fin n → F) ≃ₗ[F] (Fin n → F) => W.map g.toLinearMap = U).card =
      (Finset.univ.filter fun g : (Fin n → F) ≃ₗ[F] (Fin n → F) => W.map g.toLinearMap = W).card := by
  obtain ⟨g0, hg0⟩ := exists_map_eq (hW.trans hU.symm)
  refine Finset.card_bij' (fun (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) _ => g.trans g0.symm)
    (fun (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) _ => g.trans g0) ?_ ?_ ?_ ?_
  · intro g hg
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [map_trans, (Finset.mem_filter.mp hg).2, ← hg0, map_map_symm]
  · intro g hg
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [map_trans, (Finset.mem_filter.mp hg).2, hg0]
  · intro g _
    ext x
    simp
  · intro g _
    ext x
    simp

/-- **Averaging over `GL_n`**: `g ↦ g(W)` hits every `r`-dimensional subspace equally often. -/
theorem sum_map_mul {r : ℕ} {W : Submodule F (Fin n → F)} (hW : finrank F W = r)
    (f : Submodule F (Fin n → F) → ℝ) :
    (∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F), f (W.map g.toLinearMap)) * (Gr F n r).card =
      (Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) : ℝ) * ∑ U ∈ Gr F n r, f U := by
  classical
  set c := (Finset.univ.filter fun g : (Fin n → F) ≃ₗ[F] (Fin n → F) => W.map g.toLinearMap = W).card
    with hc
  have hmaps : ∀ g ∈ (Finset.univ : Finset ((Fin n → F) ≃ₗ[F] (Fin n → F))),
      W.map g.toLinearMap ∈ Gr F n r := by
    intro g _
    rw [mem_Gr, LinearEquiv.finrank_map_eq, hW]
  have hsum : ∀ φ : Submodule F (Fin n → F) → ℝ,
      ∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F), φ (W.map g.toLinearMap) = ∑ U ∈ Gr F n r, (c : ℝ) * φ U := by
    intro φ
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro U hU
    rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2]),
      Finset.sum_const, nsmul_eq_mul, card_fiber_eq hW (mem_Gr.mp hU)]
  have hcard : (Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) : ℝ) =
      (c : ℝ) * (Gr F n r).card := by
    have := hsum (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [this, mul_comm]
  rw [hsum f, hcard, ← Finset.mul_sum]
  ring

/-- Every subspace of dimension `k` lies in one of every dimension `k + d ≤ n`. -/
theorem exists_le_finrank (d : ℕ) :
    ∀ K : Submodule F (Fin n → F), finrank F K + d ≤ n →
      ∃ W : Submodule F (Fin n → F), K ≤ W ∧ finrank F W = finrank F K + d := by
  induction d with
  | zero => intro K _; exact ⟨K, le_rfl, rfl⟩
  | succ d ih =>
    intro K hd
    have hne : K ≠ ⊤ := by
      intro h
      rw [h, finrank_top, Module.finrank_fin_fun] at hd
      omega
    obtain ⟨v, hv⟩ : ∃ v, v ∉ K := by
      by_contra hc
      push Not at hc
      exact hne (eq_top_iff.mpr fun x _ => hc x)
    have hK' := Submodule.finrank_sup_span_singleton hv
    obtain ⟨W, hW1, hW2⟩ := ih (K ⊔ Submodule.span F {v}) (by rw [hK']; omega)
    exact ⟨W, le_trans le_sup_left hW1, by rw [hW2, hK']; ring⟩

end ListHashFurstenberg.Main.Dev.GLTool
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP
/-- Taylor shift `P(a + X)`. -/
noncomputable def shift {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R)
    (P : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  aeval (fun i => C (a i) + X i) P

/-- `P` vanishes to order at least `m` at `a`: every monomial of `P(a + X)` has degree `≥ m`. -/
def MultGe {R : Type*} [CommRing R] {n : ℕ} (P : MvPolynomial (Fin n) R) (a : Fin n → R)
    (m : ℕ) : Prop :=
  ∀ s ∈ (shift a P).support, m ≤ s.degree

/-- The point `b + B t` with coordinates in `F[t_1, …, t_r]`. -/
noncomputable def affPt {F : Type*} [Field F] {n r : ℕ} (b : Fin n → F)
    (B : Fin n → Fin r → F) : Fin n → MvPolynomial (Fin r) F :=
  fun k => C (b k) + ∑ j, C (B k j) * X j

open Classical in
/-- The column map `t ↦ V t` lands in an `r`-dimensional subspace with a `T`-rich shift. -/
def GoodMat {F : Type*} [Field F] {n : ℕ} (r : ℕ) (T : ℝ) (S : Finset (Fin n → F))
    (V : Fin n → Fin r → F) : Prop :=
  ∃ W : Submodule F (Fin n → F), Module.finrank F W = r ∧
    (∀ t : Fin r → F, (fun k => ∑ j, V k j * t j) ∈ W) ∧
    ∃ x : Fin n → F, T ≤ ((S.filter fun s => s - x ∈ W).card : ℝ)

end ListHashFurstenberg.Main.Dev.BP
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartSZ
open ListHashFurstenberg.Main.Dev.BP
theorem shift_neg_shift {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R)
    (P : MvPolynomial (Fin n) R) : shift (-a) (shift a P) = P := by
  unfold shift
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have : (fun i => aeval (fun i => C ((-a) i) + X i) (C (a i) + X i : MvPolynomial (Fin n) R)) =
      X := by
    funext i; simp
  rw [this, aeval_X_left_apply]

theorem shift_ne_zero {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R)
    (P : MvPolynomial (Fin n) R) (hP : P ≠ 0) : shift a P ≠ 0 := by
  intro h
  apply hP
  rw [← shift_neg_shift a P, h]
  simp [shift]

/-- The shift as a ring hom. -/
noncomputable def shiftHom {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R :=
  (aeval (fun i => C (a i) + X i) : MvPolynomial (Fin n) R →ₐ[R] _).toRingHom

theorem shiftHom_apply {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R)
    (P : MvPolynomial (Fin n) R) : shiftHom a P = shift a P := rfl

theorem finSuccEquiv_shift_cons {R : Type*} [CommRing R] {n : ℕ} (c : R) (a' : Fin n → R)
    (P : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n (shift (Fin.cons c a') P) =
      Polynomial.taylor (C c) (Polynomial.map (shiftHom a') (finSuccEquiv R n P)) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    simp [shift, shiftHom, finSuccEquiv_apply]
  | add p q hp hq =>
    simp only [shift, map_add, Polynomial.map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    have hC : ∀ r : R, finSuccEquiv R n (C r) = Polynomial.C (C r) := fun r => by
      simp [finSuccEquiv_apply]
    have hX : finSuccEquiv R n (shift (Fin.cons c a') (X i)) =
        Polynomial.taylor (C c) (Polynomial.map (shiftHom a') (finSuccEquiv R n (X i))) := by
      rw [shift, aeval_X]
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [Fin.cons_zero, map_add, hC, finSuccEquiv_X_zero, Polynomial.map_X,
          Polynomial.taylor_X, add_comm]
      · rw [Fin.cons_succ, map_add, hC, finSuccEquiv_X_succ, Polynomial.map_C,
          Polynomial.taylor_C, shiftHom_apply, shift, aeval_X, Polynomial.C_add]
    rw [shift] at hp hX
    rw [shift, map_mul, map_mul, hp, hX, map_mul (finSuccEquiv R n), Polynomial.map_mul,
      Polynomial.taylor_mul]

theorem coeff_shift_cons {R : Type*} [CommRing R] {n : ℕ} (c : R) (a' : Fin n → R)
    (P : MvPolynomial (Fin (n + 1)) R) (j : ℕ) (m : Fin n →₀ ℕ) :
    coeff (Finsupp.cons j m) (shift (Fin.cons c a') P) =
      coeff m ((Polynomial.taylor (C c)
        (Polynomial.map (shiftHom a') (finSuccEquiv R n P))).coeff j) := by
  rw [← finSuccEquiv_coeff_coeff, finSuccEquiv_shift_cons]

theorem degree_cons {n : ℕ} (j : ℕ) (m : Fin n →₀ ℕ) :
    (Finsupp.cons j m).degree = j + m.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  simp [Finsupp.cons_zero, Finsupp.cons_succ]

/-- Extract the coefficient of `X^i'` from each coefficient. -/
noncomputable def extr {R : Type*} [CommRing R] {n : ℕ} (i' : Fin n →₀ ℕ)
    (G : Polynomial (MvPolynomial (Fin n) R)) : Polynomial R :=
  ∑ j ∈ Finset.range (G.natDegree + 1), Polynomial.monomial j (coeff i' (G.coeff j))

theorem coeff_extr {R : Type*} [CommRing R] {n : ℕ} (i' : Fin n →₀ ℕ)
    (G : Polynomial (MvPolynomial (Fin n) R)) (k : ℕ) :
    (extr i' G).coeff k = coeff i' (G.coeff k) := by
  simp only [extr, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at h; omega), coeff_zero]

theorem natDegree_extr_le {R : Type*} [CommRing R] {n : ℕ} (i' : Fin n →₀ ℕ)
    (G : Polynomial (MvPolynomial (Fin n) R)) : (extr i' G).natDegree ≤ G.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_extr, Polynomial.coeff_eq_zero_of_natDegree_lt hN, coeff_zero]

theorem taylor_coeff_sum {T : Type*} [CommRing T] (r : T) (f : Polynomial T) (N : ℕ)
    (hN : f.natDegree < N) (k : ℕ) :
    (Polynomial.taylor r f).coeff k =
      ∑ i ∈ Finset.range N, f.coeff i * ((Polynomial.X + Polynomial.C r) ^ i).coeff k := by
  conv_lhs => rw [f.as_sum_range' N hN]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp [Polynomial.taylor_monomial, Polynomial.coeff_C_mul]

theorem coeff_taylor_extr {R : Type*} [CommRing R] {n : ℕ} (i' : Fin n →₀ ℕ)
    (G : Polynomial (MvPolynomial (Fin n) R)) (c : R) (k : ℕ) :
    (Polynomial.taylor c (extr i' G)).coeff k =
      coeff i' ((Polynomial.taylor (C c) G).coeff k) := by
  rw [taylor_coeff_sum c _ (G.natDegree + 1) (by have := natDegree_extr_le i' G; omega),
    taylor_coeff_sum (C c) G (G.natDegree + 1) (by omega), coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmap : ((Polynomial.X + Polynomial.C (C c)) ^ i : Polynomial (MvPolynomial (Fin n) R)) =
      Polynomial.map C ((Polynomial.X + Polynomial.C c) ^ i) := by
    simp [Polynomial.map_pow]
  rw [hmap, Polynomial.coeff_map, mul_comm (G.coeff i), coeff_C_mul, coeff_extr, mul_comm]

theorem sum_rootMultiplicity_le {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (S : Finset R) (g : Polynomial R) :
    ∑ c ∈ S, g.rootMultiplicity c ≤ g.natDegree := by
  calc ∑ c ∈ S, g.rootMultiplicity c = ∑ c ∈ S, g.roots.count c := by
        simp [Polynomial.count_roots]
    _ ≤ ∑ c ∈ S ∪ g.roots.toFinset, g.roots.count c :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = Multiset.card g.roots :=
        Multiset.sum_count_eq_card (fun a ha => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ g.natDegree := Polynomial.card_roots' g

theorem fiber_bound {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {n : ℕ}
    (S : Finset R) (P : MvPolynomial (Fin (n + 1)) R) (a' : Fin n → R) (μ : R → ℕ)
    (hμ : ∀ c ∈ S, MultGe P (Fin.cons c a') (μ c)) (i' : Fin n →₀ ℕ)
    (hi' : i' ∈ (shift a' (finSuccEquiv R n P).leadingCoeff).support) :
    ∑ c ∈ S, μ c ≤ S.card * i'.degree + (finSuccEquiv R n P).natDegree := by
  set t := (finSuccEquiv R n P).natDegree with ht
  set G := Polynomial.map (shiftHom a') (finSuccEquiv R n P) with hG
  set g := extr i' G with hg
  have hgt : g.coeff t ≠ 0 := by
    rw [hg, coeff_extr, hG, Polynomial.coeff_map, shiftHom_apply]
    exact mem_support_iff.mp hi'
  have hg0 : g ≠ 0 := fun h => hgt (by rw [h, Polynomial.coeff_zero])
  have hgdeg : g.natDegree ≤ t := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hg, coeff_extr, hG, Polynomial.coeff_map,
      Polynomial.coeff_eq_zero_of_natDegree_lt hN, map_zero, coeff_zero]
  have hroot : ∀ c ∈ S, μ c - i'.degree ≤ g.rootMultiplicity c := by
    intro c hc
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree, ← Polynomial.taylor_apply]
    apply Polynomial.le_natTrailingDegree
    · intro h
      apply hg0
      apply Polynomial.taylor_injective c
      rw [h, map_zero]
    · intro m hm
      rw [hg, coeff_taylor_extr, hG, ← coeff_shift_cons]
      by_contra hne
      have := hμ c hc _ (mem_support_iff.mpr hne)
      rw [degree_cons] at this
      omega
  calc ∑ c ∈ S, μ c ≤ ∑ c ∈ S, ((μ c - i'.degree) + i'.degree) :=
        Finset.sum_le_sum (fun c _ => by omega)
    _ = ∑ c ∈ S, (μ c - i'.degree) + S.card * i'.degree := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ c ∈ S, g.rootMultiplicity c + S.card * i'.degree :=
        Nat.add_le_add_right (Finset.sum_le_sum hroot) _
    _ ≤ t + S.card * i'.degree :=
        Nat.add_le_add_right (le_trans (sum_rootMultiplicity_le S g) hgdeg) _
    _ = S.card * i'.degree + t := by ring

theorem sum_piFinset_succ {R : Type*} [DecidableEq R] {n : ℕ} (S : Finset R)
    (f : (Fin (n + 1) → R) → ℕ) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), f a =
      ∑ a' ∈ Fintype.piFinset (fun _ : Fin n => S), ∑ c ∈ S, f (Fin.cons c a') := by
  rw [← Finset.sum_product_right (f := fun p : R × (Fin n → R) => f (Fin.cons p.1 p.2))]
  symm
  apply Finset.sum_bij' (fun p _ => (Fin.cons p.1 p.2 : Fin (n + 1) → R))
    (fun a _ => (a 0, Fin.tail a))
  · intro p hp
    rw [Finset.mem_product] at hp
    rw [Fintype.mem_piFinset]
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using hp.1
    · simpa using (Fintype.mem_piFinset.mp hp.2) k
  · intro a ha
    rw [Fintype.mem_piFinset] at ha
    rw [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨ha 0, fun k => ha k.succ⟩
  · intro p _
    simp
  · intro a _
    simp
  · intro p _
    rfl

theorem sum_le_of_multGe {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] (n : ℕ)
    (S : Finset R) (P : MvPolynomial (Fin n) R) (hP : P ≠ 0) (μ : (Fin n → R) → ℕ)
    (hμ : ∀ a ∈ Fintype.piFinset (fun _ : Fin n => S), MultGe P a (μ a)) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin n => S), μ a) * S.card ≤
      P.totalDegree * S.card ^ n := by
  induction n with
  | zero =>
    have h0 : ∀ a ∈ Fintype.piFinset (fun _ : Fin 0 => S), μ a = 0 := by
      intro a ha
      obtain ⟨s, hs⟩ := support_nonempty.mpr (shift_ne_zero a P hP)
      have := hμ a ha s hs
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_zero] at this
      omega
    rw [Finset.sum_eq_zero h0]
    simp
  | succ n ih =>
    classical
    set Q := finSuccEquiv R n P with hQ
    have hQ0 : Q ≠ 0 := by
      intro h
      apply hP
      rw [← (finSuccEquiv R n).symm_apply_apply P]
      rw [← hQ, h, map_zero]
    set Pt := Q.leadingCoeff with hPt
    have hPt0 : Pt ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
    set t := Q.natDegree with ht
    have hex : ∀ a' : Fin n → R, ∃ i' ∈ (shift a' Pt).support,
        ∀ s ∈ (shift a' Pt).support, i'.degree ≤ s.degree := fun a' =>
      Finset.exists_min_image _ _ (support_nonempty.mpr (shift_ne_zero a' Pt hPt0))
    choose i hi hmin using hex
    have hIH := ih Pt hPt0 (fun a' => (i a').degree) (fun a' _ s hs => hmin a' s hs)
    have hdeg : Pt.totalDegree + t ≤ P.totalDegree :=
      totalDegree_coeff_finSuccEquiv_add_le P t hPt0
    have hfib : ∀ a' ∈ Fintype.piFinset (fun _ : Fin n => S),
        ∑ c ∈ S, μ (Fin.cons c a') ≤ S.card * (i a').degree + t := by
      intro a' ha'
      apply fiber_bound S P a' (fun c => μ (Fin.cons c a'))
      · intro c hc
        apply hμ
        rw [Fintype.mem_piFinset]
        intro k
        refine Fin.cases ?_ (fun k => ?_) k
        · simpa using hc
        · simpa using (Fintype.mem_piFinset.mp ha') k
      · exact hi a'
    have hcard : (Fintype.piFinset (fun _ : Fin n => S)).card = S.card ^ n := by
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [sum_piFinset_succ]
    set k := S.card
    set sν := ∑ a' ∈ Fintype.piFinset (fun _ : Fin n => S), (i a').degree
    have h1 : ∑ a' ∈ Fintype.piFinset (fun _ : Fin n => S), ∑ c ∈ S, μ (Fin.cons c a') ≤
        k * sν + k ^ n * t := by
      calc _ ≤ ∑ a' ∈ Fintype.piFinset (fun _ : Fin n => S), (k * (i a').degree + t) :=
            Finset.sum_le_sum hfib
        _ = k * sν + k ^ n * t := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, smul_eq_mul]
    calc _ ≤ (k * sν + k ^ n * t) * k := Nat.mul_le_mul_right _ h1
      _ = k * (sν * k) + t * k ^ (n + 1) := by ring
      _ ≤ k * (Pt.totalDegree * k ^ n) + t * k ^ (n + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hIH) _
      _ = (Pt.totalDegree + t) * k ^ (n + 1) := by ring
      _ ≤ P.totalDegree * k ^ (n + 1) := Nat.mul_le_mul_right _ hdeg

end ListHashFurstenberg.Main.Dev.BP.PartSZ
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP
/-! ### Stubs (proved in the Parts) -/
alias sum_le_of_multGe := ListHashFurstenberg.Main.Dev.BP.PartSZ.sum_le_of_multGe

end ListHashFurstenberg.Main.Dev.BP
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartCnt
open ListHashFurstenberg.Main.Dev.BP
/-- Exponents of degree `< m`. -/
noncomputable def expLt (n m : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.range m).biUnion (fun k => (Finset.univ : Finset (Fin n)).finsuppAntidiag k)

theorem mem_expLt (n m : ℕ) (s : Fin n →₀ ℕ) : s ∈ expLt n m ↔ s.degree < m := by
  simp [expLt, Finsupp.degree_eq_sum]

theorem card_expLt (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    (expLt n m).card = (m + n - 1).choose n := by
  induction m with
  | zero => simp [expLt, Nat.choose_eq_zero_of_lt (show n - 1 < n by omega)]
  | succ m ih =>
    have hdisj : Disjoint (expLt n m) ((Finset.univ : Finset (Fin n)).finsuppAntidiag m) := by
      rw [Finset.disjoint_left]
      intro s hs hs'
      rw [mem_expLt] at hs
      rw [Finset.mem_finsuppAntidiag] at hs'
      rw [Finsupp.degree_eq_sum, hs'.1] at hs
      omega
    have heq : expLt n (m + 1) = expLt n m ∪ (Finset.univ : Finset (Fin n)).finsuppAntidiag m := by
      simp [expLt, Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
    rw [heq, Finset.card_union_of_disjoint hdisj, ih, Finset.card_finsuppAntidiag_nat_eq_choose,
      Finset.card_univ, Fintype.card_fin]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [show m + (n' + 1) - 1 = m + n' by omega, show n' + 1 + m - 1 = n' + m by omega,
      show m + 1 + (n' + 1) - 1 = (m + n') + 1 by omega, Nat.choose_succ_succ',
      show n' + m = m + n' by omega, Nat.choose_symm_add]
    ring

theorem coeff_sum_monomial {F : Type*} [Field F] {n : ℕ} (D : Finset (Fin n →₀ ℕ))
    (c : D → F) (s : D) :
    coeff s.1 (∑ t : D, c t • monomial t.1 (1 : F)) = c s := by
  rw [coeff_sum]
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    rw [coeff_smul, coeff_monomial, if_neg (fun h => hb (Subtype.ext h))]
    simp
  · simp

theorem exists_poly {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (hn : 1 ≤ n)
    (S : Finset (Fin n → F)) (M M' d : ℕ)
    (h : S.card * (M + n - 1).choose n + (Fintype.card F ^ n - S.card) * (M' + n - 1).choose n
        < (d + n).choose n) :
    ∃ P : MvPolynomial (Fin n) F, P ≠ 0 ∧ P.totalDegree ≤ d ∧
      (∀ x ∈ S, MultGe P x M) ∧ (∀ x, x ∉ S → MultGe P x M') := by
  classical
  set D := expLt n (d + 1) with hD
  set I1 := S ×ˢ expLt n M
  set I2 := (Finset.univ \ S) ×ˢ expLt n M'
  let L1 : (D → F) →ₗ[F] MvPolynomial (Fin n) F :=
    { toFun := fun c => ∑ t : D, c t • monomial t.1 (1 : F)
      map_add' := by
        intro a b
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp [smul_smul, Finset.smul_sum] }
  let ev : (Fin n → F) × (Fin n →₀ ℕ) → MvPolynomial (Fin n) F →ₗ[F] F := fun p =>
    (lcoeff F p.2).comp (aeval (fun i => C (p.1 i) + X i) : MvPolynomial (Fin n) F →ₐ[F] _).toLinearMap
  have hev : ∀ p P, ev p P = coeff p.2 (shift p.1 P) := by
    intro p P; rfl
  let L2 : MvPolynomial (Fin n) F →ₗ[F] ((I1 ⊕ I2) → F) :=
    LinearMap.pi (fun i => Sum.elim (fun p : I1 => ev p.1) (fun p : I2 => ev p.1) i)
  let L := L2.comp L1
  have hrank : Module.finrank F ((I1 ⊕ I2) → F) < Module.finrank F (D → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
      Finset.card_product, Finset.card_product, hD, card_expLt n hn, card_expLt n hn,
      card_expLt n hn, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, show d + 1 + n - 1 = d + n by omega]
    exact h
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt hrank)
  rw [LinearMap.mem_ker] at hc
  set P := L1 c with hP
  have hcoeffP : ∀ s : D, coeff s.1 P = c s := fun s => coeff_sum_monomial D c s
  have hsupp : ∀ s ∈ P.support, s ∈ D := by
    intro s hs
    by_contra hsD
    apply mem_support_iff.mp hs
    change coeff s (∑ t : D, c t • monomial t.1 (1 : F)) = 0
    rw [coeff_sum]
    apply Finset.sum_eq_zero
    intro t _
    rw [coeff_smul, coeff_monomial, if_neg (fun h => hsD (by rw [← h]; exact t.2))]
    simp
  have hval : ∀ i : I1 ⊕ I2, L c i = 0 := fun i => by rw [hc]; rfl
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro hP0
    apply hc0
    funext s
    rw [← hcoeffP s, hP0, coeff_zero]
    rfl
  · rw [totalDegree]
    apply Finset.sup_le
    intro s hs
    have := (mem_expLt n (d + 1) s).mp (hsupp s hs)
    have h2 : (s.sum fun _ e => e) = s.degree := rfl
    omega
  · intro x hx s hs
    by_contra hlt
    push Not at hlt
    have hmem : (x, s) ∈ I1 := Finset.mem_product.mpr ⟨hx, (mem_expLt n M s).mpr hlt⟩
    have := hval (Sum.inl ⟨(x, s), hmem⟩)
    exact (mem_support_iff.mp hs) this
  · intro x hx s hs
    by_contra hlt
    push Not at hlt
    have hmem : (x, s) ∈ I2 :=
      Finset.mem_product.mpr ⟨by simpa using hx, (mem_expLt n M' s).mpr hlt⟩
    have := hval (Sum.inr ⟨(x, s), hmem⟩)
    exact (mem_support_iff.mp hs) this

end ListHashFurstenberg.Main.Dev.BP.PartCnt
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP
alias exists_poly := ListHashFurstenberg.Main.Dev.BP.PartCnt.exists_poly

end ListHashFurstenberg.Main.Dev.BP
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartRes
open ListHashFurstenberg.Main.Dev.BP
variable {σ : Type*} {F : Type*} [Field F]
/-! ### Degree predicates on a flat polynomial ring -/
/-- every monomial of `h` has degree `< e` -/
def Lt (h : MvPolynomial σ F) (e : ℕ) : Prop := ∀ s ∈ h.support, s.degree < e

theorem deg_of_hom {φ : MvPolynomial σ F} {e : ℕ} (h : φ.IsHomogeneous e) {s : σ →₀ ℕ}
    (hs : s ∈ φ.support) : s.degree = e := by
  rw [Finsupp.degree_eq_weight_one]
  exact h (mem_support_iff.mp hs)

theorem deg_le_td {h : MvPolynomial σ F} {s : σ →₀ ℕ} (hs : s ∈ h.support) :
    s.degree ≤ h.totalDegree :=
  le_totalDegree hs

theorem lt_zero' (e : ℕ) : Lt (0 : MvPolynomial σ F) e := by
  intro s hs
  simp at hs

theorem lt_td {h : MvPolynomial σ F} {e : ℕ} (hl : Lt h e) : h.totalDegree ≤ e :=
  Finset.sup_le fun s hs => (hl s hs).le

theorem lt_mono {h : MvPolynomial σ F} {e e' : ℕ} (hl : Lt h e) (he : e ≤ e') : Lt h e' :=
  fun s hs => lt_of_lt_of_le (hl s hs) he

theorem lt_add {a b : MvPolynomial σ F} {e : ℕ} (ha : Lt a e) (hb : Lt b e) : Lt (a + b) e := by
  classical
  intro s hs
  rcases Finset.mem_union.mp (support_add hs) with h | h
  · exact ha s h
  · exact hb s h

theorem lt_sum {ι : Type*} (T : Finset ι) (f : ι → MvPolynomial σ F) (e : ℕ)
    (h : ∀ i ∈ T, Lt (f i) e) : Lt (∑ i ∈ T, f i) e := by
  classical
  intro s hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp (support_sum hs)
  exact h t ht s hst

theorem lt_mul {h1 h2 : MvPolynomial σ F} {e1 e2 : ℕ} (h1l : Lt h1 e1)
    (h2d : h2.totalDegree ≤ e2) : Lt (h1 * h2) (e1 + e2) := by
  classical
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul h1 h2 hs)
  rw [map_add]
  have h1 := h1l a ha
  have h2 := deg_le_td hb
  omega

theorem td_le_of_sub {f g : MvPolynomial σ F} {e : ℕ} (hf : Lt (f - g) e)
    (hg : g.totalDegree ≤ e) : f.totalDegree ≤ e := by
  have : f = (f - g) + g := by ring
  rw [this]
  exact (totalDegree_add _ _).trans (max_le (lt_td hf) hg)

theorem lt_mul_sub {f1 g1 f2 g2 : MvPolynomial σ F} {e1 e2 : ℕ} (hf1 : Lt (f1 - g1) e1)
    (hg1 : g1.totalDegree ≤ e1) (hf2 : Lt (f2 - g2) e2) (hg2 : g2.totalDegree ≤ e2) :
    Lt (f1 * f2 - g1 * g2) (e1 + e2) := by
  have e : f1 * f2 - g1 * g2 = (f1 - g1) * f2 + (f2 - g2) * g1 := by ring
  rw [e]
  apply lt_add (lt_mul hf1 (td_le_of_sub hf2 hg2))
  rw [add_comm]
  exact lt_mul hf2 hg1

theorem lt_pow_sub {f g : MvPolynomial σ F} {e : ℕ} (hf : Lt (f - g) e)
    (hg : g.totalDegree ≤ e) (k : ℕ) : Lt (f ^ k - g ^ k) (k * e) := by
  induction k with
  | zero => simpa using lt_zero' 0
  | succ k ih =>
    rw [pow_succ, pow_succ, add_mul, one_mul]
    refine lt_mul_sub ih ?_ hf hg
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hg)

theorem lt_prod_sub {ι : Type*} [DecidableEq ι] (T : Finset ι) (f g : ι → MvPolynomial σ F)
    (e : ι → ℕ) (hf : ∀ i ∈ T, Lt (f i - g i) (e i)) (hg : ∀ i ∈ T, (g i).totalDegree ≤ e i) :
    Lt (∏ i ∈ T, f i - ∏ i ∈ T, g i) (∑ i ∈ T, e i) := by
  induction T using Finset.induction_on with
  | empty => simpa using lt_zero' 0
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    refine lt_mul_sub (hf a (Finset.mem_insert_self _ _)) (hg a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))) ?_
    refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    exact hg i (Finset.mem_insert_of_mem hi)

theorem lt_C (c : F) : Lt (C c : MvPolynomial σ F) 1 := by
  classical
  intro s hs
  rw [mem_support_iff, coeff_C] at hs
  split_ifs at hs with h
  · subst h; simp
  · exact absurd rfl hs

end ListHashFurstenberg.Main.Dev.BP.PartRes
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartRes
open ListHashFurstenberg.Main.Dev.BP
variable {F : Type*} [Field F] {n r : ℕ}
/-! ### Substitutions -/
/-- `Z_k + ∑_j B_kj t_j` in the flat ring. -/
noncomputable def lin (B : Fin n → Fin r → F) (k : Fin n) : MvPolynomial (Fin n ⊕ Fin r) F :=
  X (Sum.inl k) + ∑ j, C (B k j) * X (Sum.inr j)

theorem lin_hom (B : Fin n → Fin r → F) (k : Fin n) : (lin B k).IsHomogeneous 1 := by
  unfold lin
  apply IsHomogeneous.add (isHomogeneous_X _ _)
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

/-- `Φ_b Q = Q(b + Bt + Z)` in the flat ring. -/
noncomputable def Phi (b : Fin n → F) (B : Fin n → Fin r → F) :
    MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n ⊕ Fin r) F :=
  aeval fun k => C (b k) + lin B k

theorem coeffΨ (f : MvPolynomial (Fin n ⊕ Fin r) F) (i : Fin n →₀ ℕ) (j : Fin r →₀ ℕ) :
    coeff j (coeff i (sumAlgEquiv F (Fin n) (Fin r) f)) = coeff (Finsupp.sumElim i j) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c =>
    have : sumAlgEquiv F (Fin n) (Fin r) (monomial s c) =
        monomial (Finsupp.sumFinsuppAddEquivProdFinsupp s).1
          (monomial (Finsupp.sumFinsuppAddEquivProdFinsupp s).2 c) := by
      simp [sumAlgEquiv, monomial]
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h1 h2 h3 <;> simp_all
    intro h
    exfalso
    apply h2
    ext x
    cases x <;> simp [← h1, ← h]
  | add p q hp hq => simp [hp, hq]

theorem degree_sumElim (i : Fin n →₀ ℕ) (j : Fin r →₀ ℕ) :
    (Finsupp.sumElim i j).degree = i.degree + j.degree := by
  simp [Finsupp.degree_eq_sum, Fintype.sum_sum_type]

theorem Ψ_Phi (b : Fin n → F) (B : Fin n → Fin r → F) (Q : MvPolynomial (Fin n) F) :
    sumAlgEquiv F (Fin n) (Fin r) (Phi b B Q) = shift (affPt b B) (map C Q) := by
  unfold Phi shift
  rw [← algebraMap_eq (R := F) (σ := Fin r), aeval_map_algebraMap]
  show (sumAlgEquiv F (Fin n) (Fin r)).toAlgHom (aeval _ Q) = _
  rw [← AlgHom.comp_apply, comp_aeval]
  have hfun : (fun k => (sumAlgEquiv F (Fin n) (Fin r)).toAlgHom
      (C (b k) + lin B k)) =
      fun k => C (affPt b B k) + X k := by
    funext k
    simp [lin, affPt, map_sum]
    ring
  rw [hfun]

theorem td_aeval_le {σ τ : Type*} (u : σ → MvPolynomial τ F) (hu : ∀ k, (u k).totalDegree ≤ 1)
    (P : MvPolynomial σ F) : (aeval u P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (deg_le_td hs)
  rw [Finsupp.degree_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hu i))

theorem lin_td (b : Fin n → F) (B : Fin n → Fin r → F) (k : Fin n) :
    (C (b k) + lin B k).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le (by simp) (lin_hom B k).totalDegree_le)

theorem td_Phi (b : Fin n → F) (B : Fin n → Fin r → F) (P : MvPolynomial (Fin n) F) :
    (Phi b B P).totalDegree ≤ P.totalDegree :=
  td_aeval_le _ (lin_td b B) P

theorem Phi_zero (B : Fin n → Fin r → F) : Phi 0 B = aeval (lin B) := by
  unfold Phi
  congr 1
  funext k
  simp

/-- `Φ_b P − Φ_0 P` has only monomials of degree `< totalDegree P` … or rather `< d`. -/
theorem lt_Phi_sub (b : Fin n → F) (B : Fin n → Fin r → F) (P : MvPolynomial (Fin n) F)
    (d : ℕ) (hd : P.totalDegree ≤ d) : Lt (Phi b B P - Phi 0 B P) d := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  refine lt_sum _ _ _ fun t ht => ?_
  rw [Phi_zero, Phi, aeval_monomial, aeval_monomial, ← mul_sub, mul_comm]
  have hl := lt_mul (e2 := 0) (lt_prod_sub t.support (fun i => (C (b i) + lin B i) ^ t i)
    (fun i => lin B i ^ t i) (fun i => t i * 1)
    (fun i _ => lt_pow_sub (by simpa using lt_C (b i)) (lin_hom B i).totalDegree_le (t i))
    (fun i _ => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (lin_hom B i).totalDegree_le)))
    (by rw [algebraMap_eq, totalDegree_C]) (h2 := algebraMap F _ (coeff t P))
  refine lt_mono hl ?_
  have := le_trans (deg_le_td ht) hd
  rw [Finsupp.degree_apply] at this
  simpa using this

theorem hc_Phi_zero (B : Fin n → Fin r → F) (P : MvPolynomial (Fin n) F) :
    homogeneousComponent P.totalDegree (Phi 0 B P) =
      Phi 0 B (homogeneousComponent P.totalDegree P) := by
  have hom : ∀ e, Phi 0 B (homogeneousComponent e P) ∈
      homogeneousSubmodule (Fin n ⊕ Fin r) F e := by
    intro e
    rw [mem_homogeneousSubmodule, Phi_zero]
    simpa using (homogeneousComponent_isHomogeneous e P).aeval _ (lin_hom B)
  have hP : Phi 0 B P = ∑ e ∈ Finset.range (P.totalDegree + 1),
      Phi 0 B (homogeneousComponent e P) := by
    rw [← map_sum, sum_homogeneousComponent]
  rw [hP, map_sum, Finset.sum_eq_single P.totalDegree]
  · rw [homogeneousComponent_of_mem (hom _), if_pos rfl]
  · intro e _ hne
    rw [homogeneousComponent_of_mem (hom e), if_neg (Ne.symm hne)]
  · intro h
    simp at h

theorem hc_Phi (b : Fin n → F) (B : Fin n → Fin r → F) (P : MvPolynomial (Fin n) F) :
    homogeneousComponent P.totalDegree (Phi b B P) =
      Phi 0 B (homogeneousComponent P.totalDegree P) := by
  rw [← hc_Phi_zero]
  have hl := lt_Phi_sub b B P P.totalDegree le_rfl
  rw [← sub_eq_zero, ← map_sub]
  ext s
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with h
  · by_contra hne
    exact absurd h (ne_of_lt (hl s (mem_support_iff.mpr hne)))
  · rfl

/-- low-degree property transported by `aeval (lin B)`. -/
theorem lowGe_aeval_lin (B : Fin n → Fin r → F) (R : MvPolynomial (Fin n) F) (μ : ℕ)
    (hR : ∀ s ∈ R.support, μ ≤ s.degree) :
    ∀ s ∈ (aeval (lin B) R).support, μ ≤ s.degree := by
  classical
  intro s hs
  rw [R.as_sum, map_sum] at hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have hom := (isHomogeneous_monomial (coeff t R) (rfl : t.degree = t.degree)).aeval _ (lin_hom B)
  rw [deg_of_hom hom hst, one_mul]
  exact hR t ht

/-- The `t`-translation map on the flat ring. -/
noncomputable def tau (t0 : Fin r → F) :
    MvPolynomial (Fin n ⊕ Fin r) F →ₐ[F] MvPolynomial (Fin n ⊕ Fin r) F :=
  aeval (Sum.elim (fun k => X (Sum.inl k)) (fun j => C (t0 j) + X (Sum.inr j)))

theorem Ψ_tau (t0 : Fin r → F) (h : MvPolynomial (Fin n ⊕ Fin r) F) (i : Fin n →₀ ℕ) :
    coeff i (sumAlgEquiv F (Fin n) (Fin r) (tau t0 h)) =
      shift t0 (coeff i (sumAlgEquiv F (Fin n) (Fin r) h)) := by
  have key : (sumAlgEquiv F (Fin n) (Fin r)).toAlgHom.comp (tau t0) =
      (mapAlgHom (aeval fun j => C (t0 j) + X j : MvPolynomial (Fin r) F →ₐ[F] _)).comp
        (sumAlgEquiv F (Fin n) (Fin r)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro x
    cases x with
    | inl k => simp [tau]
    | inr j => simp [tau]
  have := congrArg (fun φ => coeff i (φ h)) key
  simp only [AlgHom.comp_apply, mapAlgHom_apply, coeff_map] at this
  exact this

theorem tau_Phi (t0 : Fin r → F) (b : Fin n → F) (B : Fin n → Fin r → F)
    (P : MvPolynomial (Fin n) F) :
    tau t0 (Phi b B P) = aeval (lin B) (shift (fun k => b k + ∑ j, B k j * t0 j) P) := by
  unfold Phi shift
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext k
  simp only [lin, tau, map_add, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
    Sum.elim_inl, Sum.elim_inr, mul_add, Finset.sum_add_distrib]
  ring

end ListHashFurstenberg.Main.Dev.BP.PartRes
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartRes
open ListHashFurstenberg.Main.Dev.BP
theorem top_multGe_of_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n r : ℕ}
    (P : MvPolynomial (Fin n) F) (b : Fin n → F) (B : Fin n → Fin r → F)
    (μ : (Fin r → F) → ℕ)
    (hμ : ∀ t0 : Fin r → F, MultGe P (fun k => b k + ∑ j, B k j * t0 j) (μ t0))
    (m : ℕ)
    (hm : ∀ w < m, w ≤ P.totalDegree → (P.totalDegree - w) * Fintype.card F ^ r <
        Fintype.card F * ∑ t0 : Fin r → F, (μ t0 - w)) :
    MultGe (map C (homogeneousComponent P.totalDegree P)) (affPt 0 B) m := by
  classical
  set d := P.totalDegree with hd
  set f := Phi b B P with hf
  -- (c): every monomial of `f` has `Z`-degree at least `m`
  have hc : ∀ i j, coeff (Finsupp.sumElim i j) f ≠ 0 → m ≤ i.degree := by
    intro i j hij
    by_contra hlt
    push Not at hlt
    set w := i.degree with hw
    set Q := coeff i (sumAlgEquiv F (Fin n) (Fin r) f) with hQ
    have hjQ : ∀ j', coeff j' Q ≠ 0 → w + j'.degree ≤ d := by
      intro j' hj'
      rw [hQ, coeffΨ] at hj'
      have := le_trans (deg_le_td (mem_support_iff.mpr hj')) (td_Phi b B P)
      rwa [degree_sumElim] at this
    have hQ0 : Q ≠ 0 := by
      intro h0
      apply hij
      rw [← coeffΨ, ← hQ, h0, coeff_zero]
    have hwd : w ≤ d := by
      have := hjQ j (by rw [hQ, coeffΨ]; exact hij)
      omega
    have hQdeg : Q.totalDegree ≤ d - w := by
      refine Finset.sup_le fun j' hj' => ?_
      have := hjQ j' (mem_support_iff.mp hj')
      change j'.degree ≤ d - w
      omega
    have hQmult : ∀ t0 ∈ Fintype.piFinset (fun _ : Fin r => (Finset.univ : Finset F)),
        MultGe Q t0 (μ t0 - w) := by
      intro t0 _ j' hj'
      rw [hQ, ← Ψ_tau, mem_support_iff, coeffΨ, hf, tau_Phi] at hj'
      have := lowGe_aeval_lin B _ _ (hμ t0) _ (mem_support_iff.mpr hj')
      rw [degree_sumElim] at this
      omega
    have hSZ := sum_le_of_multGe r (Finset.univ : Finset F) Q hQ0 (fun t0 => μ t0 - w) hQmult
    rw [Fintype.piFinset_univ, Finset.card_univ] at hSZ
    have h1 := hm w hlt hwd
    have h2 := Nat.mul_le_mul_right (Fintype.card F ^ r) hQdeg
    rw [mul_comm] at hSZ
    omega
  -- (d): unshifting
  intro i hi
  rw [← Ψ_Phi] at hi
  obtain ⟨j, hj⟩ := MvPolynomial.ne_zero_iff.mp (mem_support_iff.mp hi)
  rw [coeffΨ, ← hc_Phi b B P, coeff_homogeneousComponent] at hj
  split_ifs at hj
  · exact hc i j hj
  · exact absurd rfl hj

end ListHashFurstenberg.Main.Dev.BP.PartRes
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP
alias top_multGe_of_sum := ListHashFurstenberg.Main.Dev.BP.PartRes.top_multGe_of_sum

end ListHashFurstenberg.Main.Dev.BP
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartGood
open ListHashFurstenberg.Main.Dev.BP
/-- Applying an `F`-algebra endomorphism of `F[t]` to the point preserves multiplicity of a
polynomial with coefficients in `F`. -/
theorem multGe_comp {F : Type*} [Field F] {n r : ℕ} (G : MvPolynomial (Fin n) F)
    (p : Fin n → MvPolynomial (Fin r) F)
    (φ : MvPolynomial (Fin r) F →ₐ[F] MvPolynomial (Fin r) F) (m : ℕ)
    (h : MultGe (map C G) p m) : MultGe (map C G) (fun k => φ (p k)) m := by
  have key : shift (fun k => φ (p k)) (map C G) = map φ (shift p (map C G)) := by
    unfold shift
    rw [← algebraMap_eq (R := F) (σ := Fin r), aeval_map_algebraMap, aeval_map_algebraMap]
    have e1 : ∀ Q : MvPolynomial (Fin n) (MvPolynomial (Fin r) F),
        map (φ : MvPolynomial (Fin r) F →+* MvPolynomial (Fin r) F) Q = mapAlgHom φ Q :=
      fun _ => rfl
    rw [e1, ← AlgHom.comp_apply, comp_aeval]
    have hfun : (fun k => mapAlgHom φ (C (p k) + X k)) = fun k => C (φ (p k)) + X k := by
      funext k
      simp
    rw [hfun]
  intro s hs
  rw [key] at hs
  exact h s (support_map_subset _ _ hs)

theorem cast_sub_le (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

theorem multGe_of_good {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n r : ℕ}
    (S : Finset (Fin n → F)) (α : ℝ) (M M' : ℕ) (hM' : M' ≤ M)
    (P : MvPolynomial (Fin n) F) (hPS : ∀ x ∈ S, MultGe P x M)
    (hPn : ∀ x, x ∉ S → MultGe P x M') (m : ℕ)
    (hm : ∀ w : ℕ, w < m → ((P.totalDegree : ℝ) - w) <
        Fintype.card F * (α * M + (1 - α) * M' - w))
    (V : Fin n → Fin r → F) (hV : GoodMat r (α * (Fintype.card F : ℝ) ^ r) S V) :
    MultGe (map C (homogeneousComponent P.totalDegree P)) (affPt 0 V) m := by
  classical
  obtain ⟨W, hW, hVW, x, hx⟩ := hV
  let bW : Module.Basis (Fin r) F W := Module.finBasisOfFinrankEq F W hW
  let B : Fin n → Fin r → F := fun k l => (bW l : Fin n → F) k
  let pt : (Fin r → F) → (Fin n → F) := fun t0 => fun k => x k + ∑ j, B k j * t0 j
  have hpt : ∀ t0, pt t0 = x + ((bW.equivFun.symm t0 : W) : Fin n → F) := by
    intro t0
    funext k
    simp [pt, B, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  let μ : (Fin r → F) → ℕ := fun t0 => if pt t0 ∈ S then M else M'
  have hμ : ∀ t0 : Fin r → F, MultGe P (fun k => x k + ∑ j, B k j * t0 j) (μ t0) := by
    intro t0
    by_cases h : pt t0 ∈ S
    · simp only [μ, if_pos h]; exact hPS _ h
    · simp only [μ, if_neg h]; exact hPn _ h
  set q : ℕ := Fintype.card F with hq
  have hq0 : (0 : ℝ) < q := by
    rw [hq]; exact_mod_cast Fintype.card_pos
  set Sg := Finset.univ.filter fun t0 => pt t0 ∈ S with hSg
  set Sb := Finset.univ.filter fun t0 => pt t0 ∉ S with hSb
  have hcard : Sg.card + Sb.card = q ^ r := by
    rw [hSg, hSb, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin]
  have hc : α * (q : ℝ) ^ r ≤ Sg.card := by
    refine le_trans hx ?_
    have : (S.filter fun s => s - x ∈ W).card ≤ Sg.card := by
      refine le_trans (Finset.card_le_card (t := Sg.image pt) ?_) Finset.card_image_le
      intro s hs
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_image]
      refine ⟨bW.equivFun ⟨s - x, hs.2⟩, ?_, ?_⟩
      · rw [hSg, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hpt, LinearEquiv.symm_apply_apply]
        simpa using hs.1
      · rw [hpt, LinearEquiv.symm_apply_apply]
        simp
    exact_mod_cast this
  have hsumμ : ((∑ t0 : Fin r → F, μ t0 : ℕ) : ℝ) = Sg.card * M + Sb.card * M' := by
    simp only [μ]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    push_cast
    rfl
  have hm' : ∀ w < m, w ≤ P.totalDegree → (P.totalDegree - w) * q ^ r <
      q * ∑ t0 : Fin r → F, (μ t0 - w) := by
    intro w hw hwd
    have h1 := hm w hw
    have h2 : ∑ t0 : Fin r → F, ((μ t0 : ℝ) - w) ≤ ((∑ t0 : Fin r → F, (μ t0 - w) : ℕ) : ℝ) := by
      push_cast
      exact Finset.sum_le_sum fun t0 _ => cast_sub_le _ _
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hsumμ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul] at h2
    have hcard' : (Sg.card : ℝ) + Sb.card = (q : ℝ) ^ r := by exact_mod_cast hcard
    have hMM : (M' : ℝ) ≤ M := by exact_mod_cast hM'
    have hqr : (0 : ℝ) < (q : ℝ) ^ r := pow_pos hq0 r
    set T := ∑ t0 : Fin r → F, (μ t0 - w)
    have h3 : (q : ℝ) ^ r * (α * M + (1 - α) * M' - w) ≤ T := by
      refine le_trans ?_ h2
      have : 0 ≤ ((Sg.card : ℝ) - α * (q : ℝ) ^ r) * ((M : ℝ) - M') :=
        mul_nonneg (by linarith) (by linarith)
      push_cast at this ⊢
      nlinarith
    have h4 : (q : ℝ) ^ r * ((P.totalDegree : ℝ) - w) <
        (q : ℝ) ^ r * (q * (α * M + (1 - α) * M' - w)) := mul_lt_mul_of_pos_left h1 hqr
    have h5 : ((P.totalDegree - w : ℕ) : ℝ) * (q : ℝ) ^ r < q * (T : ℝ) := by
      rw [Nat.cast_sub hwd]
      nlinarith
    exact_mod_cast h5
  have hB := top_multGe_of_sum P x B μ hμ m hm'
  -- pass from `B` to `V`
  have hcol : ∀ l : Fin r, (fun k => V k l) ∈ W := by
    intro l
    have := hVW (Pi.single l 1)
    simpa [Pi.single_apply] using this
  let Cm : Fin r → Fin r → F := fun j l => bW.equivFun ⟨fun k => V k l, hcol l⟩ j
  have hV : ∀ k l, V k l = ∑ j, B k j * Cm j l := by
    intro k l
    have := congrArg (fun v : W => (v : Fin n → F) k)
      (bW.equivFun.symm_apply_apply ⟨fun k => V k l, hcol l⟩)
    simp only [Module.Basis.equivFun_symm_apply] at this
    rw [Submodule.coe_sum, Finset.sum_apply] at this
    refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Cm, B]
    rw [mul_comm]
  let φ : MvPolynomial (Fin r) F →ₐ[F] MvPolynomial (Fin r) F :=
    aeval fun j => ∑ l, C (Cm j l) * X l
  have hpts : affPt 0 V = fun k => φ (affPt 0 B k) := by
    funext k
    simp only [affPt, φ, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
      Pi.zero_apply, map_zero, zero_add, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hV k l, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc]
  rw [hpts]
  exact multGe_comp _ _ φ m hB

end ListHashFurstenberg.Main.Dev.BP.PartGood
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP
alias multGe_of_good := ListHashFurstenberg.Main.Dev.BP.PartGood.multGe_of_good

end ListHashFurstenberg.Main.Dev.BP
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartGL
open ListHashFurstenberg.Main.Dev.BP ListHashFurstenberg.Main.Dev.GLTool
open Module
/-- The linear map `t ↦ V t`. -/
def colMap {F : Type*} [Field F] {n r : ℕ} (V : Fin n → Fin r → F) :
    (Fin r → F) →ₗ[F] (Fin n → F) where
  toFun t := fun k => ∑ j, V k j * t j
  map_add' a b := by
    funext k
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext k
    simp [Finset.mul_sum, mul_left_comm]

theorem colMap_apply {F : Type*} [Field F] {n r : ℕ} (V : Fin n → Fin r → F) (t : Fin r → F) :
    colMap V t = fun k => ∑ j, V k j * t j := rfl

/-- Apply `g` to every column of `V`. -/
def act {F : Type*} [Field F] {n r : ℕ} (g : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (V : Fin n → Fin r → F) : Fin n → Fin r → F :=
  fun k j => g (fun k' => V k' j) k

theorem act_vec {F : Type*} [Field F] {n r : ℕ} (g : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (V : Fin n → Fin r → F) (t : Fin r → F) :
    (fun k => ∑ j, act g V k j * t j) = g (fun k => ∑ j, V k j * t j) := by
  have h : (fun k => ∑ j, V k j * t j) = ∑ j, t j • (fun k => V k j) := by
    funext k
    simp [Finset.sum_apply, mul_comm]
  rw [h, map_sum]
  funext k
  simp [act, Finset.sum_apply, mul_comm]

/-- `V ↦ gV` as a permutation of matrices. -/
def actEquiv {F : Type*} [Field F] {n r : ℕ} (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    (Fin n → Fin r → F) ≃ (Fin n → Fin r → F) where
  toFun := act g
  invFun := act g.symm
  left_inv V := by
    funext k j
    simp [act]
  right_inv V := by
    funext k j
    simp [act]

open Classical in
theorem good_act {F : Type*} [Field F] {n r : ℕ} (T : ℝ) (S : Finset (Fin n → F))
    (V : Fin n → Fin r → F) (W : Submodule F (Fin n → F)) (hW : finrank F W = r)
    (hVW : ∀ t : Fin r → F, (fun k => ∑ j, V k j * t j) ∈ W)
    (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) (hg : ∃ x : Fin n → F,
      T ≤ ((S.filter fun s => s - x ∈ W.map g.toLinearMap).card : ℝ)) :
    GoodMat r T S (act g V) := by
  refine ⟨W.map g.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hW], fun t => ?_, hg⟩
  rw [act_vec]
  exact Submodule.mem_map_of_mem (hVW t)

open Classical in
theorem card_good_ge {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n r : ℕ) (T : ℝ)
    (S : Finset (Fin n → F)) :
    richFraction n r T S * (Fintype.card F : ℝ) ^ (n * r) ≤
      ((Finset.univ.filter (GoodMat r T S)).card : ℝ) := by
  set D := (Gr F n r).card with hD
  rcases Nat.eq_zero_or_pos D with h0 | hpos
  · rw [richFraction_eq_zero r T S h0, zero_mul]
    positivity
  obtain ⟨W0, hW0⟩ := Finset.card_pos.mp hpos
  have hrn : r ≤ n := by
    have := Submodule.finrank_le W0
    rwa [mem_Gr.mp hW0, Module.finrank_fin_fun] at this
  have hsup : ∀ V : Fin n → Fin r → F, ∃ W : Submodule F (Fin n → F), finrank F W = r ∧
      ∀ t : Fin r → F, (fun k => ∑ j, V k j * t j) ∈ W := by
    intro V
    have hK : finrank F (LinearMap.range (colMap V)) ≤ r := by
      have := LinearMap.finrank_range_le (colMap V)
      rwa [Module.finrank_fin_fun] at this
    obtain ⟨W, hKW, hW⟩ := exists_le_finrank (r - finrank F (LinearMap.range (colMap V)))
      (LinearMap.range (colMap V)) (by omega)
    refine ⟨W, by rw [hW]; omega, fun t => hKW ?_⟩
    rw [← colMap_apply]
    exact LinearMap.mem_range_self _ t
  choose Wf hWf hVW using hsup
  set ρ := richFraction n r T S with hρ
  set N := (Finset.univ.filter (GoodMat r T S)).card with hN
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hpos
  have hV : ∀ V : Fin n → Fin r → F,
      (∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F),
        if Rich T S ((Wf V).map g.toLinearMap) then (1 : ℝ) else 0) =
        Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) * ρ := by
    intro V
    have := sum_map_mul (hWf V) (fun U => if Rich T S U then (1 : ℝ) else 0)
    simp only [Finset.sum_boole] at this ⊢
    rw [hρ, richFraction_eq, mul_div_assoc', eq_div_iff hDpos.ne']
    exact this
  have h1 : (Fintype.card (Fin n → Fin r → F) : ℝ) *
      (Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) * ρ) =
      ∑ V : Fin n → Fin r → F, ∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F),
        if Rich T S ((Wf V).map g.toLinearMap) then (1 : ℝ) else 0 := by
    rw [Finset.sum_congr rfl (fun V _ => hV V), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have h2 : (∑ V : Fin n → Fin r → F, ∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F),
        if Rich T S ((Wf V).map g.toLinearMap) then (1 : ℝ) else 0) ≤
      ∑ V : Fin n → Fin r → F, ∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F),
        if GoodMat r T S (act g V) then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro V _
    apply Finset.sum_le_sum
    intro g _
    by_cases h : Rich T S ((Wf V).map g.toLinearMap)
    · rw [if_pos h, if_pos (good_act T S V (Wf V) (hWf V) (hVW V) g h)]
    · rw [if_neg h]
      split_ifs <;> norm_num
  have h3 : (∑ V : Fin n → Fin r → F, ∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F),
        if GoodMat r T S (act g V) then (1 : ℝ) else 0) =
      Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) * N := by
    rw [Finset.sum_comm]
    have hg : ∀ g : (Fin n → F) ≃ₗ[F] (Fin n → F),
        (∑ V : Fin n → Fin r → F, if GoodMat r T S (act g V) then (1 : ℝ) else 0) = N := by
      intro g
      rw [Fintype.sum_equiv (actEquiv g)
        (fun V => if GoodMat r T S (act g V) then (1 : ℝ) else 0)
        (fun V => if GoodMat r T S V then (1 : ℝ) else 0) (fun V => rfl), Finset.sum_boole]
    rw [Finset.sum_congr rfl (fun g _ => hg g), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hcardM : (Fintype.card (Fin n → Fin r → F) : ℝ) = (Fintype.card F : ℝ) ^ (n * r) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  have hGpos : (0 : ℝ) < Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨LinearEquiv.refl F _⟩
  rw [← hcardM]
  have key := h1.trans_le (h2.trans h3.le)
  rw [show (Fintype.card (Fin n → Fin r → F) : ℝ) *
      (Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) * ρ) =
      Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) *
        (ρ * Fintype.card (Fin n → Fin r → F)) by ring] at key
  exact le_of_mul_le_mul_left key hGpos

end ListHashFurstenberg.Main.Dev.BP.PartGL
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP
alias card_good_ge := ListHashFurstenberg.Main.Dev.BP.PartGL.card_good_ge

end ListHashFurstenberg.Main.Dev.BP
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartGL
open ListHashFurstenberg.Main.Dev.BP ListHashFurstenberg.Main.Dev.GLTool
open Module
theorem le_one_of_furstenberg {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n r : ℕ)
    (S : Finset (Fin n → F)) (δ α : ℝ) (hδ : 0 < δ)
    (hS : IsFurstenberg δ n r (α * (Fintype.card F : ℝ) ^ r) S) : α ≤ 1 := by
  classical
  have hρ : 0 < richFraction n r (α * (Fintype.card F : ℝ) ^ r) S := lt_of_lt_of_le hδ hS
  rw [richFraction_eq] at hρ
  have hnum : 0 < ((Gr F n r).filter (Rich (α * (Fintype.card F : ℝ) ^ r) S)).card := by
    by_contra h
    push Not at h
    rw [Nat.le_zero.mp h] at hρ
    simp at hρ
  obtain ⟨U, hU⟩ := Finset.card_pos.mp hnum
  obtain ⟨hUG, x, hx⟩ := Finset.mem_filter.mp hU
  have hfr := mem_Gr.mp hUG
  have hle : (S.filter fun s => s - x ∈ U).card ≤ Fintype.card F ^ r := by
    have h2 : (Finset.univ.filter fun y : Fin n → F => y ∈ U).card = Fintype.card F ^ r := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card, hfr]
    rw [← h2]
    apply Finset.card_le_card_of_injOn (fun s => s - x)
    · intro a ha
      have ha' : a - x ∈ U := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩)
    · intro a _ b _ hab
      simpa using hab
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) ^ r := by
    have : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    positivity
  have hle' : ((S.filter fun s => s - x ∈ U).card : ℝ) ≤ (Fintype.card F : ℝ) ^ r := by
    exact_mod_cast hle
  have : α * (Fintype.card F : ℝ) ^ r ≤ 1 * (Fintype.card F : ℝ) ^ r := by linarith
  exact le_of_mul_le_mul_right this hq

end ListHashFurstenberg.Main.Dev.BP.PartGL
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP
alias le_one_of_furstenberg := ListHashFurstenberg.Main.Dev.BP.PartGL.le_one_of_furstenberg

end ListHashFurstenberg.Main.Dev.BP
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP.PartLim
open ListHashFurstenberg.Main.Dev.BP
open Filter Topology Nat
theorem step_bound (n : ℕ) (hn : 1 ≤ n) (ψ ε s Q : ℝ) (hψ : 0 ≤ ψ) (hε1 : ε ≤ 1)
    (hs : 0 ≤ s) (hsQ : s ≤ Q) (M : ℕ) (hM : 1 ≤ M) (d : ℕ) (hd : ψ * M ≤ d)
    (hc : (((d + n - 1).choose n : ℕ) : ℝ) ≤ s * (((M + n - 1).choose n : ℕ) : ℝ) +
        (Q - s) * (((⌈(1 - ε) * M⌉₊ + n - 1).choose n : ℕ) : ℝ)) :
    ψ ^ n ≤ s * (1 + n * (1 / (M : ℝ))) ^ n + (Q - s) * ((1 - ε) + n * (1 / (M : ℝ))) ^ n := by
  have hQs : 0 ≤ Q - s := by linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have h1 : (d : ℝ) ^ n / n ! ≤ (((d + n - 1).choose n : ℕ) : ℝ) := by
    have := Nat.pow_le_choose (α := ℝ) n (d + n - 1)
    rwa [show d + n - 1 + 1 - n = d by omega] at this
  have h2 : (((M + n - 1).choose n : ℕ) : ℝ) ≤ ((M : ℝ) + n) ^ n / n ! := by
    refine (Nat.choose_le_pow_div (α := ℝ) n (M + n - 1)).trans ?_
    gcongr
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hεM : 0 ≤ (1 - ε) * (M : ℝ) := mul_nonneg (by linarith) hMpos.le
  have h3 : (((⌈(1 - ε) * M⌉₊ + n - 1).choose n : ℕ) : ℝ) ≤ ((1 - ε) * M + n) ^ n / n ! := by
    refine (Nat.choose_le_pow_div (α := ℝ) n (⌈(1 - ε) * M⌉₊ + n - 1)).trans ?_
    gcongr
    rw [Nat.cast_sub (by omega)]
    push_cast
    have := Nat.ceil_lt_add_one hεM
    linarith
  have hd0 : 0 ≤ ψ * M := mul_nonneg hψ hMpos.le
  have h4 : (ψ * M) ^ n ≤ (d : ℝ) ^ n := pow_le_pow_left₀ hd0 hd n
  have h5 : (ψ * M) ^ n ≤ s * ((M : ℝ) + n) ^ n + (Q - s) * ((1 - ε) * M + n) ^ n := by
    have := h4.trans ((div_le_iff₀ hfac).mp h1)
    have h6 : (((d + n - 1).choose n : ℕ) : ℝ) * n ! ≤
        s * ((M : ℝ) + n) ^ n + (Q - s) * ((1 - ε) * M + n) ^ n := by
      have a := mul_le_mul_of_nonneg_left h2 hs
      have b := mul_le_mul_of_nonneg_left h3 hQs
      have := (hc.trans (add_le_add a b))
      calc (((d + n - 1).choose n : ℕ) : ℝ) * n !
          ≤ (s * (((M : ℝ) + n) ^ n / n !) + (Q - s) * (((1 - ε) * M + n) ^ n / n !)) * n ! :=
            mul_le_mul_of_nonneg_right this hfac.le
        _ = _ := by field_simp
    linarith
  have e1 : (1 + n * (1 / (M : ℝ))) ^ n = ((M : ℝ) + n) ^ n / (M : ℝ) ^ n := by
    rw [← div_pow]; congr 1; field_simp
  have e2 : ((1 - ε) + n * (1 / (M : ℝ))) ^ n = ((1 - ε) * M + n) ^ n / (M : ℝ) ^ n := by
    rw [← div_pow]; congr 1; field_simp
  rw [e1, e2, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
    le_div_iff₀ (by positivity), ← mul_pow]
  exact h5

theorem limit_bound (n : ℕ) (hn : 1 ≤ n) (ψ ε s Q : ℝ) (hψ : 0 ≤ ψ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hs : 0 ≤ s) (hsQ : s ≤ Q)
    (h : ∀ M : ℕ, 1 ≤ M → ∃ d : ℕ, ψ * M ≤ d ∧
      (((d + n - 1).choose n : ℕ) : ℝ) ≤ s * (((M + n - 1).choose n : ℕ) : ℝ) +
        (Q - s) * (((⌈(1 - ε) * M⌉₊ + n - 1).choose n : ℕ) : ℝ)) :
    ψ ^ n ≤ s + (Q - s) * (1 - ε) ^ n := by
  have hcont : Continuous (fun x : ℝ =>
      s * (1 + n * x) ^ n + (Q - s) * ((1 - ε) + n * x) ^ n) := by fun_prop
  have ht := (hcont.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  simp only [mul_zero, add_zero, one_pow, mul_one] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  obtain ⟨d, hd, hc⟩ := h M hM
  exact step_bound n hn ψ ε s Q hψ hε1 hs hsQ M hM d hd hc

end ListHashFurstenberg.Main.Dev.BP.PartLim
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main.Dev.BP
alias limit_bound := ListHashFurstenberg.Main.Dev.BP.PartLim.limit_bound

/-! ### Assembly -/
theorem homogeneousComponent_totalDegree_ne_zero {F : Type*} [Field F] {n : ℕ}
    (P : MvPolynomial (Fin n) F) (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  obtain ⟨s, hs, hsd⟩ := Finset.exists_max_image P.support (fun s => s.degree)
    (support_nonempty.mpr hP)
  have hdeg : s.degree = P.totalDegree := by
    apply le_antisymm (le_totalDegree hs)
    rw [totalDegree]
    exact Finset.sup_le fun t ht => hsd t ht
  intro h0
  have := congrArg (coeff s) h0
  rw [coeff_homogeneousComponent, if_pos hdeg, coeff_zero] at this
  exact (mem_support_iff.mp hs) this

theorem linForm_injective {F : Type*} [Field F] {r : ℕ} :
    Function.Injective (fun u : Fin r → F => ∑ j, C (u j) * (X j : MvPolynomial (Fin r) F)) := by
  intro u u' h
  funext j
  have := congrArg (coeff (Finsupp.single j 1)) h
  simp only [coeff_sum, coeff_C_mul, coeff_X', Finsupp.single_eq_single_iff] at this
  simpa using this

theorem degree_lower {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n r : ℕ)
    (S : Finset (Fin n → F)) (δ α : ℝ) (hδ : 0 ≤ δ)
    (hS : IsFurstenberg δ n r (α * (Fintype.card F : ℝ) ^ r) S)
    (M M' : ℕ) (hM' : M' ≤ M) (P : MvPolynomial (Fin n) F) (hP : P ≠ 0)
    (hPS : ∀ x ∈ S, MultGe P x M) (hPn : ∀ x, x ∉ S → MultGe P x M') :
    δ * (Fintype.card F : ℝ) ^ r *
        ((Fintype.card F : ℝ) * (α * M + (1 - α) * M') - P.totalDegree) ≤
      ((Fintype.card F : ℝ) - 1) * P.totalDegree := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set d := P.totalDegree with hd
  set β : ℝ := α * M + (1 - α) * M' with hβ
  have hq1 : (1 : ℝ) < q := by
    rw [hq]; exact_mod_cast Fintype.one_lt_card
  have hqr : 0 ≤ q ^ r := pow_nonneg (by linarith) r
  by_cases hneg : q * β - d ≤ 0
  · have h1 : δ * q ^ r * (q * β - d) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hδ hqr) hneg
    have h2 : 0 ≤ (q - 1) * (d : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  push_neg at hneg
  set m : ℕ := ⌈(q * β - d) / (q - 1)⌉₊ with hm
  have hmw : ∀ w : ℕ, w < m → ((d : ℝ) - w) < q * (β - w) := by
    intro w hw
    have h1 : (w : ℝ) < (q * β - d) / (q - 1) := Nat.lt_ceil.mp hw
    rw [lt_div_iff₀ (by linarith)] at h1
    nlinarith
  set G := homogeneousComponent d P with hG
  set A := MvPolynomial (Fin r) F
  set GA : MvPolynomial (Fin n) A := map C G with hGA
  have hG0 : G ≠ 0 := homogeneousComponent_totalDegree_ne_zero P hP
  have hGA0 : GA ≠ 0 := by
    intro h
    apply hG0
    exact map_injective _ (C_injective (Fin r) F) (by rw [map_zero]; exact h)
  have hGAdeg : GA.totalDegree ≤ d := by
    calc GA.totalDegree ≤ G.totalDegree := Finset.sup_mono (support_map_subset _ _)
      _ ≤ d := by
        rcases eq_or_ne G 0 with h | h
        · simp [h]
        · exact le_of_eq ((homogeneousComponent_isHomogeneous d P).totalDegree h)
  let L : (Fin r → F) → A := fun u => ∑ j, C (u j) * X j
  let Tg : Finset A := Finset.univ.image L
  have hTg : Tg.card = Fintype.card F ^ r := by
    rw [Finset.card_image_of_injective _ linForm_injective, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
  let good : Finset (Fin n → Fin r → F) :=
    Finset.univ.filter (GoodMat r (α * (Fintype.card F : ℝ) ^ r) S)
  have hpt : ∀ V : Fin n → Fin r → F, affPt 0 V = fun k => L (V k) := by
    intro V; funext k; simp [affPt, L]
  have hptinj : Function.Injective (fun V : Fin n → Fin r → F => affPt 0 V) := by
    intro V V' h
    simp only [hpt] at h
    funext k
    exact linForm_injective (congrFun h k)
  let μ : (Fin n → A) → ℕ := fun a => if a ∈ good.image (fun V => affPt 0 V) then m else 0
  have hμ : ∀ a ∈ Fintype.piFinset (fun _ : Fin n => Tg), MultGe GA a (μ a) := by
    intro a _
    by_cases ha : a ∈ good.image (fun V => affPt 0 V)
    · simp only [μ, if_pos ha]
      obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp ha
      exact multGe_of_good S α M M' hM' P hPS hPn m hmw V (Finset.mem_filter.mp hV).2
    · simp only [μ, if_neg ha]
      intro s _
      exact Nat.zero_le _
  have hSZ := sum_le_of_multGe n Tg GA hGA0 μ hμ
  have hsub : good.image (fun V => affPt 0 V) ⊆ Fintype.piFinset (fun _ : Fin n => Tg) := by
    intro a ha
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp ha
    rw [Fintype.mem_piFinset]
    intro k
    rw [hpt]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hsum : m * good.card ≤ ∑ a ∈ Fintype.piFinset (fun _ : Fin n => Tg), μ a := by
    calc m * good.card = ∑ a ∈ good.image (fun V => affPt 0 V), m := by
          rw [Finset.sum_const, Finset.card_image_of_injective _ hptinj, smul_eq_mul, mul_comm]
      _ = ∑ a ∈ good.image (fun V => affPt 0 V), μ a :=
          Finset.sum_congr rfl (fun a ha => by simp only [μ, if_pos ha])
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  have hgood : δ * q ^ (n * r) ≤ (good.card : ℝ) := by
    have h1 := card_good_ge n r (α * (Fintype.card F : ℝ) ^ r) S
    have h2 : δ * q ^ (n * r) ≤ richFraction n r (α * (Fintype.card F : ℝ) ^ r) S * q ^ (n * r) :=
      mul_le_mul_of_nonneg_right hS (pow_nonneg (by linarith) _)
    exact le_trans h2 h1
  -- m * #good * q^r ≤ d * q^(r n)
  have hmain : (m : ℝ) * good.card * q ^ r ≤ d * (q ^ r) ^ n := by
    have : m * good.card * Tg.card ≤ d * Tg.card ^ n :=
      le_trans (Nat.mul_le_mul_right _ hsum) (le_trans hSZ (Nat.mul_le_mul_right _ hGAdeg))
    rw [hTg] at this
    have h' : ((m * good.card * Fintype.card F ^ r : ℕ) : ℝ) ≤
        ((d * (Fintype.card F ^ r) ^ n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    rw [hq]
    exact h'
  have hqrpos : 0 < q ^ r := pow_pos (by linarith) r
  have hmle : (q * β - d) / (q - 1) ≤ m := Nat.le_ceil _
  have hmle' : q * β - d ≤ m * (q - 1) := by
    rwa [div_le_iff₀ (by linarith)] at hmle
  -- δ m q^r ≤ d
  have hkey : δ * m * q ^ r ≤ d := by
    have hpow : (q ^ r) ^ n = q ^ (n * r) := by rw [← pow_mul, mul_comm]
    rw [hpow] at hmain
    have hqnr : 0 < q ^ (n * r) := pow_pos (by linarith) _
    have h3 : δ * q ^ (n * r) * m * q ^ r ≤ (good.card : ℝ) * m * q ^ r := by
      have := mul_le_mul_of_nonneg_right hgood (Nat.cast_nonneg m)
      exact mul_le_mul_of_nonneg_right this hqrpos.le
    have h4 : (δ * m * q ^ r) * q ^ (n * r) ≤ d * q ^ (n * r) := by nlinarith
    exact le_of_mul_le_mul_right h4 hqnr
  calc δ * q ^ r * (q * β - d) ≤ δ * q ^ r * (m * (q - 1)) :=
        mul_le_mul_of_nonneg_left hmle' (mul_nonneg hδ hqr)
    _ = (q - 1) * (δ * m * q ^ r) := by ring
    _ ≤ (q - 1) * d := mul_le_mul_of_nonneg_left hkey (by linarith)

theorem succ_le_choose_add (d n : ℕ) (hn : 1 ≤ n) : d + 1 ≤ (d + n).choose n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have := ih hk
      rw [show d + (k + 1) = (d + k) + 1 by ring, Nat.choose_succ_succ]
      omega

end ListHashFurstenberg.Main.Dev.BP
end

section
set_option autoImplicit false
open MvPolynomial
namespace ListHashFurstenberg.Main
open ListHashFurstenberg.Main.Dev.BP in
theorem chk_theorem_2_8 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (hn : 1 ≤ n) (δ α ε : ℝ) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (S : Finset (Fin n → F))
    (hS : IsFurstenberg δ n r (α * (Fintype.card F : ℝ) ^ r) S)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (Fintype.card F : ℝ) ^ n *
        ((δ * (α + (1 - ε) * (1 - α)) * (Fintype.card F : ℝ) ^ r /
            (δ * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1)) ^ n - (1 - ε) ^ n) /
        (1 - (1 - ε) ^ n) ≤ (S.card : ℝ) ∧
    ((Finset.univ \ S).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ n *
        (1 - (δ * (α + (1 - ε) * (1 - α)) * (Fintype.card F : ℝ) ^ r /
            (δ * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1)) ^ n) /
        (1 - (1 - ε) ^ n) ∧
    (Fintype.card F : ℝ) ^ n *
        (1 - (δ * (α + (1 - ε) * (1 - α)) * (Fintype.card F : ℝ) ^ r /
            (δ * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1)) ^ n) /
        (1 - (1 - ε) ^ n) =
      (Fintype.card F : ℝ) ^ n *
        (1 - (1 - (δ * ε * (1 - α) * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1) /
            (δ * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1)) ^ n) /
        (1 - (1 - ε) ^ n) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : (1 : ℝ) < q := by rw [hq]; exact_mod_cast Fintype.one_lt_card
  have hqr : 0 < q ^ r := pow_pos (by linarith) r
  have hD : 0 < δ * q ^ r + q - 1 := by nlinarith [mul_nonneg hδ hqr.le]
  set x : ℝ := δ * (α + (1 - ε) * (1 - α)) * q ^ r / (δ * q ^ r + q - 1) with hx
  have hy1 : (1 - ε) ^ n < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hy0 : 0 ≤ (1 - ε) ^ n := pow_nonneg (by linarith) n
  have hden : 0 < 1 - (1 - ε) ^ n := by linarith
  have hcardS : (S.card : ℝ) ≤ q ^ n := by
    have : S.card ≤ Fintype.card (Fin n → F) := Finset.card_le_univ S
    rw [Fintype.card_fun, Fintype.card_fin] at this
    rw [hq]; exact_mod_cast this
  have hcompl : ((Finset.univ \ S).card : ℝ) = q ^ n - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Nat.cast_sub, Nat.cast_pow]
    have : S.card ≤ Fintype.card (Fin n → F) := Finset.card_le_univ S
    rwa [Fintype.card_fun, Fintype.card_fin] at this
  -- the main inequality: q^n x^n ≤ |S| + (q^n - |S|) (1-ε)^n
  have hmainineq : q ^ n * x ^ n ≤ S.card + (q ^ n - S.card) * (1 - ε) ^ n := by
    rcases eq_or_lt_of_le hδ with h0 | hδpos
    · have hx0 : x = 0 := by rw [hx, ← h0]; simp
      rw [hx0, zero_pow (by omega), mul_zero]
      have := mul_nonneg (sub_nonneg.mpr hcardS) hy0
      have := (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
      linarith
    have hα1 : α ≤ 1 := le_one_of_furstenberg n r S δ α hδpos hS
    set ψ : ℝ := q * x with hψ
    have hψ0 : 0 ≤ ψ := by
      rw [hψ, hx]
      apply mul_nonneg (by linarith)
      apply div_nonneg _ hD.le
      apply mul_nonneg (mul_nonneg hδ _) hqr.le
      nlinarith
    have key := limit_bound n hn ψ ε S.card (q ^ n) hψ0 hε0 hε1 (Nat.cast_nonneg _) hcardS
      (by
        intro M hM
        set M' : ℕ := ⌈(1 - ε) * M⌉₊ with hM'
        have hM'le : M' ≤ M := by
          rw [hM']
          apply Nat.ceil_le.mpr
          have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
          nlinarith
        set N : ℕ := S.card * (M + n - 1).choose n +
          (Fintype.card F ^ n - S.card) * (M' + n - 1).choose n with hN
        have hex : ∃ d : ℕ, N < (d + n).choose n :=
          ⟨N, lt_of_lt_of_le (Nat.lt_succ_self N) (succ_le_choose_add N n hn)⟩
        set d := Nat.find hex with hd
        obtain ⟨P, hP0, hPdeg, hPS, hPn⟩ := exists_poly n hn S M M' d (Nat.find_spec hex)
        have hmin : (d + n - 1).choose n ≤ N := by
          rcases Nat.eq_zero_or_pos d with h0 | hpos
          · rw [h0, zero_add, Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _
          · have := Nat.find_min hex (show d - 1 < d by omega)
            push_neg at this
            rwa [show d - 1 + n = d + n - 1 by omega] at this
        have hlow := degree_lower n r S δ α hδ hS M M' hM'le P hP0 hPS hPn
        refine ⟨d, ?_, ?_⟩
        · -- ψ M ≤ totalDegree P ≤ d
          have hM'ge : (1 - ε) * M ≤ (M' : ℝ) := Nat.le_ceil _
          have hβ : (α + (1 - ε) * (1 - α)) * M ≤ α * M + (1 - α) * M' := by
            nlinarith
          have hdP : ψ * M ≤ (P.totalDegree : ℝ) := by
            rw [hψ, hx]
            have hP' : δ * q ^ r * (q * ((α + (1 - ε) * (1 - α)) * M) - P.totalDegree) ≤
                (q - 1) * P.totalDegree := by
              have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ (by linarith : (0:ℝ) ≤ q))
                (mul_nonneg hδ hqr.le)
              nlinarith
            rw [show q * (δ * (α + (1 - ε) * (1 - α)) * q ^ r / (δ * q ^ r + q - 1)) * M =
                (δ * q ^ r * (q * ((α + (1 - ε) * (1 - α)) * M))) / (δ * q ^ r + q - 1) by
                  field_simp]
            rw [div_le_iff₀ hD]
            nlinarith
          calc ψ * M ≤ P.totalDegree := hdP
            _ ≤ d := by exact_mod_cast hPdeg
        · have hcast : ((N : ℕ) : ℝ) = (S.card : ℝ) * (((M + n - 1).choose n : ℕ) : ℝ) +
              (q ^ n - S.card) * (((M' + n - 1).choose n : ℕ) : ℝ) := by
            have hle : S.card ≤ Fintype.card F ^ n := by
              have : S.card ≤ Fintype.card (Fin n → F) := Finset.card_le_univ S
              rwa [Fintype.card_fun, Fintype.card_fin] at this
            rw [hN]
            push_cast [Nat.cast_sub hle]
            ring
          rw [← hcast]
          exact_mod_cast hmin)
    have : ψ ^ n = q ^ n * x ^ n := by rw [hψ, mul_pow]
    linarith
  have hconj1 : q ^ n * (x ^ n - (1 - ε) ^ n) / (1 - (1 - ε) ^ n) ≤ (S.card : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hx' : x = 1 - (δ * ε * (1 - α) * q ^ r + q - 1) / (δ * q ^ r + q - 1) := by
    rw [hx]
    field_simp
    ring
  refine ⟨hconj1, ?_, ?_⟩
  · rw [hcompl]
    have : q ^ n * (1 - x ^ n) / (1 - (1 - ε) ^ n) =
        q ^ n - q ^ n * (x ^ n - (1 - ε) ^ n) / (1 - (1 - ε) ^ n) := by
      field_simp
      ring
    rw [this]
    linarith
  · rw [← hx']

end ListHashFurstenberg.Main
end

theorem solution : type_of% @ListHashFurstenberg.Main.chk_theorem_2_8 := @ListHashFurstenberg.Main.chk_theorem_2_8

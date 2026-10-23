-- Prove2me | solution 1 for KedlayaUmans.FrobeniusLift.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T06:58:47.710831+00:00
-- url     : https://prove2.me/submissions/56c6ff53-a832-4ab6-a15b-e642bdce118c

import Mathlib
import Definitions.Def_KedlayaUmans_FrobeniusLift_Setup
import Definitions.Def_KedlayaUmans_FrobeniusLift_LiftProject

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace KedlayaUmans.FrobeniusLift.Aux961

open KedlayaUmans.FrobeniusLift

section

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p]
    (P : (ZMod p)[X]) [Fact (Irreducible P)]

lemma one_lt_h : 1 < h p P := by
  have hc : 0 < P.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible (Fact.out : Irreducible P))
  exact Nat.one_lt_pow hc.ne' (Fact.out : p.Prime).one_lt

lemma pow_h_self {A : Type*} [Monoid A] (x : A) (hx : x ^ (h p P - 1) = 1) :
    x ^ h p P = x := by
  have hh := one_lt_h p P
  calc x ^ h p P = x ^ (h p P - 1) * x := by rw [← pow_succ]; congr 1; omega
    _ = x := by rw [hx, one_mul]

lemma pow_h_pow_self {A : Type*} [Monoid A] (x : A) (hx : x ^ (h p P - 1) = 1) (i : ℕ) :
    x ^ (h p P ^ i) = x := by
  induction i with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, pow_h_self p P x hx]

lemma h_pow_eq (i : ℕ) : h p P ^ i = p ^ (P.natDegree * i) := by
  rw [h, pow_mul]

lemma E_natDegree (η : K p P) : (E p F P η).natDegree = h p P - 1 := by
  rw [E, natDegree_X_pow_sub_C]

lemma E_degree_ne (η : K p P) : (E p F P η).degree ≠ 0 := by
  have hh := one_lt_h p P
  rw [degree_eq_natDegree (E_monic p F P η).ne_zero, E_natDegree]
  norm_cast
  omega

instance S_nontrivial (η : K p P) : Nontrivial (S p F P η) := by
  refine nontrivial_of_ne 1 0 ?_
  intro h0
  rw [← map_one (AdjoinRoot.mk (E p F P η)), AdjoinRoot.mk_eq_zero] at h0
  have hh := one_lt_h p P
  exact (E_monic p F P η).not_dvd_of_natDegree_lt one_ne_zero
    (by rw [natDegree_one, E_natDegree]; omega) h0

instance S_charP (η : K p P) : CharP (S p F P η) p :=
  charP_of_injective_algebraMap' F p

/-- the twisted polynomial `(σ^i g)(η^i Z)` -/
noncomputable def G {m : ℕ} (η : K p P) (α : Fin m → F) (i : ℕ) : (R p F P)[X] :=
  ((gAlpha p F P η α).map (sigma p F P i)).comp (C (ι p F P η ^ i) * X)

lemma root_pow (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (i : ℕ) :
    (AdjoinRoot.root (E p F P η)) ^ (h p P ^ i) =
      AdjoinRoot.of (E p F P η) (ι p F P η) ^ i * AdjoinRoot.root (E p F P η) := by
  set z := AdjoinRoot.root (E p F P η)
  set ζ := AdjoinRoot.of (E p F P η) (ι p F P η)
  have hh := one_lt_h p P
  have hz : z ^ (h p P - 1) = ζ := by
    have := AdjoinRoot.mk_self (f := E p F P η)
    conv at this => lhs; arg 2; rw [E]
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at this
    exact sub_eq_zero.mp this
  have hζ : ζ ^ h p P = ζ := by
    simp only [ζ, ← map_pow]
    congr 2
    exact pow_h_self p P η hη.pow_eq_one
  have hzh : z ^ h p P = ζ * z := by
    rw [← hz, ← pow_succ]; congr 1; omega
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, ih, mul_pow, ← pow_mul, mul_comm n, pow_mul, hζ, hzh, pow_succ,
      mul_assoc]

lemma phi_pow {m : ℕ} (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (α : Fin m → F) (i : ℕ) :
    (phi p F P η α) ^ (h p P ^ i) = AdjoinRoot.mk (E p F P η) (G p F P η α i) := by
  have key : ∀ Q : (R p F P)[X], AdjoinRoot.mk (E p F P η) Q =
      Q.eval₂ (AdjoinRoot.of (E p F P η)) (AdjoinRoot.root (E p F P η)) := by
    intro Q
    rw [← AdjoinRoot.aeval_eq, aeval_def, AdjoinRoot.algebraMap_eq]
  rw [phi, key, key, G, eval₂_comp, h_pow_eq]
  rw [← iterateFrobenius_def (R := S p F P η) p, hom_eval₂, eval₂_map, iterateFrobenius_def,
    ← h_pow_eq, root_pow p F P η hη]
  congr 1
  · ext x
    all_goals simp only [RingHom.comp_apply, sigma, iterateFrobenius_def, map_pow]
  · rw [eval₂_mul, eval₂_C, eval₂_X, map_pow]

lemma inj_nodes {m : ℕ} (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (hm : m < h p P) :
    Set.InjOn (node p P m η) (Finset.univ : Finset (Fin m)) := by
  intro a _ b _ hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [node] at hab
  exact Fin.ext (hη.pow_inj (by omega) (by omega) hab)

lemma natDeg_g {m : ℕ} (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (hm : m < h p P)
    (α : Fin m → F) : (gAlpha p F P η α).natDegree ≤ m - 1 := by
  rw [gAlpha]
  apply natDegree_sum_le_of_forall_le
  intro i _
  refine (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans ?_)
  rw [Lagrange.natDegree_basis (inj_nodes p P η hη hm) (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]

lemma natDeg_G {m : ℕ} (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (hm : m < h p P)
    (α : Fin m → F) (i : ℕ) : (G p F P η α i).natDegree ≤ m - 1 := by
  rw [G]
  refine natDegree_comp_le.trans ?_
  calc _ ≤ (m - 1) * 1 :=
        Nat.mul_le_mul (natDegree_map_le.trans (natDeg_g p F P η hη hm α)) ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    _ = m - 1 := mul_one _

lemma eval_g_node {m : ℕ} (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (hm : m < h p P)
    (α : Fin m → F) (i : Fin m) :
    (gAlpha p F P η α).eval (ι p F P (η ^ (i : ℕ))) =
      algebraMap F (R p F P) (sigmaInv p F P i (α i)) := by
  have hn : node p P m η i = η ^ (i : ℕ) := rfl
  rw [gAlpha, eval_finsetSum, Finset.sum_eq_single i]
  · rw [eval_mul, eval_C, eval_map, eval₂_at_apply, ← hn,
      Lagrange.eval_basis_self (inj_nodes p P η hη hm) (Finset.mem_univ _), map_one, mul_one]
  · intro j _ hj
    rw [eval_mul, eval_C, eval_map, eval₂_at_apply, ← hn,
      Lagrange.eval_basis_of_ne hj (Finset.mem_univ _), map_zero, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

lemma eval_G {m : ℕ} (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1)) (hm : m < h p P)
    (α : Fin m → F) (i : Fin m) :
    (G p F P η α i).eval 1 = algebraMap F (R p F P) (α i) := by
  have hfix : sigma p F P i (ι p F P (η ^ (i : ℕ))) = ι p F P (η ^ (i : ℕ)) := by
    simp only [sigma, iterateFrobenius_def, ← map_pow]
    congr 1
    rw [← h_pow_eq, ← pow_mul, mul_comm, pow_mul, pow_h_pow_self p P η hη.pow_eq_one]
  rw [G, eval_comp, eval_mul, eval_C, eval_X, mul_one, ← map_pow, eval_map, ← hfix,
    eval₂_at_apply, eval_g_node p F P η hη hm α i, sigma, ← RingHom.map_iterateFrobenius,
    sigmaInv, ← coe_iterateFrobeniusEquiv, RingEquiv.apply_symm_apply]

theorem main_aux (m d : ℕ) (hd : 1 ≤ d) (hmd : m ^ 2 * d < h p P)
    (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1))
    (f : MvPolynomial (Fin m) F) (hf : ∀ i, f.degreeOf i ≤ d - 1) (α : Fin m → F) :
    pi p F P η ((fStar p F P η f).eval (phi p F P η α)) =
      algebraMap F (R p F P) (MvPolynomial.eval α f) := by
  have hh := one_lt_h p P
  have hm : m < h p P := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · omega
    · calc m ≤ m ^ 2 * d := by nlinarith
        _ < _ := hmd
  set Q : (R p F P)[X] := MvPolynomial.eval₂ (C.comp (algebraMap F (R p F P)))
      (fun i : Fin m => G p F P η α i) f with hQ
  have h1 : (fStar p F P η f).eval (phi p F P η α) = AdjoinRoot.mk (E p F P η) Q := by
    rw [fStar, ← coe_evalRingHom, MvPolynomial.eval₂_comp_left, hQ, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext x
      simp only [RingHom.comp_apply, coe_evalRingHom, eval_C, AdjoinRoot.mk_C]
      rw [IsScalarTower.algebraMap_apply F (R p F P) (S p F P η)]
      rfl
    · funext i
      simp only [Function.comp_apply, coe_evalRingHom, eval_pow, eval_X,
        phi_pow p F P η hη α]
  have hGdeg : ∀ i : Fin m, (G p F P η α i).natDegree ≤ m - 1 :=
    fun i => natDeg_G p F P η hη hm α i
  have hdeg : Q.natDegree ≤ m * ((d - 1) * (m - 1)) := by
    rw [hQ, MvPolynomial.eval₂_eq']
    apply natDegree_sum_le_of_forall_le
    intro e he
    rw [RingHom.comp_apply]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i : Fin m, (G p F P η α (i : ℕ) ^ e i).natDegree ≤ ∑ _i : Fin m, (d - 1) * (m - 1) := by
          apply Finset.sum_le_sum
          intro i _
          refine natDegree_pow_le.trans ?_
          exact Nat.mul_le_mul ((MvPolynomial.monomial_le_degreeOf i he).trans (hf i)) (hGdeg i)
      _ = m * ((d - 1) * (m - 1)) := by simp
  have hlt : Q.natDegree < (E p F P η).natDegree := by
    rw [E_natDegree]
    refine lt_of_le_of_lt hdeg ?_
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp; omega
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, d = b + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have key : (a + 1) * (b * a) + 1 ≤ (a + 1) ^ 2 * (b + 1) := by ring_nf; nlinarith
    generalize (a + 1) * (b * a) = X at *
    generalize (a + 1) ^ 2 * (b + 1) = Y at *
    omega
  rw [h1, pi, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (E_monic p F P η)).mpr (degree_lt_degree hlt),
    ← coe_evalRingHom, hQ, MvPolynomial.eval₂_comp_left]
  have hev : ∀ i : Fin m, (evalRingHom (1 : R p F P)) (G p F P η α i) =
      algebraMap F (R p F P) (α i) := fun i => by
    rw [coe_evalRingHom]; exact eval_G p F P η hη hm α i
  simp only [Function.comp_def, hev]
  rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  congr 1
  ext x
  simp

end

end KedlayaUmans.FrobeniusLift.Aux961

open KedlayaUmans.FrobeniusLift Polynomial in
theorem solution (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p]
    (P : (ZMod p)[X]) [Fact (Irreducible P)]
    (m d : ℕ) (hd : 1 ≤ d) (hmd : m ^ 2 * d < h p P)
    (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1))
    (f : MvPolynomial (Fin m) F) (hf : ∀ i, f.degreeOf i ≤ d - 1) (α : Fin m → F) :
    pi p F P η ((fStar p F P η f).eval (phi p F P η α)) =
      algebraMap F (R p F P) (MvPolynomial.eval α f) := by
  exact KedlayaUmans.FrobeniusLift.Aux961.main_aux p F P m d hd hmd η hη f hf α

-- Prove2me | solution 1 for MvPolynomial.finrank_piece_eq_of_maximal_growth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6a26be68-9d97-51ed-8be4-7c6ad10d631d

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
import Theorems.Thm_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_finrank_piece_eq_of_maximal_growth

set_option autoImplicit false

namespace GotzPers

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

section Pieces

variable {L : Type} [Field L]

noncomputable def Ik (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Submodule L ↥(homogeneousSubmodule (Fin (n + 1)) L d) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) L d).subtype (I.restrictScalars L)

theorem mem_Ik {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (x : ↥(homogeneousSubmodule (Fin (n + 1)) L d)) :
    x ∈ Ik I d ↔ (x : MvPolynomial (Fin (n + 1)) L) ∈ I := Iff.rfl

theorem Ik_mono {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} (h : I ≤ I') (d : ℕ) : Ik I d ≤ Ik I' d :=
  fun x hx => (mem_Ik x).mpr (h ((mem_Ik x).mp hx))

theorem piece_eq (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    piece I d = (↥(homogeneousSubmodule (Fin (n + 1)) L d) ⧸ Ik I d) := rfl

scoped instance finite_homogeneousSubmodule (d : ℕ) :
    Module.Finite L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport L {x : Fin (n + 1) →₀ ℕ | x.degree = d})

scoped instance finite_piece (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) : Module.Finite L (piece I d) :=
  Module.Finite.quotient L _

theorem finrank_piece_add (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Module.finrank L (piece I d) + Module.finrank L ↥(Ik I d) =
      Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  unfold Ik; exact Submodule.finrank_quotient_add_finrank _

theorem finrank_piece_eq_of_Ik_eq {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ} (h : Ik I d = Ik I' d) :
    Module.finrank L (piece I d) = Module.finrank L (piece I' d) := by
  unfold Ik at h; exact (Submodule.quotEquivOfEq _ _ h).finrank_eq

theorem finrank_piece_eq_zero_of_forall {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (h : ∀ f : MvPolynomial (Fin (n + 1)) L, f.IsHomogeneous d → f ∈ I) : Module.finrank L (piece I d) = 0 := by
  have htop : Ik I d = ⊤ := eq_top_iff.mpr fun x _ => (mem_Ik x).mpr (h x x.2)
  have h1 := finrank_piece_add I d
  rw [htop, finrank_top] at h1
  omega

theorem mem_of_finrank_piece_eq_zero {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (h : Module.finrank L (piece I d) = 0) (f : MvPolynomial (Fin (n + 1)) L) (hf : f.IsHomogeneous d) :
    f ∈ I := by
  have h1 := finrank_piece_add I d
  rw [h, zero_add] at h1
  have htop : Ik I d = ⊤ := Submodule.eq_top_of_finrank_eq h1
  have : (⟨f, hf⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) L d)) ∈ Ik I d := by rw [htop]; trivial
  exact (mem_Ik _).mp this

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) L) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) L) q d : MvPolynomial (Fin (n + 1)) L) =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem homogeneousComponent_mul_add {G : MvPolynomial (Fin (n + 1)) L} {m : ℕ} (hG : G.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) L) (d : ℕ) :
    homogeneousComponent (m + d) (a * G) = homogeneousComponent d a * G := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) L)
    (a := a) (show G ∈ homogeneousSubmodule (Fin (n + 1)) L m from hG) (Nat.le_add_right m d)
  rw [decompose_eq, decompose_eq, Nat.add_sub_cancel_left] at this
  exact this

theorem span_homogeneous (s : Set (MvPolynomial (Fin (n + 1)) L))
    (hs : ∀ p ∈ s, ∃ i : ℕ, p.IsHomogeneous i) :
    ∀ p ∈ Ideal.span s, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span s := by
  intro p hp d
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) L) s (fun x hx => hs x hx)
  have := H d hp
  rwa [decompose_eq] at this

end Pieces

section Regen

variable {L : Type} [Field L]

theorem exists_eq_sum_X_mul (k : ℕ) (g : MvPolynomial (Fin (n + 1)) L) (hg : g.IsHomogeneous (k + 1)) :
    ∃ q : Fin (n + 1) → MvPolynomial (Fin (n + 1)) L, (∀ i, (q i).IsHomogeneous k) ∧ g = ∑ i, X i * q i := by
  classical
  have hg' : g ∈ (Submodule.span L ((fun μ : Fin (n + 1) →₀ ℕ => monomial μ (1 : L)) ''
      {μ : Fin (n + 1) →₀ ℕ | μ.degree = k + 1}) : Submodule L (MvPolynomial (Fin (n + 1)) L)) := by
    have : g ∈ homogeneousSubmodule (Fin (n + 1)) L (k + 1) := hg
    rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single] at this
    exact this
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨μ, hμ, rfl⟩ := hx
      have hμ' : μ.degree = k + 1 := hμ
      have hne : μ ≠ 0 := by rintro rfl; simp at hμ'
      obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
        by_contra h; push Not at h; exact hne (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ μ := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
      have hdeg : (μ - Finsupp.single i 1).degree = k := by
        have h1 : μ - Finsupp.single i 1 + Finsupp.single i 1 = μ := tsub_add_cancel_of_le hle
        have h2 := congrArg Finsupp.degree h1
        rw [map_add, Finsupp.degree_single, hμ'] at h2
        omega
      refine ⟨Pi.single i (monomial (μ - Finsupp.single i 1) 1), fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same]; exact isHomogeneous_monomial _ hdeg
        · rw [Pi.single_eq_of_ne hj]; exact isHomogeneous_zero _ _ _
      · rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same]
        show (monomial μ (1 : L)) = monomial (Finsupp.single i 1) 1 * monomial (μ - Finsupp.single i 1) 1
        rw [monomial_mul, one_mul, add_tsub_cancel_of_le hle]
  | zero => exact ⟨0, fun _ => isHomogeneous_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨q₁, hq₁, rfl⟩ := hx
      obtain ⟨q₂, hq₂, rfl⟩ := hy
      exact ⟨q₁ + q₂, fun i => (hq₁ i).add (hq₂ i), by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]⟩
  | smul c x _ hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      refine ⟨fun i => C c * q i, fun i => (hq i).C_mul c, ?_⟩
      rw [smul_eq_C_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm]

theorem finrank_piece_succ_eq_zero {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {k : ℕ}
    (h : Module.finrank L (piece I k) = 0) : Module.finrank L (piece I (k + 1)) = 0 := by
  apply finrank_piece_eq_zero_of_forall
  intro g hg
  obtain ⟨q, hq, rfl⟩ := exists_eq_sum_X_mul k g hg
  exact I.sum_mem fun i _ => I.mul_mem_left _ (mem_of_finrank_piece_eq_zero h (q i) (hq i))

variable {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) L))
  (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)

include hJ in
theorem homogeneous_of_gen : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  exact span_homogeneous s fun p hp => ⟨m, hs p hp⟩

end Regen

section Full

variable (L : Type) [Field L]

theorem finrank_homogeneousSubmodule (d : ℕ) :
    Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) = Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = d} := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport L {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem natCard_degree_zero : Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = 0} = 1 := by
  haveI : Unique {x : Fin (n + 1) →₀ ℕ // x.degree = 0} :=
    { default := ⟨0, by simp⟩
      uniq := fun x => Subtype.ext ((Finsupp.degree_eq_zero_iff _).mp x.2) }
  exact Nat.card_unique

theorem finrank_homogeneousSubmodule_le (d : ℕ) :
    Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) ≤ (n + d).choose n := by
  classical
  rw [finrank_homogeneousSubmodule]
  let e : {s : Fin (n + 1) →₀ ℕ // s.degree = d} → Sym (Fin (n + 1)) d := fun s =>
    ⟨Finsupp.toMultiset s.1, by
      have h2 := s.2
      rw [Finsupp.degree_apply] at h2
      rw [Finsupp.card_toMultiset]
      simpa [Finsupp.sum] using h2⟩
  have he : Function.Injective e := by
    intro s t h
    have h1 : Finsupp.toMultiset s.1 = Finsupp.toMultiset t.1 :=
      congrArg (fun x : Sym (Fin (n + 1)) d => (x : Multiset (Fin (n + 1)))) h
    have h2 := congrArg Multiset.toFinsupp h1
    rw [Finsupp.toMultiset_toFinsupp, Finsupp.toMultiset_toFinsupp] at h2
    exact Subtype.ext h2
  haveI : Finite {s : Fin (n + 1) →₀ ℕ // s.degree = d} := Finite.of_injective e he
  have := Nat.card_le_card_of_injective e he
  rw [Nat.card_eq_fintype_card (α := Sym (Fin (n + 1)) d), Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + d - 1 = n + d by omega] at this
  rw [Nat.choose_symm_add]; exact this

theorem finrank_piece_le (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Module.finrank L (piece I d) ≤ (n + d).choose n := by
  have := finrank_piece_add I d
  have := finrank_homogeneousSubmodule_le (n := n) L d
  omega

theorem finrank_piece_bot (d : ℕ) :
    Module.finrank L (piece (⊥ : Ideal (MvPolynomial (Fin (n + 1)) L)) d) =
      Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = d} := by
  have h1 := finrank_piece_add (⊥ : Ideal (MvPolynomial (Fin (n + 1)) L)) d
  have h2 : Ik (⊥ : Ideal (MvPolynomial (Fin (n + 1)) L)) d = ⊥ :=
    (Submodule.eq_bot_iff _).mpr fun x hx => Subtype.ext ((mem_Ik x).mp hx)
  rw [h2, finrank_bot, add_zero, finrank_homogeneousSubmodule] at h1
  exact h1

theorem eq_bot_of_finrank_piece_eq {e : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) L))
    (hI : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous e) ∧ I = Ideal.span s)
    (h : Module.finrank L (piece I e) = Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = e}) : I = ⊥ := by
  have h1 := finrank_piece_add I e
  rw [h, ← finrank_homogeneousSubmodule L e] at h1
  have h2 : Module.finrank L ↥(Ik I e) = 0 := by omega
  have h3 : Ik I e = ⊥ := Submodule.finrank_eq_zero.mp h2
  obtain ⟨s, hs, rfl⟩ := hI
  refine Ideal.span_eq_bot.mpr fun p hp => ?_
  have : (⟨p, hs p hp⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) L e)) ∈ Ik (Ideal.span s) e :=
    (mem_Ik _).mpr (Ideal.subset_span hp)
  rw [h3, Submodule.mem_bot] at this
  exact congrArg Subtype.val this

end Full

section Forms

variable {L : Type} [Field L] {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) L))
  (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)

noncomputable def formsIdeal (e : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) L)) :
    Ideal (MvPolynomial (Fin (n + 1)) L) :=
  Ideal.span {p | p ∈ J ∧ p.IsHomogeneous e}

theorem formsIdeal_le (e : ℕ) : formsIdeal e J ≤ J := Ideal.span_le.mpr fun _ hp => hp.1

theorem formsIdeal_generated (e : ℕ) : ∃ s : Set (MvPolynomial (Fin (n + 1)) L),
    (∀ p ∈ s, p.IsHomogeneous e) ∧ formsIdeal e J = Ideal.span s := ⟨_, fun _ hp => hp.2, rfl⟩

include hJ in

theorem mem_formsIdeal_of_mem {e : ℕ} (he : m ≤ e) : ∀ (i : ℕ) (x : MvPolynomial (Fin (n + 1)) L),
    x.IsHomogeneous (e + i) → x ∈ J → x ∈ formsIdeal e J
  | 0, x, hx, hxJ => Ideal.subset_span ⟨hxJ, hx⟩
  | i + 1, x, hx, hxJ => by
      obtain ⟨s, hs, hJs⟩ := hJ
      rw [hJs] at hxJ
      obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.mp hxJ
      set d := e + i + 1 - m with hd
      have hd1 : 1 ≤ d := by omega
      have hsplit : e + i + 1 = m + d := by omega

      have hq : ∀ t : Fin N, ∃ q : Fin (n + 1) → MvPolynomial (Fin (n + 1)) L,
          (∀ k, (q k).IsHomogeneous (d - 1)) ∧ homogeneousComponent d (f t) = ∑ k, X k * q k := fun t =>
        exists_eq_sum_X_mul (d - 1) _ (by rw [Nat.sub_add_cancel hd1]; exact homogeneousComponent_isHomogeneous _ _)
      choose q hq₁ hq₂ using hq
      have hx1 : x = homogeneousComponent (e + i + 1) x := by
        rw [homogeneousComponent_of_mem (show x ∈ homogeneousSubmodule (Fin (n + 1)) L (e + i + 1) from hx),
          if_pos rfl]
      have hx2 : x = ∑ k, X k * ∑ t, q t k * (g t : MvPolynomial (Fin (n + 1)) L) := by
        rw [hx1, ← hfg, hsplit, map_sum]
        have : ∀ t : Fin N, homogeneousComponent (m + d) (HSMul.hSMul (f t) (g t : MvPolynomial (Fin (n + 1)) L)) =
            ∑ k, X k * (q t k * (g t : MvPolynomial (Fin (n + 1)) L)) := fun t => by
          rw [smul_eq_mul, homogeneousComponent_mul_add (hs _ (g t).2) (f t) d, hq₂ t, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
        rw [Finset.sum_congr rfl fun t _ => this t, Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      rw [hx2]
      refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_
      refine mem_formsIdeal_of_mem he i _ ?_ ?_
      · have : (∑ t, q t k * (g t : MvPolynomial (Fin (n + 1)) L)).IsHomogeneous (d - 1 + m) :=
          IsHomogeneous.sum _ _ _ fun t _ => (hq₁ t k).mul (hs _ (g t).2)
        rwa [show d - 1 + m = e + i by omega] at this
      · rw [hJs]; exact Ideal.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (g t).2)

include hJ in
theorem Ik_formsIdeal_eq {e : ℕ} (he : m ≤ e) {k : ℕ} (hk : e ≤ k) : Ik (formsIdeal e J) k = Ik J k := by
  apply le_antisymm (Ik_mono (formsIdeal_le J e) k)
  intro x hx
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact (mem_Ik x).mpr (mem_formsIdeal_of_mem J hJ he i x x.2 ((mem_Ik x).mp hx))

end Forms

section Growth

variable (h : ℕ → ℕ) {m : ℕ}
  (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
  (h₃ : ∀ e, m ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1))

include h₂ h₃ in

theorem h_succ_eq {e : ℕ} (hme : m ≤ e) (he : 1 ≤ e) : h (e + 1) = Nat.macaulayPow e (h e) := by
  obtain ⟨K₀, _, J₀, hJ₀, he0, he1⟩ := h₃ e hme
  apply le_antisymm
  · rw [← he1, ← he0]
    exact MvPolynomial.finrank_piece_succ_le_macaulayPow n e he K₀ J₀ (homogeneous_of_gen J₀ hJ₀)
  · have hle : h e ≤ (n + e).choose n := he0 ▸ finrank_piece_le K₀ J₀ e
    obtain ⟨J₁, hJ₁, h1e, h1e1⟩ :=
      MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow n e he (h e) hle K₀
    rw [← h1e1]
    exact h₂ e hme K₀ J₁ hJ₁ h1e

end Growth

section Positive

variable {K : Type} [Field K] (h : ℕ → ℕ) {m : ℕ}
  (hgrowth : ∀ e, m ≤ e → h (e + 1) = Nat.macaulayPow e (h e))
  (J : Ideal (MvPolynomial (Fin (n + 1)) K))
  (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
  (hm : Module.finrank K (piece J m) = h m) (hm₁ : Module.finrank K (piece J (m + 1)) = h (m + 1))

include hgrowth hJ hm hm₁ in

theorem two_values : ∀ j : ℕ,
    Module.finrank K (piece J (m + j)) = h (m + j) ∧ Module.finrank K (piece J (m + j + 1)) = h (m + j + 1)
  | 0 => ⟨hm, hm₁⟩
  | j + 1 => by
      obtain ⟨hj0, hj1⟩ := two_values j
      refine ⟨hj1, ?_⟩

      have he : m ≤ m + j := Nat.le_add_right m j
      have hk : ∀ k, m + j ≤ k →
          Module.finrank K (piece (formsIdeal (m + j) J) k) = Module.finrank K (piece J k) :=
        fun k hk => finrank_piece_eq_of_Ik_eq (Ik_formsIdeal_eq J hJ he hk)
      have step := MvPolynomial.finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow n (m + j)
        K (formsIdeal (m + j) J) (formsIdeal_generated J (m + j))
        (by rw [hk (m + j) le_rfl, hk (m + j + 1) (by omega), hj0, hj1]; exact hgrowth (m + j) he)
      rw [hk (m + j + 1) (by omega), hk (m + j + 2) (by omega), hj1, ← hgrowth (m + j + 1) (by omega)] at step
      exact step

end Positive

section Zero

variable (h : ℕ → ℕ)
  (h₃ : ∀ e, 0 ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1))

include h₃ in
theorem h_eq_zero (h0 : h 0 = 0) : ∀ e, h e = 0
  | 0 => h0
  | e + 1 => by
      obtain ⟨K₀, _, J₀, -, he0, he1⟩ := h₃ e (Nat.zero_le e)
      rw [← he1]
      exact finrank_piece_succ_eq_zero (by rw [he0]; exact h_eq_zero h0 e)

include h₃ in
theorem h_eq_full (h0 : h 0 = Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = 0}) :
    ∀ e, h e = Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = e}
  | 0 => h0
  | e + 1 => by
      obtain ⟨K₀, _, J₀, hJ₀, he0, he1⟩ := h₃ e (Nat.zero_le e)
      have hbot : J₀ = ⊥ := eq_bot_of_finrank_piece_eq K₀ J₀ hJ₀ (by rw [he0]; exact h_eq_full h0 e)
      rw [← he1, hbot]
      exact finrank_piece_bot K₀ (e + 1)

variable {K : Type} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
  (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous 0) ∧ J = Ideal.span s)
  (hm : Module.finrank K (piece J 0) = h 0)

include h₃ hJ hm in
theorem persistence_zero : ∀ e, Module.finrank K (piece J e) = h e := by
  rcases Nat.eq_zero_or_pos (Module.finrank K (piece J 0)) with h0 | h0
  ·
    have hz : ∀ e, Module.finrank K (piece J e) = 0 := by
      intro e
      induction e with
      | zero => exact h0
      | succ e ih => exact finrank_piece_succ_eq_zero ih
    intro e
    rw [hz e, h_eq_zero h h₃ (by rw [← hm, h0]) e]
  ·
    have hle : Module.finrank K (piece J 0) ≤ Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = 0} := by
      have := finrank_piece_add J 0
      rw [finrank_homogeneousSubmodule] at this
      omega
    have hfull : Module.finrank K (piece J 0) = Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = 0} := by
      have h1 : Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = 0} = 1 := natCard_degree_zero
      omega
    have hbot : J = ⊥ := eq_bot_of_finrank_piece_eq K J hJ hfull
    intro e
    rw [hbot, finrank_piece_bot, h_eq_full h h₃ (by rw [← hm, hfull]) e]

end Zero

theorem main (n m : ℕ) (h : ℕ → ℕ)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (h₃ : ∀ e, m ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1))
    (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hm : Module.finrank K (piece J m) = h m) (hm₁ : Module.finrank K (piece J (m + 1)) = h (m + 1)) :
    ∀ e, m ≤ e → Module.finrank K (piece J e) = h e := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · intro e _
    exact persistence_zero h h₃ J hJ hm e
  · have hgrowth : ∀ e, m ≤ e → h (e + 1) = Nat.macaulayPow e (h e) :=
      fun e hme => h_succ_eq h h₂ h₃ hme (by omega)
    intro e he
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le he
    exact (two_values h hgrowth J hJ hm hm₁ j).1

end GotzPers
p2m_reactivate "P2MW.S_MvPolynomial_finrank_piece_eq_of_maximal_growth.GotzPers"

open MvPolynomial AlgebraicGeometry.HilbertFunctor in
theorem solution
    (n m : ℕ) (h : ℕ → ℕ)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (h₃ : ∀ e, m ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1))
    (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hm : Module.finrank K (piece J m) = h m) (hm₁ : Module.finrank K (piece J (m + 1)) = h (m + 1)) :
    ∀ e, m ≤ e → Module.finrank K (piece J e) = h e :=
  GotzPers.main n m h h₂ h₃ K J hJ hm hm₁

end S_MvPolynomial_finrank_piece_eq_of_maximal_growth
end P2MW
export P2MW.S_MvPolynomial_finrank_piece_eq_of_maximal_growth (solution)

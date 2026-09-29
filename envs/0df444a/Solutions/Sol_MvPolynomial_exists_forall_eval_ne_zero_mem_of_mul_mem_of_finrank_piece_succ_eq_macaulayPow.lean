-- Prove2me | solution 1 for MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/99f6931d-e3fe-55d7-aea3-b9d29ce65427

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
import Theorems.Thm_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span
import Theorems.Thm_MvPolynomial_relation_mem_span_of_linear_of_forall_relation_modulo_mem_span
import Theorems.Thm_MvPolynomial_relation_mem_span_of_forall_isHomogeneous_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow

set_option autoImplicit false

namespace GotzRegW2

namespace Mac

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

theorem top_eq_of (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) :
    top d a = k := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have : (k + 1).choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h
    have := choose_top_le d a
    omega
  · by_contra h
    push Not at h
    have := lt_choose_of_top_lt d a h
    omega

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

theorem top_zero_right (d : ℕ) : top d 0 = d := top_eq_of d 0 d (by simp) (by simp)

theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

theorem top_zero_left (a : ℕ) : top 0 a = a := top_eq_of 0 a a (by simp) (by simp)

theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      show _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem macaulayPow_mono : ∀ (d : ℕ) {a b : ℕ}, a ≤ b → Nat.macaulayPow d a ≤ Nat.macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow_zero]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ, macaulayPow_succ, ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono d hr
        omega
      · have h1 : Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ Nat.macaulayPow (d + 1) b := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, rem_zero_right, macaulayPow_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

theorem lt_of_macaulayPow_add_le {d t s : ℕ} (h : Nat.macaulayPow d t + s ≤ Nat.macaulayPow d s) (hs : 0 < s) :
    t < s := by
  by_contra ht
  have := macaulayPow_mono d (not_lt.mp ht)
  omega

end Mac

open MvPolynomial AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

variable {L : Type} [Field L] {n : ℕ}

noncomputable def Ik (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Submodule L ↥(homogeneousSubmodule (Fin (n + 1)) L d) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) L d).subtype (I.restrictScalars L)

theorem mem_Ik {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (x : ↥(homogeneousSubmodule (Fin (n + 1)) L d)) :
    x ∈ Ik I d ↔ (x : MvPolynomial (Fin (n + 1)) L) ∈ I := Iff.rfl

theorem Ik_mono {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} (h : I ≤ I') (d : ℕ) : Ik I d ≤ Ik I' d :=
  fun x hx => (mem_Ik x).mpr (h ((mem_Ik x).mp hx))

scoped instance finite_homogeneousSubmodule (d : ℕ) :
    Module.Finite L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport L {x : Fin (n + 1) →₀ ℕ | x.degree = d})

noncomputable def Jk (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) : Submodule L (MvPolynomial (Fin (n + 1)) L) :=
  I.restrictScalars L ⊓ homogeneousSubmodule (Fin (n + 1)) L d

scoped instance finite_Jk (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) : Module.Finite L ↥(Jk I d) :=
  Module.Finite.of_injective (Submodule.inclusion (inf_le_right : Jk I d ≤ _)) (Submodule.inclusion_injective _)

theorem finrank_piece_add (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Module.finrank L (piece I d) + Module.finrank L ↥(Ik I d) =
      Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  unfold Ik; exact Submodule.finrank_quotient_add_finrank _

theorem finrank_piece_eq_of_Ik_eq {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ} (h : Ik I d = Ik I' d) :
    Module.finrank L (piece I d) = Module.finrank L (piece I' d) := by
  unfold Ik at h; exact (Submodule.quotEquivOfEq _ _ h).finrank_eq

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

theorem exists_eq_sum_mul_of_span {N q : ℕ} (u : Fin N → MvPolynomial (Fin (n + 1)) L)
    (hspan : ∀ w : MvPolynomial (Fin (n + 1)) L, w.IsHomogeneous q → w ∈ Submodule.span L (Set.range u)) :
    ∀ (p : ℕ) (w : MvPolynomial (Fin (n + 1)) L), w.IsHomogeneous (q + p) →
      ∃ d : Fin N → MvPolynomial (Fin (n + 1)) L, (∀ j, (d j).IsHomogeneous p) ∧ w = ∑ j, d j * u j
  | 0, w, hw => by
      obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp (hspan w hw)
      refine ⟨fun j => C (κ j), fun j => isHomogeneous_C _ _, ?_⟩
      rw [← hκ]; exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_C_mul]
  | p + 1, w, hw => by
      obtain ⟨r, hr, rfl⟩ := exists_eq_sum_X_mul (q + p) w hw
      have ih := fun i => exists_eq_sum_mul_of_span u hspan p (r i) (hr i)
      choose d hd hrd using ih
      refine ⟨fun j => ∑ i, X i * d i j, fun j => IsHomogeneous.sum _ _ _ fun i _ => ?_, ?_⟩
      · have := (isHomogeneous_X L i).mul (hd i j); rwa [Nat.add_comm 1 p] at this
      · calc ∑ i, X i * r i = ∑ i, ∑ j, X i * d i j * u j := Finset.sum_congr rfl fun i _ => by
              rw [hrd i, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc]
          _ = ∑ j, (∑ i, X i * d i j) * u j := by
              rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]

theorem span_of_basis {q : ℕ} {ι : Type} (b : Module.Basis ι L ↥(homogeneousSubmodule (Fin (n + 1)) L q))
    (w : MvPolynomial (Fin (n + 1)) L) (hw : w.IsHomogeneous q) :
    w ∈ Submodule.span L (Set.range fun j => (b j : MvPolynomial (Fin (n + 1)) L)) := by
  have hx : (⟨w, hw⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) L q)) ∈ Submodule.span L (Set.range b) := by
    rw [b.span_eq]; trivial
  have := Submodule.mem_map_of_mem (f := (homogeneousSubmodule (Fin (n + 1)) L q).subtype) hx
  rw [Submodule.map_span, ← Set.range_comp] at this
  exact this

variable {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) L))
  (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)

include hJ in
theorem homogeneous_of_gen : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  exact span_homogeneous s fun p hp => ⟨m, hs p hp⟩

include hJ in

theorem eq_top_of_zero (hm : m = 0) (h1 : Module.finrank L (piece J 1) = 0) : J = ⊤ := by
  obtain ⟨s, hs, rfl⟩ := hJ
  subst hm
  have hX : (X 0 : MvPolynomial (Fin (n + 1)) L) ∈ Ideal.span s :=
    mem_of_finrank_piece_eq_zero h1 (X 0) (isHomogeneous_X L 0)
  by_contra hne
  have hs0 : ∀ p ∈ s, p = 0 := by
    intro p hp
    have hpC : p = C (coeff 0 p) := (totalDegree_eq_zero_iff_eq_C).mp (by
      have := (hs p hp).totalDegree_le; omega)
    by_contra hp0
    have hc : coeff 0 p ≠ 0 := fun h => hp0 (by rw [hpC, h, C_0])
    apply hne
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hp)
    rw [hpC]; exact (isUnit_iff_ne_zero.mpr hc).map C
  have hbot : Ideal.span s = ⊥ := Ideal.span_eq_bot.mpr hs0
  rw [hbot, Ideal.mem_bot] at hX
  exact X_ne_zero 0 hX

include hJ in

theorem span_range_eq {ι : Type} (b : Module.Basis ι L ↥(Jk J m)) :
    Ideal.span (Set.range fun i => (b i : MvPolynomial (Fin (n + 1)) L)) = J := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (b i).2.1
  · obtain ⟨s, hs, rfl⟩ := hJ
    refine Ideal.span_le.mpr fun p hp => ?_
    have hx : (⟨p, Ideal.subset_span hp, hs p hp⟩ : ↥(Jk (Ideal.span s) m)) ∈ Submodule.span L (Set.range b) := by
      rw [b.span_eq]; trivial
    have := Submodule.mem_map_of_mem (f := (Jk (Ideal.span s) m).subtype) hx
    rw [Submodule.map_span, ← Set.range_comp] at this

    have hle : Submodule.span L (Set.range (⇑(Jk (Ideal.span s) m).subtype ∘ ⇑b)) ≤
        (Ideal.span (Set.range fun i => (b i : MvPolynomial (Fin (n + 1)) L))).restrictScalars L :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Ideal.subset_span ⟨i, rfl⟩)
    exact hle this

theorem isHomogeneous_linearForm (a : Fin (n + 1) → L) :
    (∑ i, C (a i) * X i : MvPolynomial (Fin (n + 1)) L).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (a i) i

theorem mem_span_of_mem {g m : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) L) (hF : ∀ i, (F i).IsHomogeneous m)
    {w : MvPolynomial (Fin (n + 1)) L} (hw : w.IsHomogeneous m) (h : w ∈ Ideal.span (Set.range F)) :
    w ∈ Submodule.span L (Set.range F) := by
  obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
  have hsum : ∑ i, homogeneousComponent 0 (c₀ i) * F i = w := by
    calc ∑ i, homogeneousComponent 0 (c₀ i) * F i = ∑ i, homogeneousComponent (m + 0) (c₀ i * F i) :=
          Finset.sum_congr rfl fun i _ => (homogeneousComponent_mul_add (hF i) (c₀ i) 0).symm
      _ = homogeneousComponent (m + 0) w := by rw [← map_sum, hc₀]
      _ = w := by rw [homogeneousComponent_of_mem (show w ∈ homogeneousSubmodule (Fin (n + 1)) L (m + 0) from hw), if_pos rfl]
  rw [← hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h0 : homogeneousComponent 0 (c₀ i) = C (coeff 0 (homogeneousComponent 0 (c₀ i))) :=
    (totalDegree_eq_zero_iff_eq_C).mp (Nat.le_zero.mp (homogeneousComponent_isHomogeneous 0 (c₀ i)).totalDegree_le)
  rw [h0, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_eval_ne_zero [Infinite L] {G : MvPolynomial (Fin (n + 1)) L} (hG : G ≠ 0) :
    ∃ a : Fin (n + 1) → L, MvPolynomial.eval a G ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hG (MvPolynomial.funext fun a => by rw [hcon a, map_zero])

section SectionFamily

variable (m' : ℕ) {g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) L) (hF : ∀ i, (F i).IsHomogeneous (m' + 1))
  (ℓ : MvPolynomial (Fin (n + 1)) L) (hℓ : ℓ.IsHomogeneous 1)

noncomputable def NU (L : Type) [Field L] (n m' : ℕ) : ℕ :=
  Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L m')

noncomputable def uB (L : Type) [Field L] (n m' : ℕ) : Fin (NU L n m') → MvPolynomial (Fin (n + 1)) L :=
  fun j => (Module.finBasis L ↥(homogeneousSubmodule (Fin (n + 1)) L m') j : MvPolynomial (Fin (n + 1)) L)

theorem uB_hom (j : Fin (NU L n m')) : (uB L n m' j).IsHomogeneous m' :=
  (Module.finBasis L ↥(homogeneousSubmodule (Fin (n + 1)) L m') j).2

theorem uB_span (w : MvPolynomial (Fin (n + 1)) L) (hw : w.IsHomogeneous m') :
    w ∈ Submodule.span L (Set.range (uB L n m')) :=
  span_of_basis (Module.finBasis L ↥(homogeneousSubmodule (Fin (n + 1)) L m')) w hw

noncomputable def secF : Fin (g + NU L n m') → MvPolynomial (Fin (n + 1)) L :=
  Fin.append F fun j => ℓ * uB L n m' j

theorem secF_left (i : Fin g) : secF m' F ℓ (Fin.castAdd (NU L n m') i) = F i := Fin.append_left F _ i

theorem secF_right (j : Fin (NU L n m')) : secF m' F ℓ (Fin.natAdd g j) = ℓ * uB L n m' j := Fin.append_right F _ j

include hF hℓ in
theorem secF_hom : ∀ i, (secF m' F ℓ i).IsHomogeneous (m' + 1) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_)
  · rw [secF_left]; exact hF i
  · rw [secF_right]; have := hℓ.mul (uB_hom m' j); rwa [show 1 + m' = m' + 1 by omega] at this

theorem le_secF : Ideal.span (Set.range F) ≤ Ideal.span (Set.range (secF m' F ℓ)) := by
  refine Ideal.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castAdd _ i, secF_left m' F ℓ i⟩

theorem secF_le : Ideal.span (Set.range (secF m' F ℓ)) ≤ Ideal.span (Set.range F) ⊔ Ideal.span {ℓ} := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [secF_left]; exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  · rw [secF_right]; exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ℓ))

include hF hℓ in

theorem Ik_secF (j : ℕ) :
    Ik (Ideal.span (Set.range (secF m' F ℓ))) (m' + 1 + j) = Ik (Ideal.span (Set.range F) ⊔ Ideal.span {ℓ}) (m' + 1 + j) := by
  apply le_antisymm (Ik_mono (secF_le m' F ℓ) _)
  intro x hx
  rw [mem_Ik] at hx ⊢
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
  obtain ⟨g', rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have hx1 : (x : MvPolynomial (Fin (n + 1)) L) = homogeneousComponent (m' + 1 + j) x := by
    rw [homogeneousComponent_of_mem x.2, if_pos rfl]
  have hgl : homogeneousComponent (m' + 1 + j) (g' * ℓ) = homogeneousComponent (m' + j) g' * ℓ := by
    rw [show m' + 1 + j = 1 + (m' + j) by omega]; exact homogeneousComponent_mul_add hℓ g' (m' + j)
  rw [hx1, ← hyz, map_add, hgl]
  have hFh : ∀ p ∈ Ideal.span (Set.range F), ∀ i : ℕ, homogeneousComponent i p ∈ Ideal.span (Set.range F) :=
    span_homogeneous _ (by rintro _ ⟨i, rfl⟩; exact ⟨_, hF i⟩)
  refine Ideal.add_mem _ (le_secF m' F ℓ (hFh y hy _)) ?_
  obtain ⟨d, hd, hgd⟩ := exists_eq_sum_mul_of_span (uB L n m') (uB_span m') j (homogeneousComponent (m' + j) g')
    (homogeneousComponent_isHomogeneous _ _)
  rw [hgd, Finset.sum_mul]
  refine Ideal.sum_mem _ fun jj _ => ?_
  rw [mul_assoc, mul_comm (uB L n m' jj) ℓ, ← secF_right m' F ℓ]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

include hF hℓ in
theorem finrank_piece_secF (j : ℕ) :
    Module.finrank L (piece (Ideal.span (Set.range (secF m' F ℓ))) (m' + 1 + j)) =
      Module.finrank L (piece (Ideal.span (Set.range F) ⊔ Ideal.span {ℓ}) (m' + 1 + j)) :=
  finrank_piece_eq_of_Ik_eq (Ik_secF m' F hF ℓ hℓ j)

include hF hℓ in

theorem rel_mod_of_lp
    (hLP : ∀ (d : ℕ) (c : Fin (g + NU L n m') → MvPolynomial (Fin (n + 1)) L), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * secF m' F ℓ i = 0 →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) L)
        {l : Fin (g + NU L n m') → MvPolynomial (Fin (n + 1)) L |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * secF m' F ℓ i = 0}) :
    ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) L), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i ∈ Ideal.span {ℓ} →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) L)
        {l : Fin g → MvPolynomial (Fin (n + 1)) L |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}} := by
  intro d c hc hcℓ
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hcℓ

  have hcFh : (∑ i, c i * F i).IsHomogeneous (1 + (m' + d)) :=
    IsHomogeneous.sum _ _ _ fun i _ => by
      have := (hc i).mul (hF i); rwa [show d + (m' + 1) = 1 + (m' + d) by omega] at this
  set w' := homogeneousComponent (m' + d) w with hw'def
  have hw' : w' * ℓ = ∑ i, c i * F i := by
    rw [hw'def, ← homogeneousComponent_mul_add hℓ w (m' + d), hw, homogeneousComponent_of_mem hcFh, if_pos rfl]
  obtain ⟨e, he, hwe⟩ := exists_eq_sum_mul_of_span (uB L n m') (uB_span m') d w' (homogeneousComponent_isHomogeneous _ _)

  let c' : Fin (g + NU L n m') → MvPolynomial (Fin (n + 1)) L := Fin.append c fun j => -e j
  have hc'l : ∀ i, c' (Fin.castAdd (NU L n m') i) = c i := fun i => Fin.append_left c _ i
  have hc'r : ∀ j, c' (Fin.natAdd g j) = -e j := fun j => Fin.append_right c _ j
  have hc' : ∀ i, (c' i).IsHomogeneous d := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · rw [hc'l]; exact hc i
    · rw [hc'r]; exact (he j).neg
  have hc'F' : ∑ i, c' i * secF m' F ℓ i = 0 := by
    have h1 : ∀ i : Fin g, c' (Fin.castAdd (NU L n m') i) * secF m' F ℓ (Fin.castAdd (NU L n m') i) = c i * F i :=
      fun i => by rw [hc'l, secF_left]
    have h2 : ∀ j : Fin (NU L n m'), c' (Fin.natAdd g j) * secF m' F ℓ (Fin.natAdd g j) = -(e j * uB L n m' j * ℓ) :=
      fun j => by rw [hc'r, secF_right]; ring
    rw [Fin.sum_univ_add, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun j _ => h2 j, ← hw', hwe,
      Finset.sum_mul, Finset.sum_neg_distrib, add_neg_cancel]
  have hmem := hLP d c' hc' hc'F'

  let π := LinearMap.funLeft (MvPolynomial (Fin (n + 1)) L) (MvPolynomial (Fin (n + 1)) L)
    (Fin.castAdd (NU L n m') (n := g))
  have hπc : π c' = c := funext fun i => by rw [LinearMap.funLeft_apply, hc'l]
  rw [← hπc]
  have := Submodule.mem_map_of_mem (f := π) hmem
  rw [Submodule.map_span] at this
  refine Submodule.span_mono ?_ this
  rintro _ ⟨l, ⟨⟨d', hd', hl⟩, hl0⟩, rfl⟩
  refine ⟨⟨d', hd', fun i => by rw [LinearMap.funLeft_apply]; exact hl _⟩, ?_⟩
  have h1 : ∀ i : Fin g, l (Fin.castAdd (NU L n m') i) * secF m' F ℓ (Fin.castAdd (NU L n m') i) = π l i * F i :=
    fun i => by rw [LinearMap.funLeft_apply, secF_left]
  have h2 : ∀ j : Fin (NU L n m'), l (Fin.natAdd g j) * secF m' F ℓ (Fin.natAdd g j) =
      l (Fin.natAdd g j) * uB L n m' j * ℓ := fun j => by rw [secF_right]; ring
  rw [Fin.sum_univ_add, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun j _ => h2 j,
    ← Finset.sum_mul] at hl0
  refine Ideal.mem_span_singleton'.mpr ⟨-(∑ j, l (Fin.natAdd g j) * uB L n m' j), ?_⟩
  rw [eq_neg_of_add_eq_zero_left hl0, neg_mul]

end SectionFamily

theorem lp_of_maximal_growth (n m' : ℕ) (K : Type) [Field K] [Infinite K] :
    ∀ (N g : ℕ) (F : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (F i).IsHomogeneous (m' + 1)) →
      Module.finrank K (piece (Ideal.span (Set.range F)) (m' + 1)) ≤ N →
      Module.finrank K (piece (Ideal.span (Set.range F)) (m' + 1 + 1)) =
        Nat.macaulayPow (m' + 1) (Module.finrank K (piece (Ideal.span (Set.range F)) (m' + 1))) →
      ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
        ∑ i, c i * F i = 0 →
        c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
          {l : Fin g → MvPolynomial (Fin (n + 1)) K | (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} := by
  intro N
  induction N with
  | zero =>
      intro g F hF hN _ d c hc hcF

      have h0 : Module.finrank K (piece (Ideal.span (Set.range F)) (m' + 1)) = 0 := Nat.le_zero.mp hN
      refine MvPolynomial.relation_mem_span_of_forall_isHomogeneous_mem_span n (m' + 1) g K F hF
        (fun w hw => mem_span_of_mem F hF hw (mem_of_finrank_piece_eq_zero h0 w hw)) d c hc hcF
  | succ N ih =>
      intro g F hF hN hmax
      by_cases hs : Module.finrank K (piece (Ideal.span (Set.range F)) (m' + 1)) ≤ N
      · exact ih g F hF hs hmax
      have hs0 : 0 < Module.finrank K (piece (Ideal.span (Set.range F)) (m' + 1)) := by omega
      set J := Ideal.span (Set.range F) with hJdef
      have hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous (m' + 1)) ∧ J = Ideal.span s :=
        ⟨Set.range F, by rintro _ ⟨i, rfl⟩; exact hF i, rfl⟩

      obtain ⟨G, hG, H⟩ :=
        MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow n (m' + 1) K J hJ
          hmax
      obtain ⟨a, ha⟩ := exists_eval_ne_zero hG
      obtain ⟨hcolm, hgrow, heq⟩ := H a ha
      set ℓ : MvPolynomial (Fin (n + 1)) K := ∑ i, C (a i) * X i with hℓdef
      have hℓ : ℓ.IsHomogeneous 1 := isHomogeneous_linearForm a
      have hlt : Module.finrank K (piece (J ⊔ Ideal.span {ℓ}) (m' + 1)) <
          Module.finrank K (piece J (m' + 1)) := Mac.lt_of_macaulayPow_add_le heq.le hs0

      have hp0 := finrank_piece_secF m' F hF ℓ hℓ 0
      have hp1 := finrank_piece_secF m' F hF ℓ hℓ 1
      simp only [Nat.add_zero] at hp0
      rw [← hJdef] at hp0 hp1
      have hLP := ih (g + NU K n m') (secF m' F ℓ) (secF_hom m' F hF ℓ hℓ) (by rw [hp0]; omega)
        (by rw [hp0, hp1]; exact hgrow)

      have hrel := rel_mod_of_lp m' F hF ℓ hℓ hLP
      exact MvPolynomial.relation_mem_span_of_linear_of_forall_relation_modulo_mem_span n (m' + 1) g K F hF ℓ hℓ
        hcolm hrel

theorem main (n m : ℕ) (K : Type) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      ∀ k : ℕ, m ≤ k → ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous k →
        (∑ i, C (a i) * X i) * f ∈ J → f ∈ J := by
  classical
  rcases Nat.eq_zero_or_eq_succ_pred m with hm | hm
  ·
    subst hm
    have h0 : Nat.macaulayPow 0 (Module.finrank K (piece J 0)) = 0 := by simp [Nat.macaulayPow]
    rw [h0] at hmax
    have htop : J = ⊤ := eq_top_of_zero J hJ rfl hmax
    exact ⟨1, one_ne_zero, fun a _ k _ f _ _ => by rw [htop]; exact Submodule.mem_top⟩

  set m' := m.pred with hm'def
  rw [hm] at hJ hmax ⊢
  obtain ⟨G, hG, H⟩ :=
    MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow n (m' + 1) K J hJ hmax
  refine ⟨G, hG, fun a ha k hk f hf hℓf => ?_⟩
  obtain ⟨hcolm, hgrow, -⟩ := H a ha
  set ℓ : MvPolynomial (Fin (n + 1)) K := ∑ i, C (a i) * X i with hℓdef
  have hℓ : ℓ.IsHomogeneous 1 := isHomogeneous_linearForm a

  let bJ := Module.finBasis K ↥(Jk J (m' + 1))
  set g := Module.finrank K ↥(Jk J (m' + 1)) with hgdef
  let F : Fin g → MvPolynomial (Fin (n + 1)) K := fun i => (bJ i : MvPolynomial (Fin (n + 1)) K)
  have hF : ∀ i, (F i).IsHomogeneous (m' + 1) := fun i => (bJ i).2.2
  have hFJ : Ideal.span (Set.range F) = J := span_range_eq J hJ bJ

  have hp0 := finrank_piece_secF m' F hF ℓ hℓ 0
  have hp1 := finrank_piece_secF m' F hF ℓ hℓ 1
  simp only [Nat.add_zero] at hp0
  rw [hFJ] at hp0
  rw [hFJ] at hp1
  have hLP := lp_of_maximal_growth n m' K _ (g + NU K n m') (secF m' F ℓ) (secF_hom m' F hF ℓ hℓ) (le_of_eq hp0)
    (by rw [hp0, hp1]; exact hgrow)

  have hrel := rel_mod_of_lp m' F hF ℓ hℓ hLP
  have hcolF : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous (m' + 1) →
      ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F) := by
    rw [hFJ]; exact hcolm
  have hf' : ℓ * f ∈ Ideal.span (Set.range F) := by rw [hFJ]; exact hℓf
  have := MvPolynomial.mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span n (m' + 1) g K F hF ℓ hℓ
    hcolF hrel k hk f hf hf'
  rwa [hFJ] at this

end GotzRegW2
p2m_reactivate "P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2"

open MvPolynomial AlgebraicGeometry.HilbertFunctor in
theorem solution
    (n m : ℕ) (K : Type) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      ∀ k : ℕ, m ≤ k → ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous k →
        (∑ i, C (a i) * X i) * f ∈ J → f ∈ J :=
  GotzRegW2.main n m K J hJ hmax

end S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
end P2MW
export P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow (solution)

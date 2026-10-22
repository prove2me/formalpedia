-- Prove2me | solution 1 for HScattered.Bound.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:19:59.316038+00:00
-- url     : https://prove2.me/submissions/349bb5b0-e2b5-45e4-97cf-68cb272cf4c6

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered
import Definitions.Def_HScattered_Construction_DefinesSubgeometry

set_option autoImplicit false

namespace HScatteredE00

open Module

/-- Lemma A: every `K`-subspace of dimension at most `h` meets `U` in `F`-dimension at most its
`K`-dimension. -/
theorem lemA {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [FiniteDimensional K V] [FiniteDimensional F V]
    (h : ℕ) (U : Submodule F V) (hhr : h < finrank K V)
    (hspan : Submodule.span K (U : Set V) = ⊤)
    (hsc : ∀ S : Submodule K V, finrank K S = h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ h) :
    ∀ j : ℕ, ∀ S : Submodule K V, finrank K S + j = h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ finrank K S := by
  intro j
  induction j with
  | zero =>
    intro S hS
    simp only [add_zero] at hS
    rw [hS]; exact hsc S hS
  | succ j ih =>
    intro S hS
    have hnot : ¬ (U : Set V) ⊆ S := by
      intro hsub
      have h1 : Submodule.span K (U : Set V) ≤ S := Submodule.span_le.mpr hsub
      rw [hspan] at h1
      have h2 : S = ⊤ := top_le_iff.mp h1
      rw [h2, finrank_top] at hS
      omega
    obtain ⟨u, huU, huS⟩ := Set.not_subset.mp hnot
    have hS' : finrank K ↥(S ⊔ Submodule.span K {u}) = finrank K S + 1 :=
      Submodule.finrank_sup_span_singleton huS
    have hih := ih (S ⊔ Submodule.span K {u}) (by omega)
    have hlt : S.restrictScalars F ⊓ U < (S ⊔ Submodule.span K {u}).restrictScalars F ⊓ U := by
      rw [SetLike.lt_iff_le_and_exists]
      refine ⟨?_, u, ?_, ?_⟩
      · intro x hx
        rw [Submodule.mem_inf] at hx ⊢
        exact ⟨Submodule.mem_sup_left hx.1, hx.2⟩
      · rw [Submodule.mem_inf]
        exact ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self u), huU⟩
      · intro hx
        rw [Submodule.mem_inf] at hx
        exact huS hx.1
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

/-- Lemma B: an `F`-independent family in `U` with at most `h + 1` members is `K`-independent. -/
theorem lemB {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [FiniteDimensional K V] [FiniteDimensional F V]
    (h : ℕ) (U : Submodule F V) (hhr : h < finrank K V)
    (hspan : Submodule.span K (U : Set V) = ⊤)
    (hsc : ∀ S : Submodule K V, finrank K S = h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ h)
    {d : ℕ} (hd : d ≤ h + 1) (w : Fin d → V) (hwU : ∀ i, w i ∈ U)
    (hw : LinearIndependent F w) : LinearIndependent K w := by
  by_contra hK
  set S : Submodule K V := Submodule.span K (Set.range w) with hSdef
  have hle : finrank K S ≤ d := by
    have := finrank_range_le_card (R := K) w
    simp only [Fintype.card_fin] at this
    exact this
  have hne : finrank K S ≠ d := by
    intro heq
    apply hK
    rw [linearIndependent_iff_card_eq_finrank_span]
    simp only [Fintype.card_fin]
    exact heq.symm
  have hA := lemA h U hhr hspan hsc (h - finrank K S) S (by omega)
  have hFd : finrank F ↥(Submodule.span F (Set.range w)) = d := by
    have := finrank_span_eq_card hw
    simpa using this
  have hsub : Submodule.span F (Set.range w) ≤ S.restrictScalars F ⊓ U := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨?_, hwU i⟩
    show w i ∈ S
    exact Submodule.subset_span ⟨i, rfl⟩
  have := Submodule.finrank_mono hsub
  omega

/-- Injectivity of `u ↦ ∑ λᵢ uᵢ` on `U^m` for `F`-independent `λ` and `m ≤ h + 1`. -/
theorem lemC {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [FiniteDimensional K V] [FiniteDimensional F V]
    (h : ℕ) (U : Submodule F V) (hhr : h < finrank K V)
    (hspan : Submodule.span K (U : Set V) = ⊤)
    (hsc : ∀ S : Submodule K V, finrank K S = h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ h)
    {m : ℕ} (hm : m ≤ h + 1) (lam : Fin m → K) (hlam : LinearIndependent F lam)
    (u : Fin m → V) (huU : ∀ i, u i ∈ U) (hsum : ∑ i, lam i • u i = 0) :
    ∀ i, u i = 0 := by
  set W : Submodule F V := Submodule.span F (Set.range u) with hWdef
  have hWU : W ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact huU i
  have huW : ∀ i, u i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let b := Module.finBasis F W
  have hdW : finrank F W ≤ m := by
    have := finrank_range_le_card (R := F) u
    simp only [Fintype.card_fin] at this
    exact this
  let w : Fin (finrank F W) → V := fun j => (b j : V)
  have hwF : LinearIndependent F w :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hwK : LinearIndependent K w :=
    lemB h U hhr hspan hsc (by omega) w (fun j => hWU (b j).2) hwF
  -- coordinates
  let a : Fin m → Fin (finrank F W) → F := fun i j => b.repr ⟨u i, huW i⟩ j
  have hu : ∀ i, u i = ∑ j, a i j • w j := by
    intro i
    have := b.sum_repr ⟨u i, huW i⟩
    have h2 := congrArg W.subtype this
    simp only [map_sum, map_smul, Submodule.subtype_apply] at h2
    exact h2.symm
  have hsum2 : ∑ j, (∑ i, a i j • lam i) • w j = 0 := by
    rw [← hsum]
    simp_rw [hu, Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_assoc, smul_comm]
  have hcoef : ∀ j, ∑ i, a i j • lam i = 0 :=
    Fintype.linearIndependent_iff.mp hwK _ hsum2
  have ha : ∀ i j, a i j = 0 := by
    intro i j
    exact Fintype.linearIndependent_iff.mp hlam (fun i => a i j) (hcoef j) i
  intro i
  rw [hu i]
  simp [ha]

end HScatteredE00

open HScatteredE00 in
open Module in
open HScattered.Bound in
theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U) :
    (Module.finrank F U = Module.finrank K V ∧ HScattered.Construction.DefinesSubgeometry F K U ∧
        IsHScattered F K (Module.finrank K V - 1) U) ∨
      (h + 1) * Module.finrank F U ≤ Module.finrank K V * Module.finrank F K := by
  obtain ⟨hh0, hhr, hspan, hsc⟩ := hU
  have : FiniteDimensional F K := Module.Finite.of_finite
  have : FiniteDimensional F V := Module.Finite.trans K V
  have hFV : finrank F V = finrank F K * finrank K V := (Module.finrank_mul_finrank F K V).symm
  -- an F-basis of U, viewed in V
  let bU := Module.finBasis F U
  let v : Fin (finrank F U) → V := fun i => (bU i : V)
  have hspanFv : Submodule.span F (Set.range v) = U := by
    have : Set.range v = U.subtype '' Set.range bU := by
      ext x; simp [v]
    rw [this, Submodule.span_image, bU.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanKv : Submodule.span K (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower F K (Set.range v), hspanFv, hspan]
  have hrk : finrank K V ≤ finrank F U := by
    have h0 := finrank_range_le_card (R := K) v
    simp only [Fintype.card_fin] at h0
    have h3 : finrank K ↥(Submodule.span K (Set.range v)) ≤ finrank F U := h0
    rw [hspanKv, finrank_top] at h3
    exact h3
  -- the key inequality m * k ≤ r * n
  have key : ∀ m : ℕ, m ≤ h + 1 → m ≤ finrank F K →
      m * finrank F U ≤ finrank K V * finrank F K := by
    intro m hm hmn
    let bK := Module.finBasis F K
    let lam : Fin m → K := fun i => bK (Fin.castLE hmn i)
    have hlam : LinearIndependent F lam :=
      bK.linearIndependent.comp _ (Fin.castLE_injective hmn)
    let ψ : (Fin m → U) →ₗ[F] V :=
      { toFun := fun x => ∑ i, lam i • (x i : V)
        map_add' := by
          intro x y
          simp [smul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c x
          simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_comm] }
    have hinj : Function.Injective ψ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have := lemC h U hhr hspan hsc hm lam hlam (fun i => (x i : V)) (fun i => (x i).2) hx
      funext i
      exact Subtype.ext (this i)
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi_fintype, hFV] at this
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm] using this
  by_cases hk : finrank F U = finrank K V
  · left
    refine ⟨hk, ?_, ?_⟩
    · refine ⟨Set.range v, ?_, hspanFv, ?_, hspanKv⟩
      · rintro _ ⟨i, rfl⟩; exact (bU i).2
      · have hli : LinearIndependent K v :=
          linearIndependent_of_top_le_span_of_card_eq_finrank hspanKv.ge
            (by simpa using hk)
        exact hli.linearIndepOn_id
    · refine ⟨by omega, by omega, hspan, ?_⟩
      intro S hS
      by_contra hgt
      push Not at hgt
      have heq : S.restrictScalars F ⊓ U = U :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      have hUS : (U : Set V) ⊆ S := by
        intro x hx
        have : x ∈ S.restrictScalars F ⊓ U := by rw [heq]; exact hx
        exact (Submodule.mem_inf.mp this).1
      have h1 : Submodule.span K (U : Set V) ≤ S := Submodule.span_le.mpr hUS
      rw [hspan] at h1
      have h2 : S = ⊤ := top_le_iff.mp h1
      rw [h2, finrank_top] at hS
      omega
  · right
    by_cases hn : h + 1 ≤ finrank F K
    · exact key (h + 1) le_rfl hn
    · exfalso
      have h1 := key (finrank F K) (by omega) le_rfl
      have hpos : 0 < finrank F K := Module.finrank_pos
      have : finrank F U ≤ finrank K V := by
        rw [Nat.mul_comm (finrank F K)] at h1
        exact Nat.le_of_mul_le_mul_right h1 hpos
      omega

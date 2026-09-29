-- Prove2me | solution 1 for NgoFL.resultant_weyl_invariant
-- status  : ACCEPTED   (disprove)
-- author  : @Lucas
-- created : 2026-09-14T17:40:53.933608+00:00
-- url     : https://prove2.me/submissions/8e2069b9-68a9-4851-bfc9-dd19e4e7f234

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

open NgoFL

/-!
# `NgoFL.resultant_weyl_invariant` is false as stated

Ngô's Lemme 1.10.2 is a statement about the (reduced) root system of a split reductive group.
`RootPairing.IsRootSystem` only asks that the roots span `M` and the coroots span `N`, so it
also admits the non-reduced rank-one system `BC₁ = {±α, ±2α}`.  There the closed subsystem
`Φ_H = {±2α}` has Weyl group `{±1}`, the complement `{±α}` has half-system `Λ = {α}`, and the
reflection `s_{2α} = -1` sends `α` to `-α`: the resultant `∏_{β ∈ Λ} dβ` changes sign.
-/

namespace BC1

universe u v w

/-- Index type of the four roots of `BC₁`. -/
abbrev Idx : Type u := ULift.{u} (Fin 4)

/-- The weight space `ℚ`, placed in an arbitrary universe. -/
abbrev Wt : Type v := ULift.{v} ℚ

/-- The coweight space `ℚ`, placed in an arbitrary universe. -/
abbrev Cwt : Type w := ULift.{w} ℚ

/-- The four roots of `BC₁ = {±α, ±2α}`, realised in `ℚ`. -/
def rt : Fin 4 → ℚ := ![1, -1, 2, -2]

/-- The four coroots: `α^∨ = 2`, `(2α)^∨ = 1`. -/
def crt : Fin 4 → ℚ := ![2, -2, 1, -1]

/-- The permutation `α ↦ -α` of the index set. -/
def sgf : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- Every reflection of `BC₁` acts as `-1`, hence induces the permutation `sgf`. -/
def sg : Equiv.Perm (Fin 4) := ⟨sgf, sgf, by decide, by decide⟩

/-- The same permutation on the universe-lifted index type. -/
def sg' : Equiv.Perm (Idx.{u}) := Equiv.ulift.trans (sg.trans Equiv.ulift.symm)

/-- The multiplication pairing between the lifted copies of `ℚ`. -/
def pair : Wt.{v} →ₗ[ℚ] Cwt.{w} →ₗ[ℚ] ℚ :=
  (LinearMap.mul ℚ ℚ).compl₁₂ (ULift.moduleEquiv : Wt.{v} ≃ₗ[ℚ] ℚ)
    (ULift.moduleEquiv : Cwt.{w} ≃ₗ[ℚ] ℚ)

instance : (LinearMap.mul ℚ ℚ).IsPerfPair := by
  refine LinearMap.IsPerfPair.of_injective ?_ ?_
  · intro a b h
    simpa using congrArg (fun f => f 1) h
  · intro a b h
    simpa using congrArg (fun f => f 1) h

instance : (pair.{v, w}).IsPerfPair := by
  unfold pair
  infer_instance

@[simp] lemma pair_apply (a : Wt.{v}) (b : Cwt.{w}) : pair a b = a.down * b.down := rfl

lemma rt_inj : Function.Injective rt := by decide

lemma crt_inj : Function.Injective crt := by decide

/-- The non-reduced rank-one root system `BC₁`. -/
def P : RootPairing Idx.{u} ℚ Wt.{v} Cwt.{w} where
  toLinearMap := pair
  root := ⟨fun i => ULift.up (rt i.down), fun i j h =>
    ULift.ext _ _ (rt_inj (congrArg ULift.down h))⟩
  coroot := ⟨fun i => ULift.up (crt i.down), fun i j h =>
    ULift.ext _ _ (crt_inj (congrArg ULift.down h))⟩
  root_coroot_two i := by
    obtain ⟨i⟩ := i
    fin_cases i <;>
      norm_num [rt, crt, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.tail_cons, Matrix.head_cons]
  reflectionPerm _ := sg'
  reflectionPerm_root i j := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    refine ULift.ext _ _ ?_
    fin_cases i <;> fin_cases j <;>
      norm_num [rt, crt, sg, sg', sgf, Matrix.cons_val_succ, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  reflectionPerm_coroot i j := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    refine ULift.ext _ _ ?_
    fin_cases i <;> fin_cases j <;>
      norm_num [rt, crt, sg, sg', sgf, Matrix.cons_val_succ, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

instance : (P.{u, v, w}).IsRootSystem where
  span_root_eq_top := by
    refine Submodule.eq_top_iff'.2 fun x => ?_
    have h1 : (ULift.up (1 : ℚ) : Wt.{v}) ∈ Submodule.span ℚ (Set.range (P.{u, v, w}).root) :=
      Submodule.subset_span ⟨ULift.up 0, ULift.ext _ _ (by norm_num [P, rt])⟩
    have hx : x = x.down • (ULift.up (1 : ℚ) : Wt.{v}) := ULift.ext _ _ (by simp)
    rw [hx]
    exact Submodule.smul_mem _ _ h1
  span_coroot_eq_top := by
    refine Submodule.eq_top_iff'.2 fun x => ?_
    have h1 : (ULift.up (2 : ℚ) : Cwt.{w}) ∈ Submodule.span ℚ (Set.range (P.{u, v, w}).coroot) :=
      Submodule.subset_span ⟨ULift.up 0, ULift.ext _ _ (by norm_num [P, crt])⟩
    have hx : x = (x.down / 2) • (ULift.up (2 : ℚ) : Cwt.{w}) := ULift.ext _ _ (by simp)
    rw [hx]
    exact Submodule.smul_mem _ _ h1

/-- The closed subsystem `Φ_H = {±2α}`. -/
def S : Finset Idx.{u} := {ULift.up 2, ULift.up 3}

/-- The half system `Λ = {α}` of `Φ - Φ_H = {±α}`. -/
def Lam : Finset Idx.{u} := {ULift.up 0}

lemma negIdx_eq (i : Idx.{u}) : negIdx (P.{u, v, w}) i = ULift.up (sgf i.down) := rfl

lemma reflectionPerm_eq (i j : Idx.{u}) :
    (P.{u, v, w}).reflectionPerm i j = ULift.up (sgf j.down) := rfl

lemma S_closed : IsClosedSubsystem (P.{u, v, w}) ((S.{u} : Finset Idx.{u}) : Set Idx.{u}) where
  neg_mem i hi := by
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi ⊢
    rcases hi with rfl | rfl
    · exact Or.inr (by rw [negIdx_eq]; rfl)
    · exact Or.inl (by rw [negIdx_eq]; rfl)
  reflectionPerm_mem i _ j hj := by
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hj ⊢
    rcases hj with rfl | rfl
    · exact Or.inr (by rw [reflectionPerm_eq]; rfl)
    · exact Or.inl (by rw [reflectionPerm_eq]; rfl)

lemma Lam_half : IsHalfSystem (P.{u, v, w}) (S.{u})ᶜ (Lam.{u}) where
  subset := by
    intro i hi
    simp only [Lam, Finset.mem_singleton] at hi
    subst hi
    simp [S, ULift.ext_iff]
  neg_mem i hi := by
    simp only [S, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, ULift.ext_iff] at hi ⊢
    rw [negIdx_eq]
    revert hi
    obtain ⟨i⟩ := i
    fin_cases i <;> simp <;> decide
  xor_mem i hi := by
    simp only [S, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, ULift.ext_iff] at hi
    rw [negIdx_eq]
    revert hi
    obtain ⟨i⟩ := i
    fin_cases i <;> simp [Lam, ULift.ext_iff] <;> decide

lemma root'_apply (i : Idx.{u}) (x : Cwt.{w}) :
    (P.{u, v, w}).root' i x = rt i.down * x.down := rfl

lemma coroot_down (i : Idx.{u}) : ((P.{u, v, w}).coroot i).down = crt i.down := rfl

lemma resultant_Lam (x : Cwt.{w}) : resultant (P.{u, v, w}) Lam.{u} x = x.down := by
  simp [resultant, Lam, root'_apply, rt]

lemma coreflection_two (x : Cwt.{w}) :
    (P.{u, v, w}).coreflection (ULift.up 2) x = ULift.up (-x.down) := by
  refine ULift.ext _ _ ?_
  have h1 : ((P.{u, v, w}).root' (ULift.up 2) x) = 2 * x.down := by
    rw [root'_apply]
    norm_num [rt, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  have h2 : ((P.{u, v, w}).coroot (ULift.up 2)).down = 1 := by
    rw [coroot_down]
    norm_num [crt, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  show x.down - ((P.{u, v, w}).root' (ULift.up 2) x) * ((P.{u, v, w}).coroot (ULift.up 2)).down = -x.down
  rw [h1, h2]
  ring

lemma coreflection_mem_weyl :
    (P.{u, v, w}).coreflection (ULift.up 2) ∈ weylSubgroup (P.{u, v, w}) ((S.{u} : Finset Idx.{u}) : Set Idx.{u}) :=
  Subgroup.subset_closure ⟨ULift.up 2, by simp [S], rfl⟩

end BC1

theorem solution : ¬ (∀ {ι M N : Type} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [Fintype ι] [DecidableEq ι] (P : RootPairing ι ℚ M N)
    [P.IsRootSystem] (s L : Finset ι), IsClosedSubsystem P (s : Set ι) →
    IsHalfSystem P sᶜ L → ∀ (w : N ≃ₗ[ℚ] N),
    w ∈ weylSubgroup P (s : Set ι) → ∀ (x : N),
    resultant P L (w x) = resultant P L x) := by
  intro h
  have key := h (BC1.P.{0, 0, 0}) BC1.S BC1.Lam BC1.S_closed BC1.Lam_half
    ((BC1.P.{0, 0, 0}).coreflection (ULift.up 2)) BC1.coreflection_mem_weyl (ULift.up 1)
  rw [BC1.coreflection_two, BC1.resultant_Lam, BC1.resultant_Lam] at key
  norm_num at key

-- Prove2me | solution 1 for GreenTao.cs_stage_factorization
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:43:37.539977+00:00
-- url     : https://prove2.me/submissions/db5468d0-e35f-48a6-9b6e-4e6be93d79fe

import Theorems.Thm_GreenTao_cs_coefficients
import Mathlib

open scoped BigOperators
open GreenTao

private lemma avg_const_stage {α : Type} [Fintype α] [Nonempty α] (c : ℝ) :
    avg (fun _ : α => c) = c := by simp [avg, Fintype.card_ne_zero]

private lemma avg_equiv_stage {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e _

private lemma avg_prod_stage {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    avg f = avg (fun a => avg fun b => f (a, b)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.mul_sum]
  ring

private lemma avg_comm_stage {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    avg (fun a => avg (f a)) = avg (fun b => avg fun a => f a b) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma avg_update_stage {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] (i : ι) (f : (ι → α) → ℝ) :
    avg (fun y : ι → α => avg fun z : α => f (Function.update y i z)) = avg f := by
  let e : ((ι → α) × α) ≃ ((ι → α) × α) :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := by
        rintro ⟨y, z⟩
        apply Prod.ext
        · funext a
          by_cases ha : a = i
          · subst a; simp
          · simp [Function.update, ha]
        · simp
      right_inv := by
        rintro ⟨y, z⟩
        apply Prod.ext
        · funext a
          by_cases ha : a = i
          · subst a; simp
          · simp [Function.update, ha]
        · simp }
  calc
    _ = avg (fun p : (ι → α) × α => f (e p).1) := (avg_prod_stage _).symm
    _ = avg (fun p : (ι → α) × α => f p.1) := avg_equiv_stage e (fun p => f p.1)
    _ = _ := by rw [avg_prod_stage]; simp_rw [avg_const_stage]

private lemma partial_update_original {d : ℕ} {α : Type} (S : Finset (Fin d))
    (i : Fin d) (hi : i ∉ S) (y y' : Fin d → α) (ω : S → Bool) (z : α) :
    partialCubePoint S (Function.update y i z) y' ω =
      Function.update (partialCubePoint S y y' ω) i z := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [partialCubePoint, hi]
  · by_cases haS : a ∈ S
    · cases hω : ω ⟨a, haS⟩ <;> simp [partialCubePoint, haS, hω, Function.update, hai]
    · simp [partialCubePoint, haS, Function.update, hai]

private lemma partial_update_copy {d : ℕ} {α : Type} (S : Finset (Fin d))
    (i : Fin d) (hi : i ∉ S) (y y' : Fin d → α) (ω : S → Bool) (z : α) :
    partialCubePoint S y (Function.update y' i z) ω = partialCubePoint S y y' ω := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [partialCubePoint, hi]
  · by_cases haS : a ∈ S
    · cases hω : ω ⟨a, haS⟩ <;> simp [partialCubePoint, haS, hω, Function.update, hai]
    · simp [partialCubePoint, haS]

private lemma csForm_update_self (d : ℕ) (m : ℕ+) (j : Fin (d + 1)) (i : Fin d)
    (y : Fin d → ZMod (m : ℕ)) (z : ZMod (m : ℕ)) :
    csForm d j i (Function.update y i z) = csForm d j i y := by
  have hzero : csRatCoeff d j i i = 0 := (cs_coefficients d j).2.2.2 i i |>.2 rfl
  unfold csForm
  apply Finset.sum_congr rfl
  intro a _
  by_cases hai : a = i
  · subst a
    simp [hzero, ratCoeff]
  · simp [Function.update, hai]

private def cubeInsertEquiv {d : ℕ} (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S) :
    (↥(insert i S) → Bool) ≃ Bool × (S → Bool) where
  toFun ω := (ω ⟨i, Finset.mem_insert_self i S⟩,
    fun a => ω ⟨a.val, Finset.mem_insert_of_mem a.property⟩)
  invFun p a := if ha : a.val = i then p.1 else
    p.2 ⟨a.val, (Finset.mem_insert.mp a.property).resolve_left ha⟩
  left_inv := by
    intro ω
    funext a
    rcases a with ⟨a, haS⟩
    by_cases hai : a = i
    · subst a; simp
    · simp [hai]
  right_inv := by
    intro p
    apply Prod.ext
    · simp
    · funext a
      have hai : a.val ≠ i := by intro h; exact hi (h ▸ a.property)
      simp [hai]

private lemma partial_insert_point {d : ℕ} {α : Type} (S : Finset (Fin d))
    (i : Fin d) (hi : i ∉ S) (y y' : Fin d → α) (b : Bool) (ω : S → Bool) :
    partialCubePoint (insert i S) y y' ((cubeInsertEquiv S i hi).symm (b, ω)) =
      Function.update (partialCubePoint S y y' ω) i (if b then y' i else y i) := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [partialCubePoint, cubeInsertEquiv, hi]
  · by_cases haS : a ∈ S
    · simp [partialCubePoint, cubeInsertEquiv, haS, hai, Function.update]
    · simp [partialCubePoint, cubeInsertEquiv, haS, hai, Function.update]

private lemma cube_prod_insert {d : ℕ} {α : Type} (S : Finset (Fin d))
    (i : Fin d) (hi : i ∉ S) (y y' : Fin d → α) (f : (Fin d → α) → ℝ) :
    (∏ ω : ↥(insert i S) → Bool, f (partialCubePoint (insert i S) y y' ω)) =
      (∏ ω : S → Bool, f (partialCubePoint S y y' ω)) *
      ∏ ω : S → Bool, f (Function.update (partialCubePoint S y y' ω) i (y' i)) := by
  classical
  have hself (ω : S → Bool) :
      Function.update (partialCubePoint S y y' ω) i (y i) = partialCubePoint S y y' ω := by
    apply Function.update_eq_self_iff.mpr
    simp [partialCubePoint, hi]
  calc
    _ = ∏ p : Bool × (S → Bool),
        f (partialCubePoint (insert i S) y y' ((cubeInsertEquiv S i hi).symm p)) :=
      (Equiv.prod_comp (cubeInsertEquiv S i hi).symm
        (fun ω => f (partialCubePoint (insert i S) y y' ω))).symm
    _ = _ := by
      rw [Fintype.prod_prod_type, Fintype.prod_bool]
      simp_rw [partial_insert_point]
      simp only [Bool.false_eq_true, if_false, if_true, hself]
      rw [mul_comm]

private noncomputable def stageTerm {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (v : Fin d → ZMod (m : ℕ)) : ℝ :=
  F j (∑ a, v a) * ∏ a : Fin d,
    if a ∈ S then Real.sqrt (μ (csForm d j a v)) else F (j.succAbove a) (csForm d j a v)

private noncomputable def stageRest {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (i : Fin d) (v : Fin d → ZMod (m : ℕ)) : ℝ :=
  F j (∑ a, v a) * ∏ a ∈ (Finset.univ : Finset (Fin d)).erase i,
    if a ∈ S then Real.sqrt (μ (csForm d j a v)) else F (j.succAbove a) (csForm d j a v)

private lemma stageTerm_old {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S) (v : Fin d → ZMod (m : ℕ)) :
    stageTerm j μ F S v = F (j.succAbove i) (csForm d j i v) * stageRest j μ F S i v := by
  unfold stageTerm stageRest
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [if_neg hi]
  ring

private lemma stageTerm_new {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (i : Fin d) (v : Fin d → ZMod (m : ℕ)) :
    stageTerm j μ F (insert i S) v = Real.sqrt (μ (csForm d j i v)) * stageRest j μ F S i v := by
  unfold stageTerm stageRest
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Finset.mem_insert_self, if_true]
  have hprod :
      (∏ a ∈ (Finset.univ : Finset (Fin d)).erase i,
        if a ∈ insert i S then Real.sqrt (μ (csForm d j a v)) else F (j.succAbove a) (csForm d j a v)) =
      ∏ a ∈ (Finset.univ : Finset (Fin d)).erase i,
        if a ∈ S then Real.sqrt (μ (csForm d j a v)) else F (j.succAbove a) (csForm d j a v) := by
    apply Finset.prod_congr rfl
    intro a ha
    simp only [Finset.mem_insert, Finset.ne_of_mem_erase ha, false_or]
  rw [hprod]
  ring

private lemma avg_mul_stage {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

private abbrev StageOuter (d : ℕ) (m : ℕ+) := (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))

private lemma avg_update_first {d : ℕ} {m : ℕ+} (i : Fin d)
    (f : ((Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) → ℝ) :
    avg (fun p : StageOuter d m => avg fun z => f (Function.update p.1 i z, p.2)) = avg f := by
  calc
    _ = avg (fun y => avg fun z => avg fun y' => f (Function.update y i z, y')) := by
      rw [avg_prod_stage]
      congr 1
      funext y
      exact avg_comm_stage _
    _ = avg (fun y => avg fun y' => f (y, y')) :=
      avg_update_stage i (fun y : Fin d → ZMod (m : ℕ) => avg fun y' : Fin d → ZMod (m : ℕ) => f (y, y'))
    _ = _ := (avg_prod_stage f).symm

private lemma avg_update_second {d : ℕ} {m : ℕ+} (i : Fin d)
    (f : ((Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) → ℝ) :
    avg (fun p : StageOuter d m => avg fun z => f (p.1, Function.update p.2 i z)) = avg f := by
  rw [avg_prod_stage]
  have h (y : Fin d → ZMod (m : ℕ)) := avg_update_stage i (fun y' => f (y, y'))
  simp_rw [h]
  exact (avg_prod_stage f).symm

private lemma avg_update_both {d : ℕ} {m : ℕ+} (i : Fin d)
    (f : ((Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) → ℝ) :
    avg (fun p : StageOuter d m => avg fun z => avg fun z' => f (Function.update p.1 i z, Function.update p.2 i z')) = avg f := by
  calc
    _ = avg (fun p : StageOuter d m => avg fun z' => avg fun z => f (Function.update p.1 i z, Function.update p.2 i z')) := by
      congr 1
      funext p
      exact avg_comm_stage _
    _ = avg (fun p : StageOuter d m => avg fun z => f (Function.update p.1 i z, p.2)) :=
      avg_update_second i (fun p : StageOuter d m => avg fun z => f (Function.update p.1 i z, p.2))
    _ = _ := avg_update_first i f

private noncomputable def stageCube {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (y y' : Fin d → ZMod (m : ℕ)) : ℝ :=
  ∏ ω : S → Bool, stageTerm j μ F S (partialCubePoint S y y' ω)

private noncomputable def stepG {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ) (S : Finset (Fin d)) (i : Fin d)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) : ℝ :=
  ∏ ω : S → Bool, F (j.succAbove i) (csForm d j i (partialCubePoint S p.1 p.2 ω))

private noncomputable def stepW {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (S : Finset (Fin d)) (i : Fin d)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) : ℝ :=
  ∏ ω : S → Bool, μ (csForm d j i (partialCubePoint S p.1 p.2 ω))

private noncomputable def stepH {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (i : Fin d)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) (z : ZMod (m : ℕ)) : ℝ :=
  ∏ ω : S → Bool, stageRest j μ F S i (partialCubePoint S (Function.update p.1 i z) p.2 ω)

private lemma stepG_first {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ) (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) (z : ZMod (m : ℕ)) :
    stepG j F S i (Function.update p.1 i z, p.2) = stepG j F S i p := by
  unfold stepG
  simp_rw [partial_update_original S i hi, csForm_update_self]

private lemma stepW_first {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) (z : ZMod (m : ℕ)) :
    stepW j μ S i (Function.update p.1 i z, p.2) = stepW j μ S i p := by
  unfold stepW
  simp_rw [partial_update_original S i hi, csForm_update_self]

private lemma stepW_second {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) (z : ZMod (m : ℕ)) :
    stepW j μ S i (p.1, Function.update p.2 i z) = stepW j μ S i p := by
  unfold stepW
  simp_rw [partial_update_copy S i hi]

private lemma stepH_first {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (i : Fin d)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) (z z' : ZMod (m : ℕ)) :
    stepH j μ F S i (Function.update p.1 i z, p.2) z' = stepH j μ F S i p z' := by
  simp only [stepH, Function.update_idem]

private lemma stepH_second {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) (z z' : ZMod (m : ℕ)) :
    stepH j μ F S i (p.1, Function.update p.2 i z) z' = stepH j μ F S i p z' := by
  unfold stepH
  simp_rw [partial_update_copy S i hi]

private lemma stageCube_old {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) :
    stageCube j μ F S p.1 p.2 = stepG j F S i p * stepH j μ F S i p (p.1 i) := by
  unfold stageCube stepG stepH
  simp only [Function.update_eq_self]
  simp_rw [stageTerm_old j μ F S i hi, Finset.prod_mul_distrib]

private lemma stageCube_new {d : ℕ} {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (hμ : ∀ x, 0 ≤ μ x) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (p : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) :
    stageCube j μ F (insert i S) p.1 p.2 =
      stepW j μ S i p * stepH j μ F S i p (p.1 i) * stepH j μ F S i p (p.2 i) := by
  classical
  let R : ℝ := ∏ ω : S → Bool, Real.sqrt (μ (csForm d j i (partialCubePoint S p.1 p.2 ω)))
  have hR : R ^ 2 = stepW j μ S i p := by
    dsimp [R, stepW]
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro ω _
    exact Real.sq_sqrt (hμ _)
  have hH₀ : (∏ ω : S → Bool, stageRest j μ F S i (partialCubePoint S p.1 p.2 ω)) =
      stepH j μ F S i p (p.1 i) := by simp only [stepH, Function.update_eq_self]
  have hH₁ : (∏ ω : S → Bool,
      stageRest j μ F S i (Function.update (partialCubePoint S p.1 p.2 ω) i (p.2 i))) =
      stepH j μ F S i p (p.2 i) := by simp_rw [stepH, partial_update_original S i hi]
  unfold stageCube
  rw [cube_prod_insert S i hi p.1 p.2 (stageTerm j μ F (insert i S))]
  simp_rw [stageTerm_new j μ F S i, csForm_update_self, Finset.prod_mul_distrib]
  rw [hH₀, hH₁]
  change (R * _) * (R * _) = _
  rw [← hR]
  ring

theorem solution
    (d : ℕ) (m : ℕ+) (μ : ZMod (m : ℕ) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (j : Fin (d + 1)) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (hF : ∀ i x, |F i x| ≤ μ x) (l : Fin d) :
    ∃ G w : ((Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) → ℝ,
    ∃ H : ((Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) → ZMod (m : ℕ) → ℝ,
      (∀ a, 0 ≤ w a ∧ |G a| ≤ w a) ∧
      GreenTao.csStage d j μ F l.val = GreenTao.avg (fun a => G a * GreenTao.avg (H a)) ∧
      GreenTao.csStepFactor d j μ l = GreenTao.avg w ∧
      GreenTao.csStage d j μ F (l.val + 1) =
        GreenTao.avg (fun a => GreenTao.avg fun b => GreenTao.avg fun c => w a * H a b * H a c) := by
  classical
  let S := csTail d l.val
  let i : Fin d := l.rev
  have hi : i ∉ S := by
    have hl := l.isLt
    dsimp [S, i, csTail, Fin.rev]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have htail : csTail d (l.val + 1) = insert i S := by
    ext a
    have hl := l.isLt
    dsimp [csTail, S, i, Fin.rev]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  refine ⟨stepG j F S i, stepW j μ S i, stepH j μ F S i, ?_, ?_, ?_, ?_⟩
  · intro p
    constructor
    · exact Finset.prod_nonneg fun ω _ => hμ _
    · simp only [stepG, stepW, Finset.abs_prod]
      exact Finset.prod_le_prod (fun ω _ => abs_nonneg _) (fun ω _ => hF _ _)
  · calc
      csStage d j μ F l.val = avg (fun p : StageOuter d m => stageCube j μ F S p.1 p.2) :=
        (avg_prod_stage (fun p : StageOuter d m => stageCube j μ F S p.1 p.2)).symm
      _ = avg (fun p : StageOuter d m => avg fun z => stageCube j μ F S (Function.update p.1 i z) p.2) :=
        (avg_update_first i (fun p : StageOuter d m => stageCube j μ F S p.1 p.2)).symm
      _ = _ := by
        congr 1
        funext p
        have hp (z : ZMod (m : ℕ)) :
            stageCube j μ F S (Function.update p.1 i z) p.2 =
              stepG j F S i p * stepH j μ F S i p z := by
          rw [stageCube_old j μ F S i hi (Function.update p.1 i z, p.2)]
          simp only [Function.update_self]
          rw [stepG_first j F S i hi p z, stepH_first j μ F S i p z z]
        simp_rw [hp, avg_mul_stage]
  · exact (avg_prod_stage (stepW j μ S i)).symm
  · calc
      csStage d j μ F (l.val + 1) = avg (fun p : StageOuter d m => stageCube j μ F (insert i S) p.1 p.2) := by
        unfold csStage
        rw [htail]
        exact (avg_prod_stage (fun p : StageOuter d m => stageCube j μ F (insert i S) p.1 p.2)).symm
      _ = avg (fun p : StageOuter d m => avg fun z => avg fun z' =>
          stageCube j μ F (insert i S) (Function.update p.1 i z) (Function.update p.2 i z')) :=
        (avg_update_both i (fun p : StageOuter d m => stageCube j μ F (insert i S) p.1 p.2)).symm
      _ = _ := by
        congr 1
        funext p
        congr 1
        funext z
        congr 1
        funext z'
        rw [stageCube_new j μ hμ F S i hi (Function.update p.1 i z, Function.update p.2 i z')]
        simp only [Function.update_self]
        rw [stepW_first j μ S i hi (p.1, Function.update p.2 i z') z,
          stepW_second j μ S i hi p z',
          stepH_first j μ F S i (p.1, Function.update p.2 i z') z z,
          stepH_second j μ F S i hi p z' z,
          stepH_first j μ F S i (p.1, Function.update p.2 i z') z z',
          stepH_second j μ F S i hi p z' z']

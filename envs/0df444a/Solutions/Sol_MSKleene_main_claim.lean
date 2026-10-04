-- Prove2me | solution 1 for MSKleene.main_claim
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T09:17:58.522985+00:00
-- url     : https://prove2.me/submissions/2a64bd6f-60d0-4433-8177-f551ee6bb8d2

import Definitions.Def_MSKleene_AuxLang
import Theorems.Thm_MSKleene_singleton_term_regular
import Theorems.Thm_MSKleene_subterm_wf
import Theorems.Thm_MSKleene_collapse_lemma
import Theorems.Thm_MSKleene_subst_family
import Theorems.Thm_MSKleene_subst_comp
import Theorems.Thm_MSKleene_iter_absorb
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Set.Finite.Basic

namespace MSKleene

open scoped BigOperators

/-! Small, independently checkable pieces of the state-elimination proof used
by `main_claim`.  Keeping them here makes the final proof readable and avoids
changing any accepted milestone solution. -/

section Expressions

variable {S : Type} {sig : Signature S} {Z : SSet S}

/-- The empty regular expression at a fixed sort. -/
def RegExpr.empty (s : S) : RegExpr sig Z s :=
  .app (.empty s) .nil

/-- Binary union of regular expressions. -/
def RegExpr.plus {s : S} (R Q : RegExpr sig Z s) : RegExpr sig Z s :=
  .app (.plus s) (.cons R (.cons Q .nil))

/-- Iteration at a distinguished variable. -/
def RegExpr.iter {s : S} (z : Z s) (R : RegExpr sig Z s) : RegExpr sig Z s :=
  .app (.iter s z) (.cons R .nil)

/-- Language substitution at a distinguished variable. -/
def RegExpr.subst {t s : S} (z : Z t) (L : RegExpr sig Z t)
    (K : RegExpr sig Z s) : RegExpr sig Z s :=
  .app (.subst t s z) (.cons L (.cons K .nil))

/-- A finite union, with the empty expression as the empty sum. -/
def RegExpr.sum {s : S} : List (RegExpr sig Z s) → RegExpr sig Z s
  | [] => .empty s
  | R :: Rs => R.plus (RegExpr.sum Rs)

@[simp] theorem interp_empty (s : S) :
    interpExpr sig Z s (RegExpr.empty s) = ∅ := rfl

@[simp] theorem interp_plus {s : S} (R Q : RegExpr sig Z s) :
    interpExpr sig Z s (R.plus Q) =
      interpExpr sig Z s R ∪ interpExpr sig Z s Q := rfl

@[simp] theorem interp_iter {s : S} (z : Z s) (R : RegExpr sig Z s) :
    interpExpr sig Z s (R.iter z) = iterate z (interpExpr sig Z s R) := rfl

@[simp] theorem interp_subst {t s : S} (z : Z t) (L : RegExpr sig Z t)
    (K : RegExpr sig Z s) :
    interpExpr sig Z s (RegExpr.subst z L K) =
      substP z (interpExpr sig Z t L) s (interpExpr sig Z s K) := rfl

theorem interp_sum {s : S} (Rs : List (RegExpr sig Z s)) :
    interpExpr sig Z s (RegExpr.sum Rs) =
      {P | ∃ R ∈ Rs, P ∈ interpExpr sig Z s R} := by
  induction Rs with
  | nil => simp [RegExpr.sum]
  | cons R Rs ih =>
      simp only [RegExpr.sum, interp_plus, ih]
      ext P
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons]
      constructor
      · rintro (hP | hP)
        · exact ⟨R, Or.inl rfl, hP⟩
        · rcases hP with ⟨Q, hQ, hPQ⟩
          exact ⟨Q, Or.inr hQ, hPQ⟩
      · rintro ⟨Q, hQ, hPQ⟩
        rcases hQ with rfl | hQ
        · exact Or.inl hPQ
        · exact Or.inr ⟨Q, hQ, hPQ⟩

/-- Every finite language is denoted by a finite union of singleton regular
expressions. -/
theorem finite_language_expr [Finite S] (hsig : SigFinite sig) (hZ : SFinite Z)
    {s : S} (L : Set (Term sig Z s)) (hL : L.Finite) :
    ∃ R : RegExpr sig Z s, interpExpr sig Z s R = L := by
  classical
  let ps : List (Term sig Z s) := hL.toFinset.toList
  refine ⟨RegExpr.sum (ps.map Term.toReg), ?_⟩
  rw [interp_sum]
  ext P
  constructor
  · rintro ⟨R, hR, hPR⟩
    rw [List.mem_map] at hR
    rcases hR with ⟨Q, hQ, rfl⟩
    have hsingle :=
      (singleton_term_regular sig Z hsig hZ Q).1
    rw [hsingle] at hPR
    have hPQ : P = Q := Set.mem_singleton_iff.mp hPR
    subst P
    exact hL.mem_toFinset.mp (by simpa [ps] using hQ)
  · intro hP
    refine ⟨Term.toReg P, ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨P, by simpa [ps] using hL.mem_toFinset.mpr hP, rfl⟩
    · rw [(singleton_term_regular sig Z hsig hZ P).1]
      exact Set.mem_singleton P

end Expressions

section Budget

variable {S : Type}

/-- Sum of all sortwise bounds.  The theorem assumes only `[Finite S]`, so a
fintype is chosen locally and noncomputably. -/
noncomputable def budgetSize [Finite S] (K : S → ℕ) : ℕ := by
  letI := Fintype.ofFinite S
  exact ∑ s, K s

/-- Remove the greatest admissible state at one sort. -/
noncomputable def budgetPred [Finite S] (K : S → ℕ) (t : S) : S → ℕ := by
  classical
  exact Function.update K t (K t - 1)

@[simp] theorem budgetPred_apply_self [Finite S] (K : S → ℕ) (t : S) :
    budgetPred K t t = K t - 1 := by
  classical
  simp [budgetPred]

theorem budgetPred_apply_of_ne [Finite S] (K : S → ℕ) {t s : S}
    (h : s ≠ t) : budgetPred K t s = K s := by
  classical
  simp [budgetPred, h]

theorem budgetPred_le [Finite S] (K : S → ℕ) (t s : S) :
    budgetPred K t s ≤ K s := by
  classical
  by_cases h : s = t
  · subst s
    rw [budgetPred_apply_self]
    omega
  · rw [budgetPred_apply_of_ne K h]

theorem budgetPred_lt_at [Finite S] (K : S → ℕ) (t : S) (ht : 0 < K t) :
    budgetPred K t t < K t := by
  classical
  rw [budgetPred_apply_self]
  omega

theorem budgetPred_size [Finite S] (K : S → ℕ) (t : S) (ht : 0 < K t) :
    budgetSize (budgetPred K t) = budgetSize K - 1 := by
  classical
  letI := Fintype.ofFinite S
  unfold budgetSize budgetPred
  calc
    (∑ s, Function.update K t (K t - 1) s) =
        (∑ s ∈ Finset.univ.erase t, K s) + (K t - 1) := by
          rw [← Finset.sum_erase_add Finset.univ
            (Function.update K t (K t - 1)) (Finset.mem_univ t)]
          congr 1
          · apply Finset.sum_congr rfl
            intro s hs
            have hne : s ≠ t := (Finset.mem_erase.mp hs).1
            simp [Function.update, hne]
          · simp
    _ = ((∑ s ∈ Finset.univ.erase t, K s) + K t) - 1 := by omega
    _ = (∑ s, K s) - 1 := by
          rw [Finset.sum_erase_add Finset.univ K (Finset.mem_univ t)]

theorem budget_eq_zero_of_size_zero [Finite S] (K : S → ℕ)
    (hK : budgetSize K = 0) : K = fun _ => 0 := by
  classical
  letI := Fintype.ofFinite S
  unfold budgetSize at hK
  have hz : ∀ s, K s = 0 := by
    intro s
    exact (Finset.sum_eq_zero_iff.mp hK) s (Finset.mem_univ s)
  exact funext hz

theorem exists_positive_of_budgetSize_pos [Finite S] (K : S → ℕ)
    (hK : 0 < budgetSize K) : ∃ t, 0 < K t := by
  classical
  letI := Fintype.ofFinite S
  by_contra h
  push_neg at h
  have hz : ∀ t, K t = 0 := fun t => Nat.eq_zero_of_le_zero (h t)
  simp [budgetSize, hz] at hK

end Budget

section ShallowTerms

variable {S : Type} {sig : Signature S} {Z : SSet S}

theorem TermVec.varsAllIn_of_mem {pred : (s : S) → Z s → Prop} :
    ∀ {w : List S} {s : S} {P : Term sig Z s} {Ps : TermVec sig Z w},
      TermVec.Mem P Ps → TermVec.varsAllIn pred Ps → Term.varsIn pred P := by
  intro w s P Ps hmem
  induction hmem with
  | head => exact fun h => h.1
  | tail _ _ ih => exact fun h => ih h.2

theorem Term.varsIn_of_immSub {pred : (s : S) → Z s → Prop}
    {P Q : STerm sig Z} (hQP : ImmSub Q P)
    (hP : Term.varsIn pred P.2) : Term.varsIn pred Q.2 := by
  rcases hQP with ⟨w, σ, Ps, hEq, hmem⟩
  rw [hEq] at hP
  exact TermVec.varsAllIn_of_mem hmem hP

theorem Term.varsIn_of_subtermLT {pred : (s : S) → Z s → Prop}
    {P Q : STerm sig Z} (hQP : SubtermLT Q P)
    (hP : Term.varsIn pred P.2) : Term.varsIn pred Q.2 := by
  induction hQP using Relation.TransGen.trans_induction_on with
  | single h => exact Term.varsIn_of_immSub h hP
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ hP)

/-- Codes for minimal terms: either a variable or a nullary symbol. -/
def MinTermCode (sig : Signature S) (Z : SSet S) (s : S) := Z s ⊕ sig [] s

def MinTermCode.decode {s : S} : MinTermCode sig Z s → Term sig Z s
  | .inl z => .var z
  | .inr σ => .app σ .nil

theorem exists_minTermCode {s : S} (P : Term sig Z s)
    (hP : Min (⟨s, P⟩ : STerm sig Z)) :
    ∃ c : MinTermCode sig Z s, c.decode = P := by
  rcases ((subterm_wf sig Z).2 ⟨s, P⟩).mp hP with
      ⟨z, hz⟩ | ⟨σ, hσ⟩
  · exact ⟨.inl z, hz.symm⟩
  · exact ⟨.inr σ, hσ.symm⟩

theorem exists_minTermCodes :
    ∀ {w : List S} (Ps : TermVec sig Z w),
      (∀ {s : S} (P : Term sig Z s), TermVec.Mem P Ps →
        Min (⟨s, P⟩ : STerm sig Z)) →
      ∃ cs : Args (MinTermCode sig Z) w,
        TermVec.ofArgs (Args.map (fun _ c => c.decode) cs) = Ps
  | [], .nil, _ => ⟨PUnit.unit, rfl⟩
  | _ :: _, .cons P Ps, h => by
      rcases exists_minTermCode P (h P (.head P Ps)) with ⟨c, hc⟩
      have htail : ∀ {s : S} (Q : Term sig Z s), TermVec.Mem Q Ps →
          Min (⟨s, Q⟩ : STerm sig Z) := by
        intro s Q hQ
        exact h Q (.tail P hQ)
      rcases exists_minTermCodes Ps htail with ⟨cs, hcs⟩
      refine ⟨(c, cs), ?_⟩
      simp only [Args.map, TermVec.ofArgs]
      rw [hc, hcs]

/-- A finite code space covering all terms with no proper non-minimal
subterms. -/
def ShallowCode (sig : Signature S) (Z : SSet S) (u : S) :=
  Z u ⊕ (Σ op : (Σ w : List S, sig w u), Args (MinTermCode sig Z) op.1)

def ShallowCode.decode {u : S} : ShallowCode sig Z u → Term sig Z u
  | .inl z => .var z
  | .inr ⟨⟨_, σ⟩, cs⟩ =>
      .app σ (TermVec.ofArgs (Args.map (fun _ c => c.decode) cs))

theorem exists_shallowCode {u : S} (P : Term sig Z u)
    (hP : ∀ Q : STerm sig Z, SubtermLT Q ⟨u, P⟩ → Min Q) :
    ∃ c : ShallowCode sig Z u, c.decode = P := by
  cases P with
  | var z => exact ⟨.inl z, rfl⟩
  | @app w _ σ Ps =>
      have hargs : ∀ {s : S} (Q : Term sig Z s), TermVec.Mem Q Ps →
          Min (⟨s, Q⟩ : STerm sig Z) := by
        intro s Q hQ
        apply hP ⟨s, Q⟩
        exact Relation.TransGen.single ⟨w, σ, Ps, rfl, hQ⟩
      rcases exists_minTermCodes Ps hargs with ⟨cs, hcs⟩
      refine ⟨.inr ⟨⟨w, σ⟩, cs⟩, ?_⟩
      simp only [ShallowCode.decode]
      rw [hcs]

private theorem finite_fiber_of_sfinite {A : SSet S} (hA : SFinite A) (s : S) :
    Finite (A s) := by
  letI : Finite (Σ t, A t) := hA
  apply Finite.of_injective (fun a : A s => Sigma.mk s a)
  intro a b hab
  exact eq_of_heq (Sigma.mk.inj hab).2

private theorem finite_ops_at (hsig : SigFinite sig) (u : S) :
    Finite (Σ w : List S, sig w u) := by
  letI : Finite ((w : List S) × (s : S) × sig w s) := hsig
  apply Finite.of_injective
    (fun op : (Σ w : List S, sig w u) =>
      (⟨op.1, ⟨u, op.2⟩⟩ : (w : List S) × (s : S) × sig w s))
  intro a b hab
  cases a with
  | mk wa a =>
      cases b with
      | mk wb b =>
          cases hab
          rfl

private theorem finite_min_args (hZ : SFinite Z) (hsig : SigFinite sig) :
    ∀ w : List S, Finite (Args (MinTermCode sig Z) w)
  | [] => by
      change Finite PUnit
      infer_instance
  | s :: w => by
      letI : Finite (Z s) := finite_fiber_of_sfinite hZ s
      letI : Finite (sig [] s) := by
        letI : Finite ((w : List S) × (r : S) × sig w r) := hsig
        apply Finite.of_injective
          (fun σ : sig [] s =>
            (⟨[], ⟨s, σ⟩⟩ : (w : List S) × (r : S) × sig w r))
        intro a b hab
        cases hab
        rfl
      letI : Finite (MinTermCode sig Z s) := by
        unfold MinTermCode
        infer_instance
      letI : Finite (Args (MinTermCode sig Z) w) := finite_min_args hZ hsig w
      change Finite (MinTermCode sig Z s × Args (MinTermCode sig Z) w)
      infer_instance

theorem finite_shallowCode (hZ : SFinite Z) (hsig : SigFinite sig) (u : S) :
    Finite (ShallowCode sig Z u) := by
  letI : Finite (Z u) := finite_fiber_of_sfinite hZ u
  letI : Finite (Σ w : List S, sig w u) := finite_ops_at hsig u
  letI finiteArgs (op : (Σ w : List S, sig w u)) :
      Finite (Args (MinTermCode sig Z) op.1) := finite_min_args hZ hsig op.1
  unfold ShallowCode
  infer_instance

theorem finite_of_all_proper_subterms_min (hZ : SFinite Z) (hsig : SigFinite sig)
    (u : S) :
    {P : Term sig Z u | ∀ Q : STerm sig Z, SubtermLT Q ⟨u, P⟩ → Min Q}.Finite := by
  letI : Finite (ShallowCode sig Z u) := finite_shallowCode hZ hsig u
  have hrange : (Set.range (ShallowCode.decode : ShallowCode sig Z u →
      Term sig Z u)).Finite := by
    simpa only [Set.image_univ] using
      (Set.toFinite (Set.univ : Set (ShallowCode sig Z u))).image
        (ShallowCode.decode : ShallowCode sig Z u → Term sig Z u)
  apply Set.Finite.subset hrange
  intro P hP
  rcases exists_shallowCode P hP with ⟨c, rfl⟩
  exact Set.mem_range_self c

end ShallowTerms

section Monotonicity

variable {S : Type} {sig : Signature S} {X : SSet S}

theorem Term.varsIn_mono {C D : (s : S) → X s → Prop}
    (hCD : ∀ s x, C s x → D s x) :
    (∀ {s : S} (P : Term sig X s), Term.varsIn C P → Term.varsIn D P) ∧
    (∀ {w : List S} (Ps : TermVec sig X w),
      TermVec.varsAllIn C Ps → TermVec.varsAllIn D Ps) := by
  let termCase : ∀ {s : S} (x : X s), C s x → D s x :=
    fun {s} x hx => hCD s x hx
  let appCase : ∀ {w : List S} {s : S} (σ : sig w s)
      (Ps : TermVec sig X w),
      (TermVec.varsAllIn C Ps → TermVec.varsAllIn D Ps) →
      TermVec.varsAllIn C Ps → TermVec.varsAllIn D Ps :=
    fun _ _ ih h => ih h
  let nilCase : TermVec.varsAllIn C (TermVec.nil : TermVec sig X []) →
      TermVec.varsAllIn D (TermVec.nil : TermVec sig X []) := fun _ => trivial
  let consCase : ∀ {s : S} {w : List S} (P : Term sig X s)
      (Ps : TermVec sig X w),
      (Term.varsIn C P → Term.varsIn D P) →
      (TermVec.varsAllIn C Ps → TermVec.varsAllIn D Ps) →
      TermVec.varsAllIn C (.cons P Ps) →
      TermVec.varsAllIn D (.cons P Ps) :=
    fun _ _ ihP ihPs h => ⟨ihP h.1, ihPs h.2⟩
  exact ⟨@Term.rec _ _ _
      (motive_1 := fun _ P => Term.varsIn C P → Term.varsIn D P)
      (motive_2 := fun _ Ps => TermVec.varsAllIn C Ps → TermVec.varsAllIn D Ps)
      termCase appCase nilCase consCase,
    @TermVec.rec _ _ _
      (motive_1 := fun _ P => Term.varsIn C P → Term.varsIn D P)
      (motive_2 := fun _ Ps => TermVec.varsAllIn C Ps → TermVec.varsAllIn D Ps)
      termCase appCase nilCase consCase⟩

theorem auxLang_mono (ctx : KleeneCtx sig X) {u : S}
    {C D : (s : S) → Set (Fin (ctx.n s))} {K J : S → ℕ}
    (hCD : ∀ s, C s ⊆ D s) (hKJ : ∀ s, K s ≤ J s)
    (l : Fin (ctx.n u)) : ctx.auxLang u C K l ⊆ ctx.auxLang u D J l := by
  intro P hP
  rcases hP with ⟨hvars, hbound, hval⟩
  refine ⟨(Term.varsIn_mono (C := ctx.inXC C) (D := ctx.inXC D) ?_).1 P hvars,
    ?_, hval⟩
  · intro s z hz
    cases z with
    | inl x => trivial
    | inr m => exact hCD s hz
  · intro Q hQP hQ _
    exact lt_of_lt_of_le
      (hbound Q hQP hQ (Term.varsIn_of_subtermLT hQP hvars)) (hKJ Q.1)

theorem auxLang_budgetPred_subset [Finite S] (ctx : KleeneCtx sig X)
    {u : S} (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (t : S) (l : Fin (ctx.n u)) :
    ctx.auxLang u C (budgetPred K t) l ⊆ ctx.auxLang u C K l :=
  auxLang_mono ctx (fun _ => Set.Subset.rfl) (budgetPred_le K t) l

/-- Add one recognizing state to the leaf alphabet. -/
def addState (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s)))
    (t : S) (z : Fin (ctx.n t)) : (s : S) → Set (Fin (ctx.n s)) :=
  fun s => C s ∪ {m | ∃ h : s = t, h ▸ m = z}

theorem subset_addState (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s)))
    (t : S) (z : Fin (ctx.n t)) (s : S) : C s ⊆ addState ctx C t z s := by
  intro m hm
  exact (show m ∈ C s ∨ ∃ h : s = t, h ▸ m = z from Or.inl hm)

@[simp] theorem mem_addState_self (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s)))
    (t : S) (z : Fin (ctx.n t)) : z ∈ addState ctx C t z t := by
  exact (show z ∈ C t ∨ ∃ h : t = t, h ▸ z = z from Or.inr ⟨rfl, rfl⟩)

end Monotonicity

section RecursiveBounds

variable {S : Type} {sig : Signature S} {X : SSet S}

/-! The quantified subterm side condition in `auxLang` is equivalent to a
structural invariant: every non-minimal child root is within budget, and the
same condition recursively holds below that child. -/
mutual
def Term.boundedProper (ctx : KleeneCtx sig X) (K : S → ℕ) :
    {s : S} → Term sig ctx.Z s → Prop
  | _, .var _ => True
  | _, .app _ Ps => TermVec.boundedNodes ctx K Ps
def TermVec.boundedNodes (ctx : KleeneCtx sig X) (K : S → ℕ) :
    {w : List S} → TermVec sig ctx.Z w → Prop
  | _, .nil => True
  | s :: w, .cons P Ps =>
      (¬ Min (⟨s, P⟩ : STerm sig ctx.Z) → ctx.hVal ⟨s, P⟩ < K s) ∧
      Term.boundedProper ctx K P ∧ TermVec.boundedNodes ctx K Ps
end

private def termBoundRel (ctx : KleeneCtx sig X) (K : S → ℕ)
    {s : S} (P : Term sig ctx.Z s) : Prop :=
  ∀ Q : STerm sig ctx.Z, SubtermLT Q ⟨s, P⟩ → ¬ Min Q →
    ctx.hVal Q < K Q.1

private def vecBoundRel (ctx : KleeneCtx sig X) (K : S → ℕ)
    {w : List S} (Ps : TermVec sig ctx.Z w) : Prop :=
  ∀ (Q : STerm sig ctx.Z) {s : S} (P : Term sig ctx.Z s),
    TermVec.Mem P Ps → SubtermLE Q ⟨s, P⟩ → ¬ Min Q →
    ctx.hVal Q < K Q.1

theorem boundedProper_of_rel (ctx : KleeneCtx sig X) (K : S → ℕ) :
    (∀ {s : S} (P : Term sig ctx.Z s),
      termBoundRel ctx K P → Term.boundedProper ctx K P) ∧
    (∀ {w : List S} (Ps : TermVec sig ctx.Z w),
      vecBoundRel ctx K Ps → TermVec.boundedNodes ctx K Ps) := by
  let varCase : ∀ {s : S} (z : ctx.Z s),
      termBoundRel ctx K (Term.var z) →
        Term.boundedProper ctx K (Term.var z) := fun _ _ => trivial
  let appCase : ∀ {w : List S} {s : S} (σ : sig w s)
      (Ps : TermVec sig ctx.Z w),
      (vecBoundRel ctx K Ps → TermVec.boundedNodes ctx K Ps) →
      termBoundRel ctx K (Term.app σ Ps) →
        Term.boundedProper ctx K (Term.app σ Ps) := by
    intro w s σ Ps ih h
    apply ih
    intro Q r P hmem hQP hQ
    apply h Q
    exact Relation.TransGen.tail' hQP ⟨w, σ, Ps, rfl, hmem⟩
    exact hQ
  let nilCase : vecBoundRel ctx K (TermVec.nil : TermVec sig ctx.Z []) →
      TermVec.boundedNodes ctx K (TermVec.nil : TermVec sig ctx.Z []) :=
    fun _ => by simp [TermVec.boundedNodes]
  let consCase : ∀ {s : S} {w : List S} (P : Term sig ctx.Z s)
      (Ps : TermVec sig ctx.Z w),
      (termBoundRel ctx K P → Term.boundedProper ctx K P) →
      (vecBoundRel ctx K Ps → TermVec.boundedNodes ctx K Ps) →
      vecBoundRel ctx K (.cons P Ps) →
        TermVec.boundedNodes ctx K (.cons P Ps) := by
    intro s w P Ps ihP ihPs h
    refine ⟨?_, ihP ?_, ihPs ?_⟩
    · intro hP
      exact h ⟨s, P⟩ P (.head P Ps) .refl hP
    · intro Q hQP hQ
      exact h Q P (.head P Ps) hQP.to_reflTransGen hQ
    · intro Q r R hmem hQR hQ
      exact h Q R (.tail P hmem) hQR hQ
  exact ⟨@Term.rec _ _ _
      (motive_1 := fun _ P => termBoundRel ctx K P → Term.boundedProper ctx K P)
      (motive_2 := fun _ Ps => vecBoundRel ctx K Ps →
        TermVec.boundedNodes ctx K Ps)
      varCase appCase nilCase consCase,
    @TermVec.rec _ _ _
      (motive_1 := fun _ P => termBoundRel ctx K P → Term.boundedProper ctx K P)
      (motive_2 := fun _ Ps => vecBoundRel ctx K Ps →
        TermVec.boundedNodes ctx K Ps)
      varCase appCase nilCase consCase⟩

theorem rel_of_boundedProper (ctx : KleeneCtx sig X) (K : S → ℕ) :
    (∀ {s : S} (P : Term sig ctx.Z s),
      Term.boundedProper ctx K P → termBoundRel ctx K P) ∧
    (∀ {w : List S} (Ps : TermVec sig ctx.Z w),
      TermVec.boundedNodes ctx K Ps → vecBoundRel ctx K Ps) := by
  let varCase : ∀ {s : S} (z : ctx.Z s),
      Term.boundedProper ctx K (Term.var z) →
        termBoundRel ctx K (Term.var z) := by
    intro s z _ Q hQ
    cases hQ with
    | single h =>
        rcases h with ⟨w, σ, Ps, hEq, _⟩
        cases hEq
    | tail _ h =>
        rcases h with ⟨w, σ, Ps, hEq, _⟩
        cases hEq
  let appCase : ∀ {w : List S} {s : S} (σ : sig w s)
      (Ps : TermVec sig ctx.Z w),
      (TermVec.boundedNodes ctx K Ps → vecBoundRel ctx K Ps) →
      Term.boundedProper ctx K (Term.app σ Ps) →
        termBoundRel ctx K (Term.app σ Ps) := by
    intro w s σ Ps ih h Q hQP hQ
    have hsplit : ∃ (r : S) (P : Term sig ctx.Z r),
        TermVec.Mem P Ps ∧ SubtermLE Q ⟨r, P⟩ := by
      cases hQP with
      | single himm =>
          rcases himm with ⟨w', τ, Rs, hEq, hmem⟩
          cases hEq
          exact ⟨_, Q.2, hmem, .refl⟩
      | tail hpre himm =>
          rcases himm with ⟨w', τ, Rs, hEq, hmem⟩
          cases hEq
          exact ⟨_, _, hmem, hpre.to_reflTransGen⟩
    rcases hsplit with ⟨r, P, hmem, hQP⟩
    exact ih h Q P hmem hQP hQ
  let nilCase : TermVec.boundedNodes ctx K (TermVec.nil : TermVec sig ctx.Z []) →
      vecBoundRel ctx K (TermVec.nil : TermVec sig ctx.Z []) := by
    intro _ Q r P hmem
    cases hmem
  let consCase : ∀ {s : S} {w : List S} (P : Term sig ctx.Z s)
      (Ps : TermVec sig ctx.Z w),
      (Term.boundedProper ctx K P → termBoundRel ctx K P) →
      (TermVec.boundedNodes ctx K Ps → vecBoundRel ctx K Ps) →
      TermVec.boundedNodes ctx K (.cons P Ps) →
        vecBoundRel ctx K (.cons P Ps) := by
    intro s w P Ps ihP ihPs h Q r R hmem hQR hQ
    rcases h with ⟨hroot, hP, hPs⟩
    cases hmem with
    | head =>
        cases hQR with
        | refl => exact hroot hQ
        | tail hpre himm =>
            exact ihP hP Q (Relation.TransGen.tail' hpre himm) hQ
    | tail _ hmem => exact ihPs hPs Q R hmem hQR hQ
  exact ⟨@Term.rec _ _ _
      (motive_1 := fun _ P => Term.boundedProper ctx K P → termBoundRel ctx K P)
      (motive_2 := fun _ Ps => TermVec.boundedNodes ctx K Ps →
        vecBoundRel ctx K Ps)
      varCase appCase nilCase consCase,
    @TermVec.rec _ _ _
      (motive_1 := fun _ P => Term.boundedProper ctx K P → termBoundRel ctx K P)
      (motive_2 := fun _ Ps => TermVec.boundedNodes ctx K Ps →
        vecBoundRel ctx K Ps)
      varCase appCase nilCase consCase⟩

theorem boundedProper_iff (ctx : KleeneCtx sig X) (K : S → ℕ)
    {s : S} (P : Term sig ctx.Z s) :
    Term.boundedProper ctx K P ↔
      ∀ Q : STerm sig ctx.Z, SubtermLT Q ⟨s, P⟩ → ¬ Min Q →
        ctx.hVal Q < K Q.1 :=
  ⟨(rel_of_boundedProper ctx K).1 P,
    (boundedProper_of_rel ctx K).1 P⟩

theorem mem_auxLang_iff_structural (ctx : KleeneCtx sig X) {s : S}
    (C : (r : S) → Set (Fin (ctx.n r))) (K : S → ℕ)
    (l : Fin (ctx.n s)) (P : Term sig ctx.Z s) :
    P ∈ ctx.auxLang s C K l ↔
      Term.varsIn (ctx.inXC C) P ∧ Term.boundedProper ctx K P ∧
        ctx.hHom.toFun s P = l := by
  constructor
  · rintro ⟨hvars, hbound, hval⟩
    refine ⟨hvars, (boundedProper_iff ctx K P).2 ?_, hval⟩
    intro Q hQP hQ
    exact hbound Q hQP hQ (Term.varsIn_of_subtermLT hQP hvars)
  · rintro ⟨hvars, hbound, hval⟩
    refine ⟨hvars, ?_, hval⟩
    intro Q hQP hQ _
    exact (boundedProper_iff ctx K P).1 hbound Q hQP hQ

end RecursiveBounds

section SubstitutionStructure

open Classical

variable {S : Type} {sig : Signature S} {X : SSet S}

private theorem main_ofArgs_toArgs :
    ∀ {w : List S} (Ps : TermVec sig X w), TermVec.ofArgs (TermVec.toArgs Ps) = Ps
  | [], .nil => rfl
  | _ :: _, .cons P Ps => congrArg (TermVec.cons P) (main_ofArgs_toArgs Ps)

private theorem main_toArgs_ofArgs :
    ∀ {w : List S} (xs : Args (Term sig X) w),
      TermVec.toArgs (TermVec.ofArgs xs) = xs
  | [], _ => rfl
  | _ :: _, (P, xs) => congrArg (Prod.mk P) (main_toArgs_ofArgs xs)

private theorem main_min_var {s : S} (z : X s) :
    Min (⟨s, Term.var z⟩ : STerm sig X) := by
  intro Q hQ
  rcases hQ with ⟨w, σ, Ps, hEq, _⟩
  cases hEq

private theorem main_min_nil {s : S} (σ : sig [] s) :
    Min (⟨s, Term.app σ .nil⟩ : STerm sig X) := by
  intro Q hQ
  rcases hQ with ⟨w, τ, Ps, hEq, hmem⟩
  cases hEq
  cases hmem

private theorem main_nonmin_cons {s r : S} {w : List S} (σ : sig (r :: w) s)
    (P : Term sig X r) (Ps : TermVec sig X w) :
    ¬ Min (⟨s, Term.app σ (.cons P Ps)⟩ : STerm sig X) := by
  intro h
  exact h ⟨r, P⟩ ⟨r :: w, σ, .cons P Ps, rfl, .head P Ps⟩

theorem substP_mono {t s : S} (z : X t)
    {L L' : Set (Term sig X t)} {K K' : Set (Term sig X s)}
    (hL : L ⊆ L') (hK : K ⊆ K') : substP z L s K ⊆ substP z L' s K' := by
  intro R hR
  unfold substP at hR ⊢
  rcases Set.mem_iUnion.mp hR with ⟨P, hR⟩
  rcases Set.mem_iUnion.mp hR with ⟨hP, hRP⟩
  refine Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hK hP, ?_⟩⟩
  rcases ((subst_family sig X z L P).1 ▸ hRP) with ⟨qs, hqs, rfl⟩
  rw [(subst_family sig X z L' P).1]
  exact ⟨qs, fun a => hL (hqs a), rfl⟩

/-- Non-target variables cannot disappear under substitution. -/
theorem substHom_varsIn_inverse {t : S} (z : X t)
    (L : Set (Term sig X t)) (C D : (s : S) → X s → Prop)
    (hz : D t z)
    (hother : ∀ {s : S} (x : X s), C s x →
      (∀ h : s = t, h ▸ x ≠ z) → D s x) :
    (∀ {s : S} (P R : Term sig X s),
      R ∈ (show Set (Term sig X s) from (substHom z L).toFun s P) →
      Term.varsIn C R → Term.varsIn D P) ∧
    (∀ {w : List S} (Ps : TermVec sig X w)
        (xs : Args (Term sig X) w),
      Args.pmem xs
        (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
          (substAssign z L) Ps) →
      TermVec.varsAllIn C (TermVec.ofArgs xs) → TermVec.varsAllIn D Ps) := by
  let motiveT := fun (s : S) (P : Term sig X s) =>
    ∀ R : Term sig X s,
      R ∈ (show Set (Term sig X s) from
        Term.eval (powerAlgebra (freeAlgebra sig X)) (substAssign z L) P) →
      Term.varsIn C R → Term.varsIn D P
  let motiveV := fun (w : List S) (Ps : TermVec sig X w) =>
    ∀ xs : Args (Term sig X) w,
      Args.pmem xs
        (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
          (substAssign z L) Ps) →
      TermVec.varsAllIn C (TermVec.ofArgs xs) → TermVec.varsAllIn D Ps
  let varCase : ∀ {s : S} (x : X s), motiveT s (Term.var x) := by
    intro s x R hR hvars
    dsimp [motiveT] at hR ⊢
    by_cases hst : s = t
    · subst s
      by_cases hxz : x = z
      · subst x
        exact hz
      · change R ∈ (show Set (Term sig X t) from substAssign z L t x) at hR
        have hEq : R = Term.var x := by simpa [substAssign, hxz] using hR
        subst R
        exact hother x hvars (fun _ => hxz)
    · change R ∈ (show Set (Term sig X s) from substAssign z L s x) at hR
      have hEq : R = Term.var x := by simpa [substAssign, hst] using hR
      subst R
      exact hother x hvars (fun h => (hst h).elim)
  let appCase : ∀ {w : List S} {s : S} (σ : sig w s)
      (Ps : TermVec sig X w), motiveV w Ps → motiveT s (Term.app σ Ps) := by
    intro w s σ Ps ih R hR hvars
    dsimp [motiveT, motiveV] at ih hR ⊢
    simp only [Term.eval, powerAlgebra_op, powerOp, Set.mem_setOf_eq,
      freeAlgebra] at hR
    rcases hR with ⟨xs, hxs, hEq⟩
    have hEq' : Term.app σ (TermVec.ofArgs xs) = R := hEq.symm
    subst R
    exact ih xs hxs hvars
  let nilCase : motiveV [] (TermVec.nil : TermVec sig X []) := by
    intro xs _ _
    trivial
  let consCase : ∀ {s : S} {w : List S} (P : Term sig X s)
      (Ps : TermVec sig X w), motiveT s P → motiveV w Ps →
      motiveV (s :: w) (.cons P Ps) := by
    intro s w P Ps ihP ihPs xs hxs hvars
    rcases xs with ⟨R, Rs⟩
    dsimp [motiveT, motiveV] at ihP ihPs ⊢
    simp only [TermVec.evalArgs] at hxs
    exact ⟨ihP R hxs.1 hvars.1, ihPs Rs hxs.2 hvars.2⟩
  exact ⟨@Term.rec _ _ _ motiveT motiveV varCase appCase nilCase consCase,
    @TermVec.rec _ _ _ motiveT motiveV varCase appCase nilCase consCase⟩

/-- A structural preservation theorem for the semantic substitution
homomorphism.  Besides the usual variable and proper-subterm invariants it
tracks the root bound needed when a substituted result is itself used as a
child. -/
theorem substHom_preserves_aux_structure (ctx : KleeneCtx sig X)
    {t : S} (z : ctx.Z t) (L : Set (Term sig ctx.Z t))
    (D E : (s : S) → ctx.Z s → Prop) (J B : S → ℕ)
    (hvar : ∀ {s : S} (x : ctx.Z s), D s x →
      (∀ h : s = t, h ▸ x ≠ z) → E s x)
    (hJB : ∀ s, J s ≤ B s)
    (hL : ∀ Q ∈ L,
      Term.varsIn E Q ∧ Term.boundedProper ctx B Q ∧
      ctx.hHom.toFun t Q = ctx.hHom.toFun t (Term.var z) ∧
      (¬ Min (⟨t, Q⟩ : STerm sig ctx.Z) → ctx.hVal ⟨t, Q⟩ < B t)) :
    (∀ {s : S} (P R : Term sig ctx.Z s),
      R ∈ (show Set (Term sig ctx.Z s) from (substHom z L).toFun s P) →
      Term.varsIn D P →
      Term.boundedProper ctx J P →
      (Term.varsIn E R ∧ Term.boundedProper ctx B R ∧
        ctx.hHom.toFun s R = ctx.hHom.toFun s P) ∧
      ((¬ Min (⟨s, P⟩ : STerm sig ctx.Z) → ctx.hVal ⟨s, P⟩ < J s) →
        ¬ Min (⟨s, R⟩ : STerm sig ctx.Z) → ctx.hVal ⟨s, R⟩ < B s)) ∧
    (∀ {w : List S} (Ps : TermVec sig ctx.Z w)
        (xs : Args (Term sig ctx.Z) w),
      Args.pmem xs
        (TermVec.evalArgs (powerAlgebra (freeAlgebra sig ctx.Z))
          (substAssign z L) Ps) →
      TermVec.varsAllIn D Ps → TermVec.boundedNodes ctx J Ps →
      TermVec.varsAllIn E (TermVec.ofArgs xs) ∧
      TermVec.boundedNodes ctx B (TermVec.ofArgs xs) ∧
      Args.map ctx.hHom.toFun xs =
        Args.map ctx.hHom.toFun (TermVec.toArgs Ps)) := by
  let motiveT := fun (s : S) (P : Term sig ctx.Z s) =>
    ∀ R : Term sig ctx.Z s,
      R ∈ (show Set (Term sig ctx.Z s) from
        Term.eval (powerAlgebra (freeAlgebra sig ctx.Z)) (substAssign z L) P) →
      Term.varsIn D P → Term.boundedProper ctx J P →
      (Term.varsIn E R ∧ Term.boundedProper ctx B R ∧
        ctx.hHom.toFun s R = ctx.hHom.toFun s P) ∧
      ((¬ Min (⟨s, P⟩ : STerm sig ctx.Z) → ctx.hVal ⟨s, P⟩ < J s) →
        ¬ Min (⟨s, R⟩ : STerm sig ctx.Z) → ctx.hVal ⟨s, R⟩ < B s)
  let motiveV := fun (w : List S) (Ps : TermVec sig ctx.Z w) =>
    ∀ xs : Args (Term sig ctx.Z) w,
      Args.pmem xs
        (TermVec.evalArgs (powerAlgebra (freeAlgebra sig ctx.Z))
          (substAssign z L) Ps) →
      TermVec.varsAllIn D Ps → TermVec.boundedNodes ctx J Ps →
      TermVec.varsAllIn E (TermVec.ofArgs xs) ∧
      TermVec.boundedNodes ctx B (TermVec.ofArgs xs) ∧
      Args.map ctx.hHom.toFun xs =
        Args.map ctx.hHom.toFun (TermVec.toArgs Ps)
  let varCase : ∀ {s : S} (x : ctx.Z s), motiveT s (Term.var x) := by
    intro s x R hR hx _
    dsimp [motiveT] at hR ⊢
    by_cases hst : s = t
    · subst s
      by_cases hxz : x = z
      · subst x
        change R ∈ (show Set (Term sig ctx.Z t) from substAssign z L t z) at hR
        have hRL : R ∈ L := by simpa [substAssign] using hR
        rcases hL R hRL with ⟨hvars, hbound, hhom, hroot⟩
        exact ⟨⟨hvars, hbound, hhom⟩, fun _ => hroot⟩
      · change R ∈ (show Set (Term sig ctx.Z t) from substAssign z L t x) at hR
        have hEq : R = Term.var x := by simpa [substAssign, hxz] using hR
        subst R
        refine ⟨⟨hvar x hx (fun _ => hxz), trivial, rfl⟩, ?_⟩
        exact fun _ hnon => (hnon (main_min_var x)).elim
    · change R ∈ (show Set (Term sig ctx.Z s) from substAssign z L s x) at hR
      have hEq : R = Term.var x := by simpa [substAssign, hst] using hR
      subst R
      refine ⟨⟨hvar x hx (fun h => (hst h).elim), trivial, rfl⟩, ?_⟩
      exact fun _ hnon => (hnon (main_min_var x)).elim
  let appCase : ∀ {w : List S} {s : S} (σ : sig w s)
      (Ps : TermVec sig ctx.Z w), motiveV w Ps → motiveT s (Term.app σ Ps) := by
    intro w s σ Ps ih R hR hvars hbound
    dsimp [motiveT, motiveV] at ih hR ⊢
    simp only [Term.eval, powerAlgebra_op, powerOp, Set.mem_setOf_eq,
      freeAlgebra] at hR
    rcases hR with ⟨xs, hxs, hEq⟩
    have hout := ih xs hxs hvars hbound
    rcases hout with ⟨hvarsOut, hboundOut, hhomArgs⟩
    have hEq' : Term.app σ (TermVec.ofArgs xs) = R := hEq.symm
    subst R
    have hhom : ctx.hHom.toFun s (Term.app σ (TermVec.ofArgs xs)) =
        ctx.hHom.toFun s (Term.app σ Ps) := by
      calc
        ctx.hHom.toFun s (Term.app σ (TermVec.ofArgs xs)) =
            (ctx.NAlg).op σ (Args.map ctx.hHom.toFun xs) := by
          simpa [freeAlgebra] using ctx.hHom.map_op σ xs
        _ = (ctx.NAlg).op σ
            (Args.map ctx.hHom.toFun (TermVec.toArgs Ps)) :=
          congrArg ((ctx.NAlg).op σ) hhomArgs
        _ = ctx.hHom.toFun s (Term.app σ Ps) := by
          symm
          simpa [freeAlgebra, main_ofArgs_toArgs] using
            ctx.hHom.map_op σ (TermVec.toArgs Ps)
    refine ⟨⟨hvarsOut, hboundOut, hhom⟩, ?_⟩
    intro hroot hnon
    have hnonIn : ¬ Min (⟨s, Term.app σ Ps⟩ : STerm sig ctx.Z) := by
      cases w with
      | nil =>
          cases Ps
          rcases xs with ⟨⟩
          exact (hnon (main_min_nil σ)).elim
      | cons r w =>
          cases Ps with
          | cons P Ps => exact main_nonmin_cons σ P Ps
    have hv : ctx.hVal ⟨s, Term.app σ (TermVec.ofArgs xs)⟩ =
        ctx.hVal ⟨s, Term.app σ Ps⟩ := congrArg Fin.val hhom
    rw [hv]
    exact lt_of_lt_of_le (hroot hnonIn) (hJB s)
  let nilCase : motiveV [] (TermVec.nil : TermVec sig ctx.Z []) := by
    intro xs _ _ _
    rcases xs with ⟨⟩
    exact ⟨trivial, trivial, rfl⟩
  let consCase : ∀ {s : S} {w : List S} (P : Term sig ctx.Z s)
      (Ps : TermVec sig ctx.Z w), motiveT s P → motiveV w Ps →
      motiveV (s :: w) (.cons P Ps) := by
    intro s w P Ps ihP ihPs xs hxs hvars hbound
    rcases xs with ⟨R, Rs⟩
    dsimp [motiveT, motiveV] at ihP ihPs ⊢
    simp only [TermVec.evalArgs, Args.pmem] at hxs
    rcases hxs with ⟨hR, hRs⟩
    rcases hvars with ⟨hvarsP, hvarsPs⟩
    rcases hbound with ⟨hrootP, hboundP, hboundPs⟩
    rcases ihP R hR hvarsP hboundP with ⟨hbasicP, hstrongP⟩
    rcases ihPs Rs hRs hvarsPs hboundPs with
      ⟨hvarsRs, hboundRs, hhomRs⟩
    rcases hbasicP with ⟨hvarsR, hboundR, hhomR⟩
    refine ⟨⟨hvarsR, hvarsRs⟩,
      ⟨hstrongP hrootP, hboundR, hboundRs⟩, ?_⟩
    exact congrArg₂ Prod.mk hhomR hhomRs
  exact ⟨@Term.rec _ _ _ motiveT motiveV varCase appCase nilCase consCase,
    @TermVec.rec _ _ _ motiveT motiveV varCase appCase nilCase consCase⟩

/-- Claim C1 in the form actually needed by state elimination: substituting a
state-preserving language whose roots and proper nodes satisfy the output
budget preserves the auxiliary-language invariant. -/
theorem substP_aux_subset (ctx : KleeneCtx sig X) {t s : S} (z : ctx.Z t)
    (L : Set (Term sig ctx.Z t))
    (D E : (r : S) → Set (Fin (ctx.n r))) (J B : S → ℕ)
    (hvar : ∀ {r : S} (x : ctx.Z r), ctx.inXC D r x →
      (∀ h : r = t, h ▸ x ≠ z) → ctx.inXC E r x)
    (hJB : ∀ r, J r ≤ B r)
    (hLE : L ⊆ ctx.auxLang t E B (ctx.hHom.toFun t (Term.var z)))
    (hzB : (ctx.hHom.toFun t (Term.var z)).val < B t)
    (l : Fin (ctx.n s)) :
    substP z L s (ctx.auxLang s D J l) ⊆ ctx.auxLang s E B l := by
  intro R hR
  unfold substP at hR
  rcases Set.mem_iUnion.mp hR with ⟨P, hR⟩
  rcases Set.mem_iUnion.mp hR with ⟨hP, hRP⟩
  have hLstruct : ∀ Q ∈ L,
      Term.varsIn (ctx.inXC E) Q ∧ Term.boundedProper ctx B Q ∧
      ctx.hHom.toFun t Q = ctx.hHom.toFun t (Term.var z) ∧
      (¬ Min (⟨t, Q⟩ : STerm sig ctx.Z) → ctx.hVal ⟨t, Q⟩ < B t) := by
    intro Q hQ
    rcases (mem_auxLang_iff_structural ctx E B _ Q).1 (hLE hQ) with
      ⟨hvarsQ, hboundQ, hvalQ⟩
    refine ⟨hvarsQ, hboundQ, hvalQ, ?_⟩
    intro _
    change (ctx.hHom.toFun t Q).val < B t
    rw [hvalQ]
    exact hzB
  rcases (mem_auxLang_iff_structural ctx D J l P).1 hP with
    ⟨hvarsP, hboundP, hvalP⟩
  have hpres := (substHom_preserves_aux_structure ctx z L
    (ctx.inXC D) (ctx.inXC E) J B hvar hJB hLstruct).1 P R hRP hvarsP hboundP
  rcases hpres.1 with ⟨hvarsR, hboundR, hhomR⟩
  apply (mem_auxLang_iff_structural ctx E B l R).2
  exact ⟨hvarsR, hboundR, hhomR.trans hvalP⟩

end SubstitutionStructure

section TopState

variable {S : Type} [Finite S] {sig : Signature S} {X : SSet S}

/-- The state removed in one elimination step. -/
def topState (ctx : KleeneCtx sig X) (K : S → ℕ) (hK : ∀ s, K s ≤ ctx.n s)
    (t : S) (ht : 0 < K t) : Fin (ctx.n t) :=
  ⟨K t - 1, (by
    apply lt_of_lt_of_le (b := K t)
    · omega
    · exact hK t)⟩

@[simp] theorem topState_val (ctx : KleeneCtx sig X) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) (ht : 0 < K t) :
    (topState ctx K hK t ht).val = K t - 1 := rfl

theorem budgetPred_bounded (ctx : KleeneCtx sig X) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) :
    ∀ s, budgetPred K t s ≤ ctx.n s :=
  fun s => (budgetPred_le K t s).trans (hK s)

theorem state_lt_budgetPred_of_ne_top (ctx : KleeneCtx sig X) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) (ht : 0 < K t)
    (m : Fin (ctx.n t)) (hm : m.val < K t)
    (hne : m ≠ topState ctx K hK t ht) : m.val < budgetPred K t t := by
  rw [budgetPred_apply_self]
  have hvalne : m.val ≠ K t - 1 := by
    intro heq
    apply hne
    apply Fin.ext
    simpa [topState] using heq
  omega

end TopState

section EliminationClosure

variable {S : Type} [Finite S] {sig : Signature S} {X : SSet S}

@[simp] theorem hHom_stateVar (ctx : KleeneCtx sig X) {t : S}
    (z : Fin (ctx.n t)) :
    ctx.hHom.toFun t (Term.var (Sum.inr z : ctx.Z t)) = z := rfl

theorem inXC_remove_added (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s))) {t r : S}
    (z : Fin (ctx.n t)) (x : ctx.Z r)
    (hx : ctx.inXC (addState ctx C t z) r x)
    (hne : ∀ h : r = t, h ▸ x ≠ (Sum.inr z : ctx.Z t)) :
    ctx.inXC C r x := by
  cases x with
  | inl x => trivial
  | inr m =>
      change m ∈ addState ctx C t z r at hx
      change m ∈ C r
      rcases hx with hm | ⟨h, hm⟩
      · exact hm
      · exfalso
        cases h
        have hm' : m = z := by simpa using hm
        apply hne rfl
        simpa [hm']

theorem iterate_top_subset (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) (ht : 0 < K t) :
    let z := topState ctx K hK t ht
    let Cz := addState ctx C t z
    iterate (Sum.inr z : ctx.Z t)
        (ctx.auxLang t Cz (budgetPred K t) z) ⊆
      ctx.auxLang t Cz K z := by
  dsimp only
  let z := topState ctx K hK t ht
  let zv : ctx.Z t := Sum.inr z
  let Cz := addState ctx C t z
  let L := ctx.auxLang t Cz (budgetPred K t) z
  have hzK : (ctx.hHom.toFun t (Term.var zv)).val < K t := by
    change z.val < K t
    dsimp [z]
    omega
  have hstage : ∀ i : ℕ, iterStage zv L i ⊆ ctx.auxLang t Cz K z := by
    intro i
    induction i with
    | zero =>
        intro P hP
        have hEq : P = Term.var zv := by simpa [iterStage] using hP
        subst P
        apply (mem_auxLang_iff_structural ctx Cz K z (Term.var zv)).2
        refine ⟨?_, trivial, rfl⟩
        change z ∈ Cz t
        exact mem_addState_self ctx C t z
    | succ i ih =>
        rw [iterStage_succ]
        intro P hP
        rcases hP with hP | hP
        · exact ih hP
        · refine substP_aux_subset ctx zv (iterStage zv L i) Cz Cz
            (budgetPred K t) K ?_ ?_ ?_ ?_ z ?_
          · intro r x hx _
            exact hx
          · exact budgetPred_le K t
          · simpa [zv] using ih
          · exact hzK
          · simpa [L] using hP
  intro P hP
  unfold iterate at hP
  rcases Set.mem_iUnion.mp hP with ⟨i, hi⟩
  exact hstage i hi

/-- The right-to-left inclusion of the one-state elimination equation (Claims
C2 and C3 of the source proof), using a single chosen nonzero sort. -/
theorem elimination_rhs_subset (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) (ht : 0 < K t)
    (u : S) (l : Fin (ctx.n u)) :
    let z := topState ctx K hK t ht
    let zv : ctx.Z t := Sum.inr z
    let Cz := addState ctx C t z
    let Kp := budgetPred K t
    let L0 := ctx.auxLang t C Kp z
    let L1 := ctx.auxLang t Cz Kp z
    let inner := substP zv (iterate zv L1) u (ctx.auxLang u Cz Kp l)
    ctx.auxLang u C Kp l ∪ substP zv L0 u inner ⊆
      ctx.auxLang u C K l := by
  dsimp only
  let z := topState ctx K hK t ht
  let zv : ctx.Z t := Sum.inr z
  let Cz := addState ctx C t z
  let Kp := budgetPred K t
  let L0 := ctx.auxLang t C Kp z
  let L1 := ctx.auxLang t Cz Kp z
  let inner := substP zv (iterate zv L1) u (ctx.auxLang u Cz Kp l)
  have hzK : (ctx.hHom.toFun t (Term.var zv)).val < K t := by
    change z.val < K t
    dsimp [z]
    omega
  have hinner : inner ⊆ ctx.auxLang u Cz K l := by
    dsimp [inner]
    refine substP_aux_subset ctx zv (iterate zv L1) Cz Cz Kp K ?_ ?_ ?_ ?_ l
    · intro r x hx _
      exact hx
    · exact budgetPred_le K t
    · simpa [L1, zv, Cz, z] using iterate_top_subset ctx C K hK t ht
    · exact hzK
  have houter : substP zv L0 u inner ⊆ ctx.auxLang u C K l := by
    refine Set.Subset.trans (fun P hP => ?_)
      (substP_aux_subset ctx zv L0 Cz C K K ?_ (fun _ => Nat.le_refl _)
        ?_ hzK l)
    · unfold substP at hP ⊢
      rcases Set.mem_iUnion.mp hP with ⟨Q, hP⟩
      rcases Set.mem_iUnion.mp hP with ⟨hQ, hPQ⟩
      exact Set.mem_iUnion.mpr ⟨Q, Set.mem_iUnion.mpr ⟨hinner hQ, hPQ⟩⟩
    · intro r x hx hne
      exact inXC_remove_added ctx C z x hx hne
    · dsimp [L0, Kp]
      exact auxLang_budgetPred_subset ctx C K t z
  intro P hP
  rcases hP with hP | hP
  · exact auxLang_budgetPred_subset ctx C K t l hP
  · exact houter hP

/-- Claim C5 specialized to the top state selected for elimination. -/
theorem collapse_aux_step (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) (ht : 0 < K t)
    {u : S} (l : Fin (ctx.n u)) (P : Term sig ctx.Z u)
    (hP : P ∈ ctx.auxLang u C K l)
    (hnP : ¬ Min (⟨u, P⟩ : STerm sig ctx.Z)) :
    let z := topState ctx K hK t ht
    let zv : ctx.Z t := Sum.inr z
    let Cz := addState ctx C t z
    ∃ (W : Term sig ctx.Z u) (qs : Fin (Term.occ zv W) → Term sig ctx.Z t),
      P = substFam zv W qs ∧
      (∀ a, SubtermLT (⟨t, qs a⟩ : STerm sig ctx.Z) ⟨u, P⟩ ∧
        ctx.hHom.toFun t (qs a) = z) ∧
      W ∈ ctx.auxLang u Cz (budgetPred K t) l := by
  dsimp only
  let z := topState ctx K hK t ht
  let zv : ctx.Z t := Sum.inr z
  let Cz := addState ctx C t z
  rcases collapse_lemma sig ctx.Z ctx.NAlg ctx.hHom zv P hnP with
    ⟨W, qs, hEq, hhomW, hqs, hcollapse⟩
  rcases (mem_auxLang_iff_structural ctx C K l P).1 hP with
    ⟨hvarsP, hboundP, hvalP⟩
  have hSubMem : P ∈ (show Set (Term sig ctx.Z u) from
      (substHom zv (Set.range qs)).toFun u W) := by
    rw [(subst_family sig ctx.Z zv (Set.range qs) W).1]
    exact ⟨qs, fun a => Set.mem_range_self a, hEq⟩
  have hvarsW : Term.varsIn (ctx.inXC Cz) W := by
    apply (substHom_varsIn_inverse zv (Set.range qs)
      (ctx.inXC C) (ctx.inXC Cz) ?_ ?_).1 W P hSubMem hvarsP
    · change z ∈ Cz t
      exact mem_addState_self ctx C t z
    · intro r x hx _
      cases x with
      | inl x => trivial
      | inr m => exact subset_addState ctx C t z r hx
  have hboundW : Term.boundedProper ctx (budgetPred K t) W := by
    apply (boundedProper_iff ctx (budgetPred K t) W).2
    intro Q hQW hnQ
    rcases Q with ⟨q, Q⟩
    rcases hcollapse ⟨q, Q⟩ hQW hnQ with
      ⟨hnot, N, hNP, hnN, hsort, hhom⟩
    rcases N with ⟨r, N⟩
    dsimp only at hsort
    subst r
    have hQK : ctx.hVal (⟨q, Q⟩ : STerm sig ctx.Z) < K q := by
      have hNK := (boundedProper_iff ctx K P).1 hboundP
        (⟨q, N⟩ : STerm sig ctx.Z) hNP hnN
      unfold KleeneCtx.hVal at hNK ⊢
      simpa [hhom] using hNK
    by_cases hsortt : q = t
    · cases hsortt
      apply state_lt_budgetPred_of_ne_top ctx K hK t ht
          (ctx.hHom.toFun t Q) hQK
      intro heq
      apply hnot
      refine ⟨rfl, ?_⟩
      change ctx.hHom.toFun t Q = z
      exact heq
    · rw [budgetPred_apply_of_ne K hsortt]
      exact hQK
  refine ⟨W, qs, hEq, ?_, ?_⟩
  · intro a
    refine ⟨(hqs a).1, ?_⟩
    simpa [zv] using (hqs a).2
  · apply (mem_auxLang_iff_structural ctx Cz (budgetPred K t) l W).2
    exact ⟨hvarsW, hboundW, hhomW.trans hvalP⟩

/-- Claim C6: every proper subterm evaluating to the eliminated state factors
through the lower-budget base language and the iterated lower-budget loop
language. -/
theorem subterm_top_factor (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) (ht : 0 < K t)
    {u : S} (l : Fin (ctx.n u)) (P : Term sig ctx.Z u)
    (hP : P ∈ ctx.auxLang u C K l) (Q : Term sig ctx.Z t)
    (hQP : SubtermLT (⟨t, Q⟩ : STerm sig ctx.Z) ⟨u, P⟩)
    (hQstate : ctx.hHom.toFun t Q = topState ctx K hK t ht) :
    let z := topState ctx K hK t ht
    let zv : ctx.Z t := Sum.inr z
    let Cz := addState ctx C t z
    let L0 := ctx.auxLang t C (budgetPred K t) z
    let L1 := ctx.auxLang t Cz (budgetPred K t) z
    Q ∈ substP zv L0 t (iterate zv L1) := by
  dsimp only
  let z := topState ctx K hK t ht
  let zv : ctx.Z t := Sum.inr z
  let Cz := addState ctx C t z
  let L0 := ctx.auxLang t C (budgetPred K t) z
  let L1 := ctx.auxLang t Cz (budgetPred K t) z
  let M := substP zv L0 t (iterate zv L1)
  have hvarsP := ((mem_auxLang_iff_structural ctx C K l P).1 hP).1
  have hboundP := ((mem_auxLang_iff_structural ctx C K l P).1 hP).2.1
  have wf : WellFounded (fun A B : Term sig ctx.Z t =>
      SubtermLT (⟨t, A⟩ : STerm sig ctx.Z) ⟨t, B⟩) :=
    InvImage.wf (fun A : Term sig ctx.Z t => (⟨t, A⟩ : STerm sig ctx.Z))
      (subterm_wf sig ctx.Z).1
  have claim : ∀ R : Term sig ctx.Z t,
      SubtermLT (⟨t, R⟩ : STerm sig ctx.Z) ⟨u, P⟩ →
      ctx.hHom.toFun t R = z → R ∈ M := by
    intro R
    induction R using wf.induction with
    | h R ih =>
        intro hRP hRstate
        by_cases hmin : Min (⟨t, R⟩ : STerm sig ctx.Z)
        · have hRL0 : R ∈ L0 := by
            apply (mem_auxLang_iff_structural ctx C (budgetPred K t) z R).2
            refine ⟨Term.varsIn_of_subtermLT hRP hvarsP, ?_, hRstate⟩
            apply (boundedProper_iff ctx (budgetPred K t) R).2
            intro A hAR _
            cases hAR with
            | single himm => exact (hmin A himm).elim
            | tail _ himm => exact (hmin _ himm).elim
          have hzIter : Term.var zv ∈ iterate zv L1 := by
            unfold iterate
            apply Set.mem_iUnion.mpr
            exact ⟨0, by simp [iterStage]⟩
          dsimp [M]
          unfold substP
          apply Set.mem_iUnion.mpr
          refine ⟨Term.var zv, Set.mem_iUnion.mpr ⟨hzIter, ?_⟩⟩
          change R ∈ (show Set (Term sig ctx.Z t) from substAssign zv L0 t zv)
          simpa [substAssign] using hRL0
        · have hRaux : R ∈ ctx.auxLang t C K z := by
            apply (mem_auxLang_iff_structural ctx C K z R).2
            refine ⟨Term.varsIn_of_subtermLT hRP hvarsP, ?_, hRstate⟩
            apply (boundedProper_iff ctx K R).2
            intro A hAR hnA
            exact (boundedProper_iff ctx K P).1 hboundP A
              (hAR.trans hRP) hnA
          rcases collapse_aux_step ctx C K hK t ht z R hRaux hmin with
            ⟨W, qs, hEq, hqs, hWL1⟩
          have hQM : R ∈ substP zv M t L1 := by
            unfold substP
            apply Set.mem_iUnion.mpr
            refine ⟨W, Set.mem_iUnion.mpr ⟨hWL1, ?_⟩⟩
            rw [(subst_family sig ctx.Z zv M W).1]
            refine ⟨qs, ?_, hEq⟩
            intro a
            exact ih (qs a) (hqs a).1 ((hqs a).1.trans hRP) (hqs a).2
          have hcomp : R ∈ substP zv L0 t (substP zv (iterate zv L1) t L1) :=
            subst_comp sig ctx.Z zv L0 (iterate zv L1) L1 hQM
          exact substP_mono zv Set.Subset.rfl (iter_absorb sig ctx.Z zv L1) hcomp
  exact claim Q hQP hQstate

/-- The left-to-right inclusion of the one-state elimination equation.  A
minimal term already satisfies the lowered budget.  A nonminimal term is
collapsed at all first occurrences of the chosen top state, and Claim C6
factors every term substituted at those occurrences. -/
theorem elimination_lhs_subset (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) (ht : 0 < K t)
    (u : S) (l : Fin (ctx.n u)) :
    let z := topState ctx K hK t ht
    let zv : ctx.Z t := Sum.inr z
    let Cz := addState ctx C t z
    let Kp := budgetPred K t
    let L0 := ctx.auxLang t C Kp z
    let L1 := ctx.auxLang t Cz Kp z
    let inner := substP zv (iterate zv L1) u (ctx.auxLang u Cz Kp l)
    ctx.auxLang u C K l ⊆
      ctx.auxLang u C Kp l ∪ substP zv L0 u inner := by
  dsimp only
  let z := topState ctx K hK t ht
  let zv : ctx.Z t := Sum.inr z
  let Cz := addState ctx C t z
  let Kp := budgetPred K t
  let L0 := ctx.auxLang t C Kp z
  let L1 := ctx.auxLang t Cz Kp z
  let M := substP zv L0 t (iterate zv L1)
  let inner := substP zv (iterate zv L1) u (ctx.auxLang u Cz Kp l)
  intro P hP
  by_cases hmin : Min (⟨u, P⟩ : STerm sig ctx.Z)
  · apply Or.inl
    rcases (mem_auxLang_iff_structural ctx C K l P).1 hP with
      ⟨hvars, _, hval⟩
    apply (mem_auxLang_iff_structural ctx C Kp l P).2
    refine ⟨hvars, ?_, hval⟩
    apply (boundedProper_iff ctx Kp P).2
    intro Q hQP _
    cases hQP with
    | single himm => exact (hmin Q himm).elim
    | tail _ himm => exact (hmin _ himm).elim
  · apply Or.inr
    rcases collapse_aux_step ctx C K hK t ht l P hP hmin with
      ⟨W, qs, hEq, hqs, hW⟩
    have hPM : P ∈ substP zv M u (ctx.auxLang u Cz Kp l) := by
      unfold substP
      apply Set.mem_iUnion.mpr
      refine ⟨W, Set.mem_iUnion.mpr ⟨hW, ?_⟩⟩
      rw [(subst_family sig ctx.Z zv M W).1]
      refine ⟨qs, ?_, hEq⟩
      intro a
      exact subterm_top_factor ctx C K hK t ht l P hP (qs a)
        (hqs a).1 (hqs a).2
    exact subst_comp sig ctx.Z zv L0 (iterate zv L1)
      (ctx.auxLang u Cz Kp l) hPM

/-- Exact one-state elimination identity, the algebraic heart of the Main
Claim. -/
theorem elimination_eq (ctx : KleeneCtx sig X)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (t : S) (ht : 0 < K t)
    (u : S) (l : Fin (ctx.n u)) :
    let z := topState ctx K hK t ht
    let zv : ctx.Z t := Sum.inr z
    let Cz := addState ctx C t z
    let Kp := budgetPred K t
    let L0 := ctx.auxLang t C Kp z
    let L1 := ctx.auxLang t Cz Kp z
    let inner := substP zv (iterate zv L1) u (ctx.auxLang u Cz Kp l)
    ctx.auxLang u C K l =
      ctx.auxLang u C Kp l ∪ substP zv L0 u inner := by
  apply Set.Subset.antisymm
  · exact elimination_lhs_subset ctx C K hK t ht u l
  · exact elimination_rhs_subset ctx C K hK t ht u l

end EliminationClosure

section ZeroBudget

variable {S : Type} [Finite S] {sig : Signature S} {X : SSet S}

theorem KleeneCtx.Z_sfinite (ctx : KleeneCtx sig X) (hX : SFinite X) :
    SFinite ctx.Z := by
  unfold SFinite KleeneCtx.Z extVars
  letI : Finite (Σ s, X s) := hX
  letI finiteX (s : S) : Finite (X s) := finite_fiber_of_sfinite hX s
  letI finiteState (s : S) : Finite (Fin (ctx.n s)) := inferInstance
  infer_instance

theorem auxLang_zero_finite (sig : Signature S) (X : SSet S)
    (hsig : SigFinite sig) (hX : SFinite X) (ctx : KleeneCtx sig X)
    (u : S) (C : (s : S) → Set (Fin (ctx.n s))) (l : Fin (ctx.n u)) :
    (ctx.auxLang u C (fun _ => 0) l).Finite := by
  apply (finite_of_all_proper_subterms_min (ctx.Z_sfinite hX) hsig u).subset
  intro P hP
  change Term.varsIn (ctx.inXC C) P ∧
      (∀ Q : STerm sig ctx.Z, SubtermLT Q ⟨u, P⟩ → ¬ Min Q →
        Term.varsIn (ctx.inXC C) Q.2 → ctx.hVal Q < 0) ∧
      ctx.hHom.toFun u P = l at hP
  rcases hP with ⟨hvars, hbound, _⟩
  intro Q hQP
  by_contra hQ
  have hvarsQ := Term.varsIn_of_subtermLT hQP hvars
  exact (Nat.not_lt_zero (ctx.hVal Q)) (hbound Q hQP hQ hvarsQ)

/-- The base case of the Main Claim, isolated from the state-elimination
induction. -/
theorem auxLang_zero_expr (sig : Signature S) (X : SSet S)
    (hsig : SigFinite sig) (hX : SFinite X) (ctx : KleeneCtx sig X)
    (u : S) (C : (s : S) → Set (Fin (ctx.n s))) (l : Fin (ctx.n u)) :
    ∃ R : RegExpr sig ctx.Z u,
      interpExpr sig ctx.Z u R = ctx.auxLang u C (fun _ => 0) l :=
  finite_language_expr hsig (ctx.Z_sfinite hX) _
    (auxLang_zero_finite sig X hsig hX ctx u C l)

end ZeroBudget

/-- The Main Claim (Claim 4.13): every bounded auxiliary language is regular.
The induction eliminates one greatest admissible state at a time. -/
theorem main_claim_proof {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hsig : SigFinite sig) (hX : SFinite X) (ctx : KleeneCtx sig X) (u : S)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ) (hK : ∀ s, K s ≤ ctx.n s)
    (l : Fin (ctx.n u)) :
    ∃ R : RegExpr sig ctx.Z u,
      interpExpr sig ctx.Z u R = ctx.auxLang u C K l := by
  classical
  generalize hn : budgetSize K = n
  induction n using Nat.strong_induction_on generalizing u C K with
  | h n ih =>
      by_cases hn0 : n = 0
      · have hsize0 : budgetSize K = 0 := hn.trans hn0
        have hzero : K = fun _ => 0 := budget_eq_zero_of_size_zero K hsize0
        subst K
        exact auxLang_zero_expr sig X hsig hX ctx u C l
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hbudgetpos : 0 < budgetSize K := by simpa [hn] using hnpos
        rcases exists_positive_of_budgetSize_pos K hbudgetpos with ⟨t, ht⟩
        let Kp := budgetPred K t
        let z := topState ctx K hK t ht
        let zv : ctx.Z t := Sum.inr z
        let Cz := addState ctx C t z
        have hKp : ∀ s, Kp s ≤ ctx.n s := by
          intro s
          exact (budgetPred_le K t s).trans (hK s)
        have hsizep : budgetSize Kp < n := by
          rw [show Kp = budgetPred K t from rfl, budgetPred_size K t ht, hn]
          omega
        rcases ih (budgetSize Kp) hsizep t C Kp hKp z rfl with ⟨R0, hR0⟩
        rcases ih (budgetSize Kp) hsizep t Cz Kp hKp z rfl with ⟨R1, hR1⟩
        rcases ih (budgetSize Kp) hsizep u Cz Kp hKp l rfl with ⟨Router, hRouter⟩
        rcases ih (budgetSize Kp) hsizep u C Kp hKp l rfl with ⟨Rbase, hRbase⟩
        let Rinner : RegExpr sig ctx.Z u := RegExpr.subst zv (RegExpr.iter zv R1) Router
        let Rjump : RegExpr sig ctx.Z u := RegExpr.subst zv R0 Rinner
        refine ⟨RegExpr.plus Rbase Rjump, ?_⟩
        rw [interp_plus, show interpExpr sig ctx.Z u Rbase = ctx.auxLang u C Kp l from hRbase]
        rw [show interpExpr sig ctx.Z u Rjump =
            substP zv (ctx.auxLang t C Kp z) u
              (substP zv (iterate zv (ctx.auxLang t Cz Kp z)) u
                (ctx.auxLang u Cz Kp l)) by
          simp [Rjump, Rinner, hR0, hR1, hRouter]]
        symm
        exact elimination_eq ctx C K hK t ht u l

end MSKleene

theorem solution {S : Type} [Finite S] (sig : MSKleene.Signature S)
    (X : MSKleene.SSet S) (hsig : MSKleene.SigFinite sig)
    (hX : MSKleene.SFinite X) (ctx : MSKleene.KleeneCtx sig X) (u : S)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (hK : ∀ s, K s ≤ ctx.n s) (l : Fin (ctx.n u)) :
    ∃ R : MSKleene.RegExpr sig ctx.Z u,
      MSKleene.interpExpr sig ctx.Z u R = ctx.auxLang u C K l :=
  MSKleene.main_claim_proof sig X hsig hX ctx u C K hK l

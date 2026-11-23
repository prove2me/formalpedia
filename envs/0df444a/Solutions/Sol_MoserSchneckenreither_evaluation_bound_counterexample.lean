-- Prove2me | solution 1 for MoserSchneckenreither.evaluation_bound_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T05:18:15.433491+00:00
-- url     : https://prove2.me/submissions/08308ba7-dc22-49f8-b430-8f1ce85d212d

import Definitions.Def_MoserSchneckenreither_Typing
import Mathlib.Algebra.Order.Ring.NNRat

namespace MSEvalBound
open MoserSchneckenreither

/-- Symbol 0 is a unary constructor `c`; 1 is a defined constant `d`; 2 is a defined unary `g`. -/
def ar : Fin 3 → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1

abbrev sig : Signature where
  count := 3
  arity := ar
  constructors := {0}
  constructors_nonempty := ⟨0, Finset.mem_singleton_self 0⟩
  has_constant := ⟨1, rfl⟩

abbrev c : Symbol sig := (0 : Fin 3)
abbrev d : Symbol sig := (1 : Fin 3)
abbrev g : Symbol sig := (2 : Fin 3)

@[simp] theorem ar_c : ar c = 1 := rfl
@[simp] theorem ar_d : ar d = 0 := rfl
@[simp] theorem ar_g : ar g = 1 := rfl
@[simp] theorem g_ne_c : g ≠ c := by decide
@[simp] theorem g_ne_d : g ≠ d := by decide

def x0 : Term sig := Term.var 0

def cx : Term sig := Term.app c fun _ ↦ x0

def rule : Rule sig where
  head := g
  args := fun _ ↦ cx
  rhs := x0
  defined_head := by decide
  no_extra_variables := by
    intro x hx
    simpa [x0, cx, Term.vars] using hx

def P : Problem sig := ⟨[rule], []⟩

theorem mem_symbols_arg {f : Symbol sig} {ts : Fin (sig.arity f) → Term sig} (i : Fin (sig.arity f))
    {h : Symbol sig} (hg : h ∈ (ts i).symbols) : h ∈ (Term.app f ts).symbols := by
  simp only [Term.symbols]
  exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, hg⟩)

theorem rewrites_g {t u : Term sig} (h : Rewrites P.rules t u) : g ∈ t.symbols := by
  induction h with
  | root r hr τ =>
    simp only [P, Problem.rules, List.append_nil, List.mem_singleton] at hr
    subst hr
    simp [Rule.lhs, Term.subst, Term.symbols, rule]
  | arg f ts us i _ _ ih => exact mem_symbols_arg i ih

theorem normal_of {t : Term sig} (ht : g ∉ t.symbols) : Normal P.rules t :=
  fun ⟨_, hu⟩ ↦ ht (rewrites_g hu)

theorem constructorLike_iff (f : Symbol sig) : ConstructorLike P f ↔ f = c := by
  constructor
  · rintro (h | ⟨r, hr, i, hi⟩)
    · simpa using h
    · simp only [P, Problem.rules, List.append_nil, List.mem_singleton] at hr
      subst hr
      simpa [rule, cx, x0, Term.symbols] using hi
  · rintro rfl; exact Or.inl (by simp)

noncomputable def e₀ : Annotation := Finsupp.single 0 1

noncomputable def gdecl : Declaration (sig.arity g) := ⟨fun _ ↦ e₀, 0, 0⟩

noncomputable def F : AnnotatedSignature P where
  declarations f a := (f = g ∧ HEq a gdecl) ∨
    (f ≠ g ∧ a = ⟨fun _ ↦ 0, a.output 0, a.output⟩)
  nonempty f := by
    by_cases hf : f = g
    · subst hf; exact ⟨gdecl, Or.inl ⟨rfl, HEq.rfl⟩⟩
    · exact ⟨⟨fun _ ↦ 0, (0 : Annotation) 0, 0⟩, Or.inr ⟨hf, rfl⟩⟩
  input _ _ _ := 0
  cost _ q := q 0
  constructor_declaration f hf q := by
    rw [constructorLike_iff] at hf
    subst hf
    exact Or.inr ⟨by decide, rfl⟩
  constructor_unique f hf a ha := by
    rw [constructorLike_iff] at hf
    subst hf
    rcases ha with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h (by decide)
    · rw [h]; exact ⟨rfl, rfl⟩
  input_add _ _ _ _ _ := by simp
  cost_add _ _ p q := Finsupp.add_apply p q 0
  input_scale _ _ _ _ _ := by simp [Annotation.scale]
  cost_scale _ _ a q := by simp [Annotation.scale]

def dT : Term sig := Term.app d (fun i ↦ Fin.elim0 i)

def cd : Term sig := Term.app c fun _ ↦ dT

def σ : Substitution sig := ⟨{0}, fun _ ↦ cd⟩

def xg : Fin (sig.arity g) → ℕ := fun _ ↦ 0
def xc : Fin (sig.arity c) → ℕ := fun _ ↦ 0
def xd : Fin (sig.arity d) → ℕ := fun i ↦ Fin.elim0 i

theorem xg_inj : Function.Injective xg := fun i j _ ↦ Subsingleton.elim (α := Fin 1) i j
theorem xc_inj : Function.Injective xc := fun i j _ ↦ Subsingleton.elim (α := Fin 1) i j
theorem xd_inj : Function.Injective xd := fun i _ _ ↦ Fin.elim0 i

def t : Term sig := Term.app g fun i ↦ Term.var (xg i)

noncomputable def Γ : Context := flatContext xg gdecl.inputs

theorem hΓ : Γ = [(0, e₀)] := rfl

theorem typing_cast {m : Mode} {Δ Δ' : Context} {k k' : ℚ≥0} {u u' : Term sig} {p : Annotation}
    (h : Typing F m Δ k u p) (h1 : Δ = Δ') (h2 : k = k') (h3 : u = u') : Typing F m Δ' k' u' p := by
  subst h1 h2 h3; exact h

theorem typ_d : Typing F .full [] 0 dT 0 := by
  have := Typing.app (F := F) .full d ⟨fun _ ↦ 0, (0 : Annotation) 0, 0⟩
    (Or.inr ⟨by decide, rfl⟩) xd xd_inj
  refine typing_cast this ?_ ?_ ?_
  · simp [flatContext]
  · simp
  · simp only [dT]; congr 1; funext i; exact Fin.elim0 i

theorem typ_cd : ∃ k, Typing F .full [] k cd e₀ := by
  have hhead := Typing.app (F := F) .full c ⟨fun _ ↦ 0, e₀ 0, e₀⟩
    (Or.inr ⟨by decide, rfl⟩) xc xc_inj
  have := Typing.comp (F := F) (mode := .full) c (fun _ ↦ dT) xc (fun _ ↦ 0) (fun _ ↦ [])
    (fun _ ↦ 0) (e₀ 0) e₀ xc_inj (by simp [Context.keys]) (by simp [Context.keys])
    (by
      unfold Term.Linear
      have : dT.vars = [] := by simp [dT, Term.vars]
      simp [Term.vars, this]) hhead (fun _ ↦ typ_d)
  exact ⟨_, typing_cast this (by simp) rfl rfl⟩

theorem d_not_cl : ¬ ConstructorLike P d := by
  rw [constructorLike_iff]; decide

theorem pot_zero (u : Term sig) (hu : d ∈ u.symbols) (p : Annotation) : potential F u p = 0 := by
  rw [potential, if_neg]
  rintro ⟨_, h⟩
  exact d_not_cl (h d hu)

theorem d_mem : d ∈ dT.symbols := List.mem_cons_self

theorem d_mem_cd : d ∈ cd.symbols := mem_symbols_arg (f := c) (ts := fun _ ↦ dT) ⟨0, by decide⟩ d_mem

theorem σ0 : σ.apply 0 = cd := by simp [Substitution.apply, σ]

theorem g_not_cd : g ∉ cd.symbols := by
  simp [cd, dT, Term.symbols]

theorem g_not_dT : g ∉ dT.symbols := by
  simp [dT, Term.symbols]

theorem deriv : Derivation P (t.subst σ.apply) 1 dT := by
  have hs : RestrictedStep P.rules P.strict (rule.lhs.subst fun _ ↦ dT) (rule.rhs.subst fun _ ↦ dT) :=
    RestrictedStep.root rule (by simp [P]) _ (fun _ ↦ normal_of g_not_cd)
  have h1 : t.subst σ.apply = rule.lhs.subst fun _ ↦ dT := by
    simp only [t, Term.subst, Rule.lhs, rule, xg, σ0, cx, x0]
    rfl
  have h2 : rule.rhs.subst (fun _ ↦ dT) = dT := rfl
  rw [h1, ← h2]
  exact Derivation.step (CountedStep.strict hs) (Derivation.refl _)

/-! ### Context lookup -/

theorem lookup_append (Δ Δ' : Context) (y : ℕ) :
    (Δ ++ Δ').lookup y = Δ.lookup y + Δ'.lookup y := by
  simp [Context.lookup, List.filter_append]

theorem lookup_single (a : ℕ) (b : Annotation) (y : ℕ) :
    Context.lookup [(a, b)] y = if a = y then b else 0 := by
  by_cases h : a = y <;> simp [Context.lookup, h]

theorem lookup_not_mem (Δ : Context) (y : ℕ) (hy : y ∉ Δ.keys) : Δ.lookup y = 0 := by
  unfold Context.lookup
  rw [List.filter_eq_nil_iff.2]
  · rfl
  · intro a ha hb
    simp only [beq_iff_eq] at hb
    exact hy (by simp only [Context.keys, List.mem_map]; exact ⟨a, ha, hb⟩)

theorem lookup_perm {Δ Δ' : Context} (h : Δ.Perm Δ') (y : ℕ) : Δ.lookup y = Δ'.lookup y :=
  ((h.filter _).map _).sum_eq

theorem rename_var {u : Term sig} {ρ : ℕ → ℕ} {y : ℕ} (h : u.rename ρ = .var y) :
    ∃ w, u = .var w ∧ ρ w = y := by
  cases u with
  | var w => exact ⟨w, rfl, by simpa [Term.rename, Term.subst] using h⟩
  | app f ts => simp [Term.rename, Term.subst] at h

theorem lookup_bound {m : Mode} {Δ : Context} {j : ℚ≥0} {u : Term sig} {p : Annotation}
    (h : Typing F m Δ j u p) : ∀ y, u = .var y → p ≤ Δ.lookup y := by
  induction h with
  | app => intro y hy; cases hy
  | var mode x q =>
    intro y hy; cases hy; simp [lookup_single]
  | comp => intro y hy; cases hy
  | share Γ x y z p₁ p₂ p q u k hshare hxy hxz hyz hx hy hz h ih =>
    intro y' hy'
    obtain ⟨w, rfl, hw⟩ := rename_var hy'
    have := ih w rfl
    have hΓx := lookup_not_mem Γ x hx
    have hΓy := lookup_not_mem Γ y hy
    have hΓz := lookup_not_mem Γ z hz
    unfold Shares at hshare
    subst hshare hw
    rw [lookup_append] at this ⊢
    rw [show ([(x, p₁), (y, p₂)] : Context) = [(x, p₁)] ++ [(y, p₂)] from rfl,
      lookup_append, lookup_single, lookup_single] at this
    rw [lookup_single]
    by_cases hwx : w = x
    · simp [hwx, hΓx, hΓz, hxy, hxy.symm] at this ⊢
      exact this.trans le_self_add
    · by_cases hwy : w = y
      · simp [hwy, hΓy, hΓz, hxy, hxy.symm] at this ⊢
        exact this.trans le_add_self
      · simp [hwx, hwy, Ne.symm hwx, Ne.symm hwy] at this ⊢
        exact this.trans le_self_add
  | perm hperm h ih => intro y hy; rw [← lookup_perm hperm]; exact ih y hy
  | w1 h hk ih => exact ih
  | w2 Γ x p r q k u h hr ih =>
    intro y hy
    refine (ih y hy).trans ?_
    rw [lookup_append, lookup_append, lookup_single, lookup_single]
    split_ifs
    · gcongr
    · exact le_rfl
  | w3 h hq ih => intro y hy; exact hq.trans (ih y hy)
  | w4 Γ x p q k u hx h ih =>
    intro y hy
    rw [lookup_append]
    exact (ih y hy).trans le_self_add

/-! ### Resource boundedness -/

theorem rule_bounded : RuleBounded F rule 1 := by
  intro a ha
  have hag : a = gdecl := by
    rcases ha with ⟨_, h⟩ | ⟨h, _⟩
    · exact eq_of_heq h
    · exact absurd rfl h
  subst hag
  refine ⟨[(0, 0)], 1, 0, ?_, by simp [gdecl], Typing.var .full 0 0⟩
  refine ⟨rule.args, id, fun _ ↦ [(0, 0)], fun _ ↦ 1, ?_, ?_, ?_, ?_, ?_⟩
  · simp [rule, cx, x0, Term.vars]
  · intro i; rfl
  · intro i
    refine ⟨by simp [Context.keys, rule, cx, x0, Term.vars], ?_⟩
    have := Typing.app (F := F) .footprint c ⟨fun _ ↦ 0, e₀ 0, e₀⟩
      (Or.inr ⟨by decide, rfl⟩) xc xc_inj
    exact typing_cast this (by simp [flatContext, xc]) (by simp [e₀]) rfl
  · simp [Context.renameMerge, List.eraseDups, rule]
    rw [show List.eraseDupsBy (fun x1 x2 : ℕ ↦ x1 == x2) [0] = [0] from rfl]
    simp
  · simp [rule]

theorem resource_bounded : ResourceBounded F := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [P, List.mem_singleton] at hr
    subst hr
    exact rule_bounded
  · intro r hr; simp [P] at hr

theorem main :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t v : Term sig) (q : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ p, (∃ j, Typing F .full Γ j (.var x) p) →
        ∃ j, Typing F .full Γ j (σ.apply x) p) ∧
      Typing F .full Γ k t q ∧ Derivation P (t.subst σ.apply) 1 v ∧ Normal P.rules v ∧
      (∃ j, Typing F .full [] j v q) ∧
      ¬ ((1 : ℚ≥0) + potential F v q ≤ contextPotential F σ Γ + k) := by
  refine ⟨sig, P, F, Γ, σ, t, dT, 0, 0, resource_bounded, ?_, ?_, ?_, ?_, deriv,
    normal_of g_not_dT, ⟨0, typ_d⟩, ?_⟩
  · intro x _
    exact ⟨by simp [σ, cd, dT, Term.Ground, Term.vars], normal_of g_not_cd⟩
  · refine ⟨by simp [hΓ, Context.Valid, Context.keys], ?_⟩
    intro x q hx
    rw [hΓ, List.mem_singleton, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨by simp [σ], by rw [σ0]; exact typ_cd⟩
  · intro x hx p ⟨j, hj⟩
    have hx0 : x = 0 := by simpa [σ] using hx
    subst hx0
    have hp := lookup_bound hj 0 rfl
    rw [hΓ, lookup_single, if_pos rfl] at hp
    obtain ⟨k, hk⟩ := typ_cd
    refine ⟨k, ?_⟩
    rw [σ0, hΓ]
    exact Typing.w4 [] 0 e₀ p k cd (by simp [Context.keys]) (Typing.w3 hk hp)
  · exact Typing.app .full g gdecl (Or.inl ⟨rfl, HEq.rfl⟩) xg xg_inj
  · rw [pot_zero _ d_mem]
    have : contextPotential F σ Γ = 0 := by
      rw [hΓ]
      simp only [contextPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, σ0]
      exact pot_zero _ d_mem_cd _
    rw [this]; simp

end MSEvalBound

open MoserSchneckenreither in
theorem solution :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t v : Term sig) (q : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ p, (∃ j, Typing F .full Γ j (.var x) p) →
        ∃ j, Typing F .full Γ j (σ.apply x) p) ∧
      Typing F .full Γ k t q ∧ Derivation P (t.subst σ.apply) 1 v ∧ Normal P.rules v ∧
      (∃ j, Typing F .full [] j v q) ∧
      ¬ ((1 : ℚ≥0) + potential F v q ≤ contextPotential F σ Γ + k) :=
  MSEvalBound.main

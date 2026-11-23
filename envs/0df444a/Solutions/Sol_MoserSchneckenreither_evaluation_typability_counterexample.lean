-- Prove2me | solution 1 for MoserSchneckenreither.evaluation_typability_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T05:31:31.281225+00:00
-- url     : https://prove2.me/submissions/cfe1b615-dd80-4cd8-8d03-7a70f15a190d

import Definitions.Def_MoserSchneckenreither_Typing
import Mathlib.Algebra.Order.Ring.NNRat

namespace MSEvalTyp
open MoserSchneckenreither

/-- Symbol 0 is a constructor constant `c`; 1 is a defined constant `d`; 2 is a defined binary `f`. -/
def ar : Fin 3 → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 2

abbrev sig : Signature where
  count := 3
  arity := ar
  constructors := {0}
  constructors_nonempty := ⟨0, Finset.mem_singleton_self 0⟩
  has_constant := ⟨1, rfl⟩

abbrev c : Symbol sig := (0 : Fin 3)
abbrev d : Symbol sig := (1 : Fin 3)
abbrev f : Symbol sig := (2 : Fin 3)

@[simp] theorem ar_c : ar c = 0 := rfl
@[simp] theorem ar_d : ar d = 0 := rfl
@[simp] theorem ar_f : ar f = 2 := rfl

def x0 : Term sig := Term.var 0

def rule : Rule sig where
  head := f
  args := fun _ ↦ x0
  rhs := x0
  defined_head := by decide
  no_extra_variables := by
    intro x hx
    simp only [x0, Term.vars, List.mem_singleton] at hx
    subst hx
    show 0 ∈ (List.ofFn fun (i : Fin 2) ↦ Term.vars (x0 : Term sig)).flatten
    simp [x0, Term.vars, List.ofFn_succ]

def P : Problem sig := ⟨[rule], []⟩

theorem mem_symbols_arg {g : Symbol sig} {ts : Fin (sig.arity g) → Term sig} (i : Fin (sig.arity g))
    {h : Symbol sig} (hg : h ∈ (ts i).symbols) : h ∈ (Term.app g ts).symbols := by
  simp only [Term.symbols]
  exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, hg⟩)

theorem rewrites_f {t u : Term sig} (h : Rewrites P.rules t u) : f ∈ t.symbols := by
  induction h with
  | root r hr τ =>
    simp only [P, Problem.rules, List.append_nil, List.mem_singleton] at hr
    subst hr
    simp [Rule.lhs, Term.subst, Term.symbols, rule]
  | arg g ts us i _ _ ih => exact mem_symbols_arg i ih

theorem normal_of {t : Term sig} (ht : f ∉ t.symbols) : Normal P.rules t :=
  fun ⟨_, hu⟩ ↦ ht (rewrites_f hu)

theorem constructorLike_iff (g : Symbol sig) : ConstructorLike P g ↔ g = c := by
  constructor
  · rintro (h | ⟨r, hr, i, hi⟩)
    · simpa using h
    · simp only [P, Problem.rules, List.append_nil, List.mem_singleton] at hr
      subst hr
      simp [rule, x0, Term.symbols] at hi
  · rintro rfl; exact Or.inl (by simp)

noncomputable def e₀ : Annotation := Finsupp.single 0 1

noncomputable def fdecl : Declaration (sig.arity f) := ⟨fun _ ↦ e₀, 1, e₀ + e₀⟩
noncomputable def ddecl : Declaration (sig.arity d) := ⟨fun _ ↦ 0, 0, e₀⟩

noncomputable def F : AnnotatedSignature P where
  declarations g a := (g = c ∧ a = ⟨fun _ ↦ 0, a.output 0, a.output⟩) ∨
    (g = d ∧ HEq a ddecl) ∨ (g = f ∧ HEq a fdecl)
  nonempty g := by
    by_cases hc : g = c
    · exact ⟨⟨fun _ ↦ 0, (0 : Annotation) 0, 0⟩, Or.inl ⟨hc, rfl⟩⟩
    by_cases hd : g = d
    · subst hd; exact ⟨ddecl, Or.inr (Or.inl ⟨rfl, HEq.rfl⟩)⟩
    have hf : g = f := by revert hc hd; revert g; decide
    subst hf; exact ⟨fdecl, Or.inr (Or.inr ⟨rfl, HEq.rfl⟩)⟩
  input _ _ _ := 0
  cost _ q := q 0
  constructor_declaration g hg q := by
    rw [constructorLike_iff] at hg
    subst hg
    exact Or.inl ⟨rfl, rfl⟩
  constructor_unique g hg a ha := by
    rw [constructorLike_iff] at hg
    subst hg
    rcases ha with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact ⟨rfl, rfl⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  input_add _ _ _ _ _ := by simp
  cost_add _ _ p q := Finsupp.add_apply p q 0
  input_scale _ _ _ _ _ := by simp [Annotation.scale]
  cost_scale _ _ a q := by simp [Annotation.scale]

def dT : Term sig := Term.app d (fun i ↦ Fin.elim0 i)

def σ : Substitution sig := ⟨{0, 1}, fun _ ↦ dT⟩

def xf : Fin (sig.arity f) → ℕ := fun i ↦ (i : ℕ)
def xd : Fin (sig.arity d) → ℕ := fun i ↦ Fin.elim0 i

theorem xf_inj : Function.Injective xf := fun _ _ h ↦ Fin.ext h
theorem xd_inj : Function.Injective xd := fun i _ _ ↦ Fin.elim0 i

def t : Term sig := Term.app f fun i ↦ Term.var (xf i)

noncomputable def Γ : Context := flatContext xf fdecl.inputs

theorem hΓ : Γ = [(0, e₀), (1, e₀)] := rfl

theorem typing_cast {m : Mode} {Δ Δ' : Context} {k k' : ℚ≥0} {u u' : Term sig} {p : Annotation}
    (h : Typing F m Δ k u p) (h1 : Δ = Δ') (h2 : k = k') (h3 : u = u') : Typing F m Δ' k' u' p := by
  subst h1 h2 h3; exact h

theorem typ_d : Typing F .full [] 0 dT e₀ := by
  have := Typing.app (F := F) .full d ddecl (Or.inr (Or.inl ⟨rfl, HEq.rfl⟩)) xd xd_inj
  refine typing_cast this ?_ rfl ?_
  · simp [flatContext]
  · simp only [dT]; congr 1; funext i; exact Fin.elim0 i

theorem d_not_cl : ¬ ConstructorLike P d := by
  rw [constructorLike_iff]; decide

theorem pot_zero (p : Annotation) : potential F dT p = 0 := by
  rw [potential, if_neg]
  rintro ⟨_, h⟩
  exact d_not_cl (h d List.mem_cons_self)

theorem σ_apply {x : ℕ} (hx : x = 0 ∨ x = 1) : σ.apply x = dT := by
  rcases hx with rfl | rfl <;> simp [Substitution.apply, σ]

theorem f_not_dT : f ∉ dT.symbols := by
  simp [dT, Term.symbols, show f ≠ d by decide]

theorem deriv : Derivation P (t.subst σ.apply) 1 dT := by
  have hs : RestrictedStep P.rules P.strict (rule.lhs.subst fun _ ↦ dT) (rule.rhs.subst fun _ ↦ dT) :=
    RestrictedStep.root rule (by simp [P]) _ (fun _ ↦ normal_of f_not_dT)
  have h1 : t.subst σ.apply = rule.lhs.subst fun _ ↦ dT := by
    simp only [t, Term.subst, Rule.lhs, rule, x0]
    congr 1; funext i
    apply σ_apply
    have := i.isLt
    change (i : ℕ) < 2 at this
    simp only [xf]; omega
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
  have haf : a = fdecl := by
    rcases ha with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact eq_of_heq h
  subst haf
  refine ⟨[(0, e₀ + e₀)], 0, 0, ?_, by simp [fdecl], Typing.var .full 0 _⟩
  refine ⟨fun i ↦ Term.var (i : ℕ), fun _ ↦ 0, fun i ↦ [((i : ℕ), e₀)], fun _ ↦ 0,
    ?_, ?_, ?_, ?_, ?_⟩
  · show ((List.ofFn fun (i : Fin 2) ↦ (Term.var (sig := sig) (i : ℕ)).vars).flatten).Nodup
    simp [Term.vars, List.ofFn_succ]
  · intro i; rfl
  · intro i
    exact ⟨by simp [Context.keys, Term.vars], Typing.var .footprint _ _⟩
  · show [(0, e₀ + e₀)] = Context.renameMerge
      (List.ofFn fun (i : Fin 2) ↦ [((i : ℕ), e₀)]).flatten (fun _ ↦ 0)
    simp [Context.renameMerge, List.ofFn_succ]
    rw [show List.eraseDups [0, 0] = [0] from rfl]
    simp
  · simp

theorem resource_bounded : ResourceBounded F := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [P, List.mem_singleton] at hr
    subst hr
    exact rule_bounded
  · intro r hr; simp [P] at hr

/-! ### Non-typability of `d` at `e₀ + e₀` -/

theorem rename_eq_dT {u : Term sig} {ρ : ℕ → ℕ} (h : u.rename ρ = dT) : u = dT := by
  cases u with
  | var w => simp [Term.rename, Term.subst, dT] at h
  | app g ts =>
    simp only [Term.rename, Term.subst, dT] at h
    obtain ⟨rfl, -⟩ := Term.app.inj h
    simp only [dT]; congr 1; funext i; exact Fin.elim0 i

theorem dT_bound {m : Mode} {Δ : Context} {j : ℚ≥0} {u : Term sig} {p : Annotation}
    (h : Typing F m Δ j u p) : u = dT → p ≤ e₀ := by
  induction h with
  | app mode g a ha xs hx =>
    intro hu
    simp only [dT] at hu
    obtain ⟨rfl, -⟩ := Term.app.inj hu
    rcases ha with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · rw [eq_of_heq h]; exact le_rfl
    · exact absurd h (by decide)
  | var => intro hu; simp [dT] at hu
  | comp g ts xs ps Γs ks k₀ q hx hfresh hdisj hlin hhead hargs ihh iha =>
    intro hu
    simp only [dT] at hu
    obtain ⟨rfl, -⟩ := Term.app.inj hu
    apply ihh
    simp only [dT]; congr 1; funext i; exact Fin.elim0 i
  | share Γ x y z p₁ p₂ p q u k hshare hxy hxz hyz hx hy hz h ih =>
    intro hu; exact ih (rename_eq_dT hu)
  | perm _ _ ih => exact ih
  | w1 _ _ ih => exact ih
  | w2 _ _ _ _ _ _ _ _ _ ih => exact ih
  | w3 _ hq ih => intro hu; exact hq.trans (ih hu)
  | w4 _ _ _ _ _ _ _ _ ih => exact ih

theorem not_typ : ¬ ∃ j, Typing F .full [] j dT (e₀ + e₀) := by
  rintro ⟨j, hj⟩
  have h := Finsupp.le_def.1 (dT_bound hj rfl) 0
  simp [e₀] at h

theorem main :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t v : Term sig) (q : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ p j, Typing F .full Γ j (.var x) p →
        Typing F .full Γ j (σ.apply x) p) ∧
      Typing F .full Γ k t q ∧ Derivation P (t.subst σ.apply) 1 v ∧ Normal P.rules v ∧
      ((1 : ℚ≥0) + potential F v q = contextPotential F σ Γ + k) ∧
      ¬ ∃ j, Typing F .full [] j v q := by
  refine ⟨sig, P, F, Γ, σ, t, dT, e₀ + e₀, 1, resource_bounded, ?_, ?_, ?_, ?_, deriv,
    normal_of f_not_dT, ?_, not_typ⟩
  · intro x _
    exact ⟨by simp [σ, dT, Term.Ground, Term.vars], normal_of f_not_dT⟩
  · refine ⟨by simp [hΓ, Context.Valid, Context.keys], ?_⟩
    intro x q hx
    rw [hΓ] at hx
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hx
    have hx' : x = 0 ∨ x = 1 := hx.imp And.left And.left
    have hq : q = e₀ := by rcases hx with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
    subst hq
    refine ⟨by simpa [σ] using hx', 0, ?_⟩
    rw [σ_apply hx']; exact typ_d
  · intro x hx p j hj
    have hx' : x = 0 ∨ x = 1 := by simpa [σ] using hx
    have hp := lookup_bound hj x rfl
    have hl : Γ.lookup x = e₀ := by
      rw [hΓ]; rcases hx' with rfl | rfl <;> simp [Context.lookup]
    rw [hl] at hp
    rw [σ_apply hx']
    have h1 : Typing F .full [] j dT p := Typing.w1 (Typing.w3 typ_d hp) zero_le
    have h2 := Typing.w4 [] 0 e₀ p j dT (by simp [Context.keys]) h1
    have h3 := Typing.w4 _ 1 e₀ p j dT (by simp [Context.keys]) h2
    exact typing_cast h3 (by rw [hΓ]; rfl) rfl rfl
  · exact Typing.app .full f fdecl (Or.inr (Or.inr ⟨rfl, HEq.rfl⟩)) xf xf_inj
  · rw [pot_zero]
    have : contextPotential F σ Γ = 0 := by
      rw [hΓ]
      simp only [contextPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, σ_apply (Or.inl rfl), σ_apply (Or.inr rfl), pot_zero]
    rw [this]; simp

end MSEvalTyp

open MoserSchneckenreither in
theorem solution :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t v : Term sig) (q : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ p j, Typing F .full Γ j (.var x) p →
        Typing F .full Γ j (σ.apply x) p) ∧
      Typing F .full Γ k t q ∧ Derivation P (t.subst σ.apply) 1 v ∧ Normal P.rules v ∧
      ((1 : ℚ≥0) + potential F v q = contextPotential F σ Γ + k) ∧
      ¬ ∃ j, Typing F .full [] j v q :=
  MSEvalTyp.main

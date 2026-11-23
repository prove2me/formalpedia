-- Prove2me | solution 1 for MoserSchneckenreither.fixed_residual_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T05:31:32.241882+00:00
-- url     : https://prove2.me/submissions/57601dfd-2dbc-4705-9b09-f347a99f3e5c

import Definitions.Def_MoserSchneckenreither_Typing
import Definitions.Def_MoserSchneckenreither_RootPotential
import Mathlib.Algebra.Order.Ring.NNRat

namespace MSFixedRes
open MoserSchneckenreither

/-- 0 = constructor constant `c`; 1 = defined constant `d`; 2 = defined binary `g`;
3 = defined unary `h`. -/
def ar : Fin 4 → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 1

abbrev sig : Signature where
  count := 4
  arity := ar
  constructors := {0}
  constructors_nonempty := ⟨0, Finset.mem_singleton_self 0⟩
  has_constant := ⟨0, rfl⟩

abbrev sc : Symbol sig := (0 : Fin 4)
abbrev sd : Symbol sig := (1 : Fin 4)
abbrev sg : Symbol sig := (2 : Fin 4)
abbrev sh : Symbol sig := (3 : Fin 4)

@[simp] theorem ar_c : ar sc = 0 := rfl
@[simp] theorem ar_d : ar sd = 0 := rfl

def h0 : Fin (sig.arity sh) := ⟨0, by decide⟩
def g0 : Fin (sig.arity sg) := ⟨0, by decide⟩
def g1 : Fin (sig.arity sg) := ⟨1, by decide⟩

theorem fin_h_eq (i : Fin (sig.arity sh)) : i = h0 :=
  Fin.ext (by have := i.isLt; change i.val < 1 at this; show i.val = 0; omega)

theorem ofFn_h {α : Type*} (v : Fin (sig.arity sh) → α) : List.ofFn v = [v h0] := rfl
theorem ofFn_g {α : Type*} (v : Fin (sig.arity sg) → α) : List.ofFn v = [v g0, v g1] := rfl

def rule : Rule sig where
  head := sg
  args := fun _ ↦ Term.var 0
  rhs := Term.app sh fun _ ↦ Term.var 0
  defined_head := by decide
  no_extra_variables := by
    intro x hx
    simp only [Term.vars, ofFn_h, ofFn_g, List.flatten] at hx ⊢
    simpa using hx

def P : Problem sig := ⟨[rule], []⟩

theorem mem_symbols_arg {f : Symbol sig} {ts : Fin (sig.arity f) → Term sig} (i : Fin (sig.arity f))
    {s : Symbol sig} (hg : s ∈ (ts i).symbols) : s ∈ (Term.app f ts).symbols := by
  simp only [Term.symbols]
  exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, hg⟩)

theorem rewrites_g {t u : Term sig} (hr : Rewrites P.rules t u) : sg ∈ t.symbols := by
  induction hr with
  | root r hr τ =>
    simp only [P, Problem.rules, List.append_nil, List.mem_singleton] at hr
    subst hr
    simp [Rule.lhs, Term.subst, Term.symbols, rule]
  | arg f ts us i _ _ ih => exact mem_symbols_arg i ih

theorem normal_of {t : Term sig} (ht : sg ∉ t.symbols) : Normal P.rules t :=
  fun ⟨_, hu⟩ ↦ ht (rewrites_g hu)

theorem constructorLike_iff (f : Symbol sig) : ConstructorLike P f ↔ f = sc := by
  constructor
  · rintro (hf | ⟨r, hr, i, hi⟩)
    · simpa using hf
    · simp only [P, Problem.rules, List.append_nil, List.mem_singleton] at hr
      subst hr
      simp [rule, Term.symbols] at hi
  · rintro rfl; exact Or.inl (by simp)

noncomputable def e₀ : Annotation := Finsupp.single 0 1

noncomputable def ddecl : Declaration (sig.arity sd) := ⟨fun _ ↦ 0, 0, e₀⟩
noncomputable def gdecl : Declaration (sig.arity sg) := ⟨fun _ ↦ e₀, 1, 0⟩
noncomputable def hdecl : Declaration (sig.arity sh) := ⟨fun _ ↦ e₀ + e₀, 0, 0⟩

theorem sym_cases (f : Symbol sig) : f = sc ∨ f = sd ∨ f = sg ∨ f = sh := by
  revert f; decide

noncomputable def F : AnnotatedSignature P where
  declarations f a := (f = sd ∧ HEq a ddecl) ∨ (f = sg ∧ HEq a gdecl) ∨
    (f = sh ∧ HEq a hdecl) ∨ (f = sc ∧ a = ⟨fun _ ↦ 0, a.output 0, a.output⟩)
  nonempty f := by
    rcases sym_cases f with rfl | rfl | rfl | rfl
    · exact ⟨⟨fun _ ↦ 0, (0 : Annotation) 0, 0⟩, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · exact ⟨ddecl, Or.inl ⟨rfl, HEq.rfl⟩⟩
    · exact ⟨gdecl, Or.inr (Or.inl ⟨rfl, HEq.rfl⟩)⟩
    · exact ⟨hdecl, Or.inr (Or.inr (Or.inl ⟨rfl, HEq.rfl⟩))⟩
  input _ _ _ := 0
  cost _ q := q 0
  constructor_declaration f hf q := by
    rw [constructorLike_iff] at hf
    subst hf
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  constructor_unique f hf a ha := by
    rw [constructorLike_iff] at hf
    subst hf
    rcases ha with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rw [h]; exact ⟨rfl, rfl⟩
  input_add _ _ _ _ _ := by simp
  cost_add _ _ p q := Finsupp.add_apply p q 0
  input_scale _ _ _ _ _ := by simp [Annotation.scale]
  cost_scale _ _ a q := by simp [Annotation.scale]

def dT : Term sig := Term.app sd (fun i ↦ Fin.elim0 i)
def hd : Term sig := Term.app sh fun _ ↦ dT
def hv (x : ℕ) : Term sig := Term.app sh fun _ ↦ Term.var x

def σ : Substitution sig := ⟨{0, 1}, fun _ ↦ dT⟩
def τ : Substitution sig := ⟨∅, fun _ ↦ dT⟩

def xg : Fin (sig.arity sg) → ℕ := fun i ↦ i.val
def xd : Fin (sig.arity sd) → ℕ := fun i ↦ Fin.elim0 i
def xh : Fin (sig.arity sh) → ℕ := fun _ ↦ 0

theorem xg_inj : Function.Injective xg := Fin.val_injective
theorem xd_inj : Function.Injective xd := fun i _ _ ↦ Fin.elim0 i
theorem xh_inj : Function.Injective xh := fun i j _ ↦ (fin_h_eq i).trans (fin_h_eq j).symm

def t : Term sig := Term.app sg fun i ↦ Term.var (xg i)

noncomputable def Γ : Context := flatContext xg gdecl.inputs

theorem hΓ : Γ = [(0, e₀), (1, e₀)] := rfl

theorem typing_cast {m : Mode} {Δ Δ' : Context} {k k' : ℚ≥0} {u u' : Term sig} {p : Annotation}
    (h : Typing F m Δ k u p) (h1 : Δ = Δ') (h2 : k = k') (h3 : u = u') : Typing F m Δ' k' u' p := by
  subst h1 h2 h3; exact h

theorem typ_d : Typing F .full [] 0 dT e₀ := by
  have := Typing.app (F := F) .full sd ddecl (Or.inl ⟨rfl, HEq.rfl⟩) xd xd_inj
  refine typing_cast this ?_ rfl ?_
  · simp [flatContext]
  · simp only [dT]; congr 1; funext i; exact Fin.elim0 i

theorem σ_apply {x : ℕ} (hx : x ∈ σ.domain) : σ.apply x = dT := by
  rw [Substitution.apply, if_pos hx]; rfl

theorem xg_mem (i : Fin (sig.arity sg)) : xg i ∈ σ.domain := by
  have := i.isLt; change i.val < 2 at this
  simp only [σ, xg, Finset.mem_insert, Finset.mem_singleton]; omega

theorem g_not_dT : sg ∉ dT.symbols := by
  simp [dT, Term.symbols]; decide

theorem dT_subst (f : ℕ → Term sig) : dT.subst f = dT := by
  simp only [dT, Term.subst]; congr 1; funext i; exact Fin.elim0 i

theorem hd_subst (f : ℕ → Term sig) : hd.subst f = hd := by
  simp only [hd, Term.subst, dT_subst]

theorem relstep : RelativeStep P (t.subst σ.apply) (hd.subst τ.apply) := by
  have hs : RestrictedStep P.rules P.strict (rule.lhs.subst fun _ ↦ dT)
      (rule.rhs.subst fun _ ↦ dT) :=
    RestrictedStep.root rule (by simp [P]) _ (fun _ ↦ normal_of g_not_dT)
  have h1 : t.subst σ.apply = rule.lhs.subst fun _ ↦ dT := by
    simp only [t, Term.subst, Rule.lhs, rule]
    congr 1; funext i; exact σ_apply (xg_mem i)
  have h2 : rule.rhs.subst (fun _ ↦ dT) = hd.subst τ.apply := by
    rw [hd_subst]; rfl
  rw [h1, ← h2]
  exact ⟨_, _, Relation.ReflTransGen.refl, hs, Relation.ReflTransGen.refl⟩

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

theorem share_lookup (Δ : Context) (x y z : ℕ) (p₁ p₂ A : Annotation) (w : ℕ)
    (hxy : x ≠ y) (hx : x ∉ Δ.keys) (hy : y ∉ Δ.keys) (hz : z ∉ Δ.keys)
    (hA : A ≤ (Δ ++ [(x, p₁), (y, p₂)]).lookup w) :
    A ≤ (Δ ++ [(z, p₁ + p₂)]).lookup (if w = x ∨ w = y then z else w) := by
  have hΓx := lookup_not_mem Δ x hx
  have hΓy := lookup_not_mem Δ y hy
  have hΓz := lookup_not_mem Δ z hz
  rw [lookup_append] at hA ⊢
  rw [show ([(x, p₁), (y, p₂)] : Context) = [(x, p₁)] ++ [(y, p₂)] from rfl,
    lookup_append, lookup_single, lookup_single] at hA
  rw [lookup_single]
  by_cases hwx : w = x
  · simp [hwx, hΓx, hΓz, hxy, hxy.symm] at hA ⊢
    exact hA.trans le_self_add
  · by_cases hwy : w = y
    · simp [hwy, hΓy, hΓz, hxy, hxy.symm] at hA ⊢
      exact hA.trans le_add_self
    · simp [hwx, hwy, Ne.symm hwx, Ne.symm hwy] at hA ⊢
      exact hA.trans le_self_add

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
    unfold Shares at hshare
    subst hshare hw
    exact share_lookup Γ x y z p₁ p₂ q w hxy hx hy hz (ih w rfl)
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

/-! ### Inversion invariants -/

theorem flat_h (xs : Fin (sig.arity sh) → ℕ) (ps : Fin (sig.arity sh) → Annotation) :
    flatContext xs ps = [(xs h0, ps h0)] := rfl

theorem rename_dT {u : Term sig} {ρ : ℕ → ℕ} (h : u.rename ρ = dT) : u = dT := by
  cases u with
  | var w => simp [Term.rename, Term.subst, dT] at h
  | app f ts =>
    simp only [Term.rename, Term.subst, dT, Term.app.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [dT]; congr 1; funext i; exact Fin.elim0 i

theorem rename_hd {u : Term sig} {ρ : ℕ → ℕ} (h : u.rename ρ = hd) : u = hd := by
  cases u with
  | var w => simp [Term.rename, Term.subst, hd] at h
  | app f ts =>
    simp only [Term.rename, Term.subst, hd, Term.app.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have h' := congrFun (eq_of_heq h)
    simp only [hd]; congr 1; funext i
    exact rename_dT (h' i)

theorem rename_hv {u : Term sig} {ρ : ℕ → ℕ} {x : ℕ} (h : u.rename ρ = hv x) :
    ∃ w, u = hv w ∧ ρ w = x := by
  cases u with
  | var w => simp [Term.rename, Term.subst, hv] at h
  | app f ts =>
    simp only [Term.rename, Term.subst, hv, Term.app.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have h' := congrFun (eq_of_heq h)
    obtain ⟨w, hw, hρ⟩ := rename_var (h' h0)
    refine ⟨w, ?_, hρ⟩
    simp only [hv]; congr 1; funext i; rw [fin_h_eq i, hw]

/-- (I1) Every typing of `d` has annotation at most `e₀`. -/
theorem inv_d {m : Mode} {Δ : Context} {j : ℚ≥0} {u : Term sig} {p : Annotation}
    (h : Typing F m Δ j u p) : u = dT → p ≤ e₀ := by
  induction h with
  | app mode f a ha xs hx =>
    intro hu
    simp only [dT, Term.app.injEq] at hu
    obtain ⟨rfl, -⟩ := hu
    rcases ha with ⟨_, ha⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩
    · rw [eq_of_heq ha]; exact le_rfl
    · exact absurd hf (by decide)
    · exact absurd hf (by decide)
    · exact absurd hf (by decide)
  | var => intro hu; simp [dT] at hu
  | comp f ts xs ps Γs ks k₀ q hx hfresh hdisj hlin hhead hargs ihh iha =>
    intro hu
    simp only [dT, Term.app.injEq] at hu
    obtain ⟨rfl, -⟩ := hu
    exact ihh (by simp only [dT]; congr 1; funext i; exact Fin.elim0 i)
  | share Γ x y z p₁ p₂ p q u k hshare hxy hxz hyz hx hy hz h ih =>
    intro hu; exact ih (rename_dT hu)
  | perm _ _ ih => exact ih
  | w1 _ _ ih => exact ih
  | w2 _ _ _ _ _ _ _ _ _ ih => exact ih
  | w3 _ hq ih => intro hu; exact hq.trans (ih hu)
  | w4 _ _ _ _ _ _ _ _ ih => exact ih

/-- (I3) A typing of `h(x)` needs at least `e₀ + e₀` on `x`. -/
theorem inv_hv {m : Mode} {Δ : Context} {j : ℚ≥0} {u : Term sig} {p : Annotation}
    (h : Typing F m Δ j u p) : ∀ x, u = hv x → e₀ + e₀ ≤ Δ.lookup x := by
  induction h with
  | app mode f a ha xs hx =>
    intro x hu
    simp only [hv, Term.app.injEq] at hu
    obtain ⟨rfl, hu⟩ := hu
    have hxs : xs h0 = x := by
      have := congrFun (eq_of_heq hu) h0; simpa using this
    rcases ha with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨_, ha⟩ | ⟨hf, _⟩
    · exact absurd hf (by decide)
    · exact absurd hf (by decide)
    · rw [eq_of_heq ha, flat_h, lookup_single, if_pos hxs]; exact le_rfl
    · exact absurd hf (by decide)
  | var => intro x hu; simp [hv] at hu
  | comp f ts xs ps Γs ks k₀ q hx hfresh hdisj hlin hhead hargs ihh iha =>
    intro x hu
    simp only [hv, Term.app.injEq] at hu
    obtain ⟨rfl, hu⟩ := hu
    have hts := eq_of_heq hu
    have h1 := ihh (xs h0) (by simp only [hv]; congr 1; funext i; rw [fin_h_eq i])
    rw [flat_h, lookup_single, if_pos rfl] at h1
    have h2 := lookup_bound (hargs h0) x (by rw [hts])
    rw [ofFn_h]
    simpa using h1.trans h2
  | share Γ x y z p₁ p₂ p q u k hshare hxy hxz hyz hx hy hz h ih =>
    intro x' hu
    obtain ⟨w, rfl, hw⟩ := rename_hv hu
    unfold Shares at hshare
    subst hshare hw
    exact share_lookup Γ x y z p₁ p₂ _ w hxy hx hy hz (ih w rfl)
  | perm hperm h ih => intro y hy; rw [← lookup_perm hperm]; exact ih y hy
  | w1 h hk ih => exact ih
  | w2 Γ x p r q k u h hr ih =>
    intro y hy
    refine (ih y hy).trans ?_
    rw [lookup_append, lookup_append, lookup_single, lookup_single]
    split_ifs
    · gcongr
    · exact le_rfl
  | w3 h hq ih => exact ih
  | w4 Γ x p q k u hx h ih =>
    intro y hy
    rw [lookup_append]
    exact (ih y hy).trans le_self_add

/-- (I4) `h(d)` has no typing at all. -/
theorem inv_hd {m : Mode} {Δ : Context} {j : ℚ≥0} {u : Term sig} {p : Annotation}
    (h : Typing F m Δ j u p) : u = hd → False := by
  induction h with
  | app mode f a ha xs hx =>
    intro hu
    simp only [hd, Term.app.injEq] at hu
    obtain ⟨rfl, hu⟩ := hu
    have := congrFun (eq_of_heq hu) h0
    simp [dT] at this
  | var => intro hu; simp [hd] at hu
  | comp f ts xs ps Γs ks k₀ q hx hfresh hdisj hlin hhead hargs ihh iha =>
    intro hu
    simp only [hd, Term.app.injEq] at hu
    obtain ⟨rfl, hu⟩ := hu
    have hts := eq_of_heq hu
    have h1 := inv_hv hhead (xs h0) (by simp only [hv]; congr 1; funext i; rw [fin_h_eq i])
    rw [flat_h, lookup_single, if_pos rfl] at h1
    have h2 := inv_d (hargs h0) (by rw [hts])
    have h3 := Finsupp.le_def.1 (h1.trans h2) 0
    simp [e₀] at h3
  | share Γ x y z p₁ p₂ p q u k hshare hxy hxz hyz hx hy hz h ih =>
    intro hu; exact ih (rename_hd hu)
  | perm _ _ ih => exact ih
  | w1 _ _ ih => exact ih
  | w2 _ _ _ _ _ _ _ _ _ ih => exact ih
  | w3 _ _ ih => exact ih
  | w4 _ _ _ _ _ _ _ _ ih => exact ih

/-! ### Resource boundedness -/

theorem rule_bounded : RuleBounded F rule 1 := by
  intro a ha
  have hag : a = gdecl := by
    rcases ha with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact eq_of_heq h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  subst hag
  refine ⟨[(0, e₀ + e₀)], 0, 0, ?_, by simp [gdecl], ?_⟩
  · refine ⟨fun i ↦ Term.var (xg i), fun _ ↦ 0, fun i ↦ [(xg i, e₀)], fun _ ↦ 0,
      ?_, ?_, ?_, ?_, ?_⟩
    · show ([0, 1] : List ℕ).Nodup
      decide
    · intro i; rfl
    · intro i
      exact ⟨by simp [Context.keys, Term.vars], Typing.var .footprint (xg i) e₀⟩
    · show [(0, e₀ + e₀)] = Context.renameMerge [(0, e₀), (1, e₀)] (fun _ ↦ 0)
      simp only [Context.renameMerge, List.map_cons, List.map_nil]
      rw [show ([0, 0] : List ℕ).eraseDups = [0] from rfl]
      simp
    · simp
  · exact typing_cast (Typing.app .full sh hdecl (Or.inr (Or.inr (Or.inl ⟨rfl, HEq.rfl⟩)))
      xh xh_inj) rfl rfl rfl

theorem resource_bounded : ResourceBounded F := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [P, List.mem_singleton] at hr
    subst hr
    exact rule_bounded
  · intro r hr; simp [P] at hr

theorem main :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ τ : Substitution sig) (t u : Term sig) (p : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ τ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ q, (∃ j, Typing F .full Γ j (.var x) q) →
        ∃ j, Typing F .full Γ j (σ.apply x) q) ∧
      Typing F .full Γ k t p ∧ RelativeStep P (t.subst σ.apply) (u.subst τ.apply) ∧
      ¬ ∃ (Δ : Context) (ℓ : ℚ≥0) (q : Annotation), Typing F .full Δ ℓ u q ∧
        rootContextPotential F τ.apply Δ + ℓ + 1 ≤ rootContextPotential F σ.apply Γ + k := by
  refine ⟨sig, P, F, Γ, σ, τ, t, hd, 0, 1, resource_bounded, ?_, ?_, ?_, ?_, ?_, relstep, ?_⟩
  · intro x _
    exact ⟨by simp [σ, dT, Term.Ground, Term.vars], normal_of g_not_dT⟩
  · intro x hx; simp [τ] at hx
  · refine ⟨by simp [hΓ, Context.Valid, Context.keys], ?_⟩
    intro x q hx
    rw [hΓ] at hx
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hx
    have hx' : x ∈ σ.domain := by rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [σ]
    have hq : q = e₀ := by rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    subst hq
    exact ⟨hx', 0, by rw [σ_apply hx']; exact typ_d⟩
  · intro x hx q ⟨j, hj⟩
    have hq := lookup_bound hj x rfl
    have hl : Γ.lookup x = e₀ := by
      rw [hΓ]
      simp only [σ, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [Context.lookup]
    rw [hl] at hq
    exact ⟨0, typing_cast (Typing.w4 [(0, e₀)] 1 e₀ q 0 dT (by simp [Context.keys])
      (Typing.w4 [] 0 e₀ q 0 dT (by simp [Context.keys]) (Typing.w3 typ_d hq)))
      (by rw [hΓ]; rfl) rfl (σ_apply hx).symm⟩
  · exact Typing.app .full sg gdecl (Or.inr (Or.inl ⟨rfl, HEq.rfl⟩)) xg xg_inj
  · rintro ⟨Δ, ℓ, q, hT, -⟩
    exact inv_hd hT rfl

end MSFixedRes

open MoserSchneckenreither in
theorem solution :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ τ : Substitution sig) (t u : Term sig) (p : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ τ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ q, (∃ j, Typing F .full Γ j (.var x) q) →
        ∃ j, Typing F .full Γ j (σ.apply x) q) ∧
      Typing F .full Γ k t p ∧ RelativeStep P (t.subst σ.apply) (u.subst τ.apply) ∧
      ¬ ∃ (Δ : Context) (ℓ : ℚ≥0) (q : Annotation), Typing F .full Δ ℓ u q ∧
        rootContextPotential F τ.apply Δ + ℓ + 1 ≤ rootContextPotential F σ.apply Γ + k :=
  MSFixedRes.main

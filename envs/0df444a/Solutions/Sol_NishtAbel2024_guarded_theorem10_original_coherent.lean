-- Prove2me | solution 1 for NishtAbel2024.guarded_theorem10_original_coherent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:59:03.411917+00:00
-- url     : https://prove2.me/submissions/24ed7495-efd6-42e3-8d21-8a914d780593

import Definitions.Def_NishtAbel2024_ComparisonCoherenceAux

namespace NishtAbel2024

/-! Purely syntactic properties of the original size-name collector. These do not
establish capture avoidance or semantic substitution soundness. -/

mutual

theorem allSizeVars_subst_atom (Y X : TyVar) (F : TypeExpr) :
    (TypeExpr.substTyVar Y (.atom (.var X)) F).allSizeVars = F.allSizeVars := by
  cases F with
  | atom a =>
    cases a with
    | var z =>
      simp only [TypeExpr.substTyVar]
      split <;> rfl
    | size a => rfl
    | unit => rfl
    | prod => rfl
    | arr => rfl
    | all k => rfl
    | ex k => rfl
  | lam z k body =>
    simp only [TypeExpr.substTyVar]
    split
    · rfl
    · exact allSizeVars_subst_atom Y X body
  | app f g =>
    simp only [TypeExpr.substTyVar, TypeExpr.allSizeVars]
    rw [allSizeVars_subst_atom Y X f, allSizeVars_subst_atom Y X g]
  | mu a branches =>
    simp only [TypeExpr.substTyVar, TypeExpr.allSizeVars]
    rw [allSizeVarsBranches_subst_atom Y X branches]
  | nu a branches =>
    simp only [TypeExpr.substTyVar, TypeExpr.allSizeVars]
    rw [allSizeVarsBranches_subst_atom Y X branches]
termination_by sizeOf F

theorem allSizeVarsBranches_subst_atom (Y X : TyVar) (branches : List (Nat × TypeExpr)) :
    allSizeVarsBranches (TypeExpr.substTyVarBranches Y (.atom (.var X)) branches) =
      allSizeVarsBranches branches := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
    rcases branch with ⟨name, body⟩
    simp only [TypeExpr.substTyVarBranches, allSizeVarsBranches]
    rw [allSizeVars_subst_atom Y X body, allSizeVarsBranches_subst_atom Y X rest]
termination_by sizeOf branches

end

/-- Applying a type expression to a type-variable atom does not introduce a
name into the original syntactic size-variable collector. -/
theorem normApp_var_preserves_sizeVars (F : TypeExpr) (X : TyVar) :
    (F.normApp (.atom (.var X))).allSizeVars = F.allSizeVars := by
  cases F with
  | atom K => simp [TypeExpr.normApp, TypeExpr.allSizeVars]
  | lam Y κ body => exact allSizeVars_subst_atom Y X body
  | app f g => simp [TypeExpr.normApp, TypeExpr.allSizeVars]
  | mu a S => simp [TypeExpr.normApp, TypeExpr.allSizeVars]
  | nu a R => simp [TypeExpr.normApp, TypeExpr.allSizeVars]

theorem size_absent_normApp_var (i : SizeVar) (F : TypeExpr) (X : TyVar)
    (h : ¬ SizeOccursIn i F) : ¬ SizeOccursIn i (F.normApp (.atom (.var X))) := by
  simpa [SizeOccursIn, normApp_var_preserves_sizeVars] using h




/-- A compared size index can only be infinity plus an offset or an unshifted
    variable, regardless of the larger input type grammar. -/
theorem lookup_index_shape (Φ : FlexVars) (fallback p : Polarity) (a : SizeExp)
    (h : Φ.lookupSizePol fallback a = some p) :
    (∃ n, a = .inf n) ∨ (∃ i, a = .var i 0) := by
  cases a with
  | inf n => exact Or.inl ⟨n, rfl⟩
  | meet m =>
    rcases m with ⟨⟨i, n⟩, tail⟩
    cases n <;> cases tail <;> simp_all [FlexVars.lookupSizePol, SizeExp.var, SizeMin.single]

/-- If the left index does not mention `i`, every generated constraint that
    mentions `i` must mention it in the right index. -/
theorem ofPol_mentions_right (p : Polarity) (a b : SizeExp) (c : SizeConstraint)
    (i : SizeVar) (ha : i ∉ a.vars) (hc : c ∈ SizeConstraint.ofPol p a b)
    (hm : c.mentions i = true) : i ∈ b.vars := by
  cases p <;> simp_all [SizeConstraint.ofPol, SizeConstraint.mentions]
  rcases hc with rfl | rfl <;> simp_all

theorem lookup_index_mentions (Φ : FlexVars) (fallback p : Polarity) (b : SizeExp)
    (i : SizeVar) (h : Φ.lookupSizePol fallback b = some p) (hm : i ∈ b.vars) :
    b = .var i 0 := by
  rcases lookup_index_shape Φ fallback p b h with ⟨n, rfl⟩ | ⟨j, rfl⟩
  · simp [SizeExp.vars] at hm
  · simp [SizeExp.vars, SizeExp.var, SizeMin.vars, SizeMin.toList, SizeMin.single] at hm
    subst j
    rfl

/-- For a strict sign, joining any other index polarity either preserves that
    sign or suppresses all constraints. -/
theorem infoMax_generated_sign (p r π : Polarity) (a b : SizeExp) (c : SizeConstraint)
    (hp : p = .pos ∨ p = .neg)
    (hc : c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax r p) π) a b) :
    c ∈ SizeConstraint.ofPol (Polarity.comp π p) a b := by
  cases p <;> cases r <;> cases π <;>
    simp_all [Polarity.infoMax, Polarity.comp, SizeConstraint.ofPol]

/-- The fixpoint node's own generated constraint has the desired direction.
    This local fact needs neither the source grammar nor global hygiene. -/
theorem fixpoint_generated_constraint (Φ : FlexVars) (fallback p r π : Polarity)
    (a b : SizeExp) (c : SizeConstraint) (i : SizeVar) (s : Polarity)
    (hb : Φ.lookupSizePol fallback b = some p)
    (hs : Φ.lookupPol i = some s) (hstrict : s = .pos ∨ s = .neg)
    (ha : i ∉ a.vars)
    (hc : c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax r p) π) a b)
    (hm : c.mentions i = true) :
    ∃ a', c ∈ SizeConstraint.ofPol (Polarity.comp π s) a' (.var i 0) := by
  have hbmem := ofPol_mentions_right _ a b c i ha hc hm
  have hbeq := lookup_index_mentions Φ fallback p b i hb hbmem
  subst b
  have hps : p = s := by
    simpa [FlexVars.lookupSizePol, SizeExp.var, SizeMin.single, hs] using hb.symm
  subst p
  exact ⟨a, infoMax_generated_sign s r π a (.var i 0) c hstrict hc⟩

/-- A generated constraint is witnessed by a right-hand occurrence, with the
    constraint direction tracking both comparison and occurrence polarity. -/
def ConstraintTrace (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (C : TypeExpr) (c : SizeConstraint) : Prop :=
  ∃ fk q, SizeOccursFixPol Δ fk i q C ∧
    ∃ a, c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π s) q) a (.var i 0)

def BranchConstraintTrace (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (S : List (Nat × TypeExpr)) (c : SizeConstraint) : Prop :=
  ∃ fk q nm F, (nm, F) ∈ S ∧ SizeOccursFixPol Δ fk i q F ∧
    ∃ a, c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π s) q) a (.var i 0)

theorem polarity_comp_pos (p : Polarity) : Polarity.comp p .pos = p := by
  cases p <;> rfl

theorem branchTrace_mu (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (b : SizeExp) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (h : BranchConstraintTrace Δ π s i S c) : ConstraintTrace Δ π s i (.mu b S) c := by
  rcases h with ⟨fk, q, nm, F, hmem, hocc, a, hconstraint⟩
  exact ⟨fk, q, SizeOccursFixPol.mu_branch hmem hocc, a, hconstraint⟩

theorem branchTrace_nu (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (b : SizeExp) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (h : BranchConstraintTrace Δ π s i S c) : ConstraintTrace Δ π s i (.nu b S) c := by
  rcases h with ⟨fk, q, nm, F, hmem, hocc, a, hconstraint⟩
  exact ⟨fk, q, SizeOccursFixPol.nu_field hmem hocc, a, hconstraint⟩

theorem mu_node_trace (Φ : FlexVars) (Δ : KindingCtx) (p r π : Polarity)
    (a b : SizeExp) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (i : SizeVar) (s : Polarity)
    (hb : Φ.lookupSizePol .pos b = some p)
    (hs : Φ.lookupPol i = some s) (hstrict : s = .pos ∨ s = .neg)
    (ha : i ∉ a.vars)
    (hc : c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax r p) π) a b)
    (hm : c.mentions i = true) : ConstraintTrace Δ π s i (.mu b S) c := by
  have hbmem := ofPol_mentions_right _ a b c i ha hc hm
  have hbeq := lookup_index_mentions Φ .pos p b i hb hbmem
  have hshape := fixpoint_generated_constraint Φ .pos p r π a b c i s hb hs hstrict ha hc hm
  subst b
  obtain ⟨a', hshape⟩ := hshape
  exact ⟨.mu, .pos, SizeOccursFixPol.mu_top, a', by simpa only [polarity_comp_pos] using hshape⟩

theorem nu_node_trace (Φ : FlexVars) (Δ : KindingCtx) (p r π : Polarity)
    (a b : SizeExp) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (i : SizeVar) (s : Polarity)
    (hb : Φ.lookupSizePol .neg b = some p)
    (hs : Φ.lookupPol i = some s) (hstrict : s = .pos ∨ s = .neg)
    (ha : i ∉ a.vars)
    (hc : c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax r p) π) a b)
    (hm : c.mentions i = true) : ConstraintTrace Δ π s i (.nu b S) c := by
  have hbmem := ofPol_mentions_right _ a b c i ha hc hm
  have hbeq := lookup_index_mentions Φ .neg p b i hb hbmem
  have hshape := fixpoint_generated_constraint Φ .neg p r π a b c i s hb hs hstrict ha hc hm
  subst b
  obtain ⟨a', hshape⟩ := hshape
  exact ⟨.nu, .pos, SizeOccursFixPol.nu_top, a', by simpa only [polarity_comp_pos] using hshape⟩

theorem polarity_comp_rearrange (p π s q : Polarity) :
    Polarity.comp (Polarity.comp (Polarity.comp p π) s) q =
      Polarity.comp (Polarity.comp π s) (Polarity.comp p q) := by
  cases p <;> cases π <;> cases s <;> cases q <;> rfl

theorem trace_app_left (Δ : KindingCtx) (π s p : Polarity) (i : SizeVar)
    (F G : TypeExpr) (κ κ' : Kind) (c : SizeConstraint)
    (hkind : KindInfer Δ F (.arr p κ κ')) (h : ConstraintTrace Δ π s i F c) :
    ConstraintTrace Δ π s i (.app F G) c := by
  rcases h with ⟨fk, q, hocc, a, hshape⟩
  exact ⟨fk, q, SizeOccursFixPol.app_left hkind hocc, a, hshape⟩

theorem trace_app_right (Δ : KindingCtx) (π s p : Polarity) (i : SizeVar)
    (F G : TypeExpr) (κ κ' : Kind) (c : SizeConstraint)
    (hkind : KindInfer Δ F (.arr p κ κ'))
    (h : ConstraintTrace (Δ.invScalePol p) (Polarity.comp p π) s i G c) :
    ConstraintTrace Δ π s i (.app F G) c := by
  rcases h with ⟨fk, q, hocc, a, hshape⟩
  refine ⟨fk, Polarity.comp p q, SizeOccursFixPol.app_right hkind hocc, a, ?_⟩
  simpa only [polarity_comp_rearrange] using hshape

theorem trace_lam (Δ ΔX : KindingCtx) (π s : Polarity) (i : SizeVar)
    (F Fapp : TypeExpr) (c : SizeConstraint)
    (transport : ∀ fk q, SizeOccursFixPol ΔX fk i q Fapp → SizeOccursFixPol Δ fk i q F)
    (h : ConstraintTrace ΔX π s i Fapp c) : ConstraintTrace Δ π s i F c := by
  rcases h with ⟨fk, q, hocc, a, hshape⟩
  exact ⟨fk, q, transport fk q hocc, a, hshape⟩

theorem branchTrace_head (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (nm : Nat) (F : TypeExpr) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (h : ConstraintTrace Δ π s i F c) :
    BranchConstraintTrace Δ π s i ((nm, F) :: S) c := by
  rcases h with ⟨fk, q, hocc, a, hshape⟩
  exact ⟨fk, q, nm, F, by simp, hocc, a, hshape⟩

theorem branchTrace_tail (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (nm : Nat) (F : TypeExpr) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (h : BranchConstraintTrace Δ π s i S c) :
    BranchConstraintTrace Δ π s i ((nm, F) :: S) c := by
  rcases h with ⟨fk, q, nm', F', hmem, hocc, a, hshape⟩
  exact ⟨fk, q, nm', F', by simp [hmem], hocc, a, hshape⟩

def TypesTraceGoal (i : SizeVar) (Φ : FlexVars) (Δ : KindingCtx) (π : Polarity)
    (A C : TypeExpr) (Cs : List SizeConstraint) : Prop :=
  ∀ s, Φ.lookupPol i = some s → (s = .pos ∨ s = .neg) → ¬ SizeOccursIn i A →
    ∀ c ∈ Cs, c.mentions i = true → ConstraintTrace Δ π s i C c

def BranchesTraceGoal (i : SizeVar) (Φ : FlexVars) (Δ : KindingCtx) (π : Polarity)
    (S S' : List (Nat × TypeExpr)) (Cs : List SizeConstraint) : Prop :=
  ∀ s, Φ.lookupPol i = some s → (s = .pos ∨ s = .neg) → i ∉ allSizeVarsBranches S →
    ∀ c ∈ Cs, c.mentions i = true → BranchConstraintTrace Δ π s i S' c

theorem coherentTypes_trace {i : SizeVar} {Φ : FlexVars} {Δ : KindingCtx}
    {ι : SKind} {π : Polarity} {A C : TypeExpr} {Cs : List SizeConstraint}
    (h : CoherentCompareTypes i Φ Δ ι π A C Cs) : TypesTraceGoal i Φ Δ π A C Cs := by
  refine CoherentCompareTypes.rec
    (motive_1 := fun Δ _ π A C Cs _ => TypesTraceGoal i Φ Δ π A C Cs)
    (motive_2 := fun Δ π S S' Cs _ => BranchesTraceGoal i Φ Δ π S S' Cs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Δ ι π K s hs hstrict hno c hc hm
    cases hc
  · intro Δ p π ι₁ ι₂ F F' G G' C₁ C₂ hF' hcF hcG ihF ihG s hs hstrict hno c hmem hmention
    have hnoF : ¬ SizeOccursIn i F := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inl hi)
    have hnoG : ¬ SizeOccursIn i G := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inr hi)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact trace_app_left Δ π s p i F' G' _ _ c hF' (ihF s hs hstrict hnoF c hmem hmention)
    · exact trace_app_right Δ π s p i F' G' _ _ c hF' (ihG s hs hstrict hnoG c hmem hmention)
  · intro Δ p π ι₁ ι₂ F F' X C transportF' hc ih s hs hstrict hno c hmem hmention
    exact trace_lam Δ (Δ.extType X p (Kind.ofSKind ι₁)) π s i F'
      (F'.normApp (.atom (.var X))) c transportF'
      (ih s hs hstrict (size_absent_normApp_var i F X hno) c hmem hmention)
  · intro Δ π r p a b S S' C hleft hright hc ih s hs hstrict hno c hmem hmention
    have hnoIdx : i ∉ a.vars := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inl hi)
    have hnoBranches : i ∉ allSizeVarsBranches S := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inr hi)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact mu_node_trace Φ Δ p r π a b S' c i s hright hs hstrict hnoIdx hmem hmention
    · exact branchTrace_mu Δ π s i b S' c (ih s hs hstrict hnoBranches c hmem hmention)
  · intro Δ π r p a b S S' C hleft hright hc ih s hs hstrict hno c hmem hmention
    have hnoIdx : i ∉ a.vars := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inl hi)
    have hnoBranches : i ∉ allSizeVarsBranches S := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inr hi)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact nu_node_trace Φ Δ p r π a b S' c i s hright hs hstrict hnoIdx hmem hmention
    · exact branchTrace_nu Δ π s i b S' c (ih s hs hstrict hnoBranches c hmem hmention)
  · intro Δ π s hs hstrict hno c hc hm
    cases hc
  · intro Δ π nm F F' rest rest' C₁ C₂ hcF hcB ihF ihB s hs hstrict hno c hmem hmention
    have hnoF : ¬ SizeOccursIn i F := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inl hi)
    have hnoRest : i ∉ allSizeVarsBranches rest := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inr hi)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact branchTrace_head Δ π s i nm F' rest' c (ihF s hs hstrict hnoF c hmem hmention)
    · exact branchTrace_tail Δ π s i nm F' rest' c (ihB s hs hstrict hnoRest c hmem hmention)

/-- Guarded constraint-direction result. This is stronger than the corresponding
    conjunct's local polarity claim: it requires neither source-fragment nor
    global hygiene premises, but does require a coherent comparison. -/
theorem coherent_theorem10 {i : SizeVar} {Φ : FlexVars} {Δ : KindingCtx}
    {ι : SKind} {π s q : Polarity} {A C : TypeExpr} {Cs : List SizeConstraint}
    (h : CoherentCompareTypes i Φ Δ ι π A C Cs)
    (hs : Φ.lookupPol i = some s) (hstrict : s = .pos ∨ s = .neg)
    (hno : ¬ SizeOccursIn i A)
    (hocc : ∀ fk q', SizeOccursFixPol Δ fk i q' C → q' = q) :
    ∀ c ∈ Cs, c.mentions i = true →
      ∃ a, c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π s) q) a (.var i 0) := by
  intro c hmem hmention
  obtain ⟨fk, q', hocc', a, hshape⟩ := coherentTypes_trace h s hs hstrict hno c hmem hmention
  rw [hocc fk q' hocc'] at hshape
  exact ⟨a, hshape⟩

end NishtAbel2024

open NishtAbel2024

theorem solution :
    ∀ (Φ : FlexVars) (Δ : KindingCtx) (ι : SKind) (π π' π'' : Polarity)
       (A C : TypeExpr) (Cs : List SizeConstraint) (i : SizeVar),
      FlexPolHygiene Φ Δ A C →
      Φ.lookupPol i = some π' →
      (π' = .pos ∨ π' = .neg) →
      (π'' = .pos ∨ π'' = .neg) →
      ¬ SizeOccursIn i A →
      (∀ fk π₀, SizeOccursFixPol Δ fk i π₀ C →
        π₀ = π'' ∧ ((fk = .mu ∧ π' = .pos) ∨ (fk = .nu ∧ π' = .neg))) →
      CoherentCompareTypes i Φ Δ ι π A C Cs →
      ∀ c ∈ Cs, c.mentions i = true →
        ∃ a : SizeExp,
          c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π π') π'') a (.var i 0) := by
  intro Φ Δ ι π π' π'' A C Cs i _ hs hstrict _ hno hocc hcoherent
  exact coherent_theorem10 hcoherent hs hstrict hno (fun fk q h => (hocc fk q h).1)

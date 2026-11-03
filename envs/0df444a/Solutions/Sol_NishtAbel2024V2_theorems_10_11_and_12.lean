-- Prove2me | solution 1 for NishtAbel2024V2.theorems_10_11_and_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:21:02.988638+00:00
-- url     : https://prove2.me/submissions/82e78f0c-4510-4732-b164-ac34557984f8

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Inference

namespace NishtAbel2024V2

/-! ## Part 1: Guarded Type Comparison Soundness (Theorem 10) -/

mutual

theorem allSizeVars_subst_atom_1012 (Y X : TyVar) (F : TypeExpr) :
    (TypeExpr.substTyVar Y (.atom (.var X)) F).allSizeVars = F.allSizeVars := by
  cases F with
  | atom a =>
    cases a with
    | var z =>
      simp only [TypeExpr.substTyVar]
      split <;> rfl
    | size _ | unit | prod | arr | all _ | ex _ => rfl
  | lam z k body =>
    simp only [TypeExpr.substTyVar]
    split
    · rfl
    · exact allSizeVars_subst_atom_1012 Y X body
  | app f g =>
    simp only [TypeExpr.substTyVar, TypeExpr.allSizeVars]
    rw [allSizeVars_subst_atom_1012 Y X f, allSizeVars_subst_atom_1012 Y X g]
  | mu a branches =>
    simp only [TypeExpr.substTyVar, TypeExpr.allSizeVars]
    rw [allSizeVarsBranches_subst_atom_1012 Y X branches]
  | nu a branches =>
    simp only [TypeExpr.substTyVar, TypeExpr.allSizeVars]
    rw [allSizeVarsBranches_subst_atom_1012 Y X branches]
termination_by sizeOf F

theorem allSizeVarsBranches_subst_atom_1012 (Y X : TyVar) (branches : List (Nat × TypeExpr)) :
    allSizeVarsBranches (TypeExpr.substTyVarBranches Y (.atom (.var X)) branches) =
      allSizeVarsBranches branches := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
    rcases branch with ⟨name, body⟩
    simp only [TypeExpr.substTyVarBranches, allSizeVarsBranches]
    rw [allSizeVars_subst_atom_1012 Y X body, allSizeVarsBranches_subst_atom_1012 Y X rest]
termination_by sizeOf branches

end

theorem normApp_var_preserves_sizeVars_1012 (F : TypeExpr) (X : TyVar) :
    (F.normApp (.atom (.var X))).allSizeVars = F.allSizeVars := by
  cases F with
  | atom K => simp [TypeExpr.normApp, TypeExpr.allSizeVars]
  | lam Y κ body => exact allSizeVars_subst_atom_1012 Y X body
  | app f g => simp [TypeExpr.normApp, TypeExpr.allSizeVars]
  | mu a S => simp [TypeExpr.normApp, TypeExpr.allSizeVars]
  | nu a R => simp [TypeExpr.normApp, TypeExpr.allSizeVars]

theorem size_absent_normApp_var_1012 (i : SizeVar) (F : TypeExpr) (X : TyVar)
    (h : ¬ SizeOccursIn i F) : ¬ SizeOccursIn i (F.normApp (.atom (.var X))) := by
  simpa [SizeOccursIn, normApp_var_preserves_sizeVars_1012] using h

theorem lookup_index_shape_1012 (Φ : FlexVars) (fallback p : Polarity) (a : SizeExp)
    (h : Φ.lookupSizePol fallback a = some p) :
    (∃ n, a = .inf n) ∨ (∃ i, a = .var i 0) := by
  cases a with
  | inf n => exact Or.inl ⟨n, rfl⟩
  | meet m =>
    rcases m with ⟨⟨i, n⟩, tail⟩
    cases n <;> cases tail <;> simp_all [FlexVars.lookupSizePol, SizeExp.var, SizeMin.single]

theorem ofPol_mentions_right_1012 (p : Polarity) (a b : SizeExp) (c : SizeConstraint)
    (i : SizeVar) (ha : i ∉ a.vars) (hc : c ∈ SizeConstraint.ofPol p a b)
    (hm : c.mentions i = true) : i ∈ b.vars := by
  cases p <;> simp_all [SizeConstraint.ofPol, SizeConstraint.mentions]
  rcases hc with rfl | rfl <;> simp_all

theorem lookup_index_mentions_1012 (Φ : FlexVars) (fallback p : Polarity) (b : SizeExp)
    (i : SizeVar) (h : Φ.lookupSizePol fallback b = some p) (hm : i ∈ b.vars) :
    b = .var i 0 := by
  rcases lookup_index_shape_1012 Φ fallback p b h with ⟨n, rfl⟩ | ⟨j, rfl⟩
  · simp [SizeExp.vars] at hm
  · simp [SizeExp.vars, SizeExp.var, SizeMin.vars, SizeMin.toList, SizeMin.single] at hm
    subst j
    rfl

theorem infoMax_generated_sign_1012 (p r π : Polarity) (a b : SizeExp) (c : SizeConstraint)
    (hp : p = .pos ∨ p = .neg)
    (hc : c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax r p) π) a b) :
    c ∈ SizeConstraint.ofPol (Polarity.comp π p) a b := by
  cases p <;> cases r <;> cases π <;>
    simp_all [Polarity.infoMax, Polarity.comp, SizeConstraint.ofPol]

theorem fixpoint_generated_constraint_1012 (Φ : FlexVars) (fallback p r π : Polarity)
    (a b : SizeExp) (c : SizeConstraint) (i : SizeVar) (s : Polarity)
    (hb : Φ.lookupSizePol fallback b = some p)
    (hs : Φ.lookupPol i = some s) (hstrict : s = .pos ∨ s = .neg)
    (ha : i ∉ a.vars)
    (hc : c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax r p) π) a b)
    (hm : c.mentions i = true) :
    ∃ a', c ∈ SizeConstraint.ofPol (Polarity.comp π s) a' (.var i 0) := by
  have hbmem := ofPol_mentions_right_1012 _ a b c i ha hc hm
  have hbeq := lookup_index_mentions_1012 Φ fallback p b i hb hbmem
  subst b
  have hps : p = s := by
    simpa [FlexVars.lookupSizePol, SizeExp.var, SizeMin.single, hs] using hb.symm
  subst p
  exact ⟨a, infoMax_generated_sign_1012 s r π a (.var i 0) c hstrict hc⟩

def ConstraintTrace1012 (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (C : TypeExpr) (c : SizeConstraint) : Prop :=
  ∃ fk q, SizeOccursFixPol Δ fk i q C ∧
    ∃ a, c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π s) q) a (.var i 0)

def BranchConstraintTrace1012 (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (S : List (Nat × TypeExpr)) (c : SizeConstraint) : Prop :=
  ∃ fk q nm F, (nm, F) ∈ S ∧ SizeOccursFixPol Δ fk i q F ∧
    ∃ a, c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π s) q) a (.var i 0)

theorem polarity_comp_pos_1012 (p : Polarity) : Polarity.comp p .pos = p := by
  cases p <;> rfl

theorem branchTrace_mu_1012 (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (b : SizeExp) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (h : BranchConstraintTrace1012 Δ π s i S c) : ConstraintTrace1012 Δ π s i (.mu b S) c := by
  rcases h with ⟨fk, q, nm, F, hmem, hocc, a, hconstraint⟩
  exact ⟨fk, q, SizeOccursFixPol.mu_branch hmem hocc, a, hconstraint⟩

theorem branchTrace_nu_1012 (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (b : SizeExp) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (h : BranchConstraintTrace1012 Δ π s i S c) : ConstraintTrace1012 Δ π s i (.nu b S) c := by
  rcases h with ⟨fk, q, nm, F, hmem, hocc, a, hconstraint⟩
  exact ⟨fk, q, SizeOccursFixPol.nu_field hmem hocc, a, hconstraint⟩

theorem mu_node_trace_1012 (Φ : FlexVars) (Δ : KindingCtx) (p r π : Polarity)
    (a b : SizeExp) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (i : SizeVar) (s : Polarity)
    (hb : Φ.lookupSizePol .pos b = some p)
    (hs : Φ.lookupPol i = some s) (hstrict : s = .pos ∨ s = .neg)
    (ha : i ∉ a.vars)
    (hc : c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax r p) π) a b)
    (hm : c.mentions i = true) : ConstraintTrace1012 Δ π s i (.mu b S) c := by
  have hbmem := ofPol_mentions_right_1012 _ a b c i ha hc hm
  have hbeq := lookup_index_mentions_1012 Φ .pos p b i hb hbmem
  have hshape := fixpoint_generated_constraint_1012 Φ .pos p r π a b c i s hb hs hstrict ha hc hm
  subst b
  obtain ⟨a', hshape⟩ := hshape
  exact ⟨.mu, .pos, SizeOccursFixPol.mu_top, a', by simpa only [polarity_comp_pos_1012] using hshape⟩

theorem nu_node_trace_1012 (Φ : FlexVars) (Δ : KindingCtx) (p r π : Polarity)
    (a b : SizeExp) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (i : SizeVar) (s : Polarity)
    (hb : Φ.lookupSizePol .neg b = some p)
    (hs : Φ.lookupPol i = some s) (hstrict : s = .pos ∨ s = .neg)
    (ha : i ∉ a.vars)
    (hc : c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax r p) π) a b)
    (hm : c.mentions i = true) : ConstraintTrace1012 Δ π s i (.nu b S) c := by
  have hbmem := ofPol_mentions_right_1012 _ a b c i ha hc hm
  have hbeq := lookup_index_mentions_1012 Φ .neg p b i hb hbmem
  have hshape := fixpoint_generated_constraint_1012 Φ .neg p r π a b c i s hb hs hstrict ha hc hm
  subst b
  obtain ⟨a', hshape⟩ := hshape
  exact ⟨.nu, .pos, SizeOccursFixPol.nu_top, a', by simpa only [polarity_comp_pos_1012] using hshape⟩

theorem polarity_comp_rearrange_1012 (p π s q : Polarity) :
    Polarity.comp (Polarity.comp (Polarity.comp p π) s) q =
      Polarity.comp (Polarity.comp π s) (Polarity.comp p q) := by
  cases p <;> cases π <;> cases s <;> cases q <;> rfl

theorem trace_app_left_1012 (Δ : KindingCtx) (π s p : Polarity) (i : SizeVar)
    (F G : TypeExpr) (κ κ' : Kind) (c : SizeConstraint)
    (hkind : KindInfer Δ F (.arr p κ κ')) (h : ConstraintTrace1012 Δ π s i F c) :
    ConstraintTrace1012 Δ π s i (.app F G) c := by
  rcases h with ⟨fk, q, hocc, a, hshape⟩
  exact ⟨fk, q, SizeOccursFixPol.app_left hkind hocc, a, hshape⟩

theorem trace_app_right_1012 (Δ : KindingCtx) (π s p : Polarity) (i : SizeVar)
    (F G : TypeExpr) (κ κ' : Kind) (c : SizeConstraint)
    (hkind : KindInfer Δ F (.arr p κ κ'))
    (h : ConstraintTrace1012 (Δ.invScalePol p) (Polarity.comp p π) s i G c) :
    ConstraintTrace1012 Δ π s i (.app F G) c := by
  rcases h with ⟨fk, q, hocc, a, hshape⟩
  refine ⟨fk, Polarity.comp p q, SizeOccursFixPol.app_right hkind hocc, a, ?_⟩
  simpa only [polarity_comp_rearrange_1012] using hshape

theorem trace_lam_1012 (Δ ΔX : KindingCtx) (π s : Polarity) (i : SizeVar)
    (F Fapp : TypeExpr) (c : SizeConstraint)
    (transport : ∀ fk q, SizeOccursFixPol ΔX fk i q Fapp → SizeOccursFixPol Δ fk i q F)
    (h : ConstraintTrace1012 ΔX π s i Fapp c) : ConstraintTrace1012 Δ π s i F c := by
  rcases h with ⟨fk, q, hocc, a, hshape⟩
  exact ⟨fk, q, transport fk q hocc, a, hshape⟩

theorem branchTrace_head_1012 (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (nm : Nat) (F : TypeExpr) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (h : ConstraintTrace1012 Δ π s i F c) :
    BranchConstraintTrace1012 Δ π s i ((nm, F) :: S) c := by
  rcases h with ⟨fk, q, hocc, a, hshape⟩
  exact ⟨fk, q, nm, F, by simp, hocc, a, hshape⟩

theorem branchTrace_tail_1012 (Δ : KindingCtx) (π s : Polarity) (i : SizeVar)
    (nm : Nat) (F : TypeExpr) (S : List (Nat × TypeExpr)) (c : SizeConstraint)
    (h : BranchConstraintTrace1012 Δ π s i S c) :
    BranchConstraintTrace1012 Δ π s i ((nm, F) :: S) c := by
  rcases h with ⟨fk, q, nm', F', hmem, hocc, a, hshape⟩
  exact ⟨fk, q, nm', F', by simp [hmem], hocc, a, hshape⟩

def TypesTraceGoal1012 (i : SizeVar) (Φ : FlexVars) (Δ : KindingCtx) (π : Polarity)
    (A C : TypeExpr) (Cs : List SizeConstraint) : Prop :=
  ∀ s, Φ.lookupPol i = some s → (s = .pos ∨ s = .neg) → ¬ SizeOccursIn i A →
    ∀ c ∈ Cs, c.mentions i = true → ConstraintTrace1012 Δ π s i C c

def BranchesTraceGoal1012 (i : SizeVar) (Φ : FlexVars) (Δ : KindingCtx) (π : Polarity)
    (S S' : List (Nat × TypeExpr)) (Cs : List SizeConstraint) : Prop :=
  ∀ s, Φ.lookupPol i = some s → (s = .pos ∨ s = .neg) → i ∉ allSizeVarsBranches S →
    ∀ c ∈ Cs, c.mentions i = true → BranchConstraintTrace1012 Δ π s i S' c

theorem guardedTypes_trace {i : SizeVar} {Φ : FlexVars} {Δ : KindingCtx}
    {ι : SKind} {π : Polarity} {A C : TypeExpr} {Cs : List SizeConstraint}
    (h : GuardedCompareTypes i Φ Δ ι π A C Cs) : TypesTraceGoal1012 i Φ Δ π A C Cs := by
  refine GuardedCompareTypes.rec
    (motive_1 := fun Δ _ π A C Cs _ => TypesTraceGoal1012 i Φ Δ π A C Cs)
    (motive_2 := fun Δ π S S' Cs _ => BranchesTraceGoal1012 i Φ Δ π S S' Cs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Δ ι π K s hs hstrict hno c hc hm
    cases hc
  · intro Δ p π ι₁ ι₂ F F' G G' C₁ C₂ hF hF' hcF hcG ihF ihG s hs hstrict hno c hmem hmention
    have hnoF : ¬ SizeOccursIn i F := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inl hi)
    have hnoG : ¬ SizeOccursIn i G := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inr hi)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact trace_app_left_1012 Δ π s p i F' G' _ _ c hF' (ihF s hs hstrict hnoF c hmem hmention)
    · exact trace_app_right_1012 Δ π s p i F' G' _ _ c hF' (ihG s hs hstrict hnoG c hmem hmention)
  · intro Δ p π ι₁ ι₂ F F' X C _ _ _ _ transportF' _ ih s hs hstrict hno c hmem hmention
    exact trace_lam_1012 Δ (Δ.extType X p (Kind.ofSKind ι₁)) π s i F'
      (F'.normApp (.atom (.var X))) c transportF'
      (ih s hs hstrict (size_absent_normApp_var_1012 i F X hno) c hmem hmention)
  · intro Δ π r p a b S S' C _ hright _ ih s hs hstrict hno c hmem hmention
    have hnoIdx : i ∉ a.vars := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inl hi)
    have hnoBranches : i ∉ allSizeVarsBranches S := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inr hi)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact mu_node_trace_1012 Φ Δ p r π a b S' c i s hright hs hstrict hnoIdx hmem hmention
    · exact branchTrace_mu_1012 Δ π s i b S' c (ih s hs hstrict hnoBranches c hmem hmention)
  · intro Δ π r p a b S S' C _ hright _ ih s hs hstrict hno c hmem hmention
    have hnoIdx : i ∉ a.vars := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inl hi)
    have hnoBranches : i ∉ allSizeVarsBranches S := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inr hi)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact nu_node_trace_1012 Φ Δ p r π a b S' c i s hright hs hstrict hnoIdx hmem hmention
    · exact branchTrace_nu_1012 Δ π s i b S' c (ih s hs hstrict hnoBranches c hmem hmention)
  · intro Δ π s hs hstrict hno c hc hm
    cases hc
  · intro Δ π nm F F' rest rest' C₁ C₂ _ _ ihF ihB s hs hstrict hno c hmem hmention
    have hnoF : ¬ SizeOccursIn i F := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inl hi)
    have hnoRest : i ∉ allSizeVarsBranches rest := by
      intro hi
      apply hno
      exact List.mem_append.mpr (Or.inr hi)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact branchTrace_head_1012 Δ π s i nm F' rest' c (ihF s hs hstrict hnoF c hmem hmention)
    · exact branchTrace_tail_1012 Δ π s i nm F' rest' c (ihB s hs hstrict hnoRest c hmem hmention)

theorem guarded_theorem10 {i : SizeVar} {Φ : FlexVars} {Δ : KindingCtx}
    {ι : SKind} {π s q : Polarity} {A C : TypeExpr} {Cs : List SizeConstraint}
    (h : GuardedCompareTypes i Φ Δ ι π A C Cs)
    (hs : Φ.lookupPol i = some s) (hstrict : s = .pos ∨ s = .neg)
    (hno : ¬ SizeOccursIn i A)
    (hocc : ∀ fk q', SizeOccursFixPol Δ fk i q' C → q' = q) :
    ∀ c ∈ Cs, c.mentions i = true →
      ∃ a, c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π s) q) a (.var i 0) := by
  intro c hmem hmention
  obtain ⟨fk, q', hocc', a, hshape⟩ := guardedTypes_trace h s hs hstrict hno c hmem hmention
  rw [hocc fk q' hocc'] at hshape
  exact ⟨a, hshape⟩

/-! ## Part 2: Guarded Term Inference / Checking No-Incoming-Edge (Theorems 11 & 12) -/

theorem noDistinctIncoming_nil_1012 (i : SizeVar) : NoDistinctIncoming i [] := by
  intro c hc
  cases hc

theorem noDistinctIncoming_append_1012 {i : SizeVar} {C₁ C₂ : List SizeConstraint}
    (h₁ : NoDistinctIncoming i C₁) (h₂ : NoDistinctIncoming i C₂) :
    NoDistinctIncoming i (C₁ ++ C₂) := by
  intro c hc j hj
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc j hj
  · exact h₂ c hc j hj

theorem var_eq_vars_mem_1012 {a : SizeExp} {i : SizeVar} (h : a = .var i 0) :
    i ∈ a.vars := by
  subst h
  simp [SizeExp.var, SizeExp.vars, SizeMin.vars, SizeMin.single, SizeMin.toList]

theorem noDistinctIncoming_proj_1012 {i j : SizeVar} {a : SizeExp}
    {R : List (ProjName × TypeExpr)} {Cs : List SizeConstraint}
    (hnu : i ∉ nuIndexVars (.nu a R))
    (hCs : NoDistinctIncoming i Cs) :
    NoDistinctIncoming i (⟨.var j 0, .lt, a⟩ :: Cs) := by
  intro c hc k hk
  rcases List.mem_cons.mp hc with rfl | hc
  · rintro ⟨_, hrhs⟩
    apply hnu
    simp [nuIndexVars, var_eq_vars_mem_1012 hrhs]
  · exact hCs c hc k hk

theorem mu_top_index_checkUse_1012 {Δ : KindingCtx} {a : SizeExp}
    {S : List (ConsName × TypeExpr)} {i : SizeVar}
    (hk : KindCheck Δ (.mu a S) .star) (hi : i ∈ a.vars) :
    CheckUse Δ (.mu a S) .star .mu i .pos := by
  cases hk with
  | sub hinf hsub =>
    cases hinf with
    | mu hw hb =>
      exact CheckUse.sub (KindInfer.mu hw hb) hsub (InferUse.muIndex (KindInfer.mu hw hb) hi)

theorem noDistinctIncoming_cons_mu_1012 {Δ : KindingCtx} {i j : SizeVar}
    {a : SizeExp} {S : List (ConsName × TypeExpr)} {Cs : List SizeConstraint}
    (hk : KindCheck Δ (.mu a S) .star)
    (hn : ¬ CheckUse Δ (.mu a S) .star .mu i .pos)
    (hCs : NoDistinctIncoming i Cs) :
    NoDistinctIncoming i (⟨.var j 0, .lt, a⟩ :: Cs) := by
  intro c hc k hk_ne
  rcases List.mem_cons.mp hc with rfl | hc
  · rintro ⟨_, hrhs⟩
    exact hn (mu_top_index_checkUse_1012 hk (var_eq_vars_mem_1012 hrhs))
  · exact hCs c hc k hk_ne

theorem safeInferTerm_sound_1012 {sig : GlobalSig} {Ξ : MutualBlock} {i : SizeVar}
    {Φ Γ Δ t A Φ' Cs T t'}
    (h : SafeInferTerm sig Ξ i Φ Γ Δ t A Φ' Cs T t') :
    InferTerm sig Ξ Φ Γ Δ t A Φ' Cs T t' ∧ NoDistinctIncoming i Cs := by
  induction h using SafeInferTerm.rec
    (motive_2 := fun Φ Γ Δ A t Φ' Cs T t' _ =>
      CheckTerm sig Ξ Φ Γ Δ A t Φ' Cs T t' ∧ NoDistinctIncoming i Cs)
    (motive_3 := fun Φ Γ Δ C D Φ' Cs T D' _ =>
      CheckClauseInfer sig Ξ Φ Γ Δ C D Φ' Cs T D' ∧ NoDistinctIncoming i Cs)
    (motive_4 := fun Φ Γ Δ C Ds Φ' Cs T Ds' _ =>
      CheckClausesInfer sig Ξ Φ Γ Δ C Ds Φ' Cs T Ds' ∧ NoDistinctIncoming i Cs) with
  | var hmem =>
    exact ⟨.var hmem, noDistinctIncoming_nil_1012 i⟩
  | appTerm _ _ ihr ihs =>
    exact ⟨.appTerm ihr.1 ihs.1, noDistinctIncoming_append_1012 ihr.2 ihs.2⟩
  | proj j _ hnu hlookup hjΦ hjΔ hT ihr =>
    exact ⟨.proj j ihr.1 hlookup hjΦ hjΔ hT, noDistinctIncoming_proj_1012 hnu ihr.2⟩
  | appTy henc hdisj _ ihr =>
    exact ⟨.appTy henc hdisj ihr.1, ihr.2⟩
  | ascr henc hdisj _ iht =>
    exact ⟨.ascr henc hdisj iht.1, iht.2⟩
  | funCall hdecl hlen hnodup hdisjΦ hdisjΔ hpol has =>
    exact ⟨.funCall hdecl hlen hnodup hdisjΦ hdisjΔ hpol has, noDistinctIncoming_nil_1012 i⟩
  | unit Φ Γ Δ =>
    exact ⟨.unit Φ Γ Δ, noDistinctIncoming_nil_1012 i⟩
  | pair _ _ iht₁ iht₂ =>
    exact ⟨.pair iht₁.1 iht₂.1, noDistinctIncoming_append_1012 iht₁.2 iht₂.2⟩
  | lamClauses _ ihDs =>
    exact ⟨.lamClauses ihDs.1, ihDs.2⟩
  | cons j hk hn hlookup hjΦ hjΔ _ hT iht =>
    exact ⟨.cons j hlookup hjΦ hjΔ iht.1 hT, noDistinctIncoming_cons_mu_1012 hk hn iht.2⟩
  | pack henc hdisj _ iht =>
    exact ⟨.pack henc hdisj iht.1, iht.2⟩
  | sub _ hhyg hcmp hno ihr =>
    exact ⟨.sub ihr.1 hhyg hcmp, noDistinctIncoming_append_1012 ihr.2 hno⟩
  | mk hsp hΨ _ iht =>
    exact ⟨.mk hsp hΨ iht.1, iht.2⟩
  | nilClause Φ Γ Δ C =>
    exact ⟨.nil Φ Γ Δ C, noDistinctIncoming_nil_1012 i⟩
  | consClause _ _ ihD ihDs =>
    exact ⟨.cons ihD.1 ihDs.1, noDistinctIncoming_append_1012 ihD.2 ihDs.2⟩

theorem safeCheckTerm_sound_1012 {sig : GlobalSig} {Ξ : MutualBlock} {i : SizeVar}
    {Φ Γ Δ A t Φ' Cs T t'}
    (h : SafeCheckTerm sig Ξ i Φ Γ Δ A t Φ' Cs T t') :
    CheckTerm sig Ξ Φ Γ Δ A t Φ' Cs T t' ∧ NoDistinctIncoming i Cs := by
  induction h using SafeCheckTerm.rec
    (motive_1 := fun Φ Γ Δ t A Φ' Cs T t' _ =>
      InferTerm sig Ξ Φ Γ Δ t A Φ' Cs T t' ∧ NoDistinctIncoming i Cs)
    (motive_3 := fun Φ Γ Δ C D Φ' Cs T D' _ =>
      CheckClauseInfer sig Ξ Φ Γ Δ C D Φ' Cs T D' ∧ NoDistinctIncoming i Cs)
    (motive_4 := fun Φ Γ Δ C Ds Φ' Cs T Ds' _ =>
      CheckClausesInfer sig Ξ Φ Γ Δ C Ds Φ' Cs T Ds' ∧ NoDistinctIncoming i Cs) with
  | var hmem =>
    exact ⟨.var hmem, noDistinctIncoming_nil_1012 i⟩
  | appTerm _ _ ihr ihs =>
    exact ⟨.appTerm ihr.1 ihs.1, noDistinctIncoming_append_1012 ihr.2 ihs.2⟩
  | proj j _ hnu hlookup hjΦ hjΔ hT ihr =>
    exact ⟨.proj j ihr.1 hlookup hjΦ hjΔ hT, noDistinctIncoming_proj_1012 hnu ihr.2⟩
  | appTy henc hdisj _ ihr =>
    exact ⟨.appTy henc hdisj ihr.1, ihr.2⟩
  | ascr henc hdisj _ iht =>
    exact ⟨.ascr henc hdisj iht.1, iht.2⟩
  | funCall hdecl hlen hnodup hdisjΦ hdisjΔ hpol has =>
    exact ⟨.funCall hdecl hlen hnodup hdisjΦ hdisjΔ hpol has, noDistinctIncoming_nil_1012 i⟩
  | unit Φ Γ Δ =>
    exact ⟨.unit Φ Γ Δ, noDistinctIncoming_nil_1012 i⟩
  | pair _ _ iht₁ iht₂ =>
    exact ⟨.pair iht₁.1 iht₂.1, noDistinctIncoming_append_1012 iht₁.2 iht₂.2⟩
  | lamClauses _ ihDs =>
    exact ⟨.lamClauses ihDs.1, ihDs.2⟩
  | cons j hk hn hlookup hjΦ hjΔ _ hT iht =>
    exact ⟨.cons j hlookup hjΦ hjΔ iht.1 hT, noDistinctIncoming_cons_mu_1012 hk hn iht.2⟩
  | pack henc hdisj _ iht =>
    exact ⟨.pack henc hdisj iht.1, iht.2⟩
  | sub _ hhyg hcmp hno ihr =>
    exact ⟨.sub ihr.1 hhyg hcmp, noDistinctIncoming_append_1012 ihr.2 hno⟩
  | mk hsp hΨ _ iht =>
    exact ⟨.mk hsp hΨ iht.1, iht.2⟩
  | nilClause Φ Γ Δ C =>
    exact ⟨.nil Φ Γ Δ C, noDistinctIncoming_nil_1012 i⟩
  | consClause _ _ ihD ihDs =>
    exact ⟨.cons ihD.1 ihDs.1, noDistinctIncoming_append_1012 ihD.2 ihDs.2⟩

theorem noDistinctIncoming_implies_noOutsideIncoming_1012 {dom : List SizeVar} {i : SizeVar}
    {Cs : List SizeConstraint} (hi : i ∈ dom) (h : NoDistinctIncoming i Cs) :
    NoOutsideIncoming dom i Cs := by
  intro c hc j hj
  have hne : j ≠ i := by
    intro heq
    subst heq
    exact hj hi
  exact h c hc j hne

/-- Repaired Theorem 10 (Polarities in type comparison, pp. 52–53),
Theorem 11 (No incoming edges in guarded call-site inference/checking, pp. 53–54), and
Theorem 12 (No incoming flexible-to-rigid edges in clause bodies, pp. 55–56) in `NishtAbel2024V2`. -/
theorem theorems_10_11_and_12 :
    (∀ (Φ : FlexVars) (Δ : KindingCtx) (ι : SKind) (π π' π'' : Polarity)
       (A C : TypeExpr) (Cs : List SizeConstraint) (i : SizeVar),
      FlexPolHygiene Φ Δ A C →
      Φ.lookupPol i = some π' →
      (π' = .pos ∨ π' = .neg) →
      (π'' = .pos ∨ π'' = .neg) →
      ¬ SizeOccursIn i A →
      (∀ fk π₀, SizeOccursFixPol Δ fk i π₀ C →
        π₀ = π'' ∧ ((fk = .mu ∧ π' = .pos) ∨ (fk = .nu ∧ π' = .neg))) →
      GuardedCompareTypes i Φ Δ ι π A C Cs →
      ∀ c ∈ Cs, c.mentions i = true →
        ∃ a : SizeExp,
          c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π π') π'') a (.var i 0)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (i : SizeVar)
       (Φ₀ Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) (A C : TypeExpr)
       (t t' : Term) (Cs : List SizeConstraint) (T : List SizeVar),
      (SafeInferTerm sig Ξ i Φ₀ Γ Δ t C Φ Cs T t' →
        InferTerm sig Ξ Φ₀ Γ Δ t C Φ Cs T t' ∧ NoDistinctIncoming i Cs) ∧
      (SafeCheckTerm sig Ξ i Φ₀ Γ Δ A t Φ Cs T t' →
        CheckTerm sig Ξ Φ₀ Γ Δ A t Φ Cs T t' ∧ NoDistinctIncoming i Cs)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar) (j : SizeVar),
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      j ∈ (Ψ₁ ++ Ψ₂).dom →
      SafeCheckTerm sig Ξ j ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      NoOutsideIncoming (Ψ₁ ++ Ψ₂).dom j Cs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ Δ ι π π' π'' A C Cs i _ hs hstrict _ hno hocc hguarded
    exact guarded_theorem10 hguarded hs hstrict hno (fun fk q h => (hocc fk q h).1)
  · intro sig Ξ i Φ₀ Φ Γ Δ A C t t' Cs T
    exact ⟨safeInferTerm_sound_1012, safeCheckTerm_sound_1012⟩
  · intro sig Ξ Δ₀ Ψ₁ Ψ₂ A A₀ A'' qs qs' Γ Δ t t' Φ Cs T j _ _ _ hj hbody
    exact noDistinctIncoming_implies_noOutsideIncoming_1012 hj (safeCheckTerm_sound_1012 hbody).2

end NishtAbel2024V2

open NishtAbel2024V2

theorem solution :
    (∀ (Φ : FlexVars) (Δ : KindingCtx) (ι : SKind) (π π' π'' : Polarity)
       (A C : TypeExpr) (Cs : List SizeConstraint) (i : SizeVar),
      FlexPolHygiene Φ Δ A C →
      Φ.lookupPol i = some π' →
      (π' = .pos ∨ π' = .neg) →
      (π'' = .pos ∨ π'' = .neg) →
      ¬ SizeOccursIn i A →
      (∀ fk π₀, SizeOccursFixPol Δ fk i π₀ C →
        π₀ = π'' ∧ ((fk = .mu ∧ π' = .pos) ∨ (fk = .nu ∧ π' = .neg))) →
      GuardedCompareTypes i Φ Δ ι π A C Cs →
      ∀ c ∈ Cs, c.mentions i = true →
        ∃ a : SizeExp,
          c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π π') π'') a (.var i 0)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (i : SizeVar)
       (Φ₀ Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) (A C : TypeExpr)
       (t t' : Term) (Cs : List SizeConstraint) (T : List SizeVar),
      (SafeInferTerm sig Ξ i Φ₀ Γ Δ t C Φ Cs T t' →
        InferTerm sig Ξ Φ₀ Γ Δ t C Φ Cs T t' ∧ NoDistinctIncoming i Cs) ∧
      (SafeCheckTerm sig Ξ i Φ₀ Γ Δ A t Φ Cs T t' →
        CheckTerm sig Ξ Φ₀ Γ Δ A t Φ Cs T t' ∧ NoDistinctIncoming i Cs)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar) (j : SizeVar),
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      j ∈ (Ψ₁ ++ Ψ₂).dom →
      SafeCheckTerm sig Ξ j ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      NoOutsideIncoming (Ψ₁ ++ Ψ₂).dom j Cs) := NishtAbel2024V2.theorems_10_11_and_12

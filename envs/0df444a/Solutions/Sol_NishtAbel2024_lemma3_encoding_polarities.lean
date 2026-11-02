-- Prove2me | solution 1 for NishtAbel2024.lemma3_encoding_polarities
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:44:06.736423+00:00
-- url     : https://prove2.me/submissions/46307bed-f2b8-48c1-8653-547b3bec7158

import Definitions.Def_NishtAbel2024_Inference

set_option autoImplicit false

namespace NishtAbel2024

/-- Membership-based weakening; duplicates and binding order are retained. -/
def SizeIncluded (xs ys : SizeCtx) : Prop := ∀ d, d ∈ xs → d ∈ ys

theorem theorem7_sizeWf_mono {xs ys : SizeCtx} (h : SizeIncluded xs ys)
    {a : SizeExp} (hw : SizeWf xs a) : SizeWf ys a := by
  cases a with
  | inf n => trivial
  | meet m =>
    intro sv hsv
    obtain ⟨b, p, hp, hpol⟩ := hw sv hsv
    exact ⟨b, p, h _ hp, hpol⟩

theorem theorem7_sizeLt_mono {xs ys : SizeCtx} (h : SizeIncluded xs ys)
    {a b : SizeExp} (hab : SizeLt xs a b) : SizeLt ys a b := by
  induction hab with
  | inf_lt_inf hnm => exact .inf_lt_inf hnm
  | var_lt_var hnm hbound =>
    obtain ⟨p, hp, hpol⟩ := hbound
    exact .var_lt_var hnm ⟨p, h _ hp, hpol⟩
  | var_lt_inf hbound =>
    obtain ⟨p, hp, hpol⟩ := hbound
    exact .var_lt_inf ⟨p, h _ hp, hpol⟩
  | var_lt_inf_add hbound =>
    obtain ⟨p, hp, hpol⟩ := hbound
    exact .var_lt_inf_add ⟨p, h _ hp, hpol⟩
  | var_bound_step hbound hlt ih =>
    obtain ⟨p, hp, hpol⟩ := hbound
    exact .var_bound_step ⟨p, h _ hp, hpol⟩ ih
  | meet_lt_left hw hmem hlt ih =>
    exact .meet_lt_left (theorem7_sizeWf_mono h hw) hmem ih
  | lt_meet_right hlt ih => exact .lt_meet_right ih

theorem theorem7_sizeIncluded_map {xs ys : SizeCtx} (h : SizeIncluded xs ys)
    (f : SizeDecl → SizeDecl) : SizeIncluded (xs.map f) (ys.map f) := by
  intro d hd
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
  exact List.mem_map.mpr ⟨d', h _ hd', rfl⟩

theorem theorem7_kindWf_mono {xs ys : SizeCtx} (h : SizeIncluded xs ys)
    {κ : Kind} (hw : KindWf xs κ) : KindWf ys κ := by
  induction hw generalizing ys with
  | star => exact .star _
  | lt ha => exact .lt (theorem7_sizeWf_mono h ha)
  | arr h₁ h₂ ih₁ ih₂ =>
    exact .arr (ih₁ (theorem7_sizeIncluded_map h _)) (ih₂ h)

theorem theorem7_subKind_mono {xs ys : SizeCtx} (h : SizeIncluded xs ys)
    {κ κ' : Kind} (hs : SubKind xs κ κ') : SubKind ys κ κ' := by
  induction hs generalizing ys with
  | star => exact .star _
  | lt ha => exact .lt (theorem7_sizeLt_mono h ha)
  | arr hp h₁ h₂ ih₁ ih₂ =>
    exact .arr hp (ih₁ (theorem7_sizeIncluded_map h _)) (ih₂ h)

def KindingIncluded (Δ Δ' : KindingCtx) : Prop :=
  SizeIncluded Δ.sizes Δ'.sizes ∧ ∀ d, d ∈ Δ.types → d ∈ Δ'.types

theorem theorem7_ctx_invScale {Δ Δ' : KindingCtx} (h : KindingIncluded Δ Δ') (π : Polarity) :
    KindingIncluded (Δ.invScalePol π) (Δ'.invScalePol π) := by
  constructor
  · exact theorem7_sizeIncluded_map h.1 _
  · intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
    exact List.mem_map.mpr ⟨d', h.2 _ hd', rfl⟩

theorem theorem7_ctx_extType {Δ Δ' : KindingCtx} (h : KindingIncluded Δ Δ')
    (X : TyVar) (π : Polarity) (κ : Kind) :
    KindingIncluded (Δ.extType X π κ) (Δ'.extType X π κ) := by
  cases κ <;> simp only [KindingCtx.extType, KindingIncluded]
  all_goals
    constructor
    · first
      | exact h.1
      | intro d hd
        simp only [List.mem_append, List.mem_singleton] at hd ⊢
        exact hd.elim (fun hmem => Or.inl (h.1 _ hmem)) Or.inr
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd ⊢
      exact hd.elim (fun hmem => Or.inl (h.2 _ hmem)) Or.inr

theorem theorem7_kindInfer_mono {Δ : KindingCtx} {F : TypeExpr} {κ : Kind}
    (h : KindInfer Δ F κ) : ∀ Δ', KindingIncluded Δ Δ' → KindInfer Δ' F κ := by
  induction h using KindInfer.rec
    (motive_2 := fun Δ F κ _ => ∀ Δ', KindingIncluded Δ Δ' → KindCheck Δ' F κ) with
  | unit Δ => intro Δ' hi; exact .unit Δ'
  | prod Δ => intro Δ' hi; exact .prod Δ'
  | arr Δ => intro Δ' hi; exact .arr Δ'
  | size hw => intro Δ' hi; exact .size (theorem7_sizeWf_mono hi.1 hw)
  | var hm hp => intro Δ' hi; exact .var (hi.2 _ hm) hp
  | app hf hg ihf ihg =>
    intro Δ' hi
    exact .app (ihf Δ' hi) (ihg _ (theorem7_ctx_invScale hi _))
  | all hw => intro Δ' hi; exact .all (theorem7_kindWf_mono (theorem7_sizeIncluded_map hi.1 _) hw)
  | ex hw => intro Δ' hi; exact .ex (theorem7_kindWf_mono hi.1 hw)
  | mu hw hb ih =>
    intro Δ' hi
    exact .mu (theorem7_sizeWf_mono hi.1 hw) (fun p hp => ih p hp Δ' hi)
  | nu hw hb ih =>
    intro Δ' hi
    exact .nu (theorem7_sizeWf_mono (theorem7_sizeIncluded_map hi.1 _) hw) (fun p hp => ih p hp Δ' hi)
  | sub hf hs ih => rename_i Δ' hi; exact .sub (ih Δ' hi) (theorem7_subKind_mono hi.1 hs)
  | lam hw hb ih =>
    rename_i Δ' hi
    exact .lam (theorem7_kindWf_mono (theorem7_sizeIncluded_map hi.1 _) hw)
      (ih _ (theorem7_ctx_extType hi _ _ _))

theorem theorem7_kindCheck_mono {Δ : KindingCtx} {F : TypeExpr} {κ : Kind}
    (h : KindCheck Δ F κ) : ∀ Δ', KindingIncluded Δ Δ' → KindCheck Δ' F κ := by
  induction h using KindCheck.rec
    (motive_1 := fun Δ F κ _ => ∀ Δ', KindingIncluded Δ Δ' → KindInfer Δ' F κ) with
  | unit Δ => rename_i Δ' hi; exact .unit Δ'
  | prod Δ => rename_i Δ' hi; exact .prod Δ'
  | arr Δ => rename_i Δ' hi; exact .arr Δ'
  | size hw => rename_i Δ' hi; exact .size (theorem7_sizeWf_mono hi.1 hw)
  | var hm hp => rename_i Δ' hi; exact .var (hi.2 _ hm) hp
  | app hf hg ihf ihg =>
    rename_i Δ' hi
    exact .app (ihf Δ' hi) (ihg _ (theorem7_ctx_invScale hi _))
  | all hw => rename_i Δ' hi; exact .all (theorem7_kindWf_mono (theorem7_sizeIncluded_map hi.1 _) hw)
  | ex hw => rename_i Δ' hi; exact .ex (theorem7_kindWf_mono hi.1 hw)
  | mu hw hb ih =>
    rename_i Δ' hi
    exact .mu (theorem7_sizeWf_mono hi.1 hw) (fun p hp => ih p hp Δ' hi)
  | nu hw hb ih =>
    rename_i Δ' hi
    exact .nu (theorem7_sizeWf_mono (theorem7_sizeIncluded_map hi.1 _) hw) (fun p hp => ih p hp Δ' hi)
  | sub hf hs ih => intro Δ' hi; exact .sub (ih Δ' hi) (theorem7_subKind_mono hi.1 hs)
  | lam hw hb ih =>
    intro Δ' hi
    exact .lam (theorem7_kindWf_mono (theorem7_sizeIncluded_map hi.1 _) hw)
      (ih _ (theorem7_ctx_extType hi _ _ _))

end NishtAbel2024


namespace NishtAbel2024

/-- Every declaration generated by signature encoding has mixed polarity and
    the unbounded size as its bound. -/
def EncodingSizesSimple (Ψ : SizeCtx) : Prop :=
  ∀ d ∈ Ψ, d.pol = .mixed ∧ d.bound = .infty

mutual

theorem encode_sizes_simple {πstar π : Polarity} {Δ : KindingCtx}
    {A A' : TypeExpr} {Ψ : SizeCtx} (h : EncodeType πstar π Δ A Ψ A') :
    EncodingSizesSimple Ψ := by
  cases h with
  | unit | prod | arr | var | all | ex => simp [EncodingSizesSimple]
  | lam _ h => exact encode_sizes_simple h
  | app _ _ _ h₁ h₂ _ _ _ =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact encode_sizes_simple h₁ d hd
    · exact encode_sizes_simple h₂ d hd
  | mu_fresh _ _ _ _ h | nu_fresh _ _ _ _ h =>
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ⟨rfl, rfl⟩
    · exact encode_branches_sizes_simple h d hd
  | mu_inf _ h | nu_inf _ h => exact encode_branches_sizes_simple h

theorem encode_branches_sizes_simple {πstar π : Polarity} {Δ : KindingCtx}
    {S S' : List (Nat × TypeExpr)} {Ψ : SizeCtx}
    (h : EncodeBranches πstar π Δ S Ψ S') : EncodingSizesSimple Ψ := by
  cases h with
  | nil => simp [EncodingSizesSimple]
  | cons h₁ _ h₂ _ _ _ =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact encode_sizes_simple h₁ d hd
    · exact encode_branches_sizes_simple h₂ d hd

end

theorem positive_invScale_identity (Δ : KindingCtx) :
    Δ.invScalePol .pos = Δ := by
  cases Δ with
  | mk sizes types =>
    simp [KindingCtx.invScalePol, SizeCtx.invScalePol, Polarity.invComp]

theorem kind_forall_infty (Δ : KindingCtx) (i : SizeVar) (B : TypeExpr)
    (h : KindCheck (Δ.extType i .mixed (.lt .infty)) B .star) :
    KindCheck Δ (TypeExpr.forallSizeLt i .infty B) .star := by
  apply KindCheck.sub (κ := .star)
  · change KindInfer Δ (.app (.atom (.all (.lt .infty))) (.lam i .star B)) .star
    apply KindInfer.app (π := .pos) (κ := .arr .mixed (.lt .infty) .star)
    · exact KindInfer.all (KindWf.lt (by trivial))
    · rw [positive_invScale_identity]
      apply KindCheck.lam
      · exact KindWf.star _
      · exact h
  · exact SubKind.star _

theorem forallSizes_of_extended (Ψ : SizeCtx) :
    EncodingSizesSimple Ψ →
    ∀ (Δ : KindingCtx) (A : TypeExpr),
      KindCheck (Δ.extSizes Ψ) A .star →
      KindCheck Δ (TypeExpr.forallSizes Ψ A) .star := by
  induction Ψ with
  | nil =>
    intro h Δ A ha
    simpa [TypeExpr.forallSizes, KindingCtx.extSizes] using ha
  | cons d ds ih =>
    intro h Δ A ha
    have hd := h d (by simp)
    have htail : EncodingSizesSimple ds := by
      intro d' hd'
      exact h d' (by simp [hd'])
    cases d with
    | mk i p b =>
      simp only at hd
      rcases hd with ⟨rfl, rfl⟩
      change KindCheck Δ (TypeExpr.forallSizeLt i .infty (TypeExpr.forallSizes ds A)) .star
      apply kind_forall_infty
      apply ih htail
      simpa [KindingCtx.extType, KindingCtx.extSizes, List.append_assoc] using ha

end NishtAbel2024


namespace NishtAbel2024

/-- Extending a size list by membership also weakens the induced kinding
context. This preserves all existing type and size declarations. -/
theorem theorem7_extSizes_included (Δ : KindingCtx) {Ψ Ψ' : SizeCtx}
    (h : SizeIncluded Ψ Ψ') : KindingIncluded (Δ.extSizes Ψ) (Δ.extSizes Ψ') := by
  constructor
  · intro d hd
    simp only [KindingCtx.extSizes, List.mem_append] at hd ⊢
    exact hd.elim Or.inl (fun hd => Or.inr (h _ hd))
  · intro d hd
    simp only [KindingCtx.extSizes, List.mem_append] at hd ⊢
    rcases hd with hd | hd
    · exact Or.inl hd
    · obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
      exact Or.inr (List.mem_map.mpr ⟨d', h _ hd', rfl⟩)

/-- Every encoded constructor/destructor branch checks at functor kind in the
context containing all sizes generated by the branch list. -/
theorem theorem7_encodedBranches_kinded
    {πstar π : Polarity} {Δ : KindingCtx} {S S' : List (Nat × TypeExpr)} {Ψ : SizeCtx}
    (h : EncodeBranches πstar π Δ S Ψ S') :
    ∀ p ∈ S', KindCheck (Δ.extSizes Ψ) p.2 functorKind := by
  induction S' generalizing S Ψ with
  | nil =>
    intro p hp
    cases hp
  | cons head rest ih =>
    cases h with
    | cons henc hkind htail hdis₁ hdis₂ hdis₃ =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · apply theorem7_kindCheck_mono hkind
        apply theorem7_extSizes_included
        intro d hd
        exact List.mem_append.mpr (Or.inl hd)
      · apply theorem7_kindCheck_mono (ih htail p hp)
        apply theorem7_extSizes_included
        intro d hd
        exact List.mem_append.mpr (Or.inr hd)

end NishtAbel2024


namespace NishtAbel2024

/-- Mixed generated declarations are unchanged by inverse polarity scaling. -/
theorem theorem7_invComp_mixed (π : Polarity) : Polarity.invComp π .mixed = .mixed := by
  cases π <;> rfl

private theorem generated_invScale_sizes (Ψ : SizeCtx) (π : Polarity)
    (h : EncodingSizesSimple Ψ) : Ψ.invScalePol π = Ψ := by
  induction Ψ with
  | nil => rfl
  | cons d ds ih =>
    have hd := h d (by simp)
    have htail : EncodingSizesSimple ds := by
      intro e he
      exact h e (by simp [he])
    cases d with
    | mk x pol bound =>
      simp only at hd
      rcases hd with ⟨rfl, _⟩
      have ht := ih htail
      simp only [SizeCtx.invScalePol] at ht
      simp only [SizeCtx.invScalePol, List.map_cons, theorem7_invComp_mixed]
      exact congrArg (List.cons ⟨x, .mixed, bound⟩) ht

private theorem generated_invScale_types (Ψ : SizeCtx) (π : Polarity)
    (h : EncodingSizesSimple Ψ) :
    (Ψ.map (fun d => TyDecl.mk d.var d.pol (.lt d.bound))).map
        (fun d => { d with pol := Polarity.invComp π d.pol }) =
      Ψ.map (fun d => TyDecl.mk d.var d.pol (.lt d.bound)) := by
  induction Ψ with
  | nil => rfl
  | cons d ds ih =>
    have hd := h d (by simp)
    have htail : EncodingSizesSimple ds := by
      intro e he
      exact h e (by simp [he])
    cases d with
    | mk x pol bound =>
      simp only at hd
      rcases hd with ⟨rfl, _⟩
      simp [theorem7_invComp_mixed, ih htail]

/-- Generated sizes commute exactly with inverse scaling because their
polarities are mixed. -/
theorem theorem7_extSizes_invScale_eq (Δ : KindingCtx) (Ψ : SizeCtx) (π : Polarity)
    (h : EncodingSizesSimple Ψ) :
    (Δ.extSizes Ψ).invScalePol π = (Δ.invScalePol π).extSizes Ψ := by
  have hs := generated_invScale_sizes Ψ π h
  simp only [SizeCtx.invScalePol] at hs
  have hpol : ∀ d ∈ Ψ, Polarity.invComp π d.pol = d.pol := by
    intro d hd
    rw [(h d hd).1, theorem7_invComp_mixed]
  cases Δ with
  | mk sizes types =>
    simp [KindingCtx.extSizes, KindingCtx.invScalePol, SizeCtx.invScalePol,
      List.map_append, hs]
    exact hpol

theorem theorem7_extSizes_invScale_left (Δ : KindingCtx) (Ψ : SizeCtx) (π : Polarity)
    (h : EncodingSizesSimple Ψ) :
    KindingIncluded ((Δ.extSizes Ψ).invScalePol π) ((Δ.invScalePol π).extSizes Ψ) := by
  rw [theorem7_extSizes_invScale_eq Δ Ψ π h]
  exact ⟨fun _ hd => hd, fun _ hd => hd⟩

theorem theorem7_extSizes_invScale_right (Δ : KindingCtx) (Ψ : SizeCtx) (π : Polarity)
    (h : EncodingSizesSimple Ψ) :
    KindingIncluded ((Δ.invScalePol π).extSizes Ψ) ((Δ.extSizes Ψ).invScalePol π) := by
  rw [theorem7_extSizes_invScale_eq Δ Ψ π h]
  exact ⟨fun _ hd => hd, fun _ hd => hd⟩

/-- Simple-kind type binders and size-list extension commute as membership
inclusions, even when declaration names are duplicated or reorder. -/
theorem theorem7_extType_extSizes_left (Δ : KindingCtx) (Ψ : SizeCtx)
    (X : TyVar) (p : Polarity) (ι : SKind) :
    KindingIncluded ((Δ.extSizes Ψ).extType X p (Kind.ofSKind ι))
      ((Δ.extType X p (Kind.ofSKind ι)).extSizes Ψ) := by
  cases ι <;> simp [KindingIncluded, SizeIncluded, KindingCtx.extType,
    KindingCtx.extSizes, Kind.ofSKind, List.mem_append, or_comm]

theorem theorem7_extType_extSizes_right (Δ : KindingCtx) (Ψ : SizeCtx)
    (X : TyVar) (p : Polarity) (ι : SKind) :
    KindingIncluded ((Δ.extType X p (Kind.ofSKind ι)).extSizes Ψ)
      ((Δ.extSizes Ψ).extType X p (Kind.ofSKind ι)) := by
  cases ι <;> simp [KindingIncluded, SizeIncluded, KindingCtx.extType,
    KindingCtx.extSizes, Kind.ofSKind, List.mem_append, or_comm]

end NishtAbel2024

namespace NishtAbel2024

theorem lemma3_branch_vars {i : SizeVar} {S : List (Nat × TypeExpr)} {c : Nat} {F : TypeExpr}
    (hm : (c, F) ∈ S) (hi : i ∈ F.allSizeVars) : i ∈ allSizeVarsBranches S := by
  induction S with
  | nil => simp at hm
  | cons head rest ih =>
    rcases head with ⟨name, body⟩
    simp only [List.mem_cons] at hm
    simp only [allSizeVarsBranches, List.mem_append]
    rcases hm with h | h
    · cases h
      exact Or.inl hi
    · exact Or.inr (ih h)

theorem lemma3_occurs_mem {Δ : KindingCtx} {fk : FixKind} {i : SizeVar}
    {π : Polarity} {A : TypeExpr} (h : SizeOccursFixPol Δ fk i π A) :
    i ∈ A.allSizeVars := by
  induction h with
  | mu_top => simp [TypeExpr.allSizeVars, SizeExp.vars, SizeExp.var, SizeMin.vars,
      SizeMin.single, SizeMin.toList]
  | nu_top => simp [TypeExpr.allSizeVars, SizeExp.vars, SizeExp.var, SizeMin.vars,
      SizeMin.single, SizeMin.toList]
  | mu_branch hm ho ih => simp [TypeExpr.allSizeVars, lemma3_branch_vars hm ih]
  | nu_field hm ho ih => simp [TypeExpr.allSizeVars, lemma3_branch_vars hm ih]
  | lam ho ih => simpa [TypeExpr.allSizeVars] using ih
  | app_left hk ho ih => simp [TypeExpr.allSizeVars, ih]
  | app_right hk ho ih => simp [TypeExpr.allSizeVars, ih]

end NishtAbel2024

namespace NishtAbel2024

def Lemma3NoOccurs (fk : FixKind) (i : SizeVar) (A : TypeExpr) : Prop :=
  ∀ (Δ : KindingCtx) (π : Polarity), ¬ SizeOccursFixPol Δ fk i π A

theorem lemma3_no_of_absent {fk : FixKind} {i : SizeVar} {A : TypeExpr}
    (h : i ∉ A.allSizeVars) : Lemma3NoOccurs fk i A := by
  intro Δ π ho
  exact h (lemma3_occurs_mem ho)

theorem lemma3_no_app {fk : FixKind} {i : SizeVar} {F G : TypeExpr}
    (hf : Lemma3NoOccurs fk i F) (hg : Lemma3NoOccurs fk i G) :
    Lemma3NoOccurs fk i (.app F G) := by
  intro Δ π ho
  cases ho with
  | app_left hk ho => exact hf _ _ ho
  | app_right hk ho => exact hg _ _ ho

theorem lemma3_no_lam {fk : FixKind} {i : SizeVar} {X : TyVar} {ι : SKind} {F : TypeExpr}
    (hf : Lemma3NoOccurs fk i F) : Lemma3NoOccurs fk i (.lam X ι F) := by
  intro Δ π ho
  cases ho with | lam ho => exact hf _ _ ho

theorem lemma3_no_mu_other {i : SizeVar} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (hs : ∀ p ∈ S, Lemma3NoOccurs .nu i p.2) : Lemma3NoOccurs .nu i (.mu a S) := by
  intro Δ π ho
  cases ho with | mu_branch hm ho => exact hs _ hm _ _ ho

theorem lemma3_no_nu_other {i : SizeVar} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (hs : ∀ p ∈ S, Lemma3NoOccurs .mu i p.2) : Lemma3NoOccurs .mu i (.nu a S) := by
  intro Δ π ho
  cases ho with | nu_field hm ho => exact hs _ hm _ _ ho

theorem lemma3_no_mu_same {i : SizeVar} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (ha : ∀ n, a ≠ .var i n) (hs : ∀ p ∈ S, Lemma3NoOccurs .mu i p.2) :
    Lemma3NoOccurs .mu i (.mu a S) := by
  intro Δ π ho
  cases ho with
  | mu_top => exact ha _ rfl
  | mu_branch hm ho => exact hs _ hm _ _ ho

theorem lemma3_no_nu_same {i : SizeVar} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (ha : ∀ n, a ≠ .var i n) (hs : ∀ p ∈ S, Lemma3NoOccurs .nu i p.2) :
    Lemma3NoOccurs .nu i (.nu a S) := by
  intro Δ π ho
  cases ho with
  | nu_top => exact ha _ rfl
  | nu_field hm ho => exact hs _ hm _ _ ho

theorem lemma3_sizeVar_ne {i j : SizeVar} (h : i ≠ j) (n : Nat) :
    SizeExp.var j 0 ≠ .var i n := by
  intro heq
  have hx : j = i := congrArg (fun a : SizeExp =>
    match a with | .inf _ => 0 | .meet m => m.head.var) heq
  exact h hx.symm

end NishtAbel2024


namespace NishtAbel2024

/-- Polarized fixpoint occurrence is stable under membership-based weakening
of both size and type declarations in the kinding context. -/
theorem lemma3_occurs_mono {Δ : KindingCtx} {fk : FixKind} {i : SizeVar}
    {π : Polarity} {F : TypeExpr} (h : SizeOccursFixPol Δ fk i π F) :
    ∀ Δ', KindingIncluded Δ Δ' → SizeOccursFixPol Δ' fk i π F := by
  induction h with
  | mu_top =>
    intro Δ' hi
    exact .mu_top
  | nu_top =>
    intro Δ' hi
    exact .nu_top
  | mu_branch hm ho ih =>
    intro Δ' hi
    exact .mu_branch hm (ih Δ' hi)
  | nu_field hm ho ih =>
    intro Δ' hi
    exact .nu_field hm (ih Δ' hi)
  | lam ho ih =>
    intro Δ' hi
    exact .lam (ih _ (theorem7_ctx_extType hi _ _ _))
  | app_left hk ho ih =>
    intro Δ' hi
    exact .app_left (theorem7_kindInfer_mono hk Δ' hi) (ih Δ' hi)
  | app_right hk ho ih =>
    intro Δ' hi
    exact .app_right (theorem7_kindInfer_mono hk Δ' hi)
      (ih _ (theorem7_ctx_invScale hi _))

end NishtAbel2024


namespace NishtAbel2024

theorem lemma3_mu_occurs_from_branch {Δ : KindingCtx} {fk : FixKind}
    {i : SizeVar} {q : Polarity} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (h : ∃ p ∈ S, SizeOccursFixPol Δ fk i q p.2) :
    SizeOccursFixPol Δ fk i q (.mu a S) := by
  obtain ⟨⟨c, body⟩, hm, ho⟩ := h
  exact SizeOccursFixPol.mu_branch hm ho

theorem lemma3_nu_occurs_from_branch {Δ : KindingCtx} {fk : FixKind}
    {i : SizeVar} {q : Polarity} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (h : ∃ p ∈ S, SizeOccursFixPol Δ fk i q p.2) :
    SizeOccursFixPol Δ fk i q (.nu a S) := by
  obtain ⟨⟨d, body⟩, hm, ho⟩ := h
  exact SizeOccursFixPol.nu_field hm ho

/-- A same-kind outer fixpoint needs an additional index inequality;
an opposite-kind outer fixpoint does not. -/
theorem lemma3_no_mu_from_branches {fk : FixKind} {i : SizeVar}
    {a : SizeExp} {S : List (Nat × TypeExpr)}
    (ha : fk = .mu → ∀ n, a ≠ .var i n)
    (hs : ∀ p ∈ S, Lemma3NoOccurs fk i p.2) :
    Lemma3NoOccurs fk i (.mu a S) := by
  cases fk with
  | mu => exact lemma3_no_mu_same (ha rfl) hs
  | nu => exact lemma3_no_mu_other hs

theorem lemma3_no_nu_from_branches {fk : FixKind} {i : SizeVar}
    {a : SizeExp} {S : List (Nat × TypeExpr)}
    (ha : fk = .nu → ∀ n, a ≠ .var i n)
    (hs : ∀ p ∈ S, Lemma3NoOccurs fk i p.2) :
    Lemma3NoOccurs fk i (.nu a S) := by
  cases fk with
  | mu => exact lemma3_no_nu_other hs
  | nu => exact lemma3_no_nu_same (ha rfl) hs


end NishtAbel2024


namespace NishtAbel2024.Lemma3BranchCons

def other : FixKind → FixKind
  | .mu => .nu
  | .nu => .mu

def goal : FixKind → Polarity
  | .mu => .neg
  | .nu => .pos

def TypeInvariant (π : Polarity) (Δ : KindingCtx) (Ψ : SizeCtx) (A : TypeExpr) : Prop :=
  ∀ i ∈ Ψ.dom, ∃ fk q,
    Polarity.comp π q = goal fk ∧
    SizeOccursFixPol (Δ.extSizes Ψ) fk i q A ∧ Lemma3NoOccurs (other fk) i A

def BranchInvariant (π : Polarity) (Δ : KindingCtx) (Ψ : SizeCtx)
    (S : List (Nat × TypeExpr)) : Prop :=
  ∀ i ∈ Ψ.dom, ∃ fk q,
    Polarity.comp π q = goal fk ∧
    (∃ p ∈ S, SizeOccursFixPol (Δ.extSizes Ψ) fk i q p.2) ∧
    ∀ p ∈ S, Lemma3NoOccurs (other fk) i p.2

/-- Independent branch-list cons step. Cross-disjointness of generated sizes
and the opposite output branch supplies the universal-context absence claims. -/
theorem branch_cons (π : Polarity) (Δ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx)
    (nm : Nat) (F : TypeExpr) (S : List (Nat × TypeExpr))
    (hF : TypeInvariant π Δ Ψ₁ F) (hS : BranchInvariant π Δ Ψ₂ S)
    (hleft : List.Disjoint Ψ₁.dom (allSizeVarsBranches S))
    (hright : List.Disjoint Ψ₂.dom F.allSizeVars) :
    BranchInvariant π Δ (Ψ₁ ++ Ψ₂) ((nm, F) :: S) := by
  intro i hi
  simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
  rcases hi with hi | hi
  · obtain ⟨fk, q, hsign, ho, hno⟩ := hF i hi
    refine ⟨fk, q, hsign, ?_, ?_⟩
    · refine ⟨(nm, F), by simp, ?_⟩
      apply lemma3_occurs_mono ho
      exact theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inl hd))
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hno
      · apply lemma3_no_of_absent
        intro hm
        rcases p with ⟨n, A⟩
        exact (List.disjoint_left.mp hleft hi) (lemma3_branch_vars hp hm)
  · obtain ⟨fk, q, hsign, ⟨p, hp, ho⟩, hno⟩ := hS i hi
    refine ⟨fk, q, hsign, ?_, ?_⟩
    · refine ⟨p, by simp [hp], ?_⟩
      apply lemma3_occurs_mono ho
      exact theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inr hd))
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact lemma3_no_of_absent (List.disjoint_left.mp hright hi)
      · exact hno p hp

end NishtAbel2024.Lemma3BranchCons

namespace NishtAbel2024

def lemma3_other : FixKind → FixKind
  | .mu => .nu
  | .nu => .mu

def lemma3_goal : FixKind → Polarity
  | .mu => .neg
  | .nu => .pos

def Lemma3Type (π : Polarity) (Δ : KindingCtx) (Ψ : SizeCtx) (A : TypeExpr) : Prop :=
  ∀ i ∈ Ψ.dom, ∃ fk q,
    Polarity.comp π q = lemma3_goal fk ∧
    SizeOccursFixPol (Δ.extSizes Ψ) fk i q A ∧ Lemma3NoOccurs (lemma3_other fk) i A

def Lemma3Branches (π : Polarity) (Δ : KindingCtx) (Ψ : SizeCtx)
    (S : List (Nat × TypeExpr)) : Prop :=
  ∀ i ∈ Ψ.dom, ∃ fk q,
    Polarity.comp π q = lemma3_goal fk ∧
    (∃ p ∈ S, SizeOccursFixPol (Δ.extSizes Ψ) fk i q p.2) ∧
    ∀ p ∈ S, Lemma3NoOccurs (lemma3_other fk) i p.2

theorem lemma3_comp_exchange (π π' q : Polarity) :
    Polarity.comp π (Polarity.comp π' q) = Polarity.comp (Polarity.comp π' π) q := by
  cases π <;> cases π' <;> cases q <;> rfl

theorem lemma3_ctx_trans {Δ₁ Δ₂ Δ₃ : KindingCtx}
    (h₁ : KindingIncluded Δ₁ Δ₂) (h₂ : KindingIncluded Δ₂ Δ₃) :
    KindingIncluded Δ₁ Δ₃ := by
  exact ⟨fun d hd => h₂.1 d (h₁.1 d hd), fun d hd => h₂.2 d (h₁.2 d hd)⟩

theorem lemma3_strong {πstar π : Polarity} {Δ : KindingCtx} {A A' : TypeExpr} {Ψ : SizeCtx}
    (henc : EncodeType πstar π Δ A Ψ A') :
    πstar = .neg → Lemma3Type π Δ Ψ A' := by
  induction henc using EncodeType.rec
    (motive_2 := fun π Δ _ Ψ S' _ => πstar = .neg → Lemma3Branches π Δ Ψ S') with
  | unit => intro hπ i hi; simp [SizeCtx.dom] at hi
  | prod => intro hπ i hi; simp [SizeCtx.dom] at hi
  | arr => intro hπ i hi; simp [SizeCtx.dom] at hi
  | var => intro hπ i hi; simp [SizeCtx.dom] at hi
  | all => intro hπ i hi; simp [SizeCtx.dom] at hi
  | ex => intro hπ i hi; simp [SizeCtx.dom] at hi
  | @lam π₀ Δ₀ X ι F F' Ψ₀ hf he ih =>
    intro hπ i hi
    obtain ⟨fk, q, hsign, ho, hno⟩ := ih hπ i hi
    refine ⟨fk, q, hsign, ?_, lemma3_no_lam hno⟩
    apply SizeOccursFixPol.lam
    apply lemma3_occurs_mono ho
    exact theorem7_extType_extSizes_right _ _ _ _ _
  | @app π₀ πarg Δ₀ F F' G G' ι ι' Ψ₁ Ψ₂ hs hk harg heF heG hd₁ hd₂ hd₃ ihf ihg =>
    intro hπ i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hsign, ho, hno⟩ := ihf hπ i hi
      refine ⟨fk, q, hsign, ?_, ?_⟩
      · apply SizeOccursFixPol.app_left
        · apply theorem7_kindInfer_mono hk
          exact theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inl hd))
        · apply lemma3_occurs_mono ho
          exact theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inl hd))
      · apply lemma3_no_app hno
        apply lemma3_no_of_absent
        exact List.disjoint_left.mp hd₂ hi
    · obtain ⟨fk, q, hsign, ho, hno⟩ := ihg hπ i hi
      refine ⟨fk, Polarity.comp πarg q, ?_, ?_, ?_⟩
      · rw [lemma3_comp_exchange]
        exact hsign
      · apply SizeOccursFixPol.app_right
        · apply theorem7_kindInfer_mono hk
          exact theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inl hd))
        · apply lemma3_occurs_mono ho
          apply lemma3_ctx_trans (theorem7_extSizes_invScale_right _ _ _ (encode_sizes_simple heG))
          exact theorem7_ctx_invScale (theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inr hd))) _
      · apply lemma3_no_app ?_ hno
        apply lemma3_no_of_absent
        exact List.disjoint_left.mp hd₃ hi
  | @mu_fresh π₀ Δ₀ S S' Ψ₀ j hp hf₁ hf₂ hf₃ hb ih =>
    intro hπ i hi
    simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · refine ⟨.mu, .pos, ?_, SizeOccursFixPol.mu_top, ?_⟩
      · rw [hp, hπ]; rfl
      · apply lemma3_no_mu_other
        intro p hm
        apply lemma3_no_of_absent
        intro hmem
        exact hf₃ (lemma3_branch_vars hm hmem)
    · obtain ⟨fk, q, hsign, ⟨p, hm, ho⟩, hno⟩ := ih hπ i hi
      refine ⟨fk, q, hsign, ?_, ?_⟩
      · apply lemma3_mu_occurs_from_branch
        refine ⟨p, hm, ?_⟩
        apply lemma3_occurs_mono ho
        exact theorem7_extSizes_included _ (fun d hd => List.mem_cons_of_mem _ hd)
      · apply lemma3_no_mu_from_branches ?_ hno
        intro _ n
        apply lemma3_sizeVar_ne
        intro heq
        subst i
        exact hf₂ hi
  | mu_inf hp hb ih =>
    intro hπ i hi
    obtain ⟨fk, q, hsign, hw, hno⟩ := ih hπ i hi
    refine ⟨fk, q, hsign, lemma3_mu_occurs_from_branch hw, ?_⟩
    apply lemma3_no_mu_from_branches ?_ hno
    intro _ n h
    cases h
  | @nu_fresh π₀ Δ₀ R R' Ψ₀ j hp hf₁ hf₂ hf₃ hb ih =>
    intro hπ i hi
    simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · refine ⟨.nu, .pos, ?_, SizeOccursFixPol.nu_top, ?_⟩
      · rw [hp, hπ]; rfl
      · apply lemma3_no_nu_other
        intro p hm
        apply lemma3_no_of_absent
        intro hmem
        exact hf₃ (lemma3_branch_vars hm hmem)
    · obtain ⟨fk, q, hsign, ⟨p, hm, ho⟩, hno⟩ := ih hπ i hi
      refine ⟨fk, q, hsign, ?_, ?_⟩
      · apply lemma3_nu_occurs_from_branch
        refine ⟨p, hm, ?_⟩
        apply lemma3_occurs_mono ho
        exact theorem7_extSizes_included _ (fun d hd => List.mem_cons_of_mem _ hd)
      · apply lemma3_no_nu_from_branches ?_ hno
        intro _ n
        apply lemma3_sizeVar_ne
        intro heq
        subst i
        exact hf₂ hi
  | nu_inf hp hb ih =>
    intro hπ i hi
    obtain ⟨fk, q, hsign, hw, hno⟩ := ih hπ i hi
    refine ⟨fk, q, hsign, lemma3_nu_occurs_from_branch hw, ?_⟩
    apply lemma3_no_nu_from_branches ?_ hno
    intro _ n h
    cases h
  | nil => intro i hi; simp [SizeCtx.dom] at hi
  | @cons π₀ Δ₀ nm F F' rest rest' Ψ₁ Ψ₂ he hk ht hd₁ hd₂ hd₃ ihf iht =>
    rename_i hπ
    exact Lemma3BranchCons.branch_cons π₀ Δ₀ Ψ₁ Ψ₂ nm F' rest'
      (ihf hπ) (iht hπ) hd₂ hd₃
end NishtAbel2024

namespace NishtAbel2024

theorem lemma3_exact (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx)
    (henc : EncodeType .neg .pos Δ A Ψ A') :
    ∀ i ∈ Ψ.dom,
      (SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A' ∧
        ¬ SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A') ∨
      (SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A' ∧
        ¬ SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A') := by
  intro i hi
  obtain ⟨fk, q, hsign, ho, hno⟩ := lemma3_strong henc rfl i hi
  cases fk with
  | mu =>
    have hq : q = .neg := by cases q <;> simp_all [lemma3_goal, Polarity.comp]
    subst q
    exact Or.inl ⟨ho, hno _ _⟩
  | nu =>
    have hq : q = .pos := by cases q <;> simp_all [lemma3_goal, Polarity.comp]
    subst q
    exact Or.inr ⟨ho, hno _ _⟩

end NishtAbel2024

open NishtAbel2024

theorem solution :
    (∀ (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      EncodeType .neg .pos Δ A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A') ∨
        (SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A')) := by
  exact lemma3_exact

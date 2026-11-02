-- Prove2me | solution 1 for NishtAbel2024.theorem7_encoding_well_kinded
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:32:47.10135+00:00
-- url     : https://prove2.me/submissions/9d55f217-1c3f-4962-ae2e-08b7060268a6

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

/-- The embedded form of any simple kind is well formed in any size context. -/
theorem kindWf_of_simple (Ψ : SizeCtx) (ι : SKind) :
    KindWf Ψ (Kind.ofSKind ι) := by
  induction ι generalizing Ψ with
  | star | prop => exact KindWf.star _
  | arr π a b iha ihb => exact KindWf.arr (iha _) (ihb _)

/-- Subkinding is reflexive on the embedded simple kinds. -/
theorem subKind_of_simple_refl (Ψ : SizeCtx) (ι : SKind) :
    SubKind Ψ (Kind.ofSKind ι) (Kind.ofSKind ι) := by
  induction ι generalizing Ψ with
  | star | prop => exact SubKind.star _
  | arr π a b iha ihb =>
    apply SubKind.arr
    · cases π <;> rfl
    · exact iha _
    · exact ihb _

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

def PreservesKinds (A : TypeExpr) (Ψ : SizeCtx) (A' : TypeExpr) : Prop :=
  (∀ (Δ : KindingCtx) (ι : SKind), FwKindInfer Δ A ι →
    KindInfer (Δ.extSizes Ψ) A' (Kind.ofSKind ι)) ∧
  (∀ (Δ : KindingCtx) (ι : SKind), FwKindCheck Δ A ι →
    KindCheck (Δ.extSizes Ψ) A' (Kind.ofSKind ι))

def PreservesBranchKinds (S : List (Nat × TypeExpr)) (Ψ : SizeCtx)
    (S' : List (Nat × TypeExpr)) : Prop :=
  ∀ (Δ : KindingCtx), (∀ p ∈ S, FwKindCheck Δ p.2 fwFunctorSKind) →
    ∀ p ∈ S', KindCheck (Δ.extSizes Ψ) p.2 functorKind

theorem preserves_of_nonlam {A A' : TypeExpr} {Ψ : SizeCtx}
    (hinf : ∀ (Δ : KindingCtx) (ι : SKind), FwKindInfer Δ A ι →
      KindInfer (Δ.extSizes Ψ) A' (Kind.ofSKind ι))
    (hnon : ∀ X ι F, A ≠ .lam X ι F) : PreservesKinds A Ψ A' := by
  refine ⟨hinf, ?_⟩
  intro Δ ι h
  cases h with
  | infer h => exact .sub (hinf Δ _ h) (subKind_of_simple_refl _ _)
  | lam h => exact False.elim (hnon _ _ _ rfl)

theorem theorem7_fresh_sizeWf (Δ : KindingCtx) (i : SizeVar) (Ψ : SizeCtx) :
    SizeWf (Δ.extSizes (⟨i, .mixed, .infty⟩ :: Ψ)).sizes (.var i 0) := by
  intro sv hsv
  simp only [SizeMin.single, SizeMin.toList, List.mem_singleton] at hsv
  subst sv
  exact ⟨.infty, .mixed, by simp [KindingCtx.extSizes], rfl⟩

theorem theorem7_fresh_sizeWf_neg (Δ : KindingCtx) (i : SizeVar) (Ψ : SizeCtx) :
    SizeWf ((Δ.extSizes (⟨i, .mixed, .infty⟩ :: Ψ)).sizes.scalePol .neg) (.var i 0) := by
  intro sv hsv
  simp only [SizeMin.single, SizeMin.toList, List.mem_singleton] at hsv
  subst sv
  refine ⟨.infty, .mixed, ?_, rfl⟩
  simp [KindingCtx.extSizes, SizeCtx.scalePol, Polarity.comp]

theorem theorem7_all_infer {Δ : KindingCtx} {κ : Kind} {ι : SKind}
    (h : FwKindInfer Δ (.atom (.all κ)) ι) (Δ' : KindingCtx) :
    KindInfer Δ' (.atom (.all κ)) (Kind.ofSKind ι) := by
  cases h with | all => exact .all (kindWf_of_simple _ _)

theorem theorem7_ex_infer {Δ : KindingCtx} {κ : Kind} {ι : SKind}
    (h : FwKindInfer Δ (.atom (.ex κ)) ι) (Δ' : KindingCtx) :
    KindInfer Δ' (.atom (.ex κ)) (Kind.ofSKind ι) := by
  cases h with | ex => exact .ex (kindWf_of_simple _ _)

theorem theorem7_preservation {πstar π : Polarity} {Δ : KindingCtx}
    {A A' : TypeExpr} {Ψ : SizeCtx} (henc : EncodeType πstar π Δ A Ψ A') :
    PreservesKinds A Ψ A' := by
  induction henc using EncodeType.rec
    (motive_2 := fun _ _ S Ψ S' _ => PreservesBranchKinds S Ψ S') with
  | unit =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with | unit => exact .unit _
  | prod =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with | prod => exact .prod _
  | arr =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with | arr => exact .arr _
  | var =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with
    | var hm hp => apply KindInfer.var ?_ hp; simpa [KindingCtx.extSizes] using hm
  | all =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    exact theorem7_all_infer hsrc _
  | ex =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    exact theorem7_ex_infer hsrc _
  | lam hf he ih =>
    constructor
    · intro Δsource ι hsrc
      cases hsrc
    · intro Δsource ι hsrc
      cases hsrc with
      | infer hinf => cases hinf
      | lam hbody =>
        apply KindCheck.lam (kindWf_of_simple _ _)
        apply theorem7_kindCheck_mono (ih.2 _ _ hbody)
        exact theorem7_extType_extSizes_right _ _ _ _ _
  | app hsrcenc hhead harg heF heG hd₁ hd₂ hd₃ ihf ihg =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with
    | app hsF hsG =>
      refine KindInfer.app (theorem7_kindInfer_mono (ihf.1 _ _ hsF) _ ?_) ?_
      · exact theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inl hd))
      · have hg := ihg.2 _ _ hsG
        rw [← theorem7_extSizes_invScale_eq _ _ _ (encode_sizes_simple heG)] at hg
        apply theorem7_kindCheck_mono hg
        exact theorem7_ctx_invScale (theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inr hd))) _
  | mu_fresh hp hf₁ hf₂ hf₃ hb ih =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with
    | mu hbranches =>
      apply KindInfer.mu (theorem7_fresh_sizeWf _ _ _)
      intro p hp
      apply theorem7_kindCheck_mono (ih Δsource hbranches p hp)
      exact theorem7_extSizes_included _ (fun d hd => List.mem_cons_of_mem _ hd)
  | mu_inf hp hb ih =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with
    | mu hbranches => exact KindInfer.mu (by trivial) (ih Δsource hbranches)
  | nu_fresh hp hf₁ hf₂ hf₃ hb ih =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with
    | nu hbranches =>
      apply KindInfer.nu (theorem7_fresh_sizeWf_neg _ _ _)
      intro p hp
      apply theorem7_kindCheck_mono (ih Δsource hbranches p hp)
      exact theorem7_extSizes_included _ (fun d hd => List.mem_cons_of_mem _ hd)
  | nu_inf hp hb ih =>
    apply preserves_of_nonlam ?_ (by intro X ι F h; cases h)
    intro Δsource ι hsrc
    cases hsrc with
    | nu hbranches => exact KindInfer.nu (by trivial) (ih Δsource hbranches)
  | nil =>
    unfold PreservesBranchKinds
    intro Δsource hsrc p hp
    cases hp
  | cons he hk ht hd₁ hd₂ hd₃ ihf iht =>
    unfold PreservesBranchKinds at *
    intro Δsource hsrc p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · apply theorem7_kindCheck_mono (ihf.2 Δsource fwFunctorSKind (hsrc _ (List.Mem.head _)))
      exact theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inl hd))
    · apply theorem7_kindCheck_mono (iht Δsource (fun p hp => hsrc p (by simp [hp])) p hp)
      exact theorem7_extSizes_included _ (fun d hd => List.mem_append.mpr (Or.inr hd))

end NishtAbel2024

open NishtAbel2024

theorem solution :
    (∀ (πstar π : Polarity) (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      SizeCtxWf Δ.sizes →
      FwKindCheck Δ A .star →
      EncodeType πstar π Δ A Ψ A' →
      KindCheck Δ (TypeExpr.forallSizes Ψ A') .star) := by
  intro πstar π Δ A A' Ψ _hwf hsrc henc
  exact forallSizes_of_extended Ψ (encode_sizes_simple henc) Δ A'
    ((theorem7_preservation henc).2 Δ .star hsrc)

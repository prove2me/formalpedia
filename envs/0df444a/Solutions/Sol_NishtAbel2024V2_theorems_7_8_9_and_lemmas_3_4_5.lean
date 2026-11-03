-- Prove2me | solution 1 for NishtAbel2024V2.theorems_7_8_9_and_lemmas_3_4_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:38:28.043241+00:00
-- url     : https://prove2.me/submissions/6f602743-ca84-4fe2-8c56-4c4463a3ea05

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Inference

set_option autoImplicit false

namespace NishtAbel2024V2

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
  | lam hsh hw1 hw2 hb ih =>
    rename_i Δ' hi
    exact .lam hsh (theorem7_kindWf_mono (theorem7_sizeIncluded_map hi.1 _) hw1)
      (theorem7_kindWf_mono (theorem7_sizeIncluded_map hi.1 _) hw2)
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
  | lam hsh hw1 hw2 hb ih =>
    intro Δ' hi
    exact .lam hsh (theorem7_kindWf_mono (theorem7_sizeIncluded_map hi.1 _) hw1)
      (theorem7_kindWf_mono (theorem7_sizeIncluded_map hi.1 _) hw2)
      (ih _ (theorem7_ctx_extType hi _ _ _))

end NishtAbel2024V2


namespace NishtAbel2024V2

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
      · rfl
      · exact KindWf.star _
      · exact KindWf.lt (by trivial)
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

end NishtAbel2024V2


namespace NishtAbel2024V2

/-- The embedded form of any simple kind is well formed in any size context. -/
theorem simpleKindShape_eq_refinedKindShape_ofSKind (ι : SKind) :
    simpleKindShape ι = refinedKindShape (Kind.ofSKind ι) := by
  induction ι with
  | star | prop => rfl
  | arr _ a b iha ihb => simp [simpleKindShape, Kind.ofSKind, refinedKindShape, iha, ihb]

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

end NishtAbel2024V2


namespace NishtAbel2024V2

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

end NishtAbel2024V2


namespace NishtAbel2024V2

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

end NishtAbel2024V2

namespace NishtAbel2024V2

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
        apply KindCheck.lam (simpleKindShape_eq_refinedKindShape_ofSKind _)
          (kindWf_of_simple _ _) (kindWf_of_simple _ _)
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

end NishtAbel2024V2


namespace NishtAbel2024V2

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

end NishtAbel2024V2

namespace NishtAbel2024V2

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

end NishtAbel2024V2


namespace NishtAbel2024V2

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

end NishtAbel2024V2


namespace NishtAbel2024V2

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


end NishtAbel2024V2


namespace NishtAbel2024V2.Lemma3BranchCons

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

end NishtAbel2024V2.Lemma3BranchCons

namespace NishtAbel2024V2

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
end NishtAbel2024V2

namespace NishtAbel2024V2

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

end NishtAbel2024V2



namespace NishtAbel2024V2

/-! ## Theorems 8 & 9: Pattern and Copattern Spine Elaboration -/

mutual

theorem spine_subst_self_789 (X : TyVar) (F : TypeExpr) :
    TypeExpr.substTyVar X (.atom (.var X)) F = F := by
  cases F with
  | atom K =>
    cases K with
    | var Y =>
      simp only [TypeExpr.substTyVar]
      split <;> simp_all
    | size _ | unit | prod | arr | all _ | ex _ => rfl
  | lam Y ι F =>
    simp only [TypeExpr.substTyVar]
    split
    · rfl
    · rw [spine_subst_self_789 X F]
  | app F G =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_self_789 X F, spine_subst_self_789 X G]
  | mu a S =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_branches_self_789 X S]
  | nu a R =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_branches_self_789 X R]
termination_by sizeOf F

theorem spine_subst_branches_self_789 (X : TyVar) (S : List (Nat × TypeExpr)) :
    TypeExpr.substTyVarBranches X (.atom (.var X)) S = S := by
  cases S with
  | nil => rfl
  | cons p rest =>
    rcases p with ⟨name, body⟩
    simp only [TypeExpr.substTyVarBranches]
    rw [spine_subst_self_789 X body, spine_subst_branches_self_789 X rest]
termination_by sizeOf S

end

theorem spine_normApp_self_789 (X : TyVar) (ι : SKind) (B : TypeExpr) :
    (TypeExpr.lam X ι B).normApp (.atom (.var X)) = B :=
  spine_subst_self_789 X B

theorem inferPat_elaborates_789 {Δ₀ : KindingCtx} {p p' : Pat} {A : TypeExpr}
    {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx}
    (h : InferPat Δ₀ p A Γ Δ Ψ p') : PatTyping Δ₀ Δ Γ p' A := by
  induction h with
  | var Δ₀ x _ => exact PatTyping.var Δ₀ x _
  | unit Δ₀ => exact PatTyping.unit Δ₀
  | pair _ _ _ _ ih₁ ih₂ => exact PatTyping.pair ih₁ ih₂
  | cons j hlookup _ _ _ _ _ ih =>
    apply PatTyping.cons j hlookup
    apply PatTyping.tyPack
    simpa [TypeExpr.existsSizeLt, spine_normApp_self_789] using ih
  | tyPack _ _ ih => exact PatTyping.tyPack ih

theorem inferSpine_elaborates_789 {Δ₀ : KindingCtx} {qs qs' : PatSpine} {A C : TypeExpr}
    {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx}
    (h : InferSpine Δ₀ qs A C Γ Δ Ψ qs') : SpineTyping Δ₀ Δ Γ A qs' C := by
  induction h with
  | nil Δ₀ A => exact SpineTyping.nil Δ₀ A
  | pat hp _ _ _ ih => exact SpineTyping.pat (inferPat_elaborates_789 hp) ih
  | proj j hlookup _ _ _ _ _ ih =>
    apply SpineTyping.proj j hlookup
    apply SpineTyping.tyVar
    simpa [TypeExpr.forallSizeLt, spine_normApp_self_789] using ih
  | tyApp _ _ ih => exact SpineTyping.tyVar ih

/-! ## Repaired Lemmas 4 & 5: Kinding-Aware Rigid Variable Polarity Classification -/

def SizeDeclUse789 (Ψ : SizeCtx) (i : SizeVar) (q : Polarity) : Prop :=
  ∃ a p, SizeDecl.mk i p a ∈ Ψ ∧ Polarity.le p q = true

theorem inv_le_comp_789 (p r q : Polarity) :
    Polarity.le (Polarity.invComp p r) q = Polarity.le r (Polarity.comp p q) := by
  cases p <;> cases r <;> cases q <;> rfl

theorem sizeWf_sizeDeclUse_789 {Ψ : SizeCtx} {a : SizeExp} {i : SizeVar}
    (hw : SizeWf Ψ a) (hi : i ∈ a.vars) : SizeDeclUse789 Ψ i .pos :=
  match a with
  | .inf _ => False.elim (List.not_mem_nil hi)
  | .meet _m =>
    let ⟨sv, hsv, he⟩ := List.mem_map.mp (List.mem_eraseDups.mp hi)
    let ⟨b, p, hd, hp⟩ := hw sv hsv
    ⟨b, p, he ▸ hd, hp⟩

theorem sizeDeclUse_inv_789 {Ψ : SizeCtx} {i : SizeVar} {p q : Polarity}
    (h : SizeDeclUse789 (Ψ.invScalePol p) i q) :
    SizeDeclUse789 Ψ i (Polarity.comp p q) :=
  match h with
  | ⟨_a, r, hm, hl⟩ =>
    match List.mem_map.mp hm with
    | ⟨d, hd, he⟩ =>
      have hv : d.var = i := congrArg SizeDecl.var he
      have hp : Polarity.invComp p d.pol = r := congrArg SizeDecl.pol he
      have hl' : Polarity.le (Polarity.invComp p d.pol) q = true :=
        (congrArg (fun v => Polarity.le v q) hp).trans hl
      ⟨d.bound, d.pol, hv ▸ hd, (inv_le_comp_789 p d.pol q) ▸ hl'⟩

theorem sizeDeclUse_ext_789 {Δ : KindingCtx} {Y i : Nat}
    {p q : Polarity} {κ : Kind} (hne : Y ≠ i)
    (h : SizeDeclUse789 (Δ.extType Y p κ).sizes i q) :
    SizeDeclUse789 Δ.sizes i q := by
  cases κ <;> simpa [KindingCtx.extType, SizeDeclUse789, Ne.symm hne] using h

theorem negative_scale_usable_789 (p : Polarity) :
    Polarity.le (Polarity.comp .neg p) .pos = Polarity.le p .neg := by
  cases p <;> rfl

theorem sizeDeclUse_neg_789 {Ψ : SizeCtx} {i : SizeVar}
    (h : SizeDeclUse789 (Ψ.scalePol .neg) i .pos) : SizeDeclUse789 Ψ i .neg :=
  match h with
  | ⟨_a, r, hm, hl⟩ =>
    match List.mem_map.mp hm with
    | ⟨d, hd, he⟩ =>
      have hv : d.var = i := congrArg SizeDecl.var he
      have hp : Polarity.comp .neg d.pol = r := congrArg SizeDecl.pol he
      have hl' : Polarity.le (Polarity.comp .neg d.pol) .pos = true :=
        (congrArg (fun v => Polarity.le v .pos) hp).trans hl
      ⟨d.bound, d.pol, hv ▸ hd, negative_scale_usable_789 d.pol ▸ hl'⟩

theorem checkUse_sizeDeclaration_789 {Δ : KindingCtx} {F : TypeExpr} {κ : Kind}
    {fk : FixKind} {i : SizeVar} {q : Polarity}
    (h : CheckUse Δ F κ fk i q) : SizeDeclUse789 Δ.sizes i q := by
  induction h using CheckUse.rec
    (motive_1 := fun Δ _ _ _ i q _ => SizeDeclUse789 Δ.sizes i q) with
  | muIndex hk hi =>
    cases hk with
    | mu hw _ => exact sizeWf_sizeDeclUse_789 hw hi
  | nuIndex hk hi =>
    cases hk with
    | nu hw _ => exact sizeDeclUse_neg_789 (sizeWf_sizeDeclUse_789 hw hi)
  | muBranch _ _ _ ih | nuBranch _ _ _ ih | appLeft _ _ _ ih | sub _ _ _ ih => exact ih
  | appRight _ _ _ ih => exact sizeDeclUse_inv_789 ih
  | lam hn _ _ _ ih => exact sizeDeclUse_ext_789 hn ih

theorem sizeDeclUse_polarity_789 {Ψ : SizeCtx} {i : SizeVar} {p q : Polarity}
    {a : SizeExp} (h : SizeDeclUse789 Ψ i q) (hunique : Ψ.dom.Nodup)
    (hd : SizeDecl.mk i p a ∈ Ψ) : Polarity.le p q = true :=
  match h with
  | ⟨b, r, hm, hr⟩ =>
    have he : SizeDecl.mk i r b = SizeDecl.mk i p a :=
      List.inj_on_of_nodup_map hunique hm hd rfl
    (congrArg (fun v => Polarity.le v q) (congrArg SizeDecl.pol he)) ▸ hr

theorem checkUse_positive_size_declaration_789 {Δ : KindingCtx} {F : TypeExpr} {κ : Kind}
    {fk : FixKind} {i : SizeVar} {q : Polarity} {a : SizeExp}
    (h : CheckUse Δ F κ fk i q) (hunique : Δ.sizes.dom.Nodup)
    (hd : SizeDecl.mk i .pos a ∈ Δ.sizes) : q = .pos ∨ q = .top := by
  have hp := sizeDeclUse_polarity_789 (checkUse_sizeDeclaration_789 h) hunique hd
  cases q <;> simp_all [Polarity.le]

theorem checkUse_negative_size_declaration_789 {Δ : KindingCtx} {F : TypeExpr} {κ : Kind}
    {fk : FixKind} {i : SizeVar} {q : Polarity} {a : SizeExp}
    (h : CheckUse Δ F κ fk i q) (hunique : Δ.sizes.dom.Nodup)
    (hd : SizeDecl.mk i .neg a ∈ Δ.sizes) : q = .neg ∨ q = .top := by
  have hp := sizeDeclUse_polarity_789 (checkUse_sizeDeclaration_789 h) hunique hd
  cases q <;> simp_all [Polarity.le]

theorem theorems_7_8_9_and_lemmas_3_4_5 :
    (∀ (πstar π : Polarity) (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      SizeCtxWf Δ.sizes →
      FwKindCheck Δ A .star →
      EncodeType πstar π Δ A Ψ A' →
      KindCheck Δ (TypeExpr.forallSizes Ψ A') .star) ∧
    (∀ (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      EncodeType .neg .pos Δ A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A') ∨
        (SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A')) ∧
    (∀ (Δ₀ : KindingCtx) (p p' : Pat) (A : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferPat Δ₀ p A Γ Δ Ψ p' →
      PatTyping Δ₀ Δ Γ p' A) ∧
    (∀ (Δ₀ : KindingCtx) (qs qs' : PatSpine) (A C : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferSpine Δ₀ qs A C Γ Δ Ψ qs' →
      SpineTyping Δ₀ Δ Γ A qs' C) ∧
    (∀ (Δ : KindingCtx) (B : TypeExpr) (κ : Kind) (fk : FixKind)
       (i : SizeVar) (q : Polarity) (a : SizeExp),
      Δ.sizes.dom.Nodup →
      SizeDecl.mk i .pos a ∈ Δ.sizes →
      CheckUse Δ B κ fk i q →
      q = .pos ∨ q = .top) ∧
    (∀ (Δ : KindingCtx) (F : TypeExpr) (κ : Kind) (fk : FixKind)
       (i : SizeVar) (q : Polarity) (a : SizeExp),
      Δ.sizes.dom.Nodup →
      ((SizeDecl.mk i .pos a ∈ Δ.sizes → CheckUse Δ F κ fk i q → q = .pos ∨ q = .top) ∧
       (SizeDecl.mk i .neg a ∈ Δ.sizes → CheckUse Δ F κ fk i q → q = .neg ∨ q = .top))) := by
  refine ⟨?_, lemma3_exact, ?_, ?_, ?_, ?_⟩
  · intro πstar π Δ A A' Ψ _hwf hsrc henc
    exact forallSizes_of_extended Ψ (encode_sizes_simple henc) Δ A'
      ((theorem7_preservation henc).2 Δ .star hsrc)
  · intro Δ₀ p p' A Γ Δ Ψ h
    exact inferPat_elaborates_789 h
  · intro Δ₀ qs qs' A C Γ Δ Ψ h
    exact inferSpine_elaborates_789 h
  · intro Δ B κ fk i q a hnodup hd huse
    exact checkUse_positive_size_declaration_789 huse hnodup hd
  · intro Δ F κ fk i q a hnodup
    exact ⟨fun hd huse => checkUse_positive_size_declaration_789 huse hnodup hd,
           fun hd huse => checkUse_negative_size_declaration_789 huse hnodup hd⟩

end NishtAbel2024V2

open NishtAbel2024V2

theorem solution :
    (∀ (πstar π : Polarity) (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      SizeCtxWf Δ.sizes →
      FwKindCheck Δ A .star →
      EncodeType πstar π Δ A Ψ A' →
      KindCheck Δ (TypeExpr.forallSizes Ψ A') .star) ∧
    (∀ (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      EncodeType .neg .pos Δ A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A') ∨
        (SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A')) ∧
    (∀ (Δ₀ : KindingCtx) (p p' : Pat) (A : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferPat Δ₀ p A Γ Δ Ψ p' →
      PatTyping Δ₀ Δ Γ p' A) ∧
    (∀ (Δ₀ : KindingCtx) (qs qs' : PatSpine) (A C : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferSpine Δ₀ qs A C Γ Δ Ψ qs' →
      SpineTyping Δ₀ Δ Γ A qs' C) ∧
    (∀ (Δ : KindingCtx) (B : TypeExpr) (κ : Kind) (fk : FixKind)
       (i : SizeVar) (q : Polarity) (a : SizeExp),
      Δ.sizes.dom.Nodup →
      SizeDecl.mk i .pos a ∈ Δ.sizes →
      CheckUse Δ B κ fk i q →
      q = .pos ∨ q = .top) ∧
    (∀ (Δ : KindingCtx) (F : TypeExpr) (κ : Kind) (fk : FixKind)
       (i : SizeVar) (q : Polarity) (a : SizeExp),
      Δ.sizes.dom.Nodup →
      ((SizeDecl.mk i .pos a ∈ Δ.sizes → CheckUse Δ F κ fk i q → q = .pos ∨ q = .top) ∧
       (SizeDecl.mk i .neg a ∈ Δ.sizes → CheckUse Δ F κ fk i q → q = .neg ∨ q = .top))) := NishtAbel2024V2.theorems_7_8_9_and_lemmas_3_4_5

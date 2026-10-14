-- Prove2me | solution 1 for MoritaEquiv.morita_imp_categorical
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-13T21:17:14.411151+00:00
-- url     : https://prove2.me/submissions/d9245a53-f2fd-45eb-af8e-70a46f572ea0

import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_proj_faithful
import Theorems.Thm_MoritaEquiv_proj_full
import Theorems.Thm_MoritaEquiv_expansion_exists_unique
import Theorems.Thm_MoritaEquiv_Sig_Hom_IsRenaming_exists_formula_pullback
import Theorems.Thm_MoritaEquiv_ElemEmb_exists_of_sortwise_equiv

open CategoryTheory

namespace MoritaEquiv
namespace MIC

theorem elemEmb_ext {L : Sig} {M N : Str L} {f g : ElemEmb M N} (h : f.toFun = g.toFun) :
    f = g := by
  cases f; cases g; cases h; rfl

/-! ### Step 1: each Morita extension gives an equivalence `Π : Mod(T⁺) ≌ Mod(T)` -/

theorem proj_isEquivalence {L : Sig} {T : Theory L} (D : MoritaData L T) :
    D.proj.IsEquivalence := by
  haveI := proj_faithful D
  haveI := proj_full D
  haveI : D.proj.EssSurj := ⟨fun M => (expansion_exists_unique D M).1⟩
  exact { }

theorem reach_equiv {L₁ : Sig} {T₁ : Theory L₁} {L₂ : Sig} {T₂ : Theory L₂}
    (h : MoritaReach T₁ T₂) : Nonempty (Model T₁ ≌ Model T₂) := by
  induction h with
  | refl T => exact ⟨CategoryTheory.Equivalence.refl⟩
  | step D _ ih =>
    obtain ⟨e⟩ := ih
    haveI := proj_isEquivalence D
    exact ⟨D.proj.asEquivalence.symm.trans e⟩

/-! ### Step 2: a renaming `F` with `T₂' ⊨ ↔ T₁'`-reduct gives `Mod(T₂') ≌ Mod(T₁')` -/

variable {L₁ L₂ : Sig} {F : L₁.Hom L₂} {T₁ : Theory L₁} {T₂ : Theory L₂}

/-- the reduct functor along `F` -/
def redF (hT : ∀ M : Str L₂, M.IsModel T₂ ↔ (M.reduct F).IsModel T₁) : Model T₂ ⥤ Model T₁ where
  obj M := ⟨M.str.reduct F, (hT M.str).1 M.isModel⟩
  map {M N} h :=
    { toFun := fun s => h.toFun (F.onSrt s)
      map_formula := fun φ v =>
        (Formula.realize_onFormula F N.str φ _).symm.trans
          ((h.map_formula (φ.onFormula F) v).trans (Formula.realize_onFormula F M.str φ v)) }
  map_id _ := rfl
  map_comp _ _ := rfl

theorem redF_faithful (hF : F.IsRenaming)
    (hT : ∀ M : Str L₂, M.IsModel T₂ ↔ (M.reduct F).IsModel T₁) : (redF hT).Faithful := by
  constructor
  intro M N f g h
  apply elemEmb_ext
  funext s
  obtain ⟨t, rfl⟩ := hF.srt.2 s
  exact congrFun (congrArg ElemEmb.toFun h) t

noncomputable def liftFun (hF : F.IsRenaming) {M N : Str L₂}
    (g : ElemEmb (M.reduct F) (N.reduct F)) (s : L₂.Srt) (x : M.carrier s) : N.carrier s :=
  cast (congrArg N.carrier ((Equiv.ofBijective _ hF.srt).apply_symm_apply s))
    (g.toFun ((Equiv.ofBijective _ hF.srt).symm s)
      (cast (congrArg M.carrier ((Equiv.ofBijective _ hF.srt).apply_symm_apply s)).symm x))

theorem cast_aux (hF : F.IsRenaming) {M N : Str L₂} (g : ElemEmb (M.reduct F) (N.reduct F))
    {t t' : L₁.Srt} (h : F.onSrt t' = F.onSrt t) (x : M.carrier (F.onSrt t)) :
    cast (congrArg N.carrier h) (g.toFun t' (cast (congrArg M.carrier h).symm x)) =
      g.toFun t x := by
  obtain rfl := hF.srt.1 h
  rfl

theorem liftFun_apply (hF : F.IsRenaming) {M N : Str L₂} (g : ElemEmb (M.reduct F) (N.reduct F))
    (t : L₁.Srt) (x : M.carrier (F.onSrt t)) : liftFun hF g (F.onSrt t) x = g.toFun t x :=
  cast_aux hF g ((Equiv.ofBijective _ hF.srt).apply_symm_apply (F.onSrt t)) x

theorem lift_aux (hF : F.IsRenaming) {M N : Str L₂} (g : ElemEmb (M.reduct F) (N.reduct F))
    {n : ℕ} (Γ₀ : Fin n → L₁.Srt) (φ : Formula L₂ (F.onSrt ∘ Γ₀))
    (v : (i : Fin n) → M.carrier (F.onSrt (Γ₀ i))) :
    φ.Realize N (fun i => liftFun hF g (F.onSrt (Γ₀ i)) (v i)) ↔ φ.Realize M v := by
  obtain ⟨ψ, hψ⟩ := hF.exists_formula_pullback Γ₀ φ
  rw [hψ N, hψ M, Formula.realize_onFormula, Formula.realize_onFormula]
  have : (fun i => liftFun hF g (F.onSrt (Γ₀ i)) (v i)) = fun i => g.toFun (Γ₀ i) (v i) :=
    funext fun i => liftFun_apply hF g (Γ₀ i) (v i)
  rw [this]
  exact g.map_formula ψ v

noncomputable def lift (hF : F.IsRenaming) {M N : Str L₂}
    (g : ElemEmb (M.reduct F) (N.reduct F)) : ElemEmb M N where
  toFun := liftFun hF g
  map_formula := by
    intro n Γ φ v
    obtain ⟨Γ₀, rfl⟩ : ∃ Γ₀ : Fin n → L₁.Srt, F.onSrt ∘ Γ₀ = Γ :=
      ⟨fun i => (Equiv.ofBijective _ hF.srt).symm (Γ i),
        funext fun i => (Equiv.ofBijective _ hF.srt).apply_symm_apply (Γ i)⟩
    exact lift_aux hF g Γ₀ φ v

theorem redF_full (hF : F.IsRenaming)
    (hT : ∀ M : Str L₂, M.IsModel T₂ ↔ (M.reduct F).IsModel T₁) : (redF hT).Full := by
  constructor
  intro M N g
  refine ⟨(lift hF (M := M.str) (N := N.str) g : ElemEmb M.str N.str), ?_⟩
  apply elemEmb_ext
  funext t x
  exact liftFun_apply hF g t x

/-- the pushforward structure along a renaming (as in `exists_reduct_biembedding`) -/
noncomputable def push (hF : F.IsRenaming) (N : Str L₁) : Str L₂ where
  carrier s := N.carrier ((Equiv.ofBijective _ hF.srt).symm s)
  funMap {m dom s} f xs :=
    N.funMap ((Equiv.ofBijective _ (hF.func (dom := (Equiv.ofBijective _ hF.srt).symm ∘ dom)
      (s := (Equiv.ofBijective _ hF.srt).symm s))).symm
      (cast (by
        have h1 : F.onSrt ∘ ((Equiv.ofBijective _ hF.srt).symm ∘ dom) = dom :=
          funext fun j => (Equiv.ofBijective _ hF.srt).apply_symm_apply (dom j)
        have h2 : F.onSrt ((Equiv.ofBijective _ hF.srt).symm s) = s :=
          (Equiv.ofBijective _ hF.srt).apply_symm_apply s
        rw [h1, h2]) f)) xs
  relMap {m dom} r xs :=
    N.relMap ((Equiv.ofBijective _ (hF.rel (dom := (Equiv.ofBijective _ hF.srt).symm ∘ dom))).symm
      (cast (by
        have h1 : F.onSrt ∘ ((Equiv.ofBijective _ hF.srt).symm ∘ dom) = dom :=
          funext fun j => (Equiv.ofBijective _ hF.srt).apply_symm_apply (dom j)
        rw [h1]) r)) xs
  nonempty _ := N.nonempty _

theorem funMap_cast (hF : F.IsRenaming) (N : Str L₁) {m : ℕ} :
    ∀ {dom₁ dom : Fin m → L₁.Srt} {s₁ s : L₁.Srt} (hd : dom₁ = dom) (hs : s₁ = s)
      (f₁ : L₁.Func m dom₁ s₁) (f : L₁.Func m dom s)
      (H : L₂.Func m (F.onSrt ∘ dom) (F.onSrt s) = L₂.Func m (F.onSrt ∘ dom₁) (F.onSrt s₁)),
      F.onFunc f₁ = cast H (F.onFunc f) →
      ∀ (xs : (j : Fin m) → N.carrier (dom₁ j)),
      cast (congrArg N.carrier hs) (N.funMap f₁ xs) =
        N.funMap f (fun j => cast (congrArg N.carrier (congrFun hd j)) (xs j)) := by
  intro dom₁ dom s₁ s hd hs f₁ f H hf xs
  subst hd hs
  have : f₁ = f := (hF.func).1 hf
  subst this
  rfl

theorem relMap_cast (hF : F.IsRenaming) (N : Str L₁) {m : ℕ} :
    ∀ {dom₁ dom : Fin m → L₁.Srt} (hd : dom₁ = dom)
      (r₁ : L₁.Rel m dom₁) (r : L₁.Rel m dom)
      (H : L₂.Rel m (F.onSrt ∘ dom) = L₂.Rel m (F.onSrt ∘ dom₁)),
      F.onRel r₁ = cast H (F.onRel r) →
      ∀ (xs : (j : Fin m) → N.carrier (dom₁ j)),
      N.relMap r₁ xs ↔ N.relMap r (fun j => cast (congrArg N.carrier (congrFun hd j)) (xs j)) := by
  intro dom₁ dom hd r₁ r H hr xs
  subst hd
  have : r₁ = r := (hF.rel).1 hr
  subst this
  rfl

/-- the reduct of the pushforward is strongly isomorphic to `N`, via sortwise casts -/
theorem push_iso (hF : F.IsRenaming) (N : Str L₁) :
    ∃ (E : ∀ s, ((push hF N).reduct F).carrier s ≃ N.carrier s)
      (h : ElemEmb ((push hF N).reduct F) N) (h' : ElemEmb N ((push hF N).reduct F)),
      (∀ s x, h.toFun s x = E s x) ∧ (∀ s x, h'.toFun s x = (E s).symm x) := by
  let e := Equiv.ofBijective _ hF.srt
  have hsa : ∀ s, e.symm (F.onSrt s) = s := fun s => e.symm_apply_apply s
  let E : ∀ s, ((push hF N).reduct F).carrier s ≃ N.carrier s :=
    fun s => Equiv.cast (congrArg N.carrier (hsa s))
  have hf : ∀ {m : ℕ} {dom : Fin m → L₁.Srt} {s : L₁.Srt} (f : L₁.Func m dom s)
      (xs : (j : Fin m) → ((push hF N).reduct F).carrier (dom j)),
      E s (((push hF N).reduct F).funMap f xs) = N.funMap f (fun j => E _ (xs j)) := by
    intro m dom s f xs
    exact funMap_cast hF N (funext fun j => hsa (dom j)) (hsa s) _ f _
      ((Equiv.ofBijective_apply_symm_apply _ _ _).trans rfl) xs
  have hr : ∀ {m : ℕ} {dom : Fin m → L₁.Srt} (r : L₁.Rel m dom)
      (xs : (j : Fin m) → ((push hF N).reduct F).carrier (dom j)),
      N.relMap r (fun j => E _ (xs j)) ↔ ((push hF N).reduct F).relMap r xs := by
    intro m dom r xs
    exact (relMap_cast hF N (funext fun j => hsa (dom j)) _ r _
      ((Equiv.ofBijective_apply_symm_apply _ _ _).trans rfl) xs).symm
  obtain ⟨h, hh⟩ := ElemEmb.exists_of_sortwise_equiv E hf hr
  obtain ⟨h', hh'⟩ := ElemEmb.exists_of_sortwise_equiv (A := N) (B := (push hF N).reduct F)
    (fun s => (E s).symm)
    (fun {m dom s} f xs => by
      apply (E s).injective
      rw [Equiv.apply_symm_apply, hf]
      congr 1; funext j; simp)
    (fun {m dom} r xs => by
      rw [← hr]; congr!; simp)
  exact ⟨E, h, h', hh, hh'⟩

theorem redF_essSurj (hF : F.IsRenaming)
    (hT : ∀ M : Str L₂, M.IsModel T₂ ↔ (M.reduct F).IsModel T₁) : (redF hT).EssSurj := by
  constructor
  intro N
  obtain ⟨E, h, h', hh, hh'⟩ := push_iso hF N.str
  have hmod : ((push hF N.str).reduct F).IsModel T₁ := fun A hA v =>
    (h.map_formula A.φ v).1 (N.isModel A hA _)
  let M : Model T₂ := ⟨push hF N.str, (hT _).2 hmod⟩
  refine ⟨M, ⟨{ hom := h, inv := h', hom_inv_id := ?_, inv_hom_id := ?_ }⟩⟩
  · apply elemEmb_ext
    funext s x
    show h'.toFun s (h.toFun s x) = x
    exact (hh' s _).trans ((congrArg (E s).symm (hh s x)).trans ((E s).symm_apply_apply x))
  · apply elemEmb_ext
    funext s x
    show h.toFun s (h'.toFun s x) = x
    exact (hh s _).trans ((congrArg (E s) (hh' s x)).trans ((E s).apply_symm_apply x))

theorem redF_isEquivalence (hF : F.IsRenaming)
    (hT : ∀ M : Str L₂, M.IsModel T₂ ↔ (M.reduct F).IsModel T₁) : (redF hT).IsEquivalence := by
  haveI := redF_faithful hF hT
  haveI := redF_full hF hT
  haveI := redF_essSurj hF hT
  exact { }

/-! ### Main theorem -/

theorem mic_main {L₁ L₂ : Sig} (T₁ : Theory L₁) (T₂ : Theory L₂)
    (h : MoritaEquivalent T₁ T₂) : CategoricallyEquivalent T₁ T₂ := by
  obtain ⟨L₁', L₂', T₁', T₂', F, h1, h2, hF, hT⟩ := h
  obtain ⟨e1⟩ := reach_equiv h1
  obtain ⟨e2⟩ := reach_equiv h2
  haveI := redF_isEquivalence hF hT
  exact ⟨e1.trans ((redF hT).asEquivalence.symm.trans e2.symm)⟩

end MIC
end MoritaEquiv

open MoritaEquiv in
theorem solution {L₁ L₂ : Sig} (T₁ : Theory L₁) (T₂ : Theory L₂)
    (h : MoritaEquivalent T₁ T₂) : CategoricallyEquivalent T₁ T₂ :=
  MoritaEquiv.MIC.mic_main T₁ T₂ h

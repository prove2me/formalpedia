-- Prove2me | solution 1 for JMMS.isAmenable_iff_isExtensivelyAmenable_of_le_IET
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T10:57:49.783021+00:00
-- url     : https://prove2.me/submissions/99b4b881-4a87-4915-8168-a0d5d84813bf

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_mem_IET_iff
import Theorems.Thm_JMMS_isAmenable_of_isAmenable_inf_range_inr
import Theorems.Thm_JMMS_isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
import Theorems.Thm_Garrido_isAmenable_of_commGroup
import Theorems.Thm_Garrido_isAmenable_of_finite

section
/-!
# JMMS Proposition 5.3: for `G ≤ IET`, `G` is amenable iff `G ↷ ℝ/ℤ` is extensively amenable

"Only if": Lemma 2.1. "If": the paper's route. For `g ∈ IET`, `g̃` is the left-continuous
version of `g` and `τ_g = g̃ g⁻¹` is a finitely supported permutation of `ℝ/ℤ` with
`τ_{gh} = τ_g (g τ_h g⁻¹)`, and `τ_g = 1` only for rotations. With the functor
`F : A ↦ Sym(A)`, `g ↦ (τ_g, g)` embeds `G` in `F(ℝ/ℤ) ⋊ G`, meeting `G` in rotations only,
and Corollary 1.4 applies.
-/


open IntervalExchange CategoryTheory

namespace JMMS
namespace IETP53

/-- Extension of a permutation along an embedding, by the identity off the image. -/
noncomputable def permExt {α β : Type*} (e : α ↪ β) : Equiv.Perm α →* Equiv.Perm β := by
  classical exact Equiv.Perm.extendDomainHom (Equiv.ofInjective e e.injective)

lemma permExt_apply_image {α β : Type*} (e : α ↪ β) (σ : Equiv.Perm α) (a : α) :
    permExt e σ (e a) = e (σ a) := by
  classical
  have := Equiv.Perm.extendDomain_apply_image σ (Equiv.ofInjective e e.injective) a
  simpa [permExt] using this

lemma permExt_apply_not {α β : Type*} (e : α ↪ β) (σ : Equiv.Perm α) {b : β}
    (hb : b ∉ Set.range e) : permExt e σ b = b := by
  classical
  have := Equiv.Perm.extendDomain_apply_not_subtype σ (Equiv.ofInjective e e.injective) hb
  simpa [permExt] using this

lemma permExt_trans {α β γ : Type*} (e : α ↪ β) (f : β ↪ γ) (σ : Equiv.Perm α) :
    permExt (e.trans f) σ = permExt f (permExt e σ) := by
  ext c
  by_cases hc : c ∈ Set.range f
  · obtain ⟨b, rfl⟩ := hc
    rw [permExt_apply_image]
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hb
      rw [permExt_apply_image]
      have := permExt_apply_image (e.trans f) σ a
      simpa using this
    · rw [permExt_apply_not _ _ hb, permExt_apply_not]
      rintro ⟨a, ha⟩
      exact hb ⟨a, f.injective (by simpa using ha)⟩
  · rw [permExt_apply_not _ _ hc, permExt_apply_not]
    rintro ⟨a, rfl⟩
    exact hc ⟨e a, rfl⟩

lemma permExt_refl {α : Type*} (σ : Equiv.Perm α) :
    permExt (Function.Embedding.refl α) σ = σ := by
  ext a
  have := permExt_apply_image (Function.Embedding.refl α) σ a
  simpa using this

/-- The embedding underlying a morphism of `FinInj`. -/
def emb {A B : FinInj.{0}} (f : A ⟶ B) : A.obj ↪ B.obj := ⟨fun a => f.hom a, f.property⟩

/-- The functor `A ↦ Sym(A)` on finite sets and injections. -/
noncomputable abbrev symF : FinInj.{0} ⥤ GrpCat.{0} where
  obj A := GrpCat.of (Equiv.Perm A.obj)
  map f := GrpCat.ofHom (permExt (emb f))
  map_id A := by
    ext σ : 2
    simp only [GrpCat.hom_ofHom, GrpCat.hom_id, MonoidHom.id_apply]
    have : emb (𝟙 A) = Function.Embedding.refl _ := by ext a; rfl
    rw [this, permExt_refl]
  map_comp f g := by
    ext σ : 2
    simp only [GrpCat.hom_ofHom, GrpCat.hom_comp, MonoidHom.comp_apply]
    have : emb (f ≫ g) = (emb f).trans (emb g) := by ext a; rfl
    rw [this, permExt_trans]

variable {X : Type}

/-- The embedding of a finite subset. -/
def subEmb (A : Finset X) : A ↪ X := Function.Embedding.subtype (· ∈ A)

/-- The cocone `Sym(A) → Sym(X)`. -/
noncomputable def symCocone (X : Type) : Limits.Cocone (finsetDiagram X ⋙ symF) where
  pt := GrpCat.of (Equiv.Perm X)
  ι :=
    { app := fun A => GrpCat.ofHom (permExt (subEmb A))
      naturality := by
        intro A B i
        ext σ : 2
        simp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id, GrpCat.hom_comp, MonoidHom.comp_apply, GrpCat.hom_ofHom]
        show permExt (subEmb B) (permExt (emb ((finsetDiagram X).map i)) σ) = permExt (subEmb A) σ
        have := permExt_trans (emb ((finsetDiagram X).map i)) (subEmb B) σ
        refine this.symm.trans ?_
        congr 1 }

/-- The morphism `Sym(X)_fin → Sym(X)` out of the colimit. -/
noncomputable def Ψ (X : Type) : extend symF X ⟶ GrpCat.of (Equiv.Perm X) :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit.{0, 0} (finsetDiagram X ⋙ symF)).desc
    (symCocone X)

lemma Ψ_extendι (A : Finset X) (σ : Equiv.Perm A) :
    (Ψ X).hom ((extendι symF A).hom σ) = permExt (subEmb A) σ := by
  have := (GrpCat.FilteredColimits.colimitCoconeIsColimit.{0, 0} (finsetDiagram X ⋙ symF)).fac
    (symCocone X) A
  exact congrArg (fun φ => φ.hom σ) this

/-- Restriction of a permutation supported in `A` to `A`. -/
def restr (σ : Equiv.Perm X) (A : Finset X) (h : ∀ x, σ x ≠ x → x ∈ A) : Equiv.Perm A :=
  σ.subtypePerm (by
    intro x
    by_cases hs : σ x = x
    · rw [hs]
    · have h1 := h x hs
      have h2 := h (σ x) (fun he => hs (σ.injective he))
      constructor <;> intro _ <;> assumption)

@[simp] lemma restr_apply (σ : Equiv.Perm X) (A : Finset X) (h : ∀ x, σ x ≠ x → x ∈ A)
    (a : A) : (restr σ A h a : X) = σ a := rfl

lemma permExt_restr (σ : Equiv.Perm X) (A : Finset X) (h : ∀ x, σ x ≠ x → x ∈ A) :
    permExt (subEmb A) (restr σ A h) = σ := by
  ext x
  by_cases hx : x ∈ A
  · have := permExt_apply_image (subEmb A) (restr σ A h) ⟨x, hx⟩
    simpa [subEmb] using this
  · rw [permExt_apply_not]
    · by_contra hne; exact hx (h x (Ne.symm hne))
    · rintro ⟨a, rfl⟩; exact hx a.2

/-- The element of `F(X)` represented by a permutation supported in `A`. -/
noncomputable def eltA (σ : Equiv.Perm X) (A : Finset X) (h : ∀ x, σ x ≠ x → x ∈ A) :
    extend symF X :=
  (extendι symF A).hom (restr σ A h)

lemma Ψ_eltA (σ : Equiv.Perm X) (A : Finset X) (h : ∀ x, σ x ≠ x → x ∈ A) :
    (Ψ X).hom (eltA σ A h) = σ := by
  rw [eltA, Ψ_extendι, permExt_restr]

lemma eltA_congr (σ : Equiv.Perm X) {A B : Finset X} (h : ∀ x, σ x ≠ x → x ∈ A)
    (hAB : A ⊆ B) :
    eltA σ A h = eltA σ B (fun x hx => hAB (h x hx)) := by
  have h1 : A.map (Function.Embedding.refl X) ⊆ B := by simpa using hAB
  have h2 : A.map (Function.Embedding.refl X) ⊆ A := by simp
  have key := congrArg (fun φ => φ.hom (restr σ A h))
    (map_finsetMap_comp_extendι symF (Function.Embedding.refl X) h1 h2)
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at key
  have e2 : emb (finsetMap (Function.Embedding.refl X) h2) = Function.Embedding.refl _ := by
    ext a; rfl
  simp only [GrpCat.hom_ofHom] at key
  rw [e2, permExt_refl] at key
  rw [eltA, eltA, ← key]
  congr 1
  ext a
  show (permExt (emb (finsetMap (Function.Embedding.refl X) h1)) (restr σ A h) a : X) = σ a
  by_cases ha : (a : X) ∈ A
  · have := permExt_apply_image (emb (finsetMap (Function.Embedding.refl X) h1)) (restr σ A h)
      ⟨a, ha⟩
    have e : emb (finsetMap (Function.Embedding.refl X) h1) ⟨a, ha⟩ = a := rfl
    rw [e] at this
    rw [this]; rfl
  · rw [permExt_apply_not]
    · by_contra hne; exact ha (h a (Ne.symm hne))
    · rintro ⟨b, hb⟩
      apply ha
      have : (b : X) = a := congrArg Subtype.val hb
      rw [← this]; exact b.2

lemma eltA_mul (σ τ : Equiv.Perm X) (A : Finset X) (hσ : ∀ x, σ x ≠ x → x ∈ A)
    (hτ : ∀ x, τ x ≠ x → x ∈ A) (hστ : ∀ x, (σ * τ) x ≠ x → x ∈ A) :
    eltA (σ * τ) A hστ = eltA σ A hσ * eltA τ A hτ := by
  rw [eltA, eltA, eltA, ← map_mul]
  congr 1

lemma eltA_one (A : Finset X) (h : ∀ x, (1 : Equiv.Perm X) x ≠ x → x ∈ A) :
    eltA 1 A h = 1 := by
  rw [eltA, ← map_one (extendι symF A).hom]
  congr 1

lemma extendMap_eltA (π : Equiv.Perm X) (σ : Equiv.Perm X) (A : Finset X)
    (h : ∀ x, σ x ≠ x → x ∈ A) (h' : ∀ x, (π * σ * π⁻¹) x ≠ x → x ∈ A.map π.toEmbedding) :
    (extendMap symF π.toEmbedding).hom (eltA σ A h) = eltA (π * σ * π⁻¹) _ h' := by
  have key := congrArg (fun φ => φ.hom (restr σ A h)) (extendι_extendMap symF π.toEmbedding A)
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at key
  rw [eltA, key, eltA]
  congr 1
  ext a
  show (permExt (emb (finsetMap π.toEmbedding (subset_refl (A.map π.toEmbedding))))
    (restr σ A h) a : X) = (π * σ * π⁻¹) a
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
  have := permExt_apply_image (emb (finsetMap π.toEmbedding (subset_refl (A.map π.toEmbedding))))
      (restr σ A h) ⟨b, hb⟩
  have e : emb (finsetMap π.toEmbedding (subset_refl (A.map π.toEmbedding))) ⟨b, hb⟩ =
    ⟨π.toEmbedding b, ha⟩ := rfl
  rw [e] at this
  rw [this]
  simp [emb]
  rfl

end IETP53
end JMMS

open IntervalExchange
open Filter Topology

namespace JMMS
namespace IETP53

local notation "C" => UnitAddCircle

lemma contMk : Continuous (fun t : ℝ => (t : C)) := continuous_quotient_mk'

/-- A function continuous within `s` at `a` with values in a finite set is eventually constant. -/
lemma eventually_eq_of_finite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {f : α → β} {s : Set α} {a : α} {S : Set β} (hS : S.Finite) (hf : ∀ t, f t ∈ S)
    (hc : ContinuousWithinAt f s a) : ∀ᶠ t in 𝓝[s] a, f t = f a := by
  have hopen : IsOpen (S \ {f a})ᶜ := ((hS.subset Set.sdiff_subset).isClosed).isOpen_compl
  have hmem : f a ∈ (S \ {f a})ᶜ := by simp
  filter_upwards [hc (hopen.mem_nhds hmem)] with t ht
  by_contra hne
  exact ht ⟨hf t, hne⟩

/-- `g` agrees with the translation `x + t ↦ y + t` just to the left of `x`: `y` is the left
limit of `g` at `x`. -/
def LeftLim (g : C → C) (x y : C) : Prop :=
  ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ), g (x + (t : C)) = y + t

lemma leftLim_unique {g : C → C} {x y z : C} (h1 : LeftLim g x y) (h2 : LeftLim g x z) :
    y = z := by
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  rw [ht1] at ht2
  exact add_right_cancel ht2

lemma leftLim_comp {g h : C → C} {x y z : C} (hh : LeftLim h x y) (hg : LeftLim g y z) :
    LeftLim (g ∘ h) x z := by
  filter_upwards [hh, hg] with t h1 h2
  simp only [Function.comp, h1, h2]

lemma leftLim_id (x : C) : LeftLim id x x := Eventually.of_forall fun _ => rfl

lemma leftLim_of_continuousAt {g : C → C} (ha : (angles g).Finite) {x : C}
    (hc : ContinuousAt g x) : LeftLim g x (g x) := by
  have hU : ∀ᶠ z in 𝓝 x, g z - z = g x - x := by
    have := eventually_eq_of_finite (s := Set.univ) ha (fun t => ⟨t, rfl⟩)
      ((hc.sub continuousAt_id).continuousWithinAt)
    simpa [nhdsWithin_univ] using this
  have ht : Tendsto (fun t : ℝ => x + (t : C)) (𝓝[<] 0) (𝓝 x) := by
    have : Tendsto (fun t : ℝ => x + (t : C)) (𝓝 0) (𝓝 x) :=
      (continuous_const.add contMk).tendsto' 0 x (by simp)
    exact this.mono_left nhdsWithin_le_nhds
  filter_upwards [ht hU] with t ht
  have : g (x + t) = (g (x + t) - (x + t)) + (x + t) := by abel
  rw [this, ht]; abel

/-- Points just to the left of `x` avoid a given finite set. -/
lemma eventually_not_mem {D : Set C} (hD : D.Finite) (x : C) :
    ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ), x + (t : C) ∉ D := by
  have hD' : IsClosed (D \ {x}) := (hD.subset Set.sdiff_subset).isClosed
  have h1 : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), x + (t : C) ∉ D \ {x} := by
    have hc : ContinuousAt (fun t : ℝ => x + (t : C)) 0 := (continuous_const.add contMk).continuousAt
    have hx : x + ((0:ℝ) : C) ∉ D \ {x} := by simp
    exact hc.eventually (hD'.isOpen_compl.mem_nhds hx)
  have h2 : ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ), t ∈ Set.Ioo (-1 : ℝ) 0 :=
    Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [nhdsWithin_le_nhds h1, h2] with t ht ht2 hmem
  apply ht
  refine ⟨hmem, ?_⟩
  intro heq
  have h0 : ((t : ℝ) : C) = 0 := by
    have : x + (t : C) = x + 0 := by simpa using heq
    exact add_left_cancel this
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  simp only [zsmul_eq_mul, mul_one] at hn
  obtain ⟨h3, h4⟩ := ht2
  rw [← hn] at h3 h4
  have : (-1 : ℤ) < n := by exact_mod_cast h3
  have : n < 0 := by exact_mod_cast h4
  omega

lemma leftLim_exists {g : Equiv.Perm C} (hg : IsIntervalExchange g) (x : C) :
    ∃ y, LeftLim g x y := by
  obtain ⟨-, ha, hd⟩ := hg
  have hev := eventually_not_mem hd x
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hl' : l < 0 := hl
  set f : ℝ → C := fun t => g (x + (t : C)) - (x + (t : C)) with hf
  have hcont : ContinuousOn f (Set.Ioo l 0) := by
    intro s hs
    have hgc : ContinuousAt g (x + (s : C)) := by
      have := hsub hs
      simpa using this
    have h1 : ContinuousAt (fun t : ℝ => x + (t : C)) s :=
      (continuous_const.add contMk).continuousAt
    exact ((hgc.comp_of_eq h1 rfl).sub h1).continuousWithinAt
  have hdisc : IsDiscrete (angles (⇑g)) := by
    rw [isDiscrete_iff_discreteTopology]
    have : Finite (angles (⇑g)) := ha.to_subtype
    infer_instance
  have hconst : ∀ s ∈ Set.Ioo l 0, f s = f (l / 2) := by
    intro s hs
    refine isPreconnected_Ioo.constant_of_mapsTo hdisc hcont ?_ hs ?_
    · intro t _; exact ⟨_, rfl⟩
    · constructor <;> linarith
  refine ⟨x + f (l / 2), ?_⟩
  filter_upwards [Ioo_mem_nhdsLT hl] with t ht
  rw [← hconst t ht, hf]
  simp only
  abel

/-- The left-continuous version of `g`. -/
noncomputable def tl (g : C → C) (x : C) : C :=
  open Classical in if h : ∃ y, LeftLim g x y then h.choose else x

lemma tl_spec {g : Equiv.Perm C} (hg : g ∈ IET) (x : C) : LeftLim g x (tl g x) := by
  have h := leftLim_exists ((mem_IET_iff g).1 hg) x
  rw [tl, dif_pos h]
  exact h.choose_spec

lemma tl_eq {g : Equiv.Perm C} (hg : g ∈ IET) {x y : C} (h : LeftLim g x y) : tl g x = y :=
  leftLim_unique (tl_spec hg x) h

lemma tl_mul {g h : Equiv.Perm C} (hg : g ∈ IET) (hh : g ∈ IET → h ∈ IET) (x : C) :
    tl (⇑(g * h)) x = tl g (tl h x) := by
  have hh' := hh hg
  apply tl_eq (IET.mul_mem hg hh')
  rw [Equiv.Perm.coe_mul]
  exact leftLim_comp (tl_spec hh' x) (tl_spec hg _)

lemma tl_one (x : C) : tl (⇑(1 : Equiv.Perm C)) x = x :=
  tl_eq IET.one_mem (leftLim_id x)

lemma tl_eq_self {g : Equiv.Perm C} (hg : g ∈ IET) {x : C} (hc : ContinuousAt g x) :
    tl g x = g x :=
  tl_eq hg (leftLim_of_continuousAt ((mem_IET_iff g).1 hg).2.1 hc)

/-- The left-continuous version of an element of `IET`, as a permutation. -/
noncomputable def tlPerm (g : IET) : Equiv.Perm C where
  toFun := tl (g : Equiv.Perm C)
  invFun := tl ((g⁻¹ : IET) : Equiv.Perm C)
  left_inv x := by
    rw [← tl_mul (g⁻¹ : IET).2 (fun _ => g.2), ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, tl_one]
  right_inv x := by
    rw [← tl_mul g.2 (fun _ => (g⁻¹ : IET).2), ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, tl_one]

/-- `g ↦ g̃` is a homomorphism. -/
noncomputable def tlHom : IET →* Equiv.Perm C where
  toFun := tlPerm
  map_one' := by ext x; exact tl_one x
  map_mul' g h := by ext x; exact tl_mul g.2 (fun _ => h.2) x

lemma tlHom_apply (g : IET) (x : C) : tlHom g x = tl (g : Equiv.Perm C) x := rfl

/-- The cocycle `τ_g = g̃ g⁻¹`. -/
noncomputable def τ (g : IET) : Equiv.Perm C := tlHom g * (g : Equiv.Perm C)⁻¹

lemma τ_mul (g h : IET) :
    τ (g * h) = τ g * ((g : Equiv.Perm C) * τ h * (g : Equiv.Perm C)⁻¹) := by
  simp only [τ, map_mul, Subgroup.coe_mul, mul_inv_rev]
  group

lemma τ_one : τ 1 = 1 := by simp [τ]

lemma τ_support_finite (g : IET) : {y | τ g y ≠ y}.Finite := by
  have hd := ((mem_IET_iff _).1 g.2).2.2
  refine (hd.image (g : Equiv.Perm C)).subset ?_
  intro y hy
  refine ⟨(g : Equiv.Perm C)⁻¹ y, ?_, by simp⟩
  intro hc
  apply hy
  show tl (g : Equiv.Perm C) ((g : Equiv.Perm C)⁻¹ y) = y
  rw [tl_eq_self g.2 hc]
  simp

/-- `τ_g = 1` forces `g` to be a rotation. -/
lemma rotation_of_τ_eq_one (g : IET) (h : τ g = 1) :
    ∃ c : C, ∀ z, (g : Equiv.Perm C) z = z + c := by
  have hie := (mem_IET_iff _).1 g.2
  have htl : ∀ x, tl (g : Equiv.Perm C) x = (g : Equiv.Perm C) x := by
    intro x
    have := congrArg (fun π : Equiv.Perm C => π ((g : Equiv.Perm C) x)) h
    simpa [τ, tlHom_apply] using this
  -- local translation on both sides
  have hloc : ∀ x : C, ∀ᶠ t : ℝ in 𝓝 (0:ℝ),
      (g : Equiv.Perm C) (x + (t : C)) = (g : Equiv.Perm C) x + t := by
    intro x
    rw [← nhdsLT_sup_nhdsGE]
    refine Filter.eventually_sup.2 ⟨?_, ?_⟩
    · have := tl_spec g.2 x
      rw [htl] at this
      exact this
    · have hc : ContinuousWithinAt
          (fun t : ℝ => (g : Equiv.Perm C) (x + (t : C)) - (x + (t : C))) (Set.Ici 0) 0 :=
        (hie.1 x).sub ((continuous_const.add contMk).continuousWithinAt)
      filter_upwards [eventually_eq_of_finite hie.2.1 (fun t : ℝ => ⟨x + (t : C), rfl⟩) hc] with t ht
      simp only [QuotientAddGroup.mk_zero, add_zero] at ht
      rw [← sub_add_cancel ((g : Equiv.Perm C) (x + t)) (x + t), ht]
      abel
  set f : ℝ → C := fun u => (g : Equiv.Perm C) u - u with hf
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have ht : Tendsto (fun u : ℝ => u - s) (𝓝 s) (𝓝 0) := by
      exact (continuous_id.sub continuous_const).tendsto' s 0 (by simp)
    filter_upwards [ht (hloc (s : C))] with u hu
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hu
    simp only [hf]
    have e : ((s : ℝ) : C) + ((u - s : ℝ) : C) = (u : C) := by
      rw [← QuotientAddGroup.mk_add]; congr 1; ring
    rw [e] at hu
    rw [hu]
    have e2 : (u : C) = (s : C) + ((u - s : ℝ) : C) := e.symm
    conv_lhs => rw [e2]
    abel
  refine ⟨f 0, fun z => ?_⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective z
  have := hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ u) (Set.mem_univ 0)
  have e : (g : Equiv.Perm C) (u : C) = (u : C) + f u := by simp [hf]
  rw [e, this]

end IETP53
end JMMS

open IntervalExchange CategoryTheory
open scoped Pointwise

namespace JMMS
namespace IETP53

local notation "C" => UnitAddCircle

/-- Amenability transfers along a group isomorphism. -/
theorem isAmenable_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : Garrido.IsAmenable G) : Garrido.IsAmenable H := by
  obtain ⟨m, ⟨h0, hadd⟩, h1, hinv⟩ := hG
  refine ⟨fun s => m (e ⁻¹' s), ⟨by simpa using h0, ?_⟩, by simpa using h1, ?_⟩
  · intro s t hst
    show m (e ⁻¹' (s ∪ t)) = m (e ⁻¹' s) + m (e ⁻¹' t)
    rw [Set.preimage_union]
    exact hadd _ _ (hst.preimage _)
  · intro g s
    have : e ⁻¹' (g • s) = e.symm g • (e ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      simp [map_mul, map_inv]
    show m (e ⁻¹' (g • s)) = m (e ⁻¹' s)
    rw [this, hinv]

variable {X : Type}

lemma eltA_eq_of_eq {σ σ' : Equiv.Perm X} (e : σ = σ') (A : Finset X)
    (h : ∀ x, σ x ≠ x → x ∈ A) (h' : ∀ x, σ' x ≠ x → x ∈ A) : eltA σ A h = eltA σ' A h' := by
  subst e; rfl

lemma eltA_any (σ : Equiv.Perm X) {A B : Finset X} (hA : ∀ x, σ x ≠ x → x ∈ A)
    (hB : ∀ x, σ x ≠ x → x ∈ B) : eltA σ A hA = eltA σ B hB := by
  classical
  rw [eltA_congr σ hA (Finset.subset_union_left : A ⊆ A ∪ B),
    eltA_congr σ hB (Finset.subset_union_right : B ⊆ A ∪ B)]

lemma eltA_mul' (σ τ : Equiv.Perm X) {A B D : Finset X} (hA : ∀ x, σ x ≠ x → x ∈ A)
    (hB : ∀ x, τ x ≠ x → x ∈ B) (hD : ∀ x, (σ * τ) x ≠ x → x ∈ D) :
    eltA (σ * τ) D hD = eltA σ A hA * eltA τ B hB := by
  classical
  have hσ : ∀ x, σ x ≠ x → x ∈ A ∪ B := fun x hx => Finset.mem_union_left _ (hA x hx)
  have hτ : ∀ x, τ x ≠ x → x ∈ A ∪ B := fun x hx => Finset.mem_union_right _ (hB x hx)
  have hστ : ∀ x, (σ * τ) x ≠ x → x ∈ A ∪ B := by
    intro x hx
    by_cases h1 : τ x = x
    · apply hσ; simpa [Equiv.Perm.mul_apply, h1] using hx
    · exact hτ x h1
  rw [eltA_any _ hD hστ, eltA_any _ hA hσ, eltA_any _ hB hτ]
  exact eltA_mul σ τ _ hσ hτ hστ

lemma conj_supp (π σ : Equiv.Perm X) (A : Finset X) (h : ∀ x, σ x ≠ x → x ∈ A) :
    ∀ x, (π * σ * π⁻¹) x ≠ x → x ∈ A.map π.toEmbedding := by
  intro x hx
  rw [Finset.mem_map]
  refine ⟨π⁻¹ x, h _ ?_, by simp⟩
  intro he
  apply hx
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, he]
  simp

variable (G : Subgroup (Equiv.Perm C)) (hG : G ≤ IET)

/-- The finite support of `τ_g`. -/
noncomputable def supp (g : IET) : Finset C := (τ_support_finite g).toFinset

lemma mem_supp (g : IET) : ∀ x, τ g x ≠ x → x ∈ supp g := by
  intro x hx
  simpa [supp] using hx

/-- The cocycle `g ↦ τ_g ∈ F(ℝ/ℤ)`. -/
noncomputable def cocyc (g : G) : extend symF C :=
  eltA (τ (Subgroup.inclusion hG g)) (supp _) (mem_supp _)

lemma toPerm_eq (g : G) : (MulAction.toPerm g : Equiv.Perm C) = (g : Equiv.Perm C) := by
  ext; rfl

lemma cocyc_mul (g h : G) :
    cocyc G hG (g * h) = cocyc G hG g * extendAut symF G C g (cocyc G hG h) := by
  have e1 : extendAut symF G C g (cocyc G hG h) =
      (extendMap symF (MulAction.toPerm g : Equiv.Perm C).toEmbedding).hom (cocyc G hG h) := rfl
  have key : τ (Subgroup.inclusion hG g) * ((MulAction.toPerm g : Equiv.Perm C) *
      τ (Subgroup.inclusion hG h) * (MulAction.toPerm g : Equiv.Perm C)⁻¹) =
      τ (Subgroup.inclusion hG (g * h)) := by
    rw [map_mul, τ_mul, toPerm_eq]; rfl
  rw [e1]
  unfold cocyc
  rw [extendMap_eltA _ _ _ _ (conj_supp _ _ _ (mem_supp _)),
    ← eltA_mul' _ _ _ _ (fun x hx => mem_supp _ x (by rwa [key] at hx))]
  exact eltA_eq_of_eq key.symm _ _ _

lemma cocyc_one : cocyc G hG 1 = 1 := by
  rw [cocyc]
  rw [eltA_eq_of_eq (σ' := 1) (by rw [map_one, τ_one]) _ _ (by simp)]
  exact eltA_one _ _

/-- The embedding `g ↦ (τ_g, g)` of `G` into `F(ℝ/ℤ) ⋊ G`. -/
noncomputable def emb53 : G →* FunctorProduct symF G C where
  toFun g := ⟨cocyc G hG g, g⟩
  map_one' := by
    ext
    · exact cocyc_one G hG
    · rfl
  map_mul' g h := by
    ext
    · simp only [SemidirectProduct.mul_left]
      exact cocyc_mul G hG g h
    · rfl

lemma emb53_injective : Function.Injective (emb53 G hG) := by
  intro g h e
  exact congrArg SemidirectProduct.right e

lemma mem_inf (p : FunctorProduct symF G C)
    (hp : p ∈ (emb53 G hG).range ⊓ (SemidirectProduct.inr : G →* FunctorProduct symF G C).range) :
    p.left = 1 ∧ ∃ c : C, ∀ z, (p.right : Equiv.Perm C) z = z + c := by
  obtain ⟨⟨g, rfl⟩, ⟨k, hk⟩⟩ := hp
  have hl : cocyc G hG g = 1 := by
    have := congrArg SemidirectProduct.left hk
    simpa [emb53] using this.symm
  refine ⟨hl, ?_⟩
  have hτ : τ (Subgroup.inclusion hG g) = 1 := by
    have := congrArg (Ψ C).hom hl
    rw [cocyc, Ψ_eltA, map_one] at this
    exact this
  exact rotation_of_τ_eq_one _ hτ

lemma comm_inf (p q : ↥((emb53 G hG).range ⊓
    (SemidirectProduct.inr : G →* FunctorProduct symF G C).range)) : p * q = q * p := by
  obtain ⟨hp1, c, hc⟩ := mem_inf G hG p.1 p.2
  obtain ⟨hq1, d, hd⟩ := mem_inf G hG q.1 q.2
  apply Subtype.ext
  show p.1 * q.1 = q.1 * p.1
  refine SemidirectProduct.ext ?_ ?_
  · simp [SemidirectProduct.mul_left, hp1, hq1]
  · simp only [SemidirectProduct.mul_right]
    apply Subtype.ext
    ext z
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hc, hd]
    abel

end IETP53

open IETP53 in
theorem chk_isAmenable_iff_isExtensivelyAmenable_of_le_IET (G : Subgroup (Equiv.Perm UnitAddCircle))
    (hG : G ≤ IET) :
    Garrido.IsAmenable ↥G ↔ IsExtensivelyAmenable ↥G UnitAddCircle := by
  constructor
  · exact (isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
      (G := ↥G) (X := UnitAddCircle)).1
  · intro hE
    have hF : IsAmenableValued symF := fun A => Garrido.isAmenable_of_finite _
    let K := (emb53 G hG).range ⊓
      (SemidirectProduct.inr : ↥G →* FunctorProduct symF ↥G UnitAddCircle).range
    let _ : CommGroup ↥K := { (inferInstance : Group ↥K) with mul_comm := comm_inf G hG }
    have hK : Garrido.IsAmenable ↥K := Garrido.isAmenable_of_commGroup ↥K
    have hR := isAmenable_of_isAmenable_inf_range_inr symF hF ↥G UnitAddCircle hE
      (emb53 G hG).range hK
    exact isAmenable_of_mulEquiv (MonoidHom.ofInjective (emb53_injective G hG)).symm hR

end JMMS
end

open IntervalExchange
open JMMS in
theorem solution (G : Subgroup (Equiv.Perm UnitAddCircle))
    (hG : G ≤ IET) :
    Garrido.IsAmenable ↥G ↔ IsExtensivelyAmenable ↥G UnitAddCircle := by
  apply JMMS.chk_isAmenable_iff_isExtensivelyAmenable_of_le_IET <;> assumption

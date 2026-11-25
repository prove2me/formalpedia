-- Prove2me | solution 1 for GlobalTheory.SpreadSep.exists_isClosed_preimage_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:13:23.879629+00:00
-- url     : https://prove2.me/submissions/74fb39d3-0a1c-4f1e-b402-d50d61ec0061

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFgIsSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SpreadSep
universe u
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.SpreadSep
namespace _root_.GlobalTheory.SpreadSep
theorem _root_.solution {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I}
    (O O' : (D.obj i).Opens) (hO : IsCompact (O : Set (D.obj i)))
    (hO' : IsCompact (O' : Set (D.obj i)))
    (H : IsClosed (c.π.app i ⁻¹' ((O : Set (D.obj i)) \ O'))) :
    ∃ (j : I) (f : j ⟶ i), IsClosed (D.map f ⁻¹' ((O : Set (D.obj i)) \ O')) := by
  have hw : ∀ {a b : I} (g : a ⟶ b) (x : c.pt), D.map g (c.π.app a x) = c.π.app b x := by
    intro a b g x
    rw [← c.w g]; rfl
  have hpw : ∀ {a b : I} (g : a ⟶ b) (W : (D.obj b).Opens),
      c.π.app a ⁻¹ᵁ (D.map g ⁻¹ᵁ W) = c.π.app b ⁻¹ᵁ W := by
    intro a b g W
    ext x
    change D.map g (c.π.app a x) ∈ W ↔ c.π.app b x ∈ W
    rw [hw]
  have hpre : ∀ {a b : I} (g : a ⟶ b) (W : (D.obj b).Opens), IsCompact (W : Set (D.obj b)) →
      IsCompact ((D.map g ⁻¹ᵁ W : (D.obj a).Opens) : Set (D.obj a)) :=
    fun g W hW => QuasiCompact.isCompact_preimage (f := D.map g) _ W.isOpen hW
  haveI := Scheme.compactSpace_of_isLimit D c hc
  let C : c.pt.Opens := ⟨_, H.isOpen_compl⟩
  have hCmem : ∀ x, x ∈ C ↔ (c.π.app i x ∈ O → c.π.app i x ∈ O') := by
    intro x
    change x ∉ c.π.app i ⁻¹' ((O : Set (D.obj i)) \ O') ↔ _
    simp only [Set.mem_preimage, Set.mem_diff, SetLike.mem_coe, not_and, not_not]
  let K : Set c.pt := ((c.π.app i ⁻¹ᵁ O : c.pt.Opens) : Set c.pt)ᶜ
  have hK : IsCompact K := IsClosed.isCompact (X := c.pt) (c.π.app i ⁻¹ᵁ O).isOpen.isClosed_compl
  let P : c.pt.Opens → Prop := fun A => (∃ (k : I) (_ : k ⟶ i) (W : (D.obj k).Opens),
    IsCompact (W : Set (D.obj k)) ∧ c.π.app k ⁻¹ᵁ W = A) ∧ A ≤ C
  let ι := {A : c.pt.Opens // P A}
  haveI : Nonempty ι := ⟨⟨⊥, ⟨i, 𝟙 i, ⊥, by simp, by ext x; simp⟩, bot_le⟩⟩
  have hdir : Directed (· ⊆ ·) (fun A : ι => (A.1 : Set c.pt)) := by
    rintro ⟨A₁, ⟨k₁, f₁, W₁, hW₁, rfl⟩, hA₁⟩ ⟨A₂, ⟨k₂, f₂, W₂, hW₂, rfl⟩, hA₂⟩
    let l₁ := IsCofiltered.minToLeft k₁ k₂
    let l₂ := IsCofiltered.minToRight k₁ k₂
    have he : c.π.app _ ⁻¹ᵁ (D.map l₁ ⁻¹ᵁ W₁ ⊔ D.map l₂ ⁻¹ᵁ W₂) =
        c.π.app k₁ ⁻¹ᵁ W₁ ⊔ c.π.app k₂ ⁻¹ᵁ W₂ := by
      rw [Scheme.Hom.preimage_sup, hpw, hpw]
    refine ⟨⟨c.π.app k₁ ⁻¹ᵁ W₁ ⊔ c.π.app k₂ ⁻¹ᵁ W₂,
      ⟨_, l₁ ≫ f₁, _, (hpre _ _ hW₁).union (hpre _ _ hW₂), he⟩, sup_le hA₁ hA₂⟩, ?_, ?_⟩
    · exact fun x hx => Or.inl hx
    · exact fun x hx => Or.inr hx
  have hB := isBasis_preimage_isAffineOpen D c hc
  have hcov : K ⊆ ⋃ A : ι, (A.1 : Set c.pt) := by
    intro x hx
    have hxC : x ∈ C := (hCmem x).2 fun h => absurd h hx
    obtain ⟨U', ⟨j, V, hV, rfl⟩, hxU', hU'C⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 hB hxC
    let m := IsCofiltered.min j i
    refine Set.mem_iUnion.2 ⟨⟨c.π.app m ⁻¹ᵁ (D.map (IsCofiltered.minToLeft j i) ⁻¹ᵁ V),
      ⟨m, IsCofiltered.minToRight j i, _, hpre _ _ hV.isCompact, rfl⟩, ?_⟩, ?_⟩
    · rw [hpw]; exact hU'C
    · change x ∈ c.π.app m ⁻¹ᵁ (D.map (IsCofiltered.minToLeft j i) ⁻¹ᵁ V)
      rw [hpw]; exact hxU'
  obtain ⟨⟨_, ⟨k, f, W, hW, rfl⟩, hWC⟩, hKW⟩ :=
    hK.elim_directed_cover _ (fun A => A.1.isOpen) hcov hdir
  have h₁ : c.π.app k ⁻¹ᵁ (W ⊔ D.map f ⁻¹ᵁ O) = ⊤ := by
    rw [Scheme.Hom.preimage_sup, hpw, eq_top_iff]
    intro x _
    by_cases hx : c.π.app i x ∈ O
    · exact Or.inr hx
    · exact Or.inl (hKW hx)
  obtain ⟨l, g, hg⟩ := exists_map_eq_top D c hc _ h₁
  have hcpt : IsCompact ((D.map g ⁻¹ᵁ (W ⊓ D.map f ⁻¹ᵁ O) : (D.obj l).Opens) : Set (D.obj l)) :=
    hpre _ _ (QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW (D.map f ⁻¹ᵁ O).isOpen
      (hpre _ _ hO))
  have h₂ : c.π.app l ⁻¹ᵁ (D.map g ⁻¹ᵁ (W ⊓ D.map f ⁻¹ᵁ O)) ≤
      c.π.app l ⁻¹ᵁ (D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ O')) := by
    rw [hpw, hpw, hpw, Scheme.Hom.preimage_inf, hpw]
    rintro x ⟨hxW, hxO⟩
    exact (hCmem x).1 (hWC hxW) hxO
  obtain ⟨m, h, hh⟩ := exists_map_preimage_le_map_preimage D c hc hcpt h₂
  refine ⟨m, h ≫ g ≫ f, ?_⟩
  have ht : ∀ y : D.obj m, D.map g (D.map h y) ∈ W ∨ D.map f (D.map g (D.map h y)) ∈ O := by
    intro y
    have : D.map h y ∈ D.map g ⁻¹ᵁ (W ⊔ D.map f ⁻¹ᵁ O) := by rw [hg]; trivial
    simpa using this
  have hle : ∀ y : D.obj m, D.map g (D.map h y) ∈ W → D.map f (D.map g (D.map h y)) ∈ O →
      D.map f (D.map g (D.map h y)) ∈ O' := by
    intro y hy₁ hy₂
    have : y ∈ D.map h ⁻¹ᵁ (D.map g ⁻¹ᵁ (W ⊓ D.map f ⁻¹ᵁ O)) := by simpa using ⟨hy₁, hy₂⟩
    simpa using hh this
  have hset : D.map (h ≫ g ≫ f) ⁻¹' ((O : Set (D.obj i)) \ O') =
      ((D.map (h ≫ g) ⁻¹ᵁ W ⊔ D.map (h ≫ g ≫ f) ⁻¹ᵁ O' : (D.obj m).Opens) : Set (D.obj m))ᶜ := by
    ext y
    simp only [Functor.map_comp, Set.mem_preimage, Set.mem_diff, SetLike.mem_coe, Set.mem_compl_iff,
      Scheme.Hom.preimage_sup, TopologicalSpace.Opens.coe_sup, Set.mem_union, Scheme.Hom.comp_apply]
    have h1 := ht y
    have h2 := hle y
    tauto
  rw [hset]
  exact (TopologicalSpace.Opens.isOpen _).isClosed_compl
end _root_.GlobalTheory.SpreadSep
end GlobalTheory.SpreadSep

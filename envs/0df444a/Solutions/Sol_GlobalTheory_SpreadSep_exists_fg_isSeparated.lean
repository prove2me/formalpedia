-- Prove2me | solution 1 for GlobalTheory.SpreadSep.exists_fg_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:37:31.319741+00:00
-- url     : https://prove2.me/submissions/fc0b36d1-e1c2-4586-a3a0-caf6966f7321

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFgIsSeparated
import Theorems.Thm_GlobalTheory_SpreadSep_exists_isClosed_preimage_diff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SpreadSep
universe u
open AlgebraicGeometry CategoryTheory Limits in
private theorem isSeparated_iff_isClosed_range_diagonal {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    IsSeparated f ↔ IsClosed (Set.range (pullback.diagonal f)) :=
  ⟨fun _ => (pullback.diagonal f).isClosedEmbedding.isClosed_range,
    fun h => ⟨IsClosedImmersion.of_isPreimmersion _ h⟩⟩
open AlgebraicGeometry CategoryTheory Limits in
private theorem isClosed_range_iso_comp_comp_iso_inv_iff {A B C D : Scheme.{0}} (a : A ≅ B) (g : B ⟶ C)
    (e : D ≅ C) : IsClosed (Set.range (a.hom ≫ g ≫ e.inv)) ↔ IsClosed (Set.range g) := by
  have hr : Set.range (a.hom ≫ g ≫ e.inv) = e.hom ⁻¹' Set.range g := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨a.hom x, ?_⟩
      change g (a.hom x) = (e.inv ≫ e.hom) (g (a.hom x))
      rw [e.inv_hom_id]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨a.inv y, ?_⟩
      change e.inv (g ((a.inv ≫ a.hom) y)) = z
      rw [a.inv_hom_id]
      change e.inv (g y) = z
      rw [hy]
      change (e.hom ≫ e.inv) z = z
      rw [e.hom_inv_id]
      rfl
  rw [hr]
  constructor
  · intro h
    have h' := h.preimage e.inv.continuous
    convert h' using 1
    ext y
    change y ∈ Set.range g ↔ (e.inv ≫ e.hom) y ∈ Set.range g
    rw [e.inv_hom_id]
    rfl
  · intro h
    exact h.preimage e.hom.continuous
open AlgebraicGeometry CategoryTheory Limits in
private theorem isSeparated_pullback_snd_spMap_iff_isClosed_preimage (k R : Type) [CommRing k] [CommRing R] [Algebra k R]
    (X : Scheme.{0}) (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) :
    IsSeparated (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) ↔
      IsClosed (pullback.fst (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)) ⁻¹'
        Set.range (pullback.diagonal p)) := by
  rw [← pullbackSymmetry_hom_comp_fst, MorphismProperty.cancel_left_of_respectsIso @IsSeparated,
    isSeparated_iff_isClosed_range_diagonal, diagonal_pullback_fst]
  simp only [Over.pullback_map_left, Over.homMk_left, Over.mk_hom]
  rw [isClosed_range_iso_comp_comp_iso_inv_iff]
  have hL := IsPullback.of_right (h₁₁ := pullback.lift (pullback.fst p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)) ≫
      pullback.diagonal p) (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) (by simp [pullback.condition]))
    (h₁₂ := pullback.snd (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)))
    (h₂₁ := pullback.diagonal p) (h₂₂ := pullback.snd p p ≫ p)
    (v₁₁ := pullback.fst p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)))
    (v₁₂ := pullback.fst (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)))
    (v₁₃ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))
    (by
      convert (IsPullback.of_hasPullback p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))).flip using 1
      · exact pullback.lift_snd _ _ _
      · simp) (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))).flip
  have hr : Set.range (pullback.lift (pullback.fst p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)) ≫
      pullback.diagonal p) (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) (by simp [pullback.condition])) =
      pullback.fst (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)) ⁻¹'
        Set.range (pullback.diagonal p) := by
    rw [← Scheme.Pullback.range_fst, ← hL.isoPullback_hom_fst]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨hL.isoPullback.inv y, ?_⟩
      change ((hL.isoPullback.inv ≫ hL.isoPullback.hom) ≫ pullback.fst _ _) y = _
      rw [Iso.inv_hom_id, Category.id_comp]
  rw [hr]
end GlobalTheory.SpreadSep
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SpreadSep
universe u
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.SpreadSep
namespace _root_.GlobalTheory.SpreadSep
theorem _root_.solution (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V]
    [Algebra k V] (X : Scheme.{0}) (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) (h₁ : LocallyOfFiniteType p) (h₂ : QuasiCompact p)
    (h : IsSeparated (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsSeparated (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) := by
  haveI := h₁
  haveI := h₂
  let pB : pullback p p ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k := pullback.snd p p ≫ p
  haveI : IsLocallyNoetherian (pullback p p) := LocallyOfFiniteType.isLocallyNoetherian pB
  haveI : CompactSpace ↥(_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  haveI : CompactSpace ↥(pullback p p) := QuasiCompact.compactSpace_of_compactSpace pB
  haveI : QuasiSeparated pB := inferInstance
  haveI : AlgebraicGeometry.IsNoetherian (pullback p p) := {}
  let D := _root_.GlobalTheory.Spread.bcDiagram pB V
  let c := _root_.GlobalTheory.Spread.bcCone pB V
  have hc := _root_.GlobalTheory.Spread.isLimitBcCone pB V
  haveI : ∀ {i j : (Finset V)ᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
    fun f => _root_.GlobalTheory.Spread.instIsAffineHomMapOppositeFinsetSchemeBcDiagram pB V f
  haveI : ∀ i, CompactSpace (D.obj i) := _root_.GlobalTheory.Spread.instCompactSpaceCarrierCarrierCommRingCatObjOppositeFinsetSchemeBcDiagramOfQuasiCompact pB V
  haveI : ∀ i, QuasiSeparatedSpace (D.obj i) := _root_.GlobalTheory.Spread.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeFinsetSchemeBcDiagramOfQuasiSeparated pB V
  have hπ : ∀ (j : (Finset V)ᵒᵖ) (x : c.pt),
      pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j) : Set V))))
        (c.π.app j x) = pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)) x := by
    intro j x
    have e : c.π.app j ≫ pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k
        (Algebra.adjoin k (↑(Opposite.unop j) : Set V)))) = pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)) := by
      simp only [c, _root_.GlobalTheory.Spread.bcCone]
      exact _root_.GlobalTheory.Spread.bcMap_fst _ _
    rw [← e]
    try rfl
  have hmap : ∀ {j j' : (Finset V)ᵒᵖ} (f : j ⟶ j') (x : D.obj j),
      pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j') : Set V))))
        (D.map f x) =
      pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j) : Set V)))) x := by
    intro j j' f x
    have e : D.map f ≫ pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k
        (Algebra.adjoin k (↑(Opposite.unop j') : Set V)))) =
        pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j) : Set V)))) := by
      simp only [D, _root_.GlobalTheory.Spread.bcDiagram]
      exact _root_.GlobalTheory.Spread.bcMap_fst _ _
    rw [← e]
    try rfl
  let i₀ : (Finset V)ᵒᵖ := Opposite.op ∅
  let f₀ := pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop i₀) : Set V))))
  obtain ⟨U, Z, hU, hZ, hT⟩ := (pullback.diagonal p).isLocallyClosed_range
  let O : (D.obj i₀).Opens := f₀ ⁻¹ᵁ ⟨U, hU⟩
  let O' : (D.obj i₀).Opens := f₀ ⁻¹ᵁ ⟨Zᶜ, hZ.isOpen_compl⟩
  have hcpt : ∀ W : (pullback p p).Opens, IsCompact ((f₀ ⁻¹ᵁ W : (D.obj i₀).Opens) : Set (D.obj i₀)) :=
    fun W => QuasiCompact.isCompact_preimage (f := f₀) _ W.isOpen
      (TopologicalSpace.NoetherianSpace.isCompact _)
  have hset : ∀ y : D.obj i₀, y ∈ (O : Set (D.obj i₀)) \ O' ↔ f₀ y ∈ Set.range (pullback.diagonal p) := by
    intro y
    rw [hT]
    change (f₀ y ∈ U ∧ ¬ f₀ y ∈ Zᶜ) ↔ _
    simp
  have H : IsClosed (c.π.app i₀ ⁻¹' ((O : Set (D.obj i₀)) \ O')) := by
    have h' := (isSeparated_pullback_snd_spMap_iff_isClosed_preimage k V X p).1 h
    have hs : c.π.app i₀ ⁻¹' ((O : Set (D.obj i₀)) \ O') =
        pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)) ⁻¹' Set.range (pullback.diagonal p) := by
      ext x
      exact (hset (c.π.app i₀ x)).trans
        (Iff.of_eq (congrArg (· ∈ Set.range (pullback.diagonal p)) (hπ i₀ x)))
    rw [hs]
    exact h'
  obtain ⟨j, f, hj⟩ := _root_.GlobalTheory.SpreadSep.exists_isClosed_preimage_diff D c hc O O' (hcpt _) (hcpt _) H
  refine ⟨Algebra.adjoin k (↑(Opposite.unop j) : Set V), Subalgebra.fg_adjoin_finset _, ?_⟩
  rw [isSeparated_pullback_snd_spMap_iff_isClosed_preimage]
  have hs : D.map f ⁻¹' ((O : Set (D.obj i₀)) \ O') =
      pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j) : Set V)))) ⁻¹'
        Set.range (pullback.diagonal p) := by
    ext x
    exact (hset (D.map f x)).trans
      (Iff.of_eq (congrArg (· ∈ Set.range (pullback.diagonal p)) (hmap f x)))
  rw [hs] at hj
  exact hj
end _root_.GlobalTheory.SpreadSep
end GlobalTheory.SpreadSep

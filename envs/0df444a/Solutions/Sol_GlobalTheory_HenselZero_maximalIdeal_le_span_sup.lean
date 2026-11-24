-- Prove2me | solution 1 for GlobalTheory.HenselZero.maximalIdeal_le_span_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:03.240249+00:00
-- url     : https://prove2.me/submissions/74da4e3b-c8af-4be1-a9bc-7e1d98f185c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Theorems.Thm_GlobalTheory_HenselZero_exists_factor_stalk
import Theorems.Thm_GlobalTheory_HenselZero_isClosedImmersion_fibre
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
variable {O : Type} [CommRing O] [IsLocalRing O] {X Y : Scheme.{0}} {p : X ⟶ Sp O} {q : Y ⟶ Sp (ResidueField O)}
  {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
include hφ
namespace GlobalTheory.HenselZero
theorem _root_.solution {ι : Type} (y : Y) (α : CommRingCat.of O ⟶ X.presheaf.stalk (φ y))
    (hα : Spec.map α = X.fromSpecStalk (φ y) ≫ p) (f : ι → X.presheaf.stalk (φ y))
    (h : maximalIdeal _ ≤ Ideal.span (Set.range fun i => (φ.stalkMap y).hom (f i))) :
    maximalIdeal _ ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map α.hom := by
  have := isClosedImmersion_fibre hφ
  let I := (maximalIdeal O).map α.hom
  by_cases hI : I = ⊤
  · exact le_sup_of_le_right (le_top.trans hI.ge)
  have : Nontrivial (X.presheaf.stalk (φ y) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (X.presheaf.stalk (φ y) ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
  let π : X.presheaf.stalk (φ y) ⟶ .of (X.presheaf.stalk (φ y) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let β : ResidueField O →+* X.presheaf.stalk (φ y) ⧸ I := Ideal.quotientMap I α.hom Ideal.le_comap_map
  have hw : (Spec.map π ≫ X.fromSpecStalk (φ y)) ≫ p = spMap β ≫ spMap (residue O) := by
    rw [Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨χ, hχ⟩ := exists_factor_stalk (hφ.lift _ _ hw) (y := y) (φ.isClosedEmbedding.injective (by
    refine (congrArg (fun g => g (closedPoint (X.presheaf.stalk (φ y) ⧸ I))) (hφ.lift_fst _ _ hw)).trans ?_
    exact (congrArg (X.fromSpecStalk (φ y)) (comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint))
  have e : φ.stalkMap y ≫ χ = π := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (φ y)), Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      reassoc_of% hχ, hφ.lift_fst]
  have e' : ∀ a, χ.hom ((φ.stalkMap y).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun g => g.hom a) e
  intro a ha
  obtain hr := Ideal.mem_map_of_mem χ.hom (h (map_nonunit (φ.stalkMap y).hom a ha))
  rw [e', Ideal.map_span, ← Set.range_comp] at hr
  have hr' : Ideal.Quotient.mk I a ∈ (Ideal.span (Set.range f)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact (congrArg (fun F => _ ∈ Ideal.span (Set.range F)) (funext fun i => e' (f i))).mp hr
  exact Ideal.mem_quotient_iff_mem_sup.1 hr'
end GlobalTheory.HenselZero

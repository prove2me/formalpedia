-- Prove2me | solution 1 for GlobalTheory.exists_add_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:36:59.309749+00:00
-- url     : https://prove2.me/submissions/8ff7b736-382d-48f4-b369-12b4174e2845

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
import Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_triples
import Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory
open MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open SmoothLocusAdd
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∃ add : (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⊗ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ add).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) := by
  intro R _ _ _ W U hU hs hg
  let G : Over (Spec (.of R)) := Over.mk (U.ι ≫ WeierstrassCurve.toSpec W)
  have hG : IsIntegral (U : Scheme) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (U.ι ≫ WeierstrassCurve.toSpec W)
  have hN : IsLocallyNoetherian (U : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ WeierstrassCurve.toSpec W)
  have hGG : IsIntegral (G ⊗ G).left := inferInstanceAs (IsIntegral
    (pullback (U.ι ≫ WeierstrassCurve.toSpec W) (U.ι ≫ WeierstrassCurve.toSpec W)))
  have hns : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ (U : Scheme)),
      IsNonsingularAt W (x ≫ U.ι) := fun k _ x ρ P hP e => (hU k ρ P hP).mp (by
    rw [← e]
    intro y _
    exact (x y).2)
  let p : (G ⊗ G).left ⟶ (U : Scheme) := (fst G G).left
  let q : (G ⊗ G).left ⟶ (U : Scheme) := (snd G G).left
  have hp : p ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom := Over.w (fst G G)
  have hq : q ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom := Over.w (snd G G)
  have hpq : (p ≫ U.ι) ≫ WeierstrassCurve.toSpec W = (q ≫ U.ι) ≫ WeierstrassCurve.toSpec W := by
    rw [Category.assoc, Category.assoc, hp, hq]
  obtain ⟨s, hs₁, hs₂⟩ := exists_sum W (p ≫ U.ι) (q ≫ U.ι) hpq
    (fun k _ x => by rw [← Category.assoc]; exact hns k _)
    (fun k _ x => by rw [← Category.assoc]; exact hns k _)
  have hr : Set.range s ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    let x := (G ⊗ G).left.fromSpecResidueField z
    obtain ⟨ρ, P, Q, hP, hQ, eP, eQ⟩ := exists_triples W (k := (G ⊗ G).left.residueField z)
      (x ≫ p ≫ U.ι) (x ≫ q ≫ U.ι) (by rw [Category.assoc, Category.assoc x, hpq])
    obtain ⟨h, e⟩ := hs₂ ((G ⊗ G).left.residueField z) x ρ P Q hP hQ eP eQ
    have nP := hns ((G ⊗ G).left.residueField z) (x ≫ p) ρ P hP ((Category.assoc _ _ _).trans eP)
    have nQ := hns ((G ⊗ G).left.residueField z) (x ≫ q) ρ Q hQ ((Category.assoc _ _ _).trans eQ)
    have := (hU _ ρ _ h).mpr (WeierstrassCurve.Projective.nonsingular_add nP nQ)
    rw [← e] at this
    have h2 : s (x (IsLocalRing.closedPoint _)) ∈ U := this (Set.mem_univ _)
    have h3 : x (IsLocalRing.closedPoint _) = z := Scheme.fromSpecResidueField_apply z _
    rw [h3] at h2
    rw [Scheme.Opens.range_ι]
    exact h2
  have hl : IsOpenImmersion.lift U.ι s hr ≫ U.ι = s := IsOpenImmersion.lift_fac ..
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι s hr) ?_, ?_⟩
  · change IsOpenImmersion.lift U.ι s hr ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom
    rw [← Category.assoc, hl, hs₁, Category.assoc, hp]
  · intro k _ ρ x y P Q hP hQ ex ey
    let w : Spec (.of k) ⟶ (G ⊗ G).left := (lift x y).left
    have e₁ : w ≫ p = x.left := congrArg (·.left) (lift_fst x y)
    have e₂ : w ≫ q = y.left := congrArg (·.left) (lift_snd x y)
    obtain ⟨h, e⟩ := hs₂ k w ρ P Q hP hQ
      (by rw [← Category.assoc, e₁]; exact ex) (by rw [← Category.assoc, e₂]; exact ey)
    refine ⟨h, ?_⟩
    change (w ≫ IsOpenImmersion.lift U.ι s hr) ≫ U.ι = _
    rw [Category.assoc, hl, e]
end GlobalTheory

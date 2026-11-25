-- Prove2me | solution 1 for GlobalTheory.HomExtension.finite_torsion_images
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:28:47.83031+00:00
-- url     : https://prove2.me/submissions/0570081c-4608-4f4a-b0b6-0c14ac2c6493

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulEquivOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_SemiAbTorsion_comp_pow_points
import Theorems.Thm_GlobalTheory_exists_mulEquiv_of_isGrpPullback
import Theorems.Thm_GlobalTheory_semiAbelian_torsion_finite_and_closedPoint_finiteOrder
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
open GlobalTheory.HomExtension
namespace GlobalTheory.HomExtension
theorem _root_.solution
    (hab : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
      ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1})
    {Z : Scheme.{0}} (G : Over Z) [GrpObj G] (hG : IsSemiAbelian G) (z : Z) {n : ℕ} (hn : 1 ≤ n) :
    {w : G.left | G.hom w = z ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (t : Sp k ⟶ Z)
      (x : Over.mk t ⟶ G), x ^ n = 1 ∧ w ∈ Set.range x.left}.Finite := by
  let Ω : Type := AlgebraicClosure (Z.residueField z)
  let q : Sp Ω ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Ω)) ≫ Z.fromSpecResidueField z
  have := hG.comm
  have h1 := (semiAbelian_torsion_finite_and_closedPoint_finiteOrder hab).1 Ω
    ((Over.pullback q).obj G) (hG.fibres Ω q) n hn
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G q) (𝟙 (Sp Ω)) q
    (Category.id_comp _).symm
  have h2 : Finite {x : Over.mk q ⟶ G // x ^ n = 1} := by
    have : Finite {x : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback q).obj G // x ^ n = 1} := h1
    refine Finite.of_injective (β := {x : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback q).obj G // x ^ n = 1})
      (fun x => ⟨e.symm x.1, by rw [← map_pow, x.2, map_one]⟩) fun x y h => ?_
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
  let pt : Sp Ω := (⊥ : PrimeSpectrum Ω)
  refine (Set.finite_range fun x : {x : Over.mk q ⟶ G // x ^ n = 1} => x.1.left pt).subset ?_
  rintro w ⟨hw, k, _, _, t, x, hx, s, rfl⟩
  obtain ⟨⟨z', ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Z).symm.surjective t
  have hz : z' = z := by
    rw [← hw, ← Scheme.Hom.comp_apply, Over.w x]
    exact (Z.fromSpecResidueField_apply z' _).symm
  subst hz
  letI : Algebra (Z.residueField z') k := ψ.hom.toAlgebra
  let τ : k →ₐ[Z.residueField z'] Ω := IsAlgClosed.lift
  have hτ : spMap τ.toRingHom ≫ Spec.map ψ =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z') Ω)) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact τ.commutes a
  let u : Over.mk q ⟶ Over.mk ((Scheme.SpecToEquivOfField k Z).symm ⟨z', ψ⟩) :=
    Over.homMk (spMap τ.toRingHom) (by
      change spMap τ.toRingHom ≫ Spec.map ψ ≫ _ = _
      rw [reassoc_of% hτ]; rfl)
  refine ⟨⟨u ≫ x, by rw [← SemiAbTorsion.comp_pow_points, hx, MonObj.comp_one]⟩, ?_⟩
  have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  change (spMap τ.toRingHom ≫ x.left) pt = _
  rw [Scheme.Hom.comp_apply]
  exact congrArg _ (Subsingleton.elim (α := Sp k) _ _)
end GlobalTheory.HomExtension

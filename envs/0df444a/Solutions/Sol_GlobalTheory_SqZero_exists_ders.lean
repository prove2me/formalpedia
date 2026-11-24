-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_ders
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:31:51.691939+00:00
-- url     : https://prove2.me/submissions/dc6270c2-3225-4334-907d-35e49da6e4ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
variable (R B)
namespace GlobalTheory.SqZero
theorem _root_.solution [Algebra.Smooth R B] :
    ∃ (κ : Type) (_ : Fintype κ) (β : κ → B) (τ : κ → Derivation R B B),
      ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : B →ₐ[R] A),
        (∀ b b', (φ b - φ' b) * (φ b' - φ' b') = 0) →
        ∀ b, φ b - φ' b = ∑ i, φ' (τ i b) * (φ (β i) - φ' (β i)) := by
  have hfg : (Submodule.span B (Set.range (KaehlerDifferential.D R B))).FG := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Module.Finite.fg_top
  obtain ⟨s', hsub, hs'⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hex : ∀ x : s', ∃ b, KaehlerDifferential.D R B b = x := fun x => hsub x.2
  choose β hβ using hex
  have hspan : Submodule.span B (Set.range fun x : s' => KaehlerDifferential.D R B (β x)) = ⊤ := by
    rw [show (Set.range fun x : s' => KaehlerDifferential.D R B (β x)) = ↑s' by
      ext ω
      simp [hβ]]
    rw [← hs', KaehlerDifferential.span_range_derivation]
  have hsurj : Function.Surjective
      (Fintype.linearCombination B (fun x : s' => KaehlerDifferential.D R B (β x))) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  obtain ⟨h, hh⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
  let τ : s' → Derivation R B B := fun x => (LinearMap.proj x ∘ₗ h).compDer (KaehlerDifferential.D R B)
  have hD : ∀ b, KaehlerDifferential.D R B b =
      ∑ x, τ x b • KaehlerDifferential.D R B (β x) := fun b => by
    conv_lhs => rw [← LinearMap.id_apply (R := B) (KaehlerDifferential.D R B b), ← hh]
    simp [τ, Fintype.linearCombination_apply]
  refine ⟨s', inferInstance, β, τ, fun A _ _ φ φ' hprod b => ?_⟩
  let _ : Algebra B A := φ'.toRingHom.toAlgebra
  have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq fun r => (φ'.commutes r).symm
  let δ : Derivation R B A :=
    { toFun := fun b => φ b - φ' b
      map_add' := fun b b' => by simp only [map_add]; ring
      map_smul' := fun r b => by simp [smul_sub]
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        show φ (a * b) - φ' (a * b) = φ' a * (φ b - φ' b) + φ' b * (φ a - φ' a)
        rw [map_mul, map_mul]
        linear_combination hprod a b }
  have key := congrArg δ.liftKaehlerDifferential (hD b)
  simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D] at key
  exact key
end GlobalTheory.SqZero

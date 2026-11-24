-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.extends_of_regular_second_axis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:20:18.963262+00:00
-- url     : https://prove2.me/submissions/79339577-3edd-4365-b043-aed1066e0e67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFactorOfRangeSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ArcExtendsOfRegularSecondAxis
import Theorems.Thm_GlobalTheory_SS_ArcInf_exists_lift_var
import Theorems.Thm_GlobalTheory_SS_ArcInf_algOverHom_comp
import Theorems.Thm_GlobalTheory_SS_ArcInf_exists_extend_of_localSubring
import Theorems.Thm_GlobalTheory_TwoVarValRing_exists_local_ring_second_variable


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
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf
theorem _root_.solution :
    ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ (a : algOver k (FractionRing (PowerSeries k)) ⟶ G) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → TwoVar j f a h d → (∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) → ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a := by
  intro k _ G _ A _ _ j ε r f hc a h d hd ht hreg
  obtain ⟨σ₀, h0⟩ := exists_lift_var k 0
  obtain ⟨σ₁, h1⟩ := exists_lift_var k 1
  obtain ⟨L, hloc, hmem, hL0, hL1⟩ := GlobalTheory.TwoVarValRing.exists_local_ring_second_variable k σ₀ σ₁ h0 h1
  have hd' : algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k)) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hd
  obtain ⟨χ, hχ, he⟩ := ht (FractionRing (MvPowerSeries (Fin 2) k))
    (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))) σ₀ σ₁ hd' h0 h1
  have hf : ∀ i, χ (f i) ∈ L := by
    intro i
    obtain ⟨u, v, hv, huv⟩ := hreg i
    refine hmem _ u v hv ?_
    have e1 := hχ i
    simp only [IsScalarTower.toAlgHom_apply] at e1
    have e2 := congrArg (algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))) huv
    rw [map_mul, map_mul, ← e1] at e2
    apply mul_left_cancel₀ hd'
    rw [← e2]
    ring
  have hall : ∀ x, χ x ∈ L := by
    have : Algebra.adjoin k (Set.range f) ≤ L.comap χ :=
      Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hf i)
    intro x
    exact this (by rw [hc.2.2.1]; trivial)
  refine GlobalTheory.SS.ArcInf.exists_extend_of_localSubring k G (PowerSeries k) (FractionRing (PowerSeries k)) (FractionRing (MvPowerSeries (Fin 2) k))
    _ σ₁ L hloc (IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))) hL1 a
    ((algOverHom (χ.codRestrict L hall) ≫ j) * (algOverHom (σ₀.codRestrict L hL0) ≫ a)) ?_
  rw [he, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← algOverHom_comp, ← algOverHom_comp]
  rfl
end GlobalTheory.SS.ArcInf

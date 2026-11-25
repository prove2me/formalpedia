-- Prove2me | solution 1 for GlobalTheory.mapDeg_eq_pow_mul_card_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:49.280721+00:00
-- url     : https://prove2.me/submissions/b05e0f2c-71c4-4369-97f4-d16782c7e5d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
import Theorems.Thm_GlobalTheory_DegKer_finrank_eq_pow_mul_card
import Theorems.Thm_GlobalTheory_DegKer_card_fibre_eq
import Theorems.Thm_GlobalTheory_DegKer_card_ker_eq
import Theorems.Thm_GlobalTheory_DegKer_card_coset_eq
import Theorems.Thm_GlobalTheory_DegKer_exists_mapDeg_of_isFinite
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_ZV_ActsBy_comp
import Theorems.Thm_GlobalTheory_ZV_MapDeg_finrank_eq
import Theorems.Thm_GlobalTheory_flat_and_surjective_of_isFinite_grpEnd
import Theorems.Thm_GlobalTheory_polAV_isIntegral_of_isAlgClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open DegKer
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A), IsMonHom α → IsFinite α.left → Finite {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1} ∧ ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1}) := by
  intro K _ _ P α _ _
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P.isAb.smooth
  have hs := (flat_and_surjective_of_isFinite_grpEnd K P.A α).2
  obtain ⟨D, -, hD⟩ := exists_mapDeg_of_isFinite _ _ α.left inferInstance hs
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ := P.A.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint P.A.left)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : Nonempty (α.left ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := α.left.surjective (genericPoint P.A.left)
    exact ⟨⟨x, show α.left x ∈ U from hx ▸ hξ⟩⟩
  letI := (α.left.app U).hom.toAlgebra
  have : Module.Finite Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U) := α.left.finite_app U hU
  have : IsSchemeTheoreticallyDominant α.left := .of_isDominant _
  have : FaithfulSMul Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (α.left.app_injective U)
  let c : K →+* Γ(P.A.left, U) :=
    (P.A.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : ExpChar Γ(P.A.left, U) (ringExpChar K) := expChar_of_injective_ringHom c.injective _
  let Ω := AlgebraicClosure (FractionRing Γ(P.A.left, U))
  have : FaithfulSMul Γ(P.A.left, U) Ω := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq Γ(P.A.left, U) (FractionRing Γ(P.A.left, U)) Ω, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective _ _)
  obtain ⟨h0, e, he⟩ := finrank_eq_pow_mul_card Γ(P.A.left, U) Γ(P.A.left, α.left ⁻¹ᵁ U) Ω
    (ringExpChar K)
  rw [card_fibre_eq α.left hU Ω] at h0 he
  set z := Spec.map (CommRingCat.ofHom (algebraMap Γ(P.A.left, U) Ω)) ≫ hU.fromSpec with hz
  let z' : Over.mk (z ≫ P.A.hom) ⟶ P.A := Over.homMk z rfl
  have h1 : Nat.card {y : Over.mk (z ≫ P.A.hom) ⟶ P.A // y ≫ α = z'} =
      Nat.card {y : Spec (CommRingCat.of Ω) ⟶ P.A.left // y ≫ α.left = z} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨y.1.left, congrArg CommaMorphism.left y.2⟩) ⟨?_, ?_⟩)
    · intro y y' h
      exact Subtype.ext (Over.OverMorphism.ext (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      refine ⟨⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩, rfl⟩
      change y ≫ P.A.hom = z ≫ P.A.hom
      rw [← hy, Category.assoc, Over.w α]
  rw [← h1] at h0 he
  have hne := (Nat.card_ne_zero.mp h0).1
  rw [← card_coset_eq P.A _ α z' hne,
    ← card_ker_eq P.A α Ω (z ≫ P.A.hom)] at h0 he
  refine ⟨(Nat.card_ne_zero.mp h0).2, e, ?_⟩
  rw [← he, hD.finrank_eq U hU ⟨_, hξ⟩]
  exact hD
end GlobalTheory

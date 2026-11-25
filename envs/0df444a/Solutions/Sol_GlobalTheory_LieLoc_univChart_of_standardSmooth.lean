-- Prove2me | solution 1 for GlobalTheory.LieLoc.univChart_of_standardSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:56:38.039872+00:00
-- url     : https://prove2.me/submissions/e181d3d1-d8d3-4a2b-aefe-1e0341d1879e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnivChartOfStandardSmooth
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_etale_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_etale_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_trunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetZero_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_nil_of_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieLoc
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
namespace GlobalTheory.LieLoc
theorem _root_.solution (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (S : Type) [CommRing S] [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (j : sp (R₀ := R) S ⟶ G) (ε : S →ₐ[R] R) (hε : spMap ε ≫ j = 1)
    (hj : ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R), IsNilpotent (RingHom.ker aug) →
      ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ φ : S →ₐ[R] A, y = spMap φ ≫ j)
    (hinj : ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : S →ₐ[R] A),
      spMap φ ≫ j = spMap φ' ≫ j → φ = φ') :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G, IsUnivChart G n x := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R S
  letI : Algebra (MvPolynomial (Fin n) R) S := g.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) S := hg
  have hπ : ∀ m : ℕ, ∃ π : S →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε ∧
      ∀ i, π (sX R i) = algebraMap R _ (ε (sX R i)) + zR m i := fun m =>
    etale_exists (n := n) ε (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun i => by
      rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨fun m => spMap (π m) ≫ j, fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, spMap_comp]
    congr 2
    refine etale_ext (n := n) ε (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro i
      rw [AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]
      rfl
  · have e : (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp ε := by
      refine etale_ext (n := n) ε (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
        exact hπaug m
      · ext s
        simp
      · intro i
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
        rfl
    rw [← Category.assoc, spMap_comp, e, ← spMap_comp, Category.assoc, hε, comp_one']
  · intro A _ _ aug m hJ y hy
    have hJn := nil_of_pow _ hJ
    obtain ⟨φ, rfl⟩ := hj A aug hJn y hy
    have hφ : aug.comp φ = ε := hinj _ _ _ (by rw [← spMap_comp, Category.assoc, hy, hε])
    have hmem : ∀ i : Fin n, φ (sX (S := S) R i) - algebraMap R A (ε (sX (S := S) R i)) ∈
        RingHom.ker aug := by
      intro i
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ, sub_self]
    let ψ := jetLift R (RingHom.ker aug) hJ
      (fun i : Fin n => φ (sX (S := S) R i) - algebraMap R A (ε (sX (S := S) R i))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun i => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem i
    have hψπ : ψ.comp (π m) = φ := by
      refine etale_ext (n := n) ε aug hJn _ _ ?_ hφ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · intro i
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, ?_⟩, ?_⟩
    · rw [← Category.assoc, spMap_comp, hψπ]
    · rintro ψ₂ ⟨_, h2⟩
      rw [← Category.assoc, spMap_comp] at h2
      have h4 := (hinj _ _ _ h2).symm
      apply jet_ext
      intro i
      rw [jetLift_zR]
      have := AlgHom.congr_fun h4 (sX R i)
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes] at this
      rw [← this, add_sub_cancel_left]
end GlobalTheory.LieLoc

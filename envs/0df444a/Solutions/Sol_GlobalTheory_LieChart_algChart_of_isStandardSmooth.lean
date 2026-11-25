-- Prove2me | solution 1 for GlobalTheory.LieChart.algChart_of_isStandardSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:38.719565+00:00
-- url     : https://prove2.me/submissions/0ea1ae82-6a92-4322-8bcb-7bfe169a7b26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
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
open GlobalTheory GlobalTheory.LieChart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
namespace GlobalTheory.LieChart
theorem _root_.solution {R : Type} [CommRing R] (B : Type) [CommRing B] [Algebra R B]
    (hB : (algebraMap R B).IsStandardSmooth) (ε' : B →ₐ[R] R) :
    ∃ (n : ℕ) (π : ∀ m : ℕ, B →ₐ[R] JetR R (Fin n) m),
      (∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m) ∧
      (∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp ε') ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ →
        ∀ φ : B →ₐ[R] A, aug.comp φ = ε' →
          ∃! ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin n) m ∧ ψ.comp (π m) = φ := by
  obtain ⟨n, g, hgC, hg⟩ := hB.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin n) R) B := g.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) B := IsScalarTower.of_algebraMap_eq' hgC.symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hg
  have hπ : ∀ m : ℕ, ∃ π : B →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε' ∧
      ∀ j, π (sX R j) = algebraMap R _ (ε' (sX R j)) + zR m j := fun m =>
    etale_exists (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun j => by
      rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨n, π, ?_, ?_, ?_⟩
  · intro m
    refine etale_ext (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro j
      rw [AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]
      rfl
  · intro m
    refine etale_ext (n := n) ε' (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
      exact hπaug m
    · ext s
      simp
    · intro j
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
      rfl
  · intro A _ _ aug m hJ φ' hφ'aug
    have hJn := nil_of_pow _ hJ
    have hmem : ∀ j : Fin n, φ' (sX (S := B) R j) -
        algebraMap R A (ε' (sX (S := B) R j)) ∈ RingHom.ker aug := by
      intro j
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ'aug, sub_self]
    let ψ := jetLift R (RingHom.ker aug) hJ
      (fun j : Fin n => φ' (sX (S := B) R j) - algebraMap R A (ε' (sX (S := B) R j))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun j => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem j
    have hψπ : ψ.comp (π m) = φ' := by
      refine etale_ext (n := n) ε' aug hJn _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · exact hφ'aug
      · intro j
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, hψπ⟩, ?_⟩
    rintro ψ₂ ⟨_, h4⟩
    apply jet_ext
    intro j
    rw [jetLift_zR]
    have := AlgHom.congr_fun h4 (sX R j)
    rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes] at this
    rw [← this, add_sub_cancel_left]
end GlobalTheory.LieChart

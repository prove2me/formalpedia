-- Prove2me | solution 1 for GlobalTheory.LatticeHom.exists_linearEquiv_of_lifting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:55.677741+00:00
-- url     : https://prove2.me/submissions/82125dde-e1ac-40bb-9371-b4dad7897d89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaUnifAVOfLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivOfLifting
import Theorems.Thm_GlobalTheory_LatticeHom_eq_zero_of_forall_smul_mem
import Theorems.Thm_GlobalTheory_EndoLinear_fderiv_lifts
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom
namespace GlobalTheory.LatticeHom
theorem _root_.solution {A : Over (Sp ℂ)} [GrpObj A] {L L₁ : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (v : HolUnif A L₁ g)
    (hv : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (a w).left U f)
          {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 →
      ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, v.ex (G w) = a w) :
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, v.ex (T z) = u.ex z := by
  obtain ⟨G, hG0, hGa, hGe⟩ := hv g u.ex (fun U f => by simpa using u.hol U f)
    ((u.ker 0).2 u.Λ.zero_mem)
  have hT := EndoLinear.fderiv_lifts v.ex v.ex_add v.Λ v.ker v.discrete u.ex u.ex_add G hG0
    hGa.differentiableAt hGe
  have hi : Function.Injective (fderiv ℂ G 0).toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    refine eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => ?_
    have hz' : fderiv ℂ G 0 z = 0 := hz
    rw [← u.ker, ← hT, map_smul, hz', smul_zero]
    exact (v.ker 0).2 v.Λ.zero_mem
  exact ⟨LinearEquiv.ofInjectiveEndo _ hi, hT⟩
end GlobalTheory.LatticeHom

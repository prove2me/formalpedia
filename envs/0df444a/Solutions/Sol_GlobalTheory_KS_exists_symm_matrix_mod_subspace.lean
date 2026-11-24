-- Prove2me | solution 1 for GlobalTheory.KS.exists_symm_matrix_mod_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:46:55.000231+00:00
-- url     : https://prove2.me/submissions/a0c93cd2-6fc5-4115-8ba9-70abdde2f86d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Theorems.Thm_GlobalTheory_KS_exists_dual_family_mod_subspace

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (B : Submodule K V) (g : ℕ) (θ φ : Fin g → V), (∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0) → (∀ α β : Module.Dual K V, B ≤ LinearMap.ker α → B ≤ LinearMap.ker β → ∑ a, α (θ a) * β (φ a) = ∑ a, α (φ a) * β (θ a)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, θ b - ∑ a, Θ b a • φ a ∈ B := by
  intro K V _ _ _ B g θ φ hind hsym
  classical
  obtain ⟨β, hβB, hβφ⟩ := exists_dual_family_mod_subspace K V B g φ hind

  have key : ∀ α : Module.Dual K V, B ≤ LinearMap.ker α →
      ∀ b, α (θ b) = ∑ a, α (φ a) * β b (θ a) := by
    intro α hα b
    rw [← hsym α (β b) hα (hβB b)]
    simp [hβφ]
  refine ⟨Matrix.of fun b a => β b (θ a), Matrix.IsSymm.ext fun i j => ?_, fun b => ?_⟩
  · simp only [Matrix.of_apply]
    rw [key (β i) (hβB i) j]
    simp [hβφ]
  · simp only [Matrix.of_apply]
    by_contra hx
    have hq : B.mkQ (θ b - ∑ a, β b (θ a) • φ a) ≠ 0 :=
      fun h0 => hx ((Submodule.Quotient.mk_eq_zero B).mp h0)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual K (V ⧸ B), f (B.mkQ (θ b - ∑ a, β b (θ a) • φ a)) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hq ((Module.forall_dual_apply_eq_zero_iff K _).mp hall)
    apply hf
    have hα : B ≤ LinearMap.ker (f.comp B.mkQ) := fun x hx =>
      by simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]
    have hk := key (f.comp B.mkQ) hα b
    simp only [LinearMap.comp_apply] at hk
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, hk]
    simp [mul_comm]
end GlobalTheory.KS

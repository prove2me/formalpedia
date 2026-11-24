-- Prove2me | solution 1 for GlobalTheory.KS.exists_det_ne_zero_of_common_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:52.442248+00:00
-- url     : https://prove2.me/submissions/2e4d3425-5eb0-47df-9280-e171024e42cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoords

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
theorem _root_.solution {K J : Type} [Field K] {g : ℕ} (φ : J → (Fin g → K) →ₗ[K] K)
    (h : ∀ w, (∀ i, φ i w = 0) → w = 0) :
    ∃ c : Fin g → J, (Matrix.of fun a b => φ (c b) (Pi.single a 1)).det ≠ 0 := by
  classical
  let ψ : J → Module.Dual K (Fin g → K) := φ
  have hspan : Submodule.span K (Set.range ψ) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hco : (Submodule.span K (Set.range ψ)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      exact (Submodule.mem_bot K).2 (h w fun i => hw _ (Submodule.subset_span ⟨i, rfl⟩))
    have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span K (Set.range ψ))
    rw [hco, finrank_bot, add_zero] at hdim
    rw [hdim, Subspace.dual_finrank_eq]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range ψ)
  let B : Module.Basis b K (Module.Dual K (Fin g → K)) :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hspan]))
  let D : Module.Basis (Fin g) K (Module.Dual K (Fin g → K)) := (Pi.basisFun K (Fin g)).dualBasis
  let e : b ≃ Fin g := B.indexEquiv D
  have hex : ∀ k : Fin g, ∃ j, ψ j = ((e.symm k : b) : Module.Dual K (Fin g → K)) := fun k => hbsub (e.symm k).2
  choose c hc using hex
  refine ⟨c, ?_⟩
  have hM : (Matrix.of fun a k => φ (c k) (Pi.single a 1)) = D.toMatrix (B.reindex e) := by
    ext a k
    rw [Matrix.of_apply]
    change ψ (c k) (Pi.single a 1) = _
    rw [hc k]
    simp only [Module.Basis.toMatrix_apply, D, Module.Basis.dualBasis_repr,
      Module.Basis.reindex_apply, B, Module.Basis.mk_apply, Pi.basisFun_apply]
  rw [hM]
  intro h0
  have hone := congrArg Matrix.det (D.toMatrix_mul_toMatrix_flip (B.reindex e))
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hone
  exact zero_ne_one hone
end GlobalTheory.KS

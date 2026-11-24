-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.exists_mem_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:27.083518+00:00
-- url     : https://prove2.me/submissions/a0cfd6fa-04b5-422b-a76f-5215a2fef8f9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_residue_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.IwContract
theorem _root_.solution (M : Matrix (Fin n) (Fin n) F) (h1 : ∀ i j, valuation F (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → valuation F (M i j) < 1) (h3 : ∀ i, valuation F (M i i) = 1) :
    ∃ g ∈ GlobalTheory.SmGL.iwahori F (Fin n), g.val = M := by
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := fun i j => ⟨M i j, h1 i j⟩
  have hdet : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, det_of_upperTriangular]
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      show IsLocalRing.residue 𝒪[F] (A i i) ≠ 0
      rw [Ne, residue_eq_zero_iff]
      exact not_lt.2 (h3 i).ge
    · intro i l hl
      show IsLocalRing.residue 𝒪[F] (A i l) = 0
      exact (residue_eq_zero_iff _).2 (h2 i l hl)
  refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[F] F) (GeneralLinearGroup.mk'' A hdet),
    GlobalTheory.SmGL.mem_iwahori.2 ⟨⟨_, rfl⟩, fun i j hij => h2 i j hij⟩, ?_⟩
  ext i j
  rfl
end GlobalTheory.CompanionTheory.IwContract

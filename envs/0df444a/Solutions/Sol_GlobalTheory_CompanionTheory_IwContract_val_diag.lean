-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.val_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:20.445355+00:00
-- url     : https://prove2.me/submissions/43a06aef-ee3a-4e82-a49b-09346acb593c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_residue_eq_zero_iff
import Theorems.Thm_GlobalTheory_SmGL_mem_borel


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
theorem _root_.solution {g : GL (Fin n) F} (hg : g ∈ GlobalTheory.SmGL.iwahori F (Fin n)) (i : Fin n) :
    valuation F (g.val i i) = 1 := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 := (GeneralLinearGroup.det (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) h)).ne_zero
  rw [GeneralLinearGroup.val_det_apply, det_of_upperTriangular (GlobalTheory.SmGL.mem_borel _ |>.1 hh)] at h1
  have h2 : IsLocalRing.residue 𝒪[F] (h.val i i) ≠ 0 := Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ i)
  rw [Ne, residue_eq_zero_iff] at h2
  exact le_antisymm (h.val i i).2 (not_lt.1 h2)
end GlobalTheory.CompanionTheory.IwContract

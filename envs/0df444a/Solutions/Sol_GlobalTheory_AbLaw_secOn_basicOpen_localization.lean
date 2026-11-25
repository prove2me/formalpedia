-- Prove2me | solution 1 for GlobalTheory.AbLaw.secOn_basicOpen_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:11:38.679361+00:00
-- url     : https://prove2.me/submissions/8ecc253e-dcfa-4b29-ad74-b068984a7786

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_pow_smul_eq_res_of_qcqs
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_pow_smul_eq_zero_of_isCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V W : Y.Opens) (a : Γ(Y, V)) (h : W ≤ V), M.IsLB → IsCompact (V : Set Y) → IsQuasiSeparated (V : Set Y) → W = Y.basicOpen a → (∀ x : SecOn M V, SecOn.restrict M h x = 0 → ∃ k : ℕ, a ^ k • x = 0) ∧ ∀ y : SecOn M W, ∃ (k : ℕ) (x : SecOn M V), SecOn.restrict M h x = rs Y h a ^ k • y := by
  intro Y M V W a h hM hV hV' hW
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hM
  refine ⟨fun x hx => GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact (GlobalTheory.LB.toMod M) hV a h hW x hx,
    fun y => ?_⟩
  obtain ⟨k, x, e⟩ := GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod M) hV hV' a h hW y
  exact ⟨k, x, e.symm⟩
end GlobalTheory.AbLaw

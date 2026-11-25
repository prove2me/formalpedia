-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Isolate.hk_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:08.009401+00:00
-- url     : https://prove2.me/submissions/13d08aab-a2b6-4b54-93d7-73b73fb3e80d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsolateRepresentationAtCharacter
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Isolate
open GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
variable {K : Subgroup (GL ι F)} {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL ι F) V)
namespace GlobalTheory.CompanionTheory.Isolate
theorem _root_.solution (e : GL ι F → ℂ) : hk ρ K e (0 : V) = 0 := by
  simp [hk]
end GlobalTheory.CompanionTheory.Isolate

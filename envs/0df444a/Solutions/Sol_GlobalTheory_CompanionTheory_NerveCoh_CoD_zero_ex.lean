-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.CoD.zero_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:28:17.462747+00:00
-- url     : https://prove2.me/submissions/5651c81c-8d3d-4175-b529-3124f311c570

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
variable {E : Type} [Category.{0} E]
variable [Quiver.IsThin E]
variable {H : E ⥤ ModuleCat.{0} R} {B : E → ModuleCat.{0} R}
namespace GlobalTheory.CompanionTheory.NerveCoh
namespace CoD
theorem _root_.solution (A : CoD H B) (b : ∀ y, B y) :
    ∃ a : MCn H 0, mdn H 0 a = 0 ∧ ∀ y, A.ev (𝟙 y) (a (pt y)) = b y := by
  have : ∀ c : Fin 1 ⥤ E, ∃ v : H.obj (c.obj (Fin.last 0)), ∀ (y : E) (f : c.obj (Fin.last 0) ⟶ y), A.ev f v = b y :=
    fun c ↦ A.ex fun y _ ↦ b y
  choose a ha using this
  refine ⟨a, ?_, fun y ↦ ha (pt y) y (𝟙 y)⟩
  funext c
  refine A.ext _ fun y f ↦ ?_
  rw [A.ev_mdn, Fin.sum_univ_two]
  have e : (0 : B y) = ((-1 : R) ^ ((0 : Fin 2) : ℕ)) • b y + ((-1 : R) ^ ((1 : Fin 2) : ℕ)) • b y := by simp
  exact (congrArg₂ (· + ·) (congrArg _ (ha (fc 0 c) y _)) (congrArg _ (ha (fc 1 c) y _))).trans e.symm
end CoD
end GlobalTheory.CompanionTheory.NerveCoh

-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.supportedIn_le_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:34:31.096836+00:00
-- url     : https://prove2.me/submissions/9c1fe724-6434-478d-8956-cfc7ba2bc6bd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
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
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ} (γ : Fin n → ℕ)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable {σ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {Y : Set (GL (Fin n) F)}
    (hY : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y) {q : GL (Fin n) F}
    (hq : q ∈ blockUpper F n γ) :
    supportedIn σ Y ≤ (supportedIn σ Y).comap (parabolicInd F n β σ q) := by
  intro f hf g hg
  show ((parabolicInd F n β σ q f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) g = 0
  rw [coe_indRep_apply]
  apply hf
  intro hgq
  apply hg
  simpa using hY _ hgq _ ((blockUpper F n γ).inv_mem hq)
end GroundTheory.Automorphic.Parabolic

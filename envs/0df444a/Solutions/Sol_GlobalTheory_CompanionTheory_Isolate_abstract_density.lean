-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Isolate.abstract_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:10.866516+00:00
-- url     : https://prove2.me/submissions/8325bd6b-a159-4b1a-a8cf-ec8580ea8086

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsolateRepresentationAtCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_SimpleDensity_exists_smul_eq_end
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
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
namespace GlobalTheory.CompanionTheory.Isolate
theorem _root_.solution {I : Type} [Fintype I] (M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, FiniteDimensional ℂ (M i)] [∀ i, Nontrivial (M i)]
    (A : Subalgebra ℂ (∀ i, Module.End ℂ (M i)))
    (hsimple : ∀ i (S : Submodule ℂ (M i)), (∀ a ∈ A, ∀ x ∈ S, a i x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hiso : ∀ i j (φ : M i ≃ₗ[ℂ] M j), (∀ a ∈ A, ∀ x, φ (a i x) = a j (φ x)) → i = j)
    (f : ∀ i, Module.End ℂ (M i)) : ∃ a ∈ A, ∀ i, a i = f i := by
  classical
  let ev : ∀ i, A →+* Module.End ℂ (M i) := fun i =>
    (Pi.evalRingHom (fun i => Module.End ℂ (M i)) i).comp A.val.toRingHom
  letI : ∀ i, Module A (M i) := fun i => Module.compHom _ (ev i)
  haveI : ∀ i, IsScalarTower ℂ A (M i) := fun i => ⟨fun c a x => rfl⟩
  haveI : ∀ i, IsSimpleModule A (M i) := by
    intro i
    refine (isSimpleModule_iff A (M i)).2 ⟨fun S => ?_⟩
    rcases hsimple i (S.restrictScalars ℂ) (fun a ha x hx => S.smul_mem ⟨a, ha⟩ hx) with h | h
    · left
      exact Submodule.restrictScalars_injective ℂ _ _ (by simpa using h)
    · right
      exact Submodule.restrictScalars_injective ℂ _ _ (by simpa using h)
  have hiso' : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j := by
    rintro i j ⟨φ⟩
    exact hiso i j (φ.restrictScalars ℂ) fun a ha x => φ.map_smul ⟨a, ha⟩ x
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.SimpleDensity.exists_smul_eq_end A I M hiso' f
  exact ⟨a.1, a.2, fun i => LinearMap.ext fun x => ha i x⟩
end GlobalTheory.CompanionTheory.Isolate

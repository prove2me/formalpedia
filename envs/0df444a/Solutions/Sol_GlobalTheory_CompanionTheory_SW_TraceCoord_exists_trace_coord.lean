-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:15:46.542035+00:00
-- url     : https://prove2.me/submissions/6abe8f6e-2b7f-4a10-8a68-550985d8cf41

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_trace_hform
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_coord_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_coord_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_dot_mulVec_left
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_hform_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_mat_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_sigR_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_gramB_tensor
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_sig_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_gramB_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_gramB_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) ∧ ∀ h : HA R σ J, ∀ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, (∀ p q, g p q = (Algebra.TensorProduct.basis R b).repr ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2) → gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ x : Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  refine ⟨gramB (σ : E →+* E) b J, gramB_symm σ hσ J hJ b, gramB_det σ hσ J hJ b, fun x => ?_,
    fun R _ _ => ?_⟩
  · exact trace_hform (σ : E →+* E) (sig_smul σ) b J x x
  · have key : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        coord (Algebra.TensorProduct.basis R b) x ⬝ᵥ
          ((gramB (σ : E →+* E) b J).map (algebraMap F R) *ᵥ
            coord (Algebra.TensorProduct.basis R b) y) := fun x y => by
      rw [← gramB_tensor]
      exact trace_hform (sigR R σ) (sigR_smul R σ) _ (JR R J) x y
    refine ⟨key, fun h g hg => ?_⟩
    have hact := coord_mulVec (Algebra.TensorProduct.basis R b)
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) g (fun p q => by
        rw [hg, Algebra.TensorProduct.basis_apply]
        rfl)
    refine ⟨?_, hact⟩
    have hU : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J :=
      (show HR R σ J from h).2
    apply mat_ext
    intro u v
    obtain ⟨x, rfl⟩ := coord_surj (M := M) (Algebra.TensorProduct.basis R b) u
    obtain ⟨y, rfl⟩ := coord_surj (M := M) (Algebra.TensorProduct.basis R b) v
    have h1 := key ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y)
    have h2 : hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
        ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y :=
      hform_mulVec _ _ _ hU x y
    rw [h2, key x y, hact x, hact y, dot_mulVec_left, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at h1
    exact h1.symm
end GlobalTheory.CompanionTheory.SW.TraceCoord

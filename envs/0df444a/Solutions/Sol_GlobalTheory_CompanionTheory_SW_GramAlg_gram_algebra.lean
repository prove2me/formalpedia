-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:01:29.025645+00:00
-- url     : https://prove2.me/submissions/bdd4e90a-7531-47bf-bce7-6c172ea46bdf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_colM_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_mul_shape
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_cT_cT
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_sigma_invol
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_sigR_invol
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_gramR_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_colM_rmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_colM_actTup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
namespace GlobalTheory.CompanionTheory.SW.GramAlg
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ), (∀ (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g) ∧ (∀ (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), rmul R (rmul R X g) g' = rmul R X (g * g')) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, rmul R X 1 = X) ∧ (∀ (S : HermR R σ n) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n) ∧ ∀ (J' : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) = gramR R σ J' X := by
  intro F E _ _ _ _ _ σ hσ M J _ R _ _ n
  have hs : ∀ x : R ⊗[F] E, sigR R σ (sigR R σ x) = x := sigR_invol R (sigma_invol hσ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X g
    rw [gramR_eq, gramR_eq, colM_rmul, cT_mul]
    exact mul_shape _ _ _ _ _
  · intro X g g'
    apply colM_injective
    rw [colM_rmul, colM_rmul, colM_rmul, Matrix.mul_assoc]
  · intro X
    apply colM_injective
    rw [colM_rmul, Matrix.mul_one]
  · intro S g
    have hS : cT (sigR R σ) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = S := by
      ext a b
      exact S.2 a b
    have key : cT (sigR R σ) (cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g)
        = cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g := by
      rw [cT_mul, cT_mul, cT_cT _ hs, hS, Matrix.mul_assoc]
    intro a b
    exact congrFun (congrFun key a) b
  · intro J' g hJ X
    rw [gramR_eq, gramR_eq, colM_actTup, cT_mul, hJ]
    exact mul_shape _ _ _ _ _
end GlobalTheory.CompanionTheory.SW.GramAlg

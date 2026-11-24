-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.exists_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:29.302996+00:00
-- url     : https://prove2.me/submissions/f890680c-999c-4359-b4fd-1499f0f29087

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_trace_sigma
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_exists_orthonormal
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_exists_mem_X_of_N_ne_zero
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_exists_basis_of_orthonormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (x : B.Aˣ),
    Module.finrank K.E B.A = n → B.σ (x : B.A) = x → B.N x ≠ 0 →
    ∃ (γ : Matrix (Fin n) (Fin n) K.E) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  intro K B n x hn hσx hN
  obtain ⟨L, ⟨hfg, hspan⟩, -, hdual⟩ := exists_mem_X_of_N_ne_zero B (x : B.A) hN
  have hadd : ∀ y y' z, B.herm x (y + y') z = B.herm x y z + B.herm x y' z := by
    intro y y' z
    simp only [InvAlg.herm, mul_add, add_mul, map_add]
  have hsmul : ∀ (a : K.E) y z, B.herm x (a • y) z = a * B.herm x y z := by
    intro a y z
    simp only [InvAlg.herm, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hsym : ∀ y z, B.herm x z y = K.c (B.herm x y z) := by
    intro y z
    simp only [InvAlg.herm]
    rw [← trace_sigma B, map_mul B.σ, map_mul B.σ, B.σ_σ, hσx]
    congr 1
    ring
  obtain ⟨v, hv⟩ := exists_orthonormal n B.A (B.herm x) hadd hsmul hsym hn L hfg hspan hdual
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormal (B.herm x) hadd hsmul hn v hv
  let ℓ : B.A → B.A →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => B.herm x y z, map_add' := fun y y' => hadd y y' z, map_smul' := fun a y => hsmul a y z }
  have hexp : ∀ y w, B.herm x y w = ∑ i, b.repr y i * B.herm x (b i) w := by
    intro y w
    have h1 : ℓ w y = ℓ w (∑ i, b.repr y i • b i) := by rw [b.sum_repr]
    rw [map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    exact h1
  have hcol : ∀ i z, B.herm x (b i) z = K.c (b.repr z i) := by
    intro i z
    rw [hsym, hexp z (b i)]
    simp only [hb, hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g), b.equivFun, hσx, fun y => ?_, fun y z => ?_⟩
  · rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
    rfl
  · rw [hexp y z]
    simp only [stdH, Module.Basis.equivFun_apply, hcol]
end GlobalTheory.InertUnitOrb.ModelOfN

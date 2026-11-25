-- Prove2me | solution 1 for GlobalTheory.SW.Emb.transH_drop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:53.560065+00:00
-- url     : https://prove2.me/submissions/0aa9e09a-8b6a-4547-8574-70ab9438de21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_cor_inv
import Theorems.Thm_GlobalTheory_SW_Emb_corZ_mem
import Theorems.Thm_GlobalTheory_SW_Emb_pushZ_corZ
import Theorems.Thm_GlobalTheory_SW_Emb_dropZ_corZ
import Theorems.Thm_GlobalTheory_SW_Emb_drop_corV
import Theorems.Thm_GlobalTheory_SW_Emb_hDen_emb
import Theorems.Thm_P2M_GlobalTheory_SW_Emb_hDen__emb_8e89cf070fb7
import Theorems.Thm_GlobalTheory_SW_Emb_hAct_emb
import Theorems.Thm_GlobalTheory_SW_Emb_hFac_emb
import Theorems.Thm_GlobalTheory_SW_TransComp_key
import Theorems.Thm_GlobalTheory_T_tendsto_thH_pushZ_atTop_thH_dropF
import Theorems.Thm_GlobalTheory_T_unitary_act_halfSpace_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.Emb
theorem _root_.solution (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ ψ : Matrix (Fin n) (Fin (N + 1)) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    (h : TransH Ψ (emb γ) φ ψ) : TransH Ψ γ (dropF φ) (dropF ψ) := by
  intro Z hZ z z'
  obtain ⟨hden, hact, -⟩ := (GlobalTheory.T.unitary_act_halfSpace_alt E Ψ N γ hγ).2 Z hZ
  have hdet : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ => (hden τ).1
  have hdet' : ∀ τ, (hDen' Ψ γ Z τ).det ≠ 0 := fun τ h0 =>
    (hden τ).1 (by rw [← (hden τ).2.1, h0, zero_mul])
  obtain ⟨w, hw⟩ : ∃ w : CM Ψ n N, w = fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : CM Ψ n N, w' = fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hw, ← hw']
  have hWφ := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N φ hφ).2 (corZ I Z) (corZ_mem hZ)
  have hWψ := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N ψ hψ).2 (corZ I (hAct Ψ γ Z)) (corZ_mem hact)
  have L1 := hWφ.2.2 (corV z) (corV z')
  have L2 := hWψ.2.2 (corV w) (corV w')
  simp only [dropZ_corZ, drop_corV] at L1 L2
  have key : ∀ t : ℝ, 0 ≤ t →
      thH Ψ ψ (pushZ Ψ (corZ I (hAct Ψ γ Z)) (Pi.single 0 1) t) (corV w) (corV w') =
        hFac Ψ γ Z z z' * thH Ψ φ (pushZ Ψ (corZ I Z) (Pi.single 0 1) t) (corV z) (corV z') := by
    intro t ht
    have hmem := hWφ.2.1 t ht
    have e := h _ hmem (corV z) (corV z')
    simp only [pushZ_corZ] at hmem e ⊢
    rw [hAct_emb γ _ Z hdet, hFac_emb γ _ Z hdet] at e
    rw [← e]
    congr 1
    · funext τ
      ext k j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [hw, corV, hDen'_emb, cor_inv _ (hdet' τ), Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · funext τ
      ext k j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [hw', corV, hDen_emb, cor_inv _ (hdet τ), Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  exact tendsto_nhds_unique_of_eventuallyEq L2 (L1.const_mul _) ((Filter.eventually_ge_atTop 0).mono key)
end GlobalTheory.SW.Emb

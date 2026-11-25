-- Prove2me | solution 1 for GlobalTheory.SW.Emb.exists_botSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:18.576008+00:00
-- url     : https://prove2.me/submissions/6931aa72-f430-48c7-9c3d-bc2849b20b23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_ccT_fromBlocks
import Theorems.Thm_GlobalTheory_SW_Emb_botSpan_eq
import Theorems.Thm_GlobalTheory_SW_Emb_botSpan_emb
import Theorems.Thm_GlobalTheory_SW_Emb_botSpan_mul_le
import Theorems.Thm_GlobalTheory_SW_Emb_exists_col
import Theorems.Thm_GlobalTheory_SW_Emb_sub_mem
import Theorems.Thm_GlobalTheory_SW_Base_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul
import Theorems.Thm_GlobalTheory_SW_Base_ccT_one
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_mul
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_one
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
theorem _root_.solution {g : M2 E (N + 1)} (hg : g ∈ UU E (N + 1))
    (h0 : ∀ a, g.toBlocks₂₁ a 0 = 0) : ∃ γ ∈ UU E N, botSpan g = botSpan (emb γ) := by
  have hgU := (GlobalTheory.T.unitary_act_halfSpace_alt E (∅ : Finset (E →+* ℂ)) (N + 1) g hg).1
  have h0' : ∀ a, g (Sum.inr a) (Sum.inl 0) = 0 := fun a => by simpa [Matrix.toBlocks₂₁] using h0 a
  obtain ⟨v, hvd⟩ : ∃ v : Fin (N + 1) → E, v = fun i => g (Sum.inl i) (Sum.inl 0) := ⟨_, rfl⟩
  have hv : v ≠ 0 := by
    intro hv0
    refine (isUnit_iff_ne_zero.mp hgU.1) (Matrix.det_eq_zero_of_column_eq_zero (Sum.inl 0) ?_)
    rintro (i | i)
    · have := congrFun hv0 i
      rw [hvd] at this
      simpa using this
    · exact h0' i
  obtain ⟨b, hb, hbv⟩ := exists_col v hv
  have e2 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv _ hb
  have e1 : ccT b⁻¹ * ccT b = 1 := by rw [← Base.ccT_mul, e2, Base.ccT_one]
  have e0 : ccT (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) E) = 0 := by
    ext i j; simp [ccT, cc]
  obtain ⟨δ, hδd⟩ : ∃ δ : M2 E (N + 1), δ = Matrix.fromBlocks b⁻¹ 0 0 (ccT b) := ⟨_, rfl⟩
  have hδ : δ ∈ UU E (N + 1) := by
    show ccT δ * Matrix.J _ E * δ = Matrix.J _ E
    rw [hδd, ccT_fromBlocks, e0, Base.ccT_ccT, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [e1, e2]
  have hh : δ * g ∈ UU E (N + 1) := hgU.2.2.2.2 δ hδ
  have hv' : b *ᵥ Pi.single 0 1 = v := by
    funext i; simp [Matrix.mulVec_single, hbv]
  have hinv : b⁻¹ *ᵥ v = Pi.single 0 1 := by
    rw [← hv', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]
  have hc : ∀ i, (δ * g) i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : _ → E) i := by
    rintro (i | i)
    · have := congrFun hinv i
      rw [hvd] at this
      simp only [Matrix.mulVec, dotProduct] at this
      simp [hδd, Matrix.mul_apply, Fintype.sum_sum_type, h0', this, Pi.single_apply]
    · simp [hδd, Matrix.mul_apply, Fintype.sum_sum_type, h0']
  obtain ⟨hrow, hsub⟩ := sub_mem hh hc
  have h1 : ∀ a, (δ * g) (Sum.inr a) (Sum.inl 0) = 0 := fun a => by rw [hc]; simp
  refine ⟨(δ * g).submatrix (up N) (up N), hsub, ?_⟩
  rw [botSpan_emb, ← botSpan_eq (δ * g) hrow h1]
  apply le_antisymm
  · calc botSpan g = botSpan (Matrix.fromBlocks b 0 0 (ccT b⁻¹) * (δ * g)) := by
          rw [← Matrix.mul_assoc, hδd, Matrix.fromBlocks_multiply]
          simp [e1, e2]
      _ ≤ botSpan (δ * g) := botSpan_mul_le _ _ _
  · rw [hδd]
    exact botSpan_mul_le _ _ _
end GlobalTheory.SW.Emb

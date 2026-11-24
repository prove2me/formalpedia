-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.exists_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:35.679614+00:00
-- url     : https://prove2.me/submissions/edc5324c-fb6c-43ca-8d8a-55327b7f5f80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
import Theorems.Thm_GlobalTheory_SW_UniSp_conj_apply
import Theorems.Thm_GlobalTheory_SW_Dict_sum_type
import Theorems.Thm_GlobalTheory_SW_HAct_emb_cc


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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}
namespace GlobalTheory.SW.UniSp
theorem _root_.solution [IsCMField E] (hΨ : IsType Ψ) : ∃ G : Matrix (QI E N) (QI E N) ℚ,
    qm G = Sm Ψ N * blockDiagonal (fun _ : Ψ => sw (Fin N)) * (Sm Ψ N)ᵀ := by
  refine ⟨Matrix.of fun p q => if p.1 = q.1 then
    Algebra.trace ℚ E (Module.finBasis ℚ E p.2 * cc (Module.finBasis ℚ E q.2)) else 0, ?_⟩
  ext p q
  rw [conj_apply]
  have key : ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : Ψ, (τ.1 x + conj (τ.1 x)) := by
    intro x
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)
    have h2 := Dict.sum_type hΨ (fun σ => σ x)
    simp only [ComplexEmbedding.conjugate_coe_eq] at h2
    rw [← h2, ← eq_ratCast (algebraMap ℚ ℂ), h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)) _ _ fun _ => rfl).symm
  by_cases h : p.1 = q.1
  · simp only [qm, Matrix.map_apply, Matrix.of_apply, if_pos h, key]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [Sm, sw, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, h, HAct.emb_cc]
    ring
  · simp [qm, Sm, sw, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, h, Ne.symm h]
end GlobalTheory.SW.UniSp

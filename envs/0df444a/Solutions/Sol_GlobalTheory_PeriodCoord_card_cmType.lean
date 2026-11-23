-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.card_cmType
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:46.161507+00:00
-- url     : https://prove2.me/submissions/5ac11709-4f98-4864-81e5-bdaf03647ea0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_conjugate_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodCoord
theorem _root_.solution (H : Host E) :
    Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  have h2 : (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card =
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card := by
    have hinv : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      fun τ => star_star τ
    refine Finset.card_bij' (fun τ _ => ComplexEmbedding.conjugate τ) (fun τ _ => ComplexEmbedding.conjugate τ)
      ?_ ?_ (fun τ _ => hinv τ) (fun τ _ => hinv τ)
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [conjugate_mem_iff]; exact fun h => h hτ
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [conjugate_mem_iff]; exact hτ
  rw [Finset.card_univ, Embeddings.card] at h1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega
end GlobalTheory.PeriodCoord

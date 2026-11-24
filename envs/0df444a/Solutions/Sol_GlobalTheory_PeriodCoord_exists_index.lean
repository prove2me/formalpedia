-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.exists_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:22:56.867184+00:00
-- url     : https://prove2.me/submissions/ccb57e48-e6e8-4205-8633-35f2b4d2b58a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_conjugate_mem_iff
import Theorems.Thm_GlobalTheory_PeriodCoord_card_cmType

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
theorem _root_.solution (hty : IsTypeFn H D.p D.q ty) : ∃ e : Fin D.dim → Fin g × Fin g,
    ∀ i j, ty i (H.rt : E) = H.rt0 → ty j = ComplexEmbedding.conjugate (ty i) → ∃ k, e k = (i, j) := by
  classical
  let I := Σ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
    {i // ty i = τ.1} × {j // ty j = ComplexEmbedding.conjugate τ.1}
  have hI : Nat.card I = D.dim := by
    rw [Nat.card_sigma, Finset.sum_congr rfl (g := fun _ => D.p * D.q), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, card_cmType, Datum.dim, smul_eq_mul, mul_assoc]
    intro τ _
    rw [Nat.card_prod, (hty _).1 τ.2, (hty _).2 fun h => (conjugate_mem_iff H _).1 h τ.2]
  let e : I ≃ Fin D.dim := Finite.equivFinOfCardEq hI
  refine ⟨fun k => ((e.symm k).2.1.1, (e.symm k).2.2.1), fun i j hi hj =>
    ⟨e ⟨⟨ty i, hi⟩, ⟨i, rfl⟩, ⟨j, hj⟩⟩, ?_⟩⟩
  simp only []
  rw [e.symm_apply_apply]
end GlobalTheory.PeriodCoord

-- Prove2me | solution 1 for GlobalTheory.PeriodDatum.two_mul_eq_of_isTypeFn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:08.098803+00:00
-- url     : https://prove2.me/submissions/d7a5848a-1828-4c06-bce9-2aad8698f881

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_PeriodNonempty_sum_type
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
open GlobalTheory GlobalTheory.PeriodDatum
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodDatum
theorem _root_.solution (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) :
    2 * g = Module.finrank ℚ E * (p + q) := by
  classical
  let e := (Fintype.equivFin (E →+* ℂ)).symm
  have he : IsTypeFn H 1 1 e := fun τ => by
    have : Nat.card {i // e i = τ} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩, ⟨⟨e.symm τ, by simp⟩⟩⟩
    exact ⟨fun _ => this, fun _ => this⟩
  have h1 := PeriodNonempty.sum_type H hty 1
  have h2 := PeriodNonempty.sum_type H he 1
  simp only [map_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Embeddings.card, Nat.cast_one] at h1 h2
  have : (2 * g : ℂ) = Module.finrank ℚ E * (p + q) := by rw [h1, h2]; ring
  exact_mod_cast this
end GlobalTheory.PeriodDatum

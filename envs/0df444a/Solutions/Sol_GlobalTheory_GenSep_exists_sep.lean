-- Prove2me | solution 1 for GlobalTheory.GenSep.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:48:48.593381+00:00
-- url     : https://prove2.me/submissions/58a85d43-bdd1-4e92-a199-8c206367b613

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_ne_zero_of_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_weak_approx_orders


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}
variable {K' : Type} [Field K'] (φ : MvPolynomial (Fin (D + 1) × Fin N) (la.adicCompletionIntegers K) →+* K')
  (κ : la.adicCompletion K →+* K') (x : Fin N → Ω)
variable {la φ κ x}
namespace GlobalTheory.GenSep
theorem _root_.solution (v v' : AddValuation Ω (WithTop ℤ)) (h : ∃ a, v a = 1) (h' : ∃ a, v' a = 1) (hne : v ≠ v') :
    ∃ a, 0 < v a ∧ 0 < v' (a - 1) := by
  obtain ⟨s, hs⟩ := weak_approx_orders ![v, v'] (fun i a ha => by rw [Ne, AddValuation.top_iff]; exact ha)
    (fun i => by fin_cases i; exacts [h, h'])
    (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [hne.symm]) ![1, -1]
  have s1 : v s = ((1 : ℤ) : WithTop ℤ) := hs 0
  have s2 : v' s = ((-1 : ℤ) : WithTop ℤ) := hs 1
  have t1 : v (1 + s) = ((0 : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_add_eq_of_lt_left _ (by
      rw [AddValuation.map_one, s1]; exact_mod_cast (zero_lt_one : (0 : ℤ) < 1)),
      AddValuation.map_one, WithTop.coe_zero]
  have t2 : v' (1 + s) = ((-1 : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_add_eq_of_lt_right _ (by
      rw [AddValuation.map_one, s2]; exact_mod_cast (by omega : (-1 : ℤ) < 0)), s2]
  have h0 : 1 + s ≠ 0 := wa_ne_zero_of_coe _ t1
  refine ⟨s / (1 + s), ?_, ?_⟩
  · rw [wa_div _ s1 t1]; exact_mod_cast (by omega : (0 : ℤ) < 1 - 0)
  · have : s / (1 + s) - 1 = -(1 + s)⁻¹ := by field_simp; ring
    rw [this, AddValuation.map_neg, wa_inv _ t2]; exact_mod_cast (by omega : (0 : ℤ) < - -1)
end GlobalTheory.GenSep

-- Prove2me | solution 1 for GlobalTheory.GenSep.aeval_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:00.186351+00:00
-- url     : https://prove2.me/submissions/584fe499-7e7a-464f-a5a5-af6f53bb6c71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax

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
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace GlobalTheory.GenSep
theorem _root_.solution {F : Type} [Field F] [Algebra Ω F] (x : Fin N → Ω) (j0 : Fin N) (hx : x j0 ≠ 0)
    (u : Fin (D + 1) × Fin N → F) (hrel : ∀ i : Fin D, ∑ k, u (i.succ, k) * algebraMap Ω F (x k) = 0)
    (p : Fin (D + 1) × Fin N) : aeval (fun s : Free D N j0 => u s.1) (subst x j0 p) = u p := by
  classical
  unfold subst
  split_ifs with h
  · simp
  · obtain ⟨i, k⟩ := p
    simp only [not_or, ne_eq, not_not] at h
    obtain ⟨h1, rfl⟩ := h
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 h1
    have hr := hrel i'
    rw [Fintype.sum_eq_add_sum_subtype_ne _ k] at hr
    have hx' : algebraMap Ω F (x k) ≠ 0 := (map_ne_zero _).2 hx
    simp only [map_neg, map_sum, map_mul, aeval_C, aeval_X, map_div₀]
    apply mul_right_cancel₀ hx'
    rw [neg_mul, Finset.sum_mul, eq_comm, ← add_eq_zero_iff_eq_neg, ← hr]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
end GlobalTheory.GenSep

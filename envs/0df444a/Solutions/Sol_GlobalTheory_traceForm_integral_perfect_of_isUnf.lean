-- Prove2me | solution 1 for GlobalTheory.traceForm_integral_perfect_of_isUnf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:50.411013+00:00
-- url     : https://prove2.me/submissions/ec7c6b47-3da5-4aca-b751-162ffedf590d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_TraceFormIntegralPerfectOfIsUnf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ k, (∀ x ∈ (U.X k).Λ, ∀ y ∈ (U.X k).Λ, ∃ n : ℤ, EFf (U.X k).ξ0 (U.X k).Gm x y = n) ∧ ∀ φ : (U.X k).Λ →+ ℤ, ∃ x ∈ (U.X k).Λ, ∀ y : (U.X k).Λ, (φ y : ℚ) = EFf (U.X k).ξ0 (U.X k).Gm x y := by
  intro E _ _ _ H Dw l Xo c σ r U hU k
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hφ, -⟩ := hU
  refine ⟨fun x hx y hy => ?_, fun ψ => ?_⟩
  · refine ⟨(F.Di (ik k)).EF ((φ k).symm ⟨x, hx⟩) ((φ k).symm ⟨y, hy⟩), ?_⟩
    rw [hφ k]
    simp only [LinearEquiv.apply_symm_apply, EFf]
  · obtain ⟨a, ha⟩ := (F.Di (ik k)).unimod.2
      (ψ.comp (φ k).toLinearMap.toAddMonoidHom).toIntLinearMap
    refine ⟨φ k a, (φ k a).2, fun y => ?_⟩
    have h := hφ k a ((φ k).symm y)
    rw [ha] at h
    simpa [EFf] using h
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.AnArc.periods_polarised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:44.502549+00:00
-- url     : https://prove2.me/submissions/400d6595-930b-4f3a-bc58-a0623c0ef37f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_EF_bijective
import Theorems.Thm_GlobalTheory_AnArc_exists_BwMat_posDef
import Theorems.Thm_GlobalTheory_AnArc_Hw_conj
import Theorems.Thm_GlobalTheory_AnArc_Hw_pos
import Theorems.Thm_GlobalTheory_AnArc_im_Hw_Pw
import Theorems.Thm_GlobalTheory_AnArc_Pw_lattice
import Theorems.Thm_GlobalTheory_AnArc_period_clauses
import Theorems.Thm_GlobalTheory_AnArc_EF_isAlt
import Theorems.Thm_GlobalTheory_AnArc_EF_smul
import Theorems.Thm_GlobalTheory_AnArc_Pw_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution :
    A.EF.IsAlt ∧ Function.Bijective A.EF ∧ (∀ (a : O) x y, A.EF (a • x) y = A.EF x (star a • y)) ∧
    ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im →
      (A.BwMat w).PosDef ∧ Function.Injective (A.Pw w) ∧ (∀ (a : O) x, A.Pw w (a • x) = A.actV a (A.Pw w x)) ∧
      DiscreteTopology (A.Pw w).range ∧ Submodule.span ℝ (Set.range (A.Pw w)) = ⊤ ∧
      (∀ v v', starRingEnd ℂ (A.Hw w v v') = A.Hw w v' v) ∧ (∀ v, v ≠ 0 → 0 < (A.Hw w v v).re) ∧
      (∀ a b, (A.Hw w (A.Pw w a) (A.Pw w b)).im = A.EF a b) ∧
      ∀ (g : ℕ) (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (P : A.La →+ (Fin g → ℂ)), (∀ x, P x = h (A.Pw w x)) →
        Function.Injective P ∧ DiscreteTopology P.range ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
          ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            ∀ x y, (hermForm Hm (P x) (P y)).im = A.EF x y := by
  obtain ⟨T₀, hT⟩ := A.exists_BwMat_posDef
  refine ⟨A.EF_isAlt, A.EF_bijective, A.EF_smul, T₀, fun w hw => ?_⟩
  have h := hT w hw
  obtain ⟨h1, h2, h3⟩ := A.Pw_lattice h
  exact ⟨h, h1, A.Pw_smul w, h2, h3, A.Hw_conj w, fun v hv => A.Hw_pos h hv, A.im_Hw_Pw h,
    fun g k P hP => A.period_clauses h k (AddEquiv.refl _) P hP⟩
end GlobalTheory.AnArc

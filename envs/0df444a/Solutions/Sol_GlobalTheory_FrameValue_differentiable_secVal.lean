-- Prove2me | solution 1 for GlobalTheory.FrameValue.differentiable_secVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:08.640369+00:00
-- url     : https://prove2.me/submissions/f76ed5eb-7633-4dcf-b844-1ec8381c8d1c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_le_wchart_chartAt
import Theorems.Thm_GlobalTheory_FrameValue_IsLift_le_iff
import Theorems.Thm_GlobalTheory_FrameValue_frameProd_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_secVal_eq
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}
variable {u}
namespace GlobalTheory.FrameValue
theorem _root_.solution (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (p : A.left ⟶ Y) {q : E → Fin g → ℂ} (hq : Differentiable ℂ q) {z : E → K → Fin g → ℂ}
    (hd : ∀ k, Differentiable ℂ fun w => z w k) (hz : ∀ w, IsLift u φ ((u.ex (q w)).left ≫ p) (z w)) :
    Differentiable ℂ fun w => secVal u hL s ((u.ex (q w)).left ≫ p) (z w) := by
  intro w₀
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex (q w₀)).left ≫ p) ⁻¹ᵁ L.wchart φ j := ⟨_, le_wchart_chartAt hL φ _⟩
  obtain ⟨ho, hh⟩ := u.hol (p ⁻¹ᵁ L.wchart φ j) ((p.app _).hom (s.f j))
  have ho' : IsOpen {w | ⊤ ≤ ((u.ex (q w)).left ≫ p) ⁻¹ᵁ L.wchart φ j} := ho.preimage hq.continuous
  have hn := ho'.mem_nhds hj
  have d₁ : DifferentiableAt ℂ (fun w => valAt' ((u.ex (q w)).left ≫ p) (L.wchart φ j) (s.f j)) w₀ := by
    have := (hh.differentiableAt (ho.mem_nhds hj)).comp w₀ (hq w₀)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    exact ((valueRules _ (u.ex (q w)).left).2.2.2.1 _ p _ _).symm
  have d₂ : DifferentiableAt ℂ (fun w => frameProd u ε (z w) j) w₀ := by
    have a : ∀ k, DifferentiableAt ℂ (fun w => u.fr (j k) (z w k) ^ ε k) w₀ := fun k => by
      have hk := ((hz w₀).le_iff j).1 hj k
      refine DifferentiableAt.zpow ?_ (Or.inl (u.fr_ne _ _ hk))
      exact ((u.fr_hol (j k)).differentiableAt ((u.hol _ 0).1.mem_nhds hk)).comp w₀ (hd k w₀)
    classical
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (a k).hasFDerivAt).differentiableAt
  refine (d₁.fun_mul (d₂.fun_inv (frameProd_ne_zero (hz w₀) ε hj))).congr_of_eventuallyEq ?_
  filter_upwards [hn] with w hw
  exact (secVal_eq hL s (hz w) hw).trans (div_eq_mul_inv _ _)
end GlobalTheory.FrameValue

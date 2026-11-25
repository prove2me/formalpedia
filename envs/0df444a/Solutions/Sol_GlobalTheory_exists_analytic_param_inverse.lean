-- Prove2me | solution 1 for GlobalTheory.exists_analytic_param_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:16.390422+00:00
-- url     : https://prove2.me/submissions/97c6aeca-c2be-4540-94c7-845ea3fff7f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticParamInverse
import Theorems.Thm_GlobalTheory_AffinePoints_exists_openPartialHomeomorph_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Metric Set Filter Asymptotics
open scoped Topology
variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
namespace GlobalTheory
theorem _root_.solution {F : B × V → V} {b₀ : B} {A : V →L[ℂ] V}
    (hF : AnalyticAt ℂ F (b₀, 0)) (h0 : F (b₀, 0) = 0)
    (hA : HasFDerivAt (fun x => F (b₀, x)) A 0) (hinj : Function.Injective A) :
    ∃ G : B × V → V, AnalyticAt ℂ G (b₀, 0) ∧ G (b₀, 0) = 0 ∧
      ∀ᶠ q in 𝓝 ((b₀, 0) : B × V), G (q.1, F q) = q.2 ∧ F (q.1, G q) = q.2 := by
  have hd := hF.differentiableAt.hasFDerivAt
  have hA' : (fderiv ℂ F (b₀, 0)).comp (ContinuousLinearMap.inr ℂ B V) = A :=
    (HasFDerivAt.comp (f := fun x : V => (b₀, x)) (0 : V) hd
      (hasFDerivAt_prodMk_right b₀ (0 : V))).unique hA
  have hΨ : AnalyticAt ℂ (fun q : B × V => (q.1, F q)) (b₀, 0) := analyticAt_fst.prod hF
  have hdΨ : HasFDerivAt (fun q : B × V => (q.1, F q))
      ((ContinuousLinearMap.fst ℂ B V).prod (fderiv ℂ F (b₀, 0))) (b₀, 0) :=
    hasFDerivAt_fst.prodMk hd
  obtain ⟨Φ, hΦ, hs, ha⟩ := AffinePoints.exists_openPartialHomeomorph_analytic rfl hΨ (by
    rw [hdΨ.fderiv, injective_iff_map_eq_zero]
    rintro ⟨u, v⟩ huv
    have hu : u = 0 := congrArg Prod.fst huv
    subst hu
    have hv : A v = A 0 := by
      rw [map_zero, ← hA']
      exact congrArg Prod.snd huv
    rw [hinj hv]
    rfl)
  have hfix : Φ (b₀, 0) = (b₀, 0) := by rw [hΦ]; simp [h0]
  have ht : ((b₀, 0) : B × V) ∈ Φ.target := hfix ▸ Φ.map_source hs
  refine ⟨fun q => (Φ.symm q).2, analyticAt_snd.comp (ha _ ht), ?_, ?_⟩
  · have := Φ.left_inv hs
    rw [hfix] at this
    simp [this]
  · filter_upwards [Φ.eventually_left_inverse hs, Φ.eventually_right_inverse ht] with q h1 h2
    rw [hΦ] at h1 h2
    refine ⟨congrArg Prod.snd h1, ?_⟩
    have h3 : (Φ.symm q).1 = q.1 := by simpa using congrArg Prod.fst h2
    have h4 : F (Φ.symm q) = q.2 := congrArg Prod.snd h2
    rw [← h3]
    exact h4
end GlobalTheory

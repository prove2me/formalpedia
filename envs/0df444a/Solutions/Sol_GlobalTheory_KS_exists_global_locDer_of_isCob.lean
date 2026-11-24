-- Prove2me | solution 1 for GlobalTheory.KS.exists_global_locDer_of_isCob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:57:05.049798+00:00
-- url     : https://prove2.me/submissions/0119b9f9-e926-41dd-86e6-0258952e767d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGlobalLocDerOfIsCob
import Theorems.Thm_GlobalTheory_KS_GlueDer_rsT_eq
import Theorems.Thm_GlobalTheory_KS_GlueDer_res_res
import Theorems.Thm_GlobalTheory_KS_GlueDer_res_app
import Theorems.Thm_GlobalTheory_KS_GlueDer_app_const
import Theorems.Thm_GlobalTheory_KS_GlueDer_pre_mono
import Theorems.Thm_GlobalTheory_KS_GlueDer_glue
import Theorems.Thm_GlobalTheory_ConstThickening_res_app
import Theorems.Thm_GlobalTheory_ConstThickening_res_res
import Theorems.Thm_GlobalTheory_KS_IsCob_add
import Theorems.Thm_GlobalTheory_T_exists_unique_invariantVectorField_of_tangent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.KS.GlueDer
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁ := by
  intro K _ A₀ _ g v dd _ hv hdd R _ x₀ X p m hm I W D d θ hW hc hb
  choose b hb using hb
  have H := fun a => (GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₀ (v a) (hv.1 a)).2 (dd a) (hdd a)
  refine glue A₀.hom p m D W hW
    (fun i O f => d i O f - ∑ a, rsT (b a i) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) (fun i => ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro O hO f f'
      simp only [(hc.der i).add O hO, map_add, fun a => (H a).1, mul_add, Finset.sum_add_distrib]
      ring
    · intro O hO f f'
      simp only [(hc.der i).mul O hO, map_mul, fun a => (H a).2.1, mul_add, Finset.sum_add_distrib, mul_sub,
        Finset.mul_sum, mul_left_comm (rsT _ _)]
      ring
    · intro O O' h hO f
      have h' := pre_mono m h
      rw [(hc.der i).res O O' h hO, rsT_eq h', rsT_eq h', map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 := (H a).2.2.1 _ _ ((m.app O).hom f) h'
      rw [rsT_eq h', rsT_eq h', res_app m h] at h2
      rw [map_mul, h2, rsT_eq (pre_mono m hO), rsT_eq (pre_mono m (h.trans hO)), res_res]
    · intro O hO r
      simp only [(hc.der i).base O hO, app_const x₀ p A₀.hom m hm.w, fun a => (H a).2.2.2.1, mul_zero,
        Finset.sum_const_zero, sub_zero]
  · intro i j O hO f
    have h1 := hc.diff i j O hO f
    have hi : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i := pre_mono m (hO.trans inf_le_left)
    have hj : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W j := pre_mono m (hO.trans inf_le_right)
    have h2 : ∀ a, rsT (θ a i j) (m ⁻¹ᵁ O) = rsT (b a j) (m ⁻¹ᵁ O) - rsT (b a i) (m ⁻¹ᵁ O) := by
      intro a
      rw [hb, rsT_eq (le_inf hi hj), map_sub, rsT_eq inf_le_right, rsT_eq inf_le_left, res_res, res_res,
        rsT_eq hi, rsT_eq hj]
    simp only [h2, sub_mul, Finset.sum_sub_distrib] at h1
    show _ - _ = _ - _
    linear_combination -h1
end GlobalTheory.KS

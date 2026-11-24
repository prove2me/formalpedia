-- Prove2me | solution 1 for GlobalTheory.KS.GlueDer.glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:55.109753+00:00
-- url     : https://prove2.me/submissions/302f494f-782d-46f8-9779-1dcdefcad75b

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
import Theorems.Thm_GlobalTheory_KS_GlueDer_res_const
import Theorems.Thm_GlobalTheory_KS_GlueDer_pre_mono
import Theorems.Thm_GlobalTheory_KS_GlueDer_pre_cover
import Theorems.Thm_GlobalTheory_ConstThickening_res_app
import Theorems.Thm_GlobalTheory_ConstThickening_res_res
import Theorems.Thm_GlobalTheory_KS_IsCob_add


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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.GlueDer
namespace GlobalTheory.KS.GlueDer
theorem _root_.solution {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (D : R → K) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤)
    (e : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)) (he : ∀ i, LocDerK q p m D (W i) (e i))
    (hc : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, e i O f = e j O f) : ∃ d₁, LocDerK q p m D ⊤ d₁ := by
  have ex : ∀ (O : X.Opens) (f : Γ(X, O)), ∃ s : Γ(Y, m ⁻¹ᵁ O), ∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f) := by
    intro O f
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O)
      (fun i => e i (O ⊓ W i) (resG X inf_le_left f)) (by
        intro i j
        have hi := (he i).res (O ⊓ W i) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_left inf_le_right (resG X inf_le_left f)
        have hj := (he j).res (O ⊓ W j) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_right inf_le_right (resG X inf_le_left f)
        rw [rsT_eq (pre_mono m inf_le_left), res_res] at hi
        rw [rsT_eq (pre_mono m inf_le_right), res_res] at hj
        have := hc i j ((O ⊓ W i) ⊓ (O ⊓ W j)) (inf_le_inf inf_le_right inf_le_right)
          (resG X (inf_le_left.trans inf_le_left) f)
        exact hi.symm.trans (this.trans hj))
    exact ⟨s, hs⟩
  have ext : ∀ (O : X.Opens) (s t : Γ(Y, m ⁻¹ᵁ O)), (∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) t) →
      s = t := fun O s t h =>
    Y.sheaf.eq_of_locally_eq' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O) s t h
  choose d₁ hd using ex
  refine ⟨d₁, ?_, ?_, ?_, ?_⟩
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add, hd, hd, hd, map_add, (he i).add _ inf_le_right]
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add, map_mul, map_mul, hd, hd, hd, map_mul, (he i).mul _ inf_le_right,
      res_app m inf_le_left, res_app m inf_le_left]
  · intro O O' h _ f
    refine ext O' _ _ fun i => ?_
    have h' : O' ⊓ W i ≤ O ⊓ W i := inf_le_inf_right _ h
    have h1 := (he i).res (O ⊓ W i) (O' ⊓ W i) h' inf_le_right (resG X inf_le_left f)
    rw [rsT_eq (pre_mono m h'), res_res, ← hd, res_res] at h1
    rw [hd, rsT_eq (pre_mono m h), res_res, res_res, h1]
  · intro O _ r
    refine ext O _ _ fun i => ?_
    rw [hd, res_const, res_const, (he i).base _ inf_le_right]
end GlobalTheory.KS.GlueDer

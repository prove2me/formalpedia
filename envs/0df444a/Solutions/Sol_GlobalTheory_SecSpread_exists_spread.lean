-- Prove2me | solution 1 for GlobalTheory.SecSpread.exists_spread
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:50.110074+00:00
-- url     : https://prove2.me/submissions/080dde40-309c-4b06-aa1f-fae0003cc75a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_GlobalTheory_SecSpread_exists_denom_of_isAffineOpen
import Theorems.Thm_GlobalTheory_SecSpread_ext_generic
import Theorems.Thm_GlobalTheory_SecSpread_exists_glue
import Theorems.Thm_GlobalTheory_SecSpread_cst_mul
import Theorems.Thm_GlobalTheory_SecSpread_pull_sec_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_constFn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
namespace GlobalTheory.SecSpread
theorem _root_.solution (H : IsPullback φ π p (spMap (algebraMap R K))) [Flat p] [QuasiCompact p] {L : LB X}
    (hL : L.IsLB) (s : (L.pull φ).Sec) :
    ∃ d : R, d ≠ 0 ∧ ∃ θ : L.Sec, ∀ i z, φ z ∈ L.U i →
      gs φ z (L.U i) (θ.f i) = cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => i)) (s.f (fun _ => i)) := by
  classical
  have loc : ∀ x : X, ∃ (V : X.Opens) (i : L.ι) (_ : V ≤ L.U i) (_ : x ∈ V) (d : R) (_ : d ≠ 0) (a : Γ(X, V)),
      ∀ z, φ z ∈ V → gs φ z V a =
        cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => i)) (s.f (fun _ => i)) := by
    intro x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hi (L.U i).isOpen
    have hle : U ≤ L.U i := hUW
    have hle' : φ ⁻¹ᵁ U ≤ (L.pull φ).U (fun _ => i) := fun z hz => mem_pull.2 (hle hz)
    obtain ⟨d, hd, a, ha⟩ := exists_denom_of_isAffineOpen H hU (resG X' hle' (s.f (fun _ => i)))
    refine ⟨U, i, hle, hxU, d, hd, a, fun z hz => ?_⟩
    have e := congrArg (gs (𝟙 X') z _) ha
    have hz' : (𝟙 X' : X' ⟶ X') z ∈ φ ⁻¹ᵁ U := hz
    rw [gs_mul _ z _ hz', gs_res _ z hle' hz', gs_pull (𝟙 X') φ z U hz, gs_pull (𝟙 X') φ z U hz,
      Category.id_comp, gs_constFn p U φ z hz] at e
    exact e.symm
  choose V ι hV hx d hd a ha using loc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  have hglue : ∀ i, ∃ θ : Γ(X, L.U i), ∀ z, φ z ∈ L.U i → gs φ z (L.U i) θ =
      cst (φ ≫ p) z (∏ x ∈ S, d x) * gs (𝟙 X') z ((L.pull φ).U (fun _ => i)) (s.f (fun _ => i)) := by
    intro i
    refine exists_glue H (L.U i) _ fun y hy => ?_
    obtain ⟨x, hxS, hyx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ y))
    have l : L.U i ⊓ V x ≤ L.U i ⊓ L.U (ι x) := inf_le_inf_left _ (hV x)
    refine ⟨L.U i ⊓ V x, inf_le_left, ⟨hy, hyx⟩,
      constFn p _ (∏ w ∈ S.erase x, d w) * (resG X l (L.g i (ι x)).val * resG X inf_le_right (a x)), fun z hz => ?_⟩
    rw [gs_mul φ z _ hz, gs_mul φ z _ hz, gs_constFn p _ φ z hz, gs_res φ z l hz, gs_res φ z inf_le_right hz,
      ha x z hz.2, gs_unit φ z _ (l hz), pull_sec_trans s z hz.1 (hV x hz.2), ← Finset.mul_prod_erase S d hxS,
      cst_mul]
    ring
  choose θ hθ using hglue
  refine ⟨∏ x ∈ S, d x, Finset.prod_ne_zero_iff.2 fun x _ => hd x, ⟨θ, fun i j => ext_generic H fun z hz => ?_⟩, hθ⟩
  rw [gs_mul φ z _ hz, gs_res φ z inf_le_left hz, gs_res φ z inf_le_right hz, gs_unit φ z _ hz, hθ i z hz.1,
    hθ j z hz.2, pull_sec_trans s z hz.1 hz.2]
  ring
end GlobalTheory.SecSpread

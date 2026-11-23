-- Prove2me | solution 1 for GlobalTheory.wv_thickMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:47.981882+00:00
-- url     : https://prove2.me/submissions/3aa841d0-58f5-4243-9262-5c8ae8051315

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtOfSucc
import Theorems.Thm_GlobalTheory_thickMap_comp_fGl
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
private lemma mem_pull_U_of_mem_U {X Y : Scheme.{0}} {M : LB X} (f : Y ⟶ X) (j : PUnit → M.ι) (y : Y)
    (h : f y ∈ M.U (j ⟨⟩)) : y ∈ (M.pull f).U j := by
  unfold LB.pull LB.LinComb
  simp only [LB.wchart]
  simpa using fun i : PUnit => (show i = ⟨⟩ from rfl) ▸ h
private lemma gm_res_eq_gm {Z : Scheme.{0}} (z : Z) {V W : Z.Opens} (h : V ≤ W) (hz : z ∈ V) (x : Γ(Z, W)ˣ) :
    gm (𝟙 Z) z V (res h x) = gm (𝟙 Z) z W x := by
  rw [← gm_rp₁ (𝟙 Z) z W V h hz x]
  unfold pullU
  congr 2
end
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
namespace GlobalTheory
theorem _root_.solution (e : ℕ) (y : (thickObj R I e G).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : pGl U e y ∈ D.toPre.P.L.U jM) (hL : fGl I G e y ∈ U.LG.L.U jL) :
    wv U (e + 1) (thickMap R I e G) y jM jL = wv U e (𝟙 _) y jM jL := by
  have hq := U.gt_q e
  have hf := thickMap_comp_fGl I e G
  have h3 : (pGl U (e + 1)) ((thickMap R I e G) y) = (pGl U e) y := congrArg (fun g => g.base y) hq
  have h4 : (fGl I G (e + 1)) ((thickMap R I e G) y) = (fGl I G e) y := congrArg (fun g => g.base y) hf
  have hy : y ∈ ((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL :=
    ⟨mem_pull_U_of_mem_U _ _ _ hM, mem_pull_U_of_mem_U _ _ _ hL⟩
  have hy' : y ∈ thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) :=
    ⟨mem_pull_U_of_mem_U _ _ _ (h3 ▸ hM), mem_pull_U_of_mem_U _ _ _ (h4 ▸ hL)⟩
  have hle : thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) ≤
      thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) := inf_le_left
  have hV : y ∈ (thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL)) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) := ⟨hy', hy⟩
  unfold wv
  refine (gm_rp₁ (thickMap R I e G) y _ _ hle hV ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))).symm.trans ?_
  exact (congrArg (gm (𝟙 _) y _) (U.w_compat e (fun _ => jM, fun _ => jL) _ hle inf_le_right)).trans
    (gm_res_eq_gm y (inf_le_right : (thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL)) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) ≤ (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL)) hV _)
end GlobalTheory

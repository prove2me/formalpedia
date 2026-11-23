-- Prove2me | solution 1 for GlobalTheory.expandsAt_linear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:58.188849+00:00
-- url     : https://prove2.me/submissions/cddb4992-0d5f-4792-be88-f2b2c2625e08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Theorems.Thm_GlobalTheory_gs_of_eq_sum_scal
import Theorems.Thm_GlobalTheory_expandsAt_iff_stalks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k e n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α) (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ : ∀ α, D.toPre.SecB k α), (∀ i, U.ExpandsAt e k (σ i) (f i)) → (∀ j, σ₀.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j) → (∀ α j, (f₀ α).f j = ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j) → U.ExpandsAt e k σ₀ f₀ := by
  intro R _ _ I D A G _ _ U k e n c σ f σ₀ f₀ hE hσ hf
  classical
  have hE' := fun i => (expandsAt_iff_stalks U e k (σ i) (f i)).1 (hE i)
  choose S hS using hE'
  refine (expandsAt_iff_stalks U e k σ₀ f₀).2 ⟨Finset.univ.biUnion S, fun y J hJ => ?_⟩
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom := (Over.w _).trans (Over.w _).symm
  have key₀ : ∀ α, sval (f₀ α) (pGl U e) y J =
      ∑ i, cst (pGl U e ≫ D.toPre.P.A.hom) y (c i) * sval (f i α) (pGl U e) y J := fun α =>
    gs_of_eq_sum_scal D.toPre.P.A.hom (pGl U e) y _ (Good.mem hJ _ _) c (hf α _)
  refine ⟨fun α hα => ?_, fun jL hjL => ?_⟩
  · rw [key₀ α]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hS i y J hJ).1 α (fun h => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩)), mul_zero]
  · have hmem : fGl I G e y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL) :=
      Set.mem_iInter.2 fun _ => hjL
    have keyσ : sv U k σ₀ (fGl I G e) y jL =
        ∑ i, cst (fGl I G e ≫ G.hom) y (c i) * sv U k (σ i) (fGl I G e) y jL :=
      gs_of_eq_sum_scal G.hom (fGl I G e) y _ hmem c (hσ _)
    have hR : ∑ α ∈ Finset.univ.biUnion S, sval (f₀ α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val =
        ∑ i, ∑ α ∈ Finset.univ.biUnion S,
          cst (fGl I G e ≫ G.hom) y (c i) * sval (f i α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [key₀ α, Finset.sum_mul, hc]
    rw [hR, keyσ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, (hS i y J hJ).2 jL hjL,
      Finset.sum_subset (Finset.subset_biUnion_of_mem S (Finset.mem_univ i))
        (fun α _ hα => by rw [(hS i y J hJ).1 α hα, zero_mul]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [_root_.mul_assoc]
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.sec_div_of_expandsAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:05.248139+00:00
-- url     : https://prove2.me/submissions/d8d643f7-196b-4381-9319-4c22b5836b65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecDivOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AppCompEqZeroOfGermDvd
import Theorems.Thm_GlobalTheory_sec_div_of_germ_dvd
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mem
import Theorems.Thm_GlobalTheory_expandsAt_iff_stalks
import Theorems.Thm_GlobalTheory_gs_of_eq_sum_scal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (r : R), r ≠ 0 → ∀ (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) := by
  intro R _ _ I hR D A G _ _ _ U k r hr σ₀ f₀ f hf hE
  have : IsNoetherianRing R := hR.1
  have hI : I ≤ Ideal.jacobson ⊥ := have := hR.2.2.2; IsAdicComplete.le_jacobson_bot I
  have := U.smooth
  refine sec_div_of_germ_dvd R I hI G _ (linComb_isLB _ U.LG.isLB _ _) σ₀ r hr fun e j y hy ↦ ?_
  obtain ⟨S, H⟩ := (expandsAt_iff_stalks U e k σ₀ f₀).1 (hE e)
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left ↦
    exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  obtain ⟨jL, rfl⟩ : ∃ jL : U.LG.L.ι, j = fun _ ↦ jL :=
    ⟨j 0, funext fun i ↦ congrArg j (Subsingleton.elim i 0)⟩
  have h := (H y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  refine (Units.dvd_mul_left (u := wv U e (𝟙 _) y (J (pGl U e)) jL ^ k)).1 (h.symm ▸ ?_)
  refine Finset.dvd_sum fun α _ ↦ Dvd.dvd.mul_right ⟨sval (f α) (pGl U e) y J, ?_⟩ _
  rw [← hc]
  have := gs_of_eq_sum_scal (n := 1) D.toPre.P.A.hom (pGl U e) y _ (hJ.mem (D.toPre.famφB α) _)
    (fun _ ↦ r) (a := (f₀ α).f _) (b := fun _ ↦ (f α).f _) (by rw [Fin.sum_univ_one]; exact hf α _)
  rw [Fin.sum_univ_one] at this
  exact this
end GlobalTheory

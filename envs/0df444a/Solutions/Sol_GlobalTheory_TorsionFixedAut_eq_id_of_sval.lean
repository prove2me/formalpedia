-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.eq_id_of_sval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:30.986002+00:00
-- url     : https://prove2.me/submissions/3d631388-b312-4081-8e3e-6ab812849381

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_GlobalTheory_TorsionFixedAut_isUnit_sval_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {ι' : Type} (s : ι' → LB.Sec (LB.LinComb L φ ε))
    (b : Y ⟶ B) (f : Y ⟶ Y) (hf : f ≫ b = b) (hcov : ⨆ i, nonzeroLocus (s i) = ⊤)
    (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧ ∃ r : ι' → Γ(Y, nonzeroLocus (s i)),
      (∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ (LB.LinComb L φ ε).U k)).op).hom ((s j).f k) =
        (Y.presheaf.map (homOfLE (inf_le_left :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ nonzeroLocus (s i))).op).hom (r j) *
        (Y.presheaf.map (homOfLE (inf_le_right :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ (LB.LinComb L φ ε).U k)).op).hom ((s i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (b.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r))
    (h : ∀ y : Y, ∃ J, Good L y J ∧ ∃ u, ∀ i, sval (s i) f y J = u * sval (s i) (𝟙 Y) y J) : f = 𝟙 Y := by
  have cov : ∀ y : Y, ∃ i, y ∈ nonzeroLocus (s i) := fun y =>
    Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  choose J hJ u hu using h
  have uu : ∀ y, IsUnit (u y) := fun y => by
    obtain ⟨i, hi⟩ := cov (f y)
    have := (isUnit_sval_iff (s i) f y (hJ y)).2 hi
    rw [hu] at this
    exact isUnit_of_mul_isUnit_left this
  have le : ∀ i, nonzeroLocus (s i) ≤ f ⁻¹ᵁ nonzeroLocus (s i) := fun i y hy => by
    refine (isUnit_sval_iff (s i) f y (hJ y)).1 ?_
    rw [hu]
    exact (uu y).mul ((isUnit_sval_iff (s i) (𝟙 Y) y (hJ y)).2 hy)
  refine Scheme.hom_ext_of_forall _ _ fun y => ?_
  obtain ⟨i, hi⟩ := cov y
  refine ⟨nonzeroLocus (s i), hi, ?_⟩
  obtain ⟨hA, r, hr, hs⟩ := haff i
  have ratio : ∀ (g : Y ⟶ Y) (z : Y) (j), g z ∈ nonzeroLocus (s i) →
      sval (s j) g z (J z) = gs g z _ (r j) * sval (s i) g z (J z) := fun g z j hz => by
    have hm : g z ∈ nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U (fun k => J z (g ≫ φ k)) := ⟨hz, (hJ z).mem φ g⟩
    exact (gs_res g z _ hm _).symm.trans ((congrArg (gs g z _) (hr j _)).trans ((gs_mul g z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res g z _ hm _) (gs_res g z _ hm _))))
  have fixr : ∀ j, (f.appLE _ _ (le i)).hom (r j) = r j := fun j => fn_ext fun z hz => by
    have e₁ : gs (𝟙 Y) z _ ((f.appLE _ _ (le i)).hom (r j)) = gs f z _ (r j) :=
      (gs_res (𝟙 Y) z (le i) hz _).trans ((gs_pull (𝟙 Y) f z _ (le i (x := z) hz) _).trans (by rw [Category.id_comp]))
    have e₂ := ratio f z j (le i hz)
    rw [hu, hu, ratio (𝟙 Y) z j hz, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_comm (u z)] at e₂
    rw [e₁]
    exact ((uu z).mul_right_cancel (((isUnit_sval_iff (s i) (𝟙 Y) z (hJ z)).2 hz).mul_right_cancel e₂)).symm
  have fixc : b.appLE ⊤ (nonzeroLocus (s i)) le_top ≫ f.appLE _ _ (le i) = b.appLE ⊤ (nonzeroLocus (s i)) le_top := by
    refine (Scheme.Hom.appLE_comp_appLE f b ⊤ _ _ le_top (le i)).trans ?_
    simp only [hf]
  have fix : f.appLE _ _ (le i) = 𝟙 _ := by
    ext a
    obtain ⟨p, rfl⟩ := hs a
    have : (f.appLE _ _ (le i)).hom.comp (MvPolynomial.eval₂Hom (b.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r) =
        MvPolynomial.eval₂Hom (b.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
      · simpa using congrArg (fun q => q.hom a) fixc
      · simpa using fixr j
    exact congrArg (fun q => q p) this
  have e := IsAffineOpen.SpecMap_appLE_fromSpec f hA hA (le i)
  rw [fix, Spec.map_id, Category.id_comp, ← hA.isoSpec_inv_ι, Category.assoc, cancel_epi] at e
  rw [Category.comp_id, ← e]
end GlobalTheory.TorsionFixedAut

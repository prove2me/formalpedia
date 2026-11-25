-- Prove2me | solution 1 for GlobalTheory.EvenPull.pmaps_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:45:36.560797+00:00
-- url     : https://prove2.me/submissions/aba37e19-1954-48ee-8b76-28b9231a1cea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PulledComparisonEven
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EvenPull
namespace GlobalTheory.EvenPull
theorem _root_.solution {X X' Y Y' S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (π : Y' ⟶ S₀) (e : S₀ ⟶ Y') (he : e ≫ π = 𝟙 _) (hp : Function.Surjective π.appTop.hom)
    (H : ∀ y J J', Good L y J → Good L' y J' → val t (e ≫ h) y J =
      (∏ k, gw w (e ≫ φ' k) y (J ((e ≫ φ' k) ≫ F)) (J' (e ≫ φ' k)) ^ ε k) * val a e y J') :
    PMaps w φ' φ ε a t h := by
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have key := gen_unique' hL (φ := fun k => h ≫ φ k) (ε := ε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ ε I) (hψ I))
    π e he hp (DVR.pullGen_isGen _ _ _ _ ht h) ht₁ (fun y J hJ => by
      choose J' hJ' using fun χ : S₀ ⟶ X' => exists_chart hL' (χ y)
      refine (val_pull hJ _ _ _).trans ((H y J J' hJ hJ').trans (Eq.trans ?_
        (hv _ e y _ _ (hJ.mem _ e) (Good.mem hJ' _ e)).symm))
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl
      rw [Category.assoc])
  intro Z r z p q hp hq
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have m₁ : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  have m₂ : (r ≫ h) z ∈ LB.wchart L φ p := Set.mem_iInter.2 fun k =>
    (congrArg (fun g => g (r z) ∈ L.U (p k)) (hψ k)).mp (hp k)
  have c₁ := gen_trans ht (r ≫ h) z m₂ (Good.mem hJ _ _)
  have c₂ := gen_trans ht₁ r z m₁ (Good.mem hJ _ _)
  have c₃ : trF φ ε (r ≫ h) z p (fun k => J ((r ≫ h) ≫ φ k)) =
      trF (fun k => φ' k ≫ F) ε r z p (fun k => J (r ≫ φ' k ≫ F)) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (r ≫ h) ≫ φ k = r ≫ φ' k ≫ F := by rw [hψ, Category.assoc]
    show gm ((r ≫ h) ≫ φ k) z (L.U (p k) ⊓ L.U (J ((r ≫ h) ≫ φ k))) (L.g (p k) (J ((r ≫ h) ≫ φ k))) ^ _ =
      gm (r ≫ φ' k ≫ F) z (L.U (p k) ⊓ L.U (J (r ≫ φ' k ≫ F))) (L.g (p k) (J (r ≫ φ' k ≫ F))) ^ _
    rw [this]
  have c₄ : val t (r ≫ h) z J = val t₁ r z J := (val_pull hJ _ _ _).symm.trans (key Z r z J hJ)
  exact c₁.trans ((congrArg₂ (· * ·) c₃ c₄).trans (c₂.symm.trans (hv Z r z p q m₁ (Set.mem_iInter.2 hq))))
end GlobalTheory.EvenPull

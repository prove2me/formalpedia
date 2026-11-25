-- Prove2me | solution 1 for GlobalTheory.fam_eq_on_class_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:41.197197+00:00
-- url     : https://prove2.me/submissions/da2fc4a5-0718-47f2-8968-585e6a8da58a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private lemma gs_id_eq_of_presheaf_map_eq {X : Scheme.{0}} {U V : X.Opens} (hle : V ≤ U) {a b : Γ(X, U)} (y : X) (hy : y ∈ V)
    (e : (X.presheaf.map (homOfLE hle).op).hom a = (X.presheaf.map (homOfLE hle).op).hom b) :
    Geo.Tor.gs (𝟙 X) y U a = Geo.Tor.gs (𝟙 X) y U b := by
  rw [← Geo.Tor.gs_res (𝟙 X) y hle hy a, ← Geo.Tor.gs_res (𝟙 X) y hle hy b, e]
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s t : Fam D F k) (α : D.X), (∀ j, (s.s α).f j = (t.s α).f j) →
    ∀ (m : D.X) j, (s.s (α + k • m)).f j = (t.s (α + k • m)).f j := by
  intro hG R _ _ D F _ _ k s t α h m j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hG k m α
  have Hs := s.fe
  have Ht := t.fe
  unfold DegPre.FamFE at Hs Ht
  have Hs' := Hs m α u hu hc
  have Ht' := Ht m α u hu hc
  unfold GeneratorPullback.SecRel at Hs' Ht'
  refine Geo.Tor.sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  have hcoh : D.P.L.Coh
      (Sum.elim (D.famφ F (α + k • m)) (Sum.elim (fun i => (D.trF F m).left ≫ D.famφ F α i) (D.deltaφ F k α m)))
      (Sum.elim (fun i => J (D.famφ F (α + k • m) i))
        (Sum.elim (fun i => J ((D.trF F m).left ≫ D.famφ F α i)) (fun i => J (D.deltaφ F k α m i)))) := by
    intro a b hab
    rcases a with a | a | a <;> rcases b with b | b | b <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hab ⊢ <;> exact congrArg J hab
  have e := Hs' _ _ _ hcoh
  erw [h, ← Ht' _ _ _ hcoh] at e
  rw [Geo.Tor.sval_of _ _ _ _ (fun i => J (D.famφ F (α + k • m) i)) (fun i => by simp),
    Geo.Tor.sval_of _ _ _ _ (fun i => J (D.famφ F (α + k • m) i)) (fun i => by simp)]
  refine gs_id_eq_of_presheaf_map_eq _ y ?_ e
  simp only [TopologicalSpace.Opens.mem_inf]
  exact ⟨⟨Set.mem_iInter.2 fun i => hJ _, Set.mem_iInter.2 fun i => hJ _⟩, Set.mem_iInter.2 fun i => hJ _⟩
end GlobalTheory

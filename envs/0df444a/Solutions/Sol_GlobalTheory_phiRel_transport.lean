-- Prove2me | solution 1 for GlobalTheory.phiRel_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:33.967869+00:00
-- url     : https://prove2.me/submissions/16bd6c16-e292-4670-80cf-31affd74f528

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Theorems.Thm_GlobalTheory_PhiPull_base_eq
import Theorems.Thm_GlobalTheory_PhiPull_phiVal_pull
import Theorems.Thm_GlobalTheory_DegPull_exists_pmaps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_phiRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left), Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left → Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) → ∀ (k : ℕ) (p₀ : QkPt D F k) (p₀' : QkPt D' F k), p₀'.y = hD.xe.symm p₀.y → IsPullGtF φ hD F p₀.g p₀'.g → ∀ (ν : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₀.g.b) (DegPre.lineε k))), ν.IsGen → ∃ ν' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p₀'.g.b) (DegPre.lineε k)), ν'.IsGen ∧ ∀ (s s₂ : Fam D F k) (s' s₂' : Fam D' F k), (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s.s (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s'.s x).f q))) → (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s₂.s (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s₂'.s x).f q))) → PhiRel D F k p₀ ν s s₂ → PhiRel D' F k p₀' ν' s' s₂' := by
  intro hG R R' _ _ _ _ φ D D' hD F _ _ _ hF Θ hΘ₁ hΘ₂ k p₀ p₀' hy hg ν hν
  have hT := PhiPull.base_eq hF
  have hl : ∀ i, DegPre.lineφ D' F p₀'.g.b i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      𝟙 _ ≫ DegPre.lineφ D F p₀.g.b i := fun i => by
    obtain ⟨hψ, -⟩ := hg.2 0
    fin_cases i
    · exact hψ 3
    · exact hψ 2
  obtain ⟨ν', hν', pm⟩ := DegPull.exists_pmaps ((Geo.Tor.isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (𝟙 _) hl ν hν
  refine ⟨ν', hν', fun s s₂ s' s₂' H₁ H₂ H => ?_⟩
  rw [DVR.phiRel_iff hG p₀' ν' hν']
  exact PhiPull.phiVal_pull hD hT hΘ₁ hΘ₂ hG p₀ p₀' hy hg ν ν' hl pm s s₂ s' s₂' H₁ H₂
    ((DVR.phiRel_iff hG p₀ ν hν s s₂).1 H)
end GlobalTheory

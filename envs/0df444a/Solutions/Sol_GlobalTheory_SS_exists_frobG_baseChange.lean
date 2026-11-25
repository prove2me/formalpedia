-- Prove2me | solution 1 for GlobalTheory.SS.exists_frobG_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:30.532893+00:00
-- url     : https://prove2.me/submissions/2049a1cf-4013-4e3f-8b60-191fd1add462

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
import Theorems.Thm_GlobalTheory_SS_FrobField_good_of_isPullback
import Theorems.Thm_GlobalTheory_SS_FrobField_isMonHom_app
import Theorems.Thm_GlobalTheory_SS_FrobField_over_pow_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS
open FrobField
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (W k : Type) [CommRing W] [Field k] (ρ : W →+* k) (p r : ℕ) [Fact p.Prime] [CharP k p], 1 ≤ r → (∀ w, ρ w ^ (p ^ r) = ρ w) → (∀ c : k, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∃ F : End ((Over.pullback (spMap ρ)).obj G), FrobG _ F (p ^ r) ∧ ∀ (x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback (spMap ρ)).obj G) (τ : k →+* k), (∀ c, τ c = c ^ (p ^ r)) → (x ≫ (show (Over.pullback (spMap ρ)).obj G ⟶ (Over.pullback (spMap ρ)).obj G from F)).left ≫ pullback.fst G.hom (spMap ρ) = spMap τ ≫ x.left ≫ pullback.fst G.hom (spMap ρ) := by
  intro W k _ _ ρ p r hp _ _ hρ hfin G _ _
  have hk : (p : k) = 0 := CharP.cast_eq_zero k p
  refine ⟨(relNat ρ p r hp.out hk hρ).app G, ⟨isMonHom_app _ _ G, fun U hU f => ?_⟩, fun x τ hτ => ?_⟩
  · obtain ⟨m, hm, h⟩ := good_of_isPullback (IsPullback.of_hasPullback G.hom (spMap ρ)) p r hp.out
      (cast_zero_of_hom (pullback.snd _ _) (cast_zero_sp k hk)) (fun c => by
        obtain ⟨m, hm, h⟩ := hfin ((Scheme.ΓSpecIso (.of k)).hom.hom c)
        refine ⟨m, hm, (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective ?_⟩
        rw [map_pow]; exact h)
      (relLeft ρ p r hp.out hk hρ G) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) U hU.isCompact f
    refine ⟨m, hm, ?_⟩
    have e := over_pow_left ((relNat ρ p r hp.out hk hρ).app G) m
    exact (congrArg (fun φ => Q φ ((p ^ r) ^ m) U f) e).mpr h
  · have e := absFrob_nat (show Sp k ⟶ pullback G.hom (spMap ρ) from x.left) p r hp.out (cast_zero_sp k hk)
      (cast_zero_of_hom (pullback.snd _ _) (cast_zero_sp k hk))
    rw [absFrob_spec k p r hp.out _ τ hτ] at e
    have e2 : relLeft ρ p r hp.out hk hρ G ≫ pullback.fst _ _ = _ := pullback.lift_fst _ _ _
    change ((show Sp k ⟶ pullback G.hom (spMap ρ) from x.left) ≫ relLeft ρ p r hp.out hk hρ G) ≫ _ = _
    rw [Category.assoc, e2, ← Category.assoc, ← e, Category.assoc]
end GlobalTheory.SS

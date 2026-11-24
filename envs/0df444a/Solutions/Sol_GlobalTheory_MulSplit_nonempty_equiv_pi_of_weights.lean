-- Prove2me | solution 1 for GlobalTheory.MulSplit.nonempty_equiv_pi_of_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:59:31.0008+00:00
-- url     : https://prove2.me/submissions/c9d3ed4e-4bb4-4ee3-aba6-2caa9a029d7a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_apply_avg
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_apply
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_of_weight
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_of_weight_ne
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_sum_avg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
open FiniteAbelianWeights
namespace GlobalTheory.MulSplit
theorem _root_.solution {R M N G : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [CommGroup G] [Finite G] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity R n]
    (hn : IsUnit (n : R)) (hG : ∀ g : G, g ^ n = 1) (ρ : Representation R G M) (W : Submodule R M)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W)
    (h : ∀ χ : G →* Rˣ, ∃ f : N →ₗ[R] M, Function.Injective f ∧
      ∀ v, (∃ x, f x = v) ↔ v ∈ W ∧ ∀ g, ρ g v = (χ g : R) • v) :
    Nonempty (W ≃ₗ[R] (G → N)) := by
  classical
  haveI : HasEnoughRootsOfUnity R (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd R (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R
  haveI : Finite (G →* Rˣ) := Finite.of_equiv G e.toEquiv.symm
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite (G →* Rˣ)
  obtain ⟨u, hu⟩ : ∃ u : R, u * (Fintype.card G : R) = 1 := by
    have h1 := card_dvd_exponent_pow_rank' G hG
    rw [Nat.card_eq_fintype_card] at h1
    have h2 : (Fintype.card G : R) ∣ (n : R) ^ Group.rank G := by
      exact_mod_cast Nat.cast_dvd_cast (α := R) h1
    exact (isUnit_of_dvd_unit h2 (hn.pow _)).exists_left_inv
  choose f hf hr using h
  let F : ((G →* Rˣ) → N) →ₗ[R] M := ∑ χ, (f χ).comp (LinearMap.proj χ)
  have hF : ∀ x, F x = ∑ χ, f χ (x χ) := fun x => by simp [F, LinearMap.sum_apply]
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext c
    apply hf c
    have := congrArg (avg ρ u c) hx
    rw [hF, map_sum, map_zero, Finset.sum_eq_single c, avg_of_weight ρ u hu c _ ((hr c _).1 ⟨_, rfl⟩).2] at this
    · simpa using this
    · exact fun d _ hd => avg_of_weight_ne ρ u c d hd _ ((hr d _).1 ⟨_, rfl⟩).2
    · simp
  have hrange : LinearMap.range F = W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hF]
      exact W.sum_mem fun c _ => ((hr c _).1 ⟨_, rfl⟩).1
    · intro w hw
      have : ∀ c, ∃ x, f c x = avg ρ u c w := fun c => (hr c _).2 ⟨by
        rw [avg_apply]
        exact W.smul_mem _ (W.sum_mem fun t _ => W.smul_mem _ (hW t w hw)), fun g => apply_avg ρ u c g w⟩
      choose x hx using this
      refine ⟨x, ?_⟩
      rw [hF, Finset.sum_congr rfl fun c _ => hx c, sum_avg ρ u hu]
  exact ⟨(LinearEquiv.ofEq _ _ hrange).symm.trans ((LinearEquiv.ofInjective F hinj).symm.trans
    (LinearEquiv.funCongrLeft R N e.toEquiv.symm))⟩
end GlobalTheory.MulSplit

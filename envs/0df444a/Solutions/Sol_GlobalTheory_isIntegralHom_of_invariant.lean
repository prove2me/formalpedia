-- Prove2me | solution 1 for GlobalTheory.isIntegralHom_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:38.776109+00:00
-- url     : https://prove2.me/submissions/6d3947c8-034a-4739-80a6-0c30db25291d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G : Type*} [Group G] [Finite G] {X X' : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)) : IsIntegralHom π := by
  rw [isIntegralHom_iff]
  refine ⟨inferInstance, fun W hW => ?_⟩
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  classical
  have := Fintype.ofFinite G
  intro s
  rcases subsingleton_or_nontrivial Γ(X, π ⁻¹ᵁ W) with hsub | hnt
  · rw [Subsingleton.elim s 0]
    exact RingHom.isIntegralElem_zero _
  set P : Polynomial Γ(X, π ⁻¹ᵁ W) := ∏ g : G, (Polynomial.X - Polynomial.C (g • s)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hlift : P ∈ Polynomial.lifts (π.app W).hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply hinv W hW
    intro g
    refine ⟨hU g, ?_⟩
    have := congrArg (fun q => q.coeff n) (hinvP g⁻¹)
    simp only [Polynomial.coeff_smul] at this
    rw [hact] at this
    simpa only [inv_inv] using this
  have hmonic : P.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, hP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:34.303268+00:00
-- url     : https://prove2.me/submissions/ea188abc-b0b9-4546-806e-3902cdcef6d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField
import Theorems.Thm_GlobalTheory_SS_PlacesExt_fin_notIntegral
import Theorems.Thm_GlobalTheory_SS_PlacesExt_exists_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0
variable {k F L : Type} [Field k] [Field F] [Algebra k F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L] (Pl : Places k F)
variable (L)
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution [Algebra k L] [IsScalarTower k F L] (hD : ∀ i, IsDiscreteValuationRing (Pl.O i)) :
    ∃ Pl' : Places k L, ∀ y : L, (∀ j, y ∈ Pl'.O j) → ∀ i, IsIntegral (Pl.O i) y := by
  classical
  choose J hJ O' w hmul hmem hint hsum using fun i => exists_local L Pl i
  have hone : ∀ i j, w i j 1 = 0 := fun i j => by
    have := hmul i j 1 1
    rw [mul_one] at this
    omega
  have hT : ∀ y : Lˣ, ∃ T : Finset Pl.I, ∀ i ∉ T, ∀ j, w i j y = 0 := fun y => by
    refine ⟨((fin_notIntegral Pl (y : L)).union (fin_notIntegral Pl ((y⁻¹ : Lˣ) : L))).toFinset,
      fun i hi j => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hi
    have h1 := (hmem i j _).1 ((hint i _).2 hi.1 j)
    have h2 := (hmem i j _).1 ((hint i _).2 hi.2 j)
    have h3 := hmul i j y y⁻¹
    rw [mul_inv_cancel, hone] at h3
    omega
  haveI : ∀ i, Fintype (J i) := fun i => Fintype.ofFinite _
  have hsupp : ∀ (y : Lˣ) (T : Finset Pl.I), (∀ i ∉ T, ∀ j, w i j y = 0) →
      (Function.support fun p : Σ i, J i => w p.1 p.2 y) ⊆
        ((T.sigma fun _ => Finset.univ : Finset (Σ i, J i)) : Set _) := fun y T h p hp => by
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, and_true]
    by_contra hc
    exact hp (h _ hc _)
  refine ⟨⟨Σ i, J i, fun p => O' p.1 p.2, fun p => w p.1 p.2, fun p => hmul p.1 p.2,
    fun p => hmem p.1 p.2, fun p c => ?_, fun y => ?_, fun y => ?_⟩,
    fun y hy i => (hint i y).1 fun j => hy ⟨i, j⟩⟩
  · refine (hint p.1 _).2 ?_ p.2
    rw [IsScalarTower.algebraMap_apply k F L]
    exact isIntegral_algebraMap (x := (⟨_, Pl.const p.1 c⟩ : Pl.O p.1))
  · obtain ⟨T, h⟩ := hT y
    exact (Finset.finite_toSet _).subset (hsupp y T h)
  · obtain ⟨T, h⟩ := hT y
    rw [finsum_eq_sum_of_support_subset _ (hsupp y T h), Finset.sum_sigma,
      ← Pl.sum (Units.map (Algebra.norm F) y), finsum_eq_sum_of_support_subset (s := T)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hsum, finsum_eq_sum_of_fintype]
    · intro i hi
      by_contra hc
      apply hi
      simp only [← hsum, h i hc, finsum_zero]
end GlobalTheory.SS.PlacesExt

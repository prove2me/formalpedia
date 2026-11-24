-- Prove2me | solution 1 for GlobalTheory.KeyKa.exists_enum_ker_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:42.788927+00:00
-- url     : https://prove2.me/submissions/599c980b-2c66-4f64-9d49-ca00f63ba2fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsEnumKerTransposeSimilitudePoints
import Theorems.Thm_GlobalTheory_card_ker_int_matrix_four
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x, (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) ∧ (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) := by
  intro laws K _ _ x m al hm hal
  classical
  haveI := x.P.isAb.comm
  haveI := x.P.isAb.smooth
  haveI : LocallyOfFiniteType x.P.A.hom := inferInstance
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm Nat.cast_zero
  letI : CommGroup (Pt x) := Hom.commGroup
  have hG : ∀ k : ℕ, k ∣ m → Nat.card {y : Pt x // y ^ k = 1} = k ^ (2 * x.P.g) := by
    rintro k ⟨l, rfl⟩
    have hk : (k : K) ≠ 0 := fun h => hm (by rw [Nat.cast_mul, h, zero_mul])
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])
    exact (laws.mulN (Sp K) x.P k hk1).2.2.2.2 K (𝟙 _) hk
  have hcard := GlobalTheory.card_ker_int_matrix_four (Pt x) m (2 * x.P.g) al (Nat.pos_of_ne_zero hm0) hal hG
  have hfin : Finite {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)
  have hc : Nat.card (Fin 4 → Fin (m ^ x.P.g)) =
      Nat.card {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1} := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    congr 1
    ring
  obtain ⟨e⟩ := Finite.card_eq.mp hc
  refine ⟨fun I => (e I).1, fun I I' hI p => ?_, fun I c => ?_⟩
  · by_contra hne
    push_neg at hne
    refine hI (e.injective (Subtype.ext (funext fun r => ?_)))
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst hp
    exact Over.OverMorphism.ext
      (ext_of_apply_closedPoint_eq x.P.A.hom (Over.w _) (Over.w _) (hne r))
  · rw [List.prod_ofFn]
    exact (e I).2 c
end GlobalTheory.KeyKa

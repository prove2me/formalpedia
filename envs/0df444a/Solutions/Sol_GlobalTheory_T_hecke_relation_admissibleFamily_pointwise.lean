-- Prove2me | solution 1 for GlobalTheory.T.hecke_relation_admissibleFamily_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:35:43.761403+00:00
-- url     : https://prove2.me/submissions/961bab1d-20e9-44dc-b239-4c245bbaf890

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwiseStatement
import Theorems.Thm_GlobalTheory_SW_hecke_relation_pointwise


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (M R q : ℕ) (P : Ideal (𝓞 E)) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → GoodPrime (R * M) q P → ∃ (A : ℕ) (XA XB : Fin A → Lt E N) (β : Fin A → Fin (q ^ N) → Matrix (Fin N) (Fin N) E), A * (q - 1) = q ^ N - 1 ∧ (∀ i, (XA i).FG ∧ Agree (R * M) (XA i) (stdL E N) ∧ gidx (XA i) = q * gidx 𝔛 ∧ (XB i).FG ∧ Agree (R * M) (XB i) (stdL E N) ∧ q * gidx (XB i) = gidx 𝔛 ∧ ∀ j, ccT (β i j) = β i j) ∧ ∀ Λ ∈ Vset E n M, ∀ x, ((q : ℂ) - 1) * ((q : ℂ) ^ n * ∑ i, twist R (XA i) φ Λ x + ∑ i, ∑ j, chiH Ψ (β i j) x * twist R (XB i) φ Λ x) = ((q : ℂ) - 1) * (q : ℂ) ^ N * (∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x) + ((q : ℂ) ^ (2 * N) - (q : ℂ) ^ n) * twist R 𝔛 φ Λ x := by
  first | exact @GlobalTheory.SW.hecke_relation_pointwise | exact GlobalTheory.SW.hecke_relation_pointwise | (intros; apply GlobalTheory.SW.hecke_relation_pointwise <;> assumption)
end _root_.GlobalTheory.T

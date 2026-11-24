-- Prove2me | solution 1 for GlobalTheory.SS.Weight.le_add_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:50.368281+00:00
-- url     : https://prove2.me/submissions/3f0f79fc-16aa-45c6-b620-6c99ed742014

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing
import Theorems.Thm_GlobalTheory_SS_Weight_le_add_of_pairing
import Theorems.Thm_GlobalTheory_SS_Weight_card_torsion_units

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
namespace GlobalTheory.SS.Weight
theorem _root_.solution : ∀ (M : Type) [CommGroup M] (Ω : Type) [Field Ω] (l q g t a c C : ℕ), l.Prime → 3 ≤ l → (l : Ω) ≠ 0 → 2 ≤ q → 1 ≤ c → (∀ n, Nat.card {x : M // x ^ l ^ n = 1} = l ^ (n * (2 * g))) → ∀ e : ℕ → M → M → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) → ∀ S Φ : M ≃* M, (∀ n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (S x) (S y) = e n x y ∧ e n (Φ x) (Φ y) = e n x y ^ q) → (∀ n x, x ^ l ^ n = 1 → Φ (S x) = S^[q] (Φ x)) → (∀ x, x ^ l = 1 → S x = x) → ∀ (H W : Subgroup M) (P : Polynomial ℤ), (∀ n x, x ^ l ^ n = 1 → S x = x → x ^ c ∈ H) → (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : W // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) → (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) → (∀ n, ∀ x ∈ W, x ^ l ^ n = 1 → Φ x = x ^ q) → (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (P.natDegree + 1), (Φ^[j] x) ^ P.coeff j ∈ W) → g ≤ t + a := by
  intro M _ Ω _ l q g t a c C hl hl3 hlΩ hq hc hM e he S Φ hSΦ hcomm hS1 H W P hH hcard hP hW hPW
  obtain ⟨he1, he2, he3⟩ := he
  let K := AlgebraicClosure Ω
  let u : Ωˣ →* Kˣ := Units.map (algebraMap Ω K : Ω →* K)
  have hu : Function.Injective u := Units.map_injective (algebraMap Ω K).injective
  have hlK : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap Ω K)]
    exact (map_ne_zero_iff _ (algebraMap Ω K).injective).2 hlΩ
  refine GlobalTheory.SS.Weight.le_add_of_pairing (Additive M) (Additive Kˣ) l q g t a c C hl hl3 hq hc
    (GlobalTheory.SS.Weight.card_torsion_units K l hlK) hM
    (fun n x y => Additive.ofMul (u (e n x.toMul y.toMul))) ?_ ?_ ?_
    (MulEquiv.toAdditive S) (MulEquiv.toAdditive Φ) ?_ hcomm hS1 (Subgroup.toAddSubgroup H)
    (Subgroup.toAddSubgroup W) P hH hcard hP hW ?_
  · intro n x x' y hx hx' hy
    obtain ⟨h1, h2⟩ := he1 n x.toMul x'.toMul y.toMul hx hx' hy
    exact ⟨by rw [toMul_add, h1, map_mul, ofMul_mul], by rw [h2, map_inv, ofMul_inv]⟩
  · intro n x y hx hy
    rw [he2 n x.toMul y.toMul hx hy, toMul_nsmul]
  · intro n x hx h
    exact he3 n x.toMul hx fun y hy => hu ((h (Additive.ofMul y) hy).trans (map_one u).symm)
  · intro n x y hx hy
    obtain ⟨h1, h2⟩ := hSΦ n x.toMul y.toMul hx hy
    exact ⟨congrArg (fun z => Additive.ofMul (u z)) h1,
      (congrArg (fun z => Additive.ofMul (u z)) h2).trans (by rw [map_pow, ofMul_pow])⟩
  · intro n x hx hx'
    exact hPW n x.toMul hx hx'
end GlobalTheory.SS.Weight

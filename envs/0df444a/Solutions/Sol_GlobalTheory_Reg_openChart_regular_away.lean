-- Prove2me | solution 1 for GlobalTheory.Reg.openChart_regular_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:20:38.602452+00:00
-- url     : https://prove2.me/submissions/dd0088ba-a594-444f-97eb-e2e1caf535d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsExtendOfPowDenom
import Theorems.Thm_GlobalTheory_Reg_exists_extend_of_pow_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution :
    ∀ (K Ω O A : Type) [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [IsDomain A] [Algebra O A] (io : K →+* FractionRing O) (gens : Finset Ω) (e : Ω) (α : Ω →+* FractionRing A) (eb : A) (ϖ : O), Irreducible ϖ → e ≠ 0 → algebraMap A (FractionRing A) eb = α e → (∀ (k : K) (a b : O), io k * algebraMap O _ b = algebraMap O _ a → α (algebraMap K Ω k) * algebraMap A _ (algebraMap O A b) = algebraMap A _ (algebraMap O A a)) → (∀ g ∈ gens, α g ∈ Set.range (algebraMap A (FractionRing A))) → (∀ r ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), ∃ (x : A) (t : ℕ), α r * algebraMap A _ ((algebraMap O A ϖ * eb) ^ t) = algebraMap A _ x) ∧ ∀ (L : Type) [Field L] (φ : A →+* L), φ (algebraMap O A ϖ * eb) ≠ 0 → ∃ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* L, ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A), α r * algebraMap A _ s = algebraMap A _ x → ψ r * φ s = φ x := by
  intro K Ω O A _ _ _ _ _ _ _ _ _ io gens e α eb ϖ hϖ he heb hk hg
  have h1 : ∀ r ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), ∃ (x : A) (t : ℕ),
      α r * algebraMap A _ ((algebraMap O A ϖ * eb) ^ t) = algebraMap A _ x := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨algebraMap O A ϖ, 1, ?_⟩
        rw [pow_one, map_mul, heb, _root_.mul_comm _ (α e), ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ he,
          map_one, _root_.one_mul]
      · obtain ⟨y, hy⟩ := hg x hx
        exact ⟨y, 0, by simp [hy]⟩
    | algebraMap k =>
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) (io k)
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
      have hb1 : algebraMap O (FractionRing O) b ≠ 0 := by simpa using hb0
      have := hk k (a * u) (ϖ ^ n) (by
        rw [← hu, ← hab, map_mul, map_mul, ← _root_.mul_assoc, div_mul_cancel₀ _ hb1])
      refine ⟨algebraMap O A (a * u) * eb ^ n, n, ?_⟩
      rw [mul_pow, ← map_pow, map_mul, ← _root_.mul_assoc, this, ← map_mul]
    | add x y _ _ ihx ihy =>
      obtain ⟨a, s, ha⟩ := ihx
      obtain ⟨b, t, hb⟩ := ihy
      refine ⟨a * (algebraMap O A ϖ * eb) ^ t + b * (algebraMap O A ϖ * eb) ^ s, s + t, ?_⟩
      generalize algebraMap O A ϖ * eb = d at *
      rw [pow_add, map_add, map_add, map_mul, map_mul, map_mul, ← ha, ← hb]; ring
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, s, ha⟩ := ihx
      obtain ⟨b, t, hb⟩ := ihy
      refine ⟨a * b, s + t, ?_⟩
      generalize algebraMap O A ϖ * eb = d at *
      rw [pow_add, map_mul, map_mul, map_mul, ← ha, ← hb]; ring
  refine ⟨h1, fun L _ φ hφ => ?_⟩
  exact exists_extend_of_pow_denom
    (α.comp (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))).val.toRingHom) _
    (fun r => h1 r r.2) φ hφ
end GlobalTheory.Reg

-- Prove2me | solution 1 for GlobalTheory.local_norm_of_ideal_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:25:43.441771+00:00
-- url     : https://prove2.me/submissions/5398575c-54a0-4607-9413-fd50eea4076b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Theorems.Thm_GlobalTheory_LocalNorm_exists_eq_sq_add_of_mul_eq
import Theorems.Thm_GlobalTheory_LocalNorm_exists_coords
import Theorems.Thm_GlobalTheory_LocalNorm_exists_mul_norm_eq
import Theorems.Thm_GlobalTheory_LocalNorm_exists_eq_sq_add_of_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open LocalNorm
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (x : maximalRealSubfield E), x ≠ 0 → (∃ I J : Ideal (𝓞 E), I ≠ ⊥ ∧ J ≠ ⊥ ∧ FractionalIdeal.spanSingleton (𝓞 E)⁰ ((x : E)) * ((I * I.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = ((J * J.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ a b : v.adicCompletion (maximalRealSubfield E), algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) x = a ^ 2 - algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) (-(H.d : maximalRealSubfield E)) * b ^ 2) := by
  rintro E _ _ _ H x hx ⟨I, J, hI, hJ, h⟩ v
  obtain ⟨z₁, z₂, u, hz, hu, hxu⟩ := exists_mul_norm_eq x hx hI hJ _ H.bar_eq h v
  obtain ⟨a₀, b₀, h₀⟩ := exists_eq_sq_add_of_notMem H v hu
  obtain ⟨a₁, b₁, -, h₁⟩ := exists_coords H z₁
  obtain ⟨a₂, b₂, -, h₂⟩ := exists_coords H z₂
  have hne : a₁ ^ 2 + H.d * b₁ ^ 2 ≠ 0 := fun h0 => by
    rw [h0] at h₁
    exact mul_ne_zero hz ((map_ne_zero _).2 hz) h₁.symm
  have hF : x * (a₁ ^ 2 + H.d * b₁ ^ 2) = u * (a₂ ^ 2 + H.d * b₂ ^ 2) := by
    rw [← h₁, ← h₂] at hxu
    exact Subtype.ext hxu
  have hv := congrArg (algebraMap _ (v.adicCompletion (maximalRealSubfield E))) hF
  have hne' := (map_ne_zero (algebraMap _ (v.adicCompletion (maximalRealSubfield E)))).2 hne
  simp only [map_add, map_mul, map_pow, map_natCast, h₀] at hv hne'
  obtain ⟨a, b, hab⟩ := exists_eq_sq_add_of_mul_eq hne' hv
  exact ⟨a, b, by rw [hab, map_neg, map_natCast]; ring⟩
end GlobalTheory

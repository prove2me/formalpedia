-- Prove2me | solution 1 for GlobalTheory.exists_int_bound_of_dual_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:32.932083+00:00
-- url     : https://prove2.me/submissions/e0eae2ff-b965-4eee-8872-5ba8ef116730

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteUnitaryClassesOfDualEqSmul_87ddafdad67ddc06
import Theorems.Thm_GlobalTheory_exists_sesquilinear_eq_herm
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E)
    {c : FractionalIdeal (𝓞 E)⁰ E} (hc : c ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ Λ : Submodule (𝓞 E) (Fin r → E),
      (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ↔ x ∈ (c : Submodule (𝓞 E) E) • Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((N : E) * herm G x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) → (N : E) • x ∈ Λ := by
  obtain ⟨h, hh⟩ := exists_sesquilinear_eq_herm G
  obtain ⟨e, he0, he⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hc
  obtain ⟨d, hd0, hd⟩ := c.isFractional
  have he0' : algebraMap (𝓞 E) E e ≠ 0 := fun h0 => he0 (RingOfIntegers.ext h0)
  have hd0' : algebraMap (𝓞 E) E d ≠ 0 := fun h0 =>
    nonZeroDivisors.ne_zero hd0 (RingOfIntegers.ext h0)
  obtain ⟨N, hN, hNi⟩ := HermClass.exists_int_mul_isIntegral E
    (Set.toFinite {(algebraMap (𝓞 E) E e)⁻¹, (algebraMap (𝓞 E) E d)⁻¹})
  refine ⟨N, hN, fun Λ hΛ => ⟨fun x hx y hy => ?_, fun x hx => ?_⟩⟩
  · have h1 := (hNi _ (Or.inl rfl)).mul ((hΛ _).2 (Submodule.smul_mem_smul he hx) y hy)
    rwa [← hh, map_smul, LinearMap.smul_apply, smul_eq_mul, hh, mul_assoc,
      inv_mul_cancel_left₀ he0'] at h1
  · refine Submodule.smul_induction_on (p := fun x => (N : E) • x ∈ Λ) ((hΛ x).1 hx)
      (fun a ha z hz => ?_) (fun x y hx hy => by rw [smul_add]; exact add_mem hx hy)
    obtain ⟨b, hb⟩ := hd a ha
    have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E b) := b.isIntegral_coe
    have h1 := (hNi _ (Or.inr rfl)).mul h0
    rw [hb, Algebra.smul_def, mul_assoc, inv_mul_cancel_left₀ hd0'] at h1
    rw [smul_smul]
    exact Λ.smul_mem (⟨_, h1⟩ : 𝓞 E) hz
end GlobalTheory

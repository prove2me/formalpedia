-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:44:27.229811+00:00
-- url     : https://prove2.me/submissions/64c10a59-bad0-4ea6-84fa-72f41bf4029e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_cc_cc
import Theorems.Thm_GlobalTheory_SW_Nbr_herm_sr
import Theorems.Thm_GlobalTheory_SW_Nbr_proj
import Theorems.Thm_GlobalTheory_SW_Nbr_exists_vec

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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) (P : Ideal (𝓞 E)) [hP : P.IsMaximal]
    (hP0 : P ≠ ⊥) (f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P) : ∃ x : Fin n → E, ∀ y : Λ, Int' y x ↔ f y = 0 := by
  have := proj h.1
  obtain ⟨g, hg⟩ := Module.projective_lifting_property P.mkQ f P.mkQ_surjective
  obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := E) hP0 hP.ne_top
  have htP : ∀ c ∈ P, IsIntegral ℤ (t * (c : E)) := fun c hc => by
    have h1 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hP0)).1 ht _
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ hc)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have hb : (b : E) = t * (c : E) := hb
    rw [← hb]; exact b.2
  obtain ⟨x, hx⟩ := exists_vec h (Algebra.linearMap (𝓞 E) E ∘ₗ g)
  refine ⟨cc t • x, fun y => ?_⟩
  have h1 : herm 1 (y : Fin n → E) (cc t • x) = t * (g y : E) := by
    rw [herm_sr, cc_cc, hx]; rfl
  have h2 : f y = 0 ↔ g y ∈ P := by
    rw [← hg]; exact Submodule.Quotient.mk_eq_zero P
  unfold Int'
  rw [h1, h2]
  refine ⟨fun hi => by_contra fun hn => ht1 ?_, htP _⟩
  obtain ⟨u, c, hc, huc⟩ := hP.exists_inv hn
  have h3 : (u : E) * (g y : E) + (c : E) = 1 := by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) huc
  have h4 : IsIntegral ℤ t := by
    have : t = (u : E) * (t * (g y : E)) + t * (c : E) := by linear_combination (-t) * h3
    rw [this]
    exact (IsIntegral.mul u.2 hi).add (htP c hc)
  exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨t, h4⟩, rfl⟩
end GlobalTheory.SW.Nbr

-- Prove2me | solution 1 for GlobalTheory.SW.Model.mem_stdL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:09.908409+00:00
-- url     : https://prove2.me/submissions/4fa2bb83-cd33-4e28-8009-5cfe00b4671c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution {m : ℕ} (x : Fin m → E) : x ∈ stdL E m ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      by_cases h : a = b
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx =>
      intro a
      have : (c • x) a = (c : E) * x a := rfl
      rw [this]; exact c.isIntegral_coe.mul (hx a)
  · intro hx
    have : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin m → E) := by
      ext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · change x b = x b * (Pi.single b (1 : E) : Fin m → E) b
        simp
      · intro a _ h
        change x a * (Pi.single a (1 : E) : Fin m → E) b = 0
        simp [Pi.single_apply, Ne.symm h]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
end GlobalTheory.SW.Model

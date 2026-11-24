-- Prove2me | solution 1 for GlobalTheory.HeckeGal.finite_support_lPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:51:50.033899+00:00
-- url     : https://prove2.me/submissions/4efac027-8279-42e1-a582-ded6edf5eac9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_locPow_of_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (x : Ideles E) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
      locPow ι n v ((x : AdeleRing (𝓞 E) E).2 v)).Finite := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  by_contra h
  refine hv (locPow_of_notMem ι n (fun hm => h ?_) _)
  exact Ideal.dvd_span_singleton.mpr hm
end GlobalTheory.HeckeGal

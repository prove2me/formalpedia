-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.continuous_kummer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:26:03.961981+00:00
-- url     : https://prove2.me/submissions/17d4ce1f-167a-41a9-8df5-bae445e3786c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Theorems.Thm_GlobalTheory_WeilDeligne_toZModPow_kummer_eq_iff
import Theorems.Thm_ReciprocityTheory_Gal_isOpen_setOf_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable (l : ℕ) [Fact l.Prime]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution (a : Eˣ) : Continuous (kummer l a : G E Ω → ℤ_[l]) := by
  refine continuous_iff_continuousAt.mpr fun τ => Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
  filter_upwards [(isOpen_setOf_apply (F := E) (rootOf Ω l (a : E) k)
    (fun y => y = τ (rootOf Ω l (a : E) k))).mem_nhds (show τ ∈ _ from rfl)] with σ hσ
  refine lt_of_le_of_lt ?_ hk
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero, toZModPow_kummer_eq_iff]
  exact hσ
end GlobalTheory.WeilDeligne

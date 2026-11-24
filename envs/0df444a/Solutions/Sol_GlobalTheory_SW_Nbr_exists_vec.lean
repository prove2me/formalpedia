-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.exists_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:25.982453+00:00
-- url     : https://prove2.me/submissions/f0a7304a-b771-43fd-ba5a-8113988ea611

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_cc_cc
import Theorems.Thm_GlobalTheory_SW_Nbr_isLoc
import Theorems.Thm_GlobalTheory_SW_Base_herm_one


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
theorem _root_.solution {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) (g : Λ →ₗ[𝓞 E] E) :
    ∃ x : Fin n → E, ∀ y : Λ, herm 1 y x = g y := by
  have := isLoc h
  have := isLocalizedModule_id (𝓞 E)⁰ E E
  let G := IsLocalizedModule.lift (𝓞 E)⁰ Λ.subtype g
    (IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := E)))
  let G' := G.extendScalarsOfIsLocalization (𝓞 E)⁰ E
  refine ⟨fun i => cc (G' (Pi.single i 1)), fun y => ?_⟩
  have h1 : G' y = g y := IsLocalizedModule.lift_apply (𝓞 E)⁰ Λ.subtype g
    (IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := E))) y
  rw [← h1, herm_one, LinearMap.pi_apply_eq_sum_univ G']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cc_cc, smul_eq_mul]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]
end GlobalTheory.SW.Nbr

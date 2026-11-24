-- Prove2me | solution 1 for GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:07:01.010009+00:00
-- url     : https://prove2.me/submissions/faee1b29-d5e9-4c1a-976d-e62549db1080

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ElementaryDivisorsExistDiscretelyValued
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_P_cartan_decomp_gen
import Theorems.Thm_Formalism_UG_P_cartan_entries_of_mem
import Theorems.Thm_Formalism_UG_P_glint_exists_denom
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution : Smith := by
  intro L _ _ ϖ n hϖ g hg
  have hv0 : Valued.v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.exp_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hv0 (by rw [h, map_zero])
  have hnt : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, hv0, by rw [hϖ]; decide⟩
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  let G : GL (Fin n) L := Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.2 hg)
  obtain ⟨c, hc0, hcg, -⟩ := P.glint_exists_denom (n := Fin n) A G
  obtain ⟨d, -, k₁, h₁, k₂, h₂, e⟩ := P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ hϖ0
    (fun x hx => by
      have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      refine ⟨-WithZero.log (Valued.v x), ?_⟩
      rw [hϖ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hx']) G c hc0 hcg
  refine ⟨d, k₁, (k₁⁻¹ : GL (Fin n) L), k₂, (k₂⁻¹ : GL (Fin n) L), P.cartan_entries_of_mem _ _ h₁,
    P.cartan_entries_of_mem _ _ (inv_mem h₁), P.cartan_entries_of_mem _ _ h₂,
    P.cartan_entries_of_mem _ _ (inv_mem h₂), k₁.inv_mul, k₂.mul_inv, ?_⟩
  exact e
end GlobalTheory.InertZeta

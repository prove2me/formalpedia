-- Prove2me | solution 1 for GlobalTheory.CMVal.Fibre.hasProd_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:11.017235+00:00
-- url     : https://prove2.me/submissions/2774419a-f2c6-4676-89d7-5fe79127645c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Theorems.Thm_GlobalTheory_CMVal_Fibre_tendsto_of_cut
import Theorems.Thm_GlobalTheory_CMVal_Fibre_prod_single_apply
import Theorems.Thm_P2M_GlobalTheory_CMVal_Fibre_coord_inv__516d95d00b29
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Fibre
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Fibre
theorem _root_.solution (y : (Af E)ˣ) : HasProd (fun P => single P (coord P y)) y := by
  have h : ∀ y : (Af E)ˣ, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) =>
      ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E)) atTop (𝓝 (y : Af E)) := fun y =>
    tendsto_of_cut _ _ (prod_single_apply y)
  change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, single P (coord P y)) atTop (𝓝 y)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h y).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h y⁻¹
  simp only [coord_inv', map_inv, Finset.prod_inv_distrib] at h2
  exact h2
end GlobalTheory.CMVal.Fibre

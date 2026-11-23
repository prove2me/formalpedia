-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.exists_pole
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:24.874033+00:00
-- url     : https://prove2.me/submissions/09084963-4760-455e-a379-eb3a1b1ab07b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_exists_not_mem
import Theorems.Thm_GlobalTheory_SW_Nbr_exists_not_mem


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
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
omit [IsCMField E]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution (P : Ideal (𝓞 E)) [hP : P.IsMaximal] (hP0 : P ≠ ⊥) :
    ∃ t : E, (∀ c ∈ P, IsIntegral ℤ ((c : E) * t)) ∧ ∃ d ∈ P, ∃ r ∉ P, ((r : 𝓞 E) : E) = (d : E) * t := by
  obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := E) hP0 hP.ne_top
  have htP : ∀ c ∈ P, IsIntegral ℤ ((c : E) * t) := fun c hc => by
    have h1 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hP0)).1 ht _
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ hc)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have hb : (b : E) = t * (c : E) := hb
    rw [mul_comm, ← hb]; exact b.2
  exact ⟨t, htP, exists_not_mem hP0 (fun h => ht1 ((FractionalIdeal.mem_one_iff _).2 ⟨⟨t, h⟩, rfl⟩)) htP⟩
end GlobalTheory.SW.HeckeId

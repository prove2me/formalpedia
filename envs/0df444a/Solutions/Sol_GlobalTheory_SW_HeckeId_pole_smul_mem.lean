-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.pole_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:18.309953+00:00
-- url     : https://prove2.me/submissions/bcf6975d-0df7-4276-b2b5-4d2532e64da2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_smul_mem

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
theorem _root_.solution {P : Ideal (𝓞 E)} [hP : P.IsMaximal] {t : E}
    (ht : ∀ c ∈ P, IsIntegral ℤ ((c : E) * t)) {d r : 𝓞 E} (hd : d ∈ P) (hr : r ∉ P)
    (e : (r : E) = (d : E) * t) (L : Lt E n) (v : L) :
    t • (v : Fin n → E) ∈ L ↔ v ∈ (P • ⊤ : Submodule (𝓞 E) L) := by
  rw [Submodule.mem_smul_top_iff]
  constructor
  · intro h
    obtain ⟨u, c, hc, huc⟩ := hP.exists_inv hr
    have h1 : (v : Fin n → E) = u • (d • (t • (v : Fin n → E))) + c • (v : Fin n → E) := by
      rw [osmul d, smul_smul, ← e, ← osmul, smul_smul, ← add_smul, huc, one_smul]
    rw [h1]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.smul_mem_smul hd h))
      (Submodule.smul_mem_smul hc v.2)
  · intro h
    refine Submodule.smul_induction_on (p := fun w => t • w ∈ L) h (fun c hc x hx => ?_)
      fun x y hx hy => by rw [smul_add]; exact add_mem hx hy
    rw [osmul, smul_smul, mul_comm]
    exact L.smul_mem (⟨_, ht c hc⟩ : 𝓞 E) hx
end GlobalTheory.SW.HeckeId

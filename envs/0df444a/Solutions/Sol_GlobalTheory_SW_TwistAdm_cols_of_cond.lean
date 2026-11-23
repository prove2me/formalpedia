-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.cols_of_cond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:25.360339+00:00
-- url     : https://prove2.me/submissions/e4bc4583-32d5-458e-8610-12c56103ceeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_single_mem_std
import Theorems.Thm_GlobalTheory_SW_TwistAdm_col_eq

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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.TwistAdm
namespace _root_.GlobalTheory.SW.TwistAdm
theorem _root_.solution {R s : ℕ} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    {Λ : _root_.GlobalTheory.SW.Lt E n} {x : Matrix (Fin n) (Fin N) E}
    (hs : ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, (s : E) • v ∈ 𝔛)
    (hx : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) :
    _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((s : E) • x)) := by
  intro a
  have h1 := hx _ (hs _ (_root_.GlobalTheory.SW.TwistAdm.single_mem_std a))
  have e : ((R : E) • ((s : E) • x))ᵀ a = (R : E) • (x *ᵥ ((s : E) • Pi.single a 1)) := by
    rw [_root_.GlobalTheory.SW.TwistAdm.col_eq, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_smul]
  rw [e]
  exact h1
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm

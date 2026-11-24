-- Prove2me | solution 1 for GlobalTheory.PolModLattice.isIntegral_formSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:10.185389+00:00
-- url     : https://prove2.me/submissions/ee57c4a7-2362-4e76-9bcd-5afe97c3fabb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
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
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PolModLattice
theorem _root_.solution (L : Submodule (OF E) E) (N : ℕ) (hN : ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) :
    ∀ w ∈ formSpan L, IsIntegral ℤ ((N : E) ^ 2 * w) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hw
    have hb : ∀ t : E, IsIntegral ℤ t → IsIntegral ℤ (bar t) := fun t ht =>
      ht.map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)
    have e : (N : E) ^ 2 * altForm x y = (N * x) * bar (N * y) - bar (N * x) * (N * y) := by
      simp only [altForm, bar, map_mul, map_natCast]; ring
    rw [e]
    exact ((hN x hx).mul (hb _ (hN y hy))).sub ((hb _ (hN x hx)).mul (hN y hy))
  | zero => simpa using isIntegral_zero
  | add a b _ _ ha hb => rw [mul_add]; exact ha.add hb
  | smul c a _ ha =>
    rw [Algebra.smul_def, mul_left_comm]
    exact (c.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)).mul ha
end GlobalTheory.PolModLattice

-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:51.163173+00:00
-- url     : https://prove2.me/submissions/963fa785-c50c-4a8a-911f-8ae1ab573fc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}
open NumberField Complex
open scoped nonZeroDivisors ContDiff
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
theorem _root_.solution (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ)
    (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.QPair 𝔞 𝔟) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (Quotient.mk _ p) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z p.1 := by
  have hrel := Quotient.mk_out (s := _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟) p
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass
  generalize (Quotient.mk (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟) p).out = q at hrel ⊢
  obtain ⟨ε, h1, h2⟩ := hrel
  have hu : |Algebra.norm ℚ (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)| = 1 := NumberField.Units.norm F ε⁻¹
  have hmul : p.1.1 * p.1.2 = q.1.1 * q.1.2 := by
    rw [h1, h2, mul_mul_mul_comm, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul, one_mul]
  have hn : |((Algebra.norm ℚ p.1.1 : ℚ) : ℝ)| = |((Algebra.norm ℚ q.1.1 : ℚ) : ℝ)| := by
    rw [h1, map_mul, Rat.cast_mul, abs_mul, ← Rat.cast_abs, hu, Rat.cast_one, one_mul]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm
  rw [hn, hmul]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

-- Prove2me | solution 1 for GlobalTheory.FrobRestrict.isFrob_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:09.203458+00:00
-- url     : https://prove2.me/submissions/d577e401-67c5-4ceb-a87b-9879fd2ae6c8

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FrobeniusRestrictScalarsPowModInertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
noncomputable section
open GlobalTheory GlobalTheory.FrobRestrict
open scoped Pointwise
open NumberField IsDedekindDomain
open scoped Pointwise
namespace GlobalTheory.FrobRestrict
namespace _root_.GlobalTheory.FrobRestrict
theorem _root_.solution {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : _root_.Formalism.ConjugateSelfDual.G F Ω} (hφ : _root_.Formalism.ConjugateSelfDual.IsFrob A q φ) (n : ℕ) :
    _root_.Formalism.ConjugateSelfDual.IsFrob A (q ^ n) (φ ^ n) := by
  have hdec : φ ∈ ValuationSubring.decompositionSubgroup F A := hφ.1
  induction n with
  | zero => exact ⟨one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hdec _, fun x hx => ?_⟩
    have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one' hx q
    have e : (φ ^ (n + 1)) x - x ^ q ^ (n + 1)
        = ((φ ^ n) (x ^ q) - (x ^ q) ^ q ^ n) + (φ ^ n) (φ x - x ^ q) := by
      rw [pow_succ, AlgEquiv.mul_apply, map_sub, pow_succ', pow_mul]
      ring
    rw [e]
    refine Valuation.map_add_lt _ (ih.2 _ hxq) ?_
    rw [_root_.ReciprocityTheory.Gal.valuation_apply_lt_one_iff (Subgroup.pow_mem _ hdec n)]
    exact hφ.2 x hx
end _root_.GlobalTheory.FrobRestrict
end GlobalTheory.FrobRestrict

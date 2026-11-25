-- Prove2me | solution 1 for GroundTheory.Global.mem_inv_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:17:17.465964+00:00
-- url     : https://prove2.me/submissions/f2297c41-7cf6-46af-9aa1-320a5553fe24

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {M : Type*} [Field M] [NumberField M]
namespace GroundTheory.Global
theorem _root_.solution (w : HeightOneSpectrum (𝓞 M)) (n : ℕ) (x : M) :
    x ∈ ((w.asIdeal ^ n : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ↔
      w.valuation M x ≤ WithZero.exp (n : ℤ) ∧
        ∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M x ≤ 1 := by
  have hI : ((w.asIdeal ^ n : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact pow_ne_zero _ w.ne_bot
  rw [FractionalIdeal.mem_inv_iff hI]
  constructor
  · intro h
    have key : ∀ y ∈ w.asIdeal ^ n, ∀ u : HeightOneSpectrum (𝓞 M),
        u.valuation M x * u.intValuation y ≤ 1 := by
      intro y hy u
      obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 M))).1
        (h _ ((FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 M))).2 ⟨y, hy, rfl⟩))
      rw [← valuation_of_algebraMap (K := M), ← map_mul, ← hb, valuation_of_algebraMap]
      exact u.intValuation_le_one b
    refine ⟨?_, fun u hu ↦ ?_⟩
    · obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
      have hπn : w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
        rw [map_pow, hπ, ← WithZero.exp_nsmul]
        simp
      have hmem : π ^ n ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem _ n).1 hπn.le
      have h1 := key _ hmem w
      rw [hπn] at h1
      calc w.valuation M x
          = w.valuation M x * WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) := by
            rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
        _ ≤ 1 * WithZero.exp (n : ℤ) := by gcongr
        _ = WithZero.exp (n : ℤ) := one_mul _
    · have hnle : ¬ w.asIdeal ^ n ≤ u.asIdeal := by
        intro hle
        have hwu : w.asIdeal ≤ u.asIdeal := u.isPrime.le_of_pow_le hle
        exact hu (HeightOneSpectrum.ext
          ((w.isMaximal.eq_of_le u.isPrime.ne_top hwu).symm))
      obtain ⟨y, hy, hyu⟩ := SetLike.not_le_iff_exists.1 hnle
      have h1 := key y hy u
      have hy1 : u.intValuation y = 1 := le_antisymm (u.intValuation_le_one y)
        (not_lt.1 fun hlt ↦ hyu ((u.intValuation_lt_one_iff_mem y).1 hlt))
      rwa [hy1, mul_one] at h1
  · rintro ⟨hw, hu⟩ y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 M))).1 hy
    rw [FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 M))]
    refine mem_integers_of_valuation_le_one (R := 𝓞 M) (K := M) _ fun u ↦ ?_
    rw [map_mul, valuation_of_algebraMap]
    by_cases huw : u = w
    · subst huw
      calc u.valuation M x * u.intValuation y'
          ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) := by
            gcongr
            exact (u.intValuation_le_pow_iff_mem y' n).2 hy'
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    · simpa using mul_le_mul' (hu u huw) (u.intValuation_le_one y')
end GroundTheory.Global

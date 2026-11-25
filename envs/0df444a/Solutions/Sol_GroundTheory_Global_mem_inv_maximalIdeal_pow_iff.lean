-- Prove2me | solution 1 for GroundTheory.Global.mem_inv_maximalIdeal_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:23.912422+00:00
-- url     : https://prove2.me/submissions/db5fae5c-2139-4134-9e4b-06e8bf592eab

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_integers_valued
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_Global_valued_of_irreducible_integer
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
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion M)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)]
namespace GroundTheory.Global
theorem _root_.solution {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : u.adicCompletion F) :
    y ∈ ((𝓂[u.adicCompletion F] ^ n : Ideal 𝒪[u.adicCompletion F]) :
      FractionalIdeal (nonZeroDivisors 𝒪[u.adicCompletion F]) (u.adicCompletion F))⁻¹ ↔
      Valued.v y ≤ WithZero.exp (n : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[u.adicCompletion F]
  have hv : Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1) :=
    valued_of_irreducible_integer u hϖ
  have hvn : Valued.v ((ϖ : u.adicCompletion F) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hv, ← WithZero.exp_nsmul]
    simp
  have hϖ0 : ((ϖ : u.adicCompletion F) ^ n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvn
    exact WithZero.zero_ne_coe hvn
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_spanSingleton]
  change (∃ b : 𝒪[u.adicCompletion F], (b : u.adicCompletion F) *
    ((ϖ : u.adicCompletion F) ^ n)⁻¹ = y) ↔ _
  constructor
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_inv₀, hvn, WithZero.exp_neg, inv_inv]
    exact mul_le_of_le_one_left zero_le ((integers_valued u).map_le_one b)
  · intro hy
    have hb : Valued.v (y * (ϖ : u.adicCompletion F) ^ n) ≤ 1 := by
      rw [map_mul, hvn]
      calc Valued.v y * WithZero.exp (-(n : ℤ))
          ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) := by gcongr
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    refine ⟨⟨_, (mem_valuationInteger_iff u _).2 hb⟩, ?_⟩
    change y * (ϖ : u.adicCompletion F) ^ n * ((ϖ : u.adicCompletion F) ^ n)⁻¹ = y
    rw [mul_assoc, mul_inv_cancel₀ hϖ0, mul_one]
end GroundTheory.Global

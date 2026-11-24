-- Prove2me | solution 1 for GlobalTheory.QNorm.NormOpen.eventually_isSquare_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:42:38.481587+00:00
-- url     : https://prove2.me/submissions/c7486db0-7161-4b9c-a24d-a7ad58926a1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOne
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_hiUnits_le_sqs_hiUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Topology
open GlobalTheory GlobalTheory.QNorm
open GlobalTheory.QNorm.NormOpen
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.QNorm.NormOpen
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    ∀ᶠ x in 𝓝 (1 : v.adicCompletion F), IsSquare x := by
  have h2eq : ((2 : F) : v.adicCompletion F) = 2 := by
    rw [show (2 : F) = 1 + 1 from one_add_one_eq_two.symm,
      show (2 : v.adicCompletion F) = 1 + 1 from one_add_one_eq_two.symm,
      HeightOneSpectrum.adicCompletion.coe_add, HeightOneSpectrum.adicCompletion.coe_one]
  have h2v : Valued.v (2 : v.adicCompletion F) ≠ 0 := by
    rw [← h2eq, HeightOneSpectrum.adicCompletion.valued_coe]
    exact (Valuation.ne_zero_iff _).2 two_ne_zero
  have h2le : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
    rw [← one_add_one_eq_two]
    exact (Valued.v.map_add 1 1).trans (by simp)
  set m : ℤ := WithZero.log (Valued.v (2 : v.adicCompletion F)) with hm
  have hexp : WithZero.exp m = Valued.v (2 : v.adicCompletion F) := WithZero.exp_log h2v
  have hm0 : m ≤ 0 := by
    rw [← WithZero.exp_le_exp, hexp, WithZero.exp_zero]
    exact h2le
  set e : ℕ := (-m).toNat with he_def
  have he : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    rw [← hexp, he_def, this, neg_neg]
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set c : v.adicCompletion F := ((π : F) : v.adicCompletion F) ^ (2 * e + 1) with hc_def
  have hc : Valued.v c = WithZero.exp (-((2 * e + 1 : ℕ) : ℤ)) := by
    rw [hc_def, map_pow, HeightOneSpectrum.adicCompletion.valued_coe, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have hc1 : Valued.v c < 1 := by
    rw [hc, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl, WithZero.exp_lt_exp]
    omega
  have hN : {x : v.adicCompletion F | (x - 1) * c⁻¹ ∈ (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).integer} ∈
      𝓝 (1 : v.adicCompletion F) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
    · simp [Valuation.mem_integer_iff]
  filter_upwards [hN] with x hx
  rw [Valuation.mem_integer_iff] at hx
  have hle : Valued.v (x - 1) ≤ Valued.v c :=
    calc Valued.v (x - 1) = Valued.v ((x - 1) * c⁻¹) * Valued.v c := by
          rw [← map_mul, inv_mul_cancel_right₀ hc0]
      _ ≤ 1 * Valued.v c := by gcongr
      _ = Valued.v c := one_mul _
  have hvx : Valued.v x = 1 := by
    have : x = 1 + (x - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ (hle.trans_lt hc1)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hvx
    exact zero_ne_one hvx
  have hu : Units.mk0 x hx0 ∈ hiUnits (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (2 * e + 1) :=
    ⟨hvx, hc ▸ hle⟩
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (hiUnits_le_sqs_hiUnits F v e he hu)
  have hy' := congrArg Units.val hy
  simp only [powMonoidHom_apply, Units.val_mk0, pow_two] at hy'
  exact ⟨y, hy'.symm⟩
end GlobalTheory.QNorm.NormOpen

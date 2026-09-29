-- Prove2me | solution 1 for ModularCurve.coeff_qExpansionDiffAlong_cartier_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/37dd40dc-3778-5856-ad5e-edd9cbcabced

import Mathlib
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Theorems.Thm_AlgebraicCurve_kw_cart_C_eq_of_cartierLaws
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Theorems.Thm_ModularCurve_D_jqModC_ne_zero
import Theorems.Thm_AlgebraicCurve_KwPke_kw_pke_hsep_of_isSeparable_adjoin
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_cartier_pow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "ModularCurve P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_cartier_pow.ModularCurve AlgebraicCurve AlgebraicCurve.KwCart AlgebraicCurve.KwPke HahnSeries"

namespace ModularCurve
p2m_export "ModularCurve" "thetaL thetaL_apply qExpansionDiffAlong jqModC jqNModC modularFunctionFieldC jqModC_mem coeff_qExpansionDiffAlong_kw_cart_C_pow isIntegral_jqNModC_all isSeparable_adjoin_jqModC_of_isAlgebraic D_jqModC_ne_zero coeff_jqModC_neg_one"
namespace CartierQExpAbs
p2m_open "ModularCurve"

section Presentation

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem adjoin_jqModC_le :
    IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤
      IntermediateField.adjoin K ({jqModC K, jqNModC K N} : Set (LaurentSeries K)) :=
  IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem lift_adjoin :
    IntermediateField.lift (IntermediateField.adjoin K
        ({⟨jqModC K, jqModC_mem K N⟩} : Set (modularFunctionFieldC K N))) =
      IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  rw [IntermediateField.lift_adjoin_simple]

def ringEquivAdjoin :
    (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) ≃+*
      (IntermediateField.adjoin K
        ({⟨jqModC K, jqModC_mem K N⟩} : Set (modularFunctionFieldC K N))) where
  toFun y := ⟨⟨y.1, adjoin_jqModC_le K N y.2⟩,
    (IntermediateField.mem_lift (⟨y.1, adjoin_jqModC_le K N y.2⟩ : modularFunctionFieldC K N)).1
      ((SetLike.ext_iff.mp (lift_adjoin K N) y.1).2 y.2)⟩
  invFun z := ⟨z.1.1,
    (SetLike.ext_iff.mp (lift_adjoin K N) z.1.1).1 ((IntermediateField.mem_lift z.1).2 z.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def ringEquivExtendScalars :
    (IntermediateField.extendScalars (adjoin_jqModC_le K N)) ≃+* (modularFunctionFieldC K N) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem finiteDimensional_adjoin_jqModC_gen :
    FiniteDimensional
      (IntermediateField.adjoin K ({⟨jqModC K, jqModC_mem K N⟩} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) := by
  haveI : FiniteDimensional (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.extendScalars (adjoin_jqModC_le K N)) := by
    rw [IntermediateField.extendScalars_adjoin (adjoin_jqModC_le K N)]
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    rcases hx with rfl | rfl
    · exact isIntegral_algebraMap
        (x := (⟨jqModC K, IntermediateField.mem_adjoin_simple_self K (jqModC K)⟩ :
          IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))))
    · exact isIntegral_jqNModC_all K N
  exact Module.Finite.of_equiv_equiv (ringEquivAdjoin K N) (ringEquivExtendScalars K N)
    (RingHom.ext fun _ => rfl)

end Presentation

theorem coeff_thetaL {K : Type*} [Field K] (f : LaurentSeries K) (n : ℤ) :
    (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  have h1 : n - 1 + ((1 : ℕ) : ℤ) = n := by push_cast; ring
  rw [h1, Ring.choose_one_right, ← Int.cast_smul_eq_zsmul K n (f.coeff n), smul_eq_mul]

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] :
    thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun s => HahnSeries.coeff s (-1)) h
  simp only [coeff_thetaL, coeff_jqModC_neg_one, HahnSeries.coeff_zero] at h1
  norm_num at h1

theorem coeff_finset_sum {K : Type*} [Field K] {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (n : ℤ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

end ModularCurve.CartierQExpAbs

open ModularCurve.CartierQExpAbs

theorem solution
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (N : ℕ) [NeZero N] [IsCurveOver K (modularFunctionFieldC K N)]
    (C : Ω[↥(modularFunctionFieldC K N)⁄K] →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hsemi : ∀ (f : modularFunctionFieldC K N) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]),
      C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : modularFunctionFieldC K N,
      C (KaehlerDifferential.D K (modularFunctionFieldC K N) f) = 0)
    (hlog : ∀ f : modularFunctionFieldC K N,
      C (f ^ (p - 1) • KaehlerDifferential.D K (modularFunctionFieldC K N) f)
        = KaehlerDifferential.D K (modularFunctionFieldC K N) f)
    (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (n : ℤ) :
    (qExpansionDiffAlong (modularFunctionFieldC K N).val (C ω)).coeff n ^ p
      = (qExpansionDiffAlong (modularFunctionFieldC K N).val ω).coeff (n * p) := by
  haveI hfd := finiteDimensional_adjoin_jqModC_gen K N
  haveI : Algebra.IsAlgebraic
      (IntermediateField.adjoin K ({⟨jqModC K, jqModC_mem K N⟩} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) := Algebra.IsAlgebraic.of_finite _ _
  haveI : CharP (modularFunctionFieldC K N) p :=
    charP_of_injective_algebraMap (algebraMap K (modularFunctionFieldC K N)).injective p
  have hsepK := ModularCurve.isSeparable_adjoin_jqModC_of_isAlgebraic K (modularFunctionFieldC K N)
    (jqModC_mem K N)
  set t : modularFunctionFieldC K N := ⟨jqModC K, jqModC_mem K N⟩ with ht
  have hdt : KaehlerDifferential.D K (modularFunctionFieldC K N) t ≠ 0 := ModularCurve.D_jqModC_ne_zero K N
  have hspan : Submodule.span (modularFunctionFieldC K N) {KaehlerDifferential.D K (modularFunctionFieldC K N) t} = ⊤ :=
    kw_cart_hspan_of_isCurveOver (K := K) hdt
  have hsep : ∀ y : modularFunctionFieldC K N, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield y :=
    AlgebraicCurve.KwPke.kw_pke_hsep_of_isSeparable_adjoin (K := K) (ℓ := p) t hsepK
  have hdeg : (minpoly (kw_pke_pthPowers (modularFunctionFieldC K N) p) t).natDegree = p :=
    kw_cart_minpoly_natDegree_eq (K := K) (ℓ := p) hdt
  rw [← AlgebraicCurve.kw_cart_C_eq_of_cartierLaws (K := K) p t t hdt hspan hsep hdeg C hsemi hker hlog ω]
  exact ModularCurve.coeff_qExpansionDiffAlong_kw_cart_C_pow p (modularFunctionFieldC K N) t hdt hspan hsep hdeg ω n

end S_ModularCurve_coeff_qExpansionDiffAlong_cartier_pow
end P2MW
export P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_cartier_pow (solution)

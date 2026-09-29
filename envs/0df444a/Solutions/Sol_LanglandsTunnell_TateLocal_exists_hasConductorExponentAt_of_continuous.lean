-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/33bf76e1-4d02-5f2b-a037-86e3b6934791

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_Converse_units_eq_one_of_forall_zpow_norm_sub_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

open NumberField IsDedekindDomain

open LanglandsTunnell.TateLocal in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ c : ℕ, HasConductorExponentAt K v χ c := by
  classical
  suffices hex : ∃ n : ℕ, ∀ u ∈ higherUnitsAt K v n, χ u = 1 by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun m hm => ?_⟩
    by_contra hcon
    exact Nat.find_min hex hm fun u hu => by_contra fun hne => hcon ⟨u, hu, hne⟩

  have hU : {x : ℂˣ | ‖(x : ℂ) - 1‖ < 1} ∈ nhds (1 : ℂˣ) := by
    have hopen : IsOpen {x : ℂˣ | ‖(x : ℂ) - 1‖ < 1} :=
      isOpen_lt (Units.continuous_val.sub continuous_const).norm continuous_const
    refine hopen.mem_nhds ?_
    simp
  have hN : (fun u : (v.adicCompletion K)ˣ => χ u) ⁻¹' {x : ℂˣ | ‖(x : ℂ) - 1‖ < 1}
      ∈ nhds (1 : (v.adicCompletion K)ˣ) :=
    hχ.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)

  rw [Units.isInducing_embedProduct.nhds_eq_comap] at hN
  obtain ⟨W, hW, hWsub⟩ := Filter.mem_comap.mp hN
  rw [map_one, ← Prod.mk_one_one] at hW
  obtain ⟨W₁, hW₁, W₂, hW₂, hW₁₂⟩ := mem_nhds_prod_iff.mp hW
  have hW₂' : MulOpposite.op ⁻¹' W₂ ∈ nhds (1 : v.adicCompletion K) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rw [MulOpposite.op_one]; exact hW₂)
  have hV : W₁ ∩ MulOpposite.op ⁻¹' W₂ ∈ nhds (1 : v.adicCompletion K) := Filter.inter_mem hW₁ hW₂'
  have hkey : ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ →
      ‖((χ u : ℂˣ) : ℂ) - 1‖ < 1 := by
    intro u hu hu'
    have hmem : Units.embedProduct (v.adicCompletion K) u ∈ W₁ ×ˢ W₂ :=
      Set.mk_mem_prod hu.1 hu'.2
    exact hWsub (Set.mem_preimage.mpr (hW₁₂ hmem))

  obtain ⟨n, hn0, hn⟩ : ∃ n : ℕ, 0 < n ∧ ∀ y : v.adicCompletion K,
      Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ)) → y ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ := by
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hV
    have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) :=
      (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
    refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1,
      Nat.succ_pos _, fun y hy => ?_⟩
    refine hγ ?_
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    calc Valued.v (y - 1) ≤ _ := hy
      _ < WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) :=
          WithZero.exp_lt_exp.mpr (by omega)
      _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := WithZero.exp_log hγ0
  have hn0' : n ≠ 0 := hn0.ne'

  let H : Subgroup (v.adicCompletion K)ˣ :=
    { carrier := higherUnitsAt K v n
      one_mem' := one_mem_higherUnitsAt K v n
      mul_mem' := by
        intro a b ha hb
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨hb1, hb2⟩ := hb
        have ha2' := ha2.resolve_left hn0'
        have hb2' := hb2.resolve_left hn0'
        refine ⟨?_, Or.inr ?_⟩
        · rw [Units.val_mul, map_mul, ha1, hb1, one_mul]
        · have heq : ((a * b : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1
              = (a : v.adicCompletion K) * ((b : v.adicCompletion K) - 1)
                + ((a : v.adicCompletion K) - 1) := by
            rw [Units.val_mul]
            ring
          rw [heq]
          refine Valued.v.map_add_le ?_ ha2'
          rw [map_mul, ha1, one_mul]
          exact hb2'
      inv_mem' := by
        intro a ha
        obtain ⟨ha1, ha2⟩ := ha
        have ha2' := ha2.resolve_left hn0'
        have hinv : Valued.v ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀, ha1, inv_one]
        refine ⟨hinv, Or.inr ?_⟩
        have heq : ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1
            = ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)
              * (1 - (a : v.adicCompletion K)) := by
          rw [mul_sub, mul_one, Units.inv_mul]
        rw [heq, map_mul, hinv, one_mul, Valuation.map_sub_swap]
        exact ha2' }
  have hball : ∀ w : (v.adicCompletion K)ˣ, w ∈ H →
      (w : v.adicCompletion K) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ := by
    intro w hw
    have hw' : w ∈ higherUnitsAt K v n := hw
    exact hn _ (((mem_higherUnitsAt_iff K v).mp hw').2.resolve_left hn0')

  refine ⟨n, fun u hu => ?_⟩
  have huH : u ∈ H := hu
  refine LanglandsTunnell.Converse.units_eq_one_of_forall_zpow_norm_sub_one_lt (χ u) fun m => ?_
  rw [← map_zpow]
  exact hkey _ (hball _ (H.zpow_mem huH m)) (hball _ (H.inv_mem (H.zpow_mem huH m)))

end S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous (solution)

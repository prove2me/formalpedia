-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.orderC_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:54:12.805246+00:00
-- url     : https://prove2.me/submissions/c8f9154e-546d-4440-b81e-d474850befb6

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_prime_not_mem_sq
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_root_of_unity_eq_one
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
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (hc : 𝔣 ∣ c)
    (x : E) (hx0 : x ≠ 0) (hx : x ∈ orderC c) (hx' : x⁻¹ ∈ orderC c) : ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  obtain ⟨h0, h1, h⟩ := h𝔣
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔣 h1
  have hM0 : M ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hle))
  obtain ⟨⟨P, -, -, hP, -⟩, -, l, hl, hl2, hlv, hd, -⟩ := h ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.2 hle)
  have hP' : P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = M := hP
  have hlP : (l : 𝓞 E) ∈ P.asIdeal := by
    have : (l : OF E) ∈ P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) := by rw [hP']; exact hlv
    simpa using this
  have hcP : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 (hP' ▸ (Ideal.le_of_dvd hc).trans hle)
  obtain ⟨a, b, hb, hab⟩ := mem_orderC.1 hx
  obtain ⟨a', b', -, hab'⟩ := mem_orderC.1 hx'
  have e1 : x = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by rw [hab, map_add]; rfl
  have e2 : x⁻¹ = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a' + b') := by rw [hab', map_add]; rfl
  have hu : (algebraMap (OF E) (𝓞 E) a + b) * (algebraMap (OF E) (𝓞 E) a' + b') = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, ← e1, ← e2, mul_inv_cancel₀ hx0, map_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne _ _ hu
  have huv : (u : 𝓞 E) = algebraMap (OF E) (𝓞 E) a + b := rfl
  have hbc : IsCMField.ringOfIntegersComplexConj E b ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    have : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤
        (Ideal.map (algebraMap (OF E) (𝓞 E)) c).comap (IsCMField.ringOfIntegersComplexConj E) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact this hb
  have hcu : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) =
      algebraMap (OF E) (𝓞 E) a + IsCMField.ringOfIntegersComplexConj E b := by
    have : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) = IsCMField.ringOfIntegersComplexConj E u := rfl
    rw [this, huv, map_add, AlgEquiv.commutes]
  let ζ : (𝓞 E)ˣ := u * (IsCMField.unitsComplexConj E u)⁻¹
  have hfin : IsOfFinOrder ζ := (IsCMField.unitsMulComplexConjInv E u).2
  have hfin' : IsOfFinOrder (ζ : 𝓞 E) := (Units.coeHom (𝓞 E)).isOfFinOrder hfin
  have hζ : (ζ : 𝓞 E) - 1 ∈ P.asIdeal := by
    have : (ζ : 𝓞 E) - 1 = (b - IsCMField.ringOfIntegersComplexConj E b) * ↑(IsCMField.unitsComplexConj E u)⁻¹ := by
      have h3 := (IsCMField.unitsComplexConj E u).mul_inv
      rw [hcu] at h3
      simp only [ζ, Units.val_mul, huv]
      linear_combination h3
    rw [this]
    exact P.asIdeal.mul_mem_right _ (hcP (sub_mem hb hbc))
  have hone : ζ = 1 := Units.ext (root_of_unity_eq_one P.isPrime.ne_top hl hl2 hlP (prime_not_mem_sq hl hd P hlP) hfin' hζ)
  have hreal := (IsCMField.unitsComplexConj_eq_self_iff E u).1 (mul_inv_eq_one.1 hone).symm
  obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E u).1 hreal
  refine ⟨v, ?_⟩
  rw [e1, ← huv, ← hv]
  rfl
end GlobalTheory.CMVal.OrderUnits

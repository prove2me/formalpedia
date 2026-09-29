-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/891d9747-1bd4-5345-a9a9-f7797b3cd91d

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt.LanglandsTunnell LanglandsTunnell.Converse"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg"
open AutomorphicForm

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL3 inducedLevelAt localMaximalCompact3 congruenceK1 mem_localMaximalCompact3_of_mem_congruenceK1"
namespace TwistLevel
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem ringHom_ringOfIntegers_rat_ext {S : Type*} [Ring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  ext x
  have hx : x = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h _

theorem algebra_ringOfIntegers_rat_eq (X : Type) [Field X] [NumberField X] (i : Algebra (𝓞 ℚ) (𝓞 X)) :
    i = NumberField.inst_ringOfIntegersAlgebra ℚ X :=
  Algebra.algebra_ext i (NumberField.inst_ringOfIntegersAlgebra ℚ X) fun r =>
    RingHom.congr_fun
      (ringHom_ringOfIntegers_rat_ext (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ i)
        (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ X))) r

theorem localChar_twist_apply_eq_of_mem_integers (K : Type) [Field K] [NumberField K]
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : v.Extension (𝓞 K)) (hχ : IsUnramifiedCharAt χ v)
    (t : (W.1.adicCompletion K)ˣ) (ht : (t : W.1.adicCompletion K) ∈ W.1.adicCompletionIntegers K)
    (ht' : ((t⁻¹ : (W.1.adicCompletion K)ˣ) : W.1.adicCompletion K) ∈ W.1.adicCompletionIntegers K) :
    localChar (ν * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) W.1 t = localChar ν W.1 t := by
  rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K ν χ v W, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  have h1 : localChar χ v (Units.map (Algebra.norm (v.adicCompletion ℚ)) t) = 1 := by
    refine hχ _ ?_ ?_
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.coe_map,
        M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg ℚ K v W]
      exact pow_le_one₀ zero_le' ht
    · rw [← map_inv, HeightOneSpectrum.mem_adicCompletionIntegers, Units.coe_map,
        M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg ℚ K v W]
      exact pow_le_one₀ zero_le' ht'
  rw [h1, mul_one]

theorem hasConductorExponentAt_congr_units (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ₁ χ₂ : (v.adicCompletion K)ˣ →* ℂˣ)
    (h : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ₁ u = χ₂ u) (c : ℕ)
    (h₁ : LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ₁ c) :
    LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ₂ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [← h u ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff K v).mp hu).1]
    exact h₁.1 u hu
  · obtain ⟨u, hu, hne⟩ := h₁.2 m hm
    refine ⟨u, hu, fun h2 => hne ?_⟩
    rw [h u ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff K v).mp hu).1]
    exact h2

theorem conductorExponentAt_twist_eq (K : Type) [Field K] [NumberField K]
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v)
    (w : HeightOneSpectrum (𝓞 K)) (hw : w ∈ primeFibre ℚ K v) :
    LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar (ν * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w) =
      LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar ν w) := by
  have key : ∀ u : (w.adicCompletion K)ˣ, Valued.v (u : w.adicCompletion K) = 1 →
      localChar (ν * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w u = localChar ν w u := fun u hu =>
    localChar_twist_apply_eq_of_mem_integers K ν χ v ⟨w, hw⟩ hχ u
      (by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hu.le)
      (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])
  unfold LanglandsTunnell.TateLocal.conductorExponentAt
  congr 1
  ext c
  simp only [Set.mem_setOf_eq]
  exact ⟨fun h => hasConductorExponentAt_congr_units K w _ _ key c h,
    fun h => hasConductorExponentAt_congr_units K w _ _ (fun u hu => (key u hu).symm) c h⟩

theorem valued_det_le_one (v : HeightOneSpectrum (𝓞 ℚ))
    (N : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (h : ∀ i j, Valued.v (N i j) ≤ 1) :
    Valued.v N.det ≤ 1 := by
  let M : Matrix (Fin 3) (Fin 3) (v.adicCompletionIntegers ℚ) := fun i j =>
    ⟨N i j, by rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]; exact h i j⟩
  have hM : (v.adicCompletionIntegers ℚ).subtype.mapMatrix M = N := by
    ext i j
    rfl
  have hdet : N.det = (v.adicCompletionIntegers ℚ).subtype M.det := by
    rw [RingHom.map_det, hM]
  have hmem := M.det.2
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hmem
  rw [hdet]
  exact hmem

theorem localChar_det_eq_one_of_mem (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v)
    (u : LocalGL3 v) (hu : u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    localChar χ v (Matrix.GeneralLinearGroup.det u) = 1 := by
  obtain ⟨h1, h2⟩ := hu
  apply hχ
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact valued_det_le_one v _ h1
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← map_inv,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact valued_det_le_one v _ h2

end LanglandsTunnell.CubicInduction.TwistLevel

open LanglandsTunnell.CubicInduction.TwistLevel in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hν : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (v : HeightOneSpectrum (𝓞 ℚ)) (_hχv : IsUnramifiedCharAt χA v) :
    (∀ 𝔓 ∈ primeFibre ℚ K v,
      LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
        LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar ν 𝔓)) ∧
    inducedLevelAt K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v = inducedLevelAt K ν v ∧
    (∀ (c : ℕ) (W : LocalGL3 v → ℂ),
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g : LocalGL3 v, W (g * k) = W g) →
      ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g : LocalGL3 v,
        (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) (g * k) =
          (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) g) := by
  classical
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  refine ⟨fun 𝔓 h𝔓 => conductorExponentAt_twist_eq K ν χA v _hχv 𝔓 h𝔓, ?_, ?_⟩
  · unfold inducedLevelAt
    exact finsum_mem_congr rfl fun 𝔓 h𝔓 => by rw [conductorExponentAt_twist_eq K ν χA v _hχv 𝔓 h𝔓]
  · intro c W hW k hk g
    have hk1 : localChar χA v (Matrix.GeneralLinearGroup.det k) = 1 :=
      localChar_det_eq_one_of_mem χA v _hχv k (mem_localMaximalCompact3_of_mem_congruenceK1 (𝓞 ℚ) ℚ v hk)
    beta_reduce
    rw [map_mul, map_mul, hk1, mul_one, hW k hk g]

#print axioms solution

end S_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt (solution)

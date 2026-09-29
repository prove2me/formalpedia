-- Prove2me | solution 1 for LanglandsTunnell.Converse.finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/96e47807-27c8-5872-bd5d-f6ca1bb7c479

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_two_mul_conductorExponent_le
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor.LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "pinnedExp IsAdmissibleTwist"
namespace EpsDeepTwist
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

theorem algebra_ringOfIntegers_rat_ext (R : Type) [CommRing R] (i₁ i₂ : Algebra (𝓞 ℚ) R) : i₁ = i₂ := by
  have h : ∀ f g : 𝓞 ℚ →+* R, f = g := fun f g => by
    have hh : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
      Subsingleton.elim _ _
    refine RingHom.ext fun r => ?_
    have := RingHom.congr_fun hh (Rat.ringOfIntegersEquiv r)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] at this
    exact this
  exact Algebra.algebra_ext _ _ (RingHom.congr_fun (h _ _))

theorem exists_hasConductorExponentAt_le_of_forall_mem_higherUnitsAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (θ : (v.adicCompletion K)ˣ →* ℂˣ) (n : ℕ) (h : ∀ u ∈ higherUnitsAt K v n, θ u = 1) :
    ∃ c ≤ n, HasConductorExponentAt K v θ c := by
  classical
  have hex : ∃ m, ∀ u ∈ higherUnitsAt K v m, θ u = 1 := ⟨n, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, ?_⟩
  unfold HasConductorExponentAt
  refine ⟨Nat.find_spec hex, fun m hm => ?_⟩
  have hmin := Nat.find_min hex hm
  simpa only [not_forall, exists_prop] using hmin

theorem local_pair (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ θ₁ θ₂ : (v.adicCompletion K)ˣ →* ℂˣ) (a b₁ b₂ : ℕ)
    (hχ : HasConductorExponentAt K v χ a)
    (h₁ : HasConductorExponentAt K v θ₁ b₁) (h₂ : HasConductorExponentAt K v θ₂ b₂)
    (hb₁ : 2 * b₁ < a) (hb₂ : 2 * b₂ < a)
    (hu : ‖((χ (NumberField.AdelicLevel.uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1)
    (hu₁ : ‖((θ₁ (NumberField.AdelicLevel.uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1)
    (hu₂ : ‖((θ₂ (NumberField.AdelicLevel.uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) :
    conductorExponentAt K v (χ * θ₁) = a ∧ conductorExponentAt K v (χ * θ₂) = a ∧
      conductorExponentAt K v (χ * (θ₁ * θ₂)) = a ∧
      stdRootNumberAt K v (χ * θ₁) * stdRootNumberAt K v (χ * θ₂) =
        stdRootNumberAt K v (χ * (θ₁ * θ₂)) * stdRootNumberAt K v χ := by
  have h₁triv : ∀ u ∈ higherUnitsAt K v b₁, θ₁ u = 1 := by obtain ⟨h, -⟩ := h₁; exact h
  have h₂triv : ∀ u ∈ higherUnitsAt K v b₂, θ₂ u = 1 := by obtain ⟨h, -⟩ := h₂; exact h
  have h12triv : ∀ u ∈ higherUnitsAt K v (max b₁ b₂), (θ₁ * θ₂) u = 1 := fun u hu' => by
    have hu1 : u ∈ higherUnitsAt K v b₁ := higherUnitsAt_antitone K v (le_max_left _ _) hu'
    have hu2 : u ∈ higherUnitsAt K v b₂ := higherUnitsAt_antitone K v (le_max_right _ _) hu'
    rw [MonoidHom.mul_apply, h₁triv u hu1, h₂triv u hu2, one_mul]
  obtain ⟨b₁₂, hb₁₂le, h₁₂⟩ :=
    exists_hasConductorExponentAt_le_of_forall_mem_higherUnitsAt K v (θ₁ * θ₂) (max b₁ b₂) h12triv
  have hb₁₂ : 2 * b₁₂ < a := by
    rcases le_total b₁ b₂ with h | h
    · rw [max_eq_right h] at hb₁₂le; omega
    · rw [max_eq_left h] at hb₁₂le; omega
  have hu₁₂ : ‖(((θ₁ * θ₂) (NumberField.AdelicLevel.uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hu₁, hu₂, one_mul]
  have hc₁ : HasConductorExponentAt K v (χ * θ₁) a :=
    hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt K v χ θ₁ a b₁ hχ h₁ (by omega)
  have hc₂ : HasConductorExponentAt K v (χ * θ₂) a :=
    hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt K v χ θ₂ a b₂ hχ h₂ (by omega)
  have hc₁₂ : HasConductorExponentAt K v (χ * (θ₁ * θ₂)) a :=
    hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt K v χ (θ₁ * θ₂) a b₁₂ hχ h₁₂ (by omega)
  refine ⟨conductorExponentAt_eq_of_hasConductorExponentAt K v hc₁,
    conductorExponentAt_eq_of_hasConductorExponentAt K v hc₂,
    conductorExponentAt_eq_of_hasConductorExponentAt K v hc₁₂, ?_⟩
  rcases Nat.lt_or_ge a 2 with ha | ha
  ·
    have ha1 : a = 1 := by omega
    subst ha1
    have e1 : b₁ = 0 := by omega
    have e2 : b₂ = 0 := by omega
    have e12 : b₁₂ = 0 := by omega
    subst e1 e2 e12
    have hψ := psiLocal_ne_one K v
    rw [stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v χ θ₁ 1 hχ h₁ hu hu₁ hψ,
      stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v χ θ₂ 1 hχ h₂ hu hu₂ hψ,
      stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v χ (θ₁ * θ₂) 1 hχ h₁₂ hu hu₁₂ hψ,
      MonoidHom.mul_apply, Units.val_mul, mul_zpow]
    ring
  ·
    obtain ⟨c, hc⟩ :=
      exists_forall_mem_higherUnitsAt_apply_eq_psiLocal_mul_sub_one_of_hasConductorExponentAt K v χ a hχ
    rw [mul_comm χ θ₁, mul_comm χ θ₂, mul_comm χ (θ₁ * θ₂),
      stdRootNumberAt_mul_of_two_mul_conductorExponent_le K v χ θ₁ a b₁ hχ h₁ ha (by omega) hu hu₁ c hc,
      stdRootNumberAt_mul_of_two_mul_conductorExponent_le K v χ θ₂ a b₂ hχ h₂ ha (by omega) hu hu₂ c hc,
      stdRootNumberAt_mul_of_two_mul_conductorExponent_le K v χ (θ₁ * θ₂) a b₁₂ hχ h₁₂ ha (by omega) hu hu₁₂ c hc,
      MonoidHom.mul_apply, Units.val_mul, mul_inv]
    ring

theorem regroup (m1 m2 m12 m0 e1 e2 e12 e0 Y : ℂ) (hm : m1 * m2 = m12 * m0)
    (he : e1 * e2 = e12 * e0) :
    m1 * m2 * (e1 * Y * (e2 * Y)) = m12 * m0 * (e12 * Y * (e0 * Y)) := by
  rw [hm]
  congr 1
  linear_combination Y ^ 2 * he

end LanglandsTunnell.Converse.EpsDeepTwist

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : LanglandsTunnell.Converse.IsAdmissibleTwist K μ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (lam : ℂ)
    (b : ℕ)
    (hfloor : ∀ w ∈ primeFibre ℚ K p,
      2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w))
    (η₁A η₂A : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hη₁A : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ η₁A)
    (hη₂A : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ η₂A)
    (hη₁AN : LanglandsTunnell.Converse.IsAdmissibleTwist K
      (η₁A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm))
    (hη₂AN : LanglandsTunnell.Converse.IsAdmissibleTwist K
      (η₂A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm))
    (c₁ c₂ : ℕ)
    (hc₁ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar η₁A p) c₁)
    (hc₂ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar η₂A p) c₂)
    (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) :
    ∀ s : ℂ,
      (lam *
      (∏ᶠ w ∈ primeFibre ℚ K p,
        ((NumberField.TateGlobal.localChar
          (η₁A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
      (∏ᶠ w ∈ primeFibre ℚ K p,
        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
            (NumberField.TateGlobal.localChar
              (η₁A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
            (LanglandsTunnell.Converse.pinnedExp K
                (η₁A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))) *
      (lam *
      (∏ᶠ w ∈ primeFibre ℚ K p,
        ((NumberField.TateGlobal.localChar
          (η₂A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
      (∏ᶠ w ∈ primeFibre ℚ K p,
        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
            (NumberField.TateGlobal.localChar
              (η₂A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
            (LanglandsTunnell.Converse.pinnedExp K
                (η₂A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))) =
      (lam ^ 2 *
      ((∏ᶠ w ∈ primeFibre ℚ K p,
          ((NumberField.TateGlobal.localChar ((η₁A * η₂A).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
        ∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ)) *
      ((∏ᶠ w ∈ primeFibre ℚ K p,
          (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar ((η₁A * η₂A).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
            (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
              (LanglandsTunnell.Converse.pinnedExp K ((η₁A * η₂A).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))) *
        ∏ᶠ w ∈ primeFibre ℚ K p,
          (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar μ w) *
            (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
              (LanglandsTunnell.Converse.pinnedExp K μ w)))) := by
  intro s

  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
    EpsDeepTwist.algebra_ringOfIntegers_rat_ext _ _ _
  obtain ⟨-, -, hμu⟩ := hμ
  obtain ⟨-, -, hη₁u⟩ := hη₁A
  obtain ⟨-, -, hη₂u⟩ := hη₂A
  have hF : (primeFibre ℚ K p).Finite := by
    have : Finite (p.Extension (𝓞 K)) := HeightOneSpectrum.Extension.finite (𝓞 ℚ) ℚ K (𝓞 K) p
    refine (Set.finite_range (fun W : p.Extension (𝓞 K) => W.1)).subset ?_
    intro x hx
    exact ⟨⟨x, (mem_primeFibre ℚ p x).1 hx⟩, rfl⟩
  have key : ∀ (l A1 B1 A2 B2 A12 A0 B12 B0 : ℂ), A1 * A2 * (B1 * B2) = A12 * A0 * (B12 * B0) →
      l * A1 * B1 * (l * A2 * B2) = l ^ 2 * (A12 * A0) * (B12 * B0) := by
    intro l A1 B1 A2 B2 A12 A0 B12 B0 h
    linear_combination l ^ 2 * h
  refine key _ _ _ _ _ _ _ _ _ ?_
  simp only [← finprod_mem_mul_distrib hF]
  refine finprod_mem_congr rfl fun w hw => ?_
  have hw' : w.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p w).1 hw

  have Hm : NumberField.TateGlobal.localChar (η₁A * η₂A) p =
      NumberField.TateGlobal.localChar η₁A p * NumberField.TateGlobal.localChar η₂A p :=
    MonoidHom.ext fun _ => rfl
  have E₁ := NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ η₁A p ⟨w, hw'⟩
  have E₂ := NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ η₂A p ⟨w, hw'⟩
  have E₁₂ :=
    NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ (η₁A * η₂A) p ⟨w, hw'⟩
  rw [mul_comm μ] at E₁ E₂ E₁₂
  rw [Hm, MonoidHom.mul_comp (NumberField.TateGlobal.localChar η₁A p) (NumberField.TateGlobal.localChar η₂A p)]
    at E₁₂
  dsimp only at E₁ E₂ E₁₂

  have hfl := hfloor w hw
  rw [hw'] at hfl
  have hχ : HasConductorExponentAt K w (NumberField.TateGlobal.localChar μ w)
      (conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) := by
    have hne : {c | HasConductorExponentAt K w (NumberField.TateGlobal.localChar μ w) c}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : conductorExponentAt K w (NumberField.TateGlobal.localChar μ w) = 0 := by
        rw [LanglandsTunnell.TateLocal.conductorExponentAt, hemp, Nat.sInf_empty]
      omega
    exact Nat.sInf_mem hne
  obtain ⟨b₁', hθ₁, hb₁le⟩ :=
    exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul ℚ K p ⟨w, hw'⟩
      (NumberField.TateGlobal.localChar η₁A p) c₁ hc₁
  obtain ⟨b₂', hθ₂, hb₂le⟩ :=
    exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul ℚ K p ⟨w, hw'⟩
      (NumberField.TateGlobal.localChar η₂A p) c₂ hc₂
  dsimp only at hθ₁ hθ₂ hb₁le hb₂le
  have hm₁ : p.asIdeal.ramificationIdx' w.asIdeal * c₁ ≤ p.asIdeal.ramificationIdx' w.asIdeal * b :=
    Nat.mul_le_mul_left _ hc₁b
  have hm₂ : p.asIdeal.ramificationIdx' w.asIdeal * c₂ ≤ p.asIdeal.ramificationIdx' w.asIdeal * b :=
    Nat.mul_le_mul_left _ hc₂b
  have hu : ‖((NumberField.TateGlobal.localChar μ w (NumberField.AdelicLevel.uniformizerUnit K w) : ℂˣ) : ℂ)‖ = 1 := by
    rw [NumberField.TateGlobal.localChar_apply]; exact hμu _
  obtain ⟨hA1, hA2, hA12, hε⟩ := EpsDeepTwist.local_pair K w (NumberField.TateGlobal.localChar μ w) _ _
    (conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) b₁' b₂' hχ hθ₁ hθ₂ (by omega) (by omega) hu
    (by rw [MonoidHom.comp_apply, NumberField.TateGlobal.localChar_apply]; exact hη₁u _)
    (by rw [MonoidHom.comp_apply, NumberField.TateGlobal.localChar_apply]; exact hη₂u _)
  simp only [LanglandsTunnell.Converse.pinnedExp]
  rw [E₁, E₂, E₁₂, hA1, hA2, hA12]
  refine EpsDeepTwist.regroup _ _ _ _ _ _ _ _ _ ?_ hε
  simp only [MonoidHom.mul_apply, Units.val_mul]
  ring

end S_LanglandsTunnell_Converse_finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor
end P2MW
export P2MW.S_LanglandsTunnell_Converse_finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor (solution)

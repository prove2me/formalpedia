-- Prove2me | solution 1 for LanglandsTunnell.Converse.pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b4c55b20-f8af-5730-a6f4-2353c457c508

import Mathlib
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg M4aHerbrand.GenuineDescent

open IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace LTPinnedExpNormTwistStability

namespace Local

section Integers

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))

local notation "𝒪v" => HeightOneSpectrum.adicCompletionIntegers E v
local notation "𝒪w" => HeightOneSpectrum.adicCompletionIntegers M (Subtype.val w)
local notation "Ev" => HeightOneSpectrum.adicCompletion E v
local notation "Mw" => HeightOneSpectrum.adicCompletion M (Subtype.val w)

theorem algebraMap_integers_injective : Function.Injective (algebraMap 𝒪v 𝒪w) := by
  intro x y hxy
  apply Subtype.ext
  have := congrArg Subtype.val hxy
  rw [Extension.integer_algebraMap_apply, Extension.integer_algebraMap_apply] at this
  exact (w.adicCompletionSemialgHom E M).injective this

theorem isTorsionFree_integers : Module.IsTorsionFree 𝒪v 𝒪w :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_integers_injective E M v w)

theorem isScalarTower_integers : IsScalarTower 𝒪v 𝒪w Mw :=
  .of_algebraMap_smul fun _ _ ↦ rfl

attribute [local instance] isTorsionFree_integers isScalarTower_integers

theorem algebraMap_integers_adicCompletion_apply (x : 𝒪v) :
    algebraMap 𝒪v Mw x = w.adicCompletionSemialgHom E M x.1 := rfl

theorem valued_algebraMap_integers (x : 𝒪v) :
    Valued.v ((algebraMap 𝒪v 𝒪w x).1) = Valued.v x.1 ^ (w.1.under (𝓞 E)).asIdeal.ramificationIdx' w.1.asIdeal := by
  rw [Extension.integer_algebraMap_apply, Extension.valued_adicCompletionSemialgHom]

theorem isLocalization_integers :
    IsLocalization (Algebra.algebraMapSubmonoid 𝒪w (nonZeroDivisors 𝒪v)) Mw := by
  refine (IsLocalization.iff_of_le_of_exists_dvd
    (Algebra.algebraMapSubmonoid 𝒪w (nonZeroDivisors 𝒪v)) (nonZeroDivisors 𝒪w) ?_ ?_).mpr
    inferInstance
  · rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ha ?_
    exact (injective_iff_map_eq_zero _).mp (algebraMap_integers_injective E M v w) a h
  · intro b hb
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨π, hπ⟩ := adicCompletion.exists_uniformizer E v
    obtain ⟨ϖ, hϖ⟩ := adicCompletion.exists_uniformizer M w.1
    obtain ⟨m, u, hbu⟩ := adicCompletion.eq_pow_uniformizer_mul_unit M w.1 hb0 hϖ
    have hπ0 : π ≠ 0 := adicCompletion.uniformizer_ne_zero hπ
    refine ⟨algebraMap 𝒪v 𝒪w (π ^ m), ⟨π ^ m, pow_mem (mem_nonZeroDivisors_of_ne_zero hπ0) m,
      rfl⟩, ?_⟩
    apply Valuation.Integers.dvd_of_le (Valuation.valuationSubring.integers Valued.v)
    have he0 := ramificationIdx_ne_zero (𝓞 E) (𝓞 M)
      (algebraMap_injective_of_field_isFractionRing (𝓞 E) (𝓞 M) E M) w.1
    have h1 : Valued.v ((algebraMap 𝒪v 𝒪w (π ^ m)).1) =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^
          (m * ((w.1.under (𝓞 E)).asIdeal.ramificationIdx' w.1.asIdeal)) := by
      rw [Extension.integer_algebraMap_apply, Extension.valued_adicCompletionSemialgHom,
        SubmonoidClass.coe_pow, map_pow, hπ, ← pow_mul]
    have h2 : Valued.v b.1 =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m := by
      have hu : Valued.v (u : 𝒪w).1 = 1 :=
        (Valuation.valuationSubring.integers Valued.v).one_of_isUnit u.isUnit
      rw [hbu, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hϖ]
      rw [show ((u : 𝒪w) : Mw) = (u : 𝒪w).1 from rfl, hu, mul_one]
    show Valued.v ((algebraMap 𝒪v 𝒪w (π ^ m)).1) ≤ Valued.v b.1
    rw [h1, h2, pow_mul]
    conv_rhs => rw [← pow_one (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) ^ m)]
    refine pow_le_pow_right_of_le_one' (pow_le_one' (le_of_lt ?_) _)
      (Nat.one_le_iff_ne_zero.mpr he0)
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
    omega

theorem norm_coe (x : 𝒪w) :
    Algebra.norm Ev (x : Mw) = ((Algebra.norm 𝒪v x : 𝒪v) : Ev) := by
  haveI := isLocalization_integers E M v w
  exact Algebra.norm_localization (Rₘ := Ev) (Sₘ := Mw) 𝒪v (nonZeroDivisors 𝒪v) x

theorem exists_norm_one_add_smul_eq (r : 𝒪v) (y : 𝒪w) :
    ∃ z : 𝒪v, Algebra.norm 𝒪v (1 + r • y) = 1 + r * z := by
  classical
  let bs := Module.Free.chooseBasis 𝒪v 𝒪w
  refine ⟨Matrix.trace (Algebra.leftMulMatrix bs y) +
    (Matrix.det (1 + (Polynomial.X : Polynomial 𝒪v) • (Algebra.leftMulMatrix bs y).map Polynomial.C)).divX.divX.eval r
      * r, ?_⟩
  rw [Algebra.norm_eq_matrix_det bs, map_add, map_one, map_smul, Matrix.det_one_add_smul]
  ring

theorem valued_norm_eq_one {u : Mw} (hu : Valued.v u = 1) :
    Valued.v (Algebra.norm Ev u) = 1 := by
  have hu1 : u ∈ HeightOneSpectrum.adicCompletionIntegers M w.1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  set uO : 𝒪w := ⟨u, hu1⟩ with huO
  have hunit : IsUnit uO :=
    Valuation.Integers.isUnit_of_one (Valuation.valuationSubring.integers Valued.v)
      (isUnit_iff_ne_zero.mpr fun h => by
        have : u = 0 := by
          have := congrArg Subtype.val (show uO = 0 from Subtype.ext (by simpa using h))
          simpa [huO] using this
        rw [this, map_zero] at hu
        exact zero_ne_one hu)
      (by simpa [huO] using hu)
  have hN : IsUnit (Algebra.norm 𝒪v uO) := hunit.map _
  rw [show u = (uO : Mw) from rfl, norm_coe]
  exact (Valuation.valuationSubring.integers Valued.v).one_of_isUnit hN

theorem norm_mem_higherUnitsAt (n : ℕ) (u : (Mw)ˣ)
    (hu : u ∈ higherUnitsAt M w.1 ((w.1.under (𝓞 E)).asIdeal.ramificationIdx' w.1.asIdeal * n)) :
    Units.map (Algebra.norm Ev (S := Mw)) u ∈ higherUnitsAt E v n := by
  obtain ⟨hu1, hball⟩ := hu
  have hN1 : Valued.v (Algebra.norm Ev (u : Mw)) = 1 := valued_norm_eq_one E M v w hu1
  refine ⟨hN1, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact Or.inl hn
  right
  have he0 := ramificationIdx_ne_zero (𝓞 E) (𝓞 M)
    (algebraMap_injective_of_field_isFractionRing (𝓞 E) (𝓞 M) E M) w.1
  set e := (w.1.under (𝓞 E)).asIdeal.ramificationIdx' w.1.asIdeal with he
  have hen : e * n ≠ 0 := Nat.mul_ne_zero he0 (by omega)
  have hx : Valued.v ((u : Mw) - 1) ≤ WithZero.exp (-((e * n : ℕ) : ℤ)) := by
    rcases hball with h0 | h
    · exact absurd h0 hen
    · exact h

  obtain ⟨π, hπ⟩ := adicCompletion.exists_uniformizer E v
  set r : 𝒪v := π ^ n with hr
  have hvr : Valued.v r.1 = WithZero.exp (-(n : ℤ)) := by
    rw [hr, SubmonoidClass.coe_pow, map_pow, hπ, ← WithZero.exp, ← WithZero.exp_nsmul]
    congr 1; simp
  have hvr' : Valued.v ((algebraMap 𝒪v 𝒪w r).1) = WithZero.exp (-((e * n : ℕ) : ℤ)) := by
    rw [valued_algebraMap_integers, hvr, ← WithZero.exp_nsmul, ← he]
    congr 1; push_cast; ring
  have hr0 : (algebraMap 𝒪v 𝒪w r).1 ≠ 0 := by
    intro h; rw [h, map_zero] at hvr'; exact WithZero.exp_ne_zero hvr'.symm

  set yF : Mw := ((u : Mw) - 1) / (algebraMap 𝒪v 𝒪w r).1 with hyF
  have hyint : yF ∈ HeightOneSpectrum.adicCompletionIntegers M w.1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hyF, map_div₀, hvr']
    rw [div_le_one₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)]
    exact hx
  set y : 𝒪w := ⟨yF, hyint⟩ with hy
  have hu_int : (u : Mw) ∈ HeightOneSpectrum.adicCompletionIntegers M w.1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu1]
  set uO : 𝒪w := ⟨(u : Mw), hu_int⟩ with huO
  have hdecomp : uO = 1 + r • y := by
    apply Subtype.ext
    rw [Algebra.smul_def]
    show (u : Mw) = 1 + (algebraMap 𝒪v 𝒪w r).1 * yF
    rw [hyF, mul_div_cancel₀ _ hr0, add_sub_cancel]
  obtain ⟨z, hz⟩ := exists_norm_one_add_smul_eq E M v w r y
  have hNu : Algebra.norm Ev (u : Mw) = 1 + (r.1 * z.1 : Ev) := by
    rw [show (u : Mw) = (uO : Mw) from rfl, norm_coe, hdecomp, hz]
    rfl
  show Valued.v ((Units.map (Algebra.norm Ev (S := Mw)) u : Ev) - 1) ≤ WithZero.exp (-(n : ℤ))
  rw [Units.coe_map, hNu, add_sub_cancel_left, map_mul, hvr]
  calc WithZero.exp (-(n : ℤ)) * Valued.v (z.1) ≤ WithZero.exp (-(n : ℤ)) * 1 :=
        mul_le_mul' le_rfl z.2
    _ = WithZero.exp (-(n : ℤ)) := mul_one _

end Integers

end Local

section Conductor

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem hasConductorExponentAt_mul_of_forall_mem_higherUnitsAt_of_lt
    {χ Θ : (v.adicCompletion K)ˣ →* ℂˣ} {a n : ℕ}
    (hχ : HasConductorExponentAt K v χ a) (hΘ : ∀ u ∈ higherUnitsAt K v n, Θ u = 1) (hna : n < a) :
    HasConductorExponentAt K v (χ * Θ) a := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  ·
    rw [MonoidHom.mul_apply, hχ.1 u hu, hΘ u (higherUnitsAt_antitone K v hna.le hu), one_mul]
  ·
    have hmax : max m n < a := max_lt hm hna
    obtain ⟨u, hu, hne⟩ := hχ.2 (max m n) hmax
    refine ⟨u, higherUnitsAt_antitone K v (le_max_left m n) hu, ?_⟩
    rwa [MonoidHom.mul_apply, hΘ u (higherUnitsAt_antitone K v (le_max_right m n) hu), mul_one]

theorem hasConductorExponentAt_conductorExponentAt_of_pos {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (h : 0 < conductorExponentAt K v χ) :
    HasConductorExponentAt K v χ (conductorExponentAt K v χ) := by
  have hne : {c | HasConductorExponentAt K v χ c}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have : conductorExponentAt K v χ = 0 := by
      rw [conductorExponentAt, hempty, Nat.sInf_empty]
    omega
  exact Nat.sInf_mem hne

theorem conductorExponentAt_mul_eq_of_forall_mem_higherUnitsAt_of_lt
    {χ Θ : (v.adicCompletion K)ˣ →* ℂˣ} {n : ℕ}
    (hΘ : ∀ u ∈ higherUnitsAt K v n, Θ u = 1) (hna : n < conductorExponentAt K v χ) :
    conductorExponentAt K v (χ * Θ) = conductorExponentAt K v χ :=
  conductorExponentAt_eq_of_hasConductorExponentAt K v
    (hasConductorExponentAt_mul_of_forall_mem_higherUnitsAt_of_lt K v
      (hasConductorExponentAt_conductorExponentAt_of_pos K v (by omega)) hΘ hna)

end Conductor

theorem ringHom_ratInt_ext {A : Type*} [NonAssocRing A] (f g : 𝓞 ℚ →+* A) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom =
      g.comp Rat.ringOfIntegersEquiv.symm.toRingHom := RingHom.ext_int _ _
  refine RingHom.ext fun r => ?_
  have h1 := congrArg (fun φ : ℤ →+* A => φ (Rat.ringOfIntegersEquiv r)) h
  change f (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)) =
    g (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)) at h1
  rwa [RingEquiv.symm_apply_apply] at h1

theorem algebra_ratInt_subsingleton {A : Type*} [Ring A] : Subsingleton (Algebra (𝓞 ℚ) A) :=
  ⟨fun P Q => Algebra.algebra_ext P Q fun r => by
    have := ringHom_ratInt_ext (@algebraMap (𝓞 ℚ) A _ _ P) (@algebraMap (𝓞 ℚ) A _ _ Q)
    exact congrArg (fun φ : 𝓞 ℚ →+* A => φ r) this⟩

section Main

theorem conductorExponentAt_localChar_comp_idelicNorm_mul_eq
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (μ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E)) (wE : v.Extension (𝓞 M)) (b : ℕ)
    (hfloor : 2 * (Ideal.ramificationIdx' (wE.1.under (𝓞 E)).asIdeal wE.1.asIdeal * b) + 1 ≤
      conductorExponentAt M wE.1 (localChar μ wE.1))
    (ηA : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (c : ℕ) (hc : HasConductorExponentAt E v (localChar ηA v) c)
    (hcb : c ≤ b) :
    conductorExponentAt M wE.1 (localChar (ηA.comp (genuineBaseChange E M).idelicNorm * μ) wE.1) =
      conductorExponentAt M wE.1 (localChar μ wE.1) := by
  set Nm : (wE.1.adicCompletion M)ˣ →* (v.adicCompletion E)ˣ :=
    Units.map (Algebra.norm (v.adicCompletion E) (S := wE.1.adicCompletion M)) with hNm
  set Θ : (wE.1.adicCompletion M)ˣ →* ℂˣ := (localChar ηA v).comp Nm with hΘ

  have hcomp : localChar (ηA.comp (genuineBaseChange E M).idelicNorm * μ) wE.1 = localChar μ wE.1 * Θ := by
    rw [mul_comm]
    exact NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange E M μ ηA v wE

  set e := (wE.1.under (𝓞 E)).asIdeal.ramificationIdx' wE.1.asIdeal with he
  have hΘU : ∀ u ∈ higherUnitsAt M wE.1 (e * b), Θ u = 1 := fun u hu => by
    rw [hΘ, MonoidHom.comp_apply]
    exact hc.1 _ (higherUnitsAt_antitone E v hcb (Local.norm_mem_higherUnitsAt E M v wE b u hu))

  have hlt : e * b < conductorExponentAt M wE.1 (localChar μ wE.1) := by
    have h2 : 2 * (e * b) + 1 ≤ conductorExponentAt M wE.1 (localChar μ wE.1) := hfloor
    omega
  rw [hcomp]
  exact conductorExponentAt_mul_eq_of_forall_mem_higherUnitsAt_of_lt M wE.1 hΘU hlt

end Main

end LTPinnedExpNormTwistStability

open LTPinnedExpNormTwistStability in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (b : ℕ)
    (hfloor : ∀ w ∈ primeFibre ℚ K p,
      2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w))
    (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (c : ℕ)
    (hc : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ηA p) c)
    (hcb : c ≤ b) :
    ∀ w ∈ primeFibre ℚ K p,
      LanglandsTunnell.Converse.pinnedExp K
          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w =
        LanglandsTunnell.Converse.pinnedExp K μ w := by
  intro w hw
  have hfw := hfloor w hw

  haveI := algebra_ratInt_subsingleton (A := 𝓞 K)
  have hinst : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  subst hinst
  have hp : p = w.under (𝓞 ℚ) := ((mem_primeFibre (F := ℚ) p w).mp hw).symm
  subst hp
  unfold LanglandsTunnell.Converse.pinnedExp
  congr 2
  exact conductorExponentAt_localChar_comp_idelicNorm_mul_eq ℚ K μ (w.under (𝓞 ℚ)) ⟨w, rfl⟩ b hfw ηA c hc hcb

end S_LanglandsTunnell_Converse_pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor
end P2MW
export P2MW.S_LanglandsTunnell_Converse_pinnedExp_comp_idelicNorm_mul_eq_pinnedExp_of_hasConductorExponentAt_le_of_depth_floor (solution)

-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a155d095-b315-5f59-8b24-12fe7ffb3ca9

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt_apply_ne

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

noncomputable section

namespace LocalUnitCharacter

open LanglandsTunnell.TateLocal NumberField.AdelicLevel

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def higherUnitSubgroup (n : ℕ) : Subgroup (v.adicCompletion K)ˣ where
  carrier := higherUnitsAt K v n
  one_mem' := ⟨by simp, Or.inr (by simp)⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨by rw [Units.val_mul, map_mul, ha1, hb1, one_mul], ?_⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · right
      have ha2' : Valued.v ((a : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
        rcases ha2 with h | h
        · omega
        · exact h
      have hb2' : Valued.v ((b : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
        rcases hb2 with h | h
        · omega
        · exact h
      have hsplit : ((a * b : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
          (a : v.adicCompletion K) * ((b : v.adicCompletion K) - 1) + ((a : v.adicCompletion K) - 1) := by
        rw [Units.val_mul]; ring
      rw [hsplit]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ha2')
      rw [map_mul, ha1, one_mul]
      exact hb2'
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hinv : Valued.v ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ha1, inv_one]
    refine ⟨hinv, ?_⟩
    rcases ha2 with h | h
    · exact Or.inl h
    · right
      have hsplit : ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
          ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * (1 - (a : v.adicCompletion K)) := by
        rw [mul_sub, mul_one, Units.inv_mul]
      rw [hsplit, map_mul, hinv, one_mul, Valuation.map_sub_swap]
      exact h

private theorem mem_higherUnitSubgroup_iff {n : ℕ} {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitSubgroup K v n ↔ u ∈ higherUnitsAt K v n :=
  Iff.rfl

private def lg (x : (v.adicCompletion K)ˣ) : ℤ :=
  WithZero.log (Valued.v (x : v.adicCompletion K))

private theorem v_ne_zero (x : (v.adicCompletion K)ˣ) : Valued.v (x : v.adicCompletion K) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr x.ne_zero

private theorem exp_lg (x : (v.adicCompletion K)ˣ) :
    WithZero.exp (lg K v x) = Valued.v (x : v.adicCompletion K) :=
  WithZero.exp_log (v_ne_zero K v x)

private theorem lg_mul (x y : (v.adicCompletion K)ˣ) : lg K v (x * y) = lg K v x + lg K v y := by
  unfold lg
  rw [Units.val_mul, map_mul, WithZero.log_mul (v_ne_zero K v x) (v_ne_zero K v y)]

private theorem lg_eq_zero_of_v_eq_one {x : (v.adicCompletion K)ˣ}
    (hx : Valued.v (x : v.adicCompletion K) = 1) : lg K v x = 0 := by
  unfold lg
  rw [hx, WithZero.log_one]

variable (ϖ : (v.adicCompletion K)ˣ)

private def unitPart : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ where
  toFun x := x * ϖ ^ (lg K v x)
  map_one' := by
    rw [lg_eq_zero_of_v_eq_one K v (by simp), zpow_zero, one_mul]
  map_mul' x y := by
    rw [lg_mul, zpow_add]
    simp only [mul_assoc, mul_left_comm y]

private theorem unitPart_apply (x : (v.adicCompletion K)ˣ) : unitPart K v ϖ x = x * ϖ ^ (lg K v x) := rfl

variable {ϖ}

private theorem v_unitPart (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (x : (v.adicCompletion K)ˣ) : Valued.v ((unitPart K v ϖ x : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = 1 := by
  rw [unitPart_apply, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ,
    ← WithZero.exp_zsmul, ← exp_lg K v x, ← WithZero.exp_add, smul_neg, smul_eq_mul, mul_one,
    add_neg_cancel, WithZero.exp_zero]

private theorem unitPart_of_v_eq_one {x : (v.adicCompletion K)ˣ} (hx : Valued.v (x : v.adicCompletion K) = 1) :
    unitPart K v ϖ x = x := by
  rw [unitPart_apply, lg_eq_zero_of_v_eq_one K v hx, zpow_zero, mul_one]

private theorem unitPart_self (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    unitPart K v ϖ ϖ = 1 := by
  have hlg : lg K v ϖ = -1 := by
    unfold lg; rw [hϖ, WithZero.log_exp]
  rw [unitPart_apply, hlg, zpow_neg, zpow_one, mul_inv_cancel]

private theorem higherUnitsAt_mem_nhds_one (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    higherUnitsAt K v n ∈ nhds (1 : (v.adicCompletion K)ˣ) := by
  have hϖn : Valued.v ((ϖ : v.adicCompletion K) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hϖ, ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul, mul_one]
  let S : Set (v.adicCompletion K) :=
    {y | Valued.v y = 1 ∧ (n = 0 ∨ Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ)))}
  have h1 : IsOpen {y : v.adicCompletion K | Valued.v y = 1} := by
    have : {y : v.adicCompletion K | Valued.v y = 1} = {y | Valued.v.restrict y = 1} := by
      ext y
      exact (Valuation.restrict_eq_one_iff _).symm
    rw [this]
    exact Valued.isOpen_sphere (v.adicCompletion K) (r := 1) one_ne_zero
  have h2 : IsOpen {y : v.adicCompletion K | Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ))} := by
    have hr : Valued.v.restrict ((ϖ : v.adicCompletion K) ^ n) ≠ 0 := by
      rw [Ne, Valuation.restrict_eq_zero_iff, hϖn]
      exact WithZero.exp_ne_zero
    have : {y : v.adicCompletion K | Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ))} =
        (fun y => y - 1) ⁻¹'
          {x | Valued.v.restrict x ≤ Valued.v.restrict ((ϖ : v.adicCompletion K) ^ n)} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [Valuation.restrict_le_iff, hϖn]
    rw [this]
    exact (Valued.isOpen_closedBall (v.adicCompletion K) hr).preimage (continuous_id.sub continuous_const)
  have hS : IsOpen S := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have : S = {y : v.adicCompletion K | Valued.v y = 1} := by
        ext y
        simp [S, hn]
      rw [this]
      exact h1
    · have : S = {y : v.adicCompletion K | Valued.v y = 1} ∩
          {y | Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ))} := by
        ext y
        simp [S, hn.ne']
      rw [this]
      exact h1.inter h2
  have hpre : higherUnitsAt K v n = ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) ⁻¹' S := rfl
  rw [hpre]
  exact (hS.preimage Units.continuous_val).mem_nhds ⟨by simp, Or.inr (by simp)⟩

private def expUnit (q : ℚ) : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * q)) (Complex.exp_ne_zero _)

private theorem val_expUnit (q : ℚ) : (expUnit q : ℂ) = Complex.exp (2 * Real.pi * Complex.I * q) := rfl

private theorem expUnit_add (q r : ℚ) : expUnit (q + r) = expUnit q * expUnit r := by
  ext
  rw [Units.val_mul, val_expUnit, val_expUnit, val_expUnit, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem expUnit_intCast (n : ℤ) : expUnit n = 1 := by
  ext
  rw [val_expUnit, Units.val_one, Rat.cast_intCast,
    show (2 * Real.pi * Complex.I * (n : ℂ) : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

private theorem exists_int_of_expUnit_eq_one {q : ℚ} (h : expUnit q = 1) : ∃ n : ℤ, q = n := by
  have h' : Complex.exp (2 * Real.pi * Complex.I * q) = 1 := by
    rw [← val_expUnit, h, Units.val_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
  refine ⟨n, ?_⟩
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (q : ℂ) = n := by
    have : (q : ℂ) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I) := by
      rw [← hn]; ring
    exact mul_right_cancel₀ hπ this
  exact_mod_cast h2

private def expChar : ℚ →+ Additive ℂˣ where
  toFun q := Additive.ofMul (expUnit q)
  map_zero' := by
    have : expUnit 0 = 1 := by simpa using expUnit_intCast 0
    simp [this]
  map_add' q r := by simp [expUnit_add]

private theorem expChar_apply (q : ℚ) : expChar q = Additive.ofMul (expUnit q) := rfl

private theorem zmultiples_one_le_ker : AddSubgroup.zmultiples (1 : ℚ) ≤ expChar.ker := by
  intro x hx
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [AddMonoidHom.mem_ker, zsmul_one, expChar_apply, expUnit_intCast]
  rfl

private def circleChar : AddCircle (1 : ℚ) →+ Additive ℂˣ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ)) expChar zmultiples_one_le_ker

private theorem circleChar_injective : Function.Injective circleChar := by
  refine (injective_iff_map_eq_zero circleChar).mpr ?_
  intro a
  induction a using QuotientAddGroup.induction_on with
  | H q =>
    intro h
    have h1 : expChar q = 0 := by
      simpa [circleChar] using h
    have h2 : expUnit q = 1 := by
      simpa [expChar_apply] using h1
    obtain ⟨n, rfl⟩ := exists_int_of_expUnit_eq_one h2
    exact (QuotientAddGroup.eq_zero_iff (n : ℚ)).mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp⟩)

private theorem exists_continuous_apply_eq_one_apply_ne_one
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (u₀ : (v.adicCompletion K)ˣ) (hu₀ : Valued.v (u₀ : v.adicCompletion K) = 1)
    (hn : u₀ ∉ higherUnitsAt K v n) :
    ∃ ψ : (v.adicCompletion K)ˣ →* ℂˣ, Continuous ψ ∧ ψ ϖ = 1 ∧
      (∀ w ∈ higherUnitsAt K v n, ψ w = 1) ∧ ψ u₀ ≠ 1 := by
  classical
  let H : Subgroup (v.adicCompletion K)ˣ := (higherUnitSubgroup K v n).comap (unitPart K v ϖ)
  have hmemH : ∀ x : (v.adicCompletion K)ˣ, x ∈ H ↔ unitPart K v ϖ x ∈ higherUnitsAt K v n :=
    fun x => Iff.rfl
  have hU : ∀ w ∈ higherUnitsAt K v n, w ∈ H := by
    intro w hw
    rw [hmemH, unitPart_of_v_eq_one K v hw.1]
    exact hw
  have hϖH : ϖ ∈ H := by
    rw [hmemH, unitPart_self K v hϖ]
    exact (higherUnitSubgroup K v n).one_mem
  have hu₀H : u₀ ∉ H := by
    rw [hmemH, unitPart_of_v_eq_one K v hu₀]
    exact hn

  let A := (v.adicCompletion K)ˣ ⧸ H
  have ha : (QuotientGroup.mk u₀ : A) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have ha' : Additive.ofMul (QuotientGroup.mk u₀ : A) ≠ 0 := by
    simpa using ha
  obtain ⟨c, hc⟩ :=
    CharacterModule.exists_character_apply_ne_zero_of_ne_zero (A := Additive A) ha'

  let f : (v.adicCompletion K)ˣ → ℂˣ := fun x =>
    Additive.toMul (circleChar (c (Additive.ofMul (QuotientGroup.mk x : A))))
  have hf1 : f 1 = 1 := by
    simp [f]
  have hfmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    simp [f]
  let ψ : (v.adicCompletion K)ˣ →* ℂˣ := { toFun := f, map_one' := hf1, map_mul' := hfmul }
  have hψH : ∀ x ∈ H, ψ x = 1 := by
    intro x hx
    have : (QuotientGroup.mk x : A) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show f x = 1
    simp [f, this]
  refine ⟨ψ, ?_, hψH ϖ hϖH, fun w hw => hψH w (hU w hw), ?_⟩
  ·
    refine continuous_of_continuousAt_one ψ ?_
    have hev : (fun _ => (1 : ℂˣ)) =ᶠ[nhds (1 : (v.adicCompletion K)ˣ)] ψ :=
      Filter.eventuallyEq_of_mem (higherUnitsAt_mem_nhds_one K v hϖ n)
        (fun x hx => (hψH x (hU x hx)).symm)
    have h1 : ContinuousAt (fun _ : (v.adicCompletion K)ˣ => (1 : ℂˣ)) 1 := continuousAt_const
    have := h1.congr hev
    rwa [ContinuousAt, map_one] at this ⊢
  · intro h
    apply hc
    apply circleChar_injective
    rw [map_zero]
    have h' : Additive.toMul (circleChar (c (Additive.ofMul (QuotientGroup.mk u₀ : A)))) = 1 := h
    exact Additive.toMul.injective (h'.trans (by simp))

private theorem exists_not_mem_higherUnitsAt (u₀ : (v.adicCompletion K)ˣ) (h1 : u₀ ≠ 1) :
    ∃ m, u₀ ∉ higherUnitsAt K v m := by
  have hne : (u₀ : v.adicCompletion K) - 1 ≠ 0 := by
    intro h
    apply h1
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.mp h
  have hv : Valued.v ((u₀ : v.adicCompletion K) - 1) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  set k := WithZero.log (Valued.v ((u₀ : v.adicCompletion K) - 1)) with hk
  refine ⟨(-k).toNat + 1, ?_⟩
  rintro ⟨-, hball⟩
  rcases hball with h | h
  · omega
  · rw [← WithZero.exp_log hv, ← hk, WithZero.exp_le_exp] at h
    omega

private theorem exists_hasExact_apply_ne (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (hdeep : ∀ c, 2 ≤ c → ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ ϖ = 1 ∧ HasConductorExponentAt K v χ c)
    (u₀ : (v.adicCompletion K)ˣ) (hu₀ : Valued.v (u₀ : v.adicCompletion K) = 1) (h1 : u₀ ≠ 1)
    (z : ℂˣ) (d : ℕ) :
    ∃ c : ℕ, d ≤ c ∧ 2 ≤ c ∧ ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ ϖ = 1 ∧ HasConductorExponentAt K v χ c ∧ χ u₀ ≠ z := by
  obtain ⟨m, hm⟩ := exists_not_mem_higherUnitsAt K v u₀ h1
  have hU := higherUnitsAt_antitone K v
  set c := max (max m d) 2 + 1 with hc
  have hcm : m ≤ c - 1 := by omega
  have hu₀' : u₀ ∉ higherUnitsAt K v (c - 1) := fun h => hm (hU hcm h)
  obtain ⟨χ₁, hcont₁, hϖ₁, hex₁⟩ := hdeep c (by omega)
  by_cases hz : χ₁ u₀ = z
  · obtain ⟨ψ, hψc, hψϖ, hψtriv, hψu⟩ :=
      exists_continuous_apply_eq_one_apply_ne_one K v hϖ (c - 1) u₀ hu₀ hu₀'
    refine ⟨c, by omega, by omega, χ₁ * ψ, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · change Continuous fun x => χ₁ x * ψ x
      exact hcont₁.mul hψc
    · simp [hϖ₁, hψϖ]
    · intro u hu
      have hA : χ₁ u = 1 := hex₁.1 u hu
      have hB : ψ u = 1 := hψtriv u (hU (Nat.sub_le c 1) hu)
      simp [hA, hB]
    · intro n hn
      obtain ⟨u, hu, hne⟩ := hex₁.2 (c - 1) (by omega)
      refine ⟨u, hU (by omega) hu, ?_⟩
      have hB : ψ u = 1 := hψtriv u hu
      simpa [hB] using hne
    · have : (χ₁ * ψ) u₀ = z * ψ u₀ := by simp [hz]
      rw [this]
      intro h
      apply hψu
      simpa using congrArg (fun t => z⁻¹ * t) h
  · exact ⟨c, by omega, by omega, χ₁, hcont₁, hϖ₁, hex₁, hz⟩

end LocalUnitCharacter

open LanglandsTunnell.TateLocal in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (u₀ : (v.adicCompletion K)ˣ) (hu : Valued.v (u₀ : v.adicCompletion K) = 1) (hu₀ : u₀ ≠ 1)
    (z : ℂˣ) (d : ℕ) :
    ∃ c : ℕ, d ≤ c ∧ 2 ≤ c ∧ ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ (uniformizerUnit K v) = 1 ∧ HasConductorExponentAt K v χ c ∧ χ u₀ ≠ z :=
  LocalUnitCharacter.exists_hasExact_apply_ne K v (valued_uniformizerUnit K v)
    (fun c hc => LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt K v c hc) u₀ hu hu₀ z d

end

end S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt_apply_ne
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt_apply_ne (solution)

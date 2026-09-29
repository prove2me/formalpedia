-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/42f60cc9-85a3-5a73-b559-7d8e0db4a77e

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

open LanglandsTunnell.TateLocal LanglandsTunnell in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : ℕ) (hc : 2 ≤ c) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ (uniformizerUnit K v) = 1 ∧ HasConductorExponentAt K v χ c := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, c = k + 2 := ⟨c - 2, by omega⟩
  have hk2 : k + 2 ≠ 0 := by omega

  have hexists : ∀ n : ℕ, ∃ r : v.adicCompletion K, Valued.v r = WithZero.exp (-(n : ℤ)) :=
    fun n => ⟨(uniformizerUnit K v : v.adicCompletion K) ^ n, by
      rw [map_pow, valued_uniformizerUnit, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]⟩
  have hexp_lt_one : ∀ n : ℕ, 0 < n → WithZero.exp (-(n : ℤ)) < 1 := by
    intro n hn
    have h := WithZero.exp_lt_exp.mpr (show -(n : ℤ) < 0 by omega)
    rwa [WithZero.exp_zero] at h
  obtain ⟨t, ht⟩ := hexists (k + 1)
  obtain ⟨s, hs⟩ := hexists (k + 2)
  have ht1 : Valued.v t < 1 := by rw [ht]; exact hexp_lt_one _ (by omega)
  have hs1 : Valued.v s < 1 := by rw [hs]; exact hexp_lt_one _ (by omega)
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hs
    exact WithZero.exp_ne_zero hs.symm

  have hne : (1 : v.adicCompletion K) + t ≠ 0 := by
    intro h0
    have h1 : Valued.v ((1 : v.adicCompletion K) + t) = 1 := Valued.v.map_one_add_of_lt ht1
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : (v.adicCompletion K)ˣ, (u₀ : v.adicCompletion K) = 1 + t :=
    ⟨Units.mk0 _ hne, rfl⟩
  have hu₀val : Valued.v (u₀ : v.adicCompletion K) = 1 := by
    rw [hu₀]
    exact Valued.v.map_one_add_of_lt ht1
  have hu₀sub : Valued.v ((u₀ : v.adicCompletion K) - 1) = WithZero.exp (-((k + 1 : ℕ) : ℤ)) := by
    rw [hu₀, show (1 : v.adicCompletion K) + t - 1 = t by ring, ht]
  have hu₀mem : ∀ m : ℕ, m ≤ k + 1 → u₀ ∈ higherUnitsAt K v m := by
    intro m hm
    refine ⟨hu₀val, Or.inr ?_⟩
    rw [hu₀sub]
    exact WithZero.exp_le_exp.mpr (by omega)

  let Hc : Subgroup (v.adicCompletion K)ˣ :=
    { carrier := higherUnitsAt K v (k + 2)
      one_mem' := one_mem_higherUnitsAt K v (k + 2)
      mul_mem' := by
        intro a b ha hb
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨hb1, hb2⟩ := hb
        have ha2' := ha2.resolve_left hk2
        have hb2' := hb2.resolve_left hk2
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
        have ha2' := ha2.resolve_left hk2
        have hinv : Valued.v ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀, ha1, inv_one]
        refine ⟨hinv, Or.inr ?_⟩
        have heq : ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1
            = ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)
              * (1 - (a : v.adicCompletion K)) := by
          rw [mul_sub, mul_one, Units.inv_mul]
        rw [heq, map_mul, hinv, one_mul, Valuation.map_sub_swap]
        exact ha2' }

  have hu₀H : u₀ ∉ Hc ⊔ Subgroup.zpowers (uniformizerUnit K v) := by
    intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hy' : y ∈ higherUnitsAt K v (k + 2) := hy
    obtain ⟨hy1, hy2⟩ := hy'
    have hj : j = 0 := by
      have h := congrArg (fun w : (v.adicCompletion K)ˣ => Valued.v (w : v.adicCompletion K)) hyz
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hy1, one_mul,
        valued_uniformizerUnit, hu₀val] at h
      rw [← WithZero.exp_zsmul, WithZero.exp_eq_one] at h
      simpa using h
    subst hj
    rw [zpow_zero, mul_one] at hyz
    rw [hyz] at hy2
    have hb := hy2.resolve_left hk2
    rw [hu₀sub] at hb
    have hle := WithZero.exp_le_exp.mp hb
    omega
  obtain ⟨H, hHc, hHϖ, hHu₀⟩ : ∃ H : Subgroup (v.adicCompletion K)ˣ,
      (∀ x, x ∈ higherUnitsAt K v (k + 2) → x ∈ H) ∧ uniformizerUnit K v ∈ H ∧ u₀ ∉ H :=
    ⟨Hc ⊔ Subgroup.zpowers (uniformizerUnit K v),
      fun x hx => Subgroup.mem_sup_left (show x ∈ Hc from hx),
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _), hu₀H⟩

  have hg : Additive.ofMul (u₀ : (v.adicCompletion K)ˣ ⧸ H) ≠ 0 := by
    intro h0
    exact hHu₀ ((QuotientGroup.eq_one_iff u₀).mp (ofMul_eq_zero.mp h0))
  obtain ⟨f, hf⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero
    (A := Additive ((v.adicCompletion K)ˣ ⧸ H)) hg
  let fA : Additive ((v.adicCompletion K)ˣ ⧸ H) →+ AddCircle (1 : ℚ) := f
  have hfA : fA (Additive.ofMul (u₀ : (v.adicCompletion K)ˣ ⧸ H)) ≠ 0 := hf

  obtain ⟨φ, hφ⟩ : ∃ φ : ℚ →+ Additive ℂˣ, ∀ q : ℚ, Additive.toMul (φ q)
      = Units.mk0 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (q : ℂ))) (Complex.exp_ne_zero _) :=
    ⟨{ toFun := fun q => Additive.ofMul
          (Units.mk0 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (q : ℂ)))
            (Complex.exp_ne_zero _))
       map_zero' := by
         show Additive.ofMul _ = 0
         rw [ofMul_eq_zero]
         ext
         simp
       map_add' := fun a b => by
         show Additive.ofMul _ = Additive.ofMul _ + Additive.ofMul _
         rw [← ofMul_mul]
         congr 1
         ext
         simp [mul_add, Complex.exp_add] }, fun q => rfl⟩
  have hker : AddSubgroup.zmultiples (1 : ℚ) ≤ φ.ker := by
    intro x hx
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [AddMonoidHom.mem_ker, ← toMul_eq_one, hφ]
    ext
    simp only [Units.val_mk0, Units.val_one, zsmul_one, Rat.cast_intCast]
    exact Complex.exp_eq_one_iff.mpr ⟨n, by ring⟩
  obtain ⟨e, he_mk⟩ : ∃ e : AddCircle (1 : ℚ) →+ Additive ℂˣ,
      ∀ q : ℚ, e (q : AddCircle (1 : ℚ)) = φ q :=
    ⟨QuotientAddGroup.lift _ φ hker, fun q => QuotientAddGroup.lift_mk _ hker q⟩
  have he : ∀ y : AddCircle (1 : ℚ), e y = 0 → y = 0 := by
    intro y
    refine QuotientAddGroup.induction_on y fun q hq => ?_
    rw [he_mk] at hq
    have h1 : Additive.toMul (φ q) = 1 := toMul_eq_one.mpr hq
    rw [hφ] at h1
    have h2 := congrArg Units.val h1
    simp only [Units.val_mk0, Units.val_one] at h2
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
      rw [hn]
      ring
    have h4 : (q : ℂ) = (n : ℂ) := mul_left_cancel₀ Complex.two_pi_I_ne_zero h3
    have h5 : q = n := by exact_mod_cast h4
    exact (AddCircle.coe_eq_zero_iff _).mpr ⟨n, by rw [zsmul_one, h5]⟩

  let χ : (v.adicCompletion K)ˣ →* ℂˣ :=
    { toFun := fun x => Additive.toMul (e (fA (Additive.ofMul (x : (v.adicCompletion K)ˣ ⧸ H))))
      map_one' := by simp only [QuotientGroup.mk_one, ofMul_one, map_zero, toMul_zero]
      map_mul' := fun a b => by simp only [QuotientGroup.mk_mul, ofMul_mul, map_add, toMul_add] }
  have hχ_of_mem : ∀ x : (v.adicCompletion K)ˣ, x ∈ H → χ x = 1 := by
    intro x hx
    show Additive.toMul (e (fA (Additive.ofMul (x : (v.adicCompletion K)ˣ ⧸ H)))) = 1
    simp only [(QuotientGroup.eq_one_iff x).mpr hx, ofMul_one, map_zero, toMul_zero]
  have hχu₀ : χ u₀ ≠ 1 := by
    intro h0
    have h1 : Additive.toMul (e (fA (Additive.ofMul (u₀ : (v.adicCompletion K)ˣ ⧸ H)))) = 1 := h0
    rw [toMul_eq_one] at h1
    exact hfA (he _ h1)

  have hW : IsOpen
      {x : (v.adicCompletion K)ˣ | Valued.v ((x : v.adicCompletion K) - 1) ≤ Valued.v s} := by
    have hf : Continuous fun y : v.adicCompletion K => y - 1 := continuous_id.sub continuous_const
    have h1 : IsOpen {y : v.adicCompletion K | Valued.v (y - 1) ≤ Valued.v s} :=
      hf.isOpen_preimage _ (isOpen_setOf_valued_le v s hs0)
    exact Units.continuous_val.isOpen_preimage _ h1
  have h1W : (1 : (v.adicCompletion K)ˣ)
      ∈ {x : (v.adicCompletion K)ˣ | Valued.v ((x : v.adicCompletion K) - 1) ≤ Valued.v s} := by
    show Valued.v (((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) ≤ Valued.v s
    rw [Units.val_one, sub_self, map_zero]
    exact zero_le
  have hχW :
      ∀ x ∈ {x : (v.adicCompletion K)ˣ | Valued.v ((x : v.adicCompletion K) - 1) ≤ Valued.v s},
        χ x = 1 := by
    intro x hx
    have hx' : Valued.v ((x : v.adicCompletion K) - 1) ≤ Valued.v s := hx
    refine hχ_of_mem x (hHc x ⟨?_, Or.inr ?_⟩)
    · have hlt : Valued.v ((x : v.adicCompletion K) - 1) < 1 := lt_of_le_of_lt hx' hs1
      have h2 := Valued.v.map_one_add_of_lt hlt
      rwa [show (1 : v.adicCompletion K) + ((x : v.adicCompletion K) - 1) = x by ring] at h2
    · rw [hs] at hx'
      exact hx'
  have hχcont : Continuous χ :=
    continuous_of_tendsto_nhds_one χ
      (Filter.Tendsto.congr'
        (Filter.eventuallyEq_of_mem (hW.mem_nhds h1W) fun x hx => (hχW x hx).symm)
        (tendsto_const_nhds : Filter.Tendsto (fun _ : (v.adicCompletion K)ˣ => (1 : ℂˣ)) (nhds 1) (nhds 1)))
  refine ⟨χ, hχcont, hχ_of_mem _ hHϖ, ?_⟩
  exact ⟨fun u hu => hχ_of_mem u (hHc u hu), fun m hm => ⟨u₀, hu₀mem m (by omega), hχu₀⟩⟩

end S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt (solution)

-- Prove2me | solution 1 for ModularForm.exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f473c9ed-4a80-5120-b91b-00e05db0ed75

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le
set_option autoImplicit false

set_option autoImplicit false

open Finset

namespace E34SM2

private def sPrimes (p : ℕ) : Finset ℕ :=
  {q ∈ range (p + 1) | q.Prime ∧ (q - 1) ∣ (p - 1)}

private def sDen (p : ℕ) : ℕ := ∏ q ∈ sPrimes p, q

private lemma mem_sPrimes {p q : ℕ} :
    q ∈ sPrimes p ↔ q < p + 1 ∧ q.Prime ∧ (q - 1) ∣ (p - 1) := by
  simp [sPrimes]

private lemma p_mem_sPrimes {p : ℕ} (hp : p.Prime) : p ∈ sPrimes p :=
  mem_sPrimes.mpr ⟨Nat.lt_succ_self p, hp, dvd_refl _⟩

private lemma two_mem_sPrimes {p : ℕ} (_hp : p.Prime) (hp5 : 5 ≤ p) : 2 ∈ sPrimes p :=
  mem_sPrimes.mpr ⟨by omega, Nat.prime_two, one_dvd _⟩

private lemma sDen_pos {p : ℕ} : 0 < sDen p :=
  Finset.prod_pos fun _ hq => (mem_sPrimes.mp hq).2.1.pos

private lemma p_dvd_sDen {p : ℕ} (hp : p.Prime) : p ∣ sDen p :=
  Finset.dvd_prod_of_mem _ (p_mem_sPrimes hp)

private lemma q_dvd_sDen {p q : ℕ} (hq : q ∈ sPrimes p) : q ∣ sDen p :=
  Finset.dvd_prod_of_mem _ hq

private lemma p_dvd_sDen_div {p q : ℕ} (hp : p.Prime) (hq : q ∈ sPrimes p) (hqp : q ≠ p) :
    p ∣ sDen p / q := by
  have h1 : p ∣ ∏ x ∈ (sPrimes p).erase q, x :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨fun h => hqp h.symm, p_mem_sPrimes hp⟩)
  have h2 : sDen p = q * ∏ x ∈ (sPrimes p).erase q, x :=
    (Finset.mul_prod_erase _ _ hq).symm
  rw [h2, Nat.mul_div_cancel_left _ (mem_sPrimes.mp hq).2.1.pos]
  exact h1

private lemma not_p_dvd_sDen_div_p {p : ℕ} (hp : p.Prime) : ¬ p ∣ sDen p / p := by
  have h2 : sDen p = p * ∏ x ∈ (sPrimes p).erase p, x :=
    (Finset.mul_prod_erase _ _ (p_mem_sPrimes hp)).symm
  rw [h2, Nat.mul_div_cancel_left _ hp.pos]
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hdvd
  have hqmem := Finset.mem_of_mem_erase hq
  have hqne : q ≠ p := Finset.ne_of_mem_erase hq
  have hqlt : q < p + 1 := (mem_sPrimes.mp hqmem).1
  have hqprime := (mem_sPrimes.mp hqmem).2.1
  have := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
  exact hqne this.symm

private lemma vsc_at (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    bernoulli (p - 1) + ∑ q ∈ sPrimes p, (1 : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ) := by
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 * k := by
    have := hp.odd_of_ne_two (by omega)
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by omega⟩
  have hset : sPrimes p = {q ∈ range (2 * k + 2) | q.Prime ∧ (q - 1) ∣ 2 * k} := by
    unfold sPrimes
    ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, h2, hk ▸ h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, h2, hk ▸ h3⟩
  rw [hset, hk]
  exact Bernoulli.vonStaudt_clausen k

private lemma exists_NZ (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ NZ : ℤ, (NZ : ℚ) = bernoulli (p - 1) * sDen p ∧ (NZ : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := vsc_at p hp hp5
  refine ⟨z * (sDen p : ℤ) - ∑ q ∈ sPrimes p, ((sDen p / q : ℕ) : ℤ), ?_, ?_⟩
  · have hsum : ((∑ q ∈ sPrimes p, ((sDen p / q : ℕ) : ℤ) : ℤ) : ℚ) =
        (∑ q ∈ sPrimes p, (1 : ℚ) / q) * (sDen p : ℚ) := by
      rw [Int.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Int.cast_natCast,
        Nat.cast_div (q_dvd_sDen hq)
          (Nat.cast_ne_zero.mpr (mem_sPrimes.mp hq).2.1.pos.ne')]
      ring
    have hB : bernoulli (p - 1) = (z : ℚ) - ∑ q ∈ sPrimes p, (1 : ℚ) / q := by
      linarith
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hsum, hB]
    ring
  · rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_sum]
    have hcast : ∀ q ∈ sPrimes p, (((sDen p / q : ℕ) : ℤ) : ZMod p) = ((sDen p / q : ℕ) : ZMod p) :=
      fun q _ => Int.cast_natCast _
    rw [Finset.sum_congr rfl hcast]
    have hD0 : ((sDen p : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr (p_dvd_sDen hp)
    have hterm : ∀ q ∈ sPrimes p, q ≠ p → ((sDen p / q : ℕ) : ZMod p) = 0 := fun q hq hqp =>
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr (p_dvd_sDen_div hp hq hqp)
    have hsump : (∑ q ∈ sPrimes p, ((sDen p / q : ℕ) : ZMod p)) =
        ((sDen p / p : ℕ) : ZMod p) := by
      rw [Finset.sum_eq_single_of_mem p (p_mem_sPrimes hp)]
      exact fun q hq hqp => hterm q hq hqp
    rw [hD0, mul_zero, zero_sub, neg_ne_zero, hsump, Ne,
      CharP.cast_eq_zero_iff (ZMod p) p _]
    exact not_p_dvd_sDen_div_p hp

section PartB

open UpperHalfPlane CongruenceSubgroup ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups

private lemma Gamma0_coe_le_SL (N : ℕ) :
    ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  show Subgroup.map (mapGL ℝ) (Gamma0 N) ≤ _
  rw [MonoidHom.range_eq_map]
  exact Subgroup.map_mono le_top

private noncomputable def restrictGamma0 {k : ℤ} (N : ℕ) (f : ModularForm 𝒮ℒ k) :
    ModularForm (Gamma0 N) k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (Gamma0_coe_le_SL N hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono (Gamma0_coe_le_SL N))

@[scoped simp] private lemma coe_restrictGamma0 {k : ℤ} (N : ℕ) (f : ModularForm 𝒮ℒ k) :
    ⇑(restrictGamma0 N f) = ⇑f := rfl

private theorem S_M2_hasse (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] :
    ∃ (A : ModularForm (CongruenceSubgroup.Gamma0 N') ((p : ℤ) - 1)) (b : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff A n = (b n : ℂ)) ∧ (p : ℤ) ∣ b 0 - 1 ∧
        ∀ n, 0 < n → (p : ℤ) ∣ b n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk3 : 3 ≤ p - 1 := by omega
  have heven : Even (p - 1) := Nat.Odd.sub_odd (hp.odd_of_ne_two (by omega)) odd_one
  obtain ⟨NZ, hNZ, hNZp⟩ := exists_NZ p hp hp5
  have hNZ0 : NZ ≠ 0 := fun h => hNZp (by simp [h])
  have hB0 : (bernoulli (p - 1) : ℚ) ≠ 0 := by
    intro h
    apply hNZ0
    have h2 := hNZ
    rw [h, zero_mul] at h2
    exact_mod_cast h2
  set m : ℕ := ((NZ : ZMod p)⁻¹).val with hm_def
  have hm1 : (((m : ℤ) * NZ : ℤ) : ZMod p) = 1 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact inv_mul_cancel₀ hNZp
  set c : ℤ := (m : ℤ) * NZ with hc_def
  set E1 : ModularForm (Gamma0 N') ((p : ℤ) - 1) :=
    ModularForm.mcast (by omega) (restrictGamma0 N' (ModularForm.E hk3)) with hE1_def
  have hE1coe : ⇑E1 = ⇑(ModularForm.E hk3) := rfl
  refine ⟨((c : ℤ) : ℂ) • E1,
    fun n => if n = 0 then c else
      (m : ℤ) * (-(2 * ((p : ℤ) - 1)) * (sDen p : ℤ)) * (ArithmeticFunction.sigma (p - 1 - 1) n : ℤ),
    ?_, ?_, ?_⟩
  · intro n
    have hanE := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk3)
      one_pos one_mem_strictPeriods_SL
    have hcoe : ⇑(((c : ℤ) : ℂ) • E1) = ((c : ℤ) : ℂ) • ⇑(ModularForm.E hk3) := by
      rw [ModularForm.IsGLPos.coe_smul, hE1coe]
    show (UpperHalfPlane.qExpansion 1 ⇑(((c : ℤ) : ℂ) • E1)).coeff n = _
    rw [hcoe, UpperHalfPlane.qExpansion_smul hanE, PowerSeries.coeff_smul]
    have hE := EisensteinSeries.E_qExpansion_coeff hk3 heven n
    rw [hE]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · simp only [if_neg hn.ne']
      have hNZC : (NZ : ℂ) = ((bernoulli (p - 1) : ℚ) : ℂ) * ((sDen p : ℕ) : ℂ) := by
        exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) hNZ
      have hBC : ((bernoulli (p - 1) : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hB0
      have hcC : ((c : ℤ) : ℂ) = (m : ℂ) * (((bernoulli (p - 1) : ℚ) : ℂ) * ((sDen p : ℕ) : ℂ)) := by
        rw [hc_def]
        push_cast
        rw [hNZC]
      rw [hcC]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      rw [smul_eq_mul]
      field_simp [hBC]
  · simp only [↓reduceIte]
    have : ((c - 1 : ℤ) : ZMod p) = 0 := by
      have hm1' : (m : ZMod p) * ((NZ : ℤ) : ZMod p) = 1 := by exact_mod_cast hm1
      push_cast [hc_def]
      rw [hm1']
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
  · intro n hn
    simp only [if_neg hn.ne']
    have hps : (p : ℤ) ∣ (sDen p : ℤ) := Int.natCast_dvd_natCast.mpr (p_dvd_sDen hp)
    exact ((hps.mul_left _).mul_left _).mul_right _

end PartB

end E34SM2
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le.E34SM2"

theorem solution (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] :
    ∃ (A : ModularForm (CongruenceSubgroup.Gamma0 N') ((p : ℤ) - 1)) (b : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff A n = (b n : ℂ)) ∧ (p : ℤ) ∣ b 0 - 1 ∧ ∀ n, 0 < n → (p : ℤ) ∣ b n:=
  E34SM2.S_M2_hasse p hp hp5 N'

end S_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le
end P2MW
export P2MW.S_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le (solution)

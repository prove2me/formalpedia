-- Prove2me | solution 1 for IntermediateField.apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7f25d436-1722-5759-8abf-39730450bacb

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic
set_option autoImplicit false

namespace AutoCont

section Discrete

variable (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]

theorem exists_norm_pow_eq_zpow (x : L) (hx : x ≠ 0) :
    ∃ k : ℤ, ‖(x : PadicAlgCl q)‖ ^ (Module.finrank ℚ_[q] L).factorial = (q : ℝ) ^ k := by
  have hint : IsIntegral ℚ_[q] x := Algebra.IsIntegral.isIntegral x
  set g := minpoly ℚ_[q] x with hg
  have hg' : minpoly ℚ_[q] (x : PadicAlgCl q) = g := minpoly.algebraMap_eq (algebraMap L (PadicAlgCl q)).injective x
  set d := g.natDegree with hd
  have hd0 : d ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hdle : d ≤ Module.finrank ℚ_[q] L := minpoly.natDegree_le x
  have hdvd : d ∣ (Module.finrank ℚ_[q] L).factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hd0) hdle
  obtain ⟨c, hc⟩ := hdvd
  have ha0 : g.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx

  have h1 : ‖(x : PadicAlgCl q)‖ ^ d = ‖g.coeff 0‖ := by
    have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[q]) (L := PadicAlgCl q) (x : PadicAlgCl q)
    rw [PadicAlgCl.spectralNorm_eq, hg'] at h
    rw [h, ← hd, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hd0]

  have h2 : ‖g.coeff 0‖ = (q : ℝ) ^ (-(g.coeff 0).valuation) := Padic.norm_eq_zpow_neg_valuation ha0
  refine ⟨-(g.coeff 0).valuation * c, ?_⟩
  rw [hc, pow_mul, h1, h2, ← zpow_natCast, ← zpow_mul]

theorem norm_eq_one_of_forall_exists_pow_eq (x : L) (hx : x ≠ 0)
    (h : ∀ k : ℕ, ∃ y : L, y ^ (q * k + 1) = x) : ‖(x : PadicAlgCl q)‖ = 1 := by
  have hqP : q.Prime := Fact.out
  set N := (Module.finrank ℚ_[q] L).factorial with hN
  have hN0 : N ≠ 0 := Nat.factorial_ne_zero _
  obtain ⟨a, ha⟩ := exists_norm_pow_eq_zpow q L x hx

  obtain ⟨y, hy⟩ := h a.natAbs
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hy; exact hx hy.symm
  obtain ⟨b, hb⟩ := exists_norm_pow_eq_zpow q L y hy0
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hqP.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have hxm : ‖(x : PadicAlgCl q)‖ = ‖(y : PadicAlgCl q)‖ ^ (q * a.natAbs + 1) := by
    rw [← hy]; push_cast; exact norm_pow _ _
  have key : (q : ℝ) ^ a = (q : ℝ) ^ (b * (q * a.natAbs + 1 : ℕ)) := by
    rw [← ha, hxm, pow_right_comm, hb, zpow_mul, zpow_natCast]
  have key' : a = b * (q * a.natAbs + 1 : ℕ) := zpow_right_injective₀ hq0 hq1.ne' key
  have ha0 : a = 0 := by
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, zero_mul] at key'; exact key'
    · exfalso
      have h3 : |a| = |b| * ((q : ℤ) * |a| + 1) := by
        conv_lhs => rw [key']
        rw [abs_mul]
        congr 1
        push_cast
        exact abs_of_nonneg (by positivity)
      have hb1 : 1 ≤ |b| := Int.one_le_abs hb0
      have h4 : 1 * ((q : ℤ) * |a| + 1) ≤ |b| * ((q : ℤ) * |a| + 1) :=
        mul_le_mul_of_nonneg_right hb1 (by positivity)
      have h5 : (|a| : ℤ) ≤ (q : ℤ) * |a| := le_mul_of_one_le_left (abs_nonneg a) (by exact_mod_cast hqP.one_lt.le)
      linarith
  rw [ha0, zpow_zero] at ha
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).mp ha

end Discrete

end AutoCont

namespace AutoCont

theorem padicInt_exists_pow_eq (q : ℕ) [Fact q.Prime] {m : ℕ} (hm : q.Coprime m)
    {a : ℤ_[q]} (ha : ‖a - 1‖ < 1) : ∃ z : ℤ_[q], z ^ m = a := by
  set P : Polynomial ℤ_[q] := Polynomial.X ^ m - Polynomial.C a with hP
  have hder : Polynomial.derivative P = Polynomial.C (m : ℤ_[q]) * Polynomial.X ^ (m - 1) := by
    rw [hP, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero]
  have heval : P.aeval (1 : ℤ_[q]) = -(a - 1) := by
    rw [hP, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, one_pow]
    simp
  have hevald : (Polynomial.derivative P).aeval (1 : ℤ_[q]) = (m : ℤ_[q]) := by
    rw [hder, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, one_pow, mul_one]
    simp
  have hnorm : ‖P.aeval (1 : ℤ_[q])‖ < ‖(Polynomial.derivative P).aeval (1 : ℤ_[q])‖ ^ 2 := by
    rw [heval, hevald, norm_neg, PadicInt.norm_natCast_eq_one_iff.mpr hm, one_pow]
    exact ha
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  rw [hP, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hz
  simpa using hz

theorem padicInt_norm_pow_sub_one_lt (q : ℕ) [Fact q.Prime] {u : ℤ_[q]} (hu : ‖u‖ = 1) :
    ‖u ^ (q - 1) - 1‖ < 1 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_one, sub_eq_zero]
  have hu' : IsUnit (PadicInt.toZMod u) := by
    apply IsUnit.map
    exact PadicInt.isUnit_iff.mpr hu
  exact ZMod.pow_card_sub_one_eq_one hu'.ne_zero

theorem norm_le_one_of_eval₂_eq_zero (q : ℕ) [Fact q.Prime] {R : Type*} [CommRing R] (θ : R →+* PadicAlgCl q)
    (G : Polynomial R) (hG : G.Monic) (hθ : ∀ i, ‖θ (G.coeff i)‖ ≤ 1) (y : PadicAlgCl q)
    (hy : Polynomial.eval₂ θ y G = 0) : ‖y‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hy
  have htop : ‖θ (G.coeff G.natDegree) * y ^ G.natDegree‖ = ‖y‖ ^ G.natDegree := by
    rw [Polynomial.Monic.coeff_natDegree hG, map_one, one_mul, norm_pow]
  rcases Nat.eq_zero_or_pos G.natDegree with h0 | hpos
  · rw [h0, Finset.sum_range_zero, zero_add] at hy
    have h1 : G.coeff 0 = 1 := by rw [← h0]; exact hG.coeff_natDegree
    rw [h1, map_one, pow_zero, mul_one] at hy
    exact one_ne_zero hy
  · have hlow : ‖(Finset.range G.natDegree).sum fun i => θ (G.coeff i) * y ^ i‖ ≤ ‖y‖ ^ (G.natDegree - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
      intro i hi
      rw [Finset.mem_range] at hi
      rw [norm_mul, norm_pow]
      calc ‖θ (G.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ i :=
            mul_le_mul_of_nonneg_right (hθ i) (pow_nonneg (norm_nonneg _) _)
        _ = ‖y‖ ^ i := one_mul _
        _ ≤ ‖y‖ ^ (G.natDegree - 1) := pow_le_pow_right₀ h.le (by omega)
    have hlt : ‖(Finset.range G.natDegree).sum fun i => θ (G.coeff i) * y ^ i‖ < ‖θ (G.coeff G.natDegree) * y ^ G.natDegree‖ := by
      rw [htop]
      exact hlow.trans_lt (pow_lt_pow_right₀ h (by omega))
    have hsum := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [hy, norm_zero, max_eq_right hlt.le, htop] at hsum
    exact pow_ne_zero _ (lt_trans zero_lt_one h).ne' hsum.symm

theorem exists_monic_eval₂_eq_zero_of_norm_le_one (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (z : L) (hz : ‖((z : L) : PadicAlgCl q)‖ ≤ 1) :
    ∃ G : Polynomial ℤ_[q], G.Monic ∧
      Polynomial.eval₂ ((algebraMap ℚ_[q] L).comp (algebraMap ℤ_[q] ℚ_[q])) z G = 0 := by
  have hint : IsIntegral ℚ_[q] z := Algebra.IsIntegral.isIntegral z
  set g := minpoly ℚ_[q] z with hg
  have hgmonic : g.Monic := minpoly.monic hint
  have hg' : minpoly ℚ_[q] ((z : L) : PadicAlgCl q) = g :=
    minpoly.algebraMap_eq (algebraMap L (PadicAlgCl q)).injective z
  have hcoeff : ∀ n, ‖g.coeff n‖ ≤ 1 := by
    have h1 : spectralValue g ≤ 1 := by
      rw [← hg']
      show spectralNorm ℚ_[q] (PadicAlgCl q) ((z : L) : PadicAlgCl q) ≤ 1
      rw [PadicAlgCl.spectralNorm_eq]
      exact hz
    exact (spectralValue_le_one_iff hgmonic).mp h1
  have hlifts : g ∈ Polynomial.lifts (algebraMap ℤ_[q] ℚ_[q]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨g.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨G, hGmap, -, hGmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hgmonic
  refine ⟨G, hGmonic, ?_⟩
  rw [← Polynomial.eval₂_map, hGmap, ← Polynomial.aeval_def]
  exact minpoly.aeval ℚ_[q] z

section Ball

variable (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] (Ψ : K →+* PadicAlgCl q)

noncomputable def normBall : ValuationSubring K where
  carrier := {y | ‖Ψ y‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at ha hb ⊢
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (PadicAlgCl.isNonarchimedean q _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [map_neg, norm_neg] using ha
  mem_or_inv_mem' y := by
    by_cases h : ‖Ψ y‖ ≤ 1
    · exact Or.inl h
    · refine Or.inr ?_
      rw [not_le] at h
      show ‖Ψ y⁻¹‖ ≤ 1
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ h.le

theorem mem_normBall_iff (y : K) : y ∈ normBall q Ψ ↔ ‖Ψ y‖ ≤ 1 := Iff.rfl

end Ball

open ExtCitation.LocalLevel in
theorem exists_norm_pow_sub_one_lt (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (y : L) (hy : ‖(y : PadicAlgCl q)‖ = 1) :
    ∃ M : ℕ, 0 < M ∧ ‖((y ^ M : L) : PadicAlgCl q) - 1‖ < 1 := by
  have hqP : q.Prime := Fact.out
  have hy1 : y ∈ Rw q L := by
    show ‖(y : PadicAlgCl q)‖₊ ≤ 1
    exact_mod_cast hy.le
  set yr : ↥(Rw q L) := ⟨y, hy1⟩ with hyr
  set Mf := (Module.finrank ℚ_[q] L).factorial with hMf
  have hres := residue_mem_kM q L yr
  rw [mem_kM_iff] at hres
  set a : OO q := algebraMap (Rw q L) (OO q) yr with ha
  have h2 : a ^ (q ^ Mf) - a ∈ IsLocalRing.maximalIdeal (OO q) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero]
    exact hres
  have h3 : ((a ^ (q ^ Mf) - a : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits :=
    (ValuationSubring.coe_mem_nonunits_iff).mpr h2
  rw [ValuationSubring.mem_nonunits_iff, ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one] at h3
  change Valued.v (((a ^ (q ^ Mf) - a : OO q) : PadicAlgCl q)) < 1 at h3
  rw [PadicAlgCl.valuation_def] at h3
  have h4 : ‖(((a ^ (q ^ Mf) - a : OO q) : PadicAlgCl q))‖ < 1 := by exact_mod_cast h3
  have hcoe : (((a ^ (q ^ Mf) - a : OO q) : PadicAlgCl q)) = (y : PadicAlgCl q) ^ (q ^ Mf) - (y : PadicAlgCl q) := by
    push_cast
    rfl
  rw [hcoe] at h4
  refine ⟨q ^ Mf - 1, ?_, ?_⟩
  · have : 1 < q ^ Mf := Nat.one_lt_pow (Nat.factorial_ne_zero _) hqP.one_lt
    omega
  · have hfac : (y : PadicAlgCl q) ^ (q ^ Mf) - (y : PadicAlgCl q) =
        (y : PadicAlgCl q) * ((y : PadicAlgCl q) ^ (q ^ Mf - 1) - 1) := by
      have : q ^ Mf = (q ^ Mf - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hqP.pos)).symm
      conv_lhs => rw [this, pow_succ']
      ring
    rw [hfac, norm_mul, hy, one_mul] at h4
    push_cast
    exact h4

end AutoCont

namespace AutoCont

section Theta

variable (q : ℕ) [Fact q.Prime] (L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q))
  [FiniteDimensional ℚ_[q] L₁] [FiniteDimensional ℚ_[q] L₂] (α : L₁ ≃+* L₂)

theorem norm_symm_unit_eq_one (u : ℤ_[q]) (hu : ‖u‖ = 1) :
    ‖((α.symm (algebraMap ℚ_[q] L₂ (algebraMap ℤ_[q] ℚ_[q] u)) : L₁) : PadicAlgCl q)‖ = 1 := by
  have hqP : q.Prime := Fact.out
  have hq1 : q - 1 ≠ 0 := by have := hqP.two_le; omega
  have hinj : Function.Injective (fun c : ℤ_[q] => α.symm (algebraMap ℚ_[q] L₂ (algebraMap ℤ_[q] ℚ_[q] c))) :=
    α.symm.injective.comp ((algebraMap ℚ_[q] L₂).injective.comp (IsFractionRing.injective ℤ_[q] ℚ_[q]))
  have hu0 : u ^ (q - 1) ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hu)
  have hx0 : α.symm (algebraMap ℚ_[q] L₂ (algebraMap ℤ_[q] ℚ_[q] (u ^ (q - 1)))) ≠ 0 := by
    intro h
    apply hu0
    apply hinj
    simpa using h
  have key := norm_eq_one_of_forall_exists_pow_eq q L₁ _ hx0 (fun k => by
    have hcop : q.Coprime (q * k + 1) := (Nat.coprime_mul_left_add_right q 1 k).mpr (Nat.coprime_one_right q)
    obtain ⟨zz, hzz⟩ := padicInt_exists_pow_eq q hcop (padicInt_norm_pow_sub_one_lt q hu)
    exact ⟨α.symm (algebraMap ℚ_[q] L₂ (algebraMap ℤ_[q] ℚ_[q] zz)), by rw [← map_pow, ← map_pow, ← map_pow, hzz]⟩)
  rw [map_pow, map_pow, map_pow] at key
  push_cast at key
  rw [norm_pow] at key
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq1).mp key

theorem norm_symm_le_one (c : ℤ_[q]) :
    ‖((α.symm (algebraMap ℚ_[q] L₂ (algebraMap ℤ_[q] ℚ_[q] c)) : L₁) : PadicAlgCl q)‖ ≤ 1 := by
  by_cases hc : ‖c‖ = 1
  · exact (norm_symm_unit_eq_one q L₁ L₂ α c hc).le
  · have hc1 : ‖c‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one c) hc
    have h1c : ‖1 + c‖ = 1 := by
      rw [PadicInt.norm_add_eq_max_of_ne (by rw [norm_one]; exact hc1.ne'), norm_one, max_eq_left hc1.le]
    have h := norm_symm_unit_eq_one q L₁ L₂ α (1 + c) h1c
    rw [map_add, map_add, map_add, map_one, map_one, map_one] at h
    push_cast at h
    set t : PadicAlgCl q := ((α.symm (algebraMap ℚ_[q] L₂ (algebraMap ℤ_[q] ℚ_[q] c)) : L₁) : PadicAlgCl q)
    have h2 : ‖(1 + t) - 1‖ ≤ max ‖1 + t‖ ‖(1 : PadicAlgCl q)‖ := by
      rw [sub_eq_add_neg]
      refine (PadicAlgCl.isNonarchimedean q _ _).trans ?_
      rw [norm_neg]
    rw [add_sub_cancel_left, h, norm_one, max_self] at h2
    exact h2

end Theta

end AutoCont

open AutoCont in

theorem solution
    (q : ℕ) [Fact q.Prime]
    (L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L₁] [FiniteDimensional ℚ_[q] L₂]
    (α : L₁ ≃+* L₂) :
    (∀ x : ℚ_[q], α (algebraMap ℚ_[q] L₁ x) = algebraMap ℚ_[q] L₂ x) ∧
    (∀ x : L₁, ‖((α x : L₂) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖) := by
  have hqP : q.Prime := Fact.out
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hqP.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have hnq : ‖((q : ℕ) : PadicAlgCl q)‖ = (q : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)) q]
    show ‖((q : ℚ_[q]) : PadicAlgCl q)‖ = (q : ℝ)⁻¹
    rw [PadicAlgCl.norm_extends, Padic.norm_p]
  have hcoe₁ : ∀ x : ℚ_[q], ((algebraMap ℚ_[q] L₁ x : L₁) : PadicAlgCl q) = (x : PadicAlgCl q) := fun x => rfl
  have hcoe₂ : ∀ x : ℚ_[q], ((algebraMap ℚ_[q] L₂ x : L₂) : PadicAlgCl q) = (x : PadicAlgCl q) := fun x => rfl

  let Ψ : L₁ →+* PadicAlgCl q := (algebraMap L₂ (PadicAlgCl q)).comp α.toRingHom
  have hΨ : ∀ y : L₁, ‖((α y : L₂) : PadicAlgCl q)‖ = ‖Ψ y‖ := fun _ => rfl
  let S : ValuationSubring L₁ := normBall q Ψ
  let ψ₂ : ℤ_[q] →+* L₂ := (algebraMap ℚ_[q] L₂).comp (algebraMap ℤ_[q] ℚ_[q])

  have hSO : ∀ y : L₁, ‖Ψ y‖ ≤ 1 → ‖(y : PadicAlgCl q)‖ ≤ 1 := by
    intro y hy
    obtain ⟨G, hGm, hG0⟩ := exists_monic_eval₂_eq_zero_of_norm_le_one q L₂ (α y) hy
    have h2 := Polynomial.hom_eval₂ G ψ₂ α.symm.toRingHom (α y)
    have h4 : (α.symm.toRingHom) (α y) = y := α.symm_apply_apply y
    rw [h4] at h2
    have h3 := Polynomial.hom_eval₂ G (α.symm.toRingHom.comp ψ₂) (algebraMap L₁ (PadicAlgCl q)) y
    have hroot : Polynomial.eval₂ ((algebraMap L₁ (PadicAlgCl q)).comp (α.symm.toRingHom.comp ψ₂))
        (algebraMap L₁ (PadicAlgCl q) y) G = 0 := by
      rw [← h3, ← h2]
      have h5 : Polynomial.eval₂ ψ₂ (α y) G = 0 := hG0
      rw [h5, map_zero, map_zero]
    exact norm_le_one_of_eval₂_eq_zero q ((algebraMap L₁ (PadicAlgCl q)).comp (α.symm.toRingHom.comp ψ₂)) G hGm
      (fun i => norm_symm_le_one q L₁ L₂ α (G.coeff i)) (algebraMap L₁ (PadicAlgCl q) y) hroot

  have hmS : ∀ x : L₁, ‖(x : PadicAlgCl q)‖ < 1 → ‖Ψ x‖ ≤ 1 := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, map_zero, norm_zero]; exact zero_le_one
    rcases S.mem_or_inv_mem x with h | h
    · exact h
    · exfalso
      have h1 : ‖((x⁻¹ : L₁) : PadicAlgCl q)‖ ≤ 1 := hSO x⁻¹ h
      push_cast at h1
      rw [norm_inv] at h1
      have hxne : (x : PadicAlgCl q) ≠ 0 := by exact_mod_cast hx0
      have hxpos : 0 < ‖(x : PadicAlgCl q)‖ := norm_pos_iff.mpr hxne
      have h2 : 1 < ‖(x : PadicAlgCl q)‖⁻¹ := (one_lt_inv₀ hxpos).mpr hx
      linarith

  have hUS : ∀ y : L₁, ‖(y : PadicAlgCl q)‖ = 1 → ‖Ψ y‖ ≤ 1 := by
    intro y hy
    obtain ⟨M, hM, hM1⟩ := exists_norm_pow_sub_one_lt q L₁ y hy
    have hyM : y ^ M ∈ S := by
      have h1 : y ^ M - 1 ∈ S := hmS _ (by push_cast at hM1 ⊢; exact hM1)
      have h2 := add_mem h1 (one_mem S)
      rwa [sub_add_cancel] at h2
    rcases S.mem_or_inv_mem y with h | h
    · exact h
    · have hy0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      have h2 : y = y ^ M * (y⁻¹) ^ (M - 1) := by
        rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hy0), ← pow_succ', Nat.sub_add_cancel hM]
      show y ∈ S
      rw [h2]
      exact mul_mem hyM (pow_mem h _)
  have hOS : ∀ y : L₁, ‖(y : PadicAlgCl q)‖ ≤ 1 → ‖Ψ y‖ ≤ 1 := fun y hy =>
    (lt_or_eq_of_le hy).elim (hmS y) (hUS y)

  have hone : ∀ y : L₁, ‖(y : PadicAlgCl q)‖ = 1 → ‖Ψ y‖ = 1 := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    apply le_antisymm (hOS y hy.le)
    have h1 : ‖Ψ y⁻¹‖ ≤ 1 := hOS y⁻¹ (by push_cast; rw [norm_inv, hy, inv_one])
    rw [map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖Ψ y‖ := norm_pos_iff.mpr ((map_ne_zero Ψ).mpr hy0)
    by_contra h'
    rw [not_le] at h'
    have h2 : 1 < ‖Ψ y‖⁻¹ := (one_lt_inv₀ hpos).mpr h'
    linarith

  have hiso : ∀ x : L₁, ‖((α x : L₂) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖ := by
    intro x
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]; simp
    set N₁ := (Module.finrank ℚ_[q] L₁).factorial with hN₁
    set N₂ := (Module.finrank ℚ_[q] L₂).factorial with hN₂
    have hN₁0 : N₁ ≠ 0 := Nat.factorial_ne_zero _
    have hN₂0 : N₂ ≠ 0 := Nat.factorial_ne_zero _
    obtain ⟨a, ha⟩ := exists_norm_pow_eq_zpow q L₁ x hx0
    obtain ⟨a', ha'⟩ := exists_norm_pow_eq_zpow q L₂ (α x) ((map_ne_zero α).mpr hx0)
    have hq0L : ((q : ℕ) : L₁) ≠ 0 := by exact_mod_cast hqP.ne_zero

    set w : L₁ := x ^ (N₁ * N₂) * ((q : ℕ) : L₁) ^ (a * N₂) with hw
    have hxN : ‖(x : PadicAlgCl q)‖ ^ (N₁ * N₂) = (q : ℝ) ^ (a * N₂) := by
      rw [pow_mul, ha, ← zpow_natCast, ← zpow_mul]
    have hqz : ‖((q : ℕ) : PadicAlgCl q)‖ ^ (a * N₂) = ((q : ℝ) ^ (a * N₂))⁻¹ := by
      rw [hnq, inv_zpow]
    have hcz₁ : ((((q : ℕ) : L₁) ^ (a * (N₂ : ℤ)) : L₁) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) ^ (a * (N₂ : ℤ)) := by
      have h := map_zpow₀ (algebraMap (↥L₁) (PadicAlgCl q)) ((q : ℕ) : L₁) (a * N₂)
      rw [map_natCast] at h
      exact h
    have hcz₂ : ((((q : ℕ) : L₂) ^ (a * (N₂ : ℤ)) : L₂) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) ^ (a * (N₂ : ℤ)) := by
      have h := map_zpow₀ (algebraMap (↥L₂) (PadicAlgCl q)) ((q : ℕ) : L₂) (a * N₂)
      rw [map_natCast] at h
      exact h
    have hnw : ‖(w : PadicAlgCl q)‖ = 1 := by
      rw [hw]
      push_cast
      rw [norm_mul, norm_pow, hcz₁, norm_zpow, hxN, hqz, mul_inv_cancel₀ (zpow_ne_zero _ hq0.ne')]
    have h1 := hone w hnw

    have hΨw : ‖Ψ w‖ = ‖((α x : L₂) : PadicAlgCl q)‖ ^ (N₁ * N₂) * ((q : ℝ) ^ (a * N₂))⁻¹ := by
      rw [← hΨ, hw, map_mul, map_pow, map_zpow₀, map_natCast]
      push_cast
      rw [norm_mul, norm_pow, hcz₂, norm_zpow, hqz]
    have hαN : ‖((α x : L₂) : PadicAlgCl q)‖ ^ (N₁ * N₂) = (q : ℝ) ^ (a' * N₁) := by
      rw [mul_comm N₁ N₂, pow_mul, ha', ← zpow_natCast, ← zpow_mul]
    rw [h1.symm.symm, hαN] at hΨw

    have hexp : (q : ℝ) ^ (a' * N₁) = (q : ℝ) ^ (a * N₂) := by
      rw [eq_mul_inv_iff_mul_eq₀ (zpow_ne_zero _ hq0.ne'), one_mul] at hΨw
      exact hΨw.symm
    have hpow : ‖((α x : L₂) : PadicAlgCl q)‖ ^ (N₁ * N₂) = ‖(x : PadicAlgCl q)‖ ^ (N₁ * N₂) := by
      rw [hαN, hxN, hexp]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (Nat.mul_ne_zero hN₁0 hN₂0)).mp hpow

  have hint_fix : ∀ c : ℤ_[q], α (algebraMap ℚ_[q] L₁ (c : ℚ_[q])) = algebraMap ℚ_[q] L₂ (c : ℚ_[q]) := by
    intro c
    set dd : PadicAlgCl q := ((α (algebraMap ℚ_[q] L₁ (c : ℚ_[q])) : L₂) : PadicAlgCl q) -
      ((algebraMap ℚ_[q] L₂ (c : ℚ_[q]) : L₂) : PadicAlgCl q) with hdd
    suffices hd0 : dd = 0 by
      apply Subtype.ext
      exact sub_eq_zero.mp hd0
    by_contra hd0
    have hdpos : 0 < ‖dd‖ := norm_pos_iff.mpr hd0
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hdpos (inv_lt_one_of_one_lt₀ hq1)
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k c)
    have hcdec : (c : ℚ_[q]) = (PadicInt.appr c k : ℚ_[q]) + (q : ℚ_[q]) ^ k * (c' : ℚ_[q]) := by
      have h := congrArg (fun z : ℤ_[q] => (z : ℚ_[q])) hc'
      push_cast at h
      linear_combination -h
    have e1 : ‖((α (algebraMap ℚ_[q] L₁ (c' : ℚ_[q])) : L₂) : PadicAlgCl q)‖ ≤ 1 := by
      rw [hΨ]
      apply hOS
      rw [hcoe₁, PadicAlgCl.norm_extends]
      exact PadicInt.norm_le_one c'
    have e2 : ‖((algebraMap ℚ_[q] L₂ (c' : ℚ_[q]) : L₂) : PadicAlgCl q)‖ ≤ 1 := by
      rw [hcoe₂, PadicAlgCl.norm_extends]
      exact PadicInt.norm_le_one c'
    have hd' : dd = ((q : ℕ) : PadicAlgCl q) ^ k * (((α (algebraMap ℚ_[q] L₁ (c' : ℚ_[q])) : L₂) : PadicAlgCl q) -
        ((algebraMap ℚ_[q] L₂ (c' : ℚ_[q]) : L₂) : PadicAlgCl q)) := by
      rw [hdd, hcdec]
      simp only [map_add, map_mul, map_pow, map_natCast]
      push_cast
      ring
    have hbd : ‖dd‖ ≤ ((q : ℝ)⁻¹) ^ k := by
      rw [hd', norm_mul, norm_pow, hnq]
      apply mul_le_of_le_one_right (pow_nonneg (inv_nonneg.mpr hq0.le) _)
      have hsub := PadicAlgCl.isNonarchimedean q (((α (algebraMap ℚ_[q] L₁ (c' : ℚ_[q])) : L₂) : PadicAlgCl q))
        (-((algebraMap ℚ_[q] L₂ (c' : ℚ_[q]) : L₂) : PadicAlgCl q))
      rw [← sub_eq_add_neg, norm_neg] at hsub
      exact hsub.trans (max_le e1 e2)
    linarith
  have hfix : ∀ x : ℚ_[q], α (algebraMap ℚ_[q] L₁ x) = algebraMap ℚ_[q] L₂ x := by
    intro x
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖x‖ hq1
    have hxm : ‖x * (q : ℚ_[q]) ^ m‖ ≤ 1 := by
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hq0 m)]
      exact hm.le
    have hqm1 : ‖(q : ℚ_[q]) ^ m‖ ≤ 1 := by
      rw [norm_pow, Padic.norm_p, inv_pow]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hq1.le)
    have h1 := hint_fix ⟨x * (q : ℚ_[q]) ^ m, hxm⟩
    have h2 := hint_fix ⟨(q : ℚ_[q]) ^ m, hqm1⟩
    change α (algebraMap ℚ_[q] L₁ (x * (q : ℚ_[q]) ^ m)) = algebraMap ℚ_[q] L₂ (x * (q : ℚ_[q]) ^ m) at h1
    change α (algebraMap ℚ_[q] L₁ ((q : ℚ_[q]) ^ m)) = algebraMap ℚ_[q] L₂ ((q : ℚ_[q]) ^ m) at h2
    rw [map_mul, map_mul, map_mul, h2] at h1
    have hqm : algebraMap ℚ_[q] L₂ ((q : ℚ_[q]) ^ m) ≠ 0 := by
      rw [map_ne_zero]
      exact pow_ne_zero _ (by exact_mod_cast hqP.ne_zero)
    exact mul_right_cancel₀ hqm h1
  exact ⟨hfix, hiso⟩

end S_IntermediateField_apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic
end P2MW
export P2MW.S_IntermediateField_apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic (solution)

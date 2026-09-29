-- Prove2me | solution 1 for HopfAlgebra.exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/24f51508-cf20-5b90-b2c2-7229b50060e7

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_HopfTower
import Theorems.Thm_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent
import Theorems.Thm_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent
import Theorems.Thm_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open Function MvPolynomial

universe u v

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk IsHopfSubalgebra HopfTower.antipodeAlgHom_apply finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent"
namespace InfinitesimalStructure
p2m_open "HopfAlgebra"

section Basic

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

variable (k H) in

abbrev augI : Ideal H := RingHom.ker (Bialgebra.counitAlgHom k H)

theorem mem_augI {x : H} : x ∈ augI k H ↔ Coalgebra.counit (R := k) x = 0 := RingHom.mem_ker

include k in
theorem nontrivial : Nontrivial H :=
  ⟨⟨0, 1, fun h => zero_ne_one (by
    have := congrArg (Coalgebra.counit (R := k) (A := H)) h
    rwa [map_zero, Bialgebra.counit_one] at this)⟩⟩

theorem counit_algebraMap (c : k) : Coalgebra.counit (R := k) (algebraMap k H c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one]

variable (k) in
theorem algebraMap_injective : Injective (algebraMap k H) := fun a b h => by
  have := congrArg (Coalgebra.counit (R := k) (A := H)) h
  rwa [counit_algebraMap, counit_algebraMap] at this

theorem sub_algebraMap_counit_mem (x : H) :
    x - algebraMap k H (Coalgebra.counit (R := k) x) ∈ augI k H := by
  rw [mem_augI, map_sub, counit_algebraMap, sub_self]

theorem isNilpotent_augI [Module.Finite k H]
    (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x) : IsNilpotent (augI k H) := by
  haveI : IsArtinianRing H := IsArtinianRing.of_finite k H
  have hfg : (augI k H).FG := (isNoetherianRing_iff_ideal_fg H).1 inferInstance _
  rw [Ideal.FG.isNilpotent_iff_le_nilradical hfg]
  intro x hx
  exact hH x (mem_augI.1 hx)

variable (p : ℕ) [hp : Fact p.Prime] [CharP k p]

include k in
theorem charP_self : CharP H p :=
  haveI : Nontrivial H := nontrivial (k := k)
  charP_of_injective_algebraMap (algebraMap_injective k) p

theorem charP_tensor : CharP (H ⊗[k] H) p := by
  refine charP_of_injective_algebraMap (R := k) (fun a b h => ?_) p
  let g : H ⊗[k] H →ₐ[k] k :=
    ((Algebra.TensorProduct.lid k k).toAlgHom).comp
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom k H) (Bialgebra.counitAlgHom k H))
  have := congrArg g h
  rwa [AlgHom.commutes, AlgHom.commutes] at this

end Basic

section Gen

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H]

theorem eq_top_of_forall_exists_sub_mem_sq (T : Subalgebra k H) (I : Ideal H) (hI : IsNilpotent I)
    (hdec : ∀ h : H, ∃ c : k, h - algebraMap k H c ∈ I)
    (hT : ∀ h ∈ I, ∃ t ∈ T, t ∈ I ∧ h - t ∈ I ^ 2) : T = ⊤ := by

  have hQ : ∀ m : ℕ, 1 ≤ m → ∀ u ∈ I ^ m, ∃ τ ∈ T, τ ∈ I ^ m ∧ u - τ ∈ I ^ (m + 1) := by
    intro m hm
    induction m with
    | zero => exact absurd hm (by omega)
    | succ m ih =>
      intro u hu
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · rw [zero_add, pow_one] at hu
        simpa only [zero_add, pow_one] using hT u hu
      rw [pow_succ] at hu
      refine Submodule.mul_induction_on hu (fun a ha b hb => ?_) (fun x y hx hy => ?_)
      · obtain ⟨τ, hτT, hτI, haτ⟩ := ih hmpos a ha
        obtain ⟨t, htT, htI, hbt⟩ := hT b hb
        refine ⟨τ * t, T.mul_mem hτT htT, ?_, ?_⟩
        · rw [pow_succ]; exact Ideal.mul_mem_mul hτI htI
        · have h1 : τ * (b - t) ∈ I ^ (m + 1 + 1) := by
            rw [show m + 1 + 1 = m + 2 by ring, pow_add]; exact Ideal.mul_mem_mul hτI hbt
          have h2 : (a - τ) * b ∈ I ^ (m + 1 + 1) := by
            rw [pow_succ]; exact Ideal.mul_mem_mul haτ hb
          have : a * b - τ * t = τ * (b - t) + (a - τ) * b := by ring
          rw [this]
          exact add_mem h1 h2
      · obtain ⟨τ, hτT, hτI, hx'⟩ := hx
        obtain ⟨τ', hτ'T, hτ'I, hy'⟩ := hy
        refine ⟨τ + τ', T.add_mem hτT hτ'T, add_mem hτI hτ'I, ?_⟩
        have : x + y - (τ + τ') = (x - τ) + (y - τ') := by ring
        rw [this]
        exact add_mem hx' hy'

  have hR : ∀ m : ℕ, 1 ≤ m → ∀ h ∈ I, ∃ τ ∈ T, h - τ ∈ I ^ (m + 1) := by
    intro m hm
    induction m with
    | zero => exact absurd hm (by omega)
    | succ m ih =>
      intro h hh
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · obtain ⟨t, htT, -, hht⟩ := hT h hh
        exact ⟨t, htT, hht⟩
      obtain ⟨τ, hτT, hhτ⟩ := ih hmpos h hh
      obtain ⟨τ', hτ'T, -, h'⟩ := hQ (m + 1) (by omega) (h - τ) hhτ
      refine ⟨τ + τ', T.add_mem hτT hτ'T, ?_⟩
      rwa [← sub_sub]
  obtain ⟨N, hN⟩ := hI
  refine eq_top_iff.2 fun h _ => ?_
  obtain ⟨c, hc⟩ := hdec h
  obtain ⟨τ, hτT, hτ⟩ := hR (N + 1) (by omega) _ hc
  have hzero : h - algebraMap k H c - τ = 0 := by
    have hle : I ^ (N + 1 + 1) ≤ I ^ N := Ideal.pow_le_pow_right (by omega)
    have := hle hτ
    rwa [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have : h = τ + algebraMap k H c := by linear_combination hzero
  rw [this]
  exact T.add_mem hτT (T.algebraMap_mem c)

end Gen

section Frob

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectField k]
variable (H : Type v) [CommRing H] [HopfAlgebra k H]

theorem frobeniusEquiv_symm_pow (c : k) : ((frobeniusEquiv k p).symm c) ^ p = c := by
  rw [← frobenius_def]; exact frobenius_apply_frobeniusEquiv_symm k p c

def frobSub : Subalgebra k H where
  carrier := Set.range fun x : H => x ^ p
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, mul_pow x y p⟩
  one_mem' := ⟨1, one_pow p⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    haveI := charP_self (k := k) (H := H) p
    exact ⟨x + y, add_pow_char x y p⟩
  zero_mem' := ⟨0, zero_pow hp.out.ne_zero⟩
  algebraMap_mem' c := ⟨algebraMap k H ((frobeniusEquiv k p).symm c), by
    change (algebraMap k H ((frobeniusEquiv k p).symm c)) ^ p = algebraMap k H c
    rw [← map_pow, frobeniusEquiv_symm_pow]⟩

variable {k p H}

theorem mem_frobSub_iff {x : H} : x ∈ frobSub k p H ↔ ∃ y : H, y ^ p = x := Iff.rfl

theorem pow_mem_frobSub (y : H) : y ^ p ∈ frobSub k p H := ⟨y, rfl⟩

theorem pow_mem_span_tmul (z : H ⊗[k] H) :
    z ^ p ∈ Submodule.span k
      {t : H ⊗[k] H | ∃ a ∈ frobSub k p H, ∃ b ∈ frobSub k p H, t = a ⊗ₜ[k] b} := by
  haveI := charP_tensor (k := k) (H := H) p
  induction z with
  | zero => rw [zero_pow hp.out.ne_zero]; exact Submodule.zero_mem _
  | tmul a b =>
    rw [Algebra.TensorProduct.tmul_pow]
    exact Submodule.subset_span ⟨a ^ p, pow_mem_frobSub a, b ^ p, pow_mem_frobSub b, rfl⟩
  | add x y hx hy =>
    rw [add_pow_char]
    exact Submodule.add_mem _ hx hy

theorem isHopfSubalgebra_frobSub : IsHopfSubalgebra k (frobSub k p H) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, rfl⟩ := hx
    have : Coalgebra.comul (R := k) (y ^ p) = (Coalgebra.comul (R := k) y) ^ p :=
      map_pow (Bialgebra.comulAlgHom k H) y p
    rw [this]
    exact pow_mem_span_tmul _
  · obtain ⟨y, rfl⟩ := hx
    refine ⟨antipode k y, ?_⟩
    change (antipode k y) ^ p = antipode k (y ^ p)
    rw [← HopfTower.antipodeAlgHom_apply k H, ← HopfTower.antipodeAlgHom_apply k H, map_pow]

theorem counit_pow_eq_zero_iff {y : H} {m : ℕ} (hm : m ≠ 0) :
    Coalgebra.counit (R := k) (y ^ m) = 0 ↔ Coalgebra.counit (R := k) y = 0 := by
  rw [Bialgebra.counit_pow]
  exact pow_eq_zero_iff hm

theorem setOf_mem_frobSub_eq_image :
    {x : H | x ∈ frobSub k p H ∧ Coalgebra.counit (R := k) x = 0} =
      (fun a : H => a ^ p) '' (augI k H : Set H) := by
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, hx⟩
    exact ⟨y, mem_augI.2 ((counit_pow_eq_zero_iff hp.out.ne_zero).1 hx), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨pow_mem_frobSub y, (counit_pow_eq_zero_iff hp.out.ne_zero).2 (mem_augI.1 hy)⟩

theorem augI_eq_bot_of_frobSub_eq_top [Module.Finite k H]
    (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x)
    (htop : frobSub k p H = ⊤) : ∀ x : H, Coalgebra.counit (R := k) x = 0 → x = 0 := by

  have hI2 : augI k H ≤ augI k H ^ 2 := by
    intro x hx
    have hxS : x ∈ frobSub k p H := by rw [htop]; exact Algebra.mem_top
    obtain ⟨y, rfl⟩ := hxS
    have hy : y ∈ augI k H := mem_augI.2 ((counit_pow_eq_zero_iff hp.out.ne_zero).1 (mem_augI.1 hx))
    exact Ideal.pow_le_pow_right hp.out.two_le (Ideal.pow_mem_pow hy p)

  have hIN : ∀ N : ℕ, 1 ≤ N → augI k H ≤ augI k H ^ N := by
    intro N hN
    induction N with
    | zero => exact absurd hN (by omega)
    | succ N ih =>
      rcases Nat.eq_zero_or_pos N with rfl | hNpos
      · rw [zero_add, pow_one]
      · calc augI k H ≤ augI k H ^ 2 := hI2
          _ = augI k H * augI k H := pow_two _
          _ ≤ augI k H ^ N * augI k H := Ideal.mul_mono_left (ih hNpos)
          _ = augI k H ^ (N + 1) := (pow_succ _ _).symm
  obtain ⟨N, hN⟩ := isNilpotent_augI hH
  intro x hx
  have := hIN (N + 1) (by omega) (mem_augI.2 hx)
  have hle : augI k H ^ (N + 1) ≤ augI k H ^ N := Ideal.pow_le_pow_right (by omega)
  have := hle this
  rwa [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this

theorem finrank_frobSub_lt [Module.Finite k H]
    (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x)
    (hne : ∃ x : H, Coalgebra.counit (R := k) x = 0 ∧ x ≠ 0) :
    Module.finrank k (frobSub k p H) < Module.finrank k H := by
  by_contra hlt
  have heq : Module.finrank k (Subalgebra.toSubmodule (frobSub k p H)) = Module.finrank k H :=
    le_antisymm (Submodule.finrank_le _) (not_lt.1 hlt)
  have htop : frobSub k p H = ⊤ :=
    Algebra.toSubmodule_eq_top.1 (Submodule.eq_top_of_finrank_eq heq)
  obtain ⟨x, hx, hx0⟩ := hne
  exact hx0 (augI_eq_bot_of_frobSub_eq_top hH htop x hx)

end Frob

section Presentation

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime]

variable (k p) in

def Kp (d : ℕ) (e : Fin d → ℕ) : Ideal (MvPolynomial (Fin d) k) :=
  Ideal.span (Set.range fun i : Fin d => (X i : MvPolynomial (Fin d) k) ^ p ^ (e i + 1))

theorem X_pow_mem_Kp {d : ℕ} (e : Fin d → ℕ) (i : Fin d) :
    (X i : MvPolynomial (Fin d) k) ^ p ^ (e i + 1) ∈ Kp k p d e := Ideal.subset_span ⟨i, rfl⟩

variable (k) in

def XI (d : ℕ) : Ideal (MvPolynomial (Fin d) k) := Ideal.span (Set.range (X : Fin d → _))

theorem mem_XI_of_constantCoeff_eq_zero {d : ℕ} {P : MvPolynomial (Fin d) k}
    (hP : constantCoeff P = 0) : P ∈ XI k d := by
  rw [XI, ← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra hcon
  simp only [Set.mem_univ, true_and, not_exists, not_not] at hcon
  have hm0 : m = 0 := Finsupp.ext hcon
  rw [hm0, mem_support_iff] at hm
  exact hm hP

theorem Kp_le_XI_sq {d : ℕ} (e : Fin d → ℕ) : Kp k p d e ≤ XI k d ^ 2 := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  show X i ^ p ^ (e i + 1) ∈ XI k d ^ 2
  have h2 : 2 ≤ p ^ (e i + 1) := (Nat.pow_le_pow_right hp.out.pos (Nat.le_add_left 1 _)).trans'
    (by rw [pow_one]; exact hp.out.two_le)
  have hX : (X i : MvPolynomial (Fin d) k) ∈ XI k d := Ideal.subset_span ⟨i, rfl⟩
  rw [← Nat.add_sub_cancel' h2, pow_add, sq, sq]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hX hX)

theorem XI_sq_le_span_monomial (d : ℕ) :
    XI k d ^ 2 ≤ Ideal.span ((fun s => monomial s (1 : k)) ''
      {s : Fin d →₀ ℕ | ∃ a b : Fin d, s = Finsupp.single a 1 + Finsupp.single b 1}) := by
  rw [pow_two, XI, Ideal.span_mul_span']
  refine Ideal.span_mono ?_
  rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
  refine ⟨Finsupp.single a 1 + Finsupp.single b 1, ⟨a, b, rfl⟩, ?_⟩
  change monomial _ _ = X a * X b
  rw [X, X, monomial_mul, mul_one]

theorem eq_zero_of_sum_C_mul_X_mem_XI_sq {d : ℕ} (c : Fin d → k)
    (h : (∑ j, C (c j) * X j : MvPolynomial (Fin d) k) ∈ XI k d ^ 2) : ∀ j, c j = 0 := by
  intro j
  have hmem := XI_sq_le_span_monomial d h
  rw [mem_ideal_span_monomial_image] at hmem
  by_contra hcj
  have hcoeff : coeff (Finsupp.single j 1) (∑ i, C (c i) * X i : MvPolynomial (Fin d) k) = c j := by
    rw [coeff_sum]
    simp_rw [coeff_C_mul, coeff_X', Finsupp.single_left_inj Nat.one_ne_zero, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]
  have hsupp : Finsupp.single j 1 ∈ (∑ i, C (c i) * X i : MvPolynomial (Fin d) k).support := by
    rw [mem_support_iff, hcoeff]; exact hcj
  obtain ⟨_, ⟨a, b, rfl⟩, hle⟩ := hmem _ hsupp
  have ha := hle a
  have hb := hle b
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at ha hb
  split_ifs at ha hb <;> omega

end Presentation

section Presented

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {S : Type v} [CommRing S] [HopfAlgebra k S]
variable {s : ℕ} {f : Fin s → ℕ} (ψ : S ≃ₐ[k] (MvPolynomial (Fin s) k ⧸ Kp k p s f))

def yg (j : Fin s) : S := ψ.symm (Ideal.Quotient.mk _ (X j))

theorem yg_pow (j : Fin s) : yg ψ j ^ p ^ (f j + 1) = 0 := by
  rw [yg, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (X_pow_mem_Kp f j), map_zero]

theorem counit_yg (j : Fin s) : Coalgebra.counit (R := k) (yg ψ j) = 0 := by
  have h : (Coalgebra.counit (R := k) (yg ψ j)) ^ p ^ (f j + 1) = 0 := by
    rw [← Bialgebra.counit_pow, yg_pow, map_zero]
  exact pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero) |>.1 h

theorem symm_mk_eq_aeval (P : MvPolynomial (Fin s) k) :
    ψ.symm (Ideal.Quotient.mk _ P) = aeval (yg ψ) P := by
  have key : (ψ.symm : (MvPolynomial (Fin s) k ⧸ Kp k p s f) →ₐ[k] S).comp (Ideal.Quotient.mkₐ k _) =
      aeval (yg ψ) := MvPolynomial.algHom_ext fun j => by
    rw [AlgHom.comp_apply, aeval_X]; rfl
  exact AlgHom.congr_fun key P

theorem counit_symm_mk (P : MvPolynomial (Fin s) k) :
    Coalgebra.counit (R := k) (ψ.symm (Ideal.Quotient.mk _ P)) = constantCoeff P := by
  have key : (Bialgebra.counitAlgHom k S).comp
      ((ψ.symm : (MvPolynomial (Fin s) k ⧸ Kp k p s f) →ₐ[k] S).comp (Ideal.Quotient.mkₐ k _)) =
      aeval (0 : Fin s → k) := MvPolynomial.algHom_ext fun j => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, aeval_X, Pi.zero_apply, Bialgebra.counitAlgHom_apply]
    exact counit_yg ψ j
  have := AlgHom.congr_fun key P
  rwa [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, aeval_zero,
    Algebra.algebraMap_self_apply] at this

theorem apply_mem_map_XI_sq {w : S} (hw : w ∈ augI k S ^ 2) :
    ψ w ∈ (XI k s ^ 2).map (Ideal.Quotient.mk (Kp k p s f)) := by
  have hone : ∀ m ∈ augI k S, ψ m ∈ (XI k s).map (Ideal.Quotient.mk (Kp k p s f)) := by
    intro m hm
    obtain ⟨R, hR⟩ := Ideal.Quotient.mk_surjective (ψ m)
    have hR0 : constantCoeff R = 0 := by
      rw [← counit_symm_mk ψ R, hR, AlgEquiv.symm_apply_apply]
      exact mem_augI.1 hm
    rw [← hR]
    exact Ideal.mem_map_of_mem _ (mem_XI_of_constantCoeff_eq_zero hR0)
  rw [pow_two] at hw
  rw [pow_two, Ideal.map_mul]
  refine Submodule.mul_induction_on hw (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [map_mul]; exact Ideal.mul_mem_mul (hone a ha) (hone b hb)
  · rw [map_add]; exact add_mem hx hy

theorem eq_zero_of_sum_smul_yg_mem_sq (c : Fin s → k) (h : ∑ j, c j • yg ψ j ∈ augI k S ^ 2) :
    ∀ j, c j = 0 := by
  have hψ := apply_mem_map_XI_sq ψ h
  rw [map_sum] at hψ
  simp_rw [map_smul, yg, AlgEquiv.apply_symm_apply] at hψ
  have hL : (Ideal.Quotient.mk (Kp k p s f)) (∑ j, C (c j) * X j) =
      ∑ j, c j • (Ideal.Quotient.mk (Kp k p s f)) (X j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_C_mul, ← Ideal.Quotient.mkₐ_eq_mk k, map_smul]
  rw [← hL, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hψ
  obtain ⟨R, hR, hRL⟩ := hψ
  rw [Ideal.Quotient.eq] at hRL
  have hL2 : (∑ j, C (c j) * X j : MvPolynomial (Fin s) k) ∈ XI k s ^ 2 := by
    have : (∑ j, C (c j) * X j : MvPolynomial (Fin s) k) = R - (R - ∑ j, C (c j) * X j) := by ring
    rw [this]
    exact sub_mem hR (Kp_le_XI_sq f hRL)
  exact eq_zero_of_sum_C_mul_X_mem_XI_sq c hL2

end Presented

section Cotangent

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

def πI (h : H) : augI k H :=
  ⟨h - algebraMap k H (Coalgebra.counit (R := k) h), sub_algebraMap_counit_mem h⟩

@[scoped simp] theorem coe_πI (h : H) :
    ((πI (k := k) h : augI k H) : H) = h - algebraMap k H (Coalgebra.counit (R := k) h) := rfl

variable (k H) in

def cl : H →ₗ[k] (augI k H).Cotangent where
  toFun h := (augI k H).toCotangent (πI (k := k) h)
  map_add' u v := by
    rw [← map_add]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_πI, Submodule.coe_add, map_add]
    ring
  map_smul' c u := by
    rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_πI, SetLike.val_smul_of_tower, Algebra.smul_def, Bialgebra.counit_mul,
      counit_algebraMap, map_mul]
    ring

theorem cl_apply (h : H) : cl k H h = (augI k H).toCotangent (πI (k := k) h) := rfl

theorem cl_of_mem {h : H} (hh : h ∈ augI k H) : cl k H h = (augI k H).toCotangent ⟨h, hh⟩ := by
  rw [cl_apply]
  congr 1
  refine Subtype.ext ?_
  rw [coe_πI, mem_augI.1 hh, map_zero, sub_zero]

theorem cl_algebraMap (c : k) : cl k H (algebraMap k H c) = 0 := by
  rw [cl_apply, ← map_zero (augI k H).toCotangent]
  congr 1
  refine Subtype.ext ?_
  rw [coe_πI, counit_algebraMap, sub_self]
  rfl

theorem cl_one : cl k H 1 = 0 := by rw [← map_one (algebraMap k H)]; exact cl_algebraMap 1

theorem cl_eq_zero_iff_of_mem {h : H} (hh : h ∈ augI k H) : cl k H h = 0 ↔ h ∈ augI k H ^ 2 := by
  rw [cl_of_mem hh, Ideal.toCotangent_eq_zero]

theorem cl_mul (u v : H) :
    cl k H (u * v) = Coalgebra.counit (R := k) u • cl k H v + Coalgebra.counit (R := k) v • cl k H u := by
  rw [cl_apply, cl_apply, cl_apply, ← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower,
    ← map_add, Ideal.toCotangent_eq]
  have : ((πI (k := k) (u * v) : augI k H) : H) -
      ((Coalgebra.counit (R := k) u • πI (k := k) v + Coalgebra.counit (R := k) v • πI (k := k) u :
        augI k H) : H) =
      (u - algebraMap k H (Coalgebra.counit (R := k) u)) *
        (v - algebraMap k H (Coalgebra.counit (R := k) v)) := by
    simp only [Submodule.coe_add, SetLike.val_smul_of_tower, coe_πI, Bialgebra.counit_mul, map_mul,
      Algebra.smul_def]
    ring
  rw [this, pow_two]
  exact Ideal.mul_mem_mul (sub_algebraMap_counit_mem u) (sub_algebraMap_counit_mem v)

theorem exists_cl_eq (ξ : (augI k H).Cotangent) : ∃ h ∈ augI k H, cl k H h = ξ := by
  obtain ⟨⟨h, hh⟩, rfl⟩ := (augI k H).toCotangent_surjective ξ
  exact ⟨h, hh, cl_of_mem hh⟩

end Cotangent

section Step

variable {k : Type u} [Field k] [PerfectField k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {H : Type v} [CommRing H] [HopfAlgebra k H] [Module.Finite k H]

theorem step (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x)
    {s : ℕ} {f : Fin s → ℕ}
    (ψ : ↥(frobSub k p H) ≃ₐ[k] (MvPolynomial (Fin s) k ⧸ Kp k p s f)) :
    ∃ (d : ℕ) (e : Fin d → ℕ), Nonempty (H ≃ₐ[k] (MvPolynomial (Fin d) k ⧸ Kp k p d e)) := by
  classical
  haveI : Nontrivial H := nontrivial (k := k)
  haveI hchar : CharP H p := charP_self (k := k) p
  have hS : IsHopfSubalgebra k (frobSub k p H) := isHopfSubalgebra_frobSub
  letI : HopfAlgebra k ↥(frobSub k p H) := hS.hopfAlgebra
  have hcoS : ∀ w : ↥(frobSub k p H),
      Coalgebra.counit (R := k) w = Coalgebra.counit (R := k) (w : H) := fun w => rfl

  set y : Fin s → ↥(frobSub k p H) := yg ψ with hydef
  have hy_pow : ∀ j, y j ^ p ^ (f j + 1) = 0 := yg_pow ψ
  have hy_co : ∀ j, Coalgebra.counit (R := k) (y j) = 0 := counit_yg ψ
  have hx_ex : ∀ j : Fin s, ∃ x : H, x ^ p = ((y j : ↥(frobSub k p H)) : H) := fun j =>
    mem_frobSub_iff.1 (y j).2
  choose x hx using hx_ex
  have hxI : ∀ j, Coalgebra.counit (R := k) (x j) = 0 := fun j => by
    have h := hy_co j
    rw [hcoS, ← hx, Bialgebra.counit_pow] at h
    exact pow_eq_zero_iff hp.out.ne_zero |>.1 h
  have hx_pow : ∀ j, x j ^ p ^ (f j + 1 + 1) = 0 := fun j => by
    rw [pow_succ', pow_mul, hx, ← SubmonoidClass.coe_pow, hy_pow, ZeroMemClass.coe_zero]

  have hindep : LinearIndependent k fun j => cl k H (x j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hsumI : (∑ j, c j • x j : H) ∈ augI k H := Submodule.sum_mem _ fun j _ =>
      Submodule.smul_of_tower_mem _ _ (mem_augI.2 (hxI j))
    have hsum2 : (∑ j, c j • x j : H) ∈ augI k H ^ 2 := by
      rw [← cl_eq_zero_iff_of_mem hsumI, map_sum]
      simp_rw [map_smul]
      exact hc

    have hfrob : (∑ j, c j • x j : H) ^ p = ∑ j, (c j ^ p) • ((y j : ↥(frobSub k p H)) : H) := by
      rw [sum_pow_char]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_pow, hx]

    have himg : ∀ w ∈ augI k H ^ 2, ∃ wS : ↥(frobSub k p H),
        wS ∈ augI k ↥(frobSub k p H) ^ 2 ∧ (wS : H) = w ^ p := by
      intro w hw
      rw [pow_two] at hw
      refine Submodule.mul_induction_on hw (fun a ha b hb => ?_) ?_
      · refine ⟨⟨a ^ p, pow_mem_frobSub a⟩ * ⟨b ^ p, pow_mem_frobSub b⟩, ?_, ?_⟩
        · rw [pow_two]
          refine Ideal.mul_mem_mul (mem_augI.2 ?_) (mem_augI.2 ?_)
          · rw [hcoS]; exact (counit_pow_eq_zero_iff hp.out.ne_zero).2 (mem_augI.1 ha)
          · rw [hcoS]; exact (counit_pow_eq_zero_iff hp.out.ne_zero).2 (mem_augI.1 hb)
        · rw [Subalgebra.coe_mul, mul_pow]
      · rintro u v ⟨su, hsu, hu⟩ ⟨sv, hsv, hv⟩
        exact ⟨su + sv, add_mem hsu hsv, by rw [Subalgebra.coe_add, hu, hv, add_pow_char]⟩
    obtain ⟨wS, hwS, hwSval⟩ := himg _ hsum2
    rw [hfrob] at hwSval
    have hwSeq : wS = ∑ j, (c j ^ p) • y j := Subtype.ext (by
      rw [hwSval, AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun j _ => (SetLike.val_smul _ _ _).symm)
    rw [hwSeq] at hwS
    have := eq_zero_of_sum_smul_yg_mem_sq ψ (fun j => c j ^ p) hwS j
    exact pow_eq_zero_iff hp.out.ne_zero |>.1 this

  haveI : Module.Finite k ↥(augI k H) :=
    Module.Finite.of_injective ((augI k H).subtype.restrictScalars k) Subtype.val_injective
  haveI : Module.Finite k (augI k H).Cotangent :=
    Module.Finite.of_surjective ((augI k H).toCotangent.restrictScalars k) (augI k H).toCotangent_surjective
  set U : Submodule k (augI k H).Cotangent := Submodule.span k (Set.range fun j => cl k H (x j))
    with hUdef
  have hfinU : Module.finrank k U = s := (finrank_span_eq_card hindep).trans (Fintype.card_fin s)
  obtain ⟨W, hUW⟩ := U.exists_isCompl
  set t : ℕ := Module.finrank k W with htdef
  let bW := Module.finBasis k W
  have hzpre : ∀ i : Fin t, ∃ z : H, z ∈ augI k H ∧ cl k H z = (bW i : (augI k H).Cotangent) :=
    fun i => exists_cl_eq _
  choose zpre hzpreI hzpre using hzpre

  have hQ : ∀ i : Fin t, ∃ Q : MvPolynomial (Fin s) k,
      Ideal.Quotient.mk (Kp k p s f) Q = ψ ⟨zpre i ^ p, pow_mem_frobSub _⟩ :=
    fun i => Ideal.Quotient.mk_surjective _
  choose Q hQ using hQ
  have hQeval : ∀ i, aeval (fun j => ((y j : ↥(frobSub k p H)) : H)) (Q i) = zpre i ^ p := by
    intro i
    have h1 : ψ.symm (Ideal.Quotient.mk _ (Q i)) = ⟨zpre i ^ p, pow_mem_frobSub _⟩ := by
      rw [hQ, AlgEquiv.symm_apply_apply]
    rw [symm_mk_eq_aeval] at h1
    have h2 := congrArg (frobSub k p H).val h1
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h2
    exact h2

  set σi : k →+* k := ((frobeniusEquiv k p).symm : k ≃+* k).toRingHom with hσi
  set Qt : Fin t → H := fun i => MvPolynomial.eval₂ ((algebraMap k H).comp σi) x (Q i) with hQtdef
  have hQt_pow : ∀ i, Qt i ^ p = zpre i ^ p := by
    intro i
    have hcomp : (frobenius H p).comp (MvPolynomial.eval₂Hom ((algebraMap k H).comp σi) x) =
        MvPolynomial.eval₂Hom (algebraMap k H) (fun j => ((y j : ↥(frobSub k p H)) : H)) := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
          frobenius_def, ← map_pow, hσi, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          frobeniusEquiv_symm_pow]
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', frobenius_def, hx]
    have := RingHom.congr_fun hcomp (Q i)
    rw [RingHom.comp_apply, frobenius_def, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom,
      ← MvPolynomial.aeval_def, hQeval] at this
    exact this
  set z : Fin t → H := fun i => zpre i - Qt i with hzdef
  have hz_pow : ∀ i, z i ^ p = 0 := fun i => by
    rw [hzdef]
    change (zpre i - Qt i) ^ p = 0
    rw [sub_pow_char, hQt_pow, sub_self]
  have hQtI : ∀ i, Coalgebra.counit (R := k) (Qt i) = 0 := fun i => by
    have h : (Coalgebra.counit (R := k) (Qt i)) ^ p = 0 := by
      rw [← Bialgebra.counit_pow, hQt_pow, Bialgebra.counit_pow, mem_augI.1 (hzpreI i),
        zero_pow hp.out.ne_zero]
    exact pow_eq_zero_iff hp.out.ne_zero |>.1 h
  have hzI : ∀ i, Coalgebra.counit (R := k) (z i) = 0 := fun i => by
    rw [hzdef]
    change Coalgebra.counit (R := k) (zpre i - Qt i) = 0
    rw [map_sub, mem_augI.1 (hzpreI i), hQtI, sub_zero]

  have hQtU : ∀ i, cl k H (Qt i) ∈ U := by
    intro i
    suffices h : ∀ P : MvPolynomial (Fin s) k,
        cl k H (MvPolynomial.eval₂ ((algebraMap k H).comp σi) x P) ∈ U from h (Q i)
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.eval₂_C, RingHom.comp_apply, cl_algebraMap]; exact U.zero_mem
    | add P P' hP hP' => rw [MvPolynomial.eval₂_add, map_add]; exact U.add_mem hP hP'
    | mul_X P j hP =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, cl_mul, hxI, zero_smul, add_zero]
      exact U.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)

  set g : Fin (s + t) → H := Fin.append x z with hgdef
  set E : Fin (s + t) → ℕ := Fin.append (fun j => f j + 1) (fun _ => 0) with hEdef
  have hgI : ∀ v, Coalgebra.counit (R := k) (g v) = 0 := by
    refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · rw [hgdef, Fin.append_left]; exact hxI j
    · rw [hgdef, Fin.append_right]; exact hzI i
  have hg_pow : ∀ v, g v ^ p ^ (E v + 1) = 0 := by
    refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · rw [hgdef, hEdef, Fin.append_left, Fin.append_left]; exact hx_pow j
    · rw [hgdef, hEdef, Fin.append_right, Fin.append_right, zero_add, pow_one]; exact hz_pow i

  have hspan : Submodule.span k (Set.range fun v => cl k H (g v)) = ⊤ := by
    set G := Submodule.span k (Set.range fun v => cl k H (g v)) with hGdef
    have hUG : U ≤ G := Submodule.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span ⟨Fin.castAdd t j, ?_⟩
      change cl k H (g (Fin.castAdd t j)) = cl k H (x j)
      rw [hgdef, Fin.append_left])
    have hWG : W ≤ G := by
      have hb : ∀ i, (bW i : (augI k H).Cotangent) ∈ G := fun i => by
        rw [← hzpre i, show zpre i = z i + Qt i by rw [hzdef]; exact (sub_add_cancel _ _).symm,
          map_add]
        refine G.add_mem (Submodule.subset_span ⟨Fin.natAdd s i, ?_⟩) (hUG (hQtU i))
        change cl k H (g (Fin.natAdd s i)) = cl k H (z i)
        rw [hgdef, Fin.append_right]
      intro w hw
      have hw' : (⟨w, hw⟩ : W) ∈ Submodule.span k (Set.range bW) := by
        rw [bW.span_eq]; exact Submodule.mem_top
      have := Submodule.mem_map_of_mem (f := W.subtype) hw'
      rw [Submodule.map_span, ← Set.range_comp] at this
      refine (Submodule.span_le.2 ?_) this
      rintro _ ⟨i, rfl⟩
      exact hb i
    rw [eq_top_iff, ← hUW.sup_eq_top]
    exact sup_le hUG hWG

  set Φ : MvPolynomial (Fin (s + t)) k →ₐ[k] H := MvPolynomial.aeval g with hΦdef
  have hΦX : ∀ v, Φ (X v) = g v := fun v => MvPolynomial.aeval_X g v
  have hΦK : ∀ a ∈ Kp k p (s + t) E, Φ a = 0 := by
    intro a ha
    refine (Ideal.span_le (I := RingHom.ker Φ)).2 ?_ ha
    rintro _ ⟨v, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, hΦX]
    exact hg_pow v
  have hΦsurj : Function.Surjective Φ := by
    rw [← AlgHom.range_eq_top]
    refine eq_top_of_forall_exists_sub_mem_sq Φ.range (augI k H) (isNilpotent_augI hH)
      (fun h => ⟨Coalgebra.counit (R := k) h, sub_algebraMap_counit_mem h⟩) (fun h hh => ?_)
    have hmem : cl k H h ∈ Submodule.span k (Set.range fun v => cl k H (g v)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hmem
    have htI : (∑ v, c v • g v : H) ∈ augI k H :=
      Submodule.sum_mem _ fun v _ => Submodule.smul_of_tower_mem _ _ (mem_augI.2 (hgI v))
    refine ⟨∑ v, c v • g v, Subalgebra.sum_mem _ fun v _ =>
      Subalgebra.smul_mem _ ((AlgHom.mem_range _).2 ⟨X v, hΦX v⟩) _, htI, ?_⟩
    rw [← cl_eq_zero_iff_of_mem (sub_mem hh htI), map_sub, map_sum, sub_eq_zero, ← hc]
    exact Finset.sum_congr rfl fun v _ => (map_smul _ _ _).symm
  set Φb : (MvPolynomial (Fin (s + t)) k ⧸ Kp k p (s + t) E) →ₐ[k] H :=
    Ideal.Quotient.liftₐ (Kp k p (s + t) E) Φ hΦK with hΦbdef
  have hΦb_surj : Function.Surjective Φb := fun h => by
    obtain ⟨P, rfl⟩ := hΦsurj h
    exact ⟨Ideal.Quotient.mk _ P, rfl⟩

  have hORD := HopfAlgebra.finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent k H hH
    (frobSub k p H) hS.comul_mem hS.antipode_mem
  have hFK : Module.finrank k
      (H ⧸ Ideal.span {x : H | x ∈ frobSub k p H ∧ Coalgebra.counit (R := k) x = 0}) =
      p ^ Module.finrank k (augI k H).Cotangent := by
    rw [setOf_mem_frobSub_eq_image]
    exact HopfAlgebra.finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent k p H
  have hdimS : Module.finrank k ↥(frobSub k p H) = ∏ j, p ^ (f j + 1) :=
    ψ.toLinearEquiv.finrank_eq.trans
      (MvPolynomial.finrank_quotient_span_range_X_pow_eq_prod k fun j => p ^ (f j + 1))
  have hdimQ : Module.finrank k (MvPolynomial (Fin (s + t)) k ⧸ Kp k p (s + t) E) =
      ∏ v, p ^ (E v + 1) :=
    MvPolynomial.finrank_quotient_span_range_X_pow_eq_prod k fun v => p ^ (E v + 1)
  have hδ : Module.finrank k (augI k H).Cotangent = s + t := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hUW.sup_eq_top, hUW.inf_eq_bot, finrank_top, finrank_bot, add_zero, hfinU] at h
    exact h
  have hdim : Module.finrank k (MvPolynomial (Fin (s + t)) k ⧸ Kp k p (s + t) E) =
      Module.finrank k H := by
    rw [hdimQ, hORD, hFK, hdimS, hδ, Fin.prod_univ_add]
    have hl : ∀ j : Fin s, p ^ (E (Fin.castAdd t j) + 1) = p ^ (f j + 1) * p := fun j => by
      rw [hEdef, Fin.append_left, pow_succ]
    have hr : ∀ i : Fin t, p ^ (E (Fin.natAdd s i) + 1) = p := fun i => by
      rw [hEdef, Fin.append_right, zero_add, pow_one]
    simp_rw [hl, hr]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin, pow_add, mul_assoc]

  have hΦb_inj : Function.Injective Φb := by
    haveI : Module.Finite k (MvPolynomial (Fin (s + t)) k ⧸ Kp k p (s + t) E) :=
      Module.finite_of_finrank_pos (by rw [hdim]; exact Module.finrank_pos)
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := Φb.toLinearMap)).2 hΦb_surj
  exact ⟨s + t, E, ⟨(AlgEquiv.ofBijective Φb ⟨hΦb_inj, hΦb_surj⟩).symm⟩⟩

end Step

section Main

variable {k : Type u} [Field k] [PerfectField k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

theorem base {H : Type v} [CommRing H] [HopfAlgebra k H]
    (hI : ∀ x : H, Coalgebra.counit (R := k) x = 0 → x = 0) :
    ∃ (d : ℕ) (e : Fin d → ℕ), Nonempty (H ≃ₐ[k] (MvPolynomial (Fin d) k ⧸ Kp k p d e)) := by
  refine ⟨0, Fin.elim0, ⟨?_⟩⟩

  have hbij : Function.Bijective (Bialgebra.counitAlgHom k H) := by
    refine ⟨fun a b h => ?_, fun c => ⟨algebraMap k H c, counit_algebraMap c⟩⟩
    rw [← sub_eq_zero]
    refine hI _ ?_
    rw [map_sub, sub_eq_zero]
    exact h
  refine (AlgEquiv.ofBijective _ hbij).trans ((MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.trans ?_)

  have hbot : Kp k p 0 Fin.elim0 = RingHom.ker (AlgHom.id k (MvPolynomial (Fin 0) k)) := by
    rw [Kp, Set.range_eq_empty, Ideal.span_empty, eq_comm]
    exact (RingHom.injective_iff_ker_eq_bot _).1 fun a b h => h
  exact ((Ideal.quotientEquivAlgOfEq k hbot).trans
    (Ideal.quotientKerAlgEquivOfSurjective fun a => ⟨a, rfl⟩)).symm

theorem main (n : ℕ) : ∀ (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H],
    (∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x) → Module.finrank k H ≤ n →
    ∃ (d : ℕ) (e : Fin d → ℕ), Nonempty (H ≃ₐ[k] (MvPolynomial (Fin d) k ⧸ Kp k p d e)) := by
  induction n with
  | zero =>
    intro H _ _ _ hH hle
    haveI : Nontrivial H := nontrivial (k := k)
    exact absurd hle (not_le.2 Module.finrank_pos)
  | succ n ih =>
    intro H _ _ _ hH hle
    by_cases hne : ∃ x : H, Coalgebra.counit (R := k) x = 0 ∧ x ≠ 0
    ·
      have hS : IsHopfSubalgebra k (frobSub k p H) := isHopfSubalgebra_frobSub
      letI : HopfAlgebra k ↥(frobSub k p H) := hS.hopfAlgebra
      have hSnil : ∀ w : ↥(frobSub k p H), Coalgebra.counit (R := k) w = 0 → IsNilpotent w := by
        intro w hw
        obtain ⟨N, hN⟩ := hH (w : H) hw
        exact ⟨N, Subtype.ext (by rw [SubmonoidClass.coe_pow, hN]; rfl)⟩
      have hlt : Module.finrank k ↥(frobSub k p H) < Module.finrank k H := finrank_frobSub_lt hH hne
      obtain ⟨s, f, ⟨ψ⟩⟩ := ih ↥(frobSub k p H) hSnil (by omega)
      exact step hH ψ
    · exact base fun x hx => by_contra fun h => hne ⟨x, hx, h⟩

end Main

end HopfAlgebra.InfinitesimalStructure
p2m_reactivate "P2MW.S_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent.HopfAlgebra P2MW.S_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent.HopfAlgebra.InfinitesimalStructure"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent.HopfAlgebra"

theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
    (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x) :
    ∃ (d : ℕ) (e : Fin d → ℕ), Nonempty (H ≃ₐ[k] (MvPolynomial (Fin d) k ⧸
      Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ p ^ (e i + 1)))) :=
  HopfAlgebra.InfinitesimalStructure.main (Module.finrank k H) H hH le_rfl

end
end S_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent
end P2MW
export P2MW.S_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent (solution)

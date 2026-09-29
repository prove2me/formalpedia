-- Prove2me | solution 1 for HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2a2f04df-4ca5-5b46-929a-b4c84a64b0e5

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal

namespace CRe38c79ac

section Abstract

variable {O : Type*} [CommRing O] {A : Type*} [Ring A] {ι : Type*}
  (ev : A →+ (ι → O)) (ℓ : ℕ)

private def D (N : ℕ) (F : A) : Prop := ∀ i, ((ℓ : O) ^ N) ∣ ev F i

variable {ev ℓ}

private theorem D_zero_left (F : A) : D ev ℓ 0 F := fun i => by simp

private theorem D_zero (N : ℕ) : D ev ℓ N (0 : A) := fun i => by simp

private theorem D_add {N : ℕ} {F G : A} (hF : D ev ℓ N F) (hG : D ev ℓ N G) : D ev ℓ N (F + G) :=
  fun i => by simpa [map_add] using dvd_add (hF i) (hG i)

private theorem D_neg {N : ℕ} {F : A} (hF : D ev ℓ N F) : D ev ℓ N (-F) :=
  fun i => by simpa [map_neg] using (hF i)

private theorem D_sub {N : ℕ} {F G : A} (hF : D ev ℓ N F) (hG : D ev ℓ N G) : D ev ℓ N (F - G) := by
  simpa [sub_eq_add_neg] using D_add hF (D_neg hG)

private theorem D_mono {M N : ℕ} (h : M ≤ N) {F : A} (hF : D ev ℓ N F) : D ev ℓ M F :=
  fun i => (pow_dvd_pow _ h).trans (hF i)

private theorem D_sum {N : ℕ} {κ : Type*} (s : Finset κ) (f : κ → A)
    (hf : ∀ j ∈ s, D ev ℓ N (f j)) : D ev ℓ N (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using D_zero N
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact D_add (hf a (by simp)) (ih fun j hj => hf j (by simp [hj]))

private theorem ev_mul_natCast (F : A) (c : ℕ) (i : ι) : ev (F * (c : A)) i = (c : O) * ev F i := by
  induction c with
  | zero => simp
  | succ c ih => simp [Nat.cast_succ, mul_add, add_mul, ih, map_add]

private theorem D_mul_natCast_of_dvd {N : ℕ} {F : A} (hF : D ev ℓ N F) {c : ℕ} (hc : ℓ ∣ c) :
    D ev ℓ (N + 1) (F * (c : A)) := fun i => by
  rw [ev_mul_natCast, pow_succ, mul_comm ((c : O))]
  exact mul_dvd_mul (hF i) (Nat.cast_dvd_cast hc)

private theorem D_mul_ell {N : ℕ} {F : A} (hF : D ev ℓ N F) : D ev ℓ (N + 1) (F * (ℓ : A)) :=
  D_mul_natCast_of_dvd hF dvd_rfl

private theorem D_mul_ell_pow {N : ℕ} {F : A} (hF : D ev ℓ N F) (m : ℕ) :
    D ev ℓ (N + m) (F * (ℓ : A) ^ m) := by
  induction m with
  | zero => simpa using hF
  | succ m ih =>
    have e : F * (ℓ : A) ^ (m + 1) = F * (ℓ : A) ^ m * (ℓ : A) := by rw [pow_succ, mul_assoc]
    rw [e, show N + (m + 1) = N + m + 1 from rfl]
    exact D_mul_ell ih

private theorem ev_mul_ell_pow (F : A) (m : ℕ) (i : ι) :
    ev (F * (ℓ : A) ^ m) i = ((ℓ : O)) ^ m * ev F i := by
  rw [← Nat.cast_pow, ev_mul_natCast, Nat.cast_pow]

variable (hmul : ∀ (a b : ℕ) (F G : A), D ev ℓ a F → D ev ℓ b G → D ev ℓ (a + b) (F * G))
include hmul

private theorem D_pow {n : ℕ} {F : A} (hF : D ev ℓ n F) (j : ℕ) : D ev ℓ (n * j) (F ^ j) := by
  induction j with
  | zero => simpa using D_zero_left (ev := ev) (ℓ := ℓ) (1 : A)
  | succ j ih =>
    rw [pow_succ, Nat.mul_succ]
    exact hmul _ _ _ _ ih hF

private theorem level (hp : ℓ.Prime) (h3 : 3 ≤ ℓ) {n : ℕ} (hn : 1 ≤ n) {Y : A} (hY : D ev ℓ n Y) :
    D ev ℓ (n + 2) ((1 + Y) ^ ℓ - 1 - Y * (ℓ : A)) := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 + 1 + 1 := ⟨ℓ - 3, by omega⟩
  have hexp : (1 + Y) ^ (m + 1 + 1 + 1) - 1 - Y * ((m + 1 + 1 + 1 : ℕ) : A)
      = (∑ j ∈ Finset.range (m + 1),
          Y ^ (j + 1 + 1) * (((m + 1 + 1 + 1).choose (j + 1 + 1) : ℕ) : A))
        + Y ^ (m + 1 + 1 + 1) := by
    rw [add_comm (1 : A) Y, (Commute.one_right Y).add_pow, Finset.sum_range_succ',
      Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, pow_zero, pow_one, zero_add]
    abel
  rw [hexp]
  refine D_add (D_sum _ _ fun j hj => ?_) ?_
  · have hjm : j < m + 1 := Finset.mem_range.mp hj
    have hdvd : (m + 1 + 1 + 1) ∣ (m + 1 + 1 + 1).choose (j + 1 + 1) :=
      hp.dvd_choose_self (by omega) (by omega)
    have h1 := D_mul_natCast_of_dvd (D_pow hmul hY (j + 1 + 1)) hdvd
    refine D_mono ?_ h1
    nlinarith [Nat.zero_le (n * j)]
  · refine D_mono ?_ (D_pow hmul hY (m + 1 + 1 + 1))
    nlinarith [Nat.zero_le (n * m)]

private theorem iter (hp : ℓ.Prime) (h3 : 3 ≤ ℓ) {n : ℕ} (hn : 1 ≤ n) {Y : A} (hY : D ev ℓ n Y) (m : ℕ) :
    D ev ℓ (n + m + 1) ((1 + Y) ^ (ℓ ^ m) - 1 - Y * (ℓ : A) ^ m) := by
  induction m with
  | zero => simpa using D_zero (ev := ev) (ℓ := ℓ) (n + 0 + 1)
  | succ m ih =>
    have hYm' : D ev ℓ (n + m) ((1 + Y) ^ (ℓ ^ m) - 1) := by
      have h1 : D ev ℓ (n + m) (Y * (ℓ : A) ^ m) := D_mul_ell_pow hY m
      have h2 : D ev ℓ (n + m) ((1 + Y) ^ (ℓ ^ m) - 1 - Y * (ℓ : A) ^ m) := D_mono (by omega) ih
      simpa using D_add h2 h1
    have hlev := level hmul hp h3 (n := n + m) (by omega) hYm'
    have hrest := D_mul_ell ih
    have e2 : Y * (ℓ : A) ^ m * (ℓ : A) = Y * (ℓ : A) ^ (m + 1) := by rw [mul_assoc, ← pow_succ]
    have e1 : (1 + ((1 + Y) ^ (ℓ ^ m) - 1)) = (1 + Y) ^ (ℓ ^ m) := by abel
    have key : (1 + Y) ^ ℓ ^ (m + 1) - 1 - Y * (ℓ : A) ^ (m + 1)
        = ((1 + ((1 + Y) ^ (ℓ ^ m) - 1)) ^ ℓ - 1 - ((1 + Y) ^ (ℓ ^ m) - 1) * (ℓ : A))
          + ((1 + Y) ^ (ℓ ^ m) - 1 - Y * (ℓ : A) ^ m) * (ℓ : A) := by
      rw [e1, ← pow_mul, ← pow_succ]
      simp only [sub_mul, one_mul, e2]
      abel
    rw [key]
    exact D_add (D_mono (by omega) hlev) (D_mono (by omega) hrest)

private theorem all_levels [IsDomain O] (hp : ℓ.Prime) (h3 : 3 ≤ ℓ) (hℓ0 : ((ℓ : O)) ≠ 0) {Y : A}
    (h1 : D ev ℓ 1 Y) (k : ℕ) (hk : (1 + Y) ^ (ℓ ^ k) = 1) (N : ℕ) : D ev ℓ N Y := by
  have step : ∀ n, 1 ≤ n → D ev ℓ n Y → D ev ℓ (n + 1) Y := by
    intro n hn hY i
    have h := iter hmul hp h3 hn hY k
    rw [hk, sub_self, zero_sub] at h
    have h' : ((ℓ : O)) ^ (n + k + 1) ∣ ev (Y * (ℓ : A) ^ k) i := by simpa using (D_neg h) i
    rw [ev_mul_ell_pow, show n + k + 1 = k + (n + 1) by omega, pow_add] at h'
    exact (mul_dvd_mul_iff_left (pow_ne_zero k hℓ0)).mp h'
  induction N with
  | zero => exact D_zero_left (ev := ev) (ℓ := ℓ) Y
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact h1
    · exact step N hN ih

end Abstract

end CRe38c79ac

namespace CRe38c79ac

section Concrete

open WithConv

variable (O : Type*) [CommRing O] (H : Type*) [CommRing H] [Bialgebra O H]

private def evH : WithConv (H →ₗ[O] O) →+ (H → O) where
  toFun F := ⇑F.ofConv
  map_zero' := by funext h; simp
  map_add' F G := by funext h; simp

@[scoped simp] private theorem evH_apply (F : WithConv (H →ₗ[O] O)) (h : H) : evH O H F h = F.ofConv h := rfl

private theorem hmulH (ℓ : ℕ) : ∀ (a b : ℕ) (F G : WithConv (H →ₗ[O] O)),
    D (evH O H) ℓ a F → D (evH O H) ℓ b G → D (evH O H) ℓ (a + b) (F * G) := by
  intro a b F G hF hG h
  show ((ℓ : O)) ^ (a + b) ∣ (F * G).ofConv h
  have e : (F * G).ofConv h
      = LinearMap.mul' O O (TensorProduct.map F.ofConv G.ofConv (CoalgebraStruct.comul h)) := by
    first
    | exact LinearMap.convMul_apply F G h
    | rfl
  rw [e]
  induction (CoalgebraStruct.comul (R := O) h) using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simpa [pow_add] using mul_dvd_mul (hF u) (hG v)
  | add s t hs ht => simpa [map_add] using dvd_add hs ht

private theorem core [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (X : WithConv (H →ₗ[O] O))
    (hx1 : ∀ h : H, X h - algebraMap O O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O)
    (k : ℕ) (hxk : X ^ ℓ ^ k = 1) :
    X = 1 := by
  classical
  have hp : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hp.two_le; omega
  have hℓ0 : ((ℓ : ℕ) : O) ≠ 0 := hunif.ne_zero
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {((ℓ : ℕ) : O)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hunif
  have hk' : (1 + (X - 1)) ^ (ℓ ^ k) = 1 := by rwa [add_sub_cancel]
  have h1 : D (evH O H) ℓ 1 (X - 1) := by
    intro h
    have := hx1 h
    rw [hmax, Ideal.mem_span_singleton] at this
    first
    | simpa using this
    | (change ((ℓ : ℕ) : O) ^ 1 ∣ (X - 1).ofConv h
       rw [pow_one, WithConv.ofConv_sub, LinearMap.sub_apply]
       exact this)
  have hall := all_levels (hmulH O H ℓ) hp h3 hℓ0 h1 k hk'
  have hY0 : ∀ h, X.ofConv h - algebraMap O O (Coalgebra.counit h) = 0 := by
    intro h
    have hdiv : ∀ N, ((ℓ : ℕ) : O) ^ N ∣ X.ofConv h - algebraMap O O (Coalgebra.counit h) := by
      intro N
      first
      | simpa using hall N h
      | (have hN := hall N h
         change ((ℓ : ℕ) : O) ^ N ∣ (X - 1).ofConv h at hN
         rw [WithConv.ofConv_sub, LinearMap.sub_apply] at hN
         exact hN)
    by_contra hne
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hunif
    have hd : ((ℓ : ℕ) : O) ^ n * ((ℓ : ℕ) : O) ∣ ((ℓ : ℕ) : O) ^ n * 1 := by
      rw [← pow_succ, mul_one]
      exact (hdiv (n + 1)).trans hn.dvd
    exact hunif.not_isUnit
      (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n hℓ0)).mp hd))
  ext h
  first
  | (rw [LinearMap.convOne_apply]; exact sub_eq_zero.mp (hY0 h))
  | exact sub_eq_zero.mp (hY0 h)

end Concrete

end CRe38c79ac
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal.CRe38c79ac"

open WithConv in

theorem solution
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H] [Coalgebra.IsCocomm O H]
    (x : WithConv (H →ₐ[O] O))
    (hx1 : ∀ h : H, x h - algebraMap O O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O)
    (k : ℕ) (hxk : x ^ ℓ ^ k = 1) :
    x = 1 := by

  have hX : (toConv x.ofConv.toLinearMap : WithConv (H →ₗ[O] O)) ^ ℓ ^ k = 1 := by
    rw [← AlgHom.toLinearMap_convPow, hxk, AlgHom.toLinearMap_convOne]
  have hx1' : ∀ h : H, (toConv x.ofConv.toLinearMap : WithConv (H →ₗ[O] O)) h
      - algebraMap O O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O := fun h => hx1 h
  have hcore := CRe38c79ac.core O H ℓ hℓ2 hunif (toConv x.ofConv.toLinearMap) hx1' k hX
  have hval : ∀ h : H, x.ofConv h = algebraMap O O (Coalgebra.counit h) := fun h => by
    have e := congrArg (fun F : WithConv (H →ₗ[O] O) => F.ofConv h) hcore
    first
    | simpa only [LinearMap.convOne_apply, AlgHom.toLinearMap_apply] using e
    | simpa using e
    | exact e
  ext h
  first
  | (rw [AlgHom.convOne_apply]; exact hval h)
  | exact hval h

end S_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
end P2MW
export P2MW.S_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal (solution)

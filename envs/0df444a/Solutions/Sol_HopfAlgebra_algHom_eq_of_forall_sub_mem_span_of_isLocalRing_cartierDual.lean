-- Prove2me | solution 1 for HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ba7195ed-053a-5463-93e7-9e91d2422c33

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual

set_option autoImplicit false

open WithConv TensorProduct

namespace FontaineStepOneUnipotent

section Filt

variable {Y : Type*} [CommRing Y] (ℓ : ℕ)

def Filt (n : ℕ) (y : Y) : Prop := ∃ z : Y, y = (ℓ : Y) ^ n * z

variable {ℓ}

lemma Filt.zero_right (n : ℕ) : Filt ℓ n (0 : Y) := ⟨0, by simp⟩

lemma Filt.level_zero (y : Y) : Filt ℓ 0 y := ⟨y, by simp⟩

lemma Filt.add {n : ℕ} {y y' : Y} (hy : Filt ℓ n y) (hy' : Filt ℓ n y') : Filt ℓ n (y + y') := by
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨z', rfl⟩ := hy'
  exact ⟨z + z', by ring⟩

lemma Filt.neg {n : ℕ} {y : Y} (hy : Filt ℓ n y) : Filt ℓ n (-y) := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨-z, by ring⟩

lemma Filt.sub {n : ℕ} {y y' : Y} (hy : Filt ℓ n y) (hy' : Filt ℓ n y') : Filt ℓ n (y - y') := by
  rw [sub_eq_add_neg]; exact hy.add hy'.neg

lemma Filt.mul {a b : ℕ} {y y' : Y} (hy : Filt ℓ a y) (hy' : Filt ℓ b y') :
    Filt ℓ (a + b) (y * y') := by
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨z', rfl⟩ := hy'
  exact ⟨z * z', by ring⟩

lemma Filt.mono {a b : ℕ} (hab : a ≤ b) {y : Y} (hy : Filt ℓ b y) : Filt ℓ a y := by
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact ⟨(ℓ : Y) ^ c * z, by ring⟩

lemma Filt.natCast_mul {a : ℕ} (n : ℕ) {y : Y} (hy : Filt ℓ a y) : Filt ℓ a ((n : Y) * y) := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨(n : Y) * z, by ring⟩

lemma Filt.self_mul {a : ℕ} {y : Y} (hy : Filt ℓ a y) : Filt ℓ (a + 1) ((ℓ : Y) * y) := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨z, by ring⟩

lemma Filt.natCast_mul_of_dvd {a n : ℕ} (hn : ℓ ∣ n) {y : Y} (hy : Filt ℓ a y) :
    Filt ℓ (a + 1) ((n : Y) * y) := by
  obtain ⟨c, rfl⟩ := hn
  rw [Nat.cast_mul, mul_assoc]
  exact (hy.natCast_mul c).self_mul

end Filt

section Conv

variable {O : Type*} [CommRing O] {H : Type*} [AddCommMonoid H] [Module O H]
  {Y : Type*} [CommRing Y] [Algebra O Y] (ℓ : ℕ)

def InFilt (n : ℕ) (f : WithConv (H →ₗ[O] Y)) : Prop := ∀ h : H, Filt ℓ n (f h)

variable {ℓ}

lemma InFilt.level_zero (f : WithConv (H →ₗ[O] Y)) : InFilt ℓ 0 f := fun _ ↦ Filt.level_zero _

lemma InFilt.zero (n : ℕ) : InFilt ℓ n (0 : WithConv (H →ₗ[O] Y)) := fun _ ↦ Filt.zero_right n

lemma InFilt.add {n : ℕ} {f g : WithConv (H →ₗ[O] Y)} (hf : InFilt ℓ n f) (hg : InFilt ℓ n g) :
    InFilt ℓ n (f + g) := fun h ↦ (hf h).add (hg h)

lemma InFilt.neg {n : ℕ} {f : WithConv (H →ₗ[O] Y)} (hf : InFilt ℓ n f) : InFilt ℓ n (-f) :=
  fun h ↦ (hf h).neg

lemma InFilt.sub {n : ℕ} {f g : WithConv (H →ₗ[O] Y)} (hf : InFilt ℓ n f) (hg : InFilt ℓ n g) :
    InFilt ℓ n (f - g) := fun h ↦ (hf h).sub (hg h)

lemma InFilt.mono {a b : ℕ} (hab : a ≤ b) {f : WithConv (H →ₗ[O] Y)} (hf : InFilt ℓ b f) :
    InFilt ℓ a f := fun h ↦ (hf h).mono hab

lemma InFilt.sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → WithConv (H →ₗ[O] Y))
    (hF : ∀ i ∈ s, InFilt ℓ n (F i)) : InFilt ℓ n (∑ i ∈ s, F i) :=
  Finset.sum_induction F (InFilt ℓ n) (fun _ _ ha hb ↦ ha.add hb) (InFilt.zero n) hF

variable [Coalgebra O H]

lemma InFilt.mul {a b : ℕ} {f g : WithConv (H →ₗ[O] Y)} (hf : InFilt ℓ a f) (hg : InFilt ℓ b g) :
    InFilt ℓ (a + b) (f * g) := by
  intro h
  change Filt ℓ (a + b) ((f * g).ofConv h)
  rw [LinearMap.convMul_apply]
  induction (CoalgebraStruct.comul (R := O) h) using TensorProduct.induction_on with
  | zero => simpa using Filt.zero_right (ℓ := ℓ) (Y := Y) (a + b)
  | tmul p q =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    exact (hf p).mul (hg q)
  | add s t hs ht =>
    rw [map_add, map_add]
    exact hs.add ht

lemma InFilt.pow {a : ℕ} {f : WithConv (H →ₗ[O] Y)} (hf : InFilt ℓ a f) :
    ∀ n : ℕ, InFilt ℓ (n * a) (f ^ n)
  | 0 => by simpa using InFilt.level_zero (ℓ := ℓ) (1 : WithConv (H →ₗ[O] Y))
  | n + 1 => by
    rw [pow_succ, Nat.succ_mul]
    exact (hf.pow n).mul hf

lemma natCast_mul_apply (n : ℕ) (f : WithConv (H →ₗ[O] Y)) (h : H) :
    ((n : WithConv (H →ₗ[O] Y)) * f) h = (n : Y) * f h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Nat.cast_succ, add_mul, one_mul, ← ih]
    rfl

lemma InFilt.natCast_mul {a : ℕ} (n : ℕ) {f : WithConv (H →ₗ[O] Y)} (hf : InFilt ℓ a f) :
    InFilt ℓ a ((n : WithConv (H →ₗ[O] Y)) * f) := fun h ↦ by
  rw [natCast_mul_apply]; exact (hf h).natCast_mul n

lemma InFilt.natCast_mul_of_dvd {a n : ℕ} (hn : ℓ ∣ n) {f : WithConv (H →ₗ[O] Y)}
    (hf : InFilt ℓ a f) : InFilt ℓ (a + 1) ((n : WithConv (H →ₗ[O] Y)) * f) := fun h ↦ by
  rw [natCast_mul_apply]; exact (hf h).natCast_mul_of_dvd hn

lemma InFilt.pow_sub_one {y : WithConv (H →ₗ[O] Y)} (hy : InFilt ℓ 1 (y - 1)) :
    ∀ n : ℕ, InFilt ℓ 1 (y ^ n - 1)
  | 0 => by simpa using InFilt.zero (ℓ := ℓ) (H := H) (O := O) (Y := Y) 1
  | n + 1 => by
    have e : y ^ (n + 1) - 1 = (y ^ n - 1) * y + (y - 1) := by
      rw [pow_succ, sub_mul, one_mul, sub_add_sub_cancel]
    rw [e]
    exact ((hy.pow_sub_one n).mul (InFilt.level_zero y)).add hy

lemma sum_range_eq_add_add_sum {M : Type*} [AddCommMonoid M] (F : ℕ → M) (q : ℕ) :
    ∑ j ∈ Finset.range (q + 2 + 1), F j = F 0 + F 1 + ∑ k ∈ Finset.range (q + 1), F (k + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [zero_add]
  abel

lemma InFilt.succ_of_pow_eq_one (hℓ : ℓ.Prime)
    (htf : ∀ v : Y, (ℓ : Y) * v = 0 → v = 0)
    {y : WithConv (H →ₗ[O] Y)} (hy : y ^ ℓ = 1) {m : ℕ} (hm : 1 ≤ m) (hℓm : 3 ≤ ℓ ∨ 2 ≤ m)
    (hN : InFilt ℓ m (y - 1)) : InFilt ℓ (m + 1) (y - 1) := by
  set N : WithConv (H →ₗ[O] Y) := y - 1 with hNdef
  have hyN : y = N + 1 := by rw [hNdef, sub_add_cancel]
  obtain ⟨q, rfl⟩ : ∃ q, ℓ = q + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩

  have hbin := (Commute.one_right N).add_pow (q + 2)
  simp only [one_pow, mul_one] at hbin
  rw [← hyN, hy, sum_range_eq_add_add_sum] at hbin
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_one,
    Nat.choose_one_right] at hbin

  set S := ∑ k ∈ Finset.range (q + 1), N ^ (k + 2) * ((q + 2).choose (k + 2) : WithConv (H →ₗ[O] Y))
    with hSdef
  have hS : InFilt (q + 2) (m + 2) S := by
    refine InFilt.sum _ _ fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    rw [← Nat.cast_comm]
    rcases Nat.lt_or_ge (k + 2) (q + 2) with hlt | hge
    ·
      have hdvd : q + 2 ∣ (q + 2).choose (k + 2) := hℓ.dvd_choose_self (by omega) hlt
      have hpow : InFilt (q + 2) ((k + 2) * m) (N ^ (k + 2)) := hN.pow (k + 2)
      exact (hpow.natCast_mul_of_dvd hdvd).mono (by nlinarith)
    ·
      have hpow : InFilt (q + 2) ((k + 2) * m) (N ^ (k + 2)) := hN.pow (k + 2)
      refine (hpow.natCast_mul _).mono ?_
      rcases hℓm with h3 | h2 <;> nlinarith

  have hℓN : ((q + 2 : ℕ) : WithConv (H →ₗ[O] Y)) * N = -S := by
    rw [Nat.cast_comm]
    have : N * ((q + 2 : ℕ) : WithConv (H →ₗ[O] Y)) + S = 0 := by
      have h1 := hbin
      rw [add_assoc] at h1
      exact left_eq_add.mp h1
    exact eq_neg_of_add_eq_zero_left this
  have hℓN' : InFilt (q + 2) (m + 2) (((q + 2 : ℕ) : WithConv (H →ₗ[O] Y)) * N) := by
    rw [hℓN]; exact hS.neg

  intro h
  obtain ⟨z, hz⟩ := hℓN' h
  rw [natCast_mul_apply] at hz
  refine ⟨z, sub_eq_zero.mp (htf _ ?_)⟩
  rw [mul_sub, hz]
  push_cast
  ring

lemma InFilt.succ_of_pow_eq_one' (hℓ : ℓ.Prime)
    (htf : ∀ v : Y, (ℓ : Y) * v = 0 → v = 0)
    {y : WithConv (H →ₗ[O] Y)} (hy : y ^ ℓ = 1) {m : ℕ} (hm : 1 ≤ m)
    (hcorner : ℓ = 2 → y ^ 2 = 1 → InFilt ℓ 1 (y - 1) → InFilt ℓ 2 (y - 1))
    (hN : InFilt ℓ m (y - 1)) : InFilt ℓ (m + 1) (y - 1) := by
  by_cases hcase : 3 ≤ ℓ ∨ 2 ≤ m
  · exact hN.succ_of_pow_eq_one hℓ htf hy hm hcase
  · push Not at hcase
    have hℓ2 : ℓ = 2 := by have := hℓ.two_le; omega
    have hm1 : m = 1 := by omega
    subst hm1
    exact hcorner hℓ2 (by rw [← hℓ2]; exact hy) hN

lemma InFilt.forall_of_pow_eq_one (hℓ : ℓ.Prime)
    (htf : ∀ v : Y, (ℓ : Y) * v = 0 → v = 0)
    {y : WithConv (H →ₗ[O] Y)} (hy : y ^ ℓ = 1) (h1 : InFilt ℓ 1 (y - 1))
    (hcorner : ℓ = 2 → y ^ 2 = 1 → InFilt ℓ 1 (y - 1) → InFilt ℓ 2 (y - 1)) :
    ∀ m : ℕ, InFilt ℓ (m + 1) (y - 1)
  | 0 => h1
  | m + 1 => (InFilt.forall_of_pow_eq_one hℓ htf hy h1 hcorner m).succ_of_pow_eq_one' hℓ htf hy
      (Nat.succ_pos m) hcorner

lemma eq_one_of_pow_prime_eq_one (hℓ : ℓ.Prime)
    (htf : ∀ v : Y, (ℓ : Y) * v = 0 → v = 0)
    (hsep : ∀ v : Y, (∀ m : ℕ, Filt ℓ m v) → v = 0)
    {y : WithConv (H →ₗ[O] Y)} (hy : y ^ ℓ = 1) (h1 : InFilt ℓ 1 (y - 1))
    (hcorner : ℓ = 2 → y ^ 2 = 1 → InFilt ℓ 1 (y - 1) → InFilt ℓ 2 (y - 1)) : y = 1 := by
  have hall := InFilt.forall_of_pow_eq_one hℓ htf hy h1 hcorner
  have hzero : y - 1 = 0 := by
    refine WithConv.ext (LinearMap.ext fun h ↦ ?_)
    change (y - 1) h = 0
    exact hsep _ fun m ↦ (hall m h).mono (Nat.le_succ m)
  exact sub_eq_zero.mp hzero

lemma eq_one_of_pow_prime_pow_eq_one (hℓ : ℓ.Prime)
    (htf : ∀ v : Y, (ℓ : Y) * v = 0 → v = 0)
    (hsep : ∀ v : Y, (∀ m : ℕ, Filt ℓ m v) → v = 0)
    (P : WithConv (H →ₗ[O] Y) → Prop) (hP : ∀ w, P w → ∀ n : ℕ, P (w ^ n))
    (hcorner : ∀ w, P w → ℓ = 2 → w ^ 2 = 1 → InFilt ℓ 1 (w - 1) → InFilt ℓ 2 (w - 1))
    {y : WithConv (H →ₗ[O] Y)} (hPy : P y) (h1 : InFilt ℓ 1 (y - 1)) :
    ∀ k : ℕ, y ^ ℓ ^ k = 1 → y = 1
  | 0, hk => by simpa using hk
  | k + 1, hk => by
    rw [pow_succ, pow_mul] at hk
    have hw : y ^ ℓ ^ k = 1 :=
      eq_one_of_pow_prime_eq_one hℓ htf hsep hk (h1.pow_sub_one _) (hcorner _ (hP y hPy _))
    exact eq_one_of_pow_prime_pow_eq_one hℓ htf hsep P hP hcorner hPy h1 k hw

end Conv

section AtOne

variable {O : Type*} [CommSemiring O] {H : Type*} [Semiring H] [Bialgebra O H]
  {Y : Type*} [Semiring Y] [Algebra O Y]

lemma convMul_apply_one (f g : WithConv (H →ₗ[O] Y)) : (f * g) 1 = f 1 * g 1 := by
  rw [LinearMap.convMul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.map_tmul, LinearMap.mul'_apply]

lemma convOne_apply_one : (1 : WithConv (H →ₗ[O] Y)) 1 = 1 := by
  rw [LinearMap.convOne_apply, Bialgebra.counit_one, map_one]

lemma convPow_apply_one {w : WithConv (H →ₗ[O] Y)} (hw : w 1 = 1) : ∀ n : ℕ, (w ^ n) 1 = 1
  | 0 => by rw [pow_zero]; exact convOne_apply_one
  | n + 1 => by rw [pow_succ, convMul_apply_one, convPow_apply_one hw n, hw, one_mul]

end AtOne

section postComp

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {A A' : Type*} [Semiring A] [Algebra R A] [Semiring A'] [Algebra R A']

def postComp (g : A →ₐ[R] A') : WithConv (C →ₗ[R] A) →+* WithConv (C →ₗ[R] A') where
  toFun F := toConv (g.toLinearMap ∘ₗ F.ofConv)
  map_one' := by
    apply WithConv.ext
    ext c
    simp [LinearMap.convOne_def]
  map_mul' F G := by
    apply WithConv.ext
    simpa using LinearMap.algHom_comp_convMul_distrib g F G
  map_zero' := by
    apply WithConv.ext
    simp
  map_add' F G := by
    apply WithConv.ext
    simp [LinearMap.comp_add]

@[scoped simp] lemma postComp_apply_apply (g : A →ₐ[R] A') (F : WithConv (C →ₗ[R] A)) (c : C) :
    postComp g F c = g (F c) := rfl

end postComp

section antipode

variable {R : Type*} [CommSemiring R] {H : Type*} [Semiring H] [HopfAlgebra R H]

lemma id_convMul_antipode :
    toConv (LinearMap.id : H →ₗ[R] H) * toConv (HopfAlgebra.antipode R) = 1 := by
  apply WithConv.ext
  change LinearMap.mul' R H ∘ₗ TensorProduct.map LinearMap.id (HopfAlgebra.antipode R) ∘ₗ
    Coalgebra.comul = _
  exact HopfAlgebra.mul_antipode_lTensor_comul

lemma antipode_convMul_id :
    toConv (HopfAlgebra.antipode R) * toConv (LinearMap.id : H →ₗ[R] H) = 1 := by
  apply WithConv.ext
  change LinearMap.mul' R H ∘ₗ TensorProduct.map (HopfAlgebra.antipode R) LinearMap.id ∘ₗ
    Coalgebra.comul = _
  exact HopfAlgebra.mul_antipode_rTensor_comul

variable {A : Type*} [Semiring A] [Algebra R A]

lemma toLinearMap_convMul_comp_antipode (g : H →ₐ[R] A) :
    toConv g.toLinearMap * toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) = 1 := by
  have h1 : postComp g (toConv (LinearMap.id : H →ₗ[R] H)) = toConv g.toLinearMap := rfl
  have h2 : postComp g (toConv (HopfAlgebra.antipode R)) =
      toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) := rfl
  rw [← h1, ← h2, ← map_mul, id_convMul_antipode, map_one]

lemma comp_antipode_convMul_toLinearMap (g : H →ₐ[R] A) :
    toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) * toConv g.toLinearMap = 1 := by
  have h1 : postComp g (toConv (LinearMap.id : H →ₗ[R] H)) = toConv g.toLinearMap := rfl
  have h2 : postComp g (toConv (HopfAlgebra.antipode R)) =
      toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) := rfl
  rw [← h1, ← h2, ← map_mul, antipode_convMul_id, map_one]

end antipode

section commAntipode

variable {R : Type*} [CommSemiring R] {H : Type*} [CommSemiring H] [HopfAlgebra R H]

def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

variable {A : Type*} [CommSemiring A] [Algebra R A]

lemma point_mul_comp_antipode (g : WithConv (H →ₐ[R] A)) :
    g * toConv (g.ofConv.comp antipodeAlgHom) = 1 := by
  apply toConv_injective.comp (AlgHom.toLinearMap_injective.comp ofConv_injective)
  change toConv (g * toConv (g.ofConv.comp antipodeAlgHom)).ofConv.toLinearMap =
    toConv (1 : WithConv (H →ₐ[R] A)).ofConv.toLinearMap
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  exact toLinearMap_convMul_comp_antipode g.ofConv

lemma comp_antipode_mul_point (g : WithConv (H →ₐ[R] A)) :
    toConv (g.ofConv.comp antipodeAlgHom) * g = 1 := by
  apply toConv_injective.comp (AlgHom.toLinearMap_injective.comp ofConv_injective)
  change toConv (toConv (g.ofConv.comp antipodeAlgHom) * g).ofConv.toLinearMap =
    toConv (1 : WithConv (H →ₐ[R] A)).ofConv.toLinearMap
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  exact comp_antipode_convMul_toLinearMap g.ofConv

end commAntipode

section SpecialFibre

variable {O : Type*} [CommRing O] {k : Type*} [CommRing k] [Algebra O k]
  {Y : Type*} [CommRing Y] [Algebra O Y]

lemma one_tmul_eq_zero_of_mem_span {p : ℕ}
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {(p : O)})
    {y : Y} (hy : y ∈ Ideal.span {(p : Y)}) : (1 : k) ⊗ₜ[O] y = 0 := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hp : algebraMap O k p = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  calc (1 : k) ⊗ₜ[O] (z * (p : Y)) = (1 : k) ⊗ₜ[O] ((p : O) • z) := by
        rw [Algebra.smul_def, map_natCast, mul_comm]
    _ = ((p : O) • (1 : k)) ⊗ₜ[O] z := by rw [tmul_smul, smul_tmul']
    _ = 0 := by rw [← Algebra.algebraMap_eq_smul_one, hp, zero_tmul]

lemma mem_span_of_one_tmul_eq_zero (hk : Function.Surjective (algebraMap O k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {(p : O)})
    {y : Y} (hy : (1 : k) ⊗ₜ[O] y = 0) : y ∈ Ideal.span {(p : Y)} := by
  set J : Ideal Y := Ideal.span {(p : Y)} with hJ
  have hle : RingHom.ker (algebraMap O k) ≤
      RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap O Y)) := by
    intro o ho
    rw [hker] at ho
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ho
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  let κ₀ : k →+* Y ⧸ J := (algebraMap O k).liftOfSurjective hk ⟨_, hle⟩
  have hκ₀ : ∀ o, κ₀ (algebraMap O k o) = Ideal.Quotient.mk J (algebraMap O Y o) := fun o =>
    (algebraMap O k).liftOfRightInverse_comp_apply _ _ ⟨_, hle⟩ o
  let κ : k →ₐ[O] Y ⧸ J :=
    { κ₀ with commutes' := fun o => (hκ₀ o).trans rfl }
  let Ψ : k ⊗[O] Y →ₐ[O] Y ⧸ J :=
    Algebra.TensorProduct.lift κ (Ideal.Quotient.mkₐ O J) fun _ _ => Commute.all _ _
  have : Ψ ((1 : k) ⊗ₜ[O] y) = Ideal.Quotient.mk J y := by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  rw [hy, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

end SpecialFibre

section Unipotent

variable {O : Type*} [CommRing O] {k : Type*} [Field k] [Algebra O k]
variable {H : Type*} [CommRing H] [Bialgebra O H]
variable {Y' : Type*} [CommRing Y'] [Algebra O Y'] [Algebra k Y'] [IsScalarTower O k Y']

lemma mem_maximalIdeal_of_apply_one_eq_zero [Coalgebra.IsCocomm O H] [Module.Finite O H]
    (hloc : IsLocalRing (CartierDual k (k ⊗[O] H))) (φ : CartierDual k (k ⊗[O] H))
    (hφ : φ 1 = 0) : φ ∈ IsLocalRing.maximalIdeal (CartierDual k (k ⊗[O] H)) := by
  haveI := hloc
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨ψ', hψ'⟩ := hu.exists_right_inv
  have h1 := congrArg (fun χ : CartierDual k (k ⊗[O] H) => χ 1) hψ'
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply, CartierDual.one_apply, Bialgebra.counit_one,
    CartierDual.toDual_apply, hφ, zero_mul] at h1
  exact zero_ne_one h1

lemma isNilpotent_maximalIdeal [Coalgebra.IsCocomm O H] [Module.Finite O H]
    (hloc : IsLocalRing (CartierDual k (k ⊗[O] H))) :
    IsNilpotent (IsLocalRing.maximalIdeal (CartierDual k (k ⊗[O] H))) := by
  haveI := hloc
  haveI : IsArtinianRing (CartierDual k (k ⊗[O] H)) :=
    IsArtinianRing.of_finite k (CartierDual k (k ⊗[O] H))
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := CartierDual k (k ⊗[O] H))
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

variable (k Y') in
noncomputable def iotaLin (φ : CartierDual k (k ⊗[O] H)) : H →ₗ[O] Y' :=
  (Algebra.linearMap k Y').restrictScalars O ∘ₗ
    ((CartierDual.toDual k (k ⊗[O] H) φ).restrictScalars O ∘ₗ TensorProduct.mk O k H 1)

lemma iotaLin_apply (φ : CartierDual k (k ⊗[O] H)) (h : H) :
    iotaLin k Y' φ h = algebraMap k Y' (φ ((1 : k) ⊗ₜ[O] h)) := rfl

variable (k Y') in
noncomputable def iota : CartierDual k (k ⊗[O] H) →+* WithConv (H →ₗ[O] Y') where
  toFun φ := toConv (iotaLin k Y' φ)
  map_one' := by
    apply WithConv.ext
    ext h
    change iotaLin k Y' 1 h = (1 : WithConv (H →ₗ[O] Y')) h
    rw [iotaLin_apply, CartierDual.one_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      LinearMap.convOne_apply, Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply]
  map_mul' φ ψ := by
    apply WithConv.ext
    ext h
    change iotaLin k Y' (φ * ψ) h = (toConv (iotaLin k Y' φ) * toConv (iotaLin k Y' ψ)) h
    rw [iotaLin_apply, CartierDual.mul_apply, LinearMap.convMul_apply, ofConv_toConv, ofConv_toConv,
      TensorProduct.comul_tmul, CommSemiring.comul_apply]
    induction (CoalgebraStruct.comul (R := O) h) using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, RingHom.map_zero]
    | tmul a b =>
      rw [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.dualDistrib_apply,
        TensorProduct.map_tmul, LinearMap.mul'_apply, iotaLin_apply, iotaLin_apply, ← map_mul]
      rfl
    | add s t hs ht =>
      rw [tmul_add, map_add, map_add, map_add, hs, ht, map_add, map_add]
  map_zero' := by
    apply WithConv.ext
    ext h
    change iotaLin k Y' 0 h = (0 : H →ₗ[O] Y') h
    rw [iotaLin_apply, LinearMap.zero_apply, ← (algebraMap k Y').map_zero]
    rfl
  map_add' φ ψ := by
    apply WithConv.ext
    ext h
    change iotaLin k Y' (φ + ψ) h = (iotaLin k Y' φ + iotaLin k Y' ψ) h
    rw [LinearMap.add_apply, iotaLin_apply, iotaLin_apply, iotaLin_apply, ← map_add]
    rfl

lemma iota_apply_apply (φ : CartierDual k (k ⊗[O] H)) (h : H) :
    iota k Y' φ h = algebraMap k Y' (φ ((1 : k) ⊗ₜ[O] h)) := rfl

omit [Algebra k Y'] [IsScalarTower O k Y'] in

lemma toSpanSingleton_counit_convMul_apply (y : Y') (g : WithConv (H →ₗ[O] Y')) (h : H) :
    (toConv (LinearMap.toSpanSingleton O Y' y ∘ₗ (Coalgebra.counit : H →ₗ[O] O)) * g) h =
      y * g h := by
  rw [LinearMap.convMul_apply, ofConv_toConv, ← LinearMap.map_rTensor,
    Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul, LinearMap.mul'_apply,
    LinearMap.toSpanSingleton_apply, one_smul]

theorem eq_zero_of_apply_one_eq_zero_of_isIdempotentElem
    [Coalgebra.IsCocomm O H] [Module.Finite O H] [Module.Free O H]
    (hloc : IsLocalRing (CartierDual k (k ⊗[O] H)))
    (ψ : WithConv (H →ₗ[O] Y')) (hψ1 : ψ 1 = 0) (hidem : IsIdempotentElem ψ) : ψ = 0 := by
  classical
  haveI := hloc
  let b := Module.Free.chooseBasis O H
  let bA := Algebra.TensorProduct.basis k b
  let φ : Module.Free.ChooseBasisIndex O H → CartierDual k (k ⊗[O] H) :=
    fun i => CartierDual.ofDual k (k ⊗[O] H) (bA.coord i)
  let m : Module.Free.ChooseBasisIndex O H → CartierDual k (k ⊗[O] H) :=
    fun i => φ i - algebraMap k (CartierDual k (k ⊗[O] H)) (φ i 1)
  have hφ : ∀ i (a : k ⊗[O] H), φ i a = bA.repr a i := fun i a => rfl
  have hm_apply : ∀ i (a : k ⊗[O] H),
      m i a = bA.repr a i - Coalgebra.counit (R := k) a * bA.repr 1 i := by
    intro i a
    show φ i a - (algebraMap k (CartierDual k (k ⊗[O] H)) (φ i 1)) a = _
    rw [CartierDual.algebraMap_apply, hφ, hφ]
  have hm : ∀ i, m i ∈ IsLocalRing.maximalIdeal (CartierDual k (k ⊗[O] H)) := fun i => by
    apply mem_maximalIdeal_of_apply_one_eq_zero hloc
    rw [hm_apply, Bialgebra.counit_one, one_mul, sub_self]

  let ψk : k ⊗[O] H →ₗ[k] Y' := ψ.ofConv.liftBaseChange k
  have hψk : ∀ a : k ⊗[O] H, ∑ i, ψ (b i) * algebraMap k Y' (bA.repr a i) = ψk a := by
    intro a
    conv_rhs => rw [← bA.sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul,
      Algebra.smul_def, mul_comm]
  have hrepr : ψ = ∑ i, toConv (LinearMap.toSpanSingleton O Y' (ψ (b i)) ∘ₗ
      (Coalgebra.counit : H →ₗ[O] O)) * iota k Y' (m i) := by
    apply WithConv.ext
    ext h
    change ψ h = (∑ i, toConv (LinearMap.toSpanSingleton O Y' (ψ (b i)) ∘ₗ
      (Coalgebra.counit : H →ₗ[O] O)) * iota k Y' (m i)).ofConv h
    rw [ofConv_sum, LinearMap.sum_apply]
    simp only [toSpanSingleton_counit_convMul_apply, iota_apply_apply, hm_apply, map_sub, map_mul,
      mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ i, ψ (b i) * algebraMap k Y' (bA.repr ((1 : k) ⊗ₜ[O] h) i) = ψ h := by
      rw [hψk, LinearMap.liftBaseChange_tmul, one_smul]
    have e2 : ∑ i, ψ (b i) *
        (algebraMap k Y' (Coalgebra.counit (R := k) ((1 : k) ⊗ₜ[O] h)) *
          algebraMap k Y' (bA.repr 1 i)) = 0 := by
      have : ∀ i, ψ (b i) *
          (algebraMap k Y' (Coalgebra.counit (R := k) ((1 : k) ⊗ₜ[O] h)) *
            algebraMap k Y' (bA.repr 1 i)) =
          algebraMap k Y' (Coalgebra.counit (R := k) ((1 : k) ⊗ₜ[O] h)) *
            (ψ (b i) * algebraMap k Y' (bA.repr 1 i)) := fun i => by ring
      simp only [this, ← Finset.mul_sum]
      rw [Algebra.TensorProduct.one_def, hψk, LinearMap.liftBaseChange_tmul, one_smul]
      change _ * ψ 1 = 0
      rw [hψ1, mul_zero]
    rw [e1, e2, sub_zero]
  have hJ : ψ ∈ Ideal.map (iota k Y') (IsLocalRing.maximalIdeal (CartierDual k (k ⊗[O] H))) := by
    rw [hrepr]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hm i))
  obtain ⟨N, hN⟩ := isNilpotent_maximalIdeal (k := k) (O := O) (H := H) hloc
  have hJN : (Ideal.map (iota k Y') (IsLocalRing.maximalIdeal (CartierDual k (k ⊗[O] H)))) ^ N = ⊥ := by
    rw [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot]
  have hmem : ψ ^ (N + 1) ∈
      (Ideal.map (iota k Y') (IsLocalRing.maximalIdeal (CartierDual k (k ⊗[O] H)))) ^ N :=
    Ideal.pow_le_pow_right (Nat.le_succ N) (Ideal.pow_mem_pow hJ (N + 1))
  rw [hidem.pow_succ_eq, hJN, Ideal.mem_bot] at hmem
  exact hmem

end Unipotent

section Corner

variable {O : Type*} [CommRing O] {k : Type*} [Field k] [Algebra O k]
  {H : Type*} [CommRing H] [Bialgebra O H] [Coalgebra.IsCocomm O H]
  [Module.Finite O H] [Module.Free O H]
  {Y : Type*} [CommRing Y] [Algebra O Y]

theorem InFilt.two_of_one_of_isLocalRing (p : ℕ) (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {(p : O)})
    (htf : ∀ v : Y, (p : Y) * v = 0 → v = 0)
    (hloc : IsLocalRing (CartierDual k (k ⊗[O] H)))
    (N : WithConv (H →ₗ[O] Y)) (hN1 : N 1 = 0) (hN : InFilt p 1 N)
    (heq : (2 : WithConv (H →ₗ[O] Y)) * N + N * N = 0) (hp2 : p = 2) : InFilt p 2 N := by
  classical

  let b := Module.Free.chooseBasis O H
  have hz : ∀ i, ∃ z : Y, N (b i) = (p : Y) ^ 1 * z := fun i => hN (b i)
  choose z hz using hz
  let δ : H →ₗ[O] Y := b.constr O z
  have hNδ : ∀ h, N h = (p : Y) * δ h := by
    have e : N.ofConv = (p : O) • δ := b.ext fun i => by
      rw [LinearMap.smul_apply, Module.Basis.constr_basis, Algebra.smul_def, map_natCast]
      exact (hz i).trans (by rw [pow_one])
    intro h
    have := LinearMap.congr_fun e h
    rw [LinearMap.smul_apply, Algebra.smul_def, map_natCast] at this
    exact this
  set δ' : WithConv (H →ₗ[O] Y) := toConv δ with hδ'
  have hNδ' : N = (p : WithConv (H →ₗ[O] Y)) * δ' := by
    apply WithConv.ext; ext h
    change N h = ((p : WithConv (H →ₗ[O] Y)) * δ') h
    rw [natCast_mul_apply]; exact hNδ h

  have htfE : ∀ F : WithConv (H →ₗ[O] Y), (p : WithConv (H →ₗ[O] Y)) * F = 0 → F = 0 := by
    intro F hF
    apply WithConv.ext; ext h
    have := congrArg (fun G : WithConv (H →ₗ[O] Y) => G h) hF
    simp only [natCast_mul_apply] at this
    exact htf _ this
  subst hp2

  have hδeq : δ' + δ' * δ' = 0 := by
    apply htfE; apply htfE
    rw [hNδ'] at heq
    push_cast at heq ⊢
    linear_combination heq
  have hδ1 : δ 1 = 0 := htf _ (by rw [← hNδ]; exact hN1)

  let ρ : WithConv (H →ₗ[O] Y) →+* WithConv (H →ₗ[O] k ⊗[O] Y) :=
    postComp (Algebra.TensorProduct.includeRight : Y →ₐ[O] k ⊗[O] Y)
  have hρ : ∀ (F : WithConv (H →ₗ[O] Y)) (h : H), ρ F h = (1 : k) ⊗ₜ[O] F h := fun F h => rfl
  have hρN : ρ N = 0 := by
    apply WithConv.ext; ext h
    change ρ N h = 0
    rw [hρ]
    obtain ⟨w, hw⟩ := hN h
    exact one_tmul_eq_zero_of_mem_span hker
      (Ideal.mem_span_singleton'.mpr ⟨w, by rw [hw, pow_one, mul_comm]⟩)
  set ψ : WithConv (H →ₗ[O] k ⊗[O] Y) := ρ δ' with hψ
  have h2ψ : ((2 : ℕ) : WithConv (H →ₗ[O] k ⊗[O] Y)) * ψ = 0 := by
    rw [hψ, ← map_natCast ρ, ← map_mul, ← hNδ', hρN]
  have hψidem : IsIdempotentElem ψ := by
    have h0 : ψ + ψ * ψ = 0 := by
      have := congrArg ρ hδeq
      rwa [map_add, map_mul, map_zero] at this
    have hsq : ψ * ψ = -ψ := (neg_eq_of_add_eq_zero_right h0).symm
    have h2 : ψ + ψ = 0 := by rw [← two_mul]; exact_mod_cast h2ψ
    change ψ * ψ = ψ
    rw [hsq]
    exact neg_eq_of_add_eq_zero_left h2
  have hψ1 : ψ 1 = 0 := by
    change ρ δ' 1 = 0
    rw [hρ]
    change (1 : k) ⊗ₜ[O] δ 1 = 0
    rw [hδ1, tmul_zero]
  have hψ0 : ψ = 0 :=
    eq_zero_of_apply_one_eq_zero_of_isIdempotentElem (k := k) hloc ψ hψ1 hψidem

  intro h
  have h1 : (1 : k) ⊗ₜ[O] δ h = 0 := by
    have := congrArg (fun F : WithConv (H →ₗ[O] k ⊗[O] Y) => F h) hψ0
    rw [hψ, hρ] at this
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (mem_span_of_one_tmul_eq_zero hk hker h1)
  refine ⟨c, ?_⟩
  rw [hNδ h, ← hc]; ring

end Corner

section Base

variable {O : Type*} [CommRing O] {Y : Type*} [CommRing Y] [Algebra O Y] {ℓ : ℕ}

lemma natCast_mul_eq_zero_imp [IsDomain O] [Module.IsTorsionFree O Y] (hℓ0 : (ℓ : O) ≠ 0)
    (v : Y) (hv : (ℓ : Y) * v = 0) : v = 0 := by
  have e : (ℓ : O) • v = (ℓ : Y) * v := by rw [Algebra.smul_def, map_natCast]
  have := smul_right_injective Y hℓ0 (e.trans (hv.trans (smul_zero (ℓ : O)).symm))
  simpa using this

lemma eq_zero_of_forall_filt [IsNoetherianRing O] [IsLocalRing O] [Module.Finite O Y]
    (hℓu : ¬ IsUnit (ℓ : O)) (v : Y) (hv : ∀ m : ℕ, Filt ℓ m v) : v = 0 := by
  set I : Ideal O := Ideal.span {(ℓ : O)} with hI
  have hItop : I ≠ ⊤ := by
    rwa [hI, Ne, Ideal.span_singleton_eq_top]
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Y) I hItop
  have hmem : v ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule O Y) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨z, hz⟩ := hv i
    have e : v = ((ℓ : O) ^ i) • z := by
      rw [hz, Algebra.smul_def, map_pow, map_natCast]
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) i)
      Submodule.mem_top
  rw [hK] at hmem
  exact (Submodule.mem_bot O).mp hmem

end Base

end FontaineStepOneUnipotent
p2m_reactivate "P2MW.S_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual.FontaineStepOneUnipotent"

universe u v w w'

open FontaineStepOneUnipotent in
theorem solution
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : O))
    (k : Type v) [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {(p : O)})
    (H : Type w) [CommRing H] [HopfAlgebra O H] [Coalgebra.IsCocomm O H]
    [Module.Finite O H] [Module.Free O H] (hrank : ∃ a : ℕ, Module.finrank O H = p ^ a)
    (hunip : IsLocalRing (CartierDual k (TensorProduct O k H)))
    (Y : Type w') [CommRing Y] [Algebra O Y] [Module.Finite O Y] [Module.Free O Y]
    (x x' : H →ₐ[O] Y) (hxx' : ∀ h : H, x h - x' h ∈ Ideal.span {(p : Y)}) :
    x = x' := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, ha⟩ := hrank
  have htf : ∀ v : Y, (p : Y) * v = 0 → v = 0 :=
    natCast_mul_eq_zero_imp (O := O) hunif.ne_zero
  have hsep : ∀ v : Y, (∀ m : ℕ, Filt p m v) → v = 0 :=
    eq_zero_of_forall_filt (O := O) hunif.not_isUnit

  set xi : WithConv (H →ₐ[O] Y) := toConv (x'.comp antipodeAlgHom) with hxi
  set u : WithConv (H →ₐ[O] Y) := toConv x * xi with hu
  have hupow : u ^ p ^ a = 1 := by
    rw [← ha]; exact HopfAlgebra.convPow_finrank_eq_one_of_isCocomm O H Y u

  set uE : WithConv (H →ₗ[O] Y) := toConv u.ofConv.toLinearMap with huE
  have huEpow : uE ^ p ^ a = 1 := by
    rw [huE, ← AlgHom.toLinearMap_convPow, hupow, AlgHom.toLinearMap_convOne]
  have h1 : InFilt p 1 (uE - 1) := by
    have e : uE - 1 = (toConv x.toLinearMap - toConv x'.toLinearMap) *
        toConv (x'.comp antipodeAlgHom).toLinearMap := by
      rw [sub_mul, ← toLinearMap_convMul_comp_antipode x']
      rfl
    rw [e]
    refine InFilt.mul (a := 1) (b := 0) (fun h => ?_) (InFilt.level_zero _)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hxx' h)
    exact ⟨c, by change x h - x' h = _; rw [← hc, pow_one, mul_comm]⟩
  have huE1 : uE 1 = 1 := map_one u.ofConv
  have hcorner : ∀ w : WithConv (H →ₗ[O] Y), w 1 = 1 → p = 2 → w ^ 2 = 1 →
      InFilt p 1 (w - 1) → InFilt p 2 (w - 1) := by
    intro w hw1 hp2 hw2 hw
    refine InFilt.two_of_one_of_isLocalRing p hk hker htf hunip (w - 1) ?_ hw ?_ hp2
    · change w 1 - (1 : WithConv (H →ₗ[O] Y)) 1 = 0
      rw [hw1, convOne_apply_one, sub_self]
    · linear_combination hw2
  have huE_one : uE = 1 :=
    eq_one_of_pow_prime_pow_eq_one hp htf hsep (fun w => w 1 = 1) (fun w hw n => convPow_apply_one hw n)
      hcorner huE1 h1 a huEpow

  have hu1 : u = 1 := by
    apply toConv_injective.comp (AlgHom.toLinearMap_injective.comp ofConv_injective)
    change toConv u.ofConv.toLinearMap = toConv (1 : WithConv (H →ₐ[O] Y)).ofConv.toLinearMap
    rw [AlgHom.toLinearMap_convOne]
    exact huE_one
  have hxx : toConv x = toConv x' := by
    calc toConv x = toConv x * (xi * toConv x') := by
          rw [hxi, comp_antipode_mul_point (toConv x'), mul_one]
      _ = u * toConv x' := by rw [hu, mul_assoc]
      _ = toConv x' := by rw [hu1, one_mul]
  exact toConv_injective hxx

end S_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual (solution)

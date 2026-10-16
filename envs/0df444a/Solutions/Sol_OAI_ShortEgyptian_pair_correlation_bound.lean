-- Prove2me | solution 1 for OAI.ShortEgyptian.pair_correlation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:41:41.680137+00:00
-- url     : https://prove2.me/submissions/0ba8de19-75f8-4a5e-8206-ab36bc7ac9d9

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ProductCorrelations.lean:L71-L141
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.pair_correlation_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Theorems.Thm_OAI_ShortEgyptian_prod_mergeSamples
import Theorems.Thm_OAI_ShortEgyptian_uniform_prime_bilinear_two

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeProducts ----
namespace OAI

universe uJ uA uB uE uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma finite_markov {A : Type uA} [Fintype A] (f : A → ℝ) (hnonneg : ∀ a, 0 ≤ f a)
    (c : ℝ) (hc : 0 < c) :
    (𝔼 a, if c ≤ f a then (1:ℝ) else 0) ≤ (𝔼 a, f a)/c := by
  apply (le_div_iff₀ hc).mpr
  rw [Finset.expect_mul]
  apply expect_le_expect
  intro a _
  split_ifs with h
  · simpa using h
  · simpa using hnonneg a

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.SamplePartitions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uJ uA uE uM uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma expect_partition {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A]
    [AddCommMonoid E] [Module ℚ≥0 E] (L R : Finset J) (hdis : Disjoint L R)
    (F : (J → A) → E) :
    (𝔼 f : J → A, F f) =
      𝔼 z : ((L∪R)ᶜ : Finset J) → A, 𝔼 x : L → A, 𝔼 y : R → A,
        F (mergeSamples L R z x y) := by
  let e := partitionSamples (A := A) L R hdis
  calc
    _ = 𝔼 v, F (e.symm v) := Fintype.expect_equiv e _ _ (fun f => by simp)
    _ = _ := by
      rw [show (univ : Finset ((((L∪R)ᶜ : Finset J) → A) × ((L → A) × (R → A)))) = univ ×ˢ univ by simp,expect_product]
      apply expect_congr rfl
      intro z _
      rw [show (univ : Finset ((L → A) × (R → A))) = univ ×ˢ univ by simp,expect_product]
      rfl

lemma expect_normalize {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A]
    [AddCommMonoid E] [Module ℚ≥0 E] (I : J → Bool) (F : ((J × Bool) → A) → E) :
    (𝔼 f, F f) = 𝔼 x : J → A, 𝔼 y : J → A,
      F (fun jb => if jb.2 = I jb.1 then x jb.1 else y jb.1) := by
  let e := normalizeSamples (A := A) I
  calc
    _ = 𝔼 v, F (e.symm v) := Fintype.expect_equiv e _ _ (fun f => by simp)
    _ = _ := by
      rw [show (univ : Finset ((J → A) × (J → A))) = univ ×ˢ univ by simp,expect_product]
      rfl

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.BilinearProducts ----
namespace OAI

universe uJ uK uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma character_ratio_eq {u q : ℕ} [NeZero u] [NeZero q] (k c n : ℕ)
    (hcross : k*q = c*u) :
    ZMod.stdAddChar ((k*n:ℕ) : ZMod u) = ZMod.stdAddChar ((c*n:ℕ) : ZMod q) := by
  rw [ZMod.stdAddChar_apply,ZMod.toCircle_natCast,ZMod.stdAddChar_apply,ZMod.toCircle_natCast]
  congr 1
  have hu : (u:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne u
  have hq : (q:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hh : (k:ℂ)*q = (c:ℂ)*u := by exact_mod_cast hcross
  push_cast
  field_simp
  linear_combination (n:ℂ) * hh

lemma reduced_cross (k u : ℕ) (hu : 0 < u) :
    k*(u/k.gcd u) = (k/k.gcd u)*u := by
  have hg : 0 < k.gcd u := Nat.gcd_pos_of_pos_right k hu
  have hk := Nat.mul_div_cancel' (Nat.gcd_dvd_left k u)
  have hu' := Nat.mul_div_cancel' (Nat.gcd_dvd_right k u)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    _ = k*(k.gcd u*(u/k.gcd u)) := by ring
    _ = k*u := by rw [hu']
    _ = (k.gcd u*(k/k.gcd u))*u := by rw [hk]
    _ = _ := by ring

lemma gcd_mul_le (l v u : ℕ) (hl : 0 < l) (hu : 0 < u) :
    (l*v).gcd u ≤ l*(v.gcd u) := by
  have hpos : 0 < (l.gcd u)*(v.gcd u) :=
    Nat.mul_pos (Nat.gcd_pos_of_pos_right l hu) (Nat.gcd_pos_of_pos_right v hu)
  have hd : (l*v).gcd u ∣ (l.gcd u)*(v.gcd u) := by
    have hh := gcd_mul_dvd_mul_gcd u l v
    change Nat.gcd u (l*v) ∣ Nat.gcd u l * Nat.gcd u v at hh
    simpa only [Nat.gcd_comm] using hh
  exact (Nat.le_of_dvd hpos hd).trans (Nat.mul_le_mul_right _ (Nat.gcd_le_left u hl))

lemma fixed_prime_bilinear {J : Type uJ} {K : Type uK} {A : Type uA} [Fintype J] [Fintype K] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (u l v : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l) (hcard : Fintype.card K = Fintype.card J)
    (Q G B : ℝ) (hG : 0 < G) (hB : 0 ≤ B)
    (hgcd : (v.gcd u:ℝ) ≤ G) (hscale : (l:ℝ)*G*Q ≤ u)
    (hprod : ∀ f : J → A, (∏ j, p (f j):ℕ) < Q)
    (hprodK : ∀ f : K → A, (∏ j, p (f j):ℕ) < Q)
    (hatom : (Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J ≤ B) :
    ‖𝔼 f : J → A, 𝔼 g : K → A,
      ZMod.stdAddChar (((l*v)*((∏ j, p (f j))*(∏ j, p (g j))):ℕ):ZMod u)‖ ≤ Real.sqrt u*B := by
  let d := (l*v).gcd u
  let q := u/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right _ hu
  have hq : 0 < q := Nat.div_gcd_pos_of_pos_right (l*v) hu
  let : NeZero q := ⟨hq.ne'⟩
  have hdu : d*q = u := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hdb : (d:ℝ) ≤ (l:ℝ)*G := by
    calc
      _ ≤ (l:ℝ)*(v.gcd u:ℝ) := by exact_mod_cast gcd_mul_le l v u hl hu
      _ ≤ _ := mul_le_mul_of_nonneg_left hgcd (Nat.cast_nonneg l)
  have hqu : (Q:ℝ) ≤ q := by
    have hduR : (d:ℝ)*(q:ℝ) = u := by exact_mod_cast hdu
    have hmult := mul_le_mul_of_nonneg_right hdb (Nat.cast_nonneg q)
    have hpos : 0 < (l:ℝ)*G := mul_pos (by exact_mod_cast hl) hG
    nlinarith
  let c : (ZMod q)ˣ := ZMod.unitOfCoprime ((l*v)/d) (Nat.coprime_div_gcd_div_gcd hd)
  have hpJ : ∀ f : J → A, ∏ j, p (f j) < q := by
    intro f
    exact_mod_cast (hprod f).trans_le hqu
  have hpK : ∀ f : K → A, ∏ j, p (f j) < q := by
    intro f
    exact_mod_cast (hprodK f).trans_le hqu
  have heq (f : J → A) (g : K → A) :
      ZMod.stdAddChar (((l*v)*((∏ j, p (f j))*(∏ j, p (g j))):ℕ):ZMod u) =
      ZMod.stdAddChar ((c:ZMod q)*((∏ j, p (f j) : ℕ):ZMod q)*((∏ j, p (g j) : ℕ):ZMod q)) := by
    have hh := character_ratio_eq (l*v) ((l*v)/d) ((∏ j, p (f j))*(∏ j, p (g j))) (reduced_cross (l*v) u hu)
    simpa only [c,ZMod.coe_unitOfCoprime,Nat.cast_mul,mul_assoc] using hh
  simp_rw [heq]
  apply (uniform_prime_bilinear_two p hp hinj q hpJ hpK hcard c).trans
  have hqu' : (q:ℝ) ≤ u := by exact_mod_cast Nat.div_le_self u d
  calc
    _ ≤ Real.sqrt ((u:ℝ)*B^2) := by
      apply Real.sqrt_le_sqrt
      gcongr
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg u),Real.sqrt_sq hB]

lemma finset_fixed_bilinear {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (u l v : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l) (L R : Finset J) (hcard : R.card = L.card)
    (Q G B : ℝ) (hG : 0 < G) (hB : 0 ≤ B)
    (hgcd : (v.gcd u:ℝ) ≤ G) (hscale : (l:ℝ)*G*Q ≤ u)
    (hprod : ∀ f : L → A, (∏ j,p (f j):ℕ) < Q)
    (hprodR : ∀ f : R → A, (∏ j,p (f j):ℕ) < Q)
    (hatom : (L.card:ℝ)^L.card/(Fintype.card A:ℝ)^L.card ≤ B) :
    ‖𝔼 x : L → A, 𝔼 y : R → A,
      ZMod.stdAddChar (((l*v)*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)‖ ≤ Real.sqrt u*B := by
  have hc : Fintype.card R = Fintype.card L := by simpa only [Fintype.card_coe] using hcard
  have ha : (Fintype.card L:ℝ)^Fintype.card L/(Fintype.card A:ℝ)^Fintype.card L ≤ B := by
    simpa only [Fintype.card_coe] using hatom
  convert fixed_prime_bilinear (J := L) (K := R) p hp hinj u l v hu hl hc Q G B hG hB hgcd hscale hprod hprodR ha using 1
  congr 1
  apply expect_congr (by ext; simp)
  intro x _
  apply expect_congr (by ext; simp)
  intro y _
  rfl

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ProductCorrelations ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma pair_exposure_identity {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (u l : ℕ) [NeZero u] (I K : J → Bool)
    (L R : Finset J) (hdis : Disjoint L R)
    (hdiffL : ∀ j ∈ L, I j ≠ K j) (hdiffR : ∀ j ∈ R, I j ≠ K j) (a0 : A) :
    (𝔼 f : (J × Bool) → A,
      ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))) =
    𝔼 b : J → A, 𝔼 z : ((L∪R)ᶜ : Finset J) → A, 𝔼 x : L → A, 𝔼 y : R → A,
      ZMod.stdAddChar (((l*(∏ j,p (z j)))*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K
        (fun jb => if jb.2 = I jb.1 then mergeSamples L R z (fun _ => a0) (fun _ => a0) jb.1 else b jb.1):ℕ):ZMod u)) := by
  let normed (x y : J → A) (jb : J × Bool) := if jb.2 = I jb.1 then x jb.1 else y jb.1
  let second (z : ((L∪R)ᶜ : Finset J) → A) (b : J → A) :=
    sampleProduct p K (normed (mergeSamples L R z (fun _ => a0) (fun _ => a0)) b)
  let C (f : (J × Bool) → A) : ℂ :=
    ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))
  let F (b : J → A) (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) : ℂ :=
    ZMod.stdAddChar (((l*(∏ j,p (z j)))*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*second z b:ℕ):ZMod u))
  have hpoint b z x y : C (normed (mergeSamples L R z x y) b) = F b z x y := by
    have hI : sampleProduct p I (normed (mergeSamples L R z x y) b) =
        (∏ j,p (z j))*(∏ j,p (x j))*(∏ j,p (y j)) := by
      simp only [sampleProduct,normed,ite_eq_left rfl]
      exact prod_mergeSamples L R hdis z x y p
    have hK : sampleProduct p K (normed (mergeSamples L R z x y) b) = second z b := by
      apply prod_congr rfl
      intro j _
      by_cases h : K j = I j
      · have hl' : j ∉ L := fun hj => hdiffL j hj h.symm
        have hr' : j ∉ R := fun hj => hdiffR j hj h.symm
        simp [normed,mergeSamples,h,hl',hr']
      · simp [normed,h]
    dsimp only [C,F]
    rw [hI,hK]
    congr 3
    ring
  have hfull : (𝔼 f, C f) = 𝔼 b : J → A, 𝔼 z : ((L∪R)ᶜ : Finset J) → A,
      𝔼 x : L → A, 𝔼 y : R → A, F b z x y := by
    rw [expect_normalize I,expect_comm]
    apply expect_congr rfl
    intro b _
    rw [expect_partition L R hdis]
    apply expect_congr rfl
    intro z _
    apply expect_congr rfl
    intro x _
    apply expect_congr rfl
    intro y _
    exact hpoint b z x y
  exact hfull

lemma pair_correlation_bound {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (u l : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l) (I K : J → Bool)
    (L R : Finset J) (hdis : Disjoint L R) (hcard : R.card = L.card)
    (hdiffL : ∀ j ∈ L, I j ≠ K j) (hdiffR : ∀ j ∈ R, I j ≠ K j)
    (Q G B M a : ℝ) (hG : 0 < G) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hscale : (l:ℝ)*G*Q ≤ u)
    (hprod : ∀ f : L → A, (∏ j, p (f j):ℕ) < Q)
    (hprodR : ∀ f : R → A, (∏ j, p (f j):ℕ) < Q)
    (hatom : (L.card:ℝ)^L.card/(Fintype.card A:ℝ)^L.card ≤ B)
    (hMoment : (𝔼 z : ((L∪R)ᶜ : Finset J) → A, (Nat.gcd (∏ j,p (z j)) u:ℝ)^a) ≤ M) :
    ‖𝔼 f : (J × Bool) → A,
      ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))‖ ≤
        M/G^a+Real.sqrt u*B := by
  let a0 : A := Classical.choice ‹Nonempty A›
  let normed (x y : J → A) (jb : J × Bool) := if jb.2 = I jb.1 then x jb.1 else y jb.1
  let second (z : ((L∪R)ᶜ : Finset J) → A) (b : J → A) :=
    sampleProduct p K (normed (mergeSamples L R z (fun _ => a0) (fun _ => a0)) b)
  let C (f : (J × Bool) → A) : ℂ :=
    ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))
  let F (b : J → A) (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) : ℂ :=
    ZMod.stdAddChar (((l*(∏ j,p (z j)))*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*second z b:ℕ):ZMod u))
  have hfull : (𝔼 f, C f) = 𝔼 b : J → A, 𝔼 z : ((L∪R)ᶜ : Finset J) → A,
      𝔼 x : L → A, 𝔼 y : R → A, F b z x y :=
    pair_exposure_identity p u l I K L R hdis hdiffL hdiffR a0
  have hfresh (b : J → A) (z : ((L∪R)ᶜ : Finset J) → A) :
      ‖𝔼 x : L → A, 𝔼 y : R → A, F b z x y‖ ≤
        (if G ≤ (Nat.gcd (∏ j,p (z j)) u:ℝ) then 1 else 0)+Real.sqrt u*B := by
    have heq : ‖𝔼 x : L → A, 𝔼 y : R → A, F b z x y‖ =
        ‖𝔼 x : L → A, 𝔼 y : R → A,
          ZMod.stdAddChar (((l*(∏ j,p (z j)))*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)‖ := by
      dsimp only [F]
      simp only [← expect_mul,norm_mul,Complex.norm_conj,stdAddChar_norm,mul_one]
    rw [heq]
    split_ifs with h
    · apply le_trans (b := (1:ℝ))
      · apply (RCLike.norm_expect_le (K := ℂ)).trans
        apply expect_le univ_nonempty
        intro x _
        exact (RCLike.norm_expect_le (K := ℂ)).trans (expect_le univ_nonempty (fun y _ => by simp))
      · exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg u) hB)
    · rw [zero_add]
      exact finset_fixed_bilinear p hp hinj u l _ hu hl L R hcard Q G B hG hB
        (le_of_not_ge h) hscale hprod hprodR hatom
  have hbad : (𝔼 z : ((L∪R)ᶜ : Finset J) → A,
      if G ≤ (Nat.gcd (∏ j,p (z j)) u:ℝ) then (1:ℝ) else 0) ≤ M/G^a := by
    calc
      _ ≤ 𝔼 z : ((L∪R)ᶜ : Finset J) → A,
        if G^a ≤ (Nat.gcd (∏ j,p (z j)) u:ℝ)^a then (1:ℝ) else 0 := by
        apply expect_le_expect
        intro z _
        split_ifs with h h'
        · rfl
        · exact False.elim (h' (Real.rpow_le_rpow hG.le h ha))
        · positivity
        · rfl
      _ ≤ (𝔼 z : ((L∪R)ᶜ : Finset J) → A, (Nat.gcd (∏ j,p (z j)) u:ℝ)^a)/G^a :=
        finite_markov _ (fun _ => by positivity) _ (Real.rpow_pos_of_pos hG _)
      _ ≤ _ := div_le_div_of_nonneg_right hMoment (Real.rpow_nonneg hG.le _)
  change ‖𝔼 f, C f‖ ≤ _
  rw [hfull]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro b _
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (expect_le_expect (fun z _ => hfresh b z)).trans
  rw [expect_add_distrib,Fintype.expect_const]
  linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.pair_correlation_bound.{uJ,uA} := @_root_.OAI.ShortEgyptian.pair_correlation_bound.{uJ,uA}

-- Prove2me | solution 1 for OAI.ShortEgyptian.random_product_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:53:54.955501+00:00
-- url     : https://prove2.me/submissions/9f867dad-45d7-4976-b838-b85164d4080a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/RandomMoments.lean:L13-L73
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.random_product_second_moment. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_gcd_product_moment
import Theorems.Thm_OAI_ShortEgyptian_mean_square_correlation_exp
import Theorems.Thm_OAI_ShortEgyptian_pair_correlation_bound
import Theorems.Thm_OAI_ShortEgyptian_random_atom_bound
import Theorems.Thm_OAI_ShortEgyptian_random_error_sum
import Theorems.Thm_OAI_ShortEgyptian_random_fresh_bound
import Theorems.Thm_OAI_ShortEgyptian_random_lengths
import Theorems.Thm_OAI_ShortEgyptian_random_pair_scalar

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeProducts ----
namespace OAI

universe uJ uA uB uE uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma prime_divisor_count (u : ℕ) (hu : u ≠ 0) :
    (u.primeFactors.card:ℝ)*Real.log 2 ≤ Real.log u := by
  have hp : 2^u.primeFactors.card ≤ u := by
    calc
      _ ≤ ∏ p ∈ u.primeFactors, p := by
        rw [← prod_const]
        exact prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hu) (Nat.prod_primeFactors_dvd u)
  have hh := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^u.primeFactors.card)
    (show (2:ℝ)^u.primeFactors.card ≤ u by exact_mod_cast hp)
  simpa only [Real.log_pow] using hh

lemma prime_hit_probability {A : Type uA} [Fintype A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p) (u : ℕ) (hu : u ≠ 0) :
    (𝔼 a, if p a ∣ u then (1:ℝ) else 0) ≤
      (Real.log u / Real.log 2) / Fintype.card A := by
  rw [Fintype.expect_eq_sum_div_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [sum_boole]
  have hc : (univ.filter (fun a => p a ∣ u)).card ≤ u.primeFactors.card := by
    apply card_le_card_of_injOn p
    · intro a ha
      exact Nat.mem_primeFactors.mpr ⟨hp a,(mem_filter.mp ha).2,hu⟩
    · exact hinj.injOn
  apply (show ((univ.filter (fun a => p a ∣ u)).card:ℝ) ≤ u.primeFactors.card by exact_mod_cast hc).trans
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr (prime_divisor_count u hu)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ProductCorrelations ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma disjoint_subsets_card {J : Type uJ} [Fintype J] (D : Finset J) (s : ℕ) (hs : 2*s ≤ D.card) :
    ∃ L R : Finset J, L ⊆ D ∧ R ⊆ D ∧ Disjoint L R ∧ L.card = s ∧ R.card = s := by
  obtain ⟨L,hLD,hLs⟩ := exists_subset_card_eq (show s ≤ D.card by omega)
  have hcard : s ≤ (D\L).card := by
    rw [card_sdiff_of_subset hLD,hLs]
    omega
  obtain ⟨R,hRD,hRs⟩ := exists_subset_card_eq hcard
  refine ⟨L,R,hLD,(fun j hj => (mem_sdiff.mp (hRD hj)).1),?_,hLs,hRs⟩
  exact disjoint_left.mpr (fun j hjL hjR => (mem_sdiff.mp (hRD hjR)).2 hjL)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.RandomBounds ----
namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma random_gcd_exponent (S M : ℝ) (hS : 2 ≤ S) (hMS : M ≤ S) :
    M*(2/S^98)*(S^101)^(3/4:ℝ) ≤ 1 := by
  have hSpos : 0 < S := by linarith
  have hh : (S^101)^(3/4:ℝ) ≤ S^76 := by
    rw [←Real.rpow_natCast_mul hSpos.le]
    apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ S) (by norm_num : (101:ℝ)*(3/4) ≤ 76)).trans_eq
    exact Real.rpow_natCast S 76
  have hp : S^21 ≥ 2 := by
    calc
      _ ≥ S^1 := pow_le_pow_right₀ (by linarith : 1 ≤ S) (by norm_num : 1 ≤ 21)
      _ ≥ 2 := by simpa using hS
  calc
    _ ≤ S*(2/S^98)*S^76 := by gcongr
    _ = 2/S^21 := by field_simp
    _ ≤ 1 := (div_le_one (pow_pos hSpos 21)).mpr hp

lemma random_hit_bound {A : Type uA} [Fintype A] [Nonempty A]
    (S : ℝ) (hS : 0 < S) (p : A → ℕ) (hp : ∀ a, (p a).Prime)
    (hinj : Function.Injective p) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u : ℕ) (hu : 0 < u) (hVS : Real.log u ≤ S) :
    (𝔼 a, if p a ∣ u then (1:ℝ) else 0) ≤ 2/S^98 := by
  have hPpos : 0 < (Fintype.card A:ℝ) := (pow_pos hS 99).trans_le hP
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hVb : Real.log u/Real.log 2 ≤ 2*S := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    nlinarith
  calc
    _ ≤ (Real.log u/Real.log 2)/(Fintype.card A:ℝ) := prime_hit_probability p hp hinj u hu.ne'
    _ ≤ (2*S)/(Fintype.card A:ℝ) := div_le_div_of_nonneg_right hVb hPpos.le
    _ ≤ 2*S/S^99 := div_le_div_of_nonneg_left (by positivity) (pow_pos hS 99) hP
    _ = _ := by field_simp

lemma random_outside_moment {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S : ℝ) (hS : 2 ≤ S) (hcount : (Fintype.card J:ℝ) ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u : ℕ) (hu : 0 < u) (hVS : Real.log u ≤ S) :
    (𝔼 f : J → A, (Nat.gcd (∏ j,p (f j)) u:ℝ)^(3/4:ℝ)) ≤ Real.exp 1 := by
  have hSpos : 0 < S := by linarith
  have hmax' (a : A) : (p a:ℝ) ≤ S^101 := by
    calc
      _ ≤ 2*S^100 := hmax a
      _ ≤ S*S^100 := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = _ := by ring
  have hhit := random_hit_bound S hSpos p hp hinj hP u hu hVS
  apply (gcd_product_moment p hp u (S^101) (2/S^98) (3/4) (by positivity) (by norm_num)
    (by positivity) hmax' hhit).trans
  exact Real.exp_le_exp.mpr (random_gcd_exponent S _ hS hcount)

lemma random_reduced_scale (u l : ℕ) (hu : 0 < u) (hV : 0 ≤ Real.log u)
    (hlmax : (l:ℝ) ≤ Real.exp ((1/200:ℝ)*Real.log u)) :
    (l:ℝ)*Real.exp (Real.log u/10)*Real.exp (4/5*Real.log u) ≤ u := by
  have huR : 0 < (u:ℝ) := by exact_mod_cast hu
  calc
    _ ≤ Real.exp ((1/200:ℝ)*Real.log u)*Real.exp (Real.log u/10)*Real.exp (4/5*Real.log u) := by gcongr
    _ = Real.exp ((181/200:ℝ)*Real.log u) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log u) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := Real.exp_log huR

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.RandomMoments ----
namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma random_product_second_moment {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊) (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u l : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l)
    (hV : 100000*Real.log S ≤ Real.log u) (hVS : Real.log u ≤ S)
    (hlmax : (l:ℝ) ≤ Real.exp ((1/200:ℝ)*min (⌊S/Real.log S⌋₊:ℝ) (Real.log u))) :
    (𝔼 f : (J × Bool) → A,
      ‖𝔼 I : J → Bool,
        ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)‖^2) ≤
        Real.exp (-(1/100:ℝ)*min (⌊S/Real.log S⌋₊:ℝ) (Real.log u)) := by
  classical
  let m := ⌊S/Real.log S⌋₊
  let s := ⌊3*Real.log u/(400*Real.log S)⌋₊
  let V := Real.log u
  have hlen := random_lengths S V hlog hS hV hVS
  change S/(2*Real.log S) ≤ (m:ℝ) ∧ (m:ℝ) ≤ S ∧ V/(140*Real.log S) ≤ (s:ℝ) ∧
    (s:ℝ) ≤ 3*V/(400*Real.log S) ∧ 8*s ≤ m ∧ (s:ℝ) ≤ S ∧ 100 ≤ min (m:ℝ) V at hlen
  obtain ⟨hmL,hmS,hsL,hsU,h8,hsS,hw⟩ := hlen
  have hS2 : 2 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hVpos : 0 < V := by dsimp [V]; linarith
  have huR : 0 < (u:ℝ) := by exact_mod_cast hu
  have hscale : (l:ℝ)*Real.exp (V/10)*Real.exp (4/5*V) ≤ u :=
    random_reduced_scale u l hu hVpos.le
      (hlmax.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))))
  have hatom : (s:ℝ)^s/(Fintype.card A:ℝ)^s ≤ Real.exp (-(7/10:ℝ)*V) :=
    random_atom_bound S V _ s hS2 hP hsS hsL
  have hcorr (I K : J → Bool) (hIK : 2*s ≤ hammingDistance I K) :
      ‖𝔼 f : (J × Bool) → A,
        ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
          (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))‖ ≤
        Real.exp (-(1/20:ℝ)*V)+Real.exp (-(1/5:ℝ)*V) := by
    obtain ⟨L,R,hLD,hRD,hdis,hLs,hRs⟩ := disjoint_subsets_card
      (univ.filter (fun j => I j ≠ K j)) s hIK
    have hLs' : Fintype.card L = s := by simpa using hLs
    have hRs' : Fintype.card R = s := by simpa using hRs
    have hM : (𝔼 z : ((L∪R)ᶜ : Finset J) → A,
        (Nat.gcd (∏ j,p (z j)) u:ℝ)^(3/4:ℝ)) ≤ Real.exp 1 := by
      have hcount : (Fintype.card ((L∪R)ᶜ : Finset J):ℝ) ≤ S := by
        apply le_trans (b := (m:ℝ)) _ hmS
        simp only [Fintype.card_coe]
        exact_mod_cast (card_le_univ ((L∪R)ᶜ)).trans_eq hcard
      convert random_outside_moment S hS2 hcount p hp hinj hmax hP u hu hVS using 1
      apply expect_congr (by ext; simp)
      intro z _
      rfl
    have hh := pair_correlation_bound p hp hinj u l hu hl I K L R hdis (hRs.trans hLs.symm)
      (fun j hj => (mem_filter.mp (hLD hj)).2) (fun j hj => (mem_filter.mp (hRD hj)).2)
      (Real.exp (4/5*V)) (Real.exp (V/10)) (Real.exp (-(7/10:ℝ)*V)) (Real.exp 1) (3/4)
      (Real.exp_pos _) (Real.exp_nonneg _) (by norm_num) hscale (fun f => random_fresh_bound p S V hS2 hVpos hmax (by simpa only [hLs'] using hsU) f)
      (fun f => random_fresh_bound p S V hS2 hVpos hmax (by simpa only [hRs'] using hsU) f)
      (by simpa only [hLs] using hatom) hM
    exact hh.trans (random_pair_scalar u (by dsimp [V] at hVpos; linarith))
  have hh := mean_square_correlation_exp
    (fun I : J → Bool => fun f : (J × Bool) → A =>
      ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u))
    (fun I f => by simp) (2*s) (by simpa only [hcard, ←Nat.mul_assoc] using h8)
    (Real.exp (-(1/20:ℝ)*V)+Real.exp (-(1/5:ℝ)*V)) (by positivity) hcorr
  apply hh.trans
  simpa only [hcard,add_assoc] using random_error_sum (m:ℝ) V hw

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.random_product_second_moment.{uJ,uA} := @_root_.OAI.ShortEgyptian.random_product_second_moment.{uJ,uA}

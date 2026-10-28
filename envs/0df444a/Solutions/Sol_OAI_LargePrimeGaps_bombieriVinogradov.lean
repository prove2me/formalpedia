-- Prove2me | solution 1 for OAI.LargePrimeGaps.bombieriVinogradov
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:54:16.579143+00:00
-- url     : https://prove2.me/submissions/8fabe3f1-3009-4e04-a70a-7a9b0515fb3e

import Mathlib
import Definitions.Def_OAIW2PG000
import Theorems.Thm_OAI_LargePrimeGaps_primeWeighted_error_bound

section
-- module Solutions.OAIW2_P344.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_OrthantIntegrals
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem divisorMultiplicity_succ (k n : ℕ) :
    divisorMultiplicity (k+1) n = ∑ d ∈ n.divisors, divisorMultiplicity k d := by
  simp only [divisorMultiplicity, pow_succ, ArithmeticFunction.mul_zeta_apply]

theorem reciprocal_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d : ℝ)) * (harmonic Q : ℝ) := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) =
      ∑ x ∈ s, f (e x).1 / (e x).1 / (e x).2 := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    dsimp only [e]
    rw [div_div, ← Nat.cast_mul, Nat.mul_div_cancel' hdq]
  rw [hsum]
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [t, Finset.sum_product, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
        harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.sum_comm]

theorem sum_divisorMultiplicity_reciprocal_le (k Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (divisorMultiplicity k q : ℝ) / (q : ℝ)) ≤
      (harmonic Q : ℝ) ^ k := by
  induction k with
  | zero =>
    by_cases hQ : Q = 0
    · subst Q; simp
    · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
      simp [divisorMultiplicity, ArithmeticFunction.one_apply, ite_div, hQ1]
  | succ k ih =>
    have h := reciprocal_divisor_sum_le (fun n => (divisorMultiplicity k n : ℝ))
      (fun n => Nat.cast_nonneg _) Q
    simp only [divisorMultiplicity_succ, Nat.cast_sum] at ⊢
    apply h.trans
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right ih (by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_MangoldtBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem endpointClassError_le (X : ℕ) {q c : ℕ} (hc : c < q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient| ≤
      (endpointError X q : ℝ) := by
  have h := Finset.le_sup (f := fun c => if Nat.Coprime c q then
    NNReal.mk (|residuePrefix ArithmeticFunction.vonMangoldt ⌊(X:ℝ)⌋₊ q c -
      (X:ℝ)/q.totient|) (abs_nonneg _) else 0) (Finset.mem_range.mpr hc)
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [ite_eq_left hcop, NNReal.coe_mk, Nat.floor_natCast, endpointError] using hr

theorem harmonic_le_twice_log {Q X : ℕ} (hQX : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    (harmonic Q : ℝ) ≤ 2 * Real.log (X:ℝ) := by
  have hmono : (harmonic Q : ℝ) ≤ (harmonic X : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hQX) (by intros; positivity)
  have hh := harmonic_le_one_add_log X
  linarith

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_CharacterErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem character_prefix_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterPrefix x χ=
      (q.totient:ℂ)*(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c:ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have he (n : ℕ) : (c:ZMod q)=(n:ZMod q) ↔ n%q=c := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hc]
    exact eq_comm
  unfold primeCharacterPrefix
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu,he]
  simp only [residuePrefix,residueSlice,Complex.ofReal_sum,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem character_error_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ=
      (q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have huinv : IsUnit (c:ZMod q)⁻¹ := by
    obtain ⟨u,hu⟩ := hu
    rw [←hu,ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have ht : (q.totient:ℂ)≠0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hq)
  simp only [primeCharacterError,mul_sub,Finset.sum_sub_distrib]
  rw [character_prefix_orthogonality x hq hc hcop]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,MulChar.one_apply huinv,one_mul]
  push_cast
  field_simp

theorem endpointClassError_le_character_sum (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient|≤
      (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ) := by
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hphi).mpr
  have hh := character_error_orthogonality x hq hc hcop
  calc
    _ = ‖(q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    _ = ‖∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := congrArg norm hh.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem characterMeanError_nonneg (x : ℝ) (q : ℕ) : 0≤characterMeanError x q := by
  unfold characterMeanError
  positivity

theorem endpointError_le_characterMeanError (x : ℝ) {q : ℕ} (hq : 0<q) :
    (endpointError x q:ℝ)≤characterMeanError x q := by
  change (endpointError x q:ℝ)≤(⟨characterMeanError x q,characterMeanError_nonneg x q⟩:NNReal)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro c hc
  split_ifs with hcop
  · exact NNReal.coe_le_coe.mp (endpointClassError_le_character_sum x hq (Finset.mem_range.mp hc) hcop)
  · exact bot_le

theorem vonMangoldt_noncoprime_sum_le (X : ℕ) {q : ℕ} (hq : 0<q) :
    (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)≤(Nat.log 2 X:ℝ)*Real.log q := by
  classical
  let S := (Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q ∧ ArithmeticFunction.vonMangoldt n≠0)
  have he : (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)=∑ n∈S,ArithmeticFunction.vonMangoldt n := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : Nat.Coprime n q <;> by_cases hn : ArithmeticFunction.vonMangoldt n=0 <;> simp [hcop,hn]
  rw [he]
  have hsub : S⊆(q^(Nat.log 2 X)).divisors := by
    intro n hn
    obtain ⟨hnI,hnq,hnv⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,k,hp,_hk,hpkn⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnv
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hdp : p∣q := by
      by_contra hd
      have hc := (hp'.coprime_iff_not_dvd).mpr hd
      exact hnq (hpkn ▸ hc.pow_left k)
    have hkX : k≤Nat.log 2 X := by
      apply Nat.le_log_of_pow_le (by norm_num : 1<2)
      calc
        2^k≤p^k := Nat.pow_le_pow_left hp'.two_le k
        _ = n := hpkn
        _ ≤ X := (Finset.mem_Ioc.mp hnI).2
    apply Nat.mem_divisors.mpr
    refine ⟨?_,pow_ne_zero _ (ne_of_gt hq)⟩
    rw [←hpkn]
    exact (pow_dvd_pow_of_dvd hdp k).trans (pow_dvd_pow q hkX)
  calc
    _ ≤ ∑ n∈(q^(Nat.log 2 X)).divisors,ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^(Nat.log 2 X):ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

theorem primitiveCharacter_eq_one_iff {q : ℕ} (hq : 0<q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro h
    rw [←DirichletCharacter.changeLevel_primitiveCharacter χ,h,DirichletCharacter.changeLevel_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem primeCharacterPrefix_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hsame (n : ℕ) (hn : Nat.Coprime n q) :
      χ.primitiveCharacter (n:ZMod χ.conductor)=χ (n:ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hzero (n : ℕ) (hn : ¬Nat.Coprime n q) : χ (n:ZMod q)=0 :=
    χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
  calc
    _ = ‖∑ n∈Finset.Ioc 0 ⌊x⌋₊,(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := by
      congr 1
      simp only [primeCharacterPrefix,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ n∈Finset.Ioc 0 ⌊x⌋₊,‖(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈(Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Coprime n q),ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : Nat.Coprime n q
      · simp [hn,hsame n hn]
      · simp only [ite_eq_left hn,hzero n hn,zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (χ.primitiveCharacter.norm_le_one _)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le _ hq

theorem primeCharacterError_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have he : primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter=
      primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter := by
    simp only [primeCharacterError,primitiveCharacter_eq_one_iff hq χ]
    ring
  rw [he]
  exact primeCharacterPrefix_primitive_difference x hq χ

theorem primeCharacterError_le_primitive (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ‖≤‖primeCharacterError x χ.primitiveCharacter‖+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hn := norm_add_le (primeCharacterError x χ.primitiveCharacter)
    (primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter)
  rw [add_sub_cancel] at hn
  exact hn.trans (add_le_add_right (primeCharacterError_primitive_difference x hq χ) _)

theorem characterMeanError_le_primitive_average (x : ℝ) {q : ℕ} (hq : 0<q) :
    characterMeanError x q≤
      (∑ χ : DirichletCharacter ℂ q,‖primeCharacterError x χ.primitiveCharacter‖)/(q.totient:ℝ)+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcard : Fintype.card (DirichletCharacter ℂ q)=q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold characterMeanError
  calc
    _ ≤ (∑ χ : DirichletCharacter ℂ q,(‖primeCharacterError x χ.primitiveCharacter‖+
        (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q))/(q.totient:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun χ _ => primeCharacterError_le_primitive x hq χ)) hphi.le
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,add_div]
      congr 1
      exact mul_div_cancel_left₀ _ hphi.ne'

theorem primitiveErrorMass_nonneg (x : ℝ) (d : ℕ) : 0≤primitiveErrorMass x d := by
  unfold primitiveErrorMass
  positivity

theorem induced_primitive_sum_le (x : ℝ) {q : ℕ} (hq : 0<q) :
    (∑ χ : DirichletCharacter ℂ q,‖primeCharacterError x χ.primitiveCharacter‖)≤
      ∑ d∈q.divisors,primitiveErrorMass x d := by
  classical
  let i : DirichletCharacter ℂ q → Sigma (DirichletCharacter ℂ) :=
    fun χ => ⟨χ.conductor,χ.primitiveCharacter⟩
  let lift : Sigma (DirichletCharacter ℂ) → DirichletCharacter ℂ q :=
    fun p => if h : p.1∣q then DirichletCharacter.changeLevel h p.2 else 1
  have hleft (χ : DirichletCharacter ℂ q) : lift (i χ)=χ := by
    dsimp [lift,i]
    rw [dite_eq_left χ.conductor_dvd_level,DirichletCharacter.changeLevel_primitiveCharacter]
  have hi : Function.Injective i := by
    intro χ ψ h
    simpa only [hleft] using congrArg lift h
  let S := q.divisors.sigma (fun d =>
    (Finset.univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive)
  have hsub : Finset.univ.image i⊆S := by
    intro p hp
    obtain ⟨χ,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level,ne_of_gt hq⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,χ.primitiveCharacter_isPrimitive⟩⟩
  calc
    _ = ∑ p∈Finset.univ.image i,‖primeCharacterError x p.2‖ := by
      rw [Finset.sum_image (fun _ _ _ _ h => hi h)]
    _ ≤ ∑ p∈S,‖primeCharacterError x p.2‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ = _ := by rw [Finset.sum_sigma]; rfl

theorem endpointError_le_primitive_conductors (x : ℝ) {q : ℕ} (hq : 0<q) :
    (endpointError x q:ℝ)≤(∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ)+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  apply (endpointError_le_characterMeanError x hq).trans
  apply (characterMeanError_le_primitive_average x hq).trans
  exact add_le_add_left (div_le_div_of_nonneg_right (induced_primitive_sum_le x hq) (Nat.cast_nonneg _)) _

theorem nat_le_card_divisors_mul_totient (q : ℕ) : q≤q.divisors.card*q.totient := by
  calc
    q = ∑ d∈q.divisors,d.totient := (Nat.sum_totient q).symm
    _ ≤ ∑ _d∈q.divisors,q.totient := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2))
        (Nat.totient_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
    _ = _ := by simp

theorem divisorMultiplicity_two (q : ℕ) : divisorMultiplicity 2 q=q.divisors.card := by
  rw [show 2=1+1 from rfl,divisorMultiplicity_succ]
  calc
    _ = ∑ _d∈q.divisors,1 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [divisorMultiplicity,ArithmeticFunction.zeta_apply_ne
        (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)).ne']
    _ = _ := by simp

theorem sum_totient_reciprocal_le (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(1:ℝ)/(q.totient:ℝ))≤(harmonic Q:ℝ)^2 := by
  apply le_trans (Finset.sum_le_sum (g:=fun q => (divisorMultiplicity 2 q:ℝ)/(q:ℝ)) ?_)
    (sum_divisorMultiplicity_reciprocal_le 2 Q)
  intro q hq
  have hq0 : (0:ℝ)<q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1
  rw [divisorMultiplicity_two,div_le_div_iff₀ hp hq0,one_mul]
  exact_mod_cast nat_le_card_divisors_mul_totient q

theorem reciprocal_totient_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q.totient : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d.totient : ℝ)) * (harmonic Q : ℝ)^2 := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q.totient : ℝ)) ≤
      ∑ x ∈ s, f (e x).1 / (e x).1.totient / (e x).2.totient := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    have hq0 : 0<q := (Finset.mem_Icc.mp hq).1
    have hd0 : 0<d := Nat.pos_of_dvd_of_pos hdq hq0
    have hk0 : 0<q/d := Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd0
    have ht : (d.totient:ℝ)*(q/d).totient≤q.totient := by
      have hh := Nat.totient_super_multiplicative d (q/d)
      rw [Nat.mul_div_cancel' hdq] at hh
      exact_mod_cast hh
    dsimp only [e]
    rw [div_div]
    exact div_le_div_of_nonneg_left (hf d) (mul_pos
      (by exact_mod_cast Nat.totient_pos.mpr hd0) (by exact_mod_cast Nat.totient_pos.mpr hk0)) ht
  apply hsum.trans
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1.totient : ℝ) / (x.2.totient : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1.totient : ℝ) / (x.2.totient : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = (∑ d∈Finset.Icc 1 Q,f d/(d.totient:ℝ))*(∑ k∈Finset.Icc 1 Q,(1:ℝ)/k.totient) := by
      simp only [t,Finset.sum_product,div_eq_mul_inv,one_mul,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_totient_reciprocal_le Q)
      (Finset.sum_nonneg (fun _ _ => div_nonneg (hf _) (Nat.cast_nonneg _)))

theorem endpointErrors_le_primitive_weighted_sum (x : ℝ) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ))≤
      (∑ d∈Finset.Icc 1 Q,primitiveErrorMass x d/(d.totient:ℝ))*(harmonic Q:ℝ)^2+
      (Q:ℝ)*(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log Q := by
  calc
    _ ≤ ∑ q∈Finset.Icc 1 Q,((∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ)+
        (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q) :=
      Finset.sum_le_sum (fun q hq => endpointError_le_primitive_conductors x (Finset.mem_Icc.mp hq).1)
    _ = (∑ q∈Finset.Icc 1 Q,(∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ))+
        ∑ q∈Finset.Icc 1 Q,(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := Finset.sum_add_distrib
    _ ≤ _ := by
      apply add_le_add (reciprocal_totient_divisor_sum_le _ (primitiveErrorMass_nonneg x) Q)
      calc
        _ ≤ ∑ _q∈Finset.Icc 1 Q,(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log Q := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_left (Real.log_le_log
            (by exact_mod_cast (Finset.mem_Icc.mp hq).1) (by exact_mod_cast (Finset.mem_Icc.mp hq).2))
            (Nat.cast_nonneg _)
        _ = _ := by simp [mul_assoc]

theorem vaughan_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      arithmeticCutoff U ArithmeticFunction.vonMangoldt+
      arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*ArithmeticFunction.log-
      arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
        arithmeticCutoff U ArithmeticFunction.vonMangoldt*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)+
      ((ArithmeticFunction.moebius:ArithmeticFunction ℝ)-arithmeticCutoff V ArithmeticFunction.moebius)*
        (ArithmeticFunction.vonMangoldt-arithmeticCutoff U ArithmeticFunction.vonMangoldt)*
        (ArithmeticFunction.zeta:ArithmeticFunction ℝ) := by
  rw [←ArithmeticFunction.vonMangoldt_mul_zeta]
  have hmu : (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta=1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  linear_combination
    (arithmeticCutoff U ArithmeticFunction.vonMangoldt-ArithmeticFunction.vonMangoldt)*hmu

theorem vaughanSecondCoefficient_eq (U n : ℕ) :
    vaughanSecondCoefficient U n=
      ∑ d∈n.divisors,if U<d then ArithmeticFunction.vonMangoldt d else 0 := by
  rw [vaughanSecondCoefficient,ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d _
  change ArithmeticFunction.vonMangoldt d-(if d≤U then ArithmeticFunction.vonMangoldt d else 0)=_
  by_cases hd : d≤U
  · simp [hd,not_lt_of_ge hd]
  · simp [hd,lt_of_not_ge hd]

theorem vaughanSecondCoefficient_nonneg (U n : ℕ) :
    0≤vaughanSecondCoefficient U n := by
  rw [vaughanSecondCoefficient_eq]
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem vaughanSecondCoefficient_le_log (U n : ℕ) :
    vaughanSecondCoefficient U n≤Real.log n := by
  rw [vaughanSecondCoefficient_eq,←ArithmeticFunction.vonMangoldt_sum]
  apply Finset.sum_le_sum
  intro d _
  split_ifs
  · rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem vaughanSecondCoefficient_zero_of_le {U n : ℕ} (hn : n≤U) :
    vaughanSecondCoefficient U n=0 := by
  rw [vaughanSecondCoefficient_eq]
  apply Finset.sum_eq_zero
  intro d hd
  have hdle := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
    (Nat.mem_divisors.mp hd).1
  exact ite_eq_right (by omega)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_AdditiveSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem symmetric_kernel_quadratic_le {ι : Type*} (s : Finset ι) (a : ι→ℝ)
    (w : ι→ι→ℝ) (hw : ∀ i∈s,∀ j∈s,0≤w i j)
    (hs : ∀ i∈s,∀ j∈s,w i j=w j i) :
    (∑ i∈s,∑ j∈s,a i*a j*w i j)≤∑ i∈s,a i^2*(∑ j∈s,w i j) := by
  have hh : (∑ i∈s,∑ j∈s,a i*a j*w i j)≤
      ∑ i∈s,∑ j∈s,(a i^2*w i j+a j^2*w i j)/2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have h := mul_nonneg (sq_nonneg (a i-a j)) (hw i hi j hj)
    nlinarith
  have hswap : (∑ i∈s,∑ j∈s,a j^2*w i j)=(∑ i∈s,∑ j∈s,a i^2*w i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j hj i hi]
  calc
    _ ≤ _ := hh
    _ = _ := by
      simp_rw [←Finset.sum_div,Finset.sum_add_distrib]
      rw [hswap]
      simp only [Finset.mul_sum]
      ring

theorem norm_sum_smul_sq_le_gram {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι→E) (c : ι→ℂ) :
    ‖∑ i∈s,c i • v i‖^2≤∑ i∈s,‖c i‖^2*(∑ j∈s,‖inner ℂ (v i) (v j)‖) := by
  calc
    _ = ∑ i∈s,∑ j∈s,(conj (c i)*(c j*inner ℂ (v i) (v j))).re := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]
      simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum,map_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change (c j * (conj (c i) * inner ℂ (v i) (v j))).re = _
      congr 1
      ring
    _ ≤ ∑ i∈s,∑ j∈s,‖c i‖*‖c j‖*‖inner ℂ (v i) (v j)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_mul,Complex.norm_conj,mul_assoc] using
        Complex.re_le_norm (conj (c i)*(c j*inner ℂ (v i) (v j)))
    _ ≤ _ := symmetric_kernel_quadratic_le s (fun i => ‖c i‖)
      (fun i j => ‖inner ℂ (v i) (v j)‖) (fun _ _ _ _ => norm_nonneg _)
      (fun i _ j _ => by rw [←inner_conj_symm,Complex.norm_conj])

theorem gram_large_sieve {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι→E) {B : ℝ} (hB : 0≤B)
    (hrows : ∀ i∈s,(∑ j∈s,‖inner ℂ (v i) (v j)‖)≤B) (x : E) :
    (∑ i∈s,‖inner ℂ (v i) x‖^2)≤B*‖x‖^2 := by
  let c : ι→ℂ := fun i => inner ℂ (v i) x
  let y : E := ∑ i∈s,c i • v i
  let A : ℝ := ∑ i∈s,‖c i‖^2
  have hA : 0≤A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy : ‖y‖^2≤B*A := by
    apply (norm_sum_smul_sq_le_gram s v c).trans
    calc
      _ ≤ ∑ i∈s,‖c i‖^2*B := Finset.sum_le_sum
        (fun i hi => mul_le_mul_of_nonneg_left (hrows i hi) (sq_nonneg _))
      _ = B*A := by rw [←Finset.sum_mul,mul_comm]
  have hxy : inner ℂ x y=(A:ℂ) := by
    simp only [y,inner_sum,inner_smul_right,A,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (v i) x * inner ℂ x (v i)=_
    rw [←inner_conj_symm x (v i)]
    simpa only [Complex.normSq_eq_norm_sq,c] using Complex.mul_conj (inner ℂ (v i) x)
  have hn := norm_inner_le_norm (𝕜:=ℂ) x y
  rw [hxy,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA] at hn
  have hn2 : A^2≤‖x‖^2*‖y‖^2 := by
    nlinarith [norm_nonneg x,norm_nonneg y]
  have hprod := mul_le_mul_of_nonneg_left hy (sq_nonneg ‖x‖)
  change A≤B*‖x‖^2
  by_cases hA0 : A=0
  · rw [hA0]
    exact mul_nonneg hB (sq_nonneg _)
  · apply le_of_mul_le_mul_right (a := A) ?_ (lt_of_le_of_ne hA (Ne.symm hA0))
    calc
      A*A = A^2 := by ring
      _ ≤ _ := hn2.trans hprod
      _ = (B*‖x‖^2)*A := by ring

theorem bvExp_add (x y : ℝ) : bvExp (x+y)=bvExp x*bvExp y := by
  unfold bvExp
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_bvExp (x : ℝ) : conj (bvExp x)=bvExp (-x) := by
  unfold bvExp
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem bvExp_nat_mul (n : ℕ) (x : ℝ) : bvExp ((n:ℝ)*x)=bvExp x^n := by
  unfold bvExp
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem bvExp_sub_one_lower {x : ℝ} (hx : |x|≤1/2) :
    4*|x|≤‖bvExp x-1‖ := by
  rw [bvExp,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hs : |Real.pi*x|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin hs
  rw [abs_mul,abs_of_pos Real.pi_pos] at h
  have hpi : Real.pi≠0 := ne_of_gt Real.pi_pos
  have he : 2/Real.pi*(Real.pi*|x|)=2*|x| := by field_simp
  rw [he] at h
  have hid : 2*Real.pi*x/2=Real.pi*x := by ring
  rw [hid,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem exponential_sum_bound (N : ℕ) {x : ℝ} (hx : |x|≤1/2) (hx0 : x≠0) :
    ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*x)‖≤1/(2*|x|) := by
  have ha : 0 < |x| := abs_pos.mpr hx0
  have hden := bvExp_sub_one_lower hx
  have hn : 0<‖bvExp x-1‖ := lt_of_lt_of_le (by positivity : 0<4*|x|) hden
  have he := geom_sum_mul (bvExp x) N
  have hnorm := congrArg norm he
  rw [norm_mul] at hnorm
  have hu : ‖bvExp x^N-1‖≤2 := by
    calc
      _ ≤ ‖bvExp x^N‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow]; norm_num
  have htimes : ‖∑ n∈Finset.range N,bvExp x^n‖*(4*|x|)≤2 := by
    exact (mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans (hnorm.trans_le hu)
  simp_rw [bvExp_nat_mul]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*|x|)).mpr
  nlinarith

theorem reciprocal_sum_le_harmonic {ι : Type*} (s : Finset ι) (t : ι→ℝ) (D : ℕ)
    (ht : ∀ i∈s,1≤t i ∧ t i≤D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→1≤|t i-t j|) :
    (∑ i∈s,1/t i)≤(harmonic D:ℝ) := by
  classical
  let r : ι→ℕ := fun i => ⌊t i⌋₊
  have hr : ∀ i∈s,r i∈Finset.Icc 1 D := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨Nat.le_floor (by simpa using (ht i hi).1),
      Nat.floor_le_of_le (ht i hi).2⟩
  have hinj : Set.InjOn r s := by
    intro i hi j hj he
    by_contra hij
    have h := hsep i hi j hj hij
    have hil := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht i hi).1)
    have hjl := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht j hj).1)
    have hiu := Nat.lt_floor_add_one (t i)
    have hju := Nat.lt_floor_add_one (t j)
    change ⌊t i⌋₊=⌊t j⌋₊ at he
    rw [he] at hil hiu
    rcases le_abs.mp h with h|h <;> linarith
  calc
    _ ≤ ∑ i∈s,1/(r i:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply one_div_le_one_div_of_le
      · exact_mod_cast (Finset.mem_Icc.mp (hr i hi)).1
      · exact Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht i hi).1)
    _ = ∑ k∈s.image r,1/(k:ℝ) := (Finset.sum_image (f := fun k : ℕ => (1:ℝ)/k) hinj).symm
    _ ≤ ∑ k∈Finset.Icc 1 D,1/(k:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hr)
        (fun _ _ _ => by positivity)
    _ = _ := by simp [harmonic_eq_sum_Icc]

theorem reciprocal_sum_le_scaled_harmonic {ι : Type*} (s : Finset ι) (t : ι→ℝ)
    {D : ℕ} (hD : 0<D) (ht : ∀ i∈s,1/(D:ℝ)≤t i ∧ t i≤1)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→1/(D:ℝ)≤|t i-t j|) :
    (∑ i∈s,1/t i)≤(D:ℝ)*(harmonic D:ℝ) := by
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hh := reciprocal_sum_le_harmonic s (fun i => (D:ℝ)*t i) D
    (fun i hi => ⟨by have h := mul_le_mul_of_nonneg_left (ht i hi).1 hDr.le
                     field_simp at h
                     nlinarith,
      by nlinarith [(ht i hi).2]⟩)
    (fun i hi j hj hij => by
      rw [←mul_sub,abs_mul,abs_of_pos hDr]
      have h := (div_le_iff₀ hDr).mp (hsep i hi j hj hij)
      nlinarith)
  have hm := mul_le_mul_of_nonneg_left hh hDr.le
  rw [Finset.mul_sum] at hm
  calc
    _ = ∑ i∈s,(D:ℝ)*(1/((D:ℝ)*t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ ≤ _ := hm

theorem bvExp_sub_int (x : ℝ) (m : ℤ) : bvExp (x-m)=bvExp x := by
  rw [sub_eq_add_neg,bvExp_add]
  have h : bvExp (-(m:ℝ))=1 := by simpa using bvExp_int (-m)
  rw [h,mul_one]

theorem abs_bvCentered_le (x : ℝ) : |bvCentered x|≤1/2 := by
  have hl := Int.floor_le (x+1/2)
  have hu := Int.lt_floor_add_one (x+1/2)
  dsimp [bvCentered]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem bvExp_centered (x : ℝ) : bvExp (bvCentered x)=bvExp x := bvExp_sub_int _ _

theorem exponential_sum_centered (N : ℕ) (x : ℝ) :
    (∑ n∈Finset.range N,bvExp ((n:ℝ)*bvCentered x))=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*x) := by
  simp_rw [bvExp_nat_mul,bvExp_centered]

theorem centered_difference_separated {ι : Type*} (s : Finset ι) (θ : ι→ℝ) {D : ℕ}
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (a : ℝ) {i j : ι} (hi : i∈s) (hj : j∈s) (hij : i≠j) :
    1/(D:ℝ)≤|bvCentered (θ i-a)-bvCentered (θ j-a)| := by
  have h := hsep i hi j hj hij (⌊θ i-a+1/2⌋-⌊θ j-a+1/2⌋)
  dsimp [bvCentered]
  convert h using 2
  push_cast
  ring

theorem exponential_kernel_row_bound {ι : Type*} (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) {i : ι} (hi : i∈s) :
    (∑ j∈s,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by
  classical
  let t := s.erase i
  let r := fun j => bvCentered (θ j-θ i)
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hr : ∀ j∈t,1/(D:ℝ)≤|r j| := by
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hji,hjs⟩
    exact hsep j hjs i hi hji ⌊θ j-θ i+1/2⌋
  have hn : ∀ j∈t,r j≠0 := by
    intro j hj hj0
    have h := hr j hj
    rw [hj0,abs_zero] at h
    exact (not_le_of_gt (one_div_pos.mpr hDr)) h
  have hpair : ∀ j∈t,∀ k∈t,j≠k→1/(D:ℝ)≤|r j-r k| := by
    intro j hj k hk hjk
    exact centered_difference_separated s θ hsep (θ i)
      (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hjk
  have hhalf : ∀ b:Bool,
      (∑ j∈t.filter (fun j => decide (0≤r j)=b),1/|r j|)≤(D:ℝ)*(harmonic D:ℝ) := by
    intro b
    apply reciprocal_sum_le_scaled_harmonic _ _ hD
    · intro j hj
      exact ⟨hr j ((Finset.mem_filter.mp hj).1),(abs_bvCentered_le _).trans (by norm_num)⟩
    · intro j hj k hk hjk
      have h := hpair j ((Finset.mem_filter.mp hj).1) k ((Finset.mem_filter.mp hk).1) hjk
      have hjb := (Finset.mem_filter.mp hj).2
      have hkb := (Finset.mem_filter.mp hk).2
      cases b <;> simp only [decide_eq_false_iff_not,decide_eq_true_eq,not_le] at hjb hkb
      · simpa only [abs_of_neg hjb,abs_of_neg hkb,neg_sub_neg,abs_sub_comm] using h
      · simpa only [abs_of_nonneg hjb,abs_of_nonneg hkb] using h
  have hrec : (∑ j∈t,1/|r j|)≤2*(D:ℝ)*(harmonic D:ℝ) := by
    have hp := hhalf true
    have hm := hhalf false
    simp only [decide_eq_true_eq,decide_eq_false_iff_not] at hp hm
    have he := Finset.sum_filter_add_sum_filter_not t (fun j => 0≤r j) (fun j => 1/|r j|)
    linarith
  have hoff : (∑ j∈t,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (D:ℝ)*(harmonic D:ℝ) := by
    calc
      _ ≤ ∑ j∈t,1/(2*|r j|) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [←exponential_sum_centered]
        exact exponential_sum_bound N (abs_bvCentered_le _) (hn j hj)
      _ = (∑ j∈t,1/|r j|)/2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := by linarith
  rw [←Finset.sum_erase_add _ _ hi]
  have hd : ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ i-θ i))‖=(N:ℝ) := by simp
  rw [hd]
  linarith

theorem inner_bvExponentialVector (N : ℕ) (θ η : ℝ) :
    inner ℂ (bvExponentialVector N θ) (bvExponentialVector N η)=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ-η)) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,bvExponentialVector]
  simp_rw [mul_comm (bvExp _)]
  simp_rw [conj_bvExp,←bvExp_add]
  have he : ∀ n:Fin N,-(-((n:ℕ):ℝ)*θ)+(-((n:ℕ):ℝ)*η)=((n:ℕ):ℝ)*(θ-η) := by
    intro n
    ring
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => bvExp ((n:ℝ)*(θ-η))) N

theorem inner_bvExponentialVector_coefficients (N : ℕ) (θ : ℝ) (a : Fin N→ℂ) :
    inner ℂ (bvExponentialVector N θ) (WithLp.toLp 2 a)=
      ∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*θ) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,bvExponentialVector]
  apply Finset.sum_congr rfl
  intro n _
  rw [conj_bvExp]
  congr 2
  ring

theorem additive_large_sieve {ι : Type*} (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) (a : Fin N→ℂ) :
    (∑ i∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*θ i)‖^2)≤
      ((N:ℝ)+(D:ℝ)*(harmonic D:ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  have hH : 0≤(harmonic D:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact Finset.sum_nonneg (fun _ _ => by simp only [Rat.cast_inv,Rat.cast_natCast]; positivity)
  have hB : 0≤(N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by positivity
  have hr : ∀ i∈s,(∑ j∈s,‖inner ℂ (bvExponentialVector N (θ i))
      (bvExponentialVector N (θ j))‖)≤(N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by
    intro i hi
    simp_rw [inner_bvExponentialVector]
    have hh := exponential_kernel_row_bound s (fun i => -θ i) hD
      (fun j hj k hk hjk m => by
        have h := hsep j hj k hk hjk (-m)
        have he : -θ j- -θ k-(m:ℝ)=-(θ j-θ k-(-m:ℤ)) := by
          push_cast
          ring
        rw [he,abs_neg]
        exact h) N hi
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring
  have h := gram_large_sieve s (fun i => bvExponentialVector N (θ i)) hB hr (WithLp.toLp 2 a)
  simpa only [inner_bvExponentialVector_coefficients,EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp] using h

theorem rat_abs_lower (r : ℚ) (hr : r≠0) : 1/(r.den:ℝ)≤|(r:ℝ)| := by
  have hn : r.num≠0 := fun h => hr (Rat.zero_of_num_zero h)
  have ha : (1:ℝ)≤|(r.num:ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  rw [Rat.cast_def,abs_div,abs_of_pos (by exact_mod_cast r.den_pos : (0:ℝ)<r.den)]
  exact div_le_div_of_nonneg_right ha (Nat.cast_nonneg _)

theorem rational_frequency_separation {r t : ℚ} {Q : ℕ}
    (hr : 0≤r ∧ r<1) (ht : 0≤t ∧ t<1) (hrt : r≠t)
    (hrQ : r.den≤Q) (htQ : t.den≤Q) (m : ℤ) :
    1/((Q^2:ℕ):ℝ)≤|(r:ℝ)-(t:ℝ)-m| := by
  have hu0 : r-t-(m:ℚ)≠0 := by
    intro he
    have hm0 : m=0 := by
      have hlo : (-1:ℚ)<(m:ℚ) := by linarith [hr.1,ht.2]
      have hup : (m:ℚ)<1 := by linarith [ht.1,hr.2]
      have h1 : (-1:ℤ) < m := by exact_mod_cast hlo
      have h2 : m<1 := by exact_mod_cast hup
      omega
    simp only [hm0,Int.cast_zero,sub_zero,sub_eq_zero] at he
    exact hrt he
  have hd : (r-t-(m:ℚ)).den≤Q^2 := by
    rw [Rat.sub_intCast_den]
    calc
      _ ≤ r.den*t.den := Nat.le_of_dvd (Nat.mul_pos r.den_pos t.den_pos) (Rat.sub_den_dvd _ _)
      _ ≤ Q*Q := Nat.mul_le_mul hrQ htQ
      _ = _ := by ring
  have hl := rat_abs_lower (r-t-(m:ℚ)) hu0
  push_cast at hl
  exact (one_div_le_one_div_of_le
    (by exact_mod_cast (r-t-(m:ℚ)).den_pos : (0:ℝ)<(r-t-(m:ℚ)).den)
    (by exact_mod_cast hd)).trans hl

theorem rational_additive_large_sieve (s : Finset ℚ) {Q : ℕ} (hQ : 0<Q)
    (hs : ∀ r∈s,0≤r ∧ r<1 ∧ r.den≤Q) (N : ℕ) (a : Fin N→ℂ) :
    (∑ r∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(r:ℝ))‖^2)≤
      ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  have h := additive_large_sieve s (fun r => (r:ℝ)) (pow_pos hQ 2)
    (fun r hr t ht hrt m => rational_frequency_separation
      ⟨(hs r hr).1,(hs r hr).2.1⟩ ⟨(hs t ht).1,(hs t ht).2.1⟩ hrt
      (hs r hr).2.2 (hs t ht).2.2 m) N a
  simpa only [Nat.cast_pow] using h

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_MultiplicativeSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem conj_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) :
    conj (ZMod.stdAddChar a)=ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv]
  exact Circle.coe_inv_eq_conj (ZMod.toCircle a) |>.symm

theorem conj_gaussSum_eq_dft_inverse {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    conj (gaussSum χ ZMod.stdAddChar)=ZMod.dft (χ⁻¹ : DirichletCharacter ℂ q) 1 := by
  simp only [gaussSum,map_sum,map_mul,ZMod.dft_apply,smul_eq_mul,mul_one]
  apply Finset.sum_congr rfl
  intro a _
  rw [conj_stdAddChar]
  have h : conj (χ a)=(χ⁻¹) a := MulChar.star_apply' χ a
  rw [h,mul_comm]

theorem primitive_gauss_mul_conjugate {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar*conj (gaussSum χ ZMod.stdAddChar)=(q:ℂ) := by
  have hf : ZMod.dft χ=(fun k => χ⁻¹ (-k)*gaussSum χ ZMod.stdAddChar) := by
    funext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hh := congrFun (ZMod.dft_dft χ) (-1)
  rw [hf,ZMod.dft_mul_const,ZMod.dft_comp_neg] at hh
  change ZMod.dft (χ⁻¹ : DirichletCharacter ℂ q) (-(-1))*gaussSum χ ZMod.stdAddChar=_ at hh
  simp only [neg_neg,map_one,smul_eq_mul,mul_one] at hh
  rw [conj_gaussSum_eq_dft_inverse,mul_comm]
  exact hh

theorem primitive_gauss_norm_sq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : ‖gaussSum χ ZMod.stdAddChar‖^2=(q:ℝ) := by
  have h := primitive_gauss_mul_conjugate hχ
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

theorem conj_character_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    conj (χ u)=χ (u.val⁻¹) := by
  change star (χ (u:ZMod q))=_
  rw [MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit,ZMod.inv_coe_unit]

theorem inner_characterUnitVector {q : ℕ} [NeZero q] (u v : (ZMod q)ˣ) :
    inner ℂ (characterUnitVector u) (characterUnitVector v)=if u=v then (q.totient:ℂ) else 0 := by
  classical
  simp only [PiLp.inner_apply,RCLike.inner_apply,characterUnitVector]
  simp_rw [conj_character_unit]
  have he : (∑ χ : DirichletCharacter ℂ q,χ v*χ (u.val⁻¹))=
      ∑ χ : DirichletCharacter ℂ q,χ (u.val⁻¹)*χ v := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [mul_comm]
  rw [he,DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
  simp only [Units.val_inj]

theorem character_transform_bound {q : ℕ} [NeZero q] (f : (ZMod q)ˣ→ℂ) :
    (∑ χ : DirichletCharacter ℂ q,‖∑ u : (ZMod q)ˣ, f u*χ u‖^2)≤
      (q.totient:ℝ)*(∑ u : (ZMod q)ˣ,‖f u‖^2) := by
  classical
  have hv : ∀ u : (ZMod q)ˣ,(∑ v : (ZMod q)ˣ,
      ‖inner ℂ (characterUnitVector u) (characterUnitVector v)‖)=(q.totient:ℝ) := by
    intro u
    simp only [inner_characterUnitVector]
    simp_rw [apply_ite norm]
    simp
  have h := norm_sum_smul_sq_le_gram Finset.univ (fun u : (ZMod q)ˣ => characterUnitVector u) f
  simp_rw [hv] at h
  rw [←Finset.sum_mul,mul_comm] at h
  rw [EuclideanSpace.norm_sq_eq] at h
  simpa only [WithLp.ofLp_sum,WithLp.ofLp_smul,characterUnitVector,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul] using h

theorem primitive_inverse {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  change (χ⁻¹).conductor=q
  rw [DirichletCharacter.conductor_inv]
  exact hχ

theorem multiply_sum_units {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (f : ZMod q→ℂ) :
    (∑ x:ZMod q,χ x*f x)=∑ u:(ZMod q)ˣ,χ u*f u := by
  symm
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro x hx
    have hu : ¬IsUnit x := by
      rintro ⟨u,rfl⟩
      exact hx ⟨u,rfl⟩
    rw [MulChar.map_nonunit _ hu,zero_mul]
  · intro u
    rfl

theorem primitive_character_gauss_expansion {q N : ℕ} [NeZero q]
    (a : Fin N→ℂ) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum (χ⁻¹) ZMod.stdAddChar*sequenceCharacterSum a χ=
      ∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u := by
  have hg (n:Fin N) := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar
    (primitive_inverse hχ) (((n:ℕ):ZMod q))
  simp only [inv_inv] at hg
  unfold sequenceCharacterSum
  rw [Finset.mul_sum]
  calc
    _ = ∑ n:Fin N,a n*gaussSum (χ⁻¹) (ZMod.stdAddChar.mulShift (((n:ℕ):ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hg]
      ring
    _ = ∑ x:ZMod q,(χ⁻¹) x*modularFourierSum a x := by
      simp only [gaussSum,AddChar.mulShift_apply,Finset.mul_sum,modularFourierSum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ u:(ZMod q)ˣ,(χ⁻¹) u*modularFourierSum (q:=q) a (u:ZMod q) := multiply_sum_units _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_comm]

theorem primitive_character_energy_le {q N : ℕ} [NeZero q] (a : Fin N→ℂ) :
    (q:ℝ)/(q.totient:ℝ)*
        (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖sequenceCharacterSum a χ‖^2)≤
      ∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) a (u:ZMod q)‖^2 := by
  classical
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hs : (q:ℝ)*
        (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖sequenceCharacterSum a χ‖^2)≤
      (q.totient:ℝ)*(∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) a (u:ZMod q)‖^2) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u‖^2 := by
        apply Finset.sum_congr rfl
        intro χ hχ
        have hp := (Finset.mem_filter.mp hχ).2
        have h := congrArg (fun z:ℂ => ‖z‖^2) (primitive_character_gauss_expansion a hp)
        rwa [norm_mul,mul_pow,primitive_gauss_norm_sq (primitive_inverse hp)] at h
      _ ≤ ∑ χ:DirichletCharacter ℂ q,‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ = ∑ χ:DirichletCharacter ℂ q,‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*χ u‖^2 := by
        exact Fintype.sum_bijective (fun χ : DirichletCharacter ℂ q => χ⁻¹)
          inv_involutive.bijective _ _ (fun _ => rfl)
      _ ≤ _ := character_transform_bound _
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hφ).mpr (by simpa only [mul_comm] using hs)

theorem unitFrequency_den {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) : (unitFrequency u).den=q := by
  have hc : Nat.Coprime u.val.val q := (ZMod.isUnit_iff_coprime _ _).mp
    (by simpa only [ZMod.natCast_zmod_val] using u.isUnit)
  have he : unitFrequency u=Rat.divInt (u.val.val:ℤ) (q:ℤ) := by
    rw [Rat.divInt_eq_div]
    simp only [unitFrequency,Int.cast_natCast]
  rw [he,Rat.den_divInt]
  simp only [ite_eq_right (Int.natCast_ne_zero.mpr (NeZero.ne q)), Int.natAbs_natCast,
    Int.gcd_natCast_natCast,hc.symm.gcd_eq_one,Nat.div_one]

theorem unitFrequency_bounds {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    0≤unitFrequency u ∧ unitFrequency u<1 := by
  have hq : (0:ℚ)<q := by exact_mod_cast NeZero.pos q
  exact ⟨div_nonneg (Nat.cast_nonneg _) hq.le,(div_lt_one hq).mpr (by exact_mod_cast ZMod.val_lt u.val)⟩

theorem fareyFrequency_injective (Q : ℕ) :
    Function.Injective (fareyFrequency (Q:=Q)) := by
  rintro ⟨q,u⟩ ⟨r,v⟩ he
  have hd := congrArg Rat.den he
  simp only [fareyFrequency,unitFrequency_den] at hd
  have hqr : q=r := Fin.ext (by omega)
  subst r
  have hv : u=v := by
    apply Units.val_injective
    apply ZMod.val_injective
    change (u.val.val:ℚ)/(q.val+1:ℕ)=(v.val.val:ℚ)/(q.val+1:ℕ) at he
    have hq : ((q.val+1:ℕ):ℚ)≠0 := by positivity
    have he' := (div_left_inj' hq).mp he
    exact_mod_cast he'
  subst v
  rfl

theorem modularFourierSum_eq_bvExp {q N : ℕ} [NeZero q] (a : Fin N→ℂ) (u : (ZMod q)ˣ) :
    modularFourierSum (q:=q) a (u:ZMod q)=
      ∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(unitFrequency u:ℝ)) := by
  unfold modularFourierSum
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have he : (((n:ℕ)*u.val.val:ℕ):ZMod q)=((n:ℕ):ZMod q)*(u:ZMod q) := by simp
  rw [←he]
  have hh := ZMod.stdAddChar_coe (N:=q) (((n:ℕ)*u.val.val:ℕ):ℤ)
  simp only [Int.cast_natCast] at hh
  rw [hh]
  unfold bvExp unitFrequency
  push_cast
  congr 1
  ring

theorem multiplicative_large_sieve (Q N : ℕ) (a : Fin N→ℂ) :
    (∑ q:Fin Q,((q.val+1:ℕ):ℝ)/((q.val+1).totient:ℝ)*
      (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ (q.val+1))).filter (fun χ => χ.IsPrimitive),
        ‖sequenceCharacterSum a χ‖^2))≤
      ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  classical
  by_cases hQ : Q=0
  · subst Q
    simp only [Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero,zero_pow (by decide : 2≠0),
      zero_mul,add_zero]
    positivity
  have hQpos : 0<Q := Nat.pos_of_ne_zero hQ
  let s : Finset ℚ := Finset.univ.image (fareyFrequency (Q:=Q))
  have hs : ∀ r∈s,0≤r ∧ r<1 ∧ r.den≤Q := by
    intro r hr
    obtain ⟨⟨q,u⟩,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨(unitFrequency_bounds u).1,(unitFrequency_bounds u).2,by
      rw [fareyFrequency,unitFrequency_den]
      omega⟩
  calc
    _ ≤ ∑ q:Fin Q,∑ u:(ZMod (q.val+1))ˣ,‖modularFourierSum (q:=q.val+1) a (u:ZMod (q.val+1))‖^2 :=
      Finset.sum_le_sum (fun _ _ => primitive_character_energy_le a)
    _ = ∑ r∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(r:ℝ))‖^2 := by
      dsimp only [s]
      rw [Finset.sum_image (fareyFrequency_injective Q).injOn,Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro u _
      rw [modularFourierSum_eq_bvExp]
      rfl
    _ ≤ _ := rational_additive_large_sieve s hQpos hs N a

theorem weighted_sum_mul_sq_le {ι : Type*} (s : Finset ι) (w f g : ι→ℝ)
    (hw : ∀ i∈s,0≤w i) :
    (∑ i∈s,w i*(f i*g i))^2≤(∑ i∈s,w i*f i^2)*(∑ i∈s,w i*g i^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i _
    exact le_of_eq (by ring)

theorem primitiveCharacterMean_nonneg {Q : ℕ}
    (f : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ)
    (hf : ∀ q χ,0≤f q χ) : 0≤primitiveCharacterMean Q f := by
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ => hf q χ))

theorem primitiveCharacterMean_cauchy {Q : ℕ}
    (f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    (primitiveCharacterMean Q (fun q χ=>f q χ*g q χ))^2≤
      primitiveCharacterMean Q (fun q χ=>f q χ^2)*
      primitiveCharacterMean Q (fun q χ=>g q χ^2) := by
  classical
  let w : (Σ q:Fin Q,DirichletCharacter ℂ (q.val+1))→ℝ := fun x =>
    if x.2.IsPrimitive then ((x.1.val+1:ℕ):ℝ)/((x.1.val+1).totient:ℝ) else 0
  have hw (x : Σ q:Fin Q,DirichletCharacter ℂ (q.val+1)) : 0≤w x := by
    dsimp [w]
    split <;> positivity
  have hsum (a : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
      (∑ x : Σ q:Fin Q,DirichletCharacter ℂ (q.val+1),w x*a x.1 x.2)=
        primitiveCharacterMean Q a := by
    rw [Fintype.sum_sigma]
    unfold primitiveCharacterMean
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    dsimp [w]
    split <;> simp_all
  have h:=weighted_sum_mul_sq_le Finset.univ w (fun x=>f x.1 x.2) (fun x=>g x.1 x.2)
    (fun x _ => hw x)
  rw [←hsum (fun q χ=>f q χ*g q χ),←hsum (fun q χ=>f q χ^2),
    ←hsum (fun q χ=>g q χ^2)]
  exact h

theorem bilinear_multiplicative_large_sieve (Q M N : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ) :
    (primitiveCharacterMean Q (fun _ χ=>‖sequenceCharacterSum a χ*sequenceCharacterSum b χ‖))^2≤
      (((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ m:Fin M,‖a m‖^2))*
      (((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖b n‖^2)) := by
  have h:=primitiveCharacterMean_cauchy (Q:=Q)
    (fun _ χ=>‖sequenceCharacterSum a χ‖) (fun _ χ=>‖sequenceCharacterSum b χ‖)
  simp only [norm_mul]
  exact h.trans (mul_le_mul (multiplicative_large_sieve Q M a) (multiplicative_large_sieve Q N b)
    (primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _))
    ((primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _)).trans (multiplicative_large_sieve Q M a)))

theorem exponential_kernel_offdiagonal_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) {i : ι} (hi : i∈s) :
    (∑ j∈s.erase i,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (D:ℝ)*(harmonic D:ℝ) := by
  have h:=exponential_kernel_row_bound s θ hD hsep N hi
  rw [←Finset.sum_erase_add _ _ hi] at h
  have hd : ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ i-θ i))‖=(N:ℝ) := by simp
  rw [hd] at h
  linarith

theorem residue_frequency_separation {q : ℕ} [NeZero q] {a b : ZMod q}
    (hab : a≠b) (m : ℤ) :
    1/(q:ℝ)≤|(a.val:ℝ)/q-(b.val:ℝ)/q-m| := by
  have hz : (a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)≠0 := by
    intro he
    have h:=congrArg (fun t:ℤ => (t:ZMod q)) he
    simp only [Int.cast_sub,Int.cast_natCast,Int.cast_mul,ZMod.natCast_self,mul_zero,
      sub_zero,Int.cast_zero,ZMod.natCast_zmod_val] at h
    exact hab (sub_eq_zero.mp h)
  have hnum : (1:ℝ)≤|(((a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)):ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have he : (a.val:ℝ)/q-(b.val:ℝ)/q-m=
      ((((a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)):ℤ):ℝ)/(q:ℝ) := by
    push_cast
    field_simp
  rw [he,abs_div,abs_of_pos hq]
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using
    div_le_div_of_nonneg_right hnum hq.le

theorem modularFourierSum_one {q N : ℕ} [NeZero q] (u : ZMod q) :
    modularFourierSum (q:=q) (fun _:Fin N=>1) u=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*((u.val:ℝ)/q)) := by
  unfold modularFourierSum
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [one_mul]
  have he : (((n:ℕ)*u.val:ℕ):ZMod q)=((n:ℕ):ZMod q)*u := by simp
  rw [←he]
  have hh:=ZMod.stdAddChar_coe (N:=q) (((n:ℕ)*u.val:ℕ):ℤ)
  simp only [Int.cast_natCast] at hh
  rw [hh]
  unfold bvExp
  push_cast
  congr 1
  ring

theorem primitive_polya_vinogradov {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n:Fin N,χ ((n:ℕ):ZMod q)‖≤Real.sqrt q*(harmonic q:ℝ) := by
  classical
  let : NeZero q := ⟨by omega⟩
  let : Fact (1<q) := ⟨hq⟩
  let θ : ZMod q→ℝ := fun x=>(x.val:ℝ)/q
  let f : ZMod q→ℝ := fun u=>‖∑ n∈Finset.range N,bvExp ((n:ℝ)*θ u)‖
  have hr : (∑ u∈(Finset.univ : Finset (ZMod q)).erase 0,f u)≤(q:ℝ)*(harmonic q:ℝ) := by
    have h:=exponential_kernel_offdiagonal_bound Finset.univ θ (by omega : 0<q)
      (fun _ _ _ _ hne m => residue_frequency_separation hne m) N (Finset.mem_univ (0:ZMod q))
    simpa only [θ,ZMod.val_zero,Nat.cast_zero,zero_div,sub_zero,f] using h
  have hu : Finset.univ.image (fun u:(ZMod q)ˣ=>(u:ZMod q))⊆(Finset.univ : Finset (ZMod q)).erase 0 := by
    intro x hx
    obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨Units.ne_zero u,Finset.mem_univ _⟩
  have hg:=primitive_character_gauss_expansion (fun _:Fin N=>1) hχ
  have hnorm : ‖gaussSum (χ⁻¹) ZMod.stdAddChar‖*
      ‖∑ n:Fin N,χ ((n:ℕ):ZMod q)‖≤(q:ℝ)*(harmonic q:ℝ) := by
    calc
      _ = ‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) (fun _:Fin N=>1) (u:ZMod q)*(χ⁻¹) u‖ := by
        simpa only [norm_mul,sequenceCharacterSum,one_mul] using congrArg norm hg
      _ ≤ ∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) (fun _:Fin N=>1) (u:ZMod q)*(χ⁻¹) u‖ := norm_sum_le _ _
      _ ≤ ∑ u:(ZMod q)ˣ,f (u:ZMod q) := by
        apply Finset.sum_le_sum
        intro u _
        rw [norm_mul,modularFourierSum_one]
        exact mul_le_of_le_one_right (norm_nonneg _) ((χ⁻¹).norm_le_one _)
      _ = ∑ x∈Finset.univ.image (fun u:(ZMod q)ˣ=>(u:ZMod q)),f x := by
        rw [Finset.sum_image Units.val_injective.injOn]
      _ ≤ ∑ x∈(Finset.univ : Finset (ZMod q)).erase 0,f x :=
        Finset.sum_le_sum_of_subset_of_nonneg hu (fun _ _ _ => norm_nonneg _)
      _ ≤ _ := hr
  have hgn : ‖gaussSum (χ⁻¹) ZMod.stdAddChar‖=Real.sqrt q := by
    have hs:=primitive_gauss_norm_sq (primitive_inverse hχ)
    rw [←hs,Real.sqrt_sq (norm_nonneg _)]
  rw [hgn] at hnorm
  have hsq : (Real.sqrt (q:ℝ))^2=(q:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hpos : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<q by omega))
  have he : (q:ℝ)*(harmonic q:ℝ)=Real.sqrt q*(Real.sqrt q*(harmonic q:ℝ)) := by
    calc
      _ = (Real.sqrt (q:ℝ))^2*(harmonic q:ℝ) := by rw [hsq]
      _ = _ := by ring
  rw [he] at hnorm
  exact (mul_le_mul_iff_right₀ hpos).mp hnorm

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_VaughanIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem monotone_weighted_prefix_bound (g : ℕ→ℂ) (w : ℕ→ℝ) (hw : Monotone w)
    (hw0 : 0≤w 0) {B : ℝ} (hB : 0≤B) (N : ℕ)
    (hg : ∀ n≤N,‖∑ i∈Finset.range n,g i‖≤B) :
    ‖∑ i∈Finset.range N,(w i:ℂ)*g i‖≤2*w (N-1)*B := by
  have hwpos (n : ℕ) : 0≤w n := hw0.trans (hw (Nat.zero_le n))
  have hd (n : ℕ) : 0≤w (n+1)-w n := sub_nonneg.mpr (hw (by omega))
  have he:=Finset.sum_range_by_parts w g N
  simp only [Complex.real_smul] at he
  rw [he]
  calc
    _ ≤ ‖(w (N-1):ℂ)*(∑ i∈Finset.range N,g i)‖+
        ‖∑ i∈Finset.range (N-1),((w (i+1)-w i:ℝ):ℂ)*(∑ j∈Finset.range (i+1),g j)‖ := norm_sub_le _ _
    _ ≤ w (N-1)*B+(∑ i∈Finset.range (N-1),(w (i+1)-w i)*B) := by
      apply add_le_add
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos _)]
        exact mul_le_mul_of_nonneg_left (hg N le_rfl) (hwpos _)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd _)]
        exact mul_le_mul_of_nonneg_left (hg (i+1) (by have h:=Finset.mem_range.mp hi; omega)) (hd _)
    _ = w (N-1)*B+(w (N-1)-w 0)*B := by
      rw [←Finset.sum_mul,Finset.sum_range_sub]
    _ ≤ _ := by nlinarith

theorem log_nat_monotone : Monotone (fun n:ℕ=>Real.log n) := by
  intro n m hnm
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,Real.log_zero]
    by_cases hm : m=0
    · simp [hm]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm)
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn) (by exact_mod_cast hnm)

theorem primitive_log_character_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n∈Finset.range N,(Real.log n:ℂ)*χ (n:ZMod q)‖≤
      2*Real.log N*(Real.sqrt q*(harmonic q:ℝ)) := by
  have hH : 0≤(harmonic q:ℝ) := by exact_mod_cast (harmonic_pos (by omega : q≠0)).le
  have hB : 0≤Real.sqrt q*(harmonic q:ℝ) := mul_nonneg (Real.sqrt_nonneg _) hH
  have h:=monotone_weighted_prefix_bound (fun n=>χ (n:ZMod q)) (fun n:ℕ=>Real.log n)
    log_nat_monotone (by simp) hB N (fun n _ => by
      rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>χ (i:ZMod q)) n]
      exact primitive_polya_vinogradov hq hχ n)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (log_nat_monotone (Nat.sub_le N 1)) (by norm_num)) hB)

theorem primitive_typeI_log_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (X D : ℕ) (a : ℕ→ℂ) :
    ‖∑ d∈Finset.Icc 1 D,a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q))‖≤
      (∑ d∈Finset.Icc 1 D,‖a d‖)*
        (2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
  calc
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d‖*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul,norm_mul]
      apply mul_le_mul
      · exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      · exact (primitive_log_character_bound hq hχ _).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (log_nat_monotone (Nat.add_le_add_right (Nat.div_le_self X d) 1)) (by norm_num))
            (mul_nonneg (Real.sqrt_nonneg _) (by exact_mod_cast (harmonic_pos (by omega : q≠0)).le)))
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = _ := by rw [Finset.sum_mul]

theorem primitive_typeI_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (X D : ℕ) (a : ℕ→ℂ) :
    ‖∑ d∈Finset.Icc 1 D,a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),χ (n:ZMod q))‖≤
      (∑ d∈Finset.Icc 1 D,‖a d‖)*(Real.sqrt q*(harmonic q:ℝ)) := by
  calc
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),χ (n:ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d‖*(Real.sqrt q*(harmonic q:ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul,norm_mul]
      apply mul_le_mul
      · exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      · rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>χ (i:ZMod q)) (X/d+1)]
        exact primitive_polya_vinogradov hq hχ (X/d+1)
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = _ := by rw [Finset.sum_mul]

theorem sequenceSize_nonneg {N : ℕ} (a : Fin N→ℂ) : 0 ≤ sequenceSize a := Real.sqrt_nonneg _

theorem sequenceSize_sq {N : ℕ} (a : Fin N→ℂ) :
    sequenceSize a^2=∑ n:Fin N,‖a n‖^2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _=>sq_nonneg _))

theorem sequenceMask_size_le {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) :
    sequenceSize (sequenceMask p a) ≤ sequenceSize a := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro n _
  dsimp [sequenceMask]
  split <;> simp

theorem sequenceMask_size_partition {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) :
    sequenceSize (sequenceMask p a)^2+sequenceSize (sequenceMask (fun n=>¬p n) a)^2=
      sequenceSize a^2 := by
  rw [sequenceSize_sq,sequenceSize_sq,sequenceSize_sq,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h:p n <;> simp [sequenceMask,h]

theorem sequenceMask_cauchy {M N : ℕ} (p : Fin M→Prop) (r : Fin N→Prop)
    (a : Fin M→ℂ) (b : Fin N→ℂ) :
    sequenceSize (sequenceMask p a)*sequenceSize (sequenceMask r b)+
      sequenceSize (sequenceMask (fun m=>¬p m) a)*sequenceSize (sequenceMask (fun n=>¬r n) b) ≤
      sequenceSize a*sequenceSize b := by
  have h:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Bool)
    (fun z=>if z then sequenceSize (sequenceMask p a) else sequenceSize (sequenceMask (fun m=>¬p m) a))
    (fun z=>if z then sequenceSize (sequenceMask r b) else sequenceSize (sequenceMask (fun n=>¬r n) b))
  simp at h
  rw [sequenceMask_size_partition,sequenceMask_size_partition,←mul_pow] at h
  exact (sq_le_sq₀ (add_nonneg (mul_nonneg (sequenceSize_nonneg _) (sequenceSize_nonneg _))
    (mul_nonneg (sequenceSize_nonneg _) (sequenceSize_nonneg _))) (mul_nonneg (sequenceSize_nonneg a) (sequenceSize_nonneg b))).mp h

theorem sieveBilinearConstant_nonneg (Q M N : ℕ) : 0 ≤ sieveBilinearConstant Q M N := by
  unfold sieveBilinearConstant
  positivity

theorem bilinear_primitive_mean_le (Q M N : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ) :
    primitiveCharacterMean Q (fun _ χ=>‖sequenceCharacterSum a χ*sequenceCharacterSum b χ‖) ≤
      sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  have h:=bilinear_multiplicative_large_sieve Q M N a b
  have hH : 0 ≤ (harmonic (Q^2):ℝ) := by
    by_cases hh:Q=0
    · simp [hh]
    · exact_mod_cast (harmonic_pos (pow_ne_zero 2 hh)).le
  have hM : 0 ≤ (M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ) := by positivity
  have hN : 0 ≤ (N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ) := by positivity
  have he : (sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b)^2=
      (((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ m:Fin M,‖a m‖^2))*
      (((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖b n‖^2)) := by
    rw [mul_pow,mul_pow,sequenceSize_sq,sequenceSize_sq]
    unfold sieveBilinearConstant
    rw [mul_pow,Real.sq_sqrt hM,Real.sq_sqrt hN]
    ring
  rw [←he] at h
  exact (sq_le_sq₀ (primitiveCharacterMean_nonneg _ (fun _ _=>norm_nonneg _))
    (mul_nonneg (mul_nonneg (sieveBilinearConstant_nonneg _ _ _) (sequenceSize_nonneg _))
      (sequenceSize_nonneg _))).mp h

theorem primitiveCharacterMean_mono {Q : ℕ}
    {f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ}
    (h : ∀ q χ,f q χ ≤ g q χ) : primitiveCharacterMean Q f ≤ primitiveCharacterMean Q g := by
  apply Finset.sum_le_sum
  intro q _
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=>h q χ)) (by positivity)

theorem primitiveCharacterMean_add {Q : ℕ}
    (f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    primitiveCharacterMean Q (fun q χ=>f q χ+g q χ)=
      primitiveCharacterMean Q f+primitiveCharacterMean Q g := by
  simp only [primitiveCharacterMean,Finset.sum_add_distrib,mul_add]

theorem triangularCharacterSum_split {q M N : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) (H : ℕ) :
    triangularCharacterSum a b t χ=
      triangularCharacterSum (sequenceMask (fun m=>t m ≤ H) a) (sequenceMask (fun n=>n.val<H) b) t χ+
      sequenceCharacterSum (sequenceMask (fun m=>¬t m ≤ H) a) χ*
        sequenceCharacterSum (sequenceMask (fun n=>n.val<H) b) χ+
      triangularCharacterSum (sequenceMask (fun m=>¬t m ≤ H) a) (sequenceMask (fun n=>¬n.val<H) b) t χ := by
  unfold triangularCharacterSum sequenceCharacterSum
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hm:t m ≤ H <;> by_cases hn:n.val<H <;> by_cases ht:n.val<t m <;>
    simp [sequenceMask,hm,hn,ht] <;> (try omega) ; ring

theorem triangularCharacterSum_single {q M N L : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) (hb : ∀ n,b n≠0→n.val=L) :
    triangularCharacterSum a b t χ=
      sequenceCharacterSum (sequenceMask (fun m=>L<t m) a) χ*sequenceCharacterSum b χ := by
  unfold triangularCharacterSum sequenceCharacterSum
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn:b n=0
  · simp [hn,sequenceMask]
  · have he:=hb n hn
    by_cases ht:L<t m <;> simp [sequenceMask,he,ht] ; ring

theorem triangular_primitive_mean_dyadic (Q M N k L : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (hb : ∀ n,b n≠0→L ≤ n.val ∧ n.val<L+2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum a b t χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  induction k generalizing L a b with
  | zero =>
    have he (q:Fin Q) (χ : DirichletCharacter ℂ (q.val+1)) :=
      triangularCharacterSum_single a b t χ (fun n hn=>by have h:=hb n hn; simpa using (by omega : n.val=L))
    simp only [he,Nat.cast_zero,zero_add,one_mul]
    exact (bilinear_primitive_mean_le Q M N _ _).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sequenceMask_size_le _ _) (sieveBilinearConstant_nonneg _ _ _))
        (sequenceSize_nonneg _))
  | succ k ih =>
    let H:=L+2^k
    let p : Fin M→Prop := fun m=>t m ≤ H
    let r : Fin N→Prop := fun n=>n.val<H
    let a₀:=sequenceMask p a
    let a₁:=sequenceMask (fun m=>¬p m) a
    let b₀:=sequenceMask r b
    let b₁:=sequenceMask (fun n=>¬r n) b
    have hb₀ : ∀ n,b₀ n≠0→L ≤ n.val ∧ n.val<L+2^k := by
      intro n hn
      have hn' : b n≠0 ∧ n.val<H := by
        dsimp [b₀,sequenceMask,r] at hn
        split at hn <;> simp_all
      exact ⟨(hb n hn'.1).1,hn'.2⟩
    have hb₁ : ∀ n,b₁ n≠0→H ≤ n.val ∧ n.val<H+2^k := by
      intro n hn
      have hn' : b n≠0 ∧ ¬n.val<H := by
        dsimp [b₁,sequenceMask,r] at hn
        split at hn <;> simp_all
      have h:=hb n hn'.1
      simp only [pow_succ] at h
      dsimp [H]
      omega
    have hsplit := primitiveCharacterMean_mono (Q:=Q)
      (f:=fun _ χ=>‖triangularCharacterSum a b t χ‖)
      (g:=fun _ χ=>‖triangularCharacterSum a₀ b₀ t χ‖+
        ‖sequenceCharacterSum a₁ χ*sequenceCharacterSum b₀ χ‖+
        ‖triangularCharacterSum a₁ b₁ t χ‖) (fun _ χ=>by
          rw [triangularCharacterSum_split a b t χ H]
          exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
    rw [primitiveCharacterMean_add,primitiveCharacterMean_add] at hsplit
    have h0:=ih L a₀ b₀ hb₀
    have h1:=ih H a₁ b₁ hb₁
    have hR:=bilinear_primitive_mean_le Q M N a₁ b₀
    have hpair:=sequenceMask_cauchy p r a b
    have hcross : sequenceSize a₁*sequenceSize b₀ ≤ sequenceSize a*sequenceSize b :=
      mul_le_mul (sequenceMask_size_le _ _) (sequenceMask_size_le _ _)
        (sequenceSize_nonneg _) (sequenceSize_nonneg _)
    have hC:=sieveBilinearConstant_nonneg Q M N
    have hk : 0 ≤ (k:ℝ)+1 := by positivity
    have hp:=mul_le_mul_of_nonneg_left hpair (mul_nonneg hk hC)
    have hc:=mul_le_mul_of_nonneg_left hcross hC
    change sequenceSize a₀*sequenceSize b₀+sequenceSize a₁*sequenceSize b₁ ≤ _ at hpair
    change ((k:ℝ)+1)*sieveBilinearConstant Q M N*
      (sequenceSize a₀*sequenceSize b₀+sequenceSize a₁*sequenceSize b₁) ≤ _ at hp
    push_cast
    nlinarith only [hsplit,h0,h1,hR,hp,hc]

theorem triangular_primitive_mean_le (Q M N k : ℕ) (hk : N ≤ 2^k)
    (a : Fin M→ℂ) (b : Fin N→ℂ) (t : Fin M→ℕ) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum a b t χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  apply triangular_primitive_mean_dyadic Q M N k 0 a b t
  intro n _
  exact ⟨Nat.zero_le _,by simpa only [zero_add] using n.isLt.trans_le hk⟩

theorem sum_divisorsAntidiagonal_hyperbola (X : ℕ) (F : ℕ→ℕ→ℂ) :
    (∑ n∈Finset.Icc 1 X,∑ p∈n.divisorsAntidiagonal,F p.1 p.2)=
      ∑ d∈Finset.Icc 1 X,∑ m∈Finset.Icc 1 (X/d),F d m := by
  rw [Finset.sum_sigma',Finset.sum_sigma']
  apply Finset.sum_bij (fun x _ => (⟨x.2.1,x.2.2⟩ : (d:ℕ)×ℕ))
  · rintro ⟨n,d,m⟩ hx
    obtain ⟨hn,hdm⟩:=Finset.mem_sigma.mp hx
    obtain ⟨hn1,hnX⟩:=Finset.mem_Icc.mp hn
    obtain ⟨hdm,hn0⟩:=Nat.mem_divisorsAntidiagonal.mp hdm
    dsimp only at hn1 hnX hdm hn0
    have hd : 0 < d := by
      by_contra hh
      have he : d=0 := by omega
      simp only [he,zero_mul] at hdm
      omega
    have hm : 0 < m := by
      by_contra hh
      have he : m=0 := by omega
      simp only [he,mul_zero] at hdm
      omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd,by nlinarith⟩,
      Finset.mem_Icc.mpr ⟨hm,(Nat.le_div_iff_mul_le hd).mpr (by nlinarith)⟩⟩
  · rintro ⟨n,d,m⟩ hx ⟨n',d',m'⟩ hy he
    have hv:(d,m)=(d',m'):=by simpa using congrArg (fun x:(d:ℕ)×ℕ=>(x.1,x.2)) he
    have hd:d=d':=congrArg Prod.fst hv
    have hm:m=m':=congrArg Prod.snd hv
    have hn: d*m = n := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    have hn': d'*m' = n' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hy).2).1
    subst d'; subst m'
    have hnn:n=n':=hn.symm.trans hn'
    cases hnn; rfl
  · rintro ⟨d,m⟩ hy
    obtain ⟨hd,hm⟩:=Finset.mem_sigma.mp hy
    obtain ⟨hd1,hdX⟩:=Finset.mem_Icc.mp hd
    obtain ⟨hm1,hmX⟩:=Finset.mem_Icc.mp hm
    refine ⟨⟨d*m,(d,m)⟩,?_,rfl⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith,
      by have h: m*d ≤ X:=(Nat.le_div_iff_mul_le hd1).mp hmX; nlinarith⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,by positivity⟩⟩
  · intro x _; rfl

theorem arithmeticCharacterSum_convolution {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      ∑ d∈Finset.Icc 1 X,(f d:ℂ)*χ (d:ZMod q)*
        (∑ m∈Finset.Icc 1 (X/d),(g m:ℂ)*χ (m:ZMod q)) := by
  unfold arithmeticCharacterSum
  calc
    _ = ∑ n∈Finset.Icc 1 X,∑ p∈n.divisorsAntidiagonal,
        (f p.1:ℂ)*χ (p.1:ZMod q)*((g p.2:ℂ)*χ (p.2:ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have he: p.1*p.2=n := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [←he,Nat.cast_mul,map_mul]
      ring
    _ = _ := by
      rw [sum_divisorsAntidiagonal_hyperbola X (fun d m=>(f d:ℂ)*χ (d:ZMod q)*((g m:ℂ)*χ (m:ZMod q)))]
      simp only [Finset.mul_sum,mul_assoc]

theorem vaughan_character_identity {q : ℕ} (X U V : ℕ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ=
      arithmeticCharacterSum X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) χ+
      arithmeticCharacterSum X (arithmeticCutoff V ArithmeticFunction.moebius*ArithmeticFunction.log) χ-
      arithmeticCharacterSum X (arithmeticCutoff V ArithmeticFunction.moebius*
        arithmeticCutoff U ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta) χ+
      arithmeticCharacterSum X ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ := by
  have h:=congrArg (fun f=>arithmeticCharacterSum X f χ) (vaughan_identity U V)
  simpa only [arithmeticCharacterSum_add,arithmeticCharacterSum_sub,vaughanSecondCoefficient,mul_assoc] using h

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_VaughanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem sequenceSize_le_of_norm_le {N : ℕ} (a : Fin N→ℂ) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ n,‖a n‖ ≤ A) : sequenceSize a ≤ Real.sqrt N*A := by
  have hh : sequenceSize a^2 ≤ (N:ℝ)*A^2 := by
    rw [sequenceSize_sq]
    calc
      _ ≤ ∑ _n:Fin N,A^2 := Finset.sum_le_sum (fun n _=>pow_le_pow_left₀ (norm_nonneg _) (ha n) 2)
      _ = _ := by simp
  have hs : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  apply (sq_le_sq₀ (sequenceSize_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  simpa only [mul_pow,hs] using hh

theorem vaughanFirstSequence_norm_le (V M : ℕ) (m : Fin M) :
    ‖vaughanFirstSequence V M m‖ ≤ 1 := by
  unfold vaughanFirstSequence
  split_ifs
  · rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=m.val))
  · simp

theorem vaughanFirstSequence_size_le (V M : ℕ) :
    sequenceSize (vaughanFirstSequence V M) ≤ Real.sqrt M := by
  simpa only [mul_one] using sequenceSize_le_of_norm_le (vaughanFirstSequence V M)
    zero_le_one (vaughanFirstSequence_norm_le V M)

theorem vaughanSecondSequence_norm_le (U N : ℕ) (n : Fin N) :
    ‖vaughanSecondSequence U N n‖ ≤ Real.log N := by
  rw [vaughanSecondSequence,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (vaughanSecondCoefficient_nonneg _ _)]
  exact (vaughanSecondCoefficient_le_log _ _).trans (log_nat_monotone n.isLt.le)

theorem vaughanSecondSequence_size_le (U N : ℕ) :
    sequenceSize (vaughanSecondSequence U N) ≤ Real.sqrt N*Real.log N := by
  apply sequenceSize_le_of_norm_le _ _ (vaughanSecondSequence_norm_le U N)
  simpa using log_nat_monotone (Nat.zero_le N)

theorem vaughan_typeII_block_mean (Q X U V M N k : ℕ) (hk : N ≤ 2^k)
    (p : Fin M→Prop) (r : Fin N→Prop) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum
      (sequenceMask p (vaughanFirstSequence V M))
      (sequenceMask r (vaughanSecondSequence U N)) (fun m=>X/m.val+1) χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*Real.sqrt M*(Real.sqrt N*Real.log N) := by
  have h:=triangular_primitive_mean_le Q M N k hk
    (sequenceMask p (vaughanFirstSequence V M))
    (sequenceMask r (vaughanSecondSequence U N)) (fun m=>X/m.val+1)
  apply h.trans
  have hC : 0 ≤ ((k:ℝ)+1)*sieveBilinearConstant Q M N :=
    mul_nonneg (by positivity) (sieveBilinearConstant_nonneg _ _ _)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      ((sequenceMask_size_le _ _).trans (vaughanFirstSequence_size_le _ _)) hC
  · exact (sequenceMask_size_le _ _).trans (vaughanSecondSequence_size_le _ _)
  · exact sequenceSize_nonneg _
  · exact mul_nonneg hC (Real.sqrt_nonneg _)

theorem sum_Icc_one_eq_range_of_zero {E : Type*} [AddCommMonoid E]
    (F : ℕ→E) (hF : F 0=0) (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,F n)=∑ n∈Finset.range (N+1),F n := by
  apply Finset.sum_subset
  · intro n hn
    have h:=Finset.mem_Icc.mp hn
    exact Finset.mem_range.mpr (by omega)
  · intro n hn hn'
    have h:=Finset.mem_range.mp hn
    have hh:¬(1 ≤ n ∧ n ≤ N):=by simpa using hn'
    have he:n=0:=by omega
    simpa [he] using hF

theorem sum_range_filter_prefix {E : Type*} [AddCommMonoid E]
    (F : ℕ→E) {N K : ℕ} (hK : K ≤ N) :
    (∑ n∈Finset.range (N+1),if n<K+1 then F n else 0)=
      ∑ n∈Finset.range (K+1),F n := by
  rw [←Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

theorem arithmeticCharacterSum_convolution_triangular {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      triangularCharacterSum (fun m:Fin (X+1)=>(f m.val:ℂ))
        (fun n:Fin (X+1)=>(g n.val:ℂ)) (fun m=>X/m.val+1) χ := by
  rw [arithmeticCharacterSum_convolution]
  rw [sum_Icc_one_eq_range_of_zero (fun d=>(f d:ℂ)*χ (d:ZMod q)*
    (∑ m∈Finset.Icc 1 (X/d),(g m:ℂ)*χ (m:ZMod q))) (by simp)]
  have he : triangularCharacterSum (fun m:Fin (X+1)=>(f m.val:ℂ))
      (fun n:Fin (X+1)=>(g n.val:ℂ)) (fun m=>X/m.val+1) χ=
      ∑ m∈Finset.range (X+1),∑ n∈Finset.range (X+1),
        if n<X/m+1 then (f m:ℂ)*(g n:ℂ)*χ (m:ZMod q)*χ (n:ZMod q) else 0 := by
    unfold triangularCharacterSum
    trans ∑ m:Fin (X+1),∑ n∈Finset.range (X+1),
      if n<X/m.val+1 then (f m.val:ℂ)*(g n:ℂ)*χ (m.val:ZMod q)*χ (n:ZMod q) else 0
    · apply Finset.sum_congr rfl
      intro m _
      exact Fin.sum_univ_eq_sum_range (fun n:ℕ=>
        if n<X/m.val+1 then (f m.val:ℂ)*(g n:ℂ)*χ (m.val:ZMod q)*χ (n:ZMod q) else 0) _
    · exact Fin.sum_univ_eq_sum_range (fun m:ℕ=>∑ n∈Finset.range (X+1),
        if n<X/m+1 then (f m:ℂ)*(g n:ℂ)*χ (m:ZMod q)*χ (n:ZMod q) else 0) _
  rw [he]
  apply Finset.sum_congr rfl
  intro m _
  rw [sum_Icc_one_eq_range_of_zero (fun n=>(g n:ℂ)*χ (n:ZMod q)) (by simp)]
  rw [←sum_range_filter_prefix (fun n=>(g n:ℂ)*χ (n:ZMod q)) (Nat.div_le_self X m)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem vaughan_typeII_exact {q : ℕ} (X U V : ℕ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      triangularCharacterSum (vaughanFirstSequence V (X+1))
        (vaughanSecondSequence U (X+1)) (fun m=>X/m.val+1) χ := by
  rw [arithmeticCharacterSum_convolution_triangular]
  congr 1
  funext m
  change (((ArithmeticFunction.moebius m.val:ℝ)-
    (if m.val ≤ V then (ArithmeticFunction.moebius m.val:ℝ) else 0):ℝ):ℂ)=_
  by_cases hm:m.val ≤ V
  · simp [vaughanFirstSequence,hm,not_lt_of_ge hm]
  · simp [vaughanFirstSequence,hm,lt_of_not_ge hm]

theorem arithmeticCharacterSum_le_l1 {q : ℕ} (X : ℕ)
    (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    ‖arithmeticCharacterSum X f χ‖ ≤ arithmeticL1 X f := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)

theorem arithmeticL1_cutoff_le (X D : ℕ) (f : ArithmeticFunction ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hf : ∀ n∈Finset.Icc 1 D,|f n| ≤ A) :
    arithmeticL1 X (arithmeticCutoff D f) ≤ (D:ℝ)*A := by
  have he : arithmeticL1 X (arithmeticCutoff D f)=
      ∑ n∈(Finset.Icc 1 X).filter (fun n=>n ≤ D),|f n| := by
    simp only [arithmeticL1,arithmeticCutoff_apply,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp
  rw [he]
  have hs : (Finset.Icc 1 X).filter (fun n=>n ≤ D) ⊆ Finset.Icc 1 D := by
    intro n hn
    obtain ⟨hn,hnD⟩:=Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,hnD⟩
  calc
    _ ≤ ∑ _n∈(Finset.Icc 1 X).filter (fun n=>n ≤ D),A :=
      Finset.sum_le_sum (fun n hn=>hf n (hs hn))
    _ = (((Finset.Icc 1 X).filter (fun n=>n ≤ D)).card:ℝ)*A := by simp
    _ ≤ (D:ℝ)*A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast (by simpa using Finset.card_le_card hs)

theorem arithmeticCharacterSum_log_convolution_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X : ℕ) (f : ArithmeticFunction ℝ) :
    ‖arithmeticCharacterSum X (f*ArithmeticFunction.log) χ‖ ≤
      arithmeticL1 X f*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
  rw [arithmeticCharacterSum_convolution]
  have he (d : ℕ) : (∑ n∈Finset.Icc 1 (X/d),
      (ArithmeticFunction.log n:ℂ)*χ (n:ZMod q))=
      ∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q) := by
    exact sum_Icc_one_eq_range_of_zero _ (by simp) _
  simp only [he]
  have h:=primitive_typeI_log_bound hq hχ X X (fun d=>(f d:ℂ))
  simpa only [arithmeticL1,Complex.norm_real,Real.norm_eq_abs] using h

theorem arithmeticCharacterSum_zeta_convolution_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X : ℕ) (f : ArithmeticFunction ℝ) :
    ‖arithmeticCharacterSum X (f*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)) χ‖ ≤
      arithmeticL1 X f*(Real.sqrt q*(harmonic q:ℝ)) := by
  rw [arithmeticCharacterSum_convolution]
  have he (d : ℕ) : (∑ n∈Finset.Icc 1 (X/d),
      ((ArithmeticFunction.zeta:ArithmeticFunction ℝ) n:ℂ)*χ (n:ZMod q))=
      ∑ n∈Finset.range (X/d+1),χ (n:ZMod q) := by
    trans ∑ n∈Finset.Icc 1 (X/d),χ (n:ZMod q)
    · apply Finset.sum_congr rfl
      intro n hn
      have hn0:n≠0:=by have h:=(Finset.mem_Icc.mp hn).1; omega
      simp [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hn0]
    · exact sum_Icc_one_eq_range_of_zero _ (by simpa using χ.map_zero' (by omega)) _
  simp only [he]
  have h:=primitive_typeI_bound hq hχ X X (fun d=>(f d:ℂ))
  simpa only [arithmeticL1,Complex.norm_real,Real.norm_eq_abs] using h

theorem arithmeticCutoff_mul_support (U V n : ℕ) (f g : ArithmeticFunction ℝ)
    (hn : U*V < n) : (arithmeticCutoff U f*arithmeticCutoff V g) n=0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have he:p.1*p.2=n:=(Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases h1:p.1 ≤ U
  · by_cases h2:p.2 ≤ V
    · have h:=Nat.mul_le_mul h1 h2
      omega
    · simp [arithmeticCutoff_apply,h2]
  · simp [arithmeticCutoff_apply,h1]

theorem vaughanShortCoefficient_abs_le (U V n : ℕ) :
    |(arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt) n| ≤ Real.log n := by
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ p∈n.divisorsAntidiagonal,
        |arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ) p.1*
          arithmeticCutoff U ArithmeticFunction.vonMangoldt p.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p∈n.divisorsAntidiagonal,ArithmeticFunction.vonMangoldt p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul]
      have hm: |arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ) p.1| ≤ 1 := by
        rw [arithmeticCutoff_apply]
        split_ifs
        · rw [ArithmeticFunction.intCoe_apply]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=p.1))
        · simp
      have hl: |arithmeticCutoff U ArithmeticFunction.vonMangoldt p.2| ≤
          ArithmeticFunction.vonMangoldt p.2 := by
        rw [arithmeticCutoff_apply]
        split_ifs
        · exact (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg).le
        · simp
      exact (mul_le_mul hm hl (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ d=>ArithmeticFunction.vonMangoldt d),
        ArithmeticFunction.vonMangoldt_sum]

theorem arithmeticCutoff_eq_of_support (D : ℕ) (f : ArithmeticFunction ℝ)
    (hf : ∀ n,D<n→f n=0) : arithmeticCutoff D f=f := by
  ext n
  by_cases hn:n ≤ D
  · simp [arithmeticCutoff_apply,hn]
  · simp [arithmeticCutoff_apply,hn,hf n (lt_of_not_ge hn)]

theorem vonMangoldt_cutoff_l1 (X U : ℕ) :
    arithmeticL1 X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) ≤ (U:ℝ)*Real.log U := by
  apply arithmeticL1_cutoff_le
  · simpa using log_nat_monotone (Nat.zero_le U)
  · intro n hn
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log.trans (log_nat_monotone (Finset.mem_Icc.mp hn).2)

theorem moebius_cutoff_l1 (X V : ℕ) :
    arithmeticL1 X (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)) ≤ V := by
  have h:=arithmeticL1_cutoff_le X V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)
    zero_le_one (fun n _=>by
      rw [ArithmeticFunction.intCoe_apply]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n)))
  simpa only [mul_one] using h

theorem vaughanShortCoefficient_l1 (X U V : ℕ) :
    arithmeticL1 X (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt) ≤ (V*U:ℕ)*Real.log (V*U:ℕ) := by
  let f:=arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
    arithmeticCutoff U ArithmeticFunction.vonMangoldt
  have he : arithmeticCutoff (V*U) f=f :=
    arithmeticCutoff_eq_of_support _ _ (fun n hn=>arithmeticCutoff_mul_support V U n _ _ hn)
  change arithmeticL1 X f ≤ _
  rw [←he]
  apply arithmeticL1_cutoff_le
  · simpa using log_nat_monotone (Nat.zero_le (V*U))
  · intro n hn
    exact (vaughanShortCoefficient_abs_le U V n).trans (log_nat_monotone (Finset.mem_Icc.mp hn).2)

theorem primitive_vaughan_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X U V : ℕ) :
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ ≤
      (U:ℝ)*Real.log U+
      (V:ℝ)*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ)))+
      ((V*U:ℕ)*Real.log (V*U:ℕ))*(Real.sqrt q*(harmonic q:ℝ))+
      ‖triangularCharacterSum (vaughanFirstSequence V (X+1))
        (vaughanSecondSequence U (X+1)) (fun m=>X/m.val+1) χ‖ := by
  have hH : 0 ≤ (harmonic q:ℝ) := by exact_mod_cast (harmonic_pos (by omega : q≠0)).le
  have hK : 0 ≤ Real.sqrt q*(harmonic q:ℝ) := mul_nonneg (Real.sqrt_nonneg _) hH
  have hL : 0 ≤ (2:ℝ)*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X+1 by omega)))) hK
  have h0 := (arithmeticCharacterSum_le_l1 X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) χ).trans
    (vonMangoldt_cutoff_l1 X U)
  have h1 := (arithmeticCharacterSum_log_convolution_bound hq hχ X
    (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ))).trans
      (mul_le_mul_of_nonneg_right (moebius_cutoff_l1 X V) hL)
  have h2 := (arithmeticCharacterSum_zeta_convolution_bound hq hχ X
    (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt)).trans
      (mul_le_mul_of_nonneg_right (vaughanShortCoefficient_l1 X U V) hK)
  rw [vaughan_character_identity,vaughan_typeII_exact]
  apply le_trans (norm_add_le _ _)
  apply add_le_add _ le_rfl
  apply le_trans (norm_sub_le _ _)
  apply add_le_add _ h2
  exact (norm_add_le _ _).trans (add_le_add h0 h1)

theorem hyperbolaBlock_eq_triangle {q : ℕ} (X D E : ℕ) (hD : 0 < D)
    (a b : ℕ→ℂ) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X D E a b χ=
      triangularCharacterSum (sequenceMask (fun m:Fin E=>D ≤ m.val) (fun m=>a m.val))
        (fun n:Fin (X/D+1)=>b n.val) (fun m=>X/m.val+1) χ := by
  classical
  have hf : (Finset.range E).filter (fun m=>D ≤ m)=Finset.Ico D E := by
    ext m
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  have he : triangularCharacterSum
      (sequenceMask (fun m:Fin E=>D ≤ m.val) (fun m=>a m.val))
      (fun n:Fin (X/D+1)=>b n.val) (fun m=>X/m.val+1) χ=
      ∑ m∈Finset.range E,∑ n∈Finset.range (X/D+1),
        if n < X/m+1 then (if D ≤ m then a m else 0)*b n*χ (m:ZMod q)*χ (n:ZMod q) else 0 := by
    unfold triangularCharacterSum sequenceMask
    trans ∑ m:Fin E,∑ n∈Finset.range (X/D+1),
      if n < X/m.val+1 then (if D ≤ m.val then a m.val else 0)*b n*χ (m.val:ZMod q)*χ (n:ZMod q) else 0
    · apply Finset.sum_congr rfl
      intro m _
      by_cases hm:D ≤ m.val <;>
        simpa only [hm,ite_true,ite_false] using
          (Fin.sum_univ_eq_sum_range (fun n:ℕ=>
            if n < X/m.val+1 then (if D ≤ m.val then a m.val else 0)*b n*χ (m.val:ZMod q)*χ (n:ZMod q) else 0) (X/D+1))
    · exact Fin.sum_univ_eq_sum_range (fun m:ℕ=>∑ n∈Finset.range (X/D+1),
        if n < X/m+1 then (if D ≤ m then a m else 0)*b n*χ (m:ZMod q)*χ (n:ZMod q) else 0) _
  rw [he]
  unfold hyperbolaBlock
  rw [←hf,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm:D ≤ m
  · simp only [hm,ite_true]
    rw [←sum_range_filter_prefix (fun n=>b n*χ (n:ZMod q)) (Nat.div_le_div_left hm hD)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  · simp [hm]

theorem sum_Ico_one_pow_two {A : Type*} [AddCommMonoid A] (F : ℕ→A) (k : ℕ) :
    (∑ m∈Finset.Ico 1 (2^k),F m)=
      ∑ j∈Finset.range k,∑ m∈Finset.Ico (2^j) (2^(j+1)),F m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,←ih,Finset.sum_Ico_consecutive]
    · exact one_le_pow₀ (by omega)
    · exact pow_le_pow_right₀ (by omega) (Nat.le_succ k)

theorem vaughan_hyperbolaBlock_mean (Q X U V D E k : ℕ) (hD : 0 < D)
    (hk : X/D+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q E (X/D+1)*Real.sqrt E*
        (Real.sqrt ((X/D+1:ℕ):ℝ)*Real.log ((X/D+1:ℕ):ℝ)) := by
  have h:=vaughan_typeII_block_mean Q X U V E (X/D+1) k hk
    (fun m=>D ≤ m.val) (fun _=>True)
  have hr : sequenceMask (fun _ : Fin (X/D+1)=>True)
      (vaughanSecondSequence U (X/D+1))=vaughanSecondSequence U (X/D+1) := by
    funext n
    simp [sequenceMask]
  rw [hr] at h
  have he : (fun (_q : Fin Q) (χ : DirichletCharacter ℂ (_q.val+1))=>‖hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖)=
      (fun (_q : Fin Q) (χ : DirichletCharacter ℂ (_q.val+1))=>‖triangularCharacterSum
        (sequenceMask (fun m:Fin E=>D ≤ m.val) (vaughanFirstSequence V E))
        (vaughanSecondSequence U (X/D+1)) (fun m=>X/m.val+1) χ‖) := by
    funext q χ
    rw [hyperbolaBlock_eq_triangle X D E hD]
    rfl
  rw [he]
  exact h

theorem hyperbolaBlock_extend {q : ℕ} (X E : ℕ) (hE : X+1 ≤ E)
    (a b : ℕ→ℂ) (hb : b 0=0) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X 1 (X+1) a b χ=hyperbolaBlock X 1 E a b χ := by
  unfold hyperbolaBlock
  apply Finset.sum_subset
  · intro m hm
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hm).1,
      ((Finset.mem_Ico.mp hm).2).trans_le hE⟩
  · intro m hm hm'
    have hx : X < m := by
      have h:=Finset.mem_Ico.mp hm
      have hh : ¬(1 ≤ m ∧ m < X+1) := by simpa only [Finset.mem_Ico] using hm'
      omega
    simp [Nat.div_eq_of_lt hx,hb]

theorem arithmeticCharacterSum_convolution_dyadic {q : ℕ} (X k : ℕ)
    (hk : X+1 ≤ 2^k) (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      ∑ j∈Finset.range k,hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>(f m:ℂ)) (fun n=>(g n:ℂ)) χ := by
  rw [arithmeticCharacterSum_convolution]
  have he : (∑ m∈Finset.Icc 1 X,(f m:ℂ)*χ (m:ZMod q)*
      ∑ n∈Finset.Icc 1 (X/m),(g n:ℂ)*χ (n:ZMod q))=
      hyperbolaBlock X 1 (X+1) (fun m=>(f m:ℂ)) (fun n=>(g n:ℂ)) χ := by
    unfold hyperbolaBlock
    rw [show Finset.Ico 1 (X+1)=Finset.Icc 1 X by ext m; simp]
    apply Finset.sum_congr rfl
    intro m _
    rw [sum_Icc_one_eq_range_of_zero (fun n=>(g n:ℂ)*χ (n:ZMod q)) (by simp)]
  rw [he,hyperbolaBlock_extend X (2^k) hk _ _ (by simp)]
  exact sum_Ico_one_pow_two _ k

theorem vaughan_typeII_dyadic {q : ℕ} (X U V k : ℕ) (hk : X+1 ≤ 2^k)
    (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      ∑ j∈Finset.range k,hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
        (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ := by
  rw [arithmeticCharacterSum_convolution_dyadic X k hk]
  have hf : (fun m=>(((ArithmeticFunction.moebius-
        arithmeticCutoff V ArithmeticFunction.moebius):ArithmeticFunction ℝ) m:ℂ))=
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0) := by
    funext m
    change (((ArithmeticFunction.moebius m:ℝ)-
      (if m ≤ V then (ArithmeticFunction.moebius m:ℝ) else 0):ℝ):ℂ)=_
    by_cases hm:m ≤ V
    · simp [hm,not_lt_of_ge hm]
    · simp [hm,lt_of_not_ge hm]
  rw [hf]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DyadicMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem primitiveCharacterMean_sum {ι : Type*} (Q : ℕ) (s : Finset ι)
    (f : ι→(q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    primitiveCharacterMean Q (fun q χ=>∑ i∈s,f i q χ)=
      ∑ i∈s,primitiveCharacterMean Q (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [primitiveCharacterMean]
  | cons a s ha ih =>
    simp only [Finset.sum_cons,primitiveCharacterMean_add,ih]

theorem vaughan_hyperbolaBlock_zero_left {q : ℕ} (X U V D E : ℕ)
    (hE : E ≤ V+1) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have h:=Finset.mem_Ico.mp hm
  have hn:¬V < m:=by omega
  simp [hn]

theorem vaughan_hyperbolaBlock_zero_right {q : ℕ} (X U V D E : ℕ)
    (hD : 0 < D) (hU : X/D ≤ U) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have hmD: D ≤ m:=(Finset.mem_Ico.mp hm).1
  have hnU:X/m ≤ U:=(Nat.div_le_div_left hmD hD).trans hU
  have hz:(∑ n∈Finset.range (X/m+1),(vaughanSecondCoefficient U n:ℂ)*χ (n:ZMod q))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnle:n ≤ U:=by have h:=Finset.mem_range.mp hn; omega
    simp [vaughanSecondCoefficient_zero_of_le hnle]
  rw [hz,mul_zero]

theorem vaughan_typeII_active_dyadic {q : ℕ} (X U V k : ℕ) (hk : X+1 ≤ 2^k)
    (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      ∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
        hyperbolaBlock X (2^j) (2^(j+1))
          (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
          (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ := by
  rw [vaughan_typeII_dyadic X U V k hk]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hj'
  have hneg:¬(V+1 < 2^(j+1) ∧ U < X/2^j) := by
    simpa only [Finset.mem_filter,hj,true_and] using hj'
  by_cases hl:V+1 < 2^(j+1)
  · exact vaughan_hyperbolaBlock_zero_right X U V (2^j) (2^(j+1))
      (pow_pos (by omega) _) (by omega) χ
  · exact vaughan_hyperbolaBlock_zero_left X U V (2^j) (2^(j+1)) (by omega) χ

theorem vaughan_typeII_active_mean (Q X U V k : ℕ) (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ‖) ≤
      ∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
        ((k:ℝ)+1)*sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
          Real.sqrt ((2^(j+1):ℕ):ℝ)*
            (Real.sqrt ((X/2^j+1:ℕ):ℝ)*Real.log ((X/2^j+1:ℕ):ℝ)) := by
  have h:=primitiveCharacterMean_mono (Q:=Q)
    (f:=fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ‖)
    (g:=fun _ χ=>∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
      ‖hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
        (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖) (fun _ χ=>by
          rw [vaughan_typeII_active_dyadic X U V k hk]
          exact norm_sum_le _ _)
  rw [primitiveCharacterMean_sum] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  exact vaughan_hyperbolaBlock_mean Q X U V (2^j) (2^(j+1)) k
    (pow_pos (by omega) _) ((Nat.add_le_add_right (Nat.div_le_self _ _) 1).trans hk)

theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg ha hb)]
  nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sqrt_nonneg a,Real.sqrt_nonneg b]

theorem sqrt_bilinear_expansion {m n z : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hz : 0 ≤ z) :
    (Real.sqrt (m+z)*Real.sqrt (n+z))*Real.sqrt m*Real.sqrt n ≤
      m*n+Real.sqrt z*(m*Real.sqrt n+n*Real.sqrt m)+z*Real.sqrt m*Real.sqrt n := by
  have h:=mul_le_mul (sqrt_add_le_sqrt_add_sqrt hm hz) (sqrt_add_le_sqrt_add_sqrt hn hz)
    (Real.sqrt_nonneg _) (by positivity : 0 ≤ Real.sqrt m+Real.sqrt z)
  calc
    _ ≤ ((Real.sqrt m+Real.sqrt z)*(Real.sqrt n+Real.sqrt z))*Real.sqrt m*Real.sqrt n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = (Real.sqrt m)^2*(Real.sqrt n)^2+
        Real.sqrt z*((Real.sqrt m)^2*Real.sqrt n+(Real.sqrt n)^2*Real.sqrt m)+
        (Real.sqrt z)^2*Real.sqrt m*Real.sqrt n := by ring
    _ = _ := by rw [Real.sq_sqrt hm,Real.sq_sqrt hn,Real.sq_sqrt hz]

theorem sqrt_product_le_twice {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hab : a*b ≤ 4*x) :
    Real.sqrt a*Real.sqrt b ≤ 2*Real.sqrt x := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sq_sqrt hx]
  norm_num
  exact hab

theorem sqrt_bilinear_hyperbolic_bound {m n x t z : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hx : 0 ≤ x) (ht : 0 < t) (hz : 0 ≤ z)
    (hmn : m*n ≤ 4*x) (hmt : m*t ≤ 4*x) (hnt : n*t ≤ 4*x) :
    (Real.sqrt (m+z)*Real.sqrt (n+z))*Real.sqrt m*Real.sqrt n ≤
      4*x+Real.sqrt z*(8*x/Real.sqrt t)+z*(2*Real.sqrt x) := by
  have hmn' := sqrt_product_le_twice hm hn hx hmn
  have hmt' := sqrt_product_le_twice hm ht.le hx hmt
  have hnt' := sqrt_product_le_twice hn ht.le hx hnt
  have hcross : (m*Real.sqrt n+n*Real.sqrt m)*Real.sqrt t ≤ 8*x := by
    calc
      _ = (Real.sqrt m*Real.sqrt n)*
          (Real.sqrt m*Real.sqrt t+Real.sqrt n*Real.sqrt t) := by
        calc
          _ = ((Real.sqrt m)^2*Real.sqrt n+(Real.sqrt n)^2*Real.sqrt m)*Real.sqrt t := by
            rw [Real.sq_sqrt hm,Real.sq_sqrt hn]
          _ = _ := by ring
      _ ≤ (2*Real.sqrt x)*(4*Real.sqrt x) :=
        mul_le_mul hmn' (by linarith) (by positivity) (by positivity)
      _ = _ := by nlinarith [Real.sq_sqrt hx]
  have hc : m*Real.sqrt n+n*Real.sqrt m ≤ 8*x/Real.sqrt t :=
    (le_div_iff₀ (Real.sqrt_pos.mpr ht)).mpr hcross
  apply (sqrt_bilinear_expansion hm hn hz).trans
  simpa only [mul_assoc] using
    (add_le_add (add_le_add hmn (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)))
      (mul_le_mul_of_nonneg_left hmn' hz))

theorem vaughan_active_dimensions (X T j : ℕ)
    (hleft : T+1 < 2^(j+1)) (hright : T < X/2^j) :
    (2^(j+1))*(X/2^j+1) ≤ 4*X ∧
    (2^(j+1))*(T+1) ≤ 4*X ∧ (X/2^j+1)*(T+1) ≤ 4*X := by
  have hD : 0 < 2^j := pow_pos (by omega) _
  have hprod : (T+1)*2^j ≤ X := (Nat.le_div_iff_mul_le hD).mp (by omega)
  have hX : 2^j ≤ X := by nlinarith
  have hdiv := Nat.div_mul_le_self X (2^j)
  have hpow : 2^(j+1)=2*2^j := by rw [pow_succ]; omega
  have harea : (2^(j+1))*(X/2^j+1) ≤ 4*X := by rw [hpow]; nlinarith
  refine ⟨harea,?_,?_⟩
  · rw [hpow]
    nlinarith
  · exact (Nat.mul_le_mul_left (X/2^j+1) hleft.le).trans (by simpa only [Nat.mul_comm] using harea)

theorem harmonic_real_nonneg (n : ℕ) : 0 ≤ (harmonic n:ℝ) := by
  by_cases hn:n=0
  · simp [hn]
  · exact_mod_cast (harmonic_pos hn).le

theorem vaughanBilinearBound_nonneg (Q X T : ℕ) : 0 ≤ vaughanBilinearBound Q X T := by
  have hh:=harmonic_real_nonneg (Q^2)
  unfold vaughanBilinearBound
  positivity

theorem vaughan_active_bilinear_bound (Q X T j : ℕ)
    (hleft : T+1 < 2^(j+1)) (hright : T < X/2^j) :
    sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
      Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ) ≤
        vaughanBilinearBound Q X T := by
  obtain ⟨hmn,hmt,hnt⟩:=vaughan_active_dimensions X T j hleft hright
  apply sqrt_bilinear_hyperbolic_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by positivity) (mul_nonneg (sq_nonneg _) (harmonic_real_nonneg _))
  · exact_mod_cast hmn
  · exact_mod_cast hmt
  · exact_mod_cast hnt

theorem vaughan_typeII_equal_cutoff_mean (Q X T k : ℕ) (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
        vaughanSecondCoefficient T) χ‖) ≤
      (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  apply (vaughan_typeII_active_mean Q X T T k hk).trans
  let K:=((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ)
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (by positivity) (vaughanBilinearBound_nonneg _ _ _))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X+1 by omega)))
  apply le_trans (b:=∑ _j∈(Finset.range k).filter (fun j=>T+1 < 2^(j+1) ∧ T < X/2^j),K)
  · apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hl,hr⟩ := (Finset.mem_filter.mp hj).2
    have hb:=vaughan_active_bilinear_bound Q X T j hl hr
    have hlog : Real.log ((X/2^j+1:ℕ):ℝ) ≤ Real.log (X+1:ℕ) :=
      log_nat_monotone (Nat.add_le_add_right (Nat.div_le_self _ _) 1)
    have hlog0 : 0 ≤ Real.log ((X/2^j+1:ℕ):ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X/2^j+1 by omega))
    calc
      _ = ((k:ℝ)+1)*(sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
          Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ))*
            Real.log ((X/2^j+1:ℕ):ℝ) := by ring
      _ ≤ K := mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) hlog hlog0
        (mul_nonneg (by positivity) (vaughanBilinearBound_nonneg _ _ _))
  · rw [Finset.sum_const,nsmul_eq_mul]
    have hc : (((Finset.range k).filter (fun j=>T+1 < 2^(j+1) ∧ T < X/2^j)).card:ℝ) ≤ k := by
      exact_mod_cast (Finset.card_filter_le (Finset.range k) _).trans_eq (Finset.card_range k)
    exact (mul_le_mul_of_nonneg_right hc hK).trans_eq (by dsimp [K]; ring)

theorem primitiveCharacterMean_mono_primitive {Q : ℕ}
    {f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ}
    (h : ∀ q χ,χ.IsPrimitive→f q χ ≤ g q χ) :
    primitiveCharacterMean Q f ≤ primitiveCharacterMean Q g := by
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro χ hχ
  exact h q χ (Finset.mem_filter.mp hχ).2

theorem primitiveCharacterMean_constant_le (Q : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    primitiveCharacterMean Q (fun _ _=>A) ≤ (Q:ℝ)^2*A := by
  classical
  calc
    _ ≤ ∑ _q:Fin Q,(Q:ℝ)*A := by
      apply Finset.sum_le_sum
      intro q _
      let d:=q.val+1
      have hd:0 < d:=by dsimp [d]; omega
      let : NeZero d:=⟨by omega⟩
      have hphi:0 < (d.totient:ℝ):=by exact_mod_cast Nat.totient_pos.mpr hd
      have hcard:Fintype.card (DirichletCharacter ℂ d)=d.totient := by
        simpa only [Nat.card_eq_fintype_card] using
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
      have hnum:(((Finset.univ : Finset (DirichletCharacter ℂ d)).filter
          DirichletCharacter.IsPrimitive).card:ℝ) ≤ d.totient := by
        exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ d)) _).trans_eq
          (by rw [Finset.card_univ,hcard])
      change (d:ℝ)/d.totient*(∑ _χ∈(Finset.univ : Finset (DirichletCharacter ℂ d)).filter
        DirichletCharacter.IsPrimitive,A) ≤ _
      rw [Finset.sum_const,nsmul_eq_mul]
      calc
        _ ≤ (d:ℝ)/d.totient*((d.totient:ℝ)*A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnum hA) (by positivity)
        _ = (d:ℝ)*A := by field_simp
        _ ≤ (Q:ℝ)*A := mul_le_mul_of_nonneg_right (by exact_mod_cast (show d ≤ Q by dsimp [d]; omega)) hA
    _ = _ := by simp; ring

theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n:ℝ) := by
  simpa using log_nat_monotone (Nat.zero_le n)

theorem vaughanShortBound_nonneg (Q X T : ℕ) : 0 ≤ vaughanShortBound Q X T := by
  have hQ:=log_nat_nonneg Q
  have hT:=log_nat_nonneg T
  have hX:=log_nat_nonneg (X+1)
  have hTT:=log_nat_nonneg (T*T)
  unfold vaughanShortBound
  positivity

theorem polya_constant_le {q Q : ℕ} (hqQ : q ≤ Q) :
    Real.sqrt q*(harmonic q:ℝ) ≤ Real.sqrt Q*(1+Real.log Q) := by
  apply mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hqQ))
    ((harmonic_le_one_add_log q).trans (add_le_add le_rfl (log_nat_monotone hqQ)))
    (harmonic_real_nonneg _) (Real.sqrt_nonneg _)

theorem primitive_vaughan_bound_uniform {q Q : ℕ} (hq : 1 < q) (hqQ : q ≤ Q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X T : ℕ) :
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ ≤
      vaughanShortBound Q X T+
      ‖arithmeticCharacterSum X
        ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
          vaughanSecondCoefficient T) χ‖ := by
  rw [vaughan_typeII_exact]
  apply (primitive_vaughan_bound hq hχ X T T).trans
  apply add_le_add_left
  unfold vaughanShortBound
  apply add_le_add
  · apply add_le_add_right
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (polya_constant_le hqQ)
      (mul_nonneg (by norm_num) (log_nat_nonneg _))) (Nat.cast_nonneg _)
  · exact mul_le_mul_of_nonneg_left (polya_constant_le hqQ)
      (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _))

theorem finite_vaughan_primitive_mean (Q X T k : ℕ) (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun q χ=>if 1 < q.val+1 then
      ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0) ≤
      (Q:ℝ)^2*vaughanShortBound Q X T+
        (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  have h:=primitiveCharacterMean_mono_primitive (Q:=Q)
    (f:=fun q χ=>if 1 < q.val+1 then ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0)
    (g:=fun _ χ=>vaughanShortBound Q X T+
      ‖arithmeticCharacterSum X
        ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
          vaughanSecondCoefficient T) χ‖) (fun q χ hχ=>by
      by_cases hq:1 < q.val+1
      · rw [ite_eq_left hq]
        exact primitive_vaughan_bound_uniform hq (by omega) hχ X T
      · rw [ite_eq_right hq]
        exact add_nonneg (vaughanShortBound_nonneg _ _ _) (norm_nonneg _))
  rw [primitiveCharacterMean_add] at h
  exact h.trans (add_le_add (primitiveCharacterMean_constant_le _ (vaughanShortBound_nonneg _ _ _))
    (vaughan_typeII_equal_cutoff_mean Q X T k hk))

theorem primitive_ne_one {q : ℕ} (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  let : NeZero q:=⟨by omega⟩
  intro he
  have hc:=hχ
  rw [DirichletCharacter.isPrimitive_def,he,DirichletCharacter.conductor_one] at hc
  omega

theorem primeCharacterPrefix_nat {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) :
    primeCharacterPrefix (X:ℝ) χ=arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ := by
  have he : Finset.Ioc 0 X=Finset.Icc 1 X := by ext n; simp; omega
  simp only [primeCharacterPrefix,arithmeticCharacterSum,Nat.floor_natCast,he,mul_comm]

theorem primitiveErrorMass_eq_vonMangoldt_sum (X : ℕ) {q : ℕ} (hq : 1 < q) :
    primitiveErrorMass (X:ℝ) q=
      ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter DirichletCharacter.IsPrimitive,
        ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ := by
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [primeCharacterError,ite_eq_right (primitive_ne_one hq (Finset.mem_filter.mp hχ).2),
    sub_zero,primeCharacterPrefix_nat]

theorem sum_Icc_one_eq_sum_fin {A : Type*} [AddCommMonoid A] (F : ℕ→A) (Q : ℕ) :
    (∑ d∈Finset.Icc 1 Q,F d)=∑ q:Fin Q,F (q.val+1) := by
  classical
  apply Finset.sum_bij (fun d hd=>(⟨d-1,by have h:=Finset.mem_Icc.mp hd; omega⟩:Fin Q))
  · intro d hd
    exact Finset.mem_univ _
  · intro a ha b hb he
    have hh:=congrArg Fin.val he
    have h1:=Finset.mem_Icc.mp ha
    have h2:=Finset.mem_Icc.mp hb
    dsimp at hh
    omega
  · intro q _
    refine ⟨q.val+1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    apply Fin.ext
    simp
  · intro d hd
    have h:=Finset.mem_Icc.mp hd
    simp only [show d-1+1=d by omega]

theorem conductor_interval_error_le_vaughan (Q X T k R : ℕ) (hR : 1 ≤ R)
    (hk : X+1 ≤ 2^k) :
    (R:ℝ)*(∑ d∈Finset.Ioc R Q,primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      (Q:ℝ)^2*vaughanShortBound Q X T+
        (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  have hf : (Finset.Icc 1 Q).filter (fun d=>R < d)=Finset.Ioc R Q := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have he : (∑ d∈Finset.Ioc R Q,primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))=
      ∑ q:Fin Q,if R < q.val+1 then primitiveErrorMass (X:ℝ) (q.val+1)/((q.val+1).totient:ℝ) else 0 := by
    rw [←hf,Finset.sum_filter,sum_Icc_one_eq_sum_fin]
  rw [he,Finset.mul_sum]
  apply le_trans (b:=primitiveCharacterMean Q (fun q χ=>if 1 < q.val+1 then
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0))
  · apply Finset.sum_le_sum
    intro q _
    by_cases hq:R < q.val+1
    · have hq1:1 < q.val+1:=by omega
      simp only [ite_eq_left hq,ite_eq_left hq1]
      rw [←primitiveErrorMass_eq_vonMangoldt_sum X hq1]
      have hrq:(R:ℝ) ≤ q.val+1:=by exact_mod_cast hq.le
      calc
        _ ≤ ((q.val+1:ℕ):ℝ)*(primitiveErrorMass (X:ℝ) (q.val+1)/((q.val+1).totient:ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hq.le)
            (div_nonneg (primitiveErrorMass_nonneg _ _) (Nat.cast_nonneg _))
        _ = _ := by ring
    · simp only [ite_eq_right hq,mul_zero]
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro χ _
      split_ifs <;> positivity
  · exact finite_vaughan_primitive_mean Q X T k hk

theorem vaughanShortBound_mono {Q P : ℕ} (hQP : Q ≤ P) (X T : ℕ) :
    vaughanShortBound Q X T ≤ vaughanShortBound P X T := by
  have hK : Real.sqrt Q*(1+Real.log Q) ≤ Real.sqrt P*(1+Real.log P) :=
    mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hQP))
      (add_le_add le_rfl (log_nat_monotone hQP))
      (by have h:=log_nat_nonneg Q; positivity) (Real.sqrt_nonneg _)
  unfold vaughanShortBound
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK
      (mul_nonneg (by norm_num) (log_nat_nonneg _))) (Nat.cast_nonneg _)))
    (mul_le_mul_of_nonneg_left hK (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _)))

theorem conductorHarmonicBound_pos (Q : ℕ) : 0 < conductorHarmonicBound Q := by
  unfold conductorHarmonicBound
  have h:=log_nat_nonneg (Q^2)
  linarith

theorem conductor_harmonic_le {q Q : ℕ} (hqQ : q ≤ Q) :
    (harmonic (q^2):ℝ) ≤ conductorHarmonicBound Q := by
  exact (harmonic_le_one_add_log _).trans
    (add_le_add le_rfl (log_nat_monotone (Nat.pow_le_pow_left hqQ 2)))

theorem highConductorBlockBound_nonneg (Q X T R k : ℕ) :
    0 ≤ highConductorBlockBound Q X T R k := by
  have hs:=vaughanShortBound_nonneg Q X T
  have hh:=(conductorHarmonicBound_pos Q).le
  have hl:=log_nat_nonneg (X+1)
  unfold highConductorBlockBound
  positivity

theorem vaughanBilinearBound_doubling (Q X T D : ℕ) (hD : 1 ≤ D) (hQ : 2*D ≤ Q) :
    vaughanBilinearBound (2*D) X T ≤ (D:ℝ)*
      (4*(X:ℝ)/(D:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X) := by
  let H:=conductorHarmonicBound Q
  have hH : 0 ≤ H := (conductorHarmonicBound_pos Q).le
  have hDr : 0 < (D:ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hQr : 2*(D:ℝ) ≤ Q := by exact_mod_cast hQ
  have hz : ((2*D:ℕ):ℝ)^2*(harmonic ((2*D)^2):ℝ) ≤ ((2*D:ℕ):ℝ)^2*H :=
    mul_le_mul_of_nonneg_left (conductor_harmonic_le hQ) (sq_nonneg _)
  have hs : Real.sqrt (((2*D:ℕ):ℝ)^2*(harmonic ((2*D)^2):ℝ)) ≤
      ((2*D:ℕ):ℝ)*Real.sqrt H := by
    apply (Real.sqrt_le_sqrt hz).trans_eq
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  have htail : (((2*D:ℕ):ℝ)^2*H)*(2*Real.sqrt X) ≤
      (D:ℝ)*(4*(Q:ℝ)*H*Real.sqrt X) := by
    calc
      _ = (2*(D:ℝ))*(4*(D:ℝ)*H*Real.sqrt X) := by push_cast; ring
      _ ≤ (Q:ℝ)*(4*(D:ℝ)*H*Real.sqrt X) :=
        mul_le_mul_of_nonneg_right hQr (by positivity)
      _ = _ := by ring
  unfold vaughanBilinearBound
  calc
    _ ≤ 4*(X:ℝ)+(((2*D:ℕ):ℝ)*Real.sqrt H)*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+
        ((((2*D:ℕ):ℝ)^2*H)*(2*Real.sqrt X)) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hs (by positivity)))
        (mul_le_mul_of_nonneg_right hz (by positivity))
    _ ≤ 4*(X:ℝ)+(((2*D:ℕ):ℝ)*Real.sqrt H)*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+
        (D:ℝ)*(4*(Q:ℝ)*H*Real.sqrt X) := add_le_add le_rfl htail
    _ = _ := by
      change _=(D:ℝ)*(4*(X:ℝ)/(D:ℝ)+16*Real.sqrt H*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*H*Real.sqrt X)
      push_cast
      field_simp
      ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ConductorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem conductor_doubling_error_le (Q X T k D : ℕ) (hD : 1 ≤ D)
    (hQ : 2*D ≤ Q) (hk : X+1 ≤ 2^k) :
    (∑ d∈Finset.Ioc D (2*D),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      highConductorBlockBound Q X T D k := by
  have hDr : 0 < (D:ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hdq : ((2*D:ℕ):ℝ) ≤ Q := by exact_mod_cast hQ
  have hsq : (((2*D:ℕ):ℝ)^2) ≤ ((2*D:ℕ):ℝ)*(Q:ℝ) := by
    nlinarith [show (0:ℝ) ≤ ((2*D:ℕ):ℝ) from Nat.cast_nonneg _]
  have hshort : (((2*D:ℕ):ℝ)^2)*vaughanShortBound (2*D) X T ≤
      (D:ℝ)*(2*(Q:ℝ)*vaughanShortBound Q X T) := by
    calc
      _ ≤ (((2*D:ℕ):ℝ)^2)*vaughanShortBound Q X T :=
        mul_le_mul_of_nonneg_left (vaughanShortBound_mono hQ X T) (sq_nonneg _)
      _ ≤ (((2*D:ℕ):ℝ)*(Q:ℝ))*vaughanShortBound Q X T :=
        mul_le_mul_of_nonneg_right hsq (vaughanShortBound_nonneg _ _ _)
      _ = _ := by push_cast; ring
  have hbilin:=vaughanBilinearBound_doubling Q X T D hD hQ
  have hC : 0 ≤ (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) := by
    have h:=log_nat_nonneg (X+1)
    positivity
  have h:=(conductor_interval_error_le_vaughan (2*D) X T k D hD hk).trans
    (add_le_add hshort (by
      convert mul_le_mul_of_nonneg_left hbilin hC using 1
      ring))
  apply (mul_le_mul_iff_right₀ hDr).mp
  convert h using 1
  unfold highConductorBlockBound
  ring

theorem highConductorBlockBound_antitone_radius (Q X T k : ℕ) {R D : ℕ}
    (hR : 1 ≤ R) (hRD : R ≤ D) :
    highConductorBlockBound Q X T D k ≤ highConductorBlockBound Q X T R k := by
  have hdiv : 4*(X:ℝ)/(D:ℝ) ≤ 4*(X:ℝ)/(R:ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < R by omega))
      (by exact_mod_cast hRD)
  have hC : 0 ≤ (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) := by
    have h:=log_nat_nonneg (X+1)
    positivity
  unfold highConductorBlockBound
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hdiv le_rfl) le_rfl) hC)

theorem sum_Ioc_dyadic {A : Type*} [AddCommMonoid A] (F : ℕ→A) (r n : ℕ) :
    (∑ d∈Finset.Ioc (2^r) (2^(r+n)),F d)=
      ∑ j∈Finset.range n,∑ d∈Finset.Ioc (2^(r+j)) (2^(r+j+1)),F d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,←ih]
    exact (Finset.sum_Ioc_consecutive F (show 2^r ≤ 2^(r+n) from
      pow_le_pow_right₀ (by omega) (by omega))
      (show 2^(r+n) ≤ 2^(r+n+1) from pow_le_pow_right₀ (by omega) (by omega))).symm

theorem high_conductor_error_le (X T k r n : ℕ) (hk : X+1 ≤ 2^k) :
    (∑ d∈Finset.Ioc (2^r) (2^(r+n)),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k := by
  rw [sum_Ioc_dyadic]
  calc
    _ ≤ ∑ _j∈Finset.range n,highConductorBlockBound (2^(r+n)) X T (2^r) k := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn:=Finset.mem_range.mp hj
      have hD : 1 ≤ 2^(r+j) := one_le_pow₀ (by omega)
      have hpow : 2^(r+j+1)=2*2^(r+j) := by rw [pow_succ]; omega
      rw [hpow]
      apply (conductor_doubling_error_le (2^(r+n)) X T k (2^(r+j)) hD ?_ hk).trans
      · exact highConductorBlockBound_antitone_radius _ _ _ _ (one_le_pow₀ (by omega))
          (pow_le_pow_right₀ (by omega) (by omega))
      · rw [←hpow]
        exact pow_le_pow_right₀ (by omega) (by omega)
    _ = _ := by simp

theorem endpoint_errors_finite_vaughan_reduction (X T k r n : ℕ) (hk : X+1 ≤ 2^k) :
    (∑ q∈Finset.Icc 1 (2^(r+n)),(endpointError (X:ℝ) q:ℝ)) ≤
      ((∑ d∈Finset.Icc 1 (2^r),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))+
        (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k)*(harmonic (2^(r+n)):ℝ)^2+
      ((2^(r+n):ℕ):ℝ)*(Nat.log 2 X:ℝ)*Real.log (2^(r+n):ℕ) := by
  have hR : 2^r ≤ 2^(r+n) := pow_le_pow_right₀ (by omega) (by omega)
  have hRpos : 1 ≤ 2^r := one_le_pow₀ (by omega)
  have he : Finset.Icc 1 (2^(r+n))=Finset.Icc 1 (2^r)∪Finset.Ioc (2^r) (2^(r+n)) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_union,Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 (2^r)) (Finset.Ioc (2^r) (2^(r+n))) := by
    apply Finset.disjoint_left.mpr
    intro d h1 h2
    have h1':=Finset.mem_Icc.mp h1
    have h2':=Finset.mem_Ioc.mp h2
    omega
  have h:=endpointErrors_le_primitive_weighted_sum (X:ℝ) (2^(r+n))
  simp only [Nat.floor_natCast] at h
  apply h.trans
  rw [he,Finset.sum_union hd]
  exact add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (high_conductor_error_le X T k r n hk)) (sq_nonneg _)) le_rfl

theorem endpoint_errors_finite_vaughan_reduction_of_le (X T k r n Q : ℕ)
    (hk : X+1 ≤ 2^k) (hQ : Q ≤ 2^(r+n)) :
    (∑ q∈Finset.Icc 1 Q,(endpointError (X:ℝ) q:ℝ)) ≤
      ((∑ d∈Finset.Icc 1 (2^r),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))+
        (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k)*(harmonic (2^(r+n)):ℝ)^2+
      ((2^(r+n):ℕ):ℝ)*(Nat.log 2 X:ℝ)*Real.log (2^(r+n):ℕ) := by
  apply le_trans ?_ (endpoint_errors_finite_vaughan_reduction X T k r n hk)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    have h:=Finset.mem_Icc.mp hq
    exact Finset.mem_Icc.mpr ⟨h.1,h.2.trans hQ⟩
  · intro q _ _
    exact NNReal.coe_nonneg _

theorem endpointError_le_floor (x : ℝ) (q : ℕ) :
    (endpointError x q:ℝ) ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+
      |x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
  have hb : 0 ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
    positivity
  change (endpointError x q:ℝ) ≤
    ((⟨(endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ),hb⟩:NNReal):ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro c hc
  split_ifs with hcop
  · apply NNReal.coe_le_coe.mp
    change |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient| ≤ _
    calc
      _ ≤ |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-(⌊x⌋₊:ℝ)/q.totient|+
          |(⌊x⌋₊:ℝ)/q.totient-x/q.totient| := abs_sub_le _ _ _
      _ ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
        apply add_le_add (endpointClassError_le ⌊x⌋₊ (Finset.mem_range.mp hc) hcop)
        rw [←sub_div,abs_div,abs_of_nonneg (show (0:ℝ) ≤ q.totient from Nat.cast_nonneg _),abs_sub_comm]
  · exact bot_le

theorem sum_endpointError_le_floor (x : ℝ) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (∑ q∈Finset.Icc 1 Q,(endpointError (⌊x⌋₊:ℝ) q:ℝ))+
        |x-(⌊x⌋₊:ℝ)| *(harmonic Q:ℝ)^2 := by
  apply (Finset.sum_le_sum (fun q _ => endpointError_le_floor x q)).trans
  rw [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  calc
    _ = |x-(⌊x⌋₊:ℝ)| *(∑ q∈Finset.Icc 1 Q,(1:ℝ)/(q.totient:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_totient_reciprocal_le Q) (abs_nonneg _)

theorem sum_endpointError_le_floor_add_harmonic {x : ℝ} (hx : 0 ≤ x) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (∑ q∈Finset.Icc 1 Q,(endpointError (⌊x⌋₊:ℝ) q:ℝ))+(harmonic Q:ℝ)^2 := by
  apply (sum_endpointError_le_floor x Q).trans
  apply add_le_add le_rfl
  have h1 : 0 ≤ x-(⌊x⌋₊:ℝ) := sub_nonneg.mpr (Nat.floor_le hx)
  have h2 : |x-(⌊x⌋₊:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg h1]
    have h:=Nat.lt_floor_add_one x
    linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h2 (sq_nonneg (harmonic Q:ℝ))

open Filter Topology

theorem primitiveErrorMass_div_le {x M : ℝ} (hM : 0 ≤ M) {d : ℕ} (hd : 0 < d)
    (h : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → ‖primeCharacterError x χ‖ ≤ M) :
    primitiveErrorMass x d/(d.totient:ℝ) ≤ M := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hphi : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hcard : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  apply (div_le_iff₀ hphi).mpr
  calc
    _ ≤ ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
        DirichletCharacter.IsPrimitive, M := by
      exact Finset.sum_le_sum (fun χ hχ => h χ (Finset.mem_filter.mp hχ).2)
    _ ≤ ∑ _χ : DirichletCharacter ℂ d, M :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hM)
    _ = _ := by simp [hcard, mul_comm]

theorem small_conductor_mass_le {x M : ℝ} (hM : 0 ≤ M) (R : ℕ)
    (h : ∀ d : ℕ, 0 < d → d ≤ R → ∀ χ : DirichletCharacter ℂ d,
      χ.IsPrimitive → ‖primeCharacterError x χ‖ ≤ M) :
    (∑ d ∈ Finset.Icc 1 R, primitiveErrorMass x d/(d.totient:ℝ)) ≤ (R:ℝ)*M := by
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 R, M := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd0, hdR⟩ := Finset.mem_Icc.mp hd
      exact primitiveErrorMass_div_le hM (by omega) (h d (by omega) hdR)
    _ = _ := by simp

theorem dyadicExponent_mono : Monotone dyadicExponent := by
  intro x y hxy
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono hxy)) 1

theorem dyadicUpper_bounds {x : ℝ} (hx : 1 ≤ x) :
    x < ((2^(dyadicExponent x):ℕ):ℝ) ∧ ((2^(dyadicExponent x):ℕ):ℝ) ≤ 2*x := by
  have hf : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hlo := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x⌋₊
  have hup := Nat.pow_log_le_self 2 (by omega : ⌊x⌋₊ ≠ 0)
  constructor
  · apply (Nat.lt_floor_add_one x).trans_le
    exact_mod_cast hlo
  · unfold dyadicExponent
    rw [pow_succ]
    push_cast
    have hh : ((2^(Nat.log 2 ⌊x⌋₊):ℕ):ℝ) ≤ x :=
      (by exact_mod_cast hup : ((2^(Nat.log 2 ⌊x⌋₊):ℕ):ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le (by linarith))
    push_cast at hh
    nlinarith

theorem log_add_one_le_twice {X : ℕ} (hX : 2 ≤ X) :
    Real.log (X+1:ℕ) ≤ 2*Real.log (X:ℝ) := by
  have hx : (2:ℝ) ≤ X := by exact_mod_cast hX
  calc
    _ ≤ Real.log ((X:ℝ)^2) := Real.log_le_log (by positivity) (by push_cast; nlinarith)
    _ = _ := by rw [Real.log_pow]; ring

theorem vaughanBinaryExponent_bounds {X : ℕ} (hX : 2 ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    X+1 ≤ 2^(dyadicExponent (X+1:ℕ)) ∧
      (dyadicExponent (X+1:ℕ):ℝ) ≤ 6*Real.log (X:ℝ) := by
  constructor
  · exact_mod_cast (dyadicUpper_bounds (show (1:ℝ) ≤ (X+1:ℕ) by exact_mod_cast (by omega : 1 ≤ X+1))).1.le
  · rw [dyadicExponent, Nat.floor_natCast]
    push_cast
    have hn := Real.natLog_le_logb (X+1) 2
    have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hd : Real.log (X+1:ℕ)/Real.log 2 ≤ 4*Real.log (X:ℝ) := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
      have h := log_add_one_le_twice hX
      nlinarith
    norm_num only [Real.logb, Nat.cast_ofNat] at hn
    linarith

theorem vaughanShortBound_power_le {Q X T : ℕ} (hX : 2 ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) (hQX : Q ≤ X)
    (hQ : (Q:ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ))
    (hT : (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ)) :
    vaughanShortBound Q X T ≤ 32*(X:ℝ)^(3/8:ℝ)*(Real.log (X:ℝ))^2 := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL0 : 0 ≤ L := by dsimp [L,x]; linarith
  have htX : (T:ℝ) ≤ x := hT.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (1/16:ℝ) ≤ 1))
  have htL : Real.log (T:ℝ) ≤ L := log_nat_monotone (by change (T:ℝ) ≤ (X:ℝ) at htX; exact_mod_cast htX)
  have hqL : Real.log (Q:ℝ) ≤ L := log_nat_monotone hQX
  have hxxL : Real.log (X+1:ℕ) ≤ 2*L := log_add_one_le_twice hX
  have hqroot : Real.sqrt Q ≤ 2*x^(1/4:ℝ) := by
    apply (Real.sqrt_le_sqrt hQ).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow, ←Real.rpow_mul hx.le]
    norm_num
  have hK : Real.sqrt Q*(1+Real.log Q) ≤ 4*x^(1/4:ℝ)*L := by
    calc
      _ ≤ (2*x^(1/4:ℝ))*(2*L) := mul_le_mul hqroot (by dsimp [L,x] at *; linarith)
        (by have hh:=log_nat_nonneg Q; linarith) (by positivity)
      _ = _ := by ring
  have ht2 : ((T*T:ℕ):ℝ) ≤ x^(1/8:ℝ) := by
    calc
      _ = (T:ℝ)^2 := by push_cast; ring
      _ ≤ (x^(1/16:ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg T) hT 2
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]; norm_num
  have httL : Real.log (T*T:ℕ) ≤ 2*L := by
    calc
      _ = 2*Real.log (T:ℝ) := by rw [Nat.cast_mul, ←pow_two,Real.log_pow]; norm_num
      _ ≤ _ := by linarith
  have he1 : x^(1/16:ℝ) ≤ x^(3/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have he2 : x^(5/16:ℝ) ≤ x^(3/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h1 : (T:ℝ)*Real.log T ≤ x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ x^(3/8:ℝ)*L := mul_le_mul (hT.trans he1) htL (log_nat_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [L,x] at *; nlinarith) (by positivity)
  have h2 : (T:ℝ)*(2*Real.log (X+1:ℕ)*(Real.sqrt Q*(1+Real.log Q))) ≤
      16*x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ x^(1/16:ℝ)*(2*(2*L)*(4*x^(1/4:ℝ)*L)) := by gcongr
      _ = 16*x^(5/16:ℝ)*L^2 := by
        rw [show (5/16:ℝ)=1/16+1/4 by norm_num,Real.rpow_add hx]; ring
      _ ≤ _ := by gcongr
  have h3 : (((T*T:ℕ):ℝ)*Real.log (T*T:ℕ))*(Real.sqrt Q*(1+Real.log Q)) ≤
      8*x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ (x^(1/8:ℝ)*(2*L))*(4*x^(1/4:ℝ)*L) := by gcongr
      _ = _ := by rw [show (3/8:ℝ)=1/8+1/4 by norm_num,Real.rpow_add hx]; ring
  unfold vaughanShortBound
  dsimp only
  change _ ≤ 32*x^(3/8:ℝ)*L^2
  nlinarith [mul_nonneg (Real.rpow_nonneg hx.le (3/8:ℝ)) (sq_nonneg L)]

theorem conductorHarmonicBound_le {Q X : ℕ} (hQ : Q ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) :
    conductorHarmonicBound Q ≤ 3*Real.log (X:ℝ) := by
  unfold conductorHarmonicBound
  rw [Nat.cast_pow,Real.log_pow]
  have h := log_nat_monotone hQ
  norm_num only [Nat.cast_ofNat]
  linarith

theorem sqrt_conductorHarmonicBound_le {Q X : ℕ} (hQ : Q ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) :
    Real.sqrt (conductorHarmonicBound Q) ≤ 2*Real.log (X:ℝ) := by
  apply (Real.sqrt_le_sqrt (conductorHarmonicBound_le hQ hL)).trans
  apply (Real.sqrt_le_left (by linarith)).mpr
  nlinarith

theorem rpow_absorption {x L a b c : ℝ} (hx : 0 < x) (hL : 0 < L)
    (h : L^a ≤ x^b) : x^(1-b)*L^c ≤ x*L^(c-a) := by
  calc
    _ = (x^(1-b)*L^(c-a))*L^a := by
      rw [mul_assoc,←Real.rpow_add hL,sub_add_cancel]
    _ ≤ (x^(1-b)*L^(c-a))*x^b :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [mul_right_comm,←Real.rpow_add hx,sub_add_cancel,Real.rpow_one]

theorem rpow_absorption_of_exponents {x L a b a' b' c : ℝ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (h : L^a ≤ x^b) (ha : a' ≤ a) (hb : b ≤ b') :
    x^(1-b')*L^c ≤ x*L^(c-a') :=
  rpow_absorption (lt_of_lt_of_le zero_lt_one hx) (lt_of_lt_of_le zero_lt_one hL)
    ((Real.rpow_le_rpow_of_exponent_le hL ha).trans
      (h.trans (Real.rpow_le_rpow_of_exponent_le hx hb)))

theorem eventually_log_rpow_le_rpow (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^a ≤ x^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using h

theorem highConductorBlockBound_log_le {Q X T R k : ℕ} {A : ℝ}
    (hA : 0 < A) (hX : 2 ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) (hQX : Q ≤ X)
    (hQ : (Q:ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10))
    (hR : (Real.log (X:ℝ))^(A+10) ≤ (R:ℝ))
    (hk : (k:ℝ) ≤ 6*Real.log (X:ℝ))
    (hT : (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ))
    (hTroot : (X:ℝ)^(1/32:ℝ) ≤ Real.sqrt (T+1:ℕ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ)) :
    highConductorBlockBound Q X T R k ≤
      8000*(X:ℝ)*(Real.log (X:ℝ))^(-A-3) := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hneg : L^(-A-10) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1
      (show -A-10 ≤ 0 by linarith)
  have hQweak : (Q:ℝ) ≤ 4*x^(1/2:ℝ) := by
    apply hQ.trans
    exact (mul_le_mul_of_nonneg_left hneg (by positivity)).trans_eq (mul_one _)
  have hsnonneg := vaughanShortBound_nonneg Q X T
  have hHnonneg := (conductorHarmonicBound_pos Q).le
  have hshort := vaughanShortBound_power_le hX hL hQX hQweak hT
  have hshortAbs : x^(7/8:ℝ)*L^2 ≤ x*L^(-A-3) := by
    convert rpow_absorption_of_exponents (c:=2) hx1 hL1 hpower
      (show A+5 ≤ A+10 by linarith) (show (1/32:ℝ) ≤ 1/8 by norm_num) using 1 <;> norm_num
    all_goals ring_nf
    all_goals simp
  have hshortTotal : 2*(Q:ℝ)*vaughanShortBound Q X T ≤ 256*x*L^(-A-3) := by
    calc
      _ ≤ 2*(4*x^(1/2:ℝ))*(32*x^(3/8:ℝ)*L^2) := by gcongr
      _ = 256*(x^(7/8:ℝ)*L^2) := by
        rw [show (7/8:ℝ)=1/2+3/8 by norm_num, Real.rpow_add hx]; ring
      _ ≤ _ := by nlinarith [hshortAbs]
  have hcoef : (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) ≤ 84*L^3 := by
    calc
      _ ≤ (6*L)*(7*L)*(2*L) := by
        gcongr
        · dsimp [L,x] at *; linarith
        · exact log_add_one_le_twice hX
      _ = _ := by ring
  have hRpos : 0 < (R:ℝ) := (Real.rpow_pos_of_pos hL0 _).trans_le hR
  have hb1 : 4*x/(R:ℝ) ≤ 4*x*L^(-A-6) := by
    calc
      _ ≤ 4*x/L^(A+10) := div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos hL0 _) hR
      _ = 4*x*L^(-A-10) := by
        rw [show -A-10=-(A+10) by ring,Real.rpow_neg hL0.le,div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have habs2 : x^(31/32:ℝ)*L ≤ x*L^(-A-6) := by
    convert rpow_absorption_of_exponents (c:=1) hx1 hL1 hpower
      (show A+7 ≤ A+10 by linarith) (le_refl (1/32:ℝ)) using 1 <;> norm_num
    all_goals ring_nf
    all_goals simp
  have hb2 : 16*Real.sqrt (conductorHarmonicBound Q)*x/Real.sqrt (T+1:ℕ) ≤
      32*x*L^(-A-6) := by
    calc
      _ ≤ 16*(2*L)*x/x^(1/32:ℝ) := by
        apply div_le_div₀ (by positivity) ?_ (Real.rpow_pos_of_pos hx _) hTroot
        gcongr
        exact sqrt_conductorHarmonicBound_le hQX hL
      _ = 32*(x^(31/32:ℝ)*L) := by
        rw [show (31/32:ℝ)=1-1/32 by norm_num,Real.rpow_sub hx,Real.rpow_one]
        ring
      _ ≤ _ := by nlinarith [habs2]
  have hb3 : 4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X ≤ 48*x*L^(-A-6) := by
    calc
      _ ≤ 4*(4*x^(1/2:ℝ)*L^(-A-10))*(3*L)*x^(1/2:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        gcongr
        exact conductorHarmonicBound_le hQX hL
      _ = 48*x*L^(-A-9) := by
        rw [show -A-9=(-A-10)+1 by ring,Real.rpow_add hL0,Real.rpow_one]
        have hh : x^(1/2:ℝ)*x^(1/2:ℝ)=x := by rw [←Real.rpow_add hx]; norm_num
        calc
          _ = 48*(x^(1/2:ℝ)*x^(1/2:ℝ))*(L^(-A-10)*L) := by ring
          _ = _ := by rw [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have hbracket := add_le_add (add_le_add hb1 hb2) hb3
  have hlarge : ((k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ))*
      (4*x/(R:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*x/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X) ≤ 7056*x*L^(-A-3) := by
    calc
      _ ≤ (84*L^3)*(84*x*L^(-A-6)) := by
        apply mul_le_mul hcoef (by linarith [hbracket]) (by positivity) (by positivity)
      _ = _ := by
        rw [show -A-3=(-A-6)+3 by ring,Real.rpow_add hL0]
        norm_num
        ring
  unfold highConductorBlockBound
  change _ ≤ 8000*x*L^(-A-3)
  nlinarith [mul_pos hx (Real.rpow_pos_of_pos hL0 (-A-3))]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_LogParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

theorem exists_vaughan_log_parameters {A : ℝ} (hA : 0 < A) {X : ℕ}
    (hX : 16 ≤ X) (hL : 2 ≤ Real.log (X:ℝ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ)) :
    ∃ T k r n : ℕ,
      X+1 ≤ 2^k ∧
      2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) ≤ ((2^(r+n):ℕ):ℝ) ∧
      2^(r+n) ≤ X ∧
      ((2^(r+n):ℕ):ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) ∧
      (Real.log (X:ℝ))^(A+10) ≤ ((2^r:ℕ):ℝ) ∧
      ((2^r:ℕ):ℝ) ≤ 2*(Real.log (X:ℝ))^(A+10) ∧
      (n:ℝ) ≤ 6*Real.log (X:ℝ) ∧
      (k:ℝ) ≤ 6*Real.log (X:ℝ) ∧
      (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ) ∧
      (X:ℝ)^(1/32:ℝ) ≤ Real.sqrt (T+1:ℕ) := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  let B : ℝ := A+10
  let y : ℝ := 2*x^(1/2:ℝ)*L^(-B)
  let T : ℕ := ⌊x^(1/16:ℝ)⌋₊
  let k : ℕ := dyadicExponent (X+1:ℕ)
  let r : ℕ := dyadicExponent (L^B)
  let m : ℕ := dyadicExponent y
  have hx16 : (16:ℝ) ≤ x := by dsimp [x]; exact_mod_cast hX
  have hx1 : 1 ≤ x := by linarith
  have hx : 0 < x := by linarith
  have hL1 : 1 ≤ L := by dsimp [L,x]; linarith
  have hL0 : 0 < L := by linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hLB : 1 ≤ L^B := Real.one_le_rpow hL1 hB.le
  have hneg : L^(-B) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (neg_nonpos.mpr hB.le)
  have hLL : L^B*L^B ≤ x^(1/2:ℝ) := by
    calc
      _ ≤ x^(1/32:ℝ)*x^(1/32:ℝ) := mul_le_mul hpower hpower (by positivity) (by positivity)
      _ = x^(1/16:ℝ) := by rw [←Real.rpow_add hx]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have heB : -B = -A-10 := by dsimp [B]; ring
  have hyeq : y = 2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) := by
    simp only [y,heB,L,x]
  have hLy : L^B ≤ y := by
    have he : L^B*L^(-B)=1 := by rw [←Real.rpow_add hL0]; simp
    calc
      _ = (L^B*L^B)*L^(-B) := by rw [mul_assoc,he,mul_one]
      _ ≤ x^(1/2:ℝ)*L^(-B) := mul_le_mul_of_nonneg_right hLL (by positivity)
      _ ≤ y := by dsimp [y]; nlinarith [mul_nonneg (Real.rpow_nonneg hx.le (1/2:ℝ)) (Real.rpow_nonneg hL0.le (-B))]
  have hy1 : 1 ≤ y := hLB.trans hLy
  have hry : r ≤ m := dyadicExponent_mono hLy
  have hrbounds := dyadicUpper_bounds hLB
  have hmbounds := dyadicUpper_bounds hy1
  have hsqrt : 4*x^(1/2:ℝ) ≤ x := by
    rw [←Real.sqrt_eq_rpow]
    have hs : Real.sqrt x ≤ x/4 := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith
    linarith
  have hymX : 2*y ≤ x := by
    calc
      _ = 4*x^(1/2:ℝ)*L^(-B) := by dsimp [y]; ring
      _ ≤ 4*x^(1/2:ℝ) := (mul_le_mul_of_nonneg_left hneg (by positivity)).trans_eq (mul_one _)
      _ ≤ _ := hsqrt
  have hmX : 2^m ≤ X := by
    have hh : ((2^m:ℕ):ℝ) ≤ (X:ℝ) := hmbounds.2.trans hymX
    exact_mod_cast hh
  have hymk : y ≤ (X+1:ℕ) := by
    have hy0 : 0 ≤ y := by positivity
    have hyx : y ≤ x := by linarith
    push_cast
    change y ≤ x+1
    linarith
  have hmk : m ≤ k := dyadicExponent_mono hymk
  have hkbounds := vaughanBinaryExponent_bounds (show 2 ≤ X by omega) (show 1 ≤ Real.log (X:ℝ) by linarith)
  have hrnm : r+(m-r)=m := Nat.add_sub_of_le hry
  refine ⟨T,k,r,m-r,hkbounds.1,?_,?_,?_,?_,?_,?_,hkbounds.2,?_,?_⟩
  · rw [hrnm,←hyeq]
    exact hmbounds.1.le
  · simpa only [hrnm] using hmX
  · rw [hrnm]
    calc
      _ ≤ 2*y := hmbounds.2
      _ = _ := by rw [hyeq]; ring
  · exact hrbounds.1.le
  · exact hrbounds.2
  · exact (by exact_mod_cast (Nat.sub_le m r).trans hmk : ((m-r:ℕ):ℝ) ≤ k).trans hkbounds.2
  · exact Nat.floor_le (Real.rpow_nonneg hx.le _)
  · have ht := (Nat.lt_floor_add_one (x^(1/16:ℝ))).le
    have hh := Real.sqrt_le_sqrt ht
    change Real.sqrt (x^(1/16:ℝ)) ≤ Real.sqrt ((T:ℝ)+1) at hh
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hx.le] at hh
    norm_num at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh

theorem endpoint_errors_nat_log_bound {A M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    {X Q : ℕ} (hX : 16 ≤ X) (hL : 2 ≤ Real.log (X:ℝ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ))
    (hQ : (Q:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10))
    (hsmall : ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log (X:ℝ))^(A+11) →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError (X:ℝ) χ‖ ≤ M*(X:ℝ)*(Real.log (X:ℝ))^(-2*A-14)) :
    (∑ q∈Finset.Icc 1 Q,(endpointError (X:ℝ) q:ℝ)) ≤
      (8*M+192024)*(X:ℝ)*(Real.log (X:ℝ))^(-A) := by
  obtain ⟨T,k,r,n,hk,hcover,hPX,hP,hRlo,hRhi,hn,hkL,hT,hTroot⟩ :=
    exists_vaughan_log_parameters hA hX hL hpower
  let P : ℕ := 2^(r+n)
  let R : ℕ := 2^r
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL1 : 1 ≤ L := by dsimp [L,x]; linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hQP : Q ≤ P := by
    change Q ≤ 2^(r+n)
    exact_mod_cast hQ.trans hcover
  have hH : (harmonic P:ℝ) ≤ 2*L := harmonic_le_twice_log hPX hL1
  have hH2 : (harmonic P:ℝ)^2 ≤ 4*L^2 := by nlinarith [harmonic_real_nonneg P]
  have hsmallR : (∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ)) ≤
      (R:ℝ)*(M*x*L^(-2*A-14)) := by
    apply small_conductor_mass_le (by positivity)
    intro d hd hdR χ hχ
    apply hsmall d hd ?_ χ hχ
    calc
      (d:ℝ) ≤ R := by exact_mod_cast hdR
      _ ≤ 2*L^(A+10) := hRhi
      _ ≤ L*L^(A+10) := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = L^(A+11) := by rw [show A+11=1+(A+10) by ring,Real.rpow_add hL0 1 (A+10),Real.rpow_one]
  have hsmallTotal : (∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ)) *
      (harmonic P:ℝ)^2 ≤ 8*M*x*L^(-A) := by
    calc
      _ ≤ (2*L^(A+10)*(M*x*L^(-2*A-14)))*(4*L^2) := by
        apply mul_le_mul (hsmallR.trans (mul_le_mul_of_nonneg_right hRhi (by positivity))) hH2
          (sq_nonneg _) (by positivity)
      _ = 8*M*x*L^(-A-2) := by
        conv_rhs => rw [show -A-2=(A+10)+(-2*A-14)+2 by ring,
          Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_two]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have hhi := highConductorBlockBound_log_le hA (show 2 ≤ X by omega) hL1 hPX
    hP hRlo hkL hT hTroot hpower
  have hhighTotal : ((n:ℝ)*highConductorBlockBound P X T R k)*(harmonic P:ℝ)^2 ≤
      192000*x*L^(-A) := by
    calc
      _ ≤ ((6*L)*(8000*x*L^(-A-3)))*(4*L^2) := by
        apply mul_le_mul (mul_le_mul hn hhi (highConductorBlockBound_nonneg _ _ _ _ _) (by positivity))
          hH2 (sq_nonneg _) (by positivity)
      _ = _ := by
        conv_rhs => rw [show -A=(-A-3)+1+2 by ring,Real.rpow_add hL0,Real.rpow_add hL0,
          Real.rpow_one,Real.rpow_two]
        ring
  have hlog2 : (Nat.log 2 X:ℝ) ≤ 6*L := by
    have hmono : Nat.log 2 X ≤ dyadicExponent (X+1:ℕ) := by
      unfold dyadicExponent
      rw [Nat.floor_natCast]
      exact (Nat.log_mono_right (Nat.le_succ X)).trans (Nat.le_succ _)
    exact (by exact_mod_cast hmono : (Nat.log 2 X:ℝ) ≤ (dyadicExponent (X+1:ℕ):ℝ)).trans
      (vaughanBinaryExponent_bounds (show 2 ≤ X by omega) hL1).2
  have hlogP : Real.log (P:ℝ) ≤ L := log_nat_monotone hPX
  have hcost : (P:ℝ)*(Nat.log 2 X:ℝ)*Real.log P ≤ 24*x*L^(-A) := by
    calc
      _ ≤ (4*x^(1/2:ℝ)*L^(-A-10))*(6*L)*L := by
        gcongr
      _ = 24*x^(1/2:ℝ)*L^(-A-8) := by
        rw [show -A-8=(-A-10)+1+1 by ring,Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_one]
        ring
      _ ≤ _ := by
        have hsx : x^(1/2:ℝ) ≤ x := by
          simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hx1
            (by norm_num : (1/2:ℝ) ≤ 1))
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsx (by norm_num : (0:ℝ) ≤ 24))
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity) (by positivity)
  have hfinite := endpoint_errors_finite_vaughan_reduction_of_le X T k r n Q hk hQP
  apply hfinite.trans
  change ((∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ))+
    (n:ℝ)*highConductorBlockBound P X T R k)*(harmonic P:ℝ)^2+
      (P:ℝ)*(Nat.log 2 X:ℝ)*Real.log P ≤ (8*M+192024)*x*L^(-A)
  rw [add_mul]
  nlinarith [hsmallTotal,hhighTotal,hcost]

theorem endpoint_errors_real_log_bound {A M x : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (hx : 0 ≤ x) (hX : 16 ≤ ⌊x⌋₊) (hL : 2 ≤ Real.log (⌊x⌋₊:ℝ))
    (hpower : (Real.log (⌊x⌋₊:ℝ))^(A+10) ≤ (⌊x⌋₊:ℝ)^(1/32:ℝ))
    (hsmall : ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log (⌊x⌋₊:ℝ))^(A+11) →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError (⌊x⌋₊:ℝ) χ‖ ≤ M*(⌊x⌋₊:ℝ)*(Real.log (⌊x⌋₊:ℝ))^(-2*A-14)) :
    (∑ q∈Finset.Icc 1 ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊,(endpointError x q:ℝ)) ≤
      ((8*M+192028)*(2:ℝ)^A)*x*(Real.log x)^(-A) := by
  let X : ℕ := ⌊x⌋₊
  let Q : ℕ := ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊
  let L : ℝ := Real.log (X:ℝ)
  have hX16 : (16:ℝ) ≤ X := by
    change (16:ℝ) ≤ (⌊x⌋₊:ℝ)
    exact_mod_cast hX
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hX0 : (0:ℝ) < X := by linarith
  have hfloor : (X:ℝ) ≤ x := Nat.floor_le hx
  have hceil : x < (X:ℝ)+1 := Nat.lt_floor_add_one x
  have hL1 : 1 ≤ L := by dsimp [L,X]; linarith
  have hL0 : 0 < L := by linarith
  have hloglo : L ≤ Real.log x := Real.log_le_log hX0 hfloor
  have hlogx0 : 0 < Real.log x := hL0.trans_le hloglo
  have hloghi : Real.log x ≤ 2*L :=
    calc
      _ ≤ Real.log (X+1:ℕ) := Real.log_le_log (hX0.trans_le hfloor) (by push_cast; linarith)
      _ ≤ _ := log_add_one_le_twice (by omega)
  have hroot : x^(1/2:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
    calc
      _ ≤ Real.sqrt (4*(X:ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  have hQ : (Q:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ)*L^(-A-10) := by
    calc
      _ ≤ x^(1/2:ℝ)*(Real.log x)^(-(A+10)) := Nat.floor_le (by positivity)
      _ ≤ (2*(X:ℝ)^(1/2:ℝ))*L^(-(A+10)) := mul_le_mul hroot
        (Real.rpow_le_rpow_of_nonpos hL0 hloglo (by linarith)) (by positivity) (by positivity)
      _ = _ := by congr 1; congr 1; ring
  have hneg : L^(-A-10) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1
      (show -A-10 ≤ 0 by linarith)
  have hQX : Q ≤ X := by
    have hrootsmall : 2*(X:ℝ)^(1/2:ℝ) ≤ X := by
      rw [←Real.sqrt_eq_rpow]
      have hs : Real.sqrt (X:ℝ) ≤ (X:ℝ)/2 := by
        apply (Real.sqrt_le_left (by positivity)).mpr
        nlinarith
      linarith
    have hh₁ : 2*(X:ℝ)^(1/2:ℝ)*L^(-A-10) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hneg
        (by positivity : 0 ≤ 2*(X:ℝ)^(1/2:ℝ))
    have hh : (Q:ℝ) ≤ X := hQ.trans (hh₁.trans hrootsmall)
    exact_mod_cast hh
  have hnat := endpoint_errors_nat_log_bound hA hM hX hL hpower hQ hsmall
  have hH : (harmonic Q:ℝ) ≤ 2*L := harmonic_le_twice_log hQX hL1
  have habs : L^2 ≤ (X:ℝ)*L^(-A) := by
    convert rpow_absorption_of_exponents (c:=2) hX1 hL1 hpower
      (show A+2 ≤ A+10 by linarith) (show (1/32:ℝ) ≤ 1 by norm_num) using 1 <;> norm_num
  have htotal : (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (8*M+192028)*(X:ℝ)*L^(-A) := by
    have hh := sum_endpointError_le_floor_add_harmonic hx Q
    have hH2 : (harmonic Q:ℝ)^2 ≤ 4*L^2 := by nlinarith [harmonic_real_nonneg Q]
    nlinarith [hnat,hh,habs,hH2]
  have hlogscale : L^(-A) ≤ (2:ℝ)^A*(Real.log x)^(-A) := by
    calc
      _ ≤ (Real.log x/2)^(-A) := Real.rpow_le_rpow_of_nonpos (by linarith)
        (by linarith) (by linarith)
      _ = _ := by
        rw [Real.div_rpow (by linarith : 0 ≤ Real.log x) (by norm_num : (0:ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
        ring
  apply htotal.trans
  calc
    _ ≤ (8*M+192028)*x*((2:ℝ)^A*(Real.log x)^(-A)) := by gcongr
    _ = _ := by ring

theorem bombieriVinogradov_of_siegelWalfisz (hs : SiegelWalfisz) : BombieriVinogradov := by
  intro A hA
  obtain ⟨M,hM,x₀,hx₀,hSW⟩ := hs (2*A+14) (A+11) (by linarith) (by linarith)
  refine ⟨A+10,by linarith,(8*M+192028)*(2:ℝ)^A,by positivity,?_⟩
  have hf : Tendsto (fun x : ℝ => (⌊x⌋₊:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have he : ∀ᶠ x : ℝ in atTop,
      (∑ q∈Finset.Icc 1 ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊,(endpointError x q:ℝ)) ≤
        ((8*M+192028)*(2:ℝ)^A)*x*(Real.log x)^(-A) := by
    filter_upwards [eventually_ge_atTop (0:ℝ),
      tendsto_nat_floor_atTop.eventually (eventually_ge_atTop (16:ℕ)),
      (Real.tendsto_log_atTop.comp hf).eventually_ge_atTop 2,
      hf.eventually_ge_atTop x₀,
      hf.eventually (eventually_log_rpow_le_rpow (A+10) (by norm_num : (0:ℝ)<1/32))]
      with x hx hX hL hxsw hp
    apply endpoint_errors_real_log_bound hA hM.le hx hX hL hp
    intro d hd hdL χ hχ
    convert hSW (⌊x⌋₊:ℝ) hxsw d hd hdL χ hχ using 1
    congr 1
    congr 1
    ring
  obtain ⟨z,hz⟩ := eventually_atTop.mp he
  refine ⟨max z 2,by linarith [le_max_right z (2:ℝ)],?_⟩
  intro x hx
  exact hz x ((le_max_left z (2:ℝ)).trans hx)

open Complex Filter Topology

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RieszDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

open Complex Filter Topology

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

lemma characterMain_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖characterMain χ‖≤1 := by
  unfold characterMain
  split_ifs <;> norm_num

lemma primeCoefficients_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeCoefficients χ n‖≤Real.log n := by
  rw [primeCoefficients,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
    ArithmeticFunction.vonMangoldt_le_log

open Complex Real Set MeasureTheory Filter Topology

lemma weightedPrefix_difference {x h : ℝ} (hh : 0≤h) (a : ℕ → ℂ) :
    weightedPrefix a (x+h)-weightedPrefix a x=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n := by
  classical
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have he : Finset.Ioc 0 ⌊x+h⌋₊=Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Finset.mem_Ioc] at h₁ h₂
    omega
  unfold weightedPrefix
  rw [he,Finset.sum_union hd]
  have hs : (∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n)=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hs]
  ring

lemma weightedPrefix_tail_bound {x h L : ℝ} (hx : 0≤x) (hh : 0≤h) (hL : 0≤L)
    (a : ℕ → ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n‖ ≤ (h+1)*(h*L) := by
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have hn (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      0≤x+h-(n:ℝ) ∧ x+h-(n:ℝ)≤h := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hn
    have hlo : x<(n:ℝ) := by
      have hn' : (⌊x⌋₊:ℝ)+1≤n := by exact_mod_cast h₁
      linarith [Nat.lt_floor_add_one x]
    have hup : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith)).mp h₂
    constructor <;> linarith
  have hc : ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ) ≤ h+1 := by
    rw [Nat.card_Ioc,Nat.cast_sub hfloor]
    have hlo := Nat.lt_floor_add_one x
    have hup := Nat.floor_le (by linarith : 0≤x+h)
    linarith
  calc
    _ ≤ ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖((x+h-(n:ℝ):ℝ):ℂ)*a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, h*L := by
      apply Finset.sum_le_sum
      intro n hn'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn n hn').1]
      exact mul_le_mul (hn n hn').2 (ha n hn') (norm_nonneg _) hh
    _ = ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ)*(h*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg hh hL)

lemma prefix_unsmoothing {x h L : ℝ} (hx : 0≤x) (hh : 0<h) (hL : 0≤L)
    (a : ℕ → ℂ) (δ : ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖weightedPrefix a (x+h)-δ*((x+h:ℝ):ℂ)^2/2‖+
        ‖weightedPrefix a x-δ*(x:ℂ)^2/2‖)/h+(h+1)*L+‖δ‖*h/2 := by
  let T := ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let E (y : ℝ) := weightedPrefix a y-δ*(y:ℂ)^2/2
  have he : (h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))=
      (E (x+h)-E x)-T+δ*(h:ℂ)^2/2 := by
    have hd := weightedPrefix_difference (x:=x) hh.le a
    change weightedPrefix a (x+h)-weightedPrefix a x = _+T at hd
    dsimp [E]
    push_cast
    linear_combination -hd
  have hn : h*‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
    calc
      _ = ‖(h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
      _ = ‖(E (x+h)-E x)-T+δ*(h:ℂ)^2/2‖ := congrArg norm he
      _ ≤ ‖E (x+h)-E x‖+‖T‖+‖δ*(h:ℂ)^2/2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
        have hT : ‖T‖≤(h+1)*(h*L) := weightedPrefix_tail_bound hx hh.le hL a ha
        have hδ : ‖δ*(h:ℂ)^2/2‖=‖δ‖*h^2/2 := by
          simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
        rw [hδ]
        exact add_le_add (add_le_add (norm_sub_le _ _) hT) le_rfl
  have hd : h*((‖E (x+h)‖+‖E x‖)/h+(h+1)*L+‖δ‖*h/2)=
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by field_simp
  dsimp [E] at hn hd
  apply (mul_le_mul_iff_left₀ hh).mp
  rw [mul_comm _ h, mul_comm _ h, hd]
  exact hn

open Complex Real Set MeasureTheory Filter Topology

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

open Complex Filter Topology

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

lemma primeCharacterError_log_bound (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2≤x → 1≤Real.log x → (Real.log x)^(2*A+2)≤x →
        (q:ℝ)≤(Real.log x)^B →
        ‖primeCharacterError x χ‖≤M*x*(Real.log x)^(-A) := by
  obtain ⟨D,hD,hb⟩ := primeWeighted_error_bound (B+2*A+2)
  refine ⟨15*D+8,by positivity,?_⟩
  intro q _ χ hp x hx hL hpower hq
  let L := Real.log x
  let K := A+2
  let a := B+2*A+2
  let Q := ((q:ℝ)+2)^(1/2:ℝ)
  let h := x/L^K
  have hx0 : 0<x := by linarith
  have hx1 : 1<x := by linarith
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hK : 0<K := by dsimp [K]; linarith
  have ha : 0<a := by dsimp [a]; linarith
  have hpK : 0<L^K := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0<h := div_pos hx0 hpK
  have hK1 : 1≤L^K := Real.one_le_rpow hL hK.le
  have hhx : h≤x := (div_le_self hx0.le hK1)
  have hKh : L^K≤x := by
    apply (Real.rpow_le_rpow_of_exponent_le hL (show K≤2*A+2 by dsimp [K]; linarith)).trans
    exact hpower
  have hh1 : 1≤h := (le_div_iff₀ hpK).mpr (by simpa using hKh)
  have hyx : x≤x+h := by linarith
  have hy : 1<x+h := by linarith
  have hy2 : x+h≤2*x := by linarith
  have hLy : L≤Real.log (x+h) := Real.log_le_log hx0 hyx
  have hLy1 : 1≤Real.log (x+h) := hL.trans hLy
  have hLy2 : Real.log (x+h)≤2*L := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; rfl
  have hQ0 : 0≤Q := by dsimp [Q]; positivity
  have hQ : Q≤3*L^B := by
    have hq2 : 1≤(q:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) q; linarith
    have hqpow : Q≤(q:ℝ)+2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq2 (show (1/2:ℝ)≤1 by norm_num)
    have hLB : 1≤L^B := Real.one_le_rpow hL hB.le
    linarith
  let E (y : ℝ) := ‖weightedPrefix (primeCoefficients χ) y-characterMain χ*(y:ℂ)^2/2‖
  have hEx : E x≤D*Q*x^2*L^(-a)+x := hb q χ hp x hx1 hL
  have hEy : E (x+h)≤4*D*Q*x^2*L^(-a)+2*x := by
    calc
      _ ≤ D*Q*(x+h)^2*(Real.log (x+h))^(-a)+(x+h) := hb q χ hp (x+h) hy hLy1
      _ ≤ D*Q*(2*x)^2*L^(-a)+2*x := by
        apply add_le_add _ hy2
        apply mul_le_mul _ (Real.rpow_le_rpow_of_nonpos hL0 hLy (neg_nonpos.mpr ha.le)) (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  have hcoeff (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      ‖primeCoefficients χ n‖≤2*L := by
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by have := (Finset.mem_Ioc.mp hn).1; omega)
    have hnx : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith : 0≤x+h)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans ((Real.log_le_log hn0 hnx).trans hLy2)
  have heq : primeCharacterError x χ=
      (∑ n∈Finset.Ioc 0 ⌊x⌋₊, primeCoefficients χ n)-characterMain χ*(x:ℂ) := by
    classical
    simp only [primeCharacterError,primeCharacterPrefix,primeCoefficients,characterMain]
    split_ifs <;> simp
  rw [heq]
  have hu := prefix_unsmoothing hx0.le hh0 (show 0≤2*L by positivity)
    (primeCoefficients χ) (characterMain χ) hcoeff
  change _≤(E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 at hu
  have hδ : ‖characterMain χ‖*h/2≤h := by
    have := mul_le_mul_of_nonneg_right (characterMain_norm_le χ) hh0.le
    linarith
  have htail : (h+1)*(2*L)≤4*h*L := by nlinarith
  have herr : (E (x+h)+E x)/h ≤ 15*D*x*L^(-A)+3*x*L^(-A) := by
    calc
      _ ≤ (5*D*Q*x^2*L^(-a)+3*x)/h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        linarith
      _ ≤ (5*D*(3*L^B)*x^2*L^(-a)+3*x)/h := by gcongr
      _ = (15*D*L^B*x^2*L^(-a)+3*x)/h := by ring
      _ = 15*D*x*L^(-A)+3*L^K := by
        dsimp [h]
        rw [div_eq_mul_inv,inv_div]
        have hr : L^B*L^(-a)*L^K=L^(-A) := by
          rw [←Real.rpow_add hL0,←Real.rpow_add hL0]
          congr 1
          dsimp [a,K]
          ring
        field_simp
        linear_combination 15*D*x*hr
      _ ≤ _ := by
        have ht : L^K≤x*L^(-A) := by
          calc
            _ = L^(2*A+2)*L^(-A) := by rw [←Real.rpow_add hL0]; congr 1; dsimp [K]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hpower (by positivity)
        nlinarith [ht]
  have hsmall : h≤x*L^(-A) := by
    dsimp [h]
    rw [div_eq_mul_inv,←Real.rpow_neg hL0.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (show -K≤-A by dsimp [K]; linarith)) hx0.le
  have htail' : 4*h*L≤4*x*L^(-A) := by
    calc
      _ = 4*x*L^(1-K) := by
        dsimp [h]
        rw [div_eq_mul_inv,Real.rpow_sub hL0,Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (show 1-K≤-A by dsimp [K]; linarith)) (by positivity)
  calc
    _ ≤ (E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 := hu
    _ ≤ (15*D*x*L^(-A)+3*x*L^(-A))+4*x*L^(-A)+x*L^(-A) :=
      add_le_add (add_le_add herr (htail.trans htail')) (hδ.trans hsmall)
    _ = _ := by ring

theorem siegelWalfisz : SiegelWalfisz := by
  intro A B hA hB
  obtain ⟨M,hM,hb⟩ := primeCharacterError_log_bound A B hA hB
  have hevent : ∀ᶠ x : ℝ in atTop, 2≤x ∧ 1≤Real.log x ∧ (Real.log x)^(2*A+2)≤x := by
    filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (2*A+2) (by norm_num : (0:ℝ)<1)] with x hx hex hp
    refine ⟨hx,?_,by simpa only [Real.rpow_one] using hp⟩
    rw [←Real.log_exp (1:ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hex
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hevent
  refine ⟨M,hM,max x₀ 2,by have := le_max_right x₀ (2:ℝ); linarith,?_⟩
  intro x hx d hd hdlog χ hχ
  let : NeZero d := ⟨ne_of_gt hd⟩
  obtain ⟨hx2,hlog,hpower⟩ := hx₀ x ((le_max_left _ _).trans hx)
  exact hb d χ hχ x hx2 hlog hpower hdlog

theorem bombieriVinogradov_oai : BombieriVinogradov :=
  bombieriVinogradov_of_siegelWalfisz siegelWalfisz

end LargePrimeGaps

end OAI
end

theorem solution : type_of% @OAI.LargePrimeGaps.bombieriVinogradov_oai := @OAI.LargePrimeGaps.bombieriVinogradov_oai

-- Prove2me | solution 1 for OAI.FiniteCircle.mask_denominator_descent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:04:29.254417+00:00
-- url     : https://prove2.me/submissions/4dd04a2b-29c3-483d-9010-6054019cc7f7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskDescent.lean:L148-L266
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.mask_denominator_descent. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Theorems.Thm_OAI_FiniteCircle_circleCost_order_lower
import Theorems.Thm_OAI_FiniteCircle_mask_minimizer_options

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem subcircle_injective {M p : ℕ} [NeZero M] [NeZero p] (hp : p ∣ M) :
    Function.Injective (subcircle hp) := by
  apply (injective_iff_map_eq_zero (subcircle hp)).mpr
  intro a ha
  rw [subcircle_val] at ha
  have hd := (ZMod.natCast_eq_zero_iff (M/p*a.val) M).mp ha
  have hM : M/p*p = M := Nat.div_mul_cancel hp
  have hpos : 0 < M/p := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hp) (NeZero.pos p)
  have hd' : p ∣ a.val := by
    exact (Nat.mul_dvd_mul_iff_left hpos).mp (show M/p*p ∣ M/p*a.val by simpa only [hM] using hd)
  have haz := Nat.eq_zero_of_dvd_of_lt hd' a.val_lt
  exact (ZMod.val_eq_zero a).mp haz

theorem add_ne_zero_of_coprime_orders {G : Type*} [AddCommGroup G] {x y : G}
    {q r : ℕ} (hc : q.Coprime r) (hx : x ≠ 0) (hq : q • x = 0) (hr : r • y = 0) :
    x+y ≠ 0 := by
  intro h
  have he : y = -x := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
  rw [he, smul_neg, neg_eq_zero] at hr
  have hq' := addOrderOf_dvd_of_nsmul_eq_zero hq
  have hr' := addOrderOf_dvd_of_nsmul_eq_zero hr
  have ho : addOrderOf x = 1 := Nat.dvd_one.mp (hc ▸ Nat.dvd_gcd hq' hr')
  exact hx (AddMonoid.addOrderOf_eq_one_iff.mp ho)

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.MaskDescent ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem primes_coprime_prod {S A : Finset ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hA : ∀ q ∈ A, q.Prime) (hdis : Disjoint S A) :
    (∏ q ∈ S, q).Coprime (∏ q ∈ A, q) := by
  apply Nat.Coprime.prod_left
  intro q hq
  apply Nat.Coprime.prod_right
  intro r hr
  apply (hS q hq).coprime_iff_not_dvd.mpr
  intro hd
  have he : q = r := (Nat.prime_dvd_prime_iff_eq (hS q hq) (hA r hr)).mp hd
  exact Finset.disjoint_left.mp hdis hq (he.symm ▸ hr)

 theorem nsmul_zero_of_dvd {G : Type*} [AddCommGroup G] {n m : ℕ} {x : G}
    (h : n ∣ m) (hx : n • x = 0) : m • x = 0 := by
  obtain ⟨a,rfl⟩ := h
  rw [mul_nsmul, hx, nsmul_zero]

 theorem PhaseSupported.mono {G : Type*} [AddCommGroup G] {S A : Finset ℕ}
    {x : G} (hx : PhaseSupported S x) (h : S ⊆ A) : PhaseSupported A x :=
  nsmul_zero_of_dvd (Finset.prod_dvd_prod_of_subset S A id h) hx

 theorem PhaseSupported.add {G : Type*} [AddCommGroup G] {S A : Finset ℕ}
    {x y : G} (hx : PhaseSupported S x) (hy : PhaseSupported A y) :
    PhaseSupported (S ∪ A) (x+y) := by
  have hx' := hx.mono (show S ⊆ S ∪ A from Finset.subset_union_left)
  have hy' := hy.mono (show A ⊆ S ∪ A from Finset.subset_union_right)
  change _ • (x+y) = 0
  rw [nsmul_add, hx', hy', add_zero]

 theorem phase_add_supported_ne_zero {G : Type*} [AddCommGroup G] {S A : Finset ℕ}
    {x y : G} (hx : PhaseSupported S x) (hy : PhaseSupported A y)
    (hS : ∀ q ∈ S, q.Prime) (hA : ∀ q ∈ A, q.Prime) (hdis : Disjoint S A)
    (hne : x ≠ 0) : x+y ≠ 0 :=
  add_ne_zero_of_coprime_orders (primes_coprime_prod hS hA hdis) hne hx hy

 theorem support_subcircle {M p : ℕ} (hp : p ∣ M) (z : ZMod p) :
    PhaseSupported {p} (subcircle hp z) := by
  simp only [PhaseSupported, Finset.prod_singleton, ← map_nsmul]
  rw [nsmul_eq_mul]
  simp

 theorem support_mask_sum {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p l k ∣ M) (z : MaskResidues h p l) :
    PhaseSupported ((Finset.univ.filter (fun k : Fin h => z k ≠ 0)).image (fun k : Fin h => p l k))
      (∑ k, subcircle (hd k) (z k)) := by
  classical
  unfold PhaseSupported
  rw [Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hz : z k = 0
  · simp [hz]
  · apply nsmul_zero_of_dvd
    · exact Finset.dvd_prod_of_mem _ (Finset.mem_image.mpr ⟨k, by simp [hz], rfl⟩)
    · simpa only [PhaseSupported, Finset.prod_singleton] using support_subcircle (hd k) (z k)

 theorem circleCost_support_lower {M h K : ℕ} [NeZero M] (hh : 1 ≤ h)
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime ∧ q ≤ h^4) (hcard : S.card ≤ K)
    {x : ZMod M} (hx : x ≠ 0) (hs : PhaseSupported S x) :
    1 / ((h:ℝ)^(4*K)) ≤ circleCost x := by
  let Q := ∏ q ∈ S, q
  have hQ : 0 < Q := Finset.prod_pos (fun q hq => (hS q hq).1.pos)
  have hQu : Q ≤ h^(4*K) := by
    calc
      Q ≤ ∏ _q ∈ S, h^4 := Finset.prod_le_prod' (fun q hq => (hS q hq).2)
      _ = h^(4*S.card) := by simp only [Finset.prod_const]; rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right hh (by omega)
  have he := circleCost_order_lower hQ hx hs
  have hp : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  rw [div_le_iff₀ (pow_pos hp _)]
  have hc := circleCost_nonneg x
  have hQu' : (Q:ℝ) ≤ (h:ℝ)^(4*K) := by exact_mod_cast hQu
  nlinarith

 theorem resetBudget_mono {K T n m l r : ℕ} (h : n+l*T ≤ m+r*T) :
    resetBudget K T n l ≤ resetBudget K T m r := by
  unfold resetBudget
  exact Nat.div_le_div_right (by omega)

 theorem resetBudget_overflow {K T n s l : ℕ} (hK : 2 ≤ K)
    (hs : s < T) (hover : K < n+s) :
    resetBudget K T 1 l + 1 ≤ resetBudget K T n (l+1) := by
  have hstep : 1+l*T+K-2+(K-1) ≤ n+(l+1)*T+K-2 := by
    rw [Nat.add_mul]
    omega
  have hdiv := Nat.div_le_div_right (c := K-1) hstep
  rw [Nat.add_div_right _ (by omega : 0 < K-1)] at hdiv
  exact hdiv

 theorem descentBound_pos {h K T n l : ℕ} (hh : 0 < h) (hT : 0 < T) :
    0 < descentBound h K T n l := by
  unfold descentBound
  positivity

 theorem descentBound_step {h K T n m l e : ℕ} (hh : 0 < h) (hT : 1 ≤ T)
    (he : l + resetBudget K T m l + e ≤ l+1 + resetBudget K T n (l+1)) :
    descentBound h K T n (l+1) ≤
      (1/(4*(T:ℝ)^e))*descentBound h K T m l := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hp : (0:ℝ) < h := by exact_mod_cast hh
  have hlu : (T:ℝ)^(l + resetBudget K T m l + e) ≤
      (T:ℝ)^(l+1 + resetBudget K T n (l+1)) := pow_le_pow_right₀ ht he
  unfold descentBound
  rw [one_div_mul_one_div]
  apply one_div_le_one_div_of_le
  · positivity
  · calc
      4*(T:ℝ)^e*((4:ℝ)^l*(T:ℝ)^(l+resetBudget K T m l)*(h:ℝ)^(4*K)) =
        (4:ℝ)^(l+1)*(T:ℝ)^(l+resetBudget K T m l+e)*(h:ℝ)^(4*K) := by
          rw [pow_succ, pow_add]; ring
      _ ≤ _ := by gcongr

 theorem support_card_pos {G : Type*} [AddCommGroup G] {S : Finset ℕ}
    {x : G} (hx : x ≠ 0) (hs : PhaseSupported S x) : 0 < S.card := by
  by_contra h
  have he : S = ∅ := Finset.card_eq_zero.mp (by omega)
  subst S
  exact hx (by simpa [PhaseSupported] using hs)

 theorem descentBound_base {h K T n : ℕ} (hh : 0 < h) (hT : 1 ≤ T) :
    descentBound h K T n 0 ≤ 1/(h:ℝ)^(4*K) := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hp : (0:ℝ) < h := by exact_mod_cast hh
  unfold descentBound
  simp only [pow_zero, one_mul, zero_add]
  apply one_div_le_one_div_of_le (by positivity)
  exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ ht)

theorem mask_denominator_descent {h H M K T : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hT : 2 ≤ T) (hhT : h ≤ T^2) (hTh : 2*T ≤ h) (hK : 2 ≤ K)
    (hd : ∀ j (k : Fin h), p j k ∣ M) (hn : ∀ j (k : Fin h), 0 < p j k)
    (hp : ∀ j, 1 ≤ j → j ≤ H → ∀ k : Fin h, (p j k).Prime)
    (hlo : ∀ j, 1 ≤ j → j ≤ H → ∀ k : Fin h, h^3 ≤ p j k)
    (hhi : ∀ j, 1 ≤ j → j ≤ H → ∀ k : Fin h, p j k ≤ 2*h^3)
    (hlevel : ∀ j r, 1 ≤ j → j ≤ H → 1 ≤ r → r ≤ H → j ≠ r →
      ∀ k t : Fin h, p j k ≠ p r t) :
    ∀ l, l ≤ H → ∀ (S : Finset ℕ) (x : ZMod M),
      S.card ≤ K → (∀ q ∈ S, q.Prime ∧ q ≤ h^4) → LowerFresh h p l S →
      x ≠ 0 → PhaseSupported S x →
      descentBound h K T S.card l ≤ maskCost h p M hd hn l x := by
  classical
  have hh : 0 < h := by omega
  have hh2 : 2 ≤ h := by omega
  have hTp : 0 < T := by omega
  have hin (j : ℕ) (hj : 1 ≤ j) (hjH : j ≤ H) (k : Fin h) : p j k ≤ h^4 := by
    calc
      p j k ≤ 2*h^3 := hhi j hj hjH k
      _ ≤ h*h^3 := Nat.mul_le_mul_right _ hh2
      _ = h^4 := by ring
  intro l
  induction l with
  | zero =>
    intro _ S x hcard hS _ hx hs
    exact (descentBound_base hh (by omega)).trans
      (circleCost_support_lower (by omega) hS hcard hx hs)
  | succ l ih =>
    intro hlH S x hcard hS hfresh hx hs
    let : ∀ k : Fin h, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let f := maskCost h p M hd hn l
    obtain ⟨z, hact, hinact⟩ := mask_minimizer_options hh (hd (l+1))
      (hp (l+1) (by omega) hlH) (hlo (l+1) (by omega) hlH)
      (hhi (l+1) (by omega) hlH) f x
    let A := Finset.univ.filter (fun k : Fin h => z k ≠ 0)
    let P := A.image (fun k : Fin h => p (l+1) k)
    have hpP (q : ℕ) (hq : q ∈ P) : q.Prime ∧ q ≤ h^4 := by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨hp (l+1) (by omega) hlH k, hin (l+1) (by omega) hlH k⟩
    have hfreshP : LowerFresh h p l P := by
      intro j hj hjl k hk
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hk
      exact hlevel j (l+1) hj (by omega) (by omega) hlH (by omega) k t ht.symm
    have hdis : Disjoint S P := by
      apply Finset.disjoint_left.mpr
      intro q hq hqP
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hqP
      exact hfresh (l+1) (by omega) (by omega) k hq
    have hchild (k : Fin h) : descentBound h K T 1 l ≤ f (subcircle (hd (l+1) k) 1) := by
      let : Fact (p (l+1) k).Prime := ⟨hp (l+1) (by omega) hlH k⟩
      have hne : subcircle (hd (l+1) k) 1 ≠ 0 := by
        simpa only [map_zero] using (subcircle_injective (hd (l+1) k)).ne (one_ne_zero : (1:ZMod (p (l+1) k)) ≠ 0)
      have hfr : LowerFresh h p l {p (l+1) k} := by
        intro j hj hjl t ht
        have he : p j t = p (l+1) k := Finset.mem_singleton.mp ht
        exact hlevel j (l+1) hj (by omega) (by omega) hlH (by omega) t k he
      simpa only [Finset.card_singleton] using ih (by omega) {p (l+1) k}
        (subcircle (hd (l+1) k) 1) (by simp; omega)
        (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using
          (show (p (l+1) k).Prime ∧ p (l+1) k ≤ h^4 from
            ⟨hp (l+1) (by omega) hlH k, hin (l+1) (by omega) hlH k⟩))
        hfr hne (support_subcircle (hd (l+1) k) 1)
    have hreset : (A.card : ℝ)/(4*h)*descentBound h K T 1 l ≤ maskCost h p M hd hn (l+1) x :=
      hact _ (descentBound_pos hh hTp).le (fun k _ => hchild k)
    have hspos : 0 < S.card := support_card_pos hx hs
    have hhreal : (0:ℝ) < h := by exact_mod_cast hh
    have hTreal : (0:ℝ) < T := by exact_mod_cast hTp
    have hhTreal : (h:ℝ) ≤ (T:ℝ)^2 := by exact_mod_cast hhT
    by_cases hlarge : T ≤ A.card
    · have hbudget : resetBudget K T 1 l ≤ resetBudget K T S.card (l+1) := by
        apply resetBudget_mono
        rw [Nat.add_mul]
        omega
      have hstep := descentBound_step (K := K) (n := S.card) (m := 1) (l := l) (e := 1)
        hh (by omega : 1 ≤ T) (by omega)
      have hfac : (1/(4*(T:ℝ)^1)) ≤ (A.card : ℝ)/(4*h) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        simp only [pow_one]
        have hlarge' : (T:ℝ) ≤ A.card := by exact_mod_cast hlarge
        nlinarith
      exact hstep.trans ((mul_le_mul_of_nonneg_right hfac (descentBound_pos hh hTp).le).trans hreset)
    · have hsmall : A.card < T := by omega
      by_cases hover : K < S.card+A.card
      · have hapos : 0 < A.card := by omega
        have hbudget := resetBudget_overflow (l := l) hK hsmall hover
        have hstep := descentBound_step (K := K) (n := S.card) (m := 1) (l := l) (e := 2)
          hh (by omega : 1 ≤ T) (by omega)
        have hfac : (1/(4*(T:ℝ)^2)) ≤ (A.card : ℝ)/(4*h) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have ha : (1:ℝ) ≤ A.card := by exact_mod_cast hapos
          nlinarith [sq_nonneg (T:ℝ)]
        exact hstep.trans ((mul_le_mul_of_nonneg_right hfac (descentBound_pos hh hTp).le).trans hreset)
      · have hPC : P.card ≤ A.card := Finset.card_image_le
        have hunion : (S ∪ P).card ≤ S.card+A.card := (Finset.card_union_le S P).trans (by omega)
        have hnew : PhaseSupported (S ∪ P) (x+∑ k,subcircle (hd (l+1) k) (z k)) :=
          hs.add (support_mask_sum (hd (l+1)) z)
        have hnz : (x+∑ k,subcircle (hd (l+1) k) (z k)) ≠ 0 :=
          phase_add_supported_ne_zero hs (support_mask_sum (hd (l+1)) z)
            (fun q hq => (hS q hq).1) (fun q hq => (hpP q hq).1) hdis hx
        have hfr : LowerFresh h p l (S ∪ P) := by
          intro j hj hjl k hk
          rcases Finset.mem_union.mp hk with hk | hk
          · exact hfresh j hj (by omega) k hk
          · exact hfreshP j hj hjl k hk
        have hSUP (q : ℕ) (hq : q ∈ S ∪ P) : q.Prime ∧ q ≤ h^4 := by
          rcases Finset.mem_union.mp hq with hq | hq
          · exact hS q hq
          · exact hpP q hq
        have hlower := ih (by omega) (S ∪ P) (x+∑ k,subcircle (hd (l+1) k) (z k))
          (by omega) hSUP hfr hnz hnew
        have hbudget : resetBudget K T (S∪P).card l ≤ resetBudget K T S.card (l+1) := by
          apply resetBudget_mono
          rw [Nat.add_mul]
          omega
        have hstep := descentBound_step (K := K) (n := S.card) (m := (S∪P).card) (l := l) (e := 0)
          hh (by omega : 1 ≤ T) (by omega)
        simp only [pow_zero, mul_one] at hstep
        exact hstep.trans ((mul_le_mul_of_nonneg_left hlower (by norm_num : (0:ℝ)≤1/4)).trans
          (hinact (by change 2*A.card ≤ h; omega)))

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.mask_denominator_descent := @_root_.OAI.FiniteCircle.mask_denominator_descent

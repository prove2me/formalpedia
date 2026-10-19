-- Prove2me | solution 1 for OAI.FiniteCircle.excluded_denominator_descent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:06:54.940759+00:00
-- url     : https://prove2.me/submissions/a4a44587-f888-404f-8778-0fc8b8bd2afc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/ExcludedDescent.lean:L81-L200
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.excluded_denominator_descent. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Theorems.Thm_OAI_FiniteCircle_circleCost_order_lower
import Theorems.Thm_OAI_FiniteCircle_excluded_minimizer_options

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

 theorem support_card_pos {G : Type*} [AddCommGroup G] {S : Finset ℕ}
    {x : G} (hx : x ≠ 0) (hs : PhaseSupported S x) : 0 < S.card := by
  by_contra h
  have he : S = ∅ := Finset.card_eq_zero.mp (by omega)
  subst S
  exact hx (by simpa [PhaseSupported] using hs)

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.ExcludedDescent ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem PhaseSupported.neg {G : Type*} [AddCommGroup G] {S : Finset ℕ}
    {x : G} (hx : PhaseSupported S x) : PhaseSupported S (-x) := by
  change _ • (-x) = 0
  rw [smul_neg, hx, neg_zero]

 theorem circleCost_support_lower_pow {M h K e : ℕ} [NeZero M] (hh : 1 ≤ h)
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime ∧ q ≤ h^e) (hcard : S.card ≤ K)
    {x : ZMod M} (hx : x ≠ 0) (hs : PhaseSupported S x) :
    1 / ((h:ℝ)^(e*K)) ≤ circleCost x := by
  let Q := ∏ q ∈ S, q
  have hQ : 0 < Q := Finset.prod_pos (fun q hq => (hS q hq).1.pos)
  have hQu : Q ≤ h^(e*K) := by
    calc
      Q ≤ ∏ _q ∈ S, h^e := Finset.prod_le_prod' (fun q hq => (hS q hq).2)
      _ = h^(e*S.card) := by simp only [Finset.prod_const]; rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right hh (Nat.mul_le_mul_left e hcard)
  have he := circleCost_order_lower hQ hx hs
  have hp : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  rw [div_le_iff₀ (pow_pos hp _)]
  have hc := circleCost_nonneg x
  have hQu' : (Q:ℝ) ≤ (h:ℝ)^(e*K) := by exact_mod_cast hQu
  nlinarith

 theorem pairResetBudget_mono {K T n m l r : ℕ} (h : n+l*T ≤ m+r*T) :
    pairResetBudget K T n l ≤ pairResetBudget K T m r := by
  unfold pairResetBudget
  exact Nat.div_le_div_right (by omega)

 theorem pairResetBudget_overflow {K T n s l : ℕ} (hK : 3 ≤ K)
    (hs : s < T) (hover : K < n+s) :
    pairResetBudget K T 2 l+1 ≤ pairResetBudget K T n (l+1) := by
  have hstep : 2+l*T+K-3+(K-2) ≤ n+(l+1)*T+K-3 := by
    rw [Nat.add_mul]; omega
  have hdiv := Nat.div_le_div_right (c := K-2) hstep
  rw [Nat.add_div_right _ (by omega : 0 < K-2)] at hdiv
  exact hdiv

 theorem pairDescentBound_pos {m K T B n l : ℕ} (hm : 0 < m) (hB : 0 < B) :
    0 < pairDescentBound m K T B n l := by
  unfold pairDescentBound; positivity

 theorem pairDescentBound_step {m K T B n s l e : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    (he : l+3*pairResetBudget K T s l+e ≤ l+1+3*pairResetBudget K T n (l+1)) :
    pairDescentBound m K T B n (l+1) ≤
      (1/(4*(B:ℝ)^e))*pairDescentBound m K T B s l := by
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  have hlu := pow_le_pow_right₀ hb he
  unfold pairDescentBound
  rw [one_div_mul_one_div]
  apply one_div_le_one_div_of_le
  · positivity
  · calc
      4*(B:ℝ)^e*((4:ℝ)^l*(B:ℝ)^(l+3*pairResetBudget K T s l)*(m:ℝ)^(5*K)) =
        (4:ℝ)^(l+1)*(B:ℝ)^(l+3*pairResetBudget K T s l+e)*(m:ℝ)^(5*K) := by
          rw [pow_succ, pow_add]; ring
      _ ≤ _ := by gcongr

 theorem pairDescentBound_base {m K T B n : ℕ} (hm : 0 < m) (hB : 1 ≤ B) :
    pairDescentBound m K T B n 0 ≤ 1/(m:ℝ)^(5*K) := by
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  unfold pairDescentBound
  simp only [pow_zero, one_mul, zero_add]
  apply one_div_le_one_div_of_le (by positivity)
  exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hb)

theorem excluded_denominator_descent {m H M K T B : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hT : 2 ≤ T) (hB : 1 ≤ B) (hmB : m ≤ B^4) (hmTB : m ≤ T*B)
    (hsmall : 2*T ≤ m) (hK : 3 ≤ K)
    (hd : ∀ l (k : Fin m), p l k ∣ M) (hn : ∀ l (k : Fin m), 0 < p l k)
    (hp : ∀ l, 1 ≤ l → l ≤ H → ∀ k : Fin m, (p l k).Prime)
    (hin : ∀ l, 1 ≤ l → l ≤ H → ∀ k : Fin m, p l k ≤ m^5)
    (hinj : ∀ l, 1 ≤ l → l ≤ H → Function.Injective (fun k : Fin m => p l k))
    (hlevel : ∀ l r, 1 ≤ l → l ≤ H → 1 ≤ r → r ≤ H → l ≠ r →
      ∀ i j : Fin m, p l i ≠ p r j) :
    ∀ l, l ≤ H → ∀ (S : Finset ℕ) (x : ZMod M), S.card ≤ K →
      (∀ q ∈ S, q.Prime ∧ q ≤ m^5) → LowerFresh m p l S → x ≠ 0 →
      PhaseSupported S x → pairDescentBound m K T B S.card l ≤ excludedCost m p M hd hn l x := by
  classical
  have hm : 0 < m := by omega
  have hBp : 0 < B := by omega
  intro l
  induction l with
  | zero =>
    intro _ S x hcard hS _ hx hs
    exact (pairDescentBound_base hm hB).trans (circleCost_support_lower_pow (by omega) hS hcard hx hs)
  | succ l ih =>
    intro hlH S x hcard hS hfresh hx hs
    let : ∀ k : Fin m, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let f := excludedCost m p M hd hn l
    obtain ⟨z,hact,hinact⟩ := excluded_minimizer_options (by omega) (hd (l+1)) (hn (l+1)) f x
    let A := Finset.univ.filter (fun k : Fin m => z k ≠ 0)
    let P := A.image (fun k : Fin m => p (l+1) k)
    have hpP (q : ℕ) (hq : q ∈ P) : q.Prime ∧ q ≤ m^5 := by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨hp (l+1) (by omega) hlH k, hin (l+1) (by omega) hlH k⟩
    have hfreshP : LowerFresh m p l P := by
      intro j hj hjl k hk
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hk
      exact hlevel j (l+1) hj (by omega) (by omega) hlH (by omega) k t ht.symm
    have hdis : Disjoint S P := by
      apply Finset.disjoint_left.mpr
      intro q hq hqP
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hqP
      exact hfresh (l+1) (by omega) (by omega) k hq
    have hchild (i j : Fin m) (hi : z i ≠ 0) (hij : i ≠ j) :
        pairDescentBound m K T B 2 l ≤ f (subcircle (hd (l+1) i) (z i)-subcircle (hd (l+1) j) (z j)) := by
      have hne : p (l+1) i ≠ p (l+1) j := (hinj (l+1) (by omega) hlH).ne hij
      let Q : Finset ℕ := {p (l+1) i,p (l+1) j}
      have hQ : Q.card = 2 := by simp [Q,hne]
      have hfr : LowerFresh m p l Q := by
        intro r hr hrl k hk
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with hk | hk
        · exact hlevel r (l+1) hr (by omega) (by omega) hlH (by omega) k i hk
        · exact hlevel r (l+1) hr (by omega) (by omega) hlH (by omega) k j hk
      have hpi := hp (l+1) (by omega) hlH i
      have hpj := hp (l+1) (by omega) hlH j
      have hsupp : PhaseSupported Q (subcircle (hd (l+1) i) (z i)-subcircle (hd (l+1) j) (z j)) := by
        simpa only [Finset.singleton_union, sub_eq_add_neg] using
          (support_subcircle (hd (l+1) i) (z i)).add (support_subcircle (hd (l+1) j) (z j)).neg
      have hnon : subcircle (hd (l+1) i) (z i)-subcircle (hd (l+1) j) (z j) ≠ 0 := by
        rw [sub_eq_add_neg]
        apply phase_add_supported_ne_zero (support_subcircle (hd (l+1) i) (z i))
          (support_subcircle (hd (l+1) j) (z j)).neg
        · simpa using hpi
        · simpa using hpj
        · simpa using hne
        · simpa only [map_zero] using (subcircle_injective (hd (l+1) i)).ne hi
      have hQP (q : ℕ) (hq : q ∈ Q) : q.Prime ∧ q ≤ m^5 := by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact ⟨hpi,hin (l+1) (by omega) hlH i⟩
        · exact ⟨hpj,hin (l+1) (by omega) hlH j⟩
      simpa only [hQ] using ih (by omega) Q _ (by omega) hQP hfr hnon hsupp
    have hreset : (A.card:ℝ)/(4*m)*pairDescentBound m K T B 2 l ≤ excludedCost m p M hd hn (l+1) x :=
      hact _ (pairDescentBound_pos hm hBp).le hchild
    have hspos : 0 < S.card := support_card_pos hx hs
    have hmreal : (0:ℝ) < m := by exact_mod_cast hm
    have hBreal : (0:ℝ) < B := by exact_mod_cast hBp
    by_cases hlarge : T ≤ A.card
    · have hbudget : pairResetBudget K T 2 l ≤ pairResetBudget K T S.card (l+1) := by
        apply pairResetBudget_mono
        rw [Nat.add_mul]; omega
      have hstep := pairDescentBound_step (K := K) (T := T) (n := S.card) (s := 2) (l := l) (e := 1) hm hB (by omega)
      have hfac : 1/(4*(B:ℝ)^1) ≤ (A.card:ℝ)/(4*m) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        simp only [pow_one]
        have hmTB' : (m:ℝ) ≤ T*B := by exact_mod_cast hmTB
        have ha : (T:ℝ) ≤ A.card := by exact_mod_cast hlarge
        nlinarith
      exact hstep.trans ((mul_le_mul_of_nonneg_right hfac (pairDescentBound_pos hm hBp).le).trans hreset)
    · have hsm : A.card < T := by omega
      by_cases hover : K < S.card+A.card
      · have hapos : 0 < A.card := by omega
        have hbudget := pairResetBudget_overflow (l := l) hK hsm hover
        have hstep := pairDescentBound_step (K := K) (T := T) (n := S.card) (s := 2) (l := l) (e := 4) hm hB (by omega)
        have hfac : 1/(4*(B:ℝ)^4) ≤ (A.card:ℝ)/(4*m) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have ha : (1:ℝ) ≤ A.card := by exact_mod_cast hapos
          have hmB' : (m:ℝ) ≤ (B:ℝ)^4 := by exact_mod_cast hmB
          nlinarith [pow_nonneg (Nat.cast_nonneg B : (0:ℝ) ≤ B) 4]
        exact hstep.trans ((mul_le_mul_of_nonneg_right hfac (pairDescentBound_pos hm hBp).le).trans hreset)
      · have hPC : P.card ≤ A.card := Finset.card_image_le
        have hunion : (S ∪ P).card ≤ S.card+A.card := (Finset.card_union_le S P).trans (by omega)
        have hnew := hs.add (support_mask_sum (hd (l+1)) z)
        have hnz : (x+∑ k,subcircle (hd (l+1) k) (z k)) ≠ 0 :=
          phase_add_supported_ne_zero hs (support_mask_sum (hd (l+1)) z)
            (fun q hq => (hS q hq).1) (fun q hq => (hpP q hq).1) hdis hx
        have hfr : LowerFresh m p l (S ∪ P) := by
          intro j hj hjl k hk
          rcases Finset.mem_union.mp hk with hk | hk
          · exact hfresh j hj (by omega) k hk
          · exact hfreshP j hj hjl k hk
        have hSUP (q : ℕ) (hq : q ∈ S ∪ P) : q.Prime ∧ q ≤ m^5 := by
          rcases Finset.mem_union.mp hq with hq | hq
          · exact hS q hq
          · exact hpP q hq
        have hlower := ih (by omega) (S ∪ P) _ (by omega) hSUP hfr hnz hnew
        have hbudget : pairResetBudget K T (S∪P).card l ≤ pairResetBudget K T S.card (l+1) := by
          apply pairResetBudget_mono
          rw [Nat.add_mul]; omega
        have hstep := pairDescentBound_step (K := K) (T := T) (n := S.card) (s := (S∪P).card) (l := l) (e := 0) hm hB (by omega)
        simp only [pow_zero,mul_one] at hstep
        exact hstep.trans ((mul_le_mul_of_nonneg_left hlower (by norm_num : (0:ℝ) ≤ 1/4)).trans
          (hinact (by change 2*A.card ≤ m; omega)))

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.excluded_denominator_descent := @_root_.OAI.FiniteCircle.excluded_denominator_descent

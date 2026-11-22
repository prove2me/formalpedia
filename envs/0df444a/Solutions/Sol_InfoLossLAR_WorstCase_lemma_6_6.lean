-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_6_6
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:27:23.729999+00:00
-- url     : https://prove2.me/submissions/ffc76eda-fc90-4e5a-8655-83dc5e66e627

import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Mathlib
import Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_4
import Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_5

section
open InfoLossLAR.WorstCase
open scoped BigOperators
set_option autoImplicit false
namespace CarryEstimate
private theorem larShift {q d : ℕ} [NeZero q] (T : Matrix (Fin d) (Fin d) ℤ)
    (x y c : Fin d → ℤ) (h : T.mulVec y = (q : ℤ) • c) :
    AR q T (x + y) = AR q T x + c := by
  funext i
  simp only [AR, carry, Matrix.mulVec_add, h, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [show (((T.mulVec x i : ℤ) : ℚ) + (q : ℚ) * (c i : ℚ)) / (q : ℚ) =
    ((T.mulVec x i : ℤ) : ℚ) / (q : ℚ) + (c i : ℚ) by field_simp]
  exact Int.floor_add_intCast _ _

private theorem larModMul {q m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℤ) :
    modq q (A.mulVec x) = (matModq q A).mulVec (modq q x) := by
  funext i
  simp [modq, matModq, Matrix.mulVec, dotProduct]

private theorem larModAdd {q n : ℕ} (x y : Fin n → ℤ) :
    modq q (x + y) = modq q x + modq q y := by
  ext i
  simp [modq]

private theorem larModLift {q n : ℕ} [NeZero q] (x : Fin n → ZMod q) :
    modq q (lift x) = x := by
  funext i
  simp [modq, lift]

private theorem larLiftDiff {q n : ℕ} (x y : Fin n → ℤ) (h : modq q x = modq q y) :
    ∃ z : Fin n → ℤ, x = y + (q : ℤ) • z := by
  have hd (i : Fin n) : (q : ℤ) ∣ x i - y i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    rw [Int.cast_sub, show (x i : ZMod q) = (y i : ZMod q) from congrFun h i, sub_self]
  choose z hz using hd
  refine ⟨z, funext fun i => ?_⟩
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_comm] using sub_eq_iff_eq_add.mp (hz i)

theorem geom {q d : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hdq : q ≤ d)
    (y : Fin d → ℤ) :
    let T := TDef63 q d
    let w := T.mulVec y
    let z := modq q y
    let e := modq q w
    e = modq q (T.mulVec (lift z)) ∧ e ∈ H0 q d ∧
    (z = cT q d e ↔ carry q w ∈ imageLattice T) ∧
    (carry q w ∈ imageLattice T ↔ (q : ℤ) ∣ ∑ i, carry q w i) := by
  classical
  let T := TDef63 q d
  let z := modq q y
  let e := modq q (T.mulVec y)
  have image := (lemma_6_4 q d Fact.out hq2 hdq).1
  have he : e = modq q (T.mulVec (lift z)) := by
    simp [e,larModMul,z,larModLift]
  have he0 : e ∈ H0 q d := by
    change (∑ i, ((T.mulVec y i:ℤ):ZMod q)) = 0
    rw [← Int.cast_sum,ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (image _).1 ⟨y,rfl⟩
  have hparam := lemma_6_5 q d hq2 hdq
  have hz : z = cT q d e ↔ z ∈ zeroFiber63 q d := by
    constructor
    · intro h; rw [h]; exact hparam.1.mapsTo he0
    · intro h; exact (he ▸ (hparam.2 z h).2).symm
  obtain ⟨k,hk⟩ := larLiftDiff y (lift z) (larModLift z).symm
  have hshift : carry q (T.mulVec y) = AR q T (lift z) + T.mulVec k := by
    conv_lhs => rw [hk]
    apply larShift
    exact Matrix.mulVec_smul _ _ _
  have hkc : (q:ℤ) ∣ ∑ i, T.mulVec k i := (image _).1 ⟨k,rfl⟩
  have hcrit : z ∈ zeroFiber63 q d ↔ (q:ℤ) ∣ ∑ i, carry q (T.mulVec y) i := by
    change (((∑ i, AR q T (lift z) i : ℤ) : ZMod q) = 0) ↔ _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd,hshift]
    simp only [Pi.add_apply,Finset.sum_add_distrib,dvd_add_left hkc]
  exact ⟨he,he0,hz.trans (hcrit.trans (image _).symm),image _⟩
end CarryEstimate
end

section
open InfoLossLAR.WorstCase
open scoped BigOperators Classical
set_option autoImplicit false
namespace CarryEstimate
noncomputable section
variable {X P B A C : Type*} [Fintype X] [Fintype A] [Fintype B] [Fintype C]
def mix (μ : X → ℝ) (ν : P → ℝ) (Y : P → X → B) (b : B) : ℝ :=
    ∑' p, ν p * ∑ x, if Y p x = b then μ x else 0
def push (f : A → B) (m : A → ℝ) (b : B) : ℝ := ∑ a, if f a = b then m a else 0
private theorem mix_summable (μ : X → ℝ) (ν : P → ℝ) (Y : P → X → B) (b : B)
    (hμ : ∀ x, 0 ≤ μ x) (hn : ∑ x, μ x = 1) (hν : ∀ p, 0 ≤ ν p) (hs : Summable ν) :
    Summable (fun p => ν p * ∑ x, if Y p x = b then μ x else 0) := by
  apply Summable.of_nonneg_of_le _ _ hs
  · intro p; apply mul_nonneg (hν p); apply Finset.sum_nonneg; intro x _; split_ifs <;> simp [hμ]
  · intro p; apply mul_le_of_le_one_right (hν p); rw [← hn]; apply Finset.sum_le_sum; intro x _; split_ifs <;> simp [hμ]
theorem mix_nonneg (μ : X → ℝ) (ν : P → ℝ) (Y : P → X → B) (b : B)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ p, 0 ≤ ν p) : 0 ≤ mix μ ν Y b := by
  apply tsum_nonneg; intro p; apply mul_nonneg (hν p); apply Finset.sum_nonneg; intro x _; split_ifs <;> simp [hμ]
theorem mix_test (μ : X → ℝ) (ν : P → ℝ) (Y : P → X → B) (f : B → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hn : ∑ x, μ x = 1) (hν : ∀ p, 0 ≤ ν p) (hs : Summable ν) :
    ∑ b, f b * mix μ ν Y b = ∑' p, ν p * ∑ x, f (Y p x) * μ x := by
  simp only [mix,← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun b _ => (mix_summable μ ν Y b hμ hn hν hs).mul_left (f b))]
  apply tsum_congr; intro p
  simp_rw [mul_left_comm (f _) (ν p),← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_ite]
theorem push_mix (μ : X → ℝ) (ν : P → ℝ) (Y : P → X → A) (f : A → B)
    (hμ : ∀ x, 0 ≤ μ x) (hn : ∑ x, μ x = 1) (hν : ∀ p, 0 ≤ ν p) (hs : Summable ν) :
    push f (mix μ ν Y) = mix μ ν (fun p x => f (Y p x)) := by
  funext b
  simpa [push,mix,ite_mul] using mix_test μ ν Y (fun a => if f a = b then 1 else 0) hμ hn hν hs
theorem triangle (a b c : A → ℝ) : sdist a c ≤ sdist a b + sdist b c := by
  unfold sdist
  rw [← mul_add,← Finset.sum_add_distrib]
  gcongr with i
  exact abs_sub_le _ _ _
theorem map_sdist (f : A → B) (P Q : A → ℝ) : sdist (push f P) (push f Q) ≤ sdist P Q := by
  unfold sdist; gcongr
  calc
    ∑ b, |push f P b - push f Q b| ≤ ∑ b, ∑ a, if f a = b then |P a-Q a| else 0 := by
      apply Finset.sum_le_sum; intro b _
      rw [push,push,← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro a _; split_ifs <;> simp
    _ = ∑ a, |P a-Q a| := by rw [Finset.sum_comm]; simp
theorem coupling (O R : A → B) (M : A → ℝ) (hn : ∀ a, 0 ≤ M a) :
    sdist (push O M) (push R M) ≤ ∑ a, if O a = R a then 0 else M a := by
  have hb (a : A) :
      ∑ b, |(if O a = b then M a else 0) - (if R a = b then M a else 0)| =
        2 * (if O a = R a then 0 else M a) := by
    by_cases h : O a = R a
    · simp [h]
    · have hpoint (b : B) : |(if O a=b then M a else 0) - (if R a=b then M a else 0)| =
          (if O a=b then M a else 0) + (if R a=b then M a else 0) := by
        split_ifs <;> first | solve_by_elim [Eq.trans,Eq.symm] | simp [abs_of_nonneg (hn _)]
      simp_rw [hpoint]
      simp [Finset.sum_add_distrib,h,two_mul]
  have hs : ∑ b, |push O M b - push R M b| ≤
      ∑ b, ∑ a, |(if O a=b then M a else 0) - (if R a=b then M a else 0)| := by
    apply Finset.sum_le_sum; intro b _
    rw [push,push,← Finset.sum_sub_distrib]
    apply Finset.abs_sum_le_sum_abs
  rw [Finset.sum_comm,show (∑ a, ∑ b, |(if O a=b then M a else 0) - (if R a=b then M a else 0)|) = _
     from Finset.sum_congr rfl fun a _ => hb a,← Finset.mul_sum] at hs
  unfold sdist; linarith
theorem push_unif [DecidableEq A] [DecidableEq B] (f : A → B) (s : Finset A) (t : Finset B) (h : Set.BijOn f (↑s) (↑t)) :
    push f (unifOn s) = unifOn t := by
  classical
  have hcard : s.card = t.card := Finset.card_bij (fun a _ => f a) (fun a ha => h.mapsTo ha)
    (fun _ ha _ hb hf => h.injOn ha hb hf) (fun b hb => by obtain ⟨a,ha,he⟩ := h.surjOn hb; exact ⟨a,ha,he⟩)
  funext b
  by_cases hb : b ∈ t
  · obtain ⟨a,ha,hab⟩ := h.surjOn hb
    change a ∈ s at ha
    rw [push,Finset.sum_eq_single a]
    · simp [unifOn,hcard,hab,hb,ha]
    · intro k _ hka
      by_cases hk : k ∈ s
      · have hne : f k ≠ b := fun hf => hka (h.injOn hk ha (hf.trans hab.symm))
        simp [hne]
      · simp [unifOn,hk]
    · simp
  · rw [push,show unifOn t b = 0 by simp [unifOn,hb]]
    apply Finset.sum_eq_zero; intro a _
    by_cases ha : a ∈ s
    · have hne : f a ≠ b := fun hf => hb (hf ▸ h.mapsTo ha)
      simp [hne]
    · simp [unifOn,ha]
end
end CarryEstimate
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
open InfoLossLAR.WorstCase CarryEstimate
theorem solution (q d : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hdq : q ≤ d)
    (μ : (Fin d → ZMod q) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (ν : Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ) → ℝ) (hν0 : ∀ p, 0 ≤ ν p) (hν1 : HasSum ν 1)
    (hνinv : ∀ p, ν p ≠ 0 → IsUnit (matModq q p.1).det) :
    sdist
        (fun z => ∑' p, ν p * ∑ x, if modq q (p.1.mulVec (lift x) + p.2) = z then μ x else 0)
        (unifOn (Finset.univ.filter fun x : Fin d → ZMod q => fT63 q d x = 0)) ≤
      sdist
          (fun z => ∑' p, ν p *
            ∑ x, if modq q (incidenceLoad q d p.1 p.2 (lift x)) = z then μ x else 0)
          (unifOn (Finset.univ.filter fun w : Fin d → ZMod q => ∑ i, w i = 0)) +
        ∑' p, ν p * ∑ x, (open Classical in
          if carry q (incidenceLoad q d p.1 p.2 (lift x)) ∈ imageLattice (TDef63 q d)
          then 0 else μ x) ∧
    ∀ (Q : Matrix (Fin d) (Fin d) ℤ) (β : Fin d → ℤ) (x : Fin d → ZMod q),
      modq q (incidenceLoad q d Q β (lift x)) =
        modq q ((TDef63 q d).mulVec (lift (modq q (Q.mulVec (lift x) + β)))) ∧
      modq q (incidenceLoad q d Q β (lift x)) ∈ H0 q d ∧
      (modq q (Q.mulVec (lift x) + β) = cT q d (modq q (incidenceLoad q d Q β (lift x))) ↔
        carry q (incidenceLoad q d Q β (lift x)) ∈ imageLattice (TDef63 q d)) ∧
      (carry q (incidenceLoad q d Q β (lift x)) ∈ imageLattice (TDef63 q d) ↔
        (q : ℤ) ∣ ∑ j, carry q (incidenceLoad q d Q β (lift x)) j) := by
  classical
  let y := fun (p : Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) (x : Fin d → ZMod q) =>
    p.1.mulVec (lift x) + p.2
  let o := fun p x => modq q (y p x)
  let e := fun (p : Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) (x : Fin d → ZMod q) => modq q (incidenceLoad q d p.1 p.2 (lift x))
  let pair := fun p x => (o p x,e p x)
  let J := mix μ ν pair
  let c := cT q d
  let hset := Finset.univ.filter fun w : Fin d → ZMod q => ∑ i,w i = 0
  let fset := Finset.univ.filter fun z : Fin d → ZMod q => fT63 q d z = 0
  let E := Fin d → ZMod q
  have h0g (Q : Matrix (Fin d) (Fin d) ℤ) (β : Fin d → ℤ) (x : Fin d → ZMod q) :=
    geom hq2 hdq (Q.mulVec (lift x)+β)
  refine ⟨?_,h0g⟩
  have huni : push c (unifOn hset) = unifOn fset := by
    apply push_unif
    have hh : (↑hset : Set E) = H0 q d := by ext; simp [hset,H0,E]
    have hf : (↑fset : Set E) = zeroFiber63 q d := by ext; simp [fset,zeroFiber63,E]
    rw [hh,hf]
    exact (lemma_6_5 q d hq2 hdq).1
  have pm (g : E × E → E) := push_mix μ ν pair g hμ0 hμ1 hν0 hν1.summable
  have pe := push_mix μ ν e c hμ0 hμ1 hν0 hν1.summable
  have heq : push (fun a : E × E => c a.2) J = push c (mix μ ν e) := (pm _).trans pe.symm
  have hbad := mix_test μ ν pair (fun a : E × E => if a.1=c a.2 then (0:ℝ) else 1)
    hμ0 hμ1 hν0 hν1.summable
  simp only [ite_mul,zero_mul,one_mul] at hbad
  have hc := coupling (fun a : E × E => a.1) (fun a => c a.2) J (fun a => mix_nonneg μ ν pair a hμ0 hν0)
  rw [show push (fun a : E × E => a.1) J = mix μ ν o from pm _,heq] at hc
  have hpushed (f : (Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) → E → E) :
      (fun z => ∑' p, ν p * ∑ x, if f p x = z then μ x else 0) = mix μ ν f := by
    funext z
    apply tsum_congr; intro p
    congr 1
    apply Finset.sum_congr rfl; intro x _
    by_cases h : f p x = z <;> simp [h]
  rw [hpushed o,hpushed e]
  change sdist (mix μ ν o) (unifOn fset) ≤ sdist (mix μ ν e) (unifOn hset) + _
  calc
    _ ≤ sdist (mix μ ν o) (push c (mix μ ν e)) + sdist (push c (mix μ ν e)) (unifOn fset) :=
      triangle _ _ _
    _ ≤ (∑ a : E × E, if a.1 = c a.2 then 0 else J a) + sdist (mix μ ν e) (unifOn hset) := by
      apply add_le_add
      · refine hc.trans_eq ?_
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : a.1 = c a.2 <;> simp [h]
      · rw [← huni]
        exact map_sdist _ _ _
    _ = _ := by
      rw [add_comm]
      congr 1
      rw [show (∑ a : E × E, if a.1 = c a.2 then 0 else J a) = _ from hbad]
      apply tsum_congr; intro p
      congr 1
      apply Finset.sum_congr rfl; intro x _
      have hiff : (pair p x).1 = c (pair p x).2 ↔
          carry q (incidenceLoad q d p.1 p.2 (lift x)) ∈ imageLattice (TDef63 q d) :=
        (h0g p.1 p.2 x).2.2.1
      simp only [hiff]
end


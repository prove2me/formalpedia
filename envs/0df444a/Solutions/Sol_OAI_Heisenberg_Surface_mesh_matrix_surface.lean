-- Prove2me | solution 1 for OAI.Heisenberg.Surface.mesh_matrix_surface
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:34:07.699094+00:00
-- url     : https://prove2.me/submissions/758f190c-4310-433b-96ed-908aaa4ec192

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM000
import Definitions.Def_OAIW2HM001
import Theorems.Thm_OAI_Heisenberg_Bootstrap_periodic_return_estimate

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeDeterminants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.LayeredExchange
variable {T V : Type*}

lemma fibers_update [DecidableEq T] (σ : T → Equiv.Perm V) (t : T) (τ : Equiv.Perm V) :
    fibers (Function.update σ t (τ * σ t)) =
      fibers (Function.update (fun _ => 1) t τ) * fibers σ := by
  ext ⟨u,v⟩ <;> by_cases h : u = t <;> simp [fibers,Function.update,h]

lemma fibers_swap [DecidableEq T] [DecidableEq V] (t : T) (u v : V) :
    fibers (Function.update (fun _ : T => 1) t (Equiv.swap u v)) = Equiv.swap (t,u) (t,v) := by
  ext ⟨a,b⟩ <;> by_cases ht : a = t
  · subst a
    simp [fibers,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · simp [fibers,Function.update,ht,Equiv.swap_apply_def]
  · subst a
    simp [fibers,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · simp [fibers,Function.update,ht,Equiv.swap_apply_def]

end Heisenberg.LayeredExchange

namespace Heisenberg.Exposure
variable {A B : Type*} [Monoid A] [Monoid B]

lemma orderedProduct_map (f : A →* B) (n : ℕ) (x : Fin n → A) :
    f (orderedProduct n x) = orderedProduct n (fun i => f (x i)) := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => simp only [orderedProduct,map_mul,ih]

lemma orderedProduct_one (n : ℕ) (x : Fin n → A) (hx : ∀ i,x i=1) :
    orderedProduct n x = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orderedProduct,hx,ih _ fun _ => rfl]

lemma orderedProduct_single {n : ℕ} (x : Fin n → A) (i : Fin n)
    (hx : ∀ j,j ≠ i → x j=1) : orderedProduct n x = x i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [orderedProduct,orderedProduct_one _ _ (fun j => hx j.succ (Fin.succ_ne_zero j)),mul_one]
    | succ i =>
      rw [orderedProduct,hx 0 (Fin.succ_ne_zero i).symm,one_mul]
      exact ih _ i (fun j hj => hx j.succ (by simpa using hj))

end Heisenberg.Exposure
namespace Heisenberg.LayeredExchange

section
open Exposure
variable {T V : Type*}

lemma fibers_ordered_product (n : ℕ) (σ : Fin n → Equiv.Perm V) :
    fibers σ = orderedProduct n (fun i => fibers (Function.update (fun _ => 1) i (σ i))) := by
  change fibersHom σ = orderedProduct n
    (fun i => fibersHom (Function.update (fun _ => 1) i (σ i)))
  rw [← orderedProduct_map (fibersHom (T:=Fin n) (V:=V))]
  apply congrArg fibers
  funext i
  let eval : (Fin n → Equiv.Perm V) →* Equiv.Perm V :=
    { toFun := fun f => f i, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have he := orderedProduct_map eval n (fun j => Function.update (fun _ => 1) j (σ j))
  change σ i = eval (orderedProduct n (fun j => Function.update (fun _ => 1) j (σ j)))
  rw [he,orderedProduct_single _ i]
  · simp [eval]
  · intro j hj
    simp [eval,Function.update,Ne.symm hj]

end

open Exposure

end Heisenberg.LayeredExchange
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

open scoped Classical
namespace Heisenberg.Cycle

section
open Equiv
variable {V : Type*}

variable [Fintype V]

 theorem card_colorSpace (π : Perm V) (P : Set V) :
    Nat.card (colorSpace π P) = 2 ^ missingCount π P := by
  let := Fintype.ofFinite (MissingClasses π P)
  rw [Nat.card_congr (colorEquiv π P),Nat.card_fun]
  simp [missingCount]

lemma finrank_comparison {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (A B : Submodule K W) (f : W →ₗ[K] K)
    (h : ∀ x ∈ A, f x = 0 → x ∈ B) :
    Module.finrank K A ≤ Module.finrank K B + 1 := by
  let g : A →ₗ[K] K := f.comp A.subtype
  let k : LinearMap.ker g →ₗ[K] B :=
    { toFun := fun x => ⟨x.val.val,h x.val.val x.val.property x.property⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B => z.val) he
  have hd := k.finrank_le_finrank_of_injective hk
  have hr : Module.finrank K (LinearMap.range g) ≤ 1 := by
    simpa using (LinearMap.range g).finrank_le
  have ht := g.finrank_range_add_finrank_ker
  omega

 theorem missingCount_swap_le (π : Perm V) (P : Set V) (a b : V) :
    missingCount (π * swap a b) P ≤ missingCount π P + 1 := by
  let f : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun c => c a - c b
      map_add' := by intro x y; simp only [Pi.add_apply]; ring
      map_smul' := by intro r x; simp only [Pi.smul_apply, smul_sub, RingHom.id_apply] }
  have hr : Module.finrank (ZMod 2) (colorSpace (π * swap a b) P) ≤
      Module.finrank (ZMod 2) (colorSpace π P) + 1 := by
    apply finrank_comparison _ _ f
    intro c hc he
    have hab : c a = c b := sub_eq_zero.mp he
    refine ⟨?_,hc.2⟩
    intro i
    have ht := hc.1 (swap a b i)
    simpa only [Perm.mul_apply,swap_apply_self] using ht.trans (by
      by_cases hi : i = a
      · subst i; simpa using hab.symm
      by_cases hi' : i = b
      · subst i; simpa using hab
      rw [swap_apply_of_ne_of_ne hi hi'])
  have hc (σ : Perm V) : missingCount σ P = Module.finrank (ZMod 2) (colorSpace σ P) := by
    have h1 := card_colorSpace σ P
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := colorSpace σ P)
    have he : (2:ℕ) ^ missingCount σ P = 2 ^ Module.finrank (ZMod 2) (colorSpace σ P) := by
      rw [← h1]
      simpa using h2
    exact Nat.pow_right_injective (by decide : 1 < (2:ℕ)) he
  simpa only [hc] using hr

 theorem weight_swap_le (π : Perm V) (P : Set V) (a b : V) :
    (2:ℝ) ^ missingCount (π * swap a b) P ≤ 2 * (2:ℝ) ^ missingCount π P := by
  calc
    _ ≤ (2:ℝ) ^ (missingCount π P + 1) :=
      pow_le_pow_right₀ (by norm_num) (missingCount_swap_le π P a b)
    _ = _ := by rw [pow_succ]; ring

end

open Equiv

end Heisenberg.Cycle
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FiniteHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical

open scoped BigOperators Classical

open scoped Classical

namespace Heisenberg.LayeredExchange
variable {T V : Type*}
lemma wiring_update_swap [DecidableEq T] [DecidableEq V]
    (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) (u v : V) :
    wiring s (Function.update σ t (Equiv.swap u v * σ t)) =
      Equiv.swap (s t,u) (s t,v) * wiring s σ := by
  have hc : Equiv.prodCongr s (Equiv.refl V) * Equiv.swap (t,u) (t,v) =
      Equiv.swap (s t,u) (s t,v) * Equiv.prodCongr s (Equiv.refl V) := by
    apply Equiv.ext
    intro z
    change (s (Equiv.swap (t,u) (t,v) z).1, (Equiv.swap (t,u) (t,v) z).2) =
      Equiv.swap (s t,u) (s t,v) (s z.1,z.2)
    by_cases hu : z = (t,u)
    · subst z; simp
    by_cases hv : z = (t,v)
    · subst z; simp
    have hu' : (s z.1,z.2) ≠ (s t,u) := by
      intro he; apply hu; exact Prod.ext (s.injective (congrArg Prod.fst he)) (by simpa using congrArg (fun w : T × V => w.2) he)
    have hv' : (s z.1,z.2) ≠ (s t,v) := by
      intro he; apply hv; exact Prod.ext (s.injective (congrArg Prod.fst he)) (by simpa using congrArg (fun w : T × V => w.2) he)
    rw [Equiv.swap_apply_of_ne_of_ne hu hv,Equiv.swap_apply_of_ne_of_ne hu' hv']
  unfold wiring
  rw [fibers_update,fibers_swap,← mul_assoc,hc,mul_assoc]

end Heisenberg.LayeredExchange

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ReturnConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter

open scoped Classical
namespace Heisenberg.Return
open Equiv
variable {V : Type*}

lemma hitTime_zero (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x)
    (hx : x ∈ P) : hitTime π P x h = 0 := by
  exact Nat.eq_zero_of_le_zero (hitTime_le π P x h (n := 0) hx)

lemma hitTime_pos (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x)
    (hx : x ∉ P) : 0 < hitTime π P x h := by
  by_contra hn
  have he : hitTime π P x h = 0 := by omega
  have hm := hitPoint_mem π P x h
  exact hx (by simpa [hitPoint, he] using hm)

variable [Fintype V]

lemma hitTime_step (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x)
    (hx : x ∉ P) :
    hitTime π P x h = hitTime π P (π x) ((hasHit_apply π P x).mpr h) + 1 := by
  have hm := hitPoint_mem π P (π x) ((hasHit_apply π P x).mpr h)
  have hp := hitTime_pos π P x h hx
  apply Nat.le_antisymm
  · apply hitTime_le
    simpa only [hitPoint, pow_succ, Perm.mul_apply] using hm
  · have he : (π ^ (hitTime π P x h - 1)) (π x) ∈ P := by
      rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hp]
      exact hitPoint_mem π P x h
    have hl := hitTime_le π P (π x) ((hasHit_apply π P x).mpr h) he
    omega

omit [Fintype V] in
lemma firstValue_of_mem (π : Perm V) {P : Set V} {x : V} (hx : x ∈ P) :
    firstValue π P x = some x := by
  have h := hasHit_of_mem π hx
  simp [firstValue, h, hitPoint, hitTime_zero π P x h hx]

lemma firstValue_step (π : Perm V) (P : Set V) (x : V) (hx : x ∉ P) :
    firstValue π P (π x) = firstValue π P x := by
  by_cases h : HasHit π P x
  · have h' := (hasHit_apply π P x).mpr h
    simp only [firstValue, dite_eq_left h, dite_eq_left h']
    congr 1
    simp only [hitPoint, hitTime_step π P x h hx, pow_succ, Perm.mul_apply]
  · have h' : ¬ HasHit π P (π x) := by simpa only [hasHit_apply] using h
    simp [firstValue, h, h']

lemma harmonic_firstHit {W : Type*} (π : Perm V) (P : Set V) (g : V → W)
    (hg : ∀ x ∉ P, g (π x) = g x) (x : V) (h : HasHit π P x) :
    g (hitPoint π P x h) = g x := by
  have hn (n : ℕ) : ∀ x (h : HasHit π P x), hitTime π P x h = n →
      g (hitPoint π P x h) = g x := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x h he
      by_cases hx : x ∈ P
      · simp [hitPoint, hitTime_zero π P x h hx]
      · have ht := hitTime_step π P x h hx
        have hl : hitTime π P (π x) ((hasHit_apply π P x).mpr h) < n := by omega
        have hr := ih _ hl (π x) ((hasHit_apply π P x).mpr h) rfl
        rw [hitPoint, ht, pow_succ, Perm.mul_apply]
        exact hr.trans (hg x hx)
  exact hn _ x h rfl

lemma firstValue_unique {W : Type*} (π : Perm V) (P : Set V)
    (g : V → Option W) (b : V → W)
    (hb : ∀ x ∈ P, g x = some (b x))
    (hg : ∀ x ∉ P, g (π x) = g x)
    (x : V) (h : HasHit π P x) :
    g x = (firstValue π P x).map b := by
  rw [firstValue, dite_eq_left h]
  exact (harmonic_firstHit π P g hg x h).symm.trans
    (hb _ (hitPoint_mem π P x h))

lemma firstValue_splice_step (π : Perm (Option V)) (P : Set V) (i : V) :
    firstValue π (some '' P) (some (removeNone π i)) =
      firstValue π (some '' P) (π (some i)) := by
  cases h : π (some i) with
  | none =>
    rw [removeNone_none π h]
    exact firstValue_step π (some '' P) none (by simp)
  | some j =>
    rw [removeNone_some π ⟨j, h⟩, h]

lemma firstValue_spliced_harmonic (π : Perm (Option V)) (P : Set V) :
    ∀ i ∉ P, firstValue π (some '' P) (some (removeNone π i)) =
      firstValue π (some '' P) (some i) := by
  intro i hi
  rw [firstValue_splice_step]
  exact firstValue_step π _ _ (by simpa using hi)

theorem nextValue_splice (π : Perm (Option V)) (P : Set V) (i : V) (hi : i ∈ P) :
    firstValue π (some '' P) (π (some i)) =
      (firstValue (removeNone π) P (removeNone π i)).map some := by
  rw [← firstValue_splice_step]
  apply firstValue_unique (removeNone π) P
    (fun i => firstValue π (some '' P) (some i)) some
  · intro i hi
    exact firstValue_of_mem π ⟨i, hi, rfl⟩
  · exact firstValue_spliced_harmonic π P
  · exact (hasHit_apply (removeNone π) P i).mpr (hasHit_of_mem _ hi)

lemma nextValue_eq_nextPoint (π : Perm V) (P : Set V) (i : P) :
    firstValue π P (π i) = some (nextPoint π P i : V) := by
  rw [firstValue, dite_eq_left ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property))]
  rfl

end Heisenberg.Return

open scoped Classical
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExposedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

open scoped BigOperators Classical
namespace Heisenberg.Bernoulli
variable {I : Type*} [Fintype I]

omit [Fintype I] in
lemma join_update (i : I) (b b' : Bool) (d : {j // j ≠ i} → Bool) :
    Function.update (join i b d) i b' = join i b' d := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simpa only [Function.update_of_ne h] using (join_ne i b d ⟨j,h⟩).trans (join_ne i b' d ⟨j,h⟩).symm

lemma weight_join (p : I → ℝ) (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) :
    weight p (join i b d) = (if b then p i else 1-p i) * weight (fun j : {j // j ≠ i} => p j) d := by
  unfold weight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [join_at,join_ne]

lemma sum_split (p : I → ℝ) (F : (I → Bool) → ℝ) (i : I) :
    (∑ c, weight p c * F c) =
      ∑ d : {j // j ≠ i} → Bool, weight (fun j : {j // j ≠ i} => p j) d *
        ((1-p i)*F (join i false d) + p i*F (join i true d)) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp]
  change (∑ q : Bool × ({j // j ≠ i} → Bool), weight p (join i q.1 q.2) * F (join i q.1 q.2)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, weight_join, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

lemma scalar_bound {κ p W₀ W₁ : ℝ} (hκ : 1 ≤ κ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hW₁ : 0 ≤ W₁) (hW : W₁ ≤ κ*W₀) :
    W₁ ≤ κ*((1-p)*W₀+p*W₁) := by
  have h1 := mul_le_mul_of_nonneg_left hW (sub_nonneg.mpr hp1)
  have h2 := mul_le_mul_of_nonneg_left (show W₁ ≤ κ*W₁ by nlinarith) hp
  nlinarith

lemma weight_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (c : I → Bool) :
    0 ≤ weight p c := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [(hp i).1,(hp i).2]

lemma one_coin (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {κ : ℝ} (hκ : 1 ≤ κ)
    (W G : (I → Bool) → ℝ) (i : I)
    (hW : ∀ c, 0 ≤ W c) (hG : ∀ c, 0 ≤ G c)
    (hins : ∀ c, W (Function.update c i true) ≤ κ*W (Function.update c i false))
    (hGi : ∀ c, G (Function.update c i true) = G (Function.update c i false)) :
    (∑ c, weight p c * ((if c i then W c else 0)*G c)) ≤
      κ*p i * ∑ c, weight p c*(W c*G c) := by
  rw [sum_split, sum_split, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  have hi := hins (join i false d)
  have hg := hGi (join i false d)
  simp only [join_update] at hi hg
  simp only [join_at,Bool.false_eq_true,↓reduceIte,zero_mul,mul_zero,zero_add]
  rw [hg]
  have hb := scalar_bound hκ (hp i).1 (hp i).2 (hW _) hi
  have hn := mul_le_mul_of_nonneg_left hb (mul_nonneg (hp i).1 (hG (join i false d)))
  have hf := mul_le_mul_of_nonneg_left hn
    (weight_nonneg (fun j : {j // j ≠ i} => p j) (fun j => hp j) d)
  nlinarith

lemma test_nonneg (s : Finset I) (c : I → Bool) : 0 ≤ test s c := by
  unfold test; split_ifs <;> norm_num

lemma test_update {s : Finset I} {i : I} (hi : i ∉ s) (c : I → Bool) (b : Bool) :
    test s (Function.update c i b) = test s c := by
  unfold test
  congr 1
  apply propext
  constructor <;> intro h j hj
  · have hjn : j ≠ i := by intro he; subst j; exact hi hj
    simpa only [Function.update_of_ne hjn] using h j hj
  · rw [Function.update_of_ne (show j ≠ i by intro he; subst j; exact hi hj)]
    exact h j hj

lemma test_insert (s : Finset I) (i : I) (c : I → Bool) :
    test (insert i s) c = (if c i then 1 else 0)*test s c := by
  simp only [test,Finset.forall_mem_insert]
  split_ifs <;> simp_all

theorem factorial_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {κ : ℝ} (hκ : 1 ≤ κ)
    (W : (I → Bool) → ℝ) (hW : ∀ c, 0 ≤ W c)
    (hins : ∀ c i, W (Function.update c i true) ≤ κ*W (Function.update c i false))
    (s : Finset I) :
    (∑ c, weight p c*(W c*test s c)) ≤ (∏ i ∈ s, κ*p i) * ∑ c, weight p c*W c := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hc := one_coin p hp hκ W (test s) i hW (test_nonneg s)
      (fun c => hins c i) (fun c => by rw [test_update hi,test_update hi])
    have he : (∑ c, weight p c*(W c*test (insert i s) c)) =
        ∑ c, weight p c*((if c i then W c else 0)*test s c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [test_insert]
      cases c i <;> simp
    rw [he]
    exact hc.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih (mul_nonneg (by linarith) (hp i).1))

lemma test_eq_prod (s : Finset I) (c : I → Bool) :
    test s c = ∏ i ∈ s, if c i then (1:ℝ) else 0 := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih => rw [test_insert,Finset.prod_insert hi,ih]

lemma weight_test_sum (p : I → ℝ) (s : Finset I) :
    (∑ c,weight p c*test s c) = ∏ i ∈ s,p i := by
  have he (c : I → Bool) : weight p c*test s c =
      ∏ i, if c i then p i else if i ∈ s then 0 else 1-p i := by
    rw [test_eq_prod]
    have ht : (∏ i ∈ s, if c i then (1:ℝ) else 0) = ∏ i,if i ∈ s then (if c i then (1:ℝ) else 0) else 1 := by
      simp only [Finset.prod_ite_mem,Finset.univ_inter]
    rw [ht,weight,←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> cases c i <;> simp [hi]
  simp_rw [he]
  rw [←Fintype.prod_sum (fun i (b : Bool) => if b then p i else if i ∈ s then 0 else 1-p i)]
  simp only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
  have he : (fun i => p i + if i ∈ s then (0:ℝ) else 1-p i) = fun i => if i ∈ s then p i else 1 := by
    funext i
    split_ifs <;> ring
  rw [he]
  simp only [Finset.prod_ite_mem,Finset.univ_inter]

end Heisenberg.Bernoulli
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CycleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix
open Filter
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped BigOperators Classical

namespace Heisenberg.Cycle
open Equiv
variable {V : Type*} [Fintype V]

lemma weight_left_swap_le (π : Perm V) (P : Set V) (a b : V) :
    (2:ℝ)^missingCount (swap a b * π) P ≤ 2*(2:ℝ)^missingCount π P := by
  have he : swap a b * π = π * swap (π.symm a) (π.symm b) := by
    apply Equiv.ext
    intro x
    by_cases ha : x = π.symm a
    · subst x; simp
    by_cases hb : x = π.symm b
    · subst x; simp
    have ha' : π x ≠ a := fun h => ha (π.injective (h.trans (π.apply_symm_apply a).symm))
    have hb' : π x ≠ b := fun h => hb (π.injective (h.trans (π.apply_symm_apply b).symm))
    simp [Perm.mul_apply,swap_apply_of_ne_of_ne ha hb,swap_apply_of_ne_of_ne ha' hb']
  rw [he]
  exact weight_swap_le π P _ _
end Heisenberg.Cycle

namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Bernoulli
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype T] [Fintype V] in
lemma layerHistory_insert (s : Equiv.Perm T) (a b : T → V) (c : T → Bool) (t : T) :
    layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t true) =
      Equiv.swap (s t,a t) (s t,b t) *
        layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t false) := by
  let σ := fun j => if Function.update c t false j then Equiv.swap (a j) (b j) else 1
  have he : (fun j => if Function.update c t true j then Equiv.swap (a j) (b j) else 1) =
      Function.update σ t (Equiv.swap (a t) (b t)*σ t) := by
    funext j
    by_cases h : j=t
    · subst j
      simp [σ]
    · simp [Function.update_of_ne h,σ]
  change wiring s _ = _ * wiring s σ
  rw [he,wiring_update_swap]

omit [Fintype T] [Fintype V] in
lemma layerWeight_nonneg (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) :
    0 ≤ layerWeight s a b P c := by unfold layerWeight; positivity

omit [Fintype T] [Fintype V] in
lemma layerWeight_one_le (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) :
    1 ≤ layerWeight s a b P c := one_le_pow₀ (by norm_num)

lemma layerWeight_insertion (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (c : T → Bool) (t : T) :
    layerWeight s a b P (Function.update c t true) ≤
      2*layerWeight s a b P (Function.update c t false) := by
  unfold layerWeight
  have h := weight_left_swap_le (layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t false)) P (s t,a t) (s t,b t)
  convert h using 1
  congr 2
  exact (layerHistory_insert s a b c t).trans (by
    congr 1
    apply Equiv.ext
    intro x
    simp only [Equiv.swap_apply_def]
    split_ifs <;> rfl)

lemma coin_weight_sum (p : T → ℝ) : (∑ c,weight p c)=1 := by
  simpa [Bernoulli.test] using weight_test_sum p ∅

omit [Fintype V] in
lemma layerPartition_one_le (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) : 1≤layerPartition s a b P p := by
  rw [←coin_weight_sum p]
  exact Finset.sum_le_sum fun c _ => le_mul_of_one_le_right (weight_nonneg p hp c) (layerWeight_one_le s a b P c)

omit [Fintype V] in
lemma layerMass_nonneg (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (c : T → Bool) : 0≤layerMass s a b P p c := by
  exact div_nonneg (mul_nonneg (weight_nonneg p hp c) (layerWeight_nonneg s a b P c))
    (le_trans (by norm_num) (layerPartition_one_le s a b P p hp))

omit [Fintype V] in
lemma layerMass_sum (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) : (∑ c,layerMass s a b P p c)=1 := by
  simp only [layerMass,←Finset.sum_div]
  change layerPartition s a b P p / layerPartition s a b P p = 1
  exact div_self (ne_of_gt (lt_of_lt_of_le (by norm_num) (layerPartition_one_le s a b P p hp)))

theorem layer_factorial_bound (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (F : Finset T) :
    (∑ c,if ∀ i ∈ F,c i=true then layerMass s a b P p c else 0) ≤ ∏ i ∈ F,2*p i := by
  have hz : 0<layerPartition s a b P p :=
    lt_of_lt_of_le (by norm_num) (layerPartition_one_le s a b P p hp)
  have h := factorial_bound p hp (κ:=2) (by norm_num) (layerWeight s a b P)
    (layerWeight_nonneg s a b P) (layerWeight_insertion s a b P) F
  have he : (∑ c,if ∀ i ∈ F,c i=true then layerMass s a b P p c else 0) =
      (∑ c,weight p c*(layerWeight s a b P c*Bernoulli.test F c))/layerPartition s a b P p := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    unfold Bernoulli.test layerMass
    split_ifs <;> simp
  rw [he]
  exact (div_le_iff₀ hz).mpr h

end

open Heisenberg.MeshPair Heisenberg.Bernoulli

end Heisenberg.Exposure

open scoped Classical

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma card_boxFinset (d r : ℕ) : (boxFinset d r).card = (2 * r + 1) ^ d := by
  simp only [boxFinset, Fintype.card_piFinset, Int.card_Icc]
  have hc : ((r : ℤ) + 1 + (r : ℤ)).toNat = 2 * r + 1 := by omega
  simp [hc]

end Heisenberg.Geometry
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticeCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma ballFinset_card (d r : ℕ) (u : Site d) :
    (ballFinset d r u).card = (2 * r + 1) ^ d := by
  rw [ballFinset, Finset.card_image_of_injective _ (add_right_injective u), card_boxFinset]

end Heisenberg.Geometry

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_NetworkEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical

open scoped Classical
open Module
namespace Heisenberg.LatticeSum

lemma embed_injective (d : ℕ) : Function.Injective (embed (d := d)) := by
  intro x y h
  ext j
  have hj := congrFun (congrArg Subtype.val h) j
  change (x j : ℝ) = (y j : ℝ) at hj
  exact_mod_cast hj

lemma embed_norm_le {d : ℕ} (x : Site d) : ‖embed x‖ ≤ (radius x : ℝ) := by
  change ‖fun j => (x j : ℝ)‖ ≤ (radius x : ℝ)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hj : (x j).natAbs ≤ radius x := by
    exact Finset.le_sup (α := ℕ) (f := fun j => (x j).natAbs) (Finset.mem_univ j)
  simpa only [Real.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs] using
    (show ((x j).natAbs : ℝ) ≤ (radius x : ℝ) by exact_mod_cast hj)

lemma embed_ne_zero {d : ℕ} {x : Site d} (hx : x ≠ 0) : embed x ≠ 0 := by
  intro he
  apply hx
  apply embed_injective d
  convert he using 1
  apply Subtype.ext
  funext j
  simp [embed]

theorem summable_radius_rpow (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) :
    Summable (fun x : Site d => ((radius x : ℝ) + 1) ^ r) := by
  have hrank : Module.finrank ℤ (integerLattice d) = d := by
    rw [ZLattice.rank ℝ]
    simp
  have hs := ZLattice.summable_norm_rpow (integerLattice d) r (by simpa [hrank] using hr)
  have ht : Summable (fun x : Site d => ‖embed x‖ ^ r) :=
    hs.comp_injective (embed_injective d)
  apply Summable.of_norm_bounded_eventually ht
  apply Set.Finite.subset (Set.finite_singleton (0 : Site d))
  intro x hx
  by_contra hn
  have hpos : 0 < ‖embed x‖ := norm_pos_iff.mpr (embed_ne_zero hn)
  have hle : ‖((radius x : ℝ) + 1) ^ r‖ ≤ ‖embed x‖ ^ r := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos hpos (by linarith [embed_norm_le x]) (by linarith)
  exact hx hle

theorem summable_radius_sub_rpow (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) (y : Site d) :
    Summable (fun x : Site d => ((radius (x - y) : ℝ) + 1) ^ r) := by
  exact (Equiv.subRight y).summable_iff.mpr (summable_radius_rpow d r hr)

end Heisenberg.LatticeSum

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CyclicEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical RealInnerProductSpace

open Filter Topology
open scoped RealInnerProductSpace Classical

open scoped Classical
open Filter
namespace Heisenberg.Serial

section
open Matrix Heisenberg.MeshPair
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]

theorem mean_product (n : ℕ) (w : Fin n → B → ℝ)
    (K : Fin n → B → Matrix V V ℝ) :
    (∑ c : Fin n → B,(∏ i,w i (c i)) • product n (fun i => K i (c i))) =
      product n (fun i => ∑ b,w i b • K i b) := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [Fintype.sum_equiv (split n) _
      (fun c => (w 0 c.1*(∏ i,w i.succ (c.2 i))) •
        (product n (fun i => K i.succ (c.2 i))*K 0 c.1))]
    · simp only [Fintype.sum_prod_type,product]
      have he (b : B) (c : Fin n → B) :
          (w 0 b*(∏ i,w i.succ (c i))) •
            (product n (fun i => K i.succ (c i))*K 0 b) =
          ((∏ i,w i.succ (c i)) • product n (fun i => K i.succ (c i)))*(w 0 b • K 0 b) := by
        rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_comm]
      simp_rw [he,←Finset.sum_mul,ih,←Finset.mul_sum]
    · intro c
      rw [Fin.prod_univ_succ,product]
      rfl

end

open Matrix Heisenberg.Hitting

end Heisenberg.Serial

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpatialClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical BigOperators
namespace Heisenberg.SparseWitness

variable (V : Type*)
variable {V}

variable [PseudoMetricSpace V]

lemma leaves_disjoint (h : ℕ → ℝ) (hp : ∀ n, 0 < h (n+1))
    {n : ℕ} (t : Tree V (n+1)) (ht : Admissible h t) :
    Disjoint (leaves t.1) (leaves t.2) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hh := ht.2.2.2 a ha a hb
  simp only [dist_self] at hh
  linarith [hp n]

lemma card_leaves (h : ℕ → ℝ) (hp : ∀ n, 0 < h (n+1))
    {n : ℕ} (t : Tree V n) (ht : Admissible h t) : (leaves t).card = 2^n := by
  induction n with
  | zero =>
    change ({(show V from t)} : Finset V).card = 1
    exact Finset.card_singleton _
  | succ n ih =>
    rw [leaves,Finset.card_union_of_disjoint (leaves_disjoint h hp t ht),
      ih t.1 ht.1,ih t.2 ht.2.1,pow_succ]
    omega

lemma ball_meets_one_child (h : ℕ → ℝ) {n : ℕ} (t : Tree V (n+1))
    (ht : Admissible h t) (z : V) (r : ℝ) (hr : r < h (n+1)/8) :
    ((leaves t).filter (fun a => dist a z ≤ r)) =
      ((leaves t.1).filter (fun a => dist a z ≤ r)) ∨
    ((leaves t).filter (fun a => dist a z ≤ r)) =
      ((leaves t.2).filter (fun a => dist a z ≤ r)) := by
  let L := (leaves t.1).filter (fun a => dist a z ≤ r)
  let R := (leaves t.2).filter (fun a => dist a z ≤ r)
  rw [leaves,Finset.filter_union]
  change L ∪ R = L ∨ L ∪ R = R
  by_cases hL : L = ∅
  · exact Or.inr (by rw [hL,Finset.empty_union])
  · left
    have hR : R = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hL
      obtain ⟨ha,har⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb,hbr⟩ := Finset.mem_filter.mp hb
      have hs := ht.2.2.2 a ha b hb
      have hd := dist_triangle_right a b z
      linarith
    rw [hR,Finset.union_empty]

theorem admissible_sparse (h : ℕ → ℝ) (hp : ∀ n, 0 < h (n+1))
    (α : ℝ) (hα : 0 ≤ α)
    (hg : ∀ n, (2:ℝ)^(n+1) ≤ (1+h (n+1)/8)^α)
    {n : ℕ} (t : Tree V n) (ht : Admissible h t) : Sparse α 1 (leaves t) := by
  intro z r hr
  simp only [one_mul]
  induction n with
  | zero =>
    have hc : ((leaves t).filter (fun a => dist a z ≤ r)).card ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (le_of_eq (card_leaves h hp t ht))
    calc
      _ ≤ (1:ℝ) := by exact_mod_cast hc
      _ ≤ (1+r)^α := Real.one_le_rpow (by linarith) hα
  | succ n ih =>
    by_cases hh : r < h (n+1)/8
    · rcases ball_meets_one_child h t ht z r hh with he | he
      · rw [he]; exact ih t.1 ht.1
      · rw [he]; exact ih t.2 ht.2.1
    · calc
        _ ≤ ((leaves t).card:ℝ) := by
          exact_mod_cast (Finset.card_filter_le (leaves t) (fun a => dist a z ≤ r))
        _ = (2:ℝ)^(n+1) := by rw [card_leaves h hp t ht]; norm_cast
        _ ≤ (1+h (n+1)/8)^α := hg n
        _ ≤ (1+r)^α := Real.rpow_le_rpow (by linarith [hp n]) (by linarith) hα

lemma geometric_scale_growth (b α : ℝ) (hb : 1 ≤ b) (hα : 0 ≤ α)
    (hba : 2 ≤ b^α) (n : ℕ) :
    (2:ℝ)^(n+1) ≤ (1+(16*b^(n+1))/8)^α := by
  calc
    _ ≤ (b^α)^(n+1) := pow_le_pow_left₀ (by positivity) hba _
    _ = (b^(n+1))^α := by rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith),
      mul_comm,Real.rpow_mul (by linarith),Real.rpow_natCast]
    _ ≤ (1+(16*b^(n+1))/8)^α := by
      apply Real.rpow_le_rpow (by positivity) _ hα
      have : 0 ≤ b^(n+1) := by positivity
      linarith

end Heisenberg.SparseWitness

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SparseCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical BigOperators

namespace Heisenberg.SparseWitness

section
variable {V : Type*} [PseudoMetricSpace V]

lemma first_crossing (p : ℕ → V) (m : ℕ) (hstep : ∀ i < m, dist (p i) (p (i+1)) ≤ 8)
    (r : ℝ) (hr : 0 < r) (hend : r ≤ dist (p 0) (p m)) :
    ∃ k ≤ m, r ≤ dist (p 0) (p k) ∧ dist (p 0) (p k) ≤ r+8 := by
  have hex : ∃ k : ℕ, k ≤ m ∧ r ≤ dist (p 0) (p k) := ⟨m,le_rfl,hend⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  change k ≤ m ∧ r ≤ dist (p 0) (p k) at hk
  have hk0 : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    rw [he,dist_self] at hk
    linarith
  have hpre : dist (p 0) (p (k-1)) < r := by
    by_contra hn
    have hmin := Nat.find_min' hex (show k-1 ≤ m ∧ r ≤ dist (p 0) (p (k-1)) from
      ⟨by omega,by linarith⟩)
    change k ≤ k-1 at hmin
    omega
  refine ⟨k,hk.1,hk.2,?_⟩
  have hs := hstep (k-1) (by omega)
  have he : k-1+1 = k := by omega
  rw [he] at hs
  have ht := dist_triangle (p 0) (p (k-1)) (p k)
  linarith

theorem crossing_witness (h : ℕ → ℝ) (hp : ∀ n, 0 < h n)
    (hg : ∀ n, 8*h n+64 ≤ h (n+1)) (n : ℕ)
    (p : ℕ → V) (m : ℕ) (hstep : ∀ i < m, dist (p i) (p (i+1)) ≤ 8)
    (hend : h n ≤ dist (p 0) (p m)) :
    ∃ t : Tree V n, Admissible h t ∧ root t = p 0 ∧
      (∀ a ∈ leaves t, ∃ i ≤ m, p i = a) ∧
      (∀ a ∈ leaves t, dist (p 0) a ≤ h n+8) := by
  induction n generalizing p m with
  | zero =>
    refine ⟨p 0,True.intro,rfl,?_,?_⟩
    · intro a ha
      change a ∈ ({p 0} : Finset V) at ha
      have he := Finset.mem_singleton.mp ha
      exact ⟨0,Nat.zero_le _,he.symm⟩
    · intro a ha
      change a ∈ ({p 0} : Finset V) at ha
      rw [Finset.mem_singleton.mp ha,dist_self]
      linarith [hp 0]
  | succ n ih =>
    obtain ⟨k,hkm,hklo,hkhi⟩ := first_crossing p m hstep (h (n+1)/2)
      (by linarith [hp (n+1)]) (by linarith [hp (n+1)])
    obtain ⟨l,hl,hlroot,hlpath,hlball⟩ := ih p m hstep (by linarith [hg n,hp n])
    let q : ℕ → V := fun j => p (j+k)
    have hqstep : ∀ j < m-k, dist (q j) (q (j+1)) ≤ 8 := by
      intro j hj
      simpa [q,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hstep (j+k) (by omega)
    have hqend : h n ≤ dist (q 0) (q (m-k)) := by
      have he : m-k+k = m := by omega
      simp only [q,zero_add,he]
      have htri := dist_triangle (p 0) (p k) (p m)
      linarith [hg n,hp n]
    obtain ⟨r,hr,hrroot,hrpath,hrball⟩ := ih q (m-k) hqstep hqend
    have hrroot' : root r = p k := by simpa [q] using hrroot
    have hsep : ∀ a ∈ leaves l, ∀ b ∈ leaves r, h (n+1)/4 ≤ dist a b := by
      intro a ha b hb
      have hla := hlball a ha
      have hrb := hrball b hb
      simp only [q,zero_add] at hrb
      have ht₁ := dist_triangle (p 0) a (p k)
      have ht₂ := dist_triangle a b (p k)
      rw [dist_comm b (p k)] at ht₂
      linarith [hg n]
    refine ⟨(l,r),⟨hl,hr,?_,hsep⟩,hlroot,?_,?_⟩
    · rw [hlroot,hrroot']
      linarith [hp (n+1)]
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hlpath a ha
      · obtain ⟨j,hj,hja⟩ := hrpath a ha
        exact ⟨j+k,by omega,hja⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · have hh := hlball a ha
        linarith [hg n,hp n]
      · have hh := hrball a ha
        simp only [q,zero_add] at hh
        have htri := dist_triangle (p 0) (p k) a
        linarith [hg n,hp n]

lemma geometric_scale_gap (b : ℝ) (hb : 100 ≤ b) (n : ℕ) :
    8*(16*b^n)+64 ≤ 16*b^(n+1) := by
  rw [pow_succ]
  have hn : 1 ≤ b^n := one_le_pow₀ (by linarith)
  nlinarith

end

section
variable {V : Type*}

variable [PseudoMetricSpace V]
lemma admissible_mem_candidates (h : ℕ → ℝ) (B : ℕ → V → Finset V)
    (hB : ∀ n z y, dist z y ≤ h (n+1)+8 → y ∈ B (n+1) z)
    {n : ℕ} (t : Tree V n) (ht : Admissible h t) : t ∈ candidates B n (root t) := by
  induction n with
  | zero => exact Finset.mem_singleton_self _
  | succ n ih =>
    apply Finset.mem_biUnion.mpr
    refine ⟨root t.2,hB n (root t.1) (root t.2) ht.2.2.1,?_⟩
    exact Finset.mem_product.mpr ⟨ih t.1 ht.1,ih t.2 ht.2.1⟩

omit [PseudoMetricSpace V] in
lemma card_candidates_le (B : ℕ → V → Finset V) (M A : ℕ → ℕ)
    (hB : ∀ n z, (B (n+1) z).card ≤ M (n+1)) (hA0 : 1 ≤ A 0)
    (hA : ∀ n, M (n+1)*A n^2 ≤ A (n+1)) (n : ℕ) (z : V) :
    (candidates B n z).card ≤ A n := by
  induction n generalizing z with
  | zero =>
    change ({(show V from z)} : Finset V).card ≤ _
    simpa only [Finset.card_singleton] using hA0
  | succ n ih =>
    simp only [candidates]
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _y ∈ B (n+1) z, A n^2 := by
        apply Finset.sum_le_sum
        intro y _
        exact (Finset.card_product (candidates B n z) (candidates B n y)).le.trans
          (by simpa only [pow_two] using Nat.mul_le_mul (ih z) (ih y))
      _ ≤ M (n+1)*A n^2 := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (hB n z)
      _ ≤ A (n+1) := hA n

lemma assignmentBound_formula (a c n : ℕ) :
    assignmentBound a c n * a*c^(n+2) = (a*c^2)^(2^n) := by
  induction n with
  | zero => simp [assignmentBound]
  | succ n ih =>
    calc
      _ = (assignmentBound a c n*a*c^(n+2))^2 := by
        simp only [assignmentBound,pow_succ]
        ring
      _ = ((a*c^2)^(2^n))^2 := by rw [ih]
      _ = (a*c^2)^(2^(n+1)) := by rw [← pow_mul,pow_succ 2 n]

lemma assignmentBound_le (a c : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (n : ℕ) :
    assignmentBound a c n ≤ (a*c^2)^(2^n) := by
  rw [← assignmentBound_formula]
  have hp : 1 ≤ c^(n+2) := one_le_pow₀ hc
  calc
    _ ≤ assignmentBound a c n*a := by simpa using Nat.mul_le_mul_left (assignmentBound a c n) ha
    _ ≤ assignmentBound a c n*a*c^(n+2) := by
      simpa using Nat.mul_le_mul_left (assignmentBound a c n*a) hp

omit [PseudoMetricSpace V] in

theorem geometric_candidates_count (B : ℕ → V → Finset V) (a c : ℕ)
    (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hB : ∀ n z, (B (n+1) z).card ≤ a*c^(n+1)) (n : ℕ) (z : V) :
    (candidates B n z).card ≤ (a*c^2)^(2^n) := by
  apply (card_candidates_le B (fun j => a*c^j) (assignmentBound a c) hB
    le_rfl (fun _ => le_rfl) n z).trans
  exact assignmentBound_le a c ha hc n

end

variable {V Ω : Type*} [PseudoMetricSpace V] [Fintype Ω]

lemma Sparse.mono_constant {α L L' : ℝ} {F : Finset V}
    (hF : Sparse α L F) (hL : L ≤ L') : Sparse α L' F := by
  intro z r hr
  exact (hF z r hr).trans (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (by linarith) _))

lemma finite_union_mass {W : Type*} (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (F : Finset W) (E : W → Ω → Prop) (A : Ω → Prop)
    (hA : ∀ ω, A ω → ∃ t ∈ F, E t ω) :
    (∑ ω, if A ω then μ ω else 0) ≤ ∑ t ∈ F, ∑ ω, if E t ω then μ ω else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · rw [ite_eq_left ha]
    obtain ⟨t,ht,he⟩ := hA ω ha
    have h := Finset.single_le_sum (f:=fun t => if E t ω then μ ω else 0)
      (fun i _ => by split_ifs <;> simp [hμ]) ht
    simpa only [ite_eq_left he] using h
  · rw [ite_eq_right ha]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hμ])

theorem crossing_mass_bound (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (Z : Ω → Set V)
    (h : ℕ → ℝ) (hp : ∀ n, 0 < h n) (hg : ∀ n, 8*h n+64 ≤ h (n+1))
    (α L : ℝ) (hα : 0 ≤ α) (hL : 1 ≤ L)
    (hscale : ∀ n, (2:ℝ)^(n+1) ≤ (1+h (n+1)/8)^α)
    (B : ℕ → V → Finset V)
    (hB : ∀ n z y, dist z y ≤ h (n+1)+8 → y ∈ B (n+1) z)
    (a c : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hcard : ∀ n z, (B (n+1) z).card ≤ a*c^(n+1))
    (q : ℝ) (hq : 0 ≤ q)
    (htest : ∀ F : Finset V, Sparse α L F →
      (∑ ω, if (F:Set V) ⊆ Z ω then μ ω else 0) ≤ q^F.card)
    (n : ℕ) (z : V) :
    (∑ ω, if Crosses (Z ω) z (h n) then μ ω else 0) ≤
      ((a*c^2:ℕ)*q)^(2^n) := by
  let F := (candidates B n z).filter (Admissible h)
  have hcover : ∀ ω, Crosses (Z ω) z (h n) →
      ∃ t ∈ F, (leaves t : Set V) ⊆ Z ω := by
    intro ω hω
    obtain ⟨p,m,hp0,hpz,hps,hpe⟩ := hω
    obtain ⟨t,ht,htroot,htpath,_⟩ := crossing_witness h hp hg n p m hps hpe
    refine ⟨t,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨?_,ht⟩
      rw [← hp0,← htroot]
      exact admissible_mem_candidates h B hB t ht
    · intro v hv
      obtain ⟨i,hi,rfl⟩ := htpath v hv
      exact hpz i hi
  calc
    _ ≤ ∑ t ∈ F, ∑ ω, if (leaves t:Set V) ⊆ Z ω then μ ω else 0 :=
      finite_union_mass μ hμ F _ _ hcover
    _ ≤ ∑ _t ∈ F, q^(2^n) := by
      apply Finset.sum_le_sum
      intro t ht
      have had := (Finset.mem_filter.mp ht).2
      have hsp := (admissible_sparse h (fun i => hp (i+1)) α hα hscale t had).mono_constant hL
      simpa only [card_leaves h (fun i => hp (i+1)) t had] using htest (leaves t) hsp
    _ = (F.card:ℝ)*q^(2^n) := by simp
    _ ≤ ((a*c^2:ℕ):ℝ)^(2^n)*q^(2^n) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq _)
      exact_mod_cast ((Finset.card_filter_le _ _).trans (geometric_candidates_count B a c ha hc hcard n z))
    _ = _ := (mul_pow ..).symm

end Heisenberg.SparseWitness

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CrossingTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical BigOperators

namespace Heisenberg.Geometry
lemma scaled_ball_card (d b n : ℕ) (hb : 1 ≤ b) (z : Site d) :
    (ballFinset d (16*b^n+8) z).card ≤ 49^d*(b^d)^n := by
  rw [ballFinset_card]
  have hp : 1 ≤ b^n := one_le_pow₀ hb
  have h : 2*(16*b^n+8)+1 ≤ 49*b^n := by omega
  calc
    _ ≤ (49*b^n)^d := Nat.pow_le_pow_left h _
    _ = _ := by rw [mul_pow]; congr 1; rw [←pow_mul,←pow_mul,Nat.mul_comm]

theorem lattice_crossing_mass_bound {Ω : Type*} [Fintype Ω]
    (d b : ℕ) (hb : 100 ≤ b) (α L : ℝ) (hα : 0 ≤ α) (hL : 1 ≤ L)
    (hba : 2 ≤ (b:ℝ)^α)
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (Z : Ω → Set (Site d))
    (q : ℝ) (hq : 0 ≤ q)
    (htest : ∀ F : Finset (Site d), SparseWitness.Sparse α L F →
      (∑ ω, if (F:Set (Site d)) ⊆ Z ω then μ ω else 0) ≤ q^F.card)
    (n : ℕ) (z : Site d) :
    (∑ ω, if SparseWitness.Crosses (Z ω) z (16*(b:ℝ)^n) then μ ω else 0) ≤
      (((49^d*(b^d)^2:ℕ):ℝ)*q)^(2^n) := by
  have hb1 : 1 ≤ b := by omega
  have hbR : 1 ≤ (b:ℝ) := by exact_mod_cast hb1
  apply SparseWitness.crossing_mass_bound μ hμ Z (fun j => 16*(b:ℝ)^j)
    (fun j => by positivity) (fun j => SparseWitness.geometric_scale_gap _ (by exact_mod_cast hb) j)
    α L hα hL (SparseWitness.geometric_scale_growth _ _ hbR hα hba)
    (fun j z => ballFinset d (16*b^j+8) z) _ (49^d) (b^d)
    (one_le_pow₀ (by omega)) (one_le_pow₀ hb1) _ q hq htest
  · intro j x y hxy
    apply (mem_ballFinset ..).mpr
    apply (dist_le_iff_mem_ball x y).mp
    norm_cast at hxy ⊢
  · intro j x
    exact scaled_ball_card d b (j+1) hb1 x

end Heisenberg.Geometry

namespace Heisenberg.SparseWitness
variable {V Ω : Type*} [PseudoMetricSpace V] [Fintype Ω]

lemma Crosses.mono_radius {Z : Set V} {z : V} {r s : ℝ} (h : Crosses Z z r)
    (hs : s ≤ r) : Crosses Z z s := by
  obtain ⟨p,m,hp,hz,hstep,hr⟩ := h
  exact ⟨p,m,hp,hz,hstep,hs.trans hr⟩

lemma event_mass_mono (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) :
    (∑ ω, if A ω then μ ω else 0) ≤ ∑ ω, if B ω then μ ω else 0 := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · rw [ite_eq_left ha,ite_eq_left (hAB ω ha)]
  · rw [ite_eq_right ha]
    split_ifs <;> simp [hμ]

theorem stretched_tail_of_scales (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (hprob : ∑ ω, μ ω ≤ 1) (Z : Ω → Set V) (b γ : ℝ)
    (hb : 1 < b) (hγ : 0 < γ) (hbγ : b^γ = 2)
    (htail : ∀ n z, (∑ ω, if Crosses (Z ω) z (16*b^n) then μ ω else 0) ≤
      Real.exp (-2*(2:ℝ)^n)) (z : V) (r : ℝ) (hr : 0 ≤ r) :
    (∑ ω, if Crosses (Z ω) z r then μ ω else 0) ≤
      Real.exp 1 * Real.exp (-((r/(16*b))^γ)) := by
  by_cases hrs : r < 16
  · have hbase : r/(16*b) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
    have hpow : (r/(16*b))^γ ≤ 1 := Real.rpow_le_one (by positivity) hbase hγ.le
    calc
      _ ≤ ∑ ω, μ ω := Finset.sum_le_sum (fun ω _ => by split_ifs <;> simp [hμ])
      _ ≤ 1 := hprob
      _ ≤ Real.exp 1*Real.exp (-((r/(16*b))^γ)) := by
        rw [←Real.exp_add]
        exact Real.one_le_exp (by linarith)
  · obtain ⟨n,hnl,hnr⟩ := exists_nat_pow_near (x:=r/16) (by linarith) hb
    have hnr' : r/(16*b) ≤ b^n := by
      apply (div_le_iff₀ (by positivity)).mpr
      rw [pow_succ] at hnr
      nlinarith
    have hp : (r/(16*b))^γ ≤ (2:ℝ)^n := by
      calc
        _ ≤ (b^n)^γ := Real.rpow_le_rpow (by positivity) hnr' hγ.le
        _ = (b^γ)^n := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith),mul_comm,
            Real.rpow_mul (by linarith),Real.rpow_natCast]
        _ = _ := by rw [hbγ]
    calc
      _ ≤ ∑ ω, if Crosses (Z ω) z (16*b^n) then μ ω else 0 :=
        event_mass_mono μ hμ (fun _ h => h.mono_radius (by linarith))
      _ ≤ Real.exp (-2*(2:ℝ)^n) := htail n z
      _ ≤ Real.exp (-((r/(16*b))^γ)) := Real.exp_le_exp.mpr (by nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n])
      _ ≤ Real.exp 1 * Real.exp (-((r/(16*b))^γ)) := by
        simpa using mul_le_mul_of_nonneg_right (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1))
          (Real.exp_nonneg (-((r/(16*b))^γ)))

lemma exists_scale_exponent {b : ℝ} (hb : 1 < b) :
    ∃ γ : ℝ, 0 < γ ∧ b^γ = 2 := by
  refine ⟨Real.log 2/Real.log b,div_pos (Real.log_pos (by norm_num)) (Real.log_pos hb),?_⟩
  rw [Real.rpow_def_of_pos (by linarith)]
  have hlog : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb)
  rw [mul_div_cancel₀ _ hlog,Real.exp_log (by norm_num : (0:ℝ) < 2)]

lemma sparse_of_card_le {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L) (F : Finset V)
    (hF : (F.card:ℝ) ≤ L) : Sparse α L F := by
  intro z r hr
  calc
    _ ≤ (F.card:ℝ) := by exact_mod_cast Finset.card_filter_le F _
    _ ≤ L := hF
    _ ≤ L*(1+r)^α := by
      simpa using mul_le_mul_of_nonneg_left (Real.one_le_rpow (by linarith) hα) hL

lemma countable_union_mass {W : Type*} (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (E : W → Ω → Prop) (A : Ω → Prop) (g : W → ℝ)
    (hg : ∀ w, 0 ≤ g w) (hs : Summable g)
    (hE : ∀ w, (∑ ω, if E w ω then μ ω else 0) ≤ g w)
    (hA : ∀ ω, A ω → ∃ w, E w ω) :
    (∑ ω, if A ω then μ ω else 0) ≤ ∑' w, g w := by
  let S := Finset.univ.filter A
  let pick (ω : S) : W := Classical.choose (hA ω (Finset.mem_filter.mp ω.property).2)
  let F : Finset W := S.attach.image pick
  have hcover : ∀ ω, A ω → ∃ w ∈ F, E w ω := by
    intro ω hω
    let a : S := ⟨ω,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hω⟩⟩
    refine ⟨pick a, Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩,?_⟩
    exact Classical.choose_spec (hA ω hω)
  calc
    _ ≤ ∑ w ∈ F, ∑ ω, if E w ω then μ ω else 0 := finite_union_mass μ hμ F E A hcover
    _ ≤ ∑ w ∈ F, g w := Finset.sum_le_sum (fun w _ => hE w)
    _ ≤ ∑' w, g w := hs.sum_le_tsum F (fun w _ => hg w)

theorem bad_count_mass (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (Z : Ω → Set V)
    (α L p : ℝ) (hα : 0 ≤ α) (hL : 0 ≤ L) (k : ℕ) (hk : (k:ℝ) ≤ L)
    (htest : ∀ F : Finset V, Sparse α L F →
      (∑ ω, if (F:Set V) ⊆ Z ω then μ ω else 0) ≤ p^F.card)
    (B : Finset V) :
    (∑ ω, if k ≤ (B.filter (· ∈ Z ω)).card then μ ω else 0) ≤
      (B.card.choose k:ℝ)*p^k := by
  have hcover : ∀ ω, k ≤ (B.filter (· ∈ Z ω)).card →
      ∃ F ∈ B.powersetCard k, (F:Set V) ⊆ Z ω := by
    intro ω hω
    obtain ⟨F,hF,hcard⟩ := Finset.exists_subset_card_eq hω
    refine ⟨F,Finset.mem_powersetCard.mpr ⟨hF.trans (Finset.filter_subset ..),hcard⟩,?_⟩
    intro v hv
    exact (Finset.mem_filter.mp (hF hv)).2
  calc
    _ ≤ ∑ F ∈ B.powersetCard k, ∑ ω, if (F:Set V) ⊆ Z ω then μ ω else 0 :=
      by
        convert finite_union_mass μ hμ (B.powersetCard k) (fun F ω => (F:Set V) ⊆ Z ω) (fun ω => k ≤ (B.filter (· ∈ Z ω)).card) hcover using 1
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> rfl
    _ ≤ ∑ _F ∈ B.powersetCard k, p^k := by
      apply Finset.sum_le_sum
      intro F hF
      have hc := (Finset.mem_powersetCard.mp hF).2
      simpa only [hc] using htest F (sparse_of_card_le hα hL F (by simpa only [hc] using hk))
    _ = _ := by simp

end Heisenberg.SparseWitness

open scoped Classical
open Module

open scoped BigOperators
namespace Heisenberg.Stretched

lemma exp_power_bound (c ξ t : ℝ) (hc : 0 < c) (ht : 0 < t) (n : ℕ) :
    Real.exp (-c*t^ξ) ≤ (n.factorial:ℝ)/c^n * t^(-ξ*(n:ℝ)) := by
  have hct : 0 < c*t^ξ := mul_pos hc (Real.rpow_pos_of_pos ht ξ)
  have hf : 0 < (n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hh := Real.pow_div_factorial_le_exp (c*t^ξ) hct.le n
  have hi := (one_div_le_one_div_of_le (div_pos (pow_pos hct n) hf) hh)
  have he : (1:ℝ) / ((c*t^ξ)^n/(n.factorial:ℝ)) =
      (n.factorial:ℝ)/c^n * t^(-ξ*(n:ℝ)) := by
    rw [mul_pow]
    rw [← Real.rpow_natCast (t^ξ) n, ← Real.rpow_mul ht.le]
    rw [neg_mul,Real.rpow_neg ht.le]
    field_simp
  rw [he] at hi
  simpa only [one_div,←Real.exp_neg,neg_mul] using hi

theorem exists_polynomial_envelope (c ξ r : ℝ) (hc : 0 < c) (hξ : 0 < ξ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → Real.exp (-c*t^ξ) ≤ C*t^(-r) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (r/ξ)
  have hnr : r ≤ ξ*(n:ℝ) := by
    have := (div_lt_iff₀ hξ).mp hn
    nlinarith
  refine ⟨(n.factorial:ℝ)/c^n,div_pos (by exact_mod_cast Nat.factorial_pos n) (pow_pos hc n),?_⟩
  intro t ht
  exact (exp_power_bound c ξ t hc (by linarith) n).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) (by positivity))

end Heisenberg.Stretched

namespace Heisenberg.LatticeSum
open Heisenberg.Geometry

lemma radius_eq_norm {k : ℕ} (x : Site (k+1)) : (radius x : ℝ) = ‖x‖ := by
  apply le_antisymm
  · obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup Finset.univ (Finset.univ_nonempty) (fun j : Fin (k+1) => (x j).natAbs)
    change ((Finset.univ.sup (fun j => (x j).natAbs) : ℕ) : ℝ) ≤ ‖x‖
    rw [he]
    simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using norm_le_pi_norm x j
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    have h : (x j).natAbs ≤ radius x := Finset.le_sup (f:=fun j => (x j).natAbs) (Finset.mem_univ j)
    simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using (show ((x j).natAbs : ℝ) ≤ (radius x : ℝ) by exact_mod_cast h)

lemma uniform_polynomial_sum (k : ℕ) (r : ℝ) (hr : r < -(k+1:ℝ)) :
    ∃ M ≥ 0, ∀ y : Site (k+1), Summable (fun x => (1+dist x y)^r) ∧
      (∑' x, (1+dist x y)^r) = M := by
  let M := ∑' x : Site (k+1), ((radius x:ℝ)+1)^r
  refine ⟨M,tsum_nonneg (fun x => Real.rpow_nonneg (by positivity) _),?_⟩
  intro y
  have hs := summable_radius_sub_rpow (k+1) r (by push_cast; exact hr) y
  have he := (Equiv.subRight y).tsum_eq (fun x : Site (k+1) => ((radius x:ℝ)+1)^r)
  refine ⟨?_,?_⟩
  · simpa only [radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using hs
  · simpa only [M,Equiv.subRight_apply,radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using he

theorem exp_tail_polynomial (k : ℕ) (c ξ a : ℝ) (hc : 0 < c) (hξ : 0 < ξ)
    (ha : 0 ≤ a) :
    ∃ C ≥ 0, ∀ (y : Site (k+1)) (R : ℝ), 0 ≤ R →
      Summable (fun x => if R < dist x y then Real.exp (-c*(1+dist x y)^ξ) else 0) ∧
      (∑' x, if R < dist x y then Real.exp (-c*(1+dist x y)^ξ) else 0) ≤ C*(1+R)^(-a) := by
  obtain ⟨D,hD,hpoly⟩ := Heisenberg.Stretched.exists_polynomial_envelope c ξ (a+(k+2:ℝ)) hc hξ
  obtain ⟨M,hM,hMsum⟩ := uniform_polynomial_sum k (-(k+2:ℝ)) (by linarith)
  refine ⟨D*M,mul_nonneg hD.le hM,?_⟩
  intro y R hR
  let F : Site (k+1) → ℝ := fun x => if R < dist x y then Real.exp (-c*(1+dist x y)^ξ) else 0
  let G : Site (k+1) → ℝ := fun x => (D*(1+R)^(-a))*(1+dist x y)^(-(k+2:ℝ))
  have hsG : Summable G := (hMsum y).1.mul_left _
  have hFG : ∀ x, F x ≤ G x := by
    intro x
    dsimp [F,G]
    split_ifs with hx
    · have hp := hpoly (1+dist x y) (by linarith [dist_nonneg (x:=x) (y:=y)])
      have hdec : (1+dist x y)^(-a) ≤ (1+R)^(-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have he : (1+dist x y)^(-(a+(k+2:ℝ))) =
          (1+dist x y)^(-a)*(1+dist x y)^(-(k+2:ℝ)) := by
        rw [←Real.rpow_add (by positivity)]
        congr 1
        ring
      rw [he] at hp
      exact hp.trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdec (by positivity)) hD.le)
    · positivity
  have hsF : Summable F := Summable.of_nonneg_of_le (fun x => by dsimp [F]; split_ifs <;> positivity) hFG hsG
  refine ⟨hsF,?_⟩
  calc
    (∑' x, F x) ≤ ∑' x, G x := hsF.tsum_le_tsum hFG hsG
    _ = D*(1+R)^(-a)*M := by rw [tsum_mul_left,(hMsum y).2]
    _ = _ := by ring
end Heisenberg.LatticeSum

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticeRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical BigOperators
open scoped Classical
open Module
open scoped BigOperators

namespace Heisenberg.LatticeRegular
open Heisenberg.Geometry Heisenberg.LatticeComponents Heisenberg.SparseWitness
variable {d : ℕ}

lemma component_crosses (Z : Set (Site d)) {z w : Site d} (hz : z ∈ Z)
    (hw : w ∈ Component Z z) (r : ℝ) (hr : r ≤ dist z w) : Crosses Z z r := by
  have hp : ∃ (p : ℕ → Site d) (m : ℕ), p 0 = z ∧ p m = w ∧
      (∀ i ≤ m, p i ∈ Z) ∧ (∀ i < m, dist (p i) (p (i+1)) ≤ 8) := by
    have hrel := hw.2
    clear hw hr
    induction hrel with
    | refl => exact ⟨fun _ => z,0,rfl,rfl,fun _ _ => hz,by simp⟩
    | @tail b c hzb hbc ih =>
      obtain ⟨p,m,hp0,hpm,hpZ,hpstep⟩ := ih
      let t : ℕ → Site d := fun i => if i ≤ m then p i else c
      refine ⟨t,m+1,?_,?_,?_,?_⟩
      · simp [t,hp0]
      · simp [t]
      · intro i hi
        by_cases h : i ≤ m
        · simpa [t,h] using hpZ i h
        · simpa [t,h] using hbc.2.2
      · intro i hi
        by_cases h : i < m
        · simpa [t,show i ≤ m by omega,show i+1 ≤ m by omega] using hpstep i h
        · have he : i = m := by omega
          subst i
          simpa [t,hpm] using (dist_le_iff_mem_ball (r:=8) b c).mpr hbc.1
  obtain ⟨p,m,hp0,hpm,hpZ,hpstep⟩ := hp
  exact ⟨p,m,hp0,hpZ,hpstep,by simpa [hp0,hpm] using hr⟩

lemma local_bad_count_bound {Ω : Type*} [Fintype Ω]
    (k M : ℕ) (α L p : ℝ) (hα : 0 ≤ α) (hL : (2*(k+1):ℕ) ≤ L)
    (μ : Ω → ℝ) (Z : Ω → Set (Site (k+1))) (hμ : ∀ ω, 0 ≤ μ ω)
    (htest : ∀ F : Finset (Site (k+1)), Sparse α L F →
      (∑ ω, if (F:Set (Site (k+1))) ⊆ Z ω then μ ω else 0) ≤ p^F.card)
    (x : Site (k+1)) (R : ℕ) :
    (∑ ω, if ∃ z ∈ Ball (11*R:ℕ) x,
      2*(k+1) ≤ ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card then μ ω else 0) ≤
      ((23:ℝ)^(k+1)*(((2*M+1)^(k+1)).choose (2*(k+1)):ℕ)) *
        (1+(R:ℝ))^(k+1)*p^(2*(k+1)) := by
  let B : ℝ := (23:ℝ)^(k+1)*(((2*M+1)^(k+1)).choose (2*(k+1)):ℕ)
  calc
    _ ≤ ∑ z ∈ ballFinset (k+1) (11*R) x,
      ∑ ω, if 2*(k+1) ≤ ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card then μ ω else 0 :=
      by
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro ω _
        split_ifs with h
        · obtain ⟨z,hz,hh⟩ := h
          have hzm := (mem_ballFinset (k+1) (11*R) x z).mpr hz
          have hs := Finset.single_le_sum (f:=fun z =>
            if 2*(k+1) ≤ ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card then μ ω else 0)
            (fun j _ => by split_ifs <;> simp [hμ]) hzm
          simpa only [ite_eq_left hh] using hs
        · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hμ])
    _ ≤ ∑ _z ∈ ballFinset (k+1) (11*R) x, ((((2*M+1)^(k+1)).choose (2*(k+1)):ℕ):ℝ)*p^(2*(k+1)) := by
      apply Finset.sum_le_sum
      intro z _
      simpa only [ballFinset_card] using bad_count_mass μ hμ Z α L p hα
        ((by positivity : (0:ℝ) ≤ (2*(k+1):ℕ)).trans hL) (2*(k+1)) hL htest (ballFinset (k+1) M z)
    _ = (((2*(11*R)+1)^(k+1)):ℝ)*(((((2*M+1)^(k+1)).choose (2*(k+1)):ℕ):ℝ)*p^(2*(k+1))) := by simp [ballFinset_card]
    _ ≤ B*(1+(R:ℝ))^(k+1)*p^(2*(k+1)) := by
      have hp : 0 ≤ p^(2*(k+1)) := by rw [pow_mul]; positivity
      have hbase : (2*(11*R)+1:ℕ) ≤ 23*(1+(R:ℝ)) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) R]
      have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2*(11*R)+1:ℕ)) hbase (k+1)
      rw [mul_pow] at hh
      dsimp [B]
      push_cast at hh
      nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg (Nat.cast_nonneg (((2*M+1)^(k+1)).choose (2*(k+1)))) hp)]

theorem regularity_bound_of_tail
    (k M : ℕ) (α L ν a c γ : ℝ) (hα : 0 ≤ α) (hL : (2*(k+1):ℕ) ≤ L)
    (hν : 0 < ν) (ha : 0 ≤ a) (hc : 0 < c) (hγ : 0 < γ) :
    ∃ C ≥ 0, ∀ (Ω : Type*) [Fintype Ω] (μ : Ω → ℝ) (Z : Ω → Set (Site (k+1))) (p : ℝ),
      (∀ ω, 0 ≤ μ ω) →
      (∀ F : Finset (Site (k+1)), Sparse α L F →
        (∑ ω, if (F:Set (Site (k+1))) ⊆ Z ω then μ ω else 0) ≤ p^F.card) →
      (∀ z r, 0 ≤ r → (∑ ω, if Crosses (Z ω) z r then μ ω else 0) ≤
        Real.exp 1*Real.exp (-c*r^γ)) →
      ∀ (x : Site (k+1)) (R : ℕ),
        (∑ ω, if ¬ Regular (Z ω) x R M ν then μ ω else 0) ≤
          C*((1+(R:ℝ))^(k+1)*p^(2*(k+1))+(1+(R:ℝ))^(-a)) := by
  obtain ⟨D,hD,hDt⟩ := Heisenberg.LatticeSum.exp_tail_polynomial k c (ν*γ) a hc (mul_pos hν hγ) ha
  let B : ℝ := (23:ℝ)^(k+1)*(((2*M+1)^(k+1)).choose (2*(k+1)):ℕ)
  refine ⟨B+Real.exp 1*D,by dsimp [B]; positivity,?_⟩
  intro Ω inst μ Z p hμ htest htail x R
  let A : Ω → Prop := fun ω => ∃ z ∈ Ball (11*R:ℕ) x,
    2*(k+1) ≤ ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card
  let E : Site (k+1) → Ω → Prop := fun z ω => z ∉ Ball (10*R:ℕ) x ∧
    ∃ w ∈ Component (Z ω) z, (1+dist z x)^ν < dist z w ∧ z ∈ Z ω
  have hA : (∑ ω, if A ω then μ ω else 0) ≤ B*(1+(R:ℝ))^(k+1)*p^(2*(k+1)) :=
    local_bad_count_bound k M α L p hα hL μ Z hμ htest x R
  let G : Site (k+1) → ℝ := fun z => if (R:ℝ) < dist z x then Real.exp (-c*(1+dist z x)^(ν*γ)) else 0
  have ht := hDt x (R:ℝ) (Nat.cast_nonneg R)
  have hsG : Summable G := ht.1
  have hE : ∀ z, (∑ ω, if E z ω then μ ω else 0) ≤ Real.exp 1*G z := by
    intro z
    by_cases hz : (R:ℝ) < dist z x
    · calc
        _ ≤ ∑ ω, if Crosses (Z ω) z ((1+dist z x)^ν) then μ ω else 0 :=
          by
            have hm := event_mass_mono μ hμ (A:=E z) (B:=fun ω => Crosses (Z ω) z ((1+dist z x)^ν)) (by
              intro ω h
              obtain ⟨_,w,hw,hd,hzZ⟩ := h
              exact component_crosses _ hzZ hw _ hd.le)
            convert hm using 1
            apply Finset.sum_congr rfl
            intro ω _
            split_ifs <;> rfl
        _ ≤ Real.exp 1*Real.exp (-c*((1+dist z x)^ν)^γ) :=
          htail z _ (Real.rpow_nonneg (by positivity) _)
        _ = _ := by dsimp [G]; rw [ite_eq_left hz,←Real.rpow_mul (by positivity)]
    · have hempty : ∀ ω, ¬ E z ω := by
        intro ω h
        have hb : dist x z ≤ (10*R:ℕ) := by
          rw [dist_comm]; push_cast; linarith [le_of_not_gt hz,Nat.cast_nonneg (α:=ℝ) R]
        exact h.1 ((dist_le_iff_mem_ball x z).mp hb)
      simp [hempty,G,hz]
  have hremote : (∑ ω, if ∃ z, E z ω then μ ω else 0) ≤ Real.exp 1*D*(1+(R:ℝ))^(-a) := by
    calc
      _ ≤ ∑' z, Real.exp 1*G z := countable_union_mass μ hμ E (fun ω => ∃ z, E z ω)
        (fun z => Real.exp 1*G z) (by intro z; dsimp [G]; split_ifs <;> positivity)
        (hsG.mul_left _) (by
          intro z
          convert hE z using 1
          apply Finset.sum_congr rfl
          intro ω _
          split_ifs <;> rfl) (fun ω h => h)
      _ = Real.exp 1*(∑' z, G z) := tsum_mul_left
      _ ≤ Real.exp 1*(D*(1+(R:ℝ))^(-a)) := mul_le_mul_of_nonneg_left ht.2 (Real.exp_pos _).le
      _ = _ := by ring
  have hsplit : (∑ ω, if ¬ Regular (Z ω) x R M ν then μ ω else 0) ≤
      (∑ ω, if A ω then μ ω else 0)+(∑ ω, if ∃ z, E z ω then μ ω else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have hcover : ¬ Regular (Z ω) x R M ν → A ω ∨ ∃ z, E z ω := by
      intro hh
      dsimp [Regular] at hh
      push Not at hh
      by_cases h : A ω
      · exact Or.inl h
      · right
        have hn : ∀ z ∈ Ball (11*R:ℕ) x, ((ballFinset (k+1) M z).filter (· ∈ Z ω)).card < 2*(k+1) := by
          intro z hz
          exact lt_of_not_ge (fun hh => h ⟨z,hz,hh⟩)
        obtain ⟨z,hz,hzn,w,hw,hd⟩ := hh hn
        exact ⟨z,hzn,w,hw,hd,hz⟩
    split_ifs <;> try linarith [hμ ω]
    exact False.elim (by rcases hcover ‹¬ Regular (Z ω) x R M ν› with h | h <;> contradiction)
  calc
    _ ≤ B*(1+(R:ℝ))^(k+1)*p^(2*(k+1))+Real.exp 1*D*(1+(R:ℝ))^(-a) := hsplit.trans (add_le_add hA hremote)
    _ ≤ _ := by
      have hp : 0 ≤ p^(2*(k+1)) := by rw [pow_mul]; positivity
      have hB : 0 ≤ B := by dsimp [B]; positivity
      nlinarith [mul_nonneg hB (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1+(R:ℝ)) (-a)),
        mul_nonneg (mul_nonneg (Real.exp_pos 1).le hD) (mul_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ 1+(R:ℝ)) (k+1)) hp)]

theorem regularity_probability (k M b : ℕ) (hb : 100 ≤ b)
    (α L ν a : ℝ) (hα : 0 ≤ α) (hL : (2*(k+1):ℕ) ≤ L)
    (hba : 2 ≤ (b:ℝ)^α) (hν : 0 < ν) (ha : 0 ≤ a) :
    ∃ p₀ > 0, ∃ C ≥ 0, ∀ (Ω : Type*) [Fintype Ω]
      (μ : Ω → ℝ) (Z : Ω → Set (Site (k+1))) (p : ℝ),
      (∀ ω, 0 ≤ μ ω) → (∑ ω, μ ω ≤ 1) → 0 ≤ p → p ≤ p₀ →
      (∀ F : Finset (Site (k+1)), Sparse α L F →
        (∑ ω, if (F:Set (Site (k+1))) ⊆ Z ω then μ ω else 0) ≤ p^F.card) →
      ∀ (x : Site (k+1)) (R : ℕ),
        (∑ ω, if ¬ Regular (Z ω) x R M ν then μ ω else 0) ≤
          C*((1+(R:ℝ))^(k+1)*p^(2*(k+1))+(1+(R:ℝ))^(-a)) := by
  have hbR : (1:ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  obtain ⟨γ,hγ,hbγ⟩ := exists_scale_exponent hbR
  let c : ℝ := (16*(b:ℝ))^(-γ)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨C,hC,hreg⟩ := regularity_bound_of_tail k M α L ν a c γ hα hL hν ha hc hγ
  let B : ℝ := (49^(k+1)*(b^(k+1))^2:ℕ)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨Real.exp (-2)/B,by positivity,C,hC,?_⟩
  intro Ω inst μ Z p hμ hprob hp hps htest x R
  apply hreg Ω μ Z p hμ htest _ x R
  intro z r hr
  have hL' : (1:ℝ) ≤ L := by
    have hh : (1:ℝ) ≤ (2*(k+1):ℕ) := by exact_mod_cast (show 1 ≤ 2*(k+1) by omega)
    exact hh.trans hL
  have ht := stretched_tail_of_scales μ hμ hprob Z (b:ℝ) γ hbR hγ hbγ ?_ z r hr
  · convert ht using 1
    rw [Real.div_rpow hr (by positivity)]
    dsimp [c]
    rw [Real.rpow_neg (by positivity)]
    ring_nf
  · intro n z
    calc
      _ ≤ (B*p)^(2^n) := lattice_crossing_mass_bound (k+1) b hb α L hα hL' hba μ hμ Z p hp htest n z
      _ ≤ (Real.exp (-2))^(2^n) := by
        apply pow_le_pow_left₀ (mul_nonneg hB.le hp)
        have hh := (le_div_iff₀ hB).mp hps
        simpa only [mul_comm] using hh
      _ = Real.exp (-2*(2:ℝ)^n) := by rw [←Real.exp_nat_mul]; congr 1; push_cast; ring

end Heisenberg.LatticeRegular

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LayerRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical BigOperators
open Module
open scoped BigOperators

open scoped Classical

open scoped BigOperators Classical
namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype T] [Fintype V] in
lemma localGrowth_image {X Y Z : Type*} [PseudoMetricSpace X] [DecidableEq Z]
    (loc : Z → X) (f : Y → Z) (F : Finset Y) (α L : ℝ)
    (hf : Function.Injective f) :
    localGrowth loc α L (F.image f) ↔ localGrowth (loc ∘ f) α L F := by
  unfold localGrowth
  have he (x : X) (r : ℝ) :
      ((F.image f).filter (fun v => dist (loc v) x ≤ r)).card =
        (F.filter (fun v => dist (loc (f v)) x ≤ r)).card := by
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ hf
  simp only [he,Function.comp_apply]

theorem layer_blocked_mass_le {X : Type*} [PseudoMetricSpace X]
    (loc : V → X) (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (t : T) (μ : (T → Bool) → ℝ) (hμ : ∀ b,0≤μ b)
    (α L p : ℝ) (hp : 0≤p)
    (htest : ∀ U : Finset V, localGrowth loc α L U →
      (∀ v ∈ U,(t,v) ∉ P) →
      (∑ b,if ∀ v ∈ U,(t,v) ∈ MissingSet (layerHistory s τ b) P then μ b else 0) ≤ p^U.card)
    (F : Finset X) (hF : localGrowth id α L F) :
    (∑ b,if (F:Set X) ⊆ layerBlocked loc s τ P b t then μ b else 0) ≤ p^F.card := by
  classical
  by_cases hr : ∀ x ∈ F,∃ v,loc v=x
  · choose r hloc using (fun x : F => hr x x.property)
    let U : Finset V := Finset.univ.image r
    have hinj : Function.Injective r := by
      intro x y h
      apply Subtype.ext
      exact (hloc x).symm.trans ((congrArg loc h).trans (hloc y))
    have hcard : U.card=F.card := by
      rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_coe]
    have hUg : localGrowth loc α L U := by
      rw [localGrowth_image _ _ _ _ _ hinj]
      intro x h hh
      have he : (Finset.univ.filter (fun v : F => dist (loc (r v)) x ≤ h)).card =
          (F.filter (fun v => dist v x ≤ h)).card := by
        simp only [hloc]
        apply Finset.card_bij (fun v _ => v.val)
        · intro v hv
          exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
        · intro v _ w _ h
          exact Subtype.ext h
        · intro v hv
          exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,by simpa using (Finset.mem_filter.mp hv).2,rfl⟩
      simpa only [Function.comp_apply,he,id_eq] using hF x h hh
    have hcover (b) (hb : (F:Set X) ⊆ layerBlocked loc s τ P b t) :
        ∀ v ∈ U,(t,v) ∈ MissingSet (layerHistory s τ b) P := by
      intro v hv
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
      exact not_not.mp ((hb x.property).2 (r x) (hloc x))
    by_cases hP : ∀ v ∈ U,(t,v) ∉ P
    · calc
        _ ≤ ∑ b,if ∀ v ∈ U,(t,v) ∈ MissingSet (layerHistory s τ b) P then μ b else 0 := by
          apply Finset.sum_le_sum
          intro b _
          split_ifs with hb hm
          · rfl
          · exact False.elim (hm (hcover b hb))
          · exact hμ b
          · rfl
        _ ≤ p^U.card := htest U hUg hP
        _ = _ := by rw [hcard]
    · have hz : ∀ b,¬(F:Set X) ⊆ layerBlocked loc s τ P b t := by
        intro b hb
        obtain ⟨v,hv,hvP⟩ := by simpa only [not_forall,Classical.not_imp,not_not] using hP
        exact hcover b hb v hv (t,v) hvP rfl
      simp only [hz,ite_false,Finset.sum_const_zero]
      exact pow_nonneg hp _
  · have hz : ∀ b,¬(F:Set X) ⊆ layerBlocked loc s τ P b t := by
      intro b hb
      exact hr fun x hx => (hb hx).1
    simp only [hz,ite_false,Finset.sum_const_zero]
    exact pow_nonneg hp _

end

open Heisenberg.Geometry Heisenberg.SparseWitness Heisenberg.LatticeRegular

end Heisenberg.Exposure

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ScheduledResiduals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Fin.NatCast

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.Serial
open Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks
variable {V T X E : Type} [Fintype V] [DecidableEq V] [Fintype T]
  [PseudoMetricSpace X] [Fintype E]

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma product_snoc (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ) :
    product (n+1) K=K (Fin.last n)*product n (fun i=>K i.castSucc) := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [product,ih,product,Matrix.mul_assoc]
    rfl

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma prefix_product (K : ℕ → Matrix V V ℝ) (n : ℕ) :
    prefixMatrix K n=product n (fun i=>K i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixMatrix,product_snoc]
    simpa only [Fin.val_last,Fin.val_castSucc] using congrArg (K n * ·) ih

end Heisenberg.Serial

end
end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ReversedExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.Exposure
open Heisenberg.Geometry Heisenberg.SpatialFrame Heisenberg.SparseWitness Heisenberg.LatticeRegular

lemma layerBlocked_frame {X B T : Type} [Fintype B] [Nonempty B] [Fintype T]
    (Λ : Finset X) (s : Equiv.Perm T) (τ : T → Equiv.Perm (Slots (B:=B) Λ))
    (P : Set (T×Slots (B:=B) Λ)) (base : T → Bool) (t : T) :
    layerBlocked (fun v : Slots (B:=B) Λ=>v.1.val) s τ P base t =
      blocked Λ (holeCut s τ base P t) := by
  ext x
  constructor
  · rintro ⟨⟨v,hv⟩,hh⟩
    have hx : x∈Λ := hv ▸ v.1.property
    refine ⟨hx,?_⟩
    intro a
    exact hh (⟨x,hx⟩,a) rfl
  · rintro ⟨hx,hh⟩
    refine ⟨⟨(⟨x,hx⟩,Classical.choice inferInstance),rfl⟩,?_⟩
    intro v hv
    obtain ⟨⟨y,hy⟩,a⟩ := v
    dsimp only at hv
    subst y
    exact hh a

theorem uniform_layer_regularity (k M b : ℕ) (hb : 100≤b)
    (α L ν a : ℝ) (hα : 0≤α) (hL : (2*(k+1):ℕ)≤L)
    (hba : 2≤(b:ℝ)^α) (hν : 0<ν) (ha : 0≤a) :
    ∃ p₀>0,∃ C≥0,∀ (T V : Type) [Fintype T] [Fintype V] (loc : V → Site (k+1)) (s : Equiv.Perm T)
      (u v : T → V) (P : Set (T×V)) (rates : T → ℝ)
      (_hrates : ∀ i,0≤rates i ∧ rates i≤1) (t : T) (p : ℝ),
      0≤p → p≤p₀ →
      (∀ U : Finset V,localGrowth loc α L U → (∀ j∈U,(t,j)∉P) →
        (∑ c,if ∀ j∈U,(t,j)∈Cycle.MissingSet
          (layerHistory s (fun i=>Equiv.swap (u i) (v i)) c) P then
          layerMass s u v P rates c else 0)≤p^U.card) →
      ∀ (x : Site (k+1)) (R : ℕ),
        (∑ c,if ¬Regular (layerBlocked loc s (fun i=>Equiv.swap (u i) (v i)) P c t)
          x R M ν then layerMass s u v P rates c else 0) ≤
          C*((1+(R:ℝ))^(k+1)*p^(2*(k+1))+(1+(R:ℝ))^(-a)) := by
  obtain ⟨p₀,hp₀,C,hC,hr⟩ := regularity_probability k M b hb α L ν a hα hL hba hν ha
  refine ⟨p₀,hp₀,C,hC,?_⟩
  intro T V _ _ loc s u v P rates hrates t p hp hpp htest x R
  apply hr (T → Bool) (layerMass s u v P rates)
    (fun c=>layerBlocked loc s (fun i=>Equiv.swap (u i) (v i)) P c t) p
    (layerMass_nonneg s u v P rates hrates) (layerMass_sum s u v P rates hrates).le hp hpp _ x R
  intro F hF
  exact layer_blocked_mass_le loc s (fun i=>Equiv.swap (u i) (v i)) P t
    (layerMass s u v P rates) (layerMass_nonneg s u v P rates hrates)
    α L p hp htest F hF

end Heisenberg.Exposure

end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PeriodicLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
lemma swap_classical {α : Type*} [h : DecidableEq α] (a b : α) :
    Equiv.swap a b = @Equiv.swap α (Classical.decEq α) a b := by
  have he : h=Classical.decEq α := Subsingleton.elim _ _
  cases he
  rfl

end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PolynomialLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical Topology
open Set Filter Metric
namespace Heisenberg.Pin

lemma nonzero_uniform_limit_disk {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε)
    (hF : ∀ᶠ i in φ, DiffContOnCl ℂ (F i) (ball c r))
    (h₀ : ∀ᶠ i in φ, ∀ z ∈ closedBall c r, F i z ≠ 0)
    (hf : TendstoUniformlyOn F f φ (closedBall c r))
    (hbound : ∀ z ∈ sphere c r, ε ≤ ‖f z‖) : f c ≠ 0 := by
  have hevent : ∀ᶠ i in φ, ε / 2 ≤ ‖F i c‖ := by
    filter_upwards [hF, h₀, (Metric.tendstoUniformlyOn_iff.mp hf) (ε / 2)
      (half_pos hε)] with i hi hz hclose
    have hfront : ∀ z ∈ frontier (ball c r), ‖(F i z)⁻¹‖ ≤ (ε / 2)⁻¹ := by
      intro z hz'
      rw [frontier_ball c hr.ne'] at hz'
      have hcz := hclose z (sphere_subset_closedBall hz')
      have hlen : ε / 2 ≤ ‖F i z‖ := by
        have htriangle := norm_sub_norm_le (f z) (F i z)
        rw [dist_eq_norm] at hcz
        linarith [hbound z hz']
      rw [norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le (half_pos hε) hlen) (half_pos hε)).mpr hlen
    have hb : ‖(F i c)⁻¹‖ ≤ (ε / 2)⁻¹ := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (hi.inv (by simpa [closure_ball c hr.ne'] using hz)) hfront
      rw [closure_ball c hr.ne']
      exact mem_closedBall_self hr.le
    rw [norm_inv] at hb
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hz c (mem_closedBall_self hr.le)))
      (half_pos hε)).mp hb
  have hlim := (hf.tendsto_at (mem_closedBall_self hr.le)).norm
  have hlen : ε / 2 ≤ ‖f c‖ := ge_of_tendsto hlim hevent
  intro hz
  simp only [hz, norm_zero] at hlen
  exact (not_le_of_gt (half_pos hε)) hlen

lemma polynomial_disk {p : Polynomial ℂ} (hp : p ≠ 0) {U : Set ℂ} (hU : IsOpen U)
    {c : ℂ} (hc : c ∈ U) :
    ∃ r > 0, closedBall c r ⊆ U ∧ ∀ z ∈ sphere c r, p.eval z ≠ 0 := by
  let Z : Set ℂ := {z | p.IsRoot z} \ {c}
  have hZ : IsClosed Z := ((Polynomial.finite_setOfPred_isRoot hp).sdiff).isClosed
  have hcZ : c ∈ Zᶜ := by simp [Z]
  have hn : U ∩ Zᶜ ∈ 𝓝 c := (hU.inter hZ.isOpen_compl).mem_nhds ⟨hc, hcZ⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ / 2, half_pos hδ, ?_, ?_⟩
  · exact fun z hz => (hδU (closedBall_subset_ball (half_lt_self hδ) hz)).1
  · intro z hz hzero
    have hmem := (hδU (closedBall_subset_ball (half_lt_self hδ)
      (sphere_subset_closedBall hz))).2
    apply hmem
    refine ⟨hzero, ?_⟩
    simp only [mem_singleton_iff]
    intro heq
    subst z
    have hs : dist c c = δ / 2 := hz
    rw [dist_self] at hs
    exact (half_pos hδ).ne' hs.symm

theorem polynomial_nonvanishing_limit {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → ℂ} {p : Polynomial ℂ} (hp : p ≠ 0)
    {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ i in φ, DifferentiableOn ℂ (F i) U)
    (h₀ : ∀ᶠ i in φ, ∀ z ∈ U, F i z ≠ 0)
    (hf : TendstoLocallyUniformlyOn F (fun z => p.eval z) φ U) :
    ∀ c ∈ U, p.eval c ≠ 0 := by
  intro c hc
  obtain ⟨r, hr, hball, hsphere⟩ := polynomial_disk hp hU hc
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere c r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (p.continuous.norm.continuousOn)
  refine nonzero_uniform_limit_disk (F := F) (φ := φ) (f := fun z => p.eval z) (c := c) (r := r) hr (norm_pos_iff.mpr (hsphere z₀ hz₀)) ?_ ?_ ?_ ?_
  · filter_upwards [hF] with i hi
    apply DifferentiableOn.diffContOnCl
    exact hi.mono (by simpa only [closure_ball c hr.ne'] using hball)
  · filter_upwards [h₀] with i hi z hz
    exact hi z (hball hz)
  · exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf
      (closedBall c r) hball (isCompact_closedBall c r)
  · exact fun z hz => hmin hz

end Heisenberg.Pin
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StablePolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric

namespace Heisenberg.Pin

lemma isOpen_upper {σ : Type*} [Finite σ] : IsOpen (Upper (σ := σ)) := by
  have he : Upper (σ := σ) = ⋂ j : σ, {z | 0 < (z j).im} := by ext; simp [Upper]
  rw [he]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
    (Complex.continuous_im.comp (continuous_apply j))

lemma linePolynomial_eval {σ : Type*} (p : MvPolynomial σ ℂ) (z v : σ → ℂ) (t : ℂ) :
    (linePolynomial p z v).eval t = MvPolynomial.eval (fun j => z j + t * v j) p := by
  unfold linePolynomial
  rw [MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by ext; simp
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, hc, MvPolynomial.eval₂_id]

lemma locallyUniform_const {ι X : Type*} [TopologicalSpace X] (φ : Filter ι)
    (f : X → ℂ) (U : Set X) : TendstoLocallyUniformlyOn (fun _ => f) f φ U := by
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact Filter.Eventually.of_forall fun _ x _ => by simpa using hε

theorem stable_locallyUniform_limit {ι σ : Type*} [Fintype σ] {φ : Filter ι} [φ.NeBot]
    {P : ι → MvPolynomial σ ℂ} {p : MvPolynomial σ ℂ} (hp0 : p ≠ 0)
    (hc : TendstoLocallyUniformlyOn (fun i z => MvPolynomial.eval z (P i))
      (fun z => MvPolynomial.eval z p) φ Upper)
    (hstable : ∀ᶠ i in φ, Stable (P i)) : Stable p := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w p ≠ 0 := by
    by_contra h
    apply hp0
    apply MvPolynomial.funext
    simpa using (not_exists.mp h)
  intro z hz
  let v : σ → ℂ := fun j => w j - z j
  let f : ℂ → σ → ℂ := fun t j => z j + t * v j
  have hf : Continuous f := by fun_prop
  let U : Set ℂ := f ⁻¹' Upper
  have hU : IsOpen U := isOpen_upper.preimage hf
  have hzero : (0 : ℂ) ∈ U := by simpa [U, f, Upper] using hz
  have hp' : linePolynomial p z v ≠ 0 := by
    intro h
    have he := congrArg (fun q : Polynomial ℂ => q.eval 1) h
    simp only [linePolynomial_eval, one_mul, Polynomial.eval_zero] at he
    have hv : (fun j => z j + v j) = w := by funext j; dsimp [v]; ring
    rw [hv] at he
    exact hw he
  have hval := polynomial_nonvanishing_limit (φ := φ)
    (F := fun i t => (linePolynomial (P i) z v).eval t) hp' hU
    (Eventually.of_forall fun i => (linePolynomial (P i) z v).differentiable.differentiableOn)
    (by
      filter_upwards [hstable] with i hi t ht
      rw [linePolynomial_eval]
      exact hi (f t) ht)
    (by
      simp_rw [linePolynomial_eval]
      exact hc.comp f (fun _ ht => ht) hf.continuousOn) 0 hzero
  simpa only [linePolynomial_eval, zero_mul, add_zero] using hval

lemma locallyUniform_eval {ι σ X : Type*} [TopologicalSpace X] {φ : Filter ι}
    {z : ι → X → σ → ℂ} {w : X → σ → ℂ} {U : Set X}
    (hz : ∀ j, TendstoLocallyUniformlyOn (fun i x => z i x j) (fun x => w x j) φ U)
    (hw : ContinuousOn w U) (p : MvPolynomial σ ℂ) :
    TendstoLocallyUniformlyOn (fun i x => MvPolynomial.eval (z i x) p)
      (fun x => MvPolynomial.eval (w x) p) φ U := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using locallyUniform_const φ (fun _ : X => c) U
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul₀ (hz j) (p.continuous_eval.comp_continuousOn hw)
      ((continuous_apply j).comp_continuousOn hw)

lemma variablePolynomial_eval {σ : Type*} (p : MvPolynomial σ ℂ) (z : σ → ℂ)
    (j : σ) (t : ℂ) :
    (variablePolynomial p z j).eval t = MvPolynomial.eval (Function.update z j t) p := by
  unfold variablePolynomial
  rw [MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by ext; simp
  rw [hc, MvPolynomial.eval₂_id]
  congr 2
  funext k
  by_cases h : k = j <;> simp [h, Function.update]

lemma variablePolynomial_pderiv {σ : Type*} (p : MvPolynomial σ ℂ) (z : σ → ℂ) (j : σ) :
    variablePolynomial (MvPolynomial.pderiv j p) z j =
    (variablePolynomial p z j).derivative := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [variablePolynomial]
  | add p q hp hq =>
    simpa only [map_add, variablePolynomial, MvPolynomial.eval₂_add, Polynomial.derivative_add]
      using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [MvPolynomial.pderiv_mul, variablePolynomial, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Polynomial.derivative_mul]
    rw [show MvPolynomial.eval₂ Polynomial.C
      (fun k => if k = j then Polynomial.X else Polynomial.C (z k)) (MvPolynomial.pderiv j p) =
      variablePolynomial (MvPolynomial.pderiv j p) z j from rfl, hp]
    by_cases h : k = j
    · subst k
      simp [variablePolynomial]
    · simp [h, MvPolynomial.pderiv_X_of_ne h, variablePolynomial]

lemma polynomial_logDerivative_im_nonpos {p : Polynomial ℂ}
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    (p.derivative.eval z / p.eval z).im ≤ 0 := by
  have hpz := hp z hz
  have hp0 : p ≠ 0 := by intro h; simp [h] at hpz
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz]
  have hterm : ∀ w ∈ p.roots, (1 / (z - w)).im ≤ 0 := by
    intro w hw
    have hw0 : p.eval w = 0 := (Polynomial.mem_roots hp0).mp hw
    have hwim : w.im ≤ 0 := by
      by_contra h
      exact hp w (lt_of_not_ge h) hw0
    rw [one_div, Complex.inv_im]
    apply div_nonpos_of_nonpos_of_nonneg
    · simp only [Complex.sub_im]
      linarith
    · exact Complex.normSq_nonneg _
  generalize p.roots = s at *
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons w s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
    exact add_nonpos (hterm w (Multiset.mem_cons_self _ _))
      (ih (fun v hv => hterm v (Multiset.mem_cons_of_mem hv)))

lemma stable_add_imaginary_derivative {σ : Type*} {p : MvPolynomial σ ℂ}
    (hp : Stable p) (j : σ) {r : ℝ} (hr : 0 < r) :
    Stable (MvPolynomial.C (r : ℂ) * p + MvPolynomial.C Complex.I * MvPolynomial.pderiv j p) := by
  intro z hz heq
  have hpz := hp z hz
  let q := variablePolynomial p z j
  have hq : ∀ t : ℂ, 0 < t.im → q.eval t ≠ 0 := by
    intro t ht
    rw [variablePolynomial_eval]
    apply hp
    intro k
    by_cases hk : k = j
    · subst k; simpa using ht
    · simpa [Function.update_of_ne hk] using hz k
  have hlog := polynomial_logDerivative_im_nonpos hq (hz j)
  have hv : Function.update z j (z j) = z := Function.update_eq_self j z
  rw [show q = variablePolynomial p z j from rfl,
    ← variablePolynomial_pderiv, variablePolynomial_eval, variablePolynomial_eval, hv] at hlog
  simp only [map_add, map_mul, MvPolynomial.eval_C] at heq
  have hdiv : (r : ℂ) + Complex.I *
      (MvPolynomial.eval z (MvPolynomial.pderiv j p) / MvPolynomial.eval z p) = 0 := by
    apply (mul_left_inj' hpz).mp
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hpz, zero_mul]
    exact heq
  have hreal := congrArg Complex.re hdiv
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, Complex.zero_re] at hreal
  linarith

theorem stable_pderiv {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : Stable p) (j : σ) : MvPolynomial.pderiv j p = 0 ∨ Stable (MvPolynomial.pderiv j p) := by
  by_cases hzero : MvPolynomial.pderiv j p = 0
  · exact Or.inl hzero
  right
  let q := MvPolynomial.C Complex.I * MvPolynomial.pderiv j p
  have hq0 : q ≠ 0 := mul_ne_zero (MvPolynomial.C_ne_zero.mpr Complex.I_ne_zero) hzero
  have hc : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hq : Stable q := by
    apply stable_locallyUniform_limit (φ := 𝓝[>] (0 : ℝ))
      (P := fun r => MvPolynomial.C (r : ℂ) * p + q) hq0
    · have hconv := ((hc.tendstoUniformlyOn_const Upper).tendstoLocallyUniformlyOn.mul₀
        (locallyUniform_const (𝓝[>] (0 : ℝ)) (fun z => MvPolynomial.eval z p) Upper)
        continuousOn_const p.continuous_eval.continuousOn).add
        (locallyUniform_const (𝓝[>] (0 : ℝ)) (fun z => MvPolynomial.eval z q) Upper)
      change TendstoLocallyUniformlyOn
        (fun (r : ℝ) (z : σ → ℂ) => (r : ℂ) * MvPolynomial.eval z p + MvPolynomial.eval z q)
        (fun z => (0 : ℂ) * MvPolynomial.eval z p + MvPolynomial.eval z q)
        (𝓝[>] (0 : ℝ)) Upper at hconv
      simpa only [zero_mul, zero_add, map_add, map_mul, MvPolynomial.eval_C] using hconv
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact stable_add_imaginary_derivative hp j hr
  intro z hz hv
  apply hq z hz
  simp [q, hv]

end Heisenberg.Pin
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StableSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric

open scoped ComplexConjugate
namespace Heisenberg.Pin

section

lemma quotient_im (x y : ℂ) :
    (-(x / y)).im = -((x * conj y).im) / Complex.normSq y := by
  simp only [Complex.neg_im, Complex.div_im, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma section_swap {a b c e : ℂ} (h : StableSection a b c e) :
    StableSection a c b e := by
  intro z w hz hw
  have hs := h w z hw hz
  have he : biaffine a c b e z w = biaffine a b c e w z := by
    unfold biaffine
    ring
  exact he ▸ hs

lemma rootCriterion_nonneg {a b c e : ℂ} (h : StableSection a b c e)
    {z : ℂ} (hz : 0 < z.im) : 0 ≤ rootCriterion a b c e z := by
  by_cases hc : c + e * z = 0
  · simp [rootCriterion, hc]
  · by_contra hn
    have hn' : rootCriterion a b c e z < 0 := lt_of_not_ge hn
    have hip : 0 < (-( (a + b * z) / (c + e * z))).im := by
      rw [quotient_im]
      exact div_pos (neg_pos.mpr hn') (Complex.normSq_pos.mpr hc)
    apply h z (-( (a + b * z) / (c + e * z))) hz hip
    calc
      _ = (a + b * z) - ((a + b * z) / (c + e * z)) * (c + e * z) := by
        unfold biaffine
        ring
      _ = 0 := by rw [div_mul_cancel₀ _ hc, sub_self]

lemma symmetrization_identity (a b c e z : ℂ) (u : ℝ) :
    rootCriterion a ((1 - (u : ℂ)) * b + (u : ℂ) * c)
      ((1 - (u : ℂ)) * c + (u : ℂ) * b) e z =
      (1 - u) * rootCriterion a b c e z + u * rootCriterion a c b e z +
        u * (1 - u) * Complex.normSq (b - c) * z.im := by
  simp only [rootCriterion, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.normSq_apply]
  ring

lemma criterion_ne_zero {a b c e z w : ℂ}
    (hn : 0 < rootCriterion a b c e z) (hw : 0 < w.im) :
    biaffine a b c e z w ≠ 0 := by
  intro he
  have hc : c + e * z ≠ 0 := by
    intro hc
    simp [rootCriterion, hc] at hn
  have hw' : w = -((a + b * z) / (c + e * z)) := by
    rw [← neg_div]
    apply (eq_div_iff hc).mpr
    dsimp [biaffine] at he
    linear_combination he
  rw [hw', quotient_im] at hw
  have hneg : -rootCriterion a b c e z / Complex.normSq (c + e * z) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hn) (Complex.normSq_pos.mpr hc)
  exact (not_lt_of_ge hneg.le) hw

theorem partial_symmetrization {a b c e : ℂ} (h : StableSection a b c e)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    StableSection a ((1 - (u : ℂ)) * b + (u : ℂ) * c)
      ((1 - (u : ℂ)) * c + (u : ℂ) * b) e := by
  by_cases hu : u = 0
  · simpa [hu] using h
  by_cases hv : u = 1
  · simpa [hv] using section_swap h
  by_cases hbc : b = c
  · have hb : (1 - (u : ℂ)) * b + (u : ℂ) * c = b := by rw [← hbc]; ring
    have hc : (1 - (u : ℂ)) * c + (u : ℂ) * b = c := by rw [hbc]; ring
    rw [hb, hc]
    exact h
  intro z w hz hw
  apply criterion_ne_zero (hw := hw)
  rw [symmetrization_identity]
  have h₁ := rootCriterion_nonneg h hz
  have h₂ := rootCriterion_nonneg (section_swap h) hz
  have hp : 0 < u * (1 - u) * Complex.normSq (b - c) * z.im := by
    exact mul_pos (mul_pos (mul_pos (lt_of_le_of_ne hu0 (Ne.symm hu))
      (sub_pos.mpr (lt_of_le_of_ne hu1 hv)))
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hbc))) hz
  exact add_pos_of_nonneg_of_pos (add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) h₁)
    (mul_nonneg hu0 h₂)) hp

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
lemma subsetMonomial_insert (i : σ) (A : Finset σ) (hi : i ∉ A) :
    subsetMonomial (insert i A) = MvPolynomial.X i * subsetMonomial A := by
  simp [subsetMonomial, hi]

omit [Fintype σ] in
lemma pderiv_subsetMonomial (i : σ) (A : Finset σ) :
    MvPolynomial.pderiv i (subsetMonomial A) =
      if i ∈ A then subsetMonomial (A.erase i) else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [subsetMonomial_insert a A ha, Derivation.leibniz, ih]
    simp only [smul_eq_mul]
    by_cases hia : i = a
    · subst a
      simp [ha]
    · simp only [MvPolynomial.pderiv_X_of_ne (Ne.symm hia), mul_zero, add_zero,
        Finset.mem_insert, hia, false_or]
      by_cases hi : i ∈ A
      · rw [ite_eq_left hi, ite_eq_left hi, Finset.erase_insert_of_ne (Ne.symm hia)]
        rw [subsetMonomial_insert a (A.erase i) (fun h => ha (Finset.mem_of_mem_erase h))]
      · simp [hi]

lemma eval_presencePolynomial_one (μ : Finset σ → ℝ) (B : Finset σ) :
    MvPolynomial.eval (fun _ => 1) (presencePolynomial μ B) = (presence μ B : ℂ) := by
  simp [presencePolynomial, presence, subsetMonomial, apply_ite]

lemma pderiv_presencePolynomial (μ : Finset σ → ℝ) (B : Finset σ) (i : σ)
    (hi : i ∉ B) :
    MvPolynomial.pderiv i (presencePolynomial μ B) = presencePolynomial μ (insert i B) := by
  unfold presencePolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hB : B ⊆ A
  · by_cases hiA : i ∈ A
    · rw [ite_eq_left hB, ite_eq_left (Finset.insert_subset hiA hB), MvPolynomial.pderiv_C_mul,
        pderiv_subsetMonomial, ite_eq_left (Finset.mem_sdiff.mpr ⟨hiA, hi⟩)]
      congr 2
      ext j
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
      tauto
    · rw [ite_eq_left hB, ite_eq_right (fun h => hiA (h (Finset.mem_insert_self _ _))), MvPolynomial.pderiv_C_mul,
        pderiv_subsetMonomial, ite_eq_right (fun h => hiA (Finset.mem_sdiff.mp h).1), mul_zero]
  · have hB' : ¬ insert i B ⊆ A := fun h => hB (Finset.Subset.trans (Finset.subset_insert _ _) h)
    simp [hB, hB']

lemma presence_nonneg {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A) (B : Finset σ) :
    0 ≤ presence μ B := by
  unfold presence
  exact Finset.sum_nonneg fun A _ => by split_ifs; exact hμ A; exact le_rfl

lemma presence_polynomial_ne_zero {μ : Finset σ → ℝ} {B : Finset σ}
    (hB : 0 < presence μ B) : presencePolynomial μ B ≠ 0 := by
  intro h
  have hv := eval_presencePolynomial_one μ B
  rw [h, map_zero] at hv
  exact hB.ne' (by exact_mod_cast hv.symm)

theorem stable_presencePolynomial {μ : Finset σ → ℝ}
    (hs : Stable (presencePolynomial μ ∅)) (B : Finset σ) :
    presencePolynomial μ B = 0 ∨ Stable (presencePolynomial μ B) := by
  induction B using Finset.induction_on with
  | empty => exact Or.inr hs
  | @insert i B hi ih =>
    rw [← pderiv_presencePolynomial μ B i hi]
    rcases ih with h | h
    · simp [h]
    · exact stable_pderiv h i

end

lemma eval_boundarySection {σ τ : Type*} (p : MvPolynomial σ ℂ)
    (f : σ → Option τ) (a : σ → ℂ) (z : τ → ℂ) :
    MvPolynomial.eval z (boundarySection p f a) =
      MvPolynomial.eval (fun j => (f j).elim (a j) z) p := by
  rw [boundarySection, MvPolynomial.eval_eval₂]
  have hc : (MvPolynomial.eval z).comp MvPolynomial.C = RingHom.id ℂ := by ext; simp
  simp only [hc, MvPolynomial.eval₂_id]
  apply congrArg (fun z => MvPolynomial.eval z p)
  funext j
  cases f j <;> simp

theorem stable_boundarySection {σ τ : Type*} [Fintype τ]
    {p : MvPolynomial σ ℂ} (hp : Stable p) (f : σ → Option τ) (a : σ → ℝ)
    (hn : boundarySection p f (fun j => (a j : ℂ)) ≠ 0) :
    Stable (boundarySection p f (fun j => (a j : ℂ))) := by
  let ar : ℝ → σ → ℂ := fun r j => (a j : ℂ) + (r : ℂ) * Complex.I
  apply stable_locallyUniform_limit (φ := 𝓝[>] (0 : ℝ))
    (P := fun r => boundarySection p f (ar r)) hn
  · simp_rw [eval_boundarySection]
    apply locallyUniform_eval
    · intro j
      cases h : f j with
      | none =>
        simp only [Option.elim_none]
        have ht : Tendsto (fun r : ℝ => ar r j) (𝓝[>] 0) (𝓝 (a j : ℂ)) := by
          have hc : Continuous (fun r : ℝ => ar r j) := by fun_prop
          simpa [ar] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        exact (ht.tendstoUniformlyOn_const Upper).tendstoLocallyUniformlyOn
      | some k =>
        simp only [Option.elim_some]
        exact locallyUniform_const _ _ _
    · apply Continuous.continuousOn
      apply continuous_pi
      intro j
      cases h : f j <;> simp only [Option.elim_none, Option.elim_some] <;> fun_prop
  · filter_upwards [self_mem_nhdsWithin] with r hr z hz
    rw [eval_boundarySection]
    apply hp
    intro j
    cases h : f j with
    | none => simpa [h, ar] using hr
    | some k => simpa [h] using hz k

lemma stable_section_real_rayleigh {a b c e : ℝ}
    (h : StableSection (a : ℂ) (b : ℂ) (c : ℂ) (e : ℂ)) : a * e ≤ b * c := by
  have hn := rootCriterion_nonneg h (z := Complex.I) (by simp)
  have he : rootCriterion (a : ℂ) (b : ℂ) (c : ℂ) (e : ℂ) Complex.I = b * c - a * e := by
    simp [rootCriterion, Complex.mul_im, Complex.mul_re]
    ring
  rw [he] at hn
  linarith

end Heisenberg.Pin
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

namespace Heisenberg.Pin

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
lemma prod_pairAssignment (A : Finset σ) (i j : σ) (hij : i ≠ j) (z w : ℂ) :
    (∏ k ∈ A, pairAssignment i j z w k) =
      (if i ∈ A then z else 1) * (if j ∈ A then w else 1) := by
  have he (k : σ) : pairAssignment i j z w k =
      (if k = i then z else 1) * (if k = j then w else 1) := by
    by_cases hi : k = i
    · subst k; simp [pairAssignment, hij]
    · by_cases hj : k = j <;> simp [pairAssignment, hi, hj, Ne.symm hij]
  simp_rw [he, Finset.prod_mul_distrib]
  simp

lemma ofReal_presence (μ : Finset σ → ℝ) (B : Finset σ) :
    (presence μ B : ℂ) = ∑ A : Finset σ, if B ⊆ A then (μ A : ℂ) else 0 := by
  simp [presence, apply_ite]

lemma eval_presencePolynomial_pair (μ : Finset σ → ℝ) (B : Finset σ)
    (i j : σ) (hij : i ≠ j) (hi : i ∉ B) (hj : j ∉ B) (z w : ℂ) :
    MvPolynomial.eval (pairAssignment i j z w) (presencePolynomial μ B) =
      (presence μ B : ℂ) + (presence μ (insert i B) : ℂ) * (z - 1) +
      (presence μ (insert j B) : ℂ) * (w - 1) +
      (presence μ (insert i (insert j B)) : ℂ) * (z - 1) * (w - 1) := by
  simp only [presencePolynomial, map_sum, apply_ite, map_mul, MvPolynomial.eval_C,
    map_zero, subsetMonomial, MvPolynomial.eval_prod, MvPolynomial.eval_X]
  simp_rw [prod_pairAssignment _ i j hij z w]
  simp_rw [ofReal_presence, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hB : B ⊆ A
  · by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A <;>
      simp [Finset.insert_subset_iff, Finset.mem_sdiff, hi, hj, hB, hiA, hjA] <;> ring
  · have hBi : ¬ insert i B ⊆ A := fun h => hB (Finset.Subset.trans (Finset.subset_insert _ _) h)
    have hBj : ¬ insert j B ⊆ A := fun h => hB (Finset.Subset.trans (Finset.subset_insert _ _) h)
    have hBij : ¬ insert i (insert j B) ⊆ A := fun h => hBj (Finset.Subset.trans (Finset.subset_insert _ _) h)
    simp [hB, hBi, hBj, hBij]

lemma presence_mono {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    {B C : Finset σ} (hBC : B ⊆ C) : presence μ C ≤ presence μ B := by
  unfold presence
  apply Finset.sum_le_sum
  intro A _
  by_cases hC : C ⊆ A
  · simp [hC, Finset.Subset.trans hBC hC]
  · simp only [ite_eq_right hC]
    split_ifs
    · exact hμ A
    · exact le_rfl

theorem presence_pair_inequality {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    (hs : Stable (presencePolynomial μ ∅)) (B : Finset σ) (i j : σ)
    (hij : i ≠ j) (hi : i ∉ B) (hj : j ∉ B) :
    presence μ (insert i (insert j B)) * presence μ B ≤
      presence μ (insert i B) * presence μ (insert j B) := by
  by_cases hB : presence μ B = 0
  · rw [hB, mul_zero]
    exact mul_nonneg (presence_nonneg hμ _) (presence_nonneg hμ _)
  have hBpos : 0 < presence μ B := lt_of_le_of_ne (presence_nonneg hμ B) (Ne.symm hB)
  have hsB : Stable (presencePolynomial μ B) :=
    (stable_presencePolynomial hs B).resolve_left (presence_polynomial_ne_zero hBpos)
  let f : σ → Option Bool := fun k => if k = i then some false else if k = j then some true else none
  let q := boundarySection (presencePolynomial μ B) f (fun _ => (1 : ℂ))
  have evalq (z w : ℂ) :
      MvPolynomial.eval (fun b : Bool => if b then w else z) q =
       MvPolynomial.eval (pairAssignment i j z w) (presencePolynomial μ B) := by
    rw [eval_boundarySection]
    apply congrArg (fun z => MvPolynomial.eval z (presencePolynomial μ B))
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [f, pairAssignment, hki, hkj, Ne.symm hij]
  have hq : q ≠ 0 := by
    intro h
    have he := evalq 1 1
    simp only [h, map_zero] at he
    have hone : pairAssignment i j 1 1 = fun _ => 1 := by funext k; simp [pairAssignment]
    rw [hone, eval_presencePolynomial_one] at he
    exact hB (by exact_mod_cast he.symm)
  have hsq : Stable q := stable_boundarySection hsB f (fun _ => 1) hq
  have hsection : StableSection
      ((presence μ B - presence μ (insert i B) - presence μ (insert j B) +
        presence μ (insert i (insert j B)) : ℝ) : ℂ)
      ((presence μ (insert i B) - presence μ (insert i (insert j B)) : ℝ) : ℂ)
      ((presence μ (insert j B) - presence μ (insert i (insert j B)) : ℝ) : ℂ)
      (presence μ (insert i (insert j B)) : ℂ) := by
    intro z w hz hw
    have hn := hsq (fun b : Bool => if b then w else z) (by intro b; cases b <;> assumption)
    rw [evalq, eval_presencePolynomial_pair μ B i j hij hi hj] at hn
    convert hn using 1
    push_cast
    unfold biaffine
    ring
  have hiq := stable_section_real_rayleigh hsection
  nlinarith

end Heisenberg.Pin

namespace Heisenberg.Pin

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem presence_insert_le {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    (h₁ : presence μ ∅ = 1) (hs : Stable (presencePolynomial μ ∅))
    (B : Finset σ) (i : σ) (hi : i ∉ B) :
    presence μ (insert i B) ≤ presence μ {i} * presence μ B := by
  induction B using Finset.induction_on with
  | empty => simp [h₁]
  | @insert j B hj ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hiB : i ∉ B := fun h => hi (Finset.mem_insert_of_mem h)
    by_cases hB : presence μ B = 0
    · have hBi : presence μ (insert i (insert j B)) = 0 := by
        apply le_antisymm
        · calc
            _ ≤ presence μ B := presence_mono hμ (B := B)
                (C := insert i (insert j B)) (by intro k hk; simp [hk])
            _ = 0 := hB
        · exact presence_nonneg hμ _
      rw [hBi]
      exact mul_nonneg (presence_nonneg hμ _) (presence_nonneg hμ _)
    have hp : 0 < presence μ B := lt_of_le_of_ne (presence_nonneg hμ B) (Ne.symm hB)
    have hpair := presence_pair_inequality hμ hs B i j hij hiB hj
    have hstep := mul_le_mul_of_nonneg_right (ih hiB) (presence_nonneg hμ (insert j B))
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      presence μ (insert i (insert j B)) * presence μ B
          ≤ presence μ (insert i B) * presence μ (insert j B) := hpair
      _ ≤ (presence μ {i} * presence μ B) * presence μ (insert j B) := hstep
      _ = (presence μ {i} * presence μ (insert j B)) * presence μ B := by ring

theorem presence_product {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    (h₁ : presence μ ∅ = 1) (hs : Stable (presencePolynomial μ ∅))
    (J : Finset σ) : presence μ J ≤ ∏ j ∈ J, presence μ {j} := by
  induction J using Finset.induction_on with
  | empty => simp [h₁]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi]
    exact (presence_insert_le hμ h₁ hs J i hi).trans
      (mul_le_mul_of_nonneg_left ih (presence_nonneg hμ _))

end Heisenberg.Pin

namespace Heisenberg.Pin

lemma product_le_mean_pow {σ : Type*} (J : Finset σ) (hJ : J.Nonempty)
    (v : σ → ℝ) (hv : ∀ j ∈ J, 0 ≤ v j) :
    (∏ j ∈ J, v j) ≤ ((∑ j ∈ J, v j) / J.card) ^ J.card := by
  have hn : 0 < (J.card : ℝ) := by exact_mod_cast hJ.card_pos
  have hmean := Real.geom_mean_le_arith_mean J (fun _ => 1) v (by intros; norm_num)
    (by simpa using hn) hv
  simp only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hmean
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg hv) _) hmean J.card
  rw [Real.rpow_inv_natCast_pow (Finset.prod_nonneg hv) (ne_of_gt hJ.card_pos)] at hpow
  exact hpow

theorem presence_mean_bound {σ : Type*} [Fintype σ] [DecidableEq σ]
    {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A) (h₁ : presence μ ∅ = 1)
    (hs : Stable (presencePolynomial μ ∅)) (J : Finset σ) (hJ : J.Nonempty) :
    presence μ J ≤ ((∑ j ∈ J, presence μ {j}) / J.card) ^ J.card :=
  (presence_product hμ h₁ hs J).trans
    (product_le_mean_pow J hJ (fun j => presence μ {j}) (fun _ _ => presence_nonneg hμ _))

end Heisenberg.Pin

namespace Heisenberg.Pin

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma prod_pow_update (z : σ → ℂ) (i : σ) (u : ℂ) (a : σ →₀ ℕ) :
    (∏ k, (Function.update z i u k) ^ a k) =
      u ^ a i * ∏ k ∈ Finset.univ.erase i, z k ^ a k := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

lemma eval_update_affine (p : MvPolynomial σ ℂ) (i : σ) (hi : p.degreeOf i ≤ 1)
    (z : σ → ℂ) (u : ℂ) :
    MvPolynomial.eval (Function.update z i u) p =
      MvPolynomial.eval (Function.update z i 0) p +
      (MvPolynomial.eval (Function.update z i 1) p -
        MvPolynomial.eval (Function.update z i 0) p) * u := by
  simp only [MvPolynomial.eval_eq', prod_pow_update]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hdeg : a i ≤ 1 := (MvPolynomial.degreeOf_le_iff.mp hi) a ha
  interval_cases a i
  · simp
  · simp only [pow_one, zero_mul, mul_zero, sub_zero, zero_add]; ring

lemma exists_biaffine_section (p : MvPolynomial σ ℂ) (hp : MultiAffine p)
    (i j : σ) (hij : i ≠ j) (z : σ → ℂ) :
    ∃ a b c e : ℂ, ∀ u v,
      MvPolynomial.eval (Function.update (Function.update z i u) j v) p =
        biaffine a b c e u v := by
  let f (u v : ℂ) := MvPolynomial.eval (Function.update (Function.update z i u) j v) p
  have hf (u v : ℂ) : f u v = f 0 v + (f 1 v - f 0 v) * u := by
    unfold f
    rw [Function.update_comm hij]
    rw [eval_update_affine p i (hp i)]
    simp only [Function.update_comm hij]
  have hg (u v : ℂ) : f u v = f u 0 + (f u 1 - f u 0) * v :=
    eval_update_affine p j (hp j) _ _
  refine ⟨f 0 0, f 1 0 - f 0 0, f 0 1 - f 0 0,
    f 1 1 - f 1 0 - f 0 1 + f 0 0, ?_⟩
  intro u v
  change f u v = _
  rw [hf u v, hg 0 v, hg 1 v]
  unfold biaffine
  ring

omit [Fintype σ] [DecidableEq σ] in
lemma MultiAffine.const_mul {p : MvPolynomial σ ℂ} (hp : MultiAffine p) (c : ℂ) :
    MultiAffine (MvPolynomial.C c * p) := by
  intro i
  exact (MvPolynomial.degreeOf_mul_le i _ _).trans (by simpa using hp i)

theorem stable_symmetrize {p : MvPolynomial σ ℂ} (hp : Stable p)
    (hm : MultiAffine p) (i j : σ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Stable (symmetrize p i j u) := by
  by_cases hij : i = j
  · subst j
    have he : symmetrize p i i u = p := by
      simp only [symmetrize, Equiv.swap_self, Equiv.coe_refl, MvPolynomial.rename_id, AlgHom.id_apply]
      rw [← add_mul, ← map_add]
      simp
    rw [he]
    exact hp
  intro z hz
  obtain ⟨a, b, c, e, hsec⟩ := exists_biaffine_section p hm i j hij z
  have hs : StableSection a b c e := by
    intro v w hv hw
    rw [← hsec v w]
    apply hp
    intro k
    by_cases hj : k = j
    · subst k; simpa using hw
    by_cases hi : k = i
    · subst k; simpa [Function.update_of_ne hij] using hv
    simpa [Function.update_of_ne hj, Function.update_of_ne hi] using hz k
  have hs' := partial_symmetrization hs h0 h1 (z i) (z j) (hz i) (hz j)
  have hzself : Function.update (Function.update z i (z i)) j (z j) = z := by simp
  have hzswap : Function.update (Function.update z i (z j)) j (z i) = z ∘ Equiv.swap i j := by
    funext k
    by_cases hi : k = i
    · subst k; simp [hij]
    by_cases hj : k = j
    · subst k; simp
    simp [Function.update_of_ne hi, Function.update_of_ne hj,
      Equiv.swap_apply_of_ne_of_ne hi hj]
  have heval : MvPolynomial.eval z (symmetrize p i j u) =
      biaffine a ((1 - (u : ℂ)) * b + (u : ℂ) * c)
        ((1 - (u : ℂ)) * c + (u : ℂ) * b) e (z i) (z j) := by
    simp only [symmetrize, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
    rw [← hzself, hsec]
    rw [hzself, ← hzswap, hsec]
    unfold biaffine
    ring
  rwa [heval]

end Heisenberg.Pin
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PermutationSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

namespace Heisenberg.Pin

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma stable_permutationSymbol (π : Equiv.Perm V) : Stable (permutationSymbol π) := by
  intro z hz
  simp only [permutationSymbol, MvPolynomial.eval_prod, map_add, MvPolynomial.eval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hzero
  have hpos := add_pos (hz (Sum.inl i)) (hz (Sum.inr (π i)))
  rw [← Complex.add_im, hzero, Complex.zero_im] at hpos
  exact (lt_irrefl 0) hpos

lemma multiAffine_permutationSymbol (π : Equiv.Perm V) :
    MultiAffine (permutationSymbol π) := by
  intro j
  apply (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans
  apply (Finset.sum_le_sum fun i _ => MvPolynomial.degreeOf_add_le j _ _).trans
  cases j with
  | inl j => simp [MvPolynomial.degreeOf_X]
  | inr j =>
    simp only [MvPolynomial.degreeOf_X, reduceCtorEq, ite_false, zero_le, max_eq_right,
      Sum.inr.injEq]
    simp [← π.symm_apply_eq, eq_comm]

lemma Stable.rename {σ τ : Type*} {p : MvPolynomial σ ℂ}
    (hp : Stable p) (f : σ → τ) : Stable (MvPolynomial.rename f p) := by
  intro z hz
  rw [MvPolynomial.eval_rename]
  exact hp (z ∘ f) (fun i => hz (f i))

omit [DecidableEq V] in
lemma rename_permutationSymbol (π τ : Equiv.Perm V) :
    MvPolynomial.rename (Sum.map id τ) (permutationSymbol π) =
      permutationSymbol (τ * π) := by
  simp [permutationSymbol, map_prod, map_add,
    MvPolynomial.rename_X, Equiv.Perm.mul_apply]

omit [Fintype V] [DecidableEq V] in

lemma stable_rename_outputs {p : MvPolynomial (V ⊕ V) ℂ} (hp : Stable p)
    (τ : Equiv.Perm V) : Stable (MvPolynomial.rename (Sum.map id τ) p) :=
  hp.rename (Sum.map id τ)

end Heisenberg.Pin

namespace Heisenberg.Pin

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

lemma multiAffine_lawSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) :
    MultiAffine (lawSymbol μ π) := by
  intro i
  apply (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans
  apply Finset.sup_le
  intro ω _
  exact ((multiAffine_permutationSymbol (π ω)).const_mul (μ ω)) i

omit [Fintype V] in
lemma swap_output_map (i j : V) :
    Sum.map (id : V → V) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  funext k
  cases k with
  | inl k => simp [Equiv.swap_apply_def]
  | inr k =>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [Equiv.swap_apply_def, hki, hkj]

lemma lawSymbol_bernoulli (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (i j : V) (u : ℝ) :
    lawSymbol (fun z : Bool × Ω => (if z.1 then u else 1 - u) * μ z.2)
      (fun z : Bool × Ω => (if z.1 then Equiv.swap i j else 1) * π z.2) =
      symmetrize (lawSymbol μ π) (Sum.inr i) (Sum.inr j) u := by
  simp only [lawSymbol, Fintype.sum_prod_type, Fintype.sum_bool, ite_true,
    Bool.false_eq_true, ite_false, one_mul]
  unfold symmetrize
  rw [map_sum, Finset.mul_sum, Finset.mul_sum]
  simp only [map_mul, MvPolynomial.rename_C]
  rw [add_comm]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro ω _
    push_cast
    rw [map_mul, mul_assoc]
  · apply Finset.sum_congr rfl
    intro ω _
    rw [← swap_output_map, rename_permutationSymbol]
    push_cast
    rw [map_mul, mul_assoc]

theorem stable_lawSymbol_bernoulli (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hs : Stable (lawSymbol μ π)) (i j : V) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Stable (lawSymbol (fun z : Bool × Ω => (if z.1 then u else 1 - u) * μ z.2)
      (fun z : Bool × Ω => (if z.1 then Equiv.swap i j else 1) * π z.2)) := by
  rw [lawSymbol_bernoulli]
  exact stable_symmetrize hs (multiAffine_lawSymbol μ π) _ _ h0 h1

omit [DecidableEq V] in
lemma lawSymbol_deterministic_output (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (τ : Equiv.Perm V) :
    lawSymbol μ (fun ω => τ * π ω) = MvPolynomial.rename (Sum.map id τ) (lawSymbol μ π) := by
  simp only [lawSymbol, map_sum, map_mul, MvPolynomial.rename_C, rename_permutationSymbol]

end Heisenberg.Pin

namespace Heisenberg.Pin
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

omit [Fintype V] in
lemma partialSymbol_insert (π : V → V) (i : V) (U : Finset V) (hi : i ∉ U) :
    partialSymbol π (insert i U) =
      (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr (π i))) * partialSymbol π U := by
  simp [partialSymbol, hi]

omit [Fintype V] in
lemma pderiv_partialSymbol (π : V → V) (i : V) (U : Finset V) :
    MvPolynomial.pderiv (Sum.inl i) (partialSymbol π U) =
      if i ∈ U then partialSymbol π (U.erase i) else 0 := by
  induction U using Finset.induction_on with
  | empty => simp [partialSymbol]
  | @insert j U hj ih =>
    rw [partialSymbol_insert π j U hj, MvPolynomial.pderiv_mul, ih]
    by_cases hij : i = j
    · subst j
      simp [hj]
    · simp only [map_add, MvPolynomial.pderiv_X_of_ne (by simpa using Ne.symm hij : (Sum.inl j : V ⊕ V) ≠ Sum.inl i),
        MvPolynomial.pderiv_X_of_ne (by simp : Sum.inr (π j) ≠ Sum.inl i),
        zero_add, zero_mul, Finset.mem_insert, hij, false_or]
      by_cases hi : i ∈ U
      · rw [ite_eq_left hi, ite_eq_left hi, Finset.erase_insert_of_ne (Ne.symm hij)]
        rw [partialSymbol_insert π j (U.erase i) (fun h => hj (Finset.mem_of_mem_erase h))]
      · simp [hi]

omit [Fintype V] [DecidableEq V] in
lemma partialLawSymbol_eval_one (μ : Ω → ℝ) (π : Ω → V → V) (U : Finset V) :
    MvPolynomial.eval (fun _ => 1) (partialLawSymbol μ π U) =
      ((∑ ω, μ ω : ℝ) : ℂ) * 2 ^ U.card := by
  simp only [partialLawSymbol, partialSymbol, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, map_add, MvPolynomial.eval_X, one_add_one_eq_two,
    Finset.prod_const]
  rw [← Finset.sum_mul, Complex.ofReal_sum]

omit [Fintype V] [DecidableEq V] in
lemma partialLawSymbol_ne_zero (μ : Ω → ℝ) (π : Ω → V → V) (U : Finset V)
    (hμ : ∑ ω, μ ω ≠ 0) : partialLawSymbol μ π U ≠ 0 := by
  intro hz
  have he := partialLawSymbol_eval_one μ π U
  rw [hz, map_zero] at he
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ) (pow_ne_zero _ (by norm_num)) he.symm

omit [Fintype V] in
lemma pderiv_partialLawSymbol (μ : Ω → ℝ) (π : Ω → V → V) (U : Finset V)
    (i : V) (hi : i ∈ U) :
    MvPolynomial.pderiv (Sum.inl i) (partialLawSymbol μ π U) =
      partialLawSymbol μ π (U.erase i) := by
  simp only [partialLawSymbol, map_sum, MvPolynomial.pderiv_C_mul,
    pderiv_partialSymbol, hi, ite_true]

theorem stable_partialLawSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∑ ω, μ ω ≠ 0) (hs : Stable (lawSymbol μ π)) (U : Finset V) :
    Stable (partialLawSymbol μ (fun ω => π ω) U) := by
  have hall (B : Finset V) : Stable (partialLawSymbol μ (fun ω => π ω) (Finset.univ \ B)) := by
    induction B using Finset.induction_on with
    | empty => simpa [partialLawSymbol, partialSymbol, lawSymbol, permutationSymbol] using hs
    | @insert i B hi ih =>
      have hm : i ∈ Finset.univ \ B := by simp [hi]
      have he : (Finset.univ \ B).erase i = Finset.univ \ insert i B := by ext j; simp
      have hd := stable_pderiv ih (Sum.inl i)
      rw [pderiv_partialLawSymbol μ (fun ω => π ω) _ i hm, he] at hd
      exact hd.resolve_left (partialLawSymbol_ne_zero μ _ _ hμ)
  simpa using hall (Finset.univ \ U)

omit [Fintype V] [DecidableEq V] in
lemma output_extraction (μ : Ω → ℝ) (π : Ω → V → V) (T : Finset V) :
    boundarySection (partialLawSymbol μ π T)
      (Sum.elim (fun _ => none) (fun i => some i)) (fun _ => 0) = outputSymbol μ π T := by
  simp [boundarySection, partialLawSymbol, partialSymbol, outputSymbol]

omit [Fintype V] [DecidableEq V] in
lemma outputSymbol_eval_one (μ : Ω → ℝ) (π : Ω → V → V) (T : Finset V) :
    MvPolynomial.eval (fun _ => 1) (outputSymbol μ π T) = ((∑ ω, μ ω : ℝ) : ℂ) := by
  simp [outputSymbol]

theorem stable_outputSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∑ ω, μ ω ≠ 0) (hs : Stable (lawSymbol μ π)) (T : Finset V) :
    Stable (outputSymbol μ (fun ω => π ω) T) := by
  have hn : outputSymbol μ (fun ω => π ω) T ≠ 0 := by
    intro hz
    have he := outputSymbol_eval_one μ (fun ω => π ω) T
    rw [hz, map_zero] at he
    exact (Complex.ofReal_ne_zero.mpr hμ) he.symm
  rw [← output_extraction] at hn ⊢
  exact stable_boundarySection (stable_partialLawSymbol μ π hμ hs T)
    _ (fun _ => 0) hn

end Heisenberg.Pin
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinSplicing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

open scoped Classical
namespace Heisenberg.Pin

section

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma eraseNone_rename_some {σ : Type*} (p : MvPolynomial σ ℂ) :
    eraseNone (MvPolynomial.rename some p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [eraseNone]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    simp [eraseNone]

lemma pderiv_none_rename_some {σ : Type*} (p : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv none (MvPolynomial.rename some p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma eraseNone_X_none {σ : Type*} :
    eraseNone (MvPolynomial.X (none : Option σ)) = 0 := by simp [eraseNone]

lemma eraseNone_X_some {σ : Type*} (i : σ) :
    eraseNone (MvPolynomial.X (some i)) = MvPolynomial.X i := by simp [eraseNone]

omit [DecidableEq V] in
lemma renamed_symbol_fixed (π : Equiv.Perm (Option V)) (h : π none = none) :
    MvPolynomial.rename spliceVariables (permutationSymbol π) =
      (2 * MvPolynomial.X none) *
        MvPolynomial.rename some (permutationSymbol (Equiv.removeNone π)) := by
  have hs (i : V) : π (some i) = some (Equiv.removeNone π i) := by
    apply Eq.symm
    apply Equiv.removeNone_some
    cases he : π (some i) with
    | none => exact False.elim (Option.some_ne_none i (π.injective (he.trans h.symm)))
    | some j => exact ⟨j, rfl⟩
  simp only [permutationSymbol, map_prod, Fintype.prod_option, map_mul, map_add,
    MvPolynomial.rename_X, h, spliceVariables, hs]
  congr 1
  ring

theorem splice_permutationSymbol_fixed (π : Equiv.Perm (Option V)) (h : π none = none) :
    splice (permutationSymbol π) = 2 * permutationSymbol (Equiv.removeNone π) := by
  have hd : MvPolynomial.pderiv none (2 : MvPolynomial (Option (V ⊕ V)) ℂ) = 0 :=
    (MvPolynomial.pderiv none).map_natCast 2
  rw [splice, renamed_symbol_fixed π h, MvPolynomial.pderiv_mul]
  simp [hd, pderiv_none_rename_some, eraseNone_rename_some, map_ofNat]

omit [Fintype V] [DecidableEq V] in
lemma removeNone_at_predecessor (π : Equiv.Perm (Option V)) (a b : V)
    (ha : π (some a) = none) (hb : π none = some b) : Equiv.removeNone π a = b := by
  exact Option.some.inj ((Equiv.removeNone_none π ha).trans hb)

omit [Fintype V] [DecidableEq V] in
lemma removeNone_off_predecessor (π : Equiv.Perm (Option V)) (a i : V)
    (ha : π (some a) = none) (hi : i ≠ a) :
    π (some i) = some (Equiv.removeNone π i) := by
  apply Eq.symm
  apply Equiv.removeNone_some
  cases he : π (some i) with
  | none => exact False.elim (hi (Option.some.inj (π.injective (he.trans ha.symm))))
  | some j => exact ⟨j, rfl⟩

lemma renamed_symbol_spliced (π : Equiv.Perm (Option V)) (a b : V)
    (ha : π (some a) = none) (hb : π none = some b) :
    MvPolynomial.rename spliceVariables (permutationSymbol π) =
      (MvPolynomial.X none + MvPolynomial.X (some (Sum.inr b))) *
      (MvPolynomial.X (some (Sum.inl a)) + MvPolynomial.X none) *
      MvPolynomial.rename some
        (∏ i ∈ Finset.univ.erase a,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr (Equiv.removeNone π i)))) := by
  rw [permutationSymbol, Fintype.prod_option]
  rw [← Finset.mul_prod_erase Finset.univ (fun i : V =>
    MvPolynomial.X (Sum.inl (some i)) + MvPolynomial.X (Sum.inr (π (some i))))
    (Finset.mem_univ a)]
  simp only [map_mul, map_add, map_prod, MvPolynomial.rename_X, ha, hb,
    spliceVariables, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  rw [removeNone_off_predecessor π a i ha (Finset.mem_erase.mp hi).1]

theorem splice_permutationSymbol_nonfixed (π : Equiv.Perm (Option V))
    (h : π none ≠ none) :
    splice (permutationSymbol π) = permutationSymbol (Equiv.removeNone π) := by
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
  have hi : π.symm none ≠ none := by simpa using h
  obtain ⟨a, ha'⟩ := Option.ne_none_iff_exists'.mp hi
  have ha : π (some a) = none := by rw [← ha']; exact π.apply_symm_apply none
  rw [splice, renamed_symbol_spliced π a b ha hb, MvPolynomial.pderiv_mul]
  simp only [pderiv_none_rename_some, mul_zero, add_zero, MvPolynomial.pderiv_mul,
    map_add, MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne (Option.some_ne_none _),
    add_zero, zero_add, one_mul, mul_one, map_mul, eraseNone_X_none,
    eraseNone_X_some, eraseNone_rename_some]
  rw [permutationSymbol, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
  rw [removeNone_at_predecessor π a b ha hb]

end

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

lemma eraseNone_eq_boundarySection {σ : Type*} (p : MvPolynomial (Option σ) ℂ) :
    eraseNone p = boundarySection p id (fun _ => 0) := by
  simp only [eraseNone, boundarySection, MvPolynomial.aeval_def]
  congr 1
  funext j
  cases j <;> simp

omit [DecidableEq V] in

theorem stable_splice {p : MvPolynomial (Option V ⊕ Option V) ℂ}
    (hp : Stable p) (hn : splice p ≠ 0) : Stable (splice p) := by
  have hr : Stable (MvPolynomial.rename spliceVariables p) := by
    intro z hz
    rw [MvPolynomial.eval_rename]
    exact hp (z ∘ spliceVariables) (fun i => hz (spliceVariables i))
  obtain hz | hd := stable_pderiv hr none
  · exact False.elim (hn (by simp [splice, hz]))
  rw [splice, eraseNone_eq_boundarySection] at hn ⊢
  exact stable_boundarySection hd id (fun _ => 0) hn

omit [Fintype V] [DecidableEq V] in
lemma splice_C_mul (c : ℂ) (p : MvPolynomial (Option V ⊕ Option V) ℂ) :
    splice (MvPolynomial.C c * p) = MvPolynomial.C c * splice p := by
  simp only [splice, map_mul, MvPolynomial.rename_C, MvPolynomial.pderiv_C_mul]
  congr 1
  simp [eraseNone]

omit [Fintype V] [DecidableEq V] in
lemma splice_sum (p : Ω → MvPolynomial (Option V ⊕ Option V) ℂ) :
    splice (∑ ω, p ω) = ∑ ω, splice (p ω) := by simp [splice]

omit [Fintype V] [DecidableEq V] in
lemma spliceWeight_ge_one (π : Equiv.Perm (Option V)) : 1 ≤ spliceWeight π := by
  unfold spliceWeight
  split_ifs <;> norm_num

lemma splice_permutationSymbol (π : Equiv.Perm (Option V)) :
    splice (permutationSymbol π) =
      MvPolynomial.C (spliceWeight π : ℂ) * permutationSymbol (Equiv.removeNone π) := by
  by_cases h : π none = none
  · rw [splice_permutationSymbol_fixed π h]
    norm_num [spliceWeight, h, map_ofNat]
  · rw [splice_permutationSymbol_nonfixed π h]
    simp [spliceWeight, h]

lemma splice_lawSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm (Option V)) :
    splice (lawSymbol μ π) =
      lawSymbol (fun ω => μ ω * spliceWeight (π ω)) (fun ω => Equiv.removeNone (π ω)) := by
  simp only [lawSymbol, splice_sum, splice_C_mul, splice_permutationSymbol,
    Complex.ofReal_mul, map_mul, mul_assoc]

omit [DecidableEq V] in
lemma lawSymbol_eval_one_general (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) :
    MvPolynomial.eval (fun _ => 1) (lawSymbol μ π) =
      ((∑ ω, μ ω : ℝ) : ℂ) * 2 ^ Fintype.card V := by
  simp only [lawSymbol, permutationSymbol, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, map_add, MvPolynomial.eval_X, one_add_one_eq_two,
    Finset.prod_const, Finset.card_univ]
  rw [← Finset.sum_mul, Complex.ofReal_sum]

omit [DecidableEq V] in
lemma lawSymbol_ne_zero_general (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∑ ω, μ ω ≠ 0) : lawSymbol μ π ≠ 0 := by
  intro hzero
  have he := lawSymbol_eval_one_general μ π
  rw [hzero, map_zero] at he
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ) (pow_ne_zero _ (by norm_num)) he.symm

theorem stable_spliced_law (μ : Ω → ℝ) (π : Ω → Equiv.Perm (Option V))
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (hs : Stable (lawSymbol μ π)) :
    Stable (lawSymbol (fun ω => μ ω * spliceWeight (π ω))
      (fun ω => Equiv.removeNone (π ω))) := by
  rw [← splice_lawSymbol]
  apply stable_splice hs
  rw [splice_lawSymbol]
  apply lawSymbol_ne_zero_general
  apply ne_of_gt
  apply hpos.trans_le
  apply Finset.sum_le_sum
  intro ω _
  exact le_mul_of_one_le_right (hμ ω) (spliceWeight_ge_one (π ω))

end Heisenberg.Pin

namespace Heisenberg.Cycle

open Equiv

variable {V : Type*}

variable [Fintype V]

lemma classInclusion_surjective (π : Perm (Option V)) (hn : π none ≠ none) :
    Function.Surjective (classInclusion π) := by
  intro c
  induction c using Quotient.inductionOn with | _ i =>
    cases i with
    | some i => exact ⟨classOf (removeNone π) i, rfl⟩
    | none =>
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hn
      refine ⟨classOf (removeNone π) i, ?_⟩
      simp only [classInclusion_mk]
      rw [← hi, classOf_apply]
      rfl

lemma classInclusion_range_fixed (π : Perm (Option V)) (hfix : π none = none) :
    Set.range (classInclusion π) = {c | c ≠ classOf π none} := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩ h
    induction a using Quotient.inductionOn with | _ i =>
      have hs := (classOf_eq_iff π (some i) none).mp h
      exact Option.some_ne_none i (hs.eq_of_right hfix)
  · intro h
    induction c using Quotient.inductionOn with | _ i =>
      cases i with
      | none => exact False.elim (h rfl)
      | some i => exact ⟨classOf (removeNone π) i, rfl⟩

lemma missingInclusion_injective (π : Perm (Option V)) (P : Set V) :
    Function.Injective (missingInclusion π P) := by
  intro a b h
  apply Subtype.ext
  exact classInclusion_injective π (congrArg Subtype.val h)

lemma missingInclusion_surjective (π : Perm (Option V)) (P : Set V)
    (hn : π none ≠ none) : Function.Surjective (missingInclusion π P) := by
  intro c
  obtain ⟨a, ha⟩ := classInclusion_surjective π hn c.val
  refine ⟨⟨a, (missingInclusion_condition π P a).mp (by simpa [ha] using c.property)⟩, ?_⟩
  exact Subtype.ext ha

lemma missingCount_nonfixed (π : Perm (Option V)) (P : Set V) (hn : π none ≠ none) :
    missingCount π (some '' P) = missingCount (removeNone π) P := by
  unfold missingCount
  exact (Nat.card_congr (Equiv.ofBijective (missingInclusion π P)
    ⟨missingInclusion_injective π P, missingInclusion_surjective π P hn⟩)).symm

lemma missingOption_injective (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    Function.Injective (missingOption π P hf) := by
  intro a b he
  have hv := congrArg Subtype.val he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hb : classInclusion π b.val ≠ classOf π none := by
        have hr : classInclusion π b.val ∈ Set.range (classInclusion π) := ⟨b.val, rfl⟩
        rw [classInclusion_range_fixed π hf] at hr
        exact hr
      exact False.elim (hb hv.symm)
  | some a =>
    cases b with
    | none =>
      have ha : classInclusion π a.val ≠ classOf π none := by
        have hr : classInclusion π a.val ∈ Set.range (classInclusion π) := ⟨a.val, rfl⟩
        rw [classInclusion_range_fixed π hf] at hr
        exact hr
      exact False.elim (ha hv)
    | some b => exact congrArg some (missingInclusion_injective π P he)

lemma missingOption_surjective (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    Function.Surjective (missingOption π P hf) := by
  classical
  intro c
  by_cases hc : c.val = classOf π none
  · exact ⟨none, Subtype.ext hc.symm⟩
  · have hr : c.val ∈ Set.range (classInclusion π) := by
      rw [classInclusion_range_fixed π hf]
      exact hc
    obtain ⟨a, ha⟩ := hr
    refine ⟨some ⟨a, (missingInclusion_condition π P a).mp ?_⟩, Subtype.ext ha⟩
    simpa [ha] using c.property

lemma missingCount_fixed (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    missingCount π (some '' P) = missingCount (removeNone π) P + 1 := by
  unfold missingCount
  have he := Nat.card_congr (Equiv.ofBijective (missingOption π P hf)
    ⟨missingOption_injective π P hf, missingOption_surjective π P hf⟩)
  let _ : Fintype (MissingClasses (removeNone π) P) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option] using he.symm

theorem cycle_weight_splice (π : Perm (Option V)) (P : Set V) :
    (2 : ℝ) ^ missingCount π (some '' P) =
      (if π none = none then 2 else 1) * (2 : ℝ) ^ missingCount (removeNone π) P := by
  classical
  by_cases hf : π none = none
  · rw [ite_eq_left hf, missingCount_fixed π P hf, pow_succ, mul_comm]
  · rw [ite_eq_right hf, missingCount_nonfixed π P hf, one_mul]

end Heisenberg.Cycle

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StablePinLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
namespace Heisenberg.Transport
open Equiv
open Heisenberg.Cycle Heisenberg.Return
variable {V W : Type*} [Fintype V] [Fintype W]

lemma missing_pred_congr (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) (c : Classes π) :
    (∀ i ∈ P, c ≠ classOf π i) ↔
      ∀ j ∈ Q, classCongr e π c ≠ classOf (e.permCongr π) j := by
  constructor
  · intro hc j hj he
    have hm : e.symm j ∈ P := (h _).mpr (by simpa using hj)
    apply hc _ hm
    apply (classCongr e π).injective
    simpa using he
  · intro hc i hi he
    apply hc (e i) ((h i).mp hi)
    rw [he, classCongr_mk]

lemma missingCount_congr (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) :
    missingCount π P = missingCount (e.permCongr π) Q :=
  Nat.card_congr ((classCongr e π).subtypeEquiv (missing_pred_congr e π P Q h))

lemma firstValue_congr_at_hit (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) (x : V) (hx : HasHit π P x) :
    firstValue (e.permCongr π) Q (e x) = (firstValue π P x).map e := by
  apply firstValue_unique π P (fun x => firstValue (e.permCongr π) Q (e x)) e
  · intro i hi
    exact firstValue_of_mem _ ((h i).mp hi)
  · intro i hi
    have he := firstValue_step (e.permCongr π) Q (e i) (mt (h i).mpr hi)
    simpa using he
  · exact hx

lemma nextPoint_congr (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) (i : P) :
    nextPoint (e.permCongr π) Q (e.subtypeEquiv h i) =
      e.subtypeEquiv h (nextPoint π P i) := by
  apply Subtype.ext
  have hh := firstValue_congr_at_hit e π P Q h (π i)
    ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property))
  have he : e (π i) = (e.permCongr π) (e.subtypeEquiv h i : W) := by simp
  rw [he, nextValue_eq_nextPoint, nextValue_eq_nextPoint] at hh
  exact Option.some.inj hh

lemma nextPermutation_congr (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) :
    (e.subtypeEquiv h).permCongr (nextPermutation π P) =
      nextPermutation (e.permCongr π) Q := by
  apply Equiv.ext
  intro j
  obtain ⟨i, rfl⟩ := (e.subtypeEquiv h).surjective j
  simpa only [permCongr_apply, symm_apply_apply, nextPermutation, Equiv.ofBijective_apply] using (nextPoint_congr e π P Q h i).symm

lemma nextPoint_splice (π : Perm (Option V)) (P : Set V) (i : P) :
    nextPoint π (some '' P) (somePins P i) =
      somePins P (nextPoint (removeNone π) P i) := by
  apply Subtype.ext
  have hh := nextValue_splice π P (i : V) i.property
  change firstValue π (some '' P) (π (somePins P i : Option V)) = _ at hh
  rw [nextValue_eq_nextPoint, nextValue_eq_nextPoint] at hh
  exact Option.some.inj hh

lemma nextPermutation_splice (π : Perm (Option V)) (P : Set V) :
    (somePins P).permCongr (nextPermutation (removeNone π) P) =
      nextPermutation π (some '' P) := by
  apply Equiv.ext
  intro j
  obtain ⟨i, rfl⟩ := (somePins P).surjective j
  simpa only [permCongr_apply, symm_apply_apply, nextPermutation, Equiv.ofBijective_apply] using (nextPoint_splice π P i).symm

omit [Fintype V] in
lemma missingCount_univ (π : Perm V) : missingCount π Set.univ = 0 := by
  let : IsEmpty (MissingClasses π Set.univ) := ⟨by
    rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with | _ i => exact hc i (Set.mem_univ i) rfl⟩
  exact Nat.card_of_isEmpty

lemma nextPoint_all (π : Perm V) (i : V) :
    (nextPoint π Set.univ ⟨i, Set.mem_univ i⟩ : V) = π i := by
  have h := firstValue_of_mem π (P := Set.univ) (x := π i) (Set.mem_univ _)
  rw [nextValue_eq_nextPoint π Set.univ ⟨i, Set.mem_univ i⟩] at h
  exact Option.some.inj h

lemma nextPermutation_all (π : Perm V) :
    (Equiv.Set.univ V).symm.permCongr π = nextPermutation π Set.univ := by
  apply Equiv.ext
  intro i
  apply Subtype.ext
  change π (i : V) = (nextPoint π Set.univ i : V)
  exact (nextPoint_all π i).symm

end Heisenberg.Transport

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
open Heisenberg.Cycle Heisenberg.Return Heisenberg.Transport
open Equiv
variable {V W Ω : Type*} [Fintype V] [Fintype W] [Fintype Ω]

lemma permutationSymbol_congr (e : V ≃ W) (π : Perm V) :
    MvPolynomial.rename (Sum.map e e) (permutationSymbol π) =
      permutationSymbol (e.permCongr π) := by
  simp only [permutationSymbol, map_prod, map_add, MvPolynomial.rename_X,
    Sum.map_inl, Sum.map_inr]
  rw [← e.prod_comp (fun j => MvPolynomial.X (Sum.inl j) +
    MvPolynomial.X (Sum.inr (e.permCongr π j)))]
  simp only [permCongr_apply, symm_apply_apply]

lemma lawSymbol_congr (e : V ≃ W) (μ : Ω → ℝ) (π : Ω → Perm V) :
    MvPolynomial.rename (Sum.map e e) (lawSymbol μ π) =
      lawSymbol μ (fun ω => e.permCongr (π ω)) := by
  simp only [lawSymbol, map_sum, map_mul, MvPolynomial.rename_C, permutationSymbol_congr]

lemma stable_law_congr (e : V ≃ W) (μ : Ω → ℝ) (π : Ω → Perm V)
    (hs : Stable (lawSymbol μ π)) : Stable (lawSymbol μ (fun ω => e.permCongr (π ω))) := by
  rw [← lawSymbol_congr]
  exact hs.rename (Sum.map e e)

lemma pinLaw_all (μ : Ω → ℝ) (π : Ω → Perm V) :
    pinLaw μ π Set.univ = MvPolynomial.rename
      (Sum.map (Equiv.Set.univ V).symm (Equiv.Set.univ V).symm) (lawSymbol μ π) := by
  rw [lawSymbol_congr]
  unfold pinLaw
  simp only [missingCount_univ, pow_zero, mul_one, nextPermutation_all]
  exact congrArg (fun f : Fintype (Set.univ : Set V) =>
    @lawSymbol (Set.univ : Set V) Ω f inferInstance μ
      (fun ω => nextPermutation (π ω) Set.univ)) (Subsingleton.elim _ _)

lemma stable_pinLaw_all (μ : Ω → ℝ) (π : Ω → Perm V)
    (hs : Stable (lawSymbol μ π)) : Stable (pinLaw μ π Set.univ) := by
  rw [pinLaw_all]
  exact hs.rename _

omit [Fintype V] [Fintype Ω] in
lemma splice_mass_nonneg (μ : Ω → ℝ) (π : Ω → Perm (Option V))
    (hμ : ∀ ω, 0 ≤ μ ω) (ω : Ω) : 0 ≤ μ ω * spliceWeight (π ω) :=
  mul_nonneg (hμ ω) (le_trans zero_le_one (spliceWeight_ge_one (π ω)))

omit [Fintype V] in
lemma splice_mass_pos (μ : Ω → ℝ) (π : Ω → Perm (Option V))
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) :
    0 < ∑ ω, μ ω * spliceWeight (π ω) := by
  apply hpos.trans_le
  apply Finset.sum_le_sum
  intro ω _
  exact le_mul_of_one_le_right (hμ ω) (spliceWeight_ge_one (π ω))

universe u

theorem stable_pinLaw {V : Type u} [Fintype V] (μ : Ω → ℝ) (π : Ω → Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (hs : Stable (lawSymbol μ π))
    (P : Set V) : Stable (pinLaw μ π P) := by
  have hall (n : ℕ) : ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (μ : Ω → ℝ) (π : Ω → Perm V), (∀ ω, 0 ≤ μ ω) →
      0 < ∑ ω, μ ω → Stable (lawSymbol μ π) →
      ∀ P : Set V, Stable (pinLaw μ π P) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ hn μ π hμ hpos hs P
      by_cases hP : P = Set.univ
      · subst P
        exact stable_pinLaw_all μ π hs
      obtain ⟨q, hq⟩ : ∃ q : V, q ∉ P := by
        by_contra h
        apply hP
        exact Set.eq_univ_of_forall (by simpa only [not_exists, not_not] using h)
      let W := {i : V // i ≠ q}
      let e : Option W ≃ V := Equiv.optionSubtypeNe q
      let π' : Ω → Perm (Option W) := fun ω => e.symm.permCongr (π ω)
      let P' : Set W := {i | (i : V) ∈ P}
      have heπ (ω : Ω) : e.permCongr (π' ω) = π ω := by
        exact e.permCongr.apply_symm_apply (π ω)
      have heP : ∀ i : Option W, i ∈ some '' P' ↔ e i ∈ P := by
        intro i
        cases i with
        | none =>
          change (none ∈ some '' P') ↔ (Equiv.optionSubtypeNe q) none ∈ P
          rw [Equiv.optionSubtypeNe_none]
          simp [hq]
        | some i =>
          change (some i ∈ some '' P') ↔ (Equiv.optionSubtypeNe q) (some i) ∈ P
          rw [Equiv.optionSubtypeNe_some]
          simp [P']
      have hs' := stable_law_congr e.symm μ π hs
      have hss := stable_spliced_law μ π' hμ hpos hs'
      let μ' : Ω → ℝ := fun ω => μ ω * spliceWeight (π' ω)
      let π'' : Ω → Perm W := fun ω => Equiv.removeNone (π' ω)
      have hcard : Fintype.card W < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := q) (by simp)
      have hi := ih (Fintype.card W) hcard W rfl μ' π''
        (splice_mass_nonneg μ π' hμ) (splice_mass_pos μ π' hμ hpos) hss P'
      let ep : P' ≃ P := (somePins P').trans (e.subtypeEquiv heP)
      have hnext (ω : Ω) : ep.permCongr (nextPermutation (π'' ω) P') =
          nextPermutation (π ω) P := by
        have he := nextPermutation_congr e (π' ω) (some '' P') P heP
        rw [heπ] at he
        rw [← he, ← nextPermutation_splice]
        rfl
      have hweight (ω : Ω) : μ' ω * (2 : ℝ) ^ missingCount (π'' ω) P' =
          μ ω * (2 : ℝ) ^ missingCount (π ω) P := by
        have hc := missingCount_congr e (π' ω) (some '' P') P heP
        rw [heπ] at hc
        rw [← hc, cycle_weight_splice]
        simp only [μ', π'', spliceWeight, mul_assoc]
      have ht := stable_law_congr ep
        (fun ω => μ' ω * (2 : ℝ) ^ missingCount (π'' ω) P')
        (fun ω => nextPermutation (π'' ω) P') hi
      simpa only [hnext, hweight, pinLaw] using ht
  exact hall (Fintype.card V) V rfl μ π hμ hpos hs P

end Heisenberg.Pin
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SimultaneousPins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

omit [Fintype V] in
lemma subsetLaw_nonneg (μ : Ω → ℝ) (A : Ω → Finset V)
    (hμ : ∀ ω, 0 ≤ μ ω) (B : Finset V) : 0 ≤ subsetLaw μ A B := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> simp [hμ]

lemma presence_subsetLaw (μ : Ω → ℝ) (A : Ω → Finset V) (J : Finset V) :
    presence (subsetLaw μ A) J = ∑ ω, if J ⊆ A ω then μ ω else 0 := by
  have hterm (B : Finset V) : (if J ⊆ B then subsetLaw μ A B else 0) =
      ∑ ω, if A ω = B then (if J ⊆ A ω then μ ω else 0) else 0 := by
    by_cases hJ : J ⊆ B
    · rw [ite_eq_left hJ]
      unfold subsetLaw
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : A ω = B <;> simp [he, hJ]
    · rw [ite_eq_right hJ]
      symm
      apply Finset.sum_eq_zero
      intro ω _
      by_cases he : A ω = B <;> simp [he, hJ]
  unfold presence
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

lemma presencePolynomial_subsetLaw (μ : Ω → ℝ) (A : Ω → Finset V) :
    presencePolynomial (subsetLaw μ A) ∅ =
      ∑ ω, MvPolynomial.C (μ ω : ℂ) * subsetMonomial (A ω) := by
  simp only [presencePolynomial, Finset.empty_subset, ite_true, Finset.sdiff_empty,
    subsetLaw, Complex.ofReal_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [apply_ite, Complex.ofReal_zero, map_zero, ite_mul, zero_mul]
  simp

omit [Fintype V] in
lemma subsetMonomial_image (π : Equiv.Perm V) (T : Finset V) :
    subsetMonomial (T.image π) = ∏ i ∈ T, MvPolynomial.X (π i) := by
  simp only [subsetMonomial]
  exact Finset.prod_image (fun i _ j _ h => π.injective h)

lemma subsetLaw_output (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (T : Finset V) :
    presencePolynomial (subsetLaw μ (fun ω => T.image (π ω))) ∅ =
      outputSymbol μ (fun ω => π ω) T := by
  rw [presencePolynomial_subsetLaw]
  simp only [subsetMonomial_image, outputSymbol]

theorem finite_output_return_bound (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (h₁ : ∑ ω, μ ω = 1) (hs : Stable (lawSymbol μ π))
    (T : Finset V) (hT : T.Nonempty) :
    (∑ ω, if T ⊆ T.image (π ω) then μ ω else 0) ≤
      ((∑ j ∈ T, ∑ ω, if j ∈ T.image (π ω) then μ ω else 0) / T.card) ^ T.card := by
  let ν := subsetLaw μ (fun ω => T.image (π ω))
  have hν : ∀ B, 0 ≤ ν B := subsetLaw_nonneg μ _ hμ
  have hν₁ : presence ν ∅ = 1 := by
    rw [presence_subsetLaw]
    simpa using h₁
  have hνs : Stable (presencePolynomial ν ∅) := by
    rw [subsetLaw_output]
    exact stable_outputSymbol μ π (by rw [h₁]; norm_num) hs T
  have hb := presence_mean_bound hν hν₁ hνs T hT
  simpa only [ν, presence_subsetLaw, Finset.singleton_subset_iff] using hb

end Heisenberg.Pin

noncomputable section
open scoped Classical
namespace Heisenberg.Cycle
open Equiv
variable {V : Type*} [Fintype V]

lemma missingCount_antitone (π : Perm V) {E P : Set V} (hEP : E ⊆ P) :
    missingCount π P ≤ missingCount π E := by
  apply Nat.card_le_card_of_injective
    (fun c : MissingClasses π P => (⟨c.val, fun i hi => c.property i (hEP hi)⟩ : MissingClasses π E))
  intro a b h
  exact Subtype.ext (congrArg (fun c : MissingClasses π E => c.val) h)

lemma missingCount_union_le (π : Perm V) (E : Set V) (T : Finset V) :
    missingCount π E ≤ missingCount π (E ∪ (T : Set V)) + T.card := by
  let _ : Fintype (Classes π) := Fintype.ofFinite _
  let A : Finset (Classes π) := Finset.univ.filter (fun c => ∀ i ∈ E, c ≠ classOf π i)
  let B : Finset (Classes π) := Finset.univ.filter (fun c => ∀ i ∈ E ∪ (T : Set V), c ≠ classOf π i)
  have hA : missingCount π E = A.card := by
    simp [missingCount, A, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hB : missingCount π (E ∪ (T : Set V)) = B.card := by
    simp [missingCount, B, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : A ⊆ B ∪ T.image (classOf π) := by
    intro c hc
    have hcE : ∀ i ∈ E, c ≠ classOf π i := (Finset.mem_filter.mp hc).2
    by_cases hcB : c ∈ B
    · exact Finset.mem_union_left _ hcB
    · apply Finset.mem_union_right
      have hh : ¬ ∀ i ∈ E ∪ (T : Set V), c ≠ classOf π i := by
        simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hcB
      push Not at hh
      obtain ⟨i, hi, he⟩ := hh
      rcases hi with hi | hi
      · exact False.elim (hcE i hi he)
      · exact Finset.mem_image.mpr ⟨i, hi, he.symm⟩
  rw [hA, hB]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_image_le) _))

theorem pin_weight_comparison (π : Perm V) (E : Set V) (T : Finset V) :
    (2 : ℝ) ^ missingCount π (E ∪ (T : Set V)) ≤ (2 : ℝ) ^ missingCount π E ∧
    (2 : ℝ) ^ missingCount π E ≤
      (2 : ℝ) ^ T.card * (2 : ℝ) ^ missingCount π (E ∪ (T : Set V)) := by
  constructor
  · exact pow_le_pow_right₀ (by norm_num) (missingCount_antitone π Set.subset_union_left)
  · calc
      (2 : ℝ) ^ missingCount π E ≤
          (2 : ℝ) ^ (missingCount π (E ∪ (T : Set V)) + T.card) :=
        pow_le_pow_right₀ (by norm_num) (missingCount_union_le π E T)
      _ = _ := by rw [pow_add, mul_comm]

end Heisenberg.Cycle

noncomputable section
open scoped Classical
namespace Heisenberg.Return
open Equiv
variable {V : Type*} [Fintype V]

theorem nextPoint_preserves_iff (π : Perm V) (E T : Set V)
    (hET : Disjoint E T) :
    (∀ i (hi : i ∈ T), (nextPoint π (E ∪ T) ⟨i, Or.inr hi⟩ : V) ∈ T) ↔
    ∀ i ∈ T, ¬ HasHit π E i := by
  constructor
  · intro hnext
    have hall (n : ℕ) : ∀ i ∈ T, (π ^ n) i ∉ E := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro i hi hE
        have hn : 0 < n := by
          by_contra h
          have hz : n = 0 := by omega
          rw [hz, pow_zero, Perm.one_apply] at hE
          exact Set.disjoint_left.mp hET hE hi
        let p : ↥(E ∪ T) := ⟨i, Or.inr hi⟩
        let m := nextTime π (E ∪ T) p
        have hm0 : 0 < m := nextTime_pos π (E ∪ T) p
        have hmn : m ≤ n := nextTime_min π (E ∪ T) p hn (Or.inl hE)
        have hlt : n - m < n := Nat.sub_lt hn hm0
        have hp : (nextPoint π (E ∪ T) p : V) ∈ T := hnext i hi
        have he : (π ^ (n - m)) (nextPoint π (E ∪ T) p : V) = (π ^ n) i := by
          rw [← nextPoint_spec, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hmn]
        exact ih _ hlt _ hp (he ▸ hE)
    intro i hi ⟨n, hn⟩
    exact hall n i hi hn
  · intro havoid i hi
    have hp := (nextPoint π (E ∪ T) ⟨i, Or.inr hi⟩).property
    rcases hp with hE | hT
    · exact False.elim (havoid i hi ⟨nextTime π (E ∪ T) ⟨i, Or.inr hi⟩,
        (nextPoint_spec π (E ∪ T) ⟨i, Or.inr hi⟩).symm ▸ hE⟩)
    · exact hT

omit [Fintype V] in
lemma subset_image_iff_mapsTo (π : Perm V) (T : Finset V) :
    T ⊆ T.image π ↔ ∀ i ∈ T, π i ∈ T := by
  have hc : (T.image π).card = T.card := Finset.card_image_of_injective T π.injective
  constructor
  · intro h i hi
    have he : T.image π = T := (Finset.eq_of_subset_of_card_le h (by omega)).symm
    rw [← he]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · intro h
    have hsub : T.image π ⊆ T := by
      rintro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact h i hi
    rw [Finset.eq_of_subset_of_card_le hsub (by omega)]

end Heisenberg.Return

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
attribute [-instance] Subtype.instDecidableEq
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

omit [Fintype V] in
lemma input_output_card (π : Equiv.Perm V) (T : Finset V) :
    (T.filter (fun j => j ∈ T.image π)).card =
      (T.filter (fun i => π i ∈ T)).card := by
  symm
  apply Finset.card_bij (fun i _ => π i)
  · intro i hi
    obtain ⟨hi, hπ⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hπ, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  · intro i _ j _ hij
    exact π.injective hij
  · intro j hj
    obtain ⟨hj, hmem⟩ := Finset.mem_filter.mp hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hj⟩, rfl⟩

omit [Fintype V] in
lemma input_output_sum (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (T : Finset V) :
    (∑ j ∈ T, ∑ ω, if j ∈ T.image (π ω) then μ ω else 0) =
      ∑ i ∈ T, ∑ ω, if π ω i ∈ T then μ ω else 0 := by
  rw [Finset.sum_comm, Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, input_output_card]

omit [Fintype V] in
lemma pinPartition_pos (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (P : Set V) :
    0 < pinPartition μ π P := by
  apply hpos.trans_le
  apply Finset.sum_le_sum
  intro ω _
  exact le_mul_of_one_le_right (hμ ω) (one_le_pow₀ (by norm_num))

omit [Fintype V] in
lemma pinDensity_nonneg (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (P : Set V) (ω : Ω) :
    0 ≤ pinDensity μ π P ω :=
  div_nonneg (mul_nonneg (hμ ω) (by positivity)) (pinPartition_pos μ π hμ hpos P).le

omit [Fintype V] in
lemma pinDensity_sum (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (P : Set V) :
    ∑ ω, pinDensity μ π P ω = 1 := by
  simp only [pinDensity, ← Finset.sum_div]
  change pinPartition μ π P / pinPartition μ π P = 1
  exact div_self (pinPartition_pos μ π hμ hpos P).ne'

lemma stable_pinDensity (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω)
    (hs : Stable (lawSymbol μ π)) (P : Set V) :
    Stable (lawSymbol (pinDensity μ π P) (fun ω => nextPermutation (π ω) P)) := by
  have he : lawSymbol (pinDensity μ π P) (fun ω => nextPermutation (π ω) P) =
      MvPolynomial.C ((pinPartition μ π P : ℂ)⁻¹) * pinLaw μ π P := by
    simp only [pinLaw, lawSymbol, pinDensity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    push_cast
    simp only [div_eq_mul_inv, map_mul]
    ring
  rw [he]
  intro z hz
  simp only [map_mul, MvPolynomial.eval_C]
  apply mul_ne_zero
  · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (pinPartition_pos μ π hμ hpos P).ne')
  · exact stable_pinLaw μ π hμ hpos hs P z hz

lemma finite_input_return_bound (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (h₁ : ∑ ω, μ ω = 1) (hs : Stable (lawSymbol μ π))
    (T : Finset V) (hT : T.Nonempty) :
    (∑ ω, if ∀ i ∈ T, π ω i ∈ T then μ ω else 0) ≤
      ((∑ i ∈ T, ∑ ω, if π ω i ∈ T then μ ω else 0) / T.card) ^ T.card := by
  have h := finite_output_return_bound μ π hμ h₁ hs T hT
  rw [input_output_sum] at h
  simpa only [subset_image_iff_mapsTo] using h

end Heisenberg.Pin
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical

namespace Heisenberg.Pin
attribute [-instance] Subtype.instDecidableEq
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

lemma pinDensity_comparison (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (E : Set V) (T : Finset V) (ω : Ω) :
    pinDensity μ π E ω ≤ (2 : ℝ) ^ T.card * pinDensity μ π (E ∪ (T : Set V)) ω := by
  have hZ : pinPartition μ π (E ∪ (T : Set V)) ≤ pinPartition μ π E := by
    apply Finset.sum_le_sum
    intro o _
    exact mul_le_mul_of_nonneg_left (pin_weight_comparison (π o) E T).1 (hμ o)
  have hn : μ ω * (2 : ℝ) ^ missingCount (π ω) E ≤
      (2 : ℝ) ^ T.card * (μ ω * (2 : ℝ) ^ missingCount (π ω) (E ∪ (T : Set V))) := by
    calc
      _ ≤ μ ω * ((2 : ℝ) ^ T.card * (2 : ℝ) ^ missingCount (π ω) (E ∪ (T : Set V))) :=
        mul_le_mul_of_nonneg_left (pin_weight_comparison (π ω) E T).2 (hμ ω)
      _ = _ := by ring
  have hμω := hμ ω
  unfold pinDensity
  rw [← mul_div_assoc]
  exact div_le_div₀ (by positivity) hn (pinPartition_pos μ π hμ hpos _) hZ

lemma testPins_event (π : Equiv.Perm V) (E : Set V) (T : Finset V)
    (hET : Disjoint E (T : Set V)) :
    (∀ i ∈ testPins E T, nextPermutation π (E ∪ (T : Set V)) i ∈ testPins E T) ↔
      ∀ i ∈ T, ¬ HasHit π E i := by
  refine Iff.trans ?_ (nextPoint_preserves_iff π E (T : Set V) hET)
  simp only [mem_testPins]
  constructor
  · intro h i hi
    exact h ⟨i, Or.inr hi⟩ hi
  · intro h i hi
    exact h i hi

lemma pinned_input_return_bound (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (hs : Stable (lawSymbol μ π))
    (P : Set V) (T : Finset P) (hT : T.Nonempty) :
    (∑ ω, if ∀ i ∈ T, nextPermutation (π ω) P i ∈ T then pinDensity μ π P ω else 0) ≤
      ((∑ i ∈ T, ∑ ω, if nextPermutation (π ω) P i ∈ T then pinDensity μ π P ω else 0)
        / T.card) ^ T.card := by
  have h := finite_input_return_bound (pinDensity μ π P)
    (fun ω => nextPermutation (π ω) P) (pinDensity_nonneg μ π hμ hpos P)
    (pinDensity_sum μ π hμ hpos P) (stable_pinDensity μ π hμ hpos hs P) T hT
  simpa only using h

theorem finite_simultaneous_pin_test (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (hs : Stable (lawSymbol μ π))
    (E : Set V) (T : Finset V) (hT : T.Nonempty) (hET : Disjoint E (T : Set V)) :
    (∑ ω, if ∀ i ∈ T, ¬ HasHit (π ω) E i then pinDensity μ π E ω else 0) ≤
      (2 * returnFraction μ π E T) ^ T.card := by
  have hTP : (testPins E T).Nonempty := by
    obtain ⟨i, hi⟩ := hT
    exact ⟨⟨i, Or.inr hi⟩, (mem_testPins E T _).mpr hi⟩
  have hb := pinned_input_return_bound μ π hμ hpos hs (E ∪ (T : Set V))
    (testPins E T) hTP
  simp only [testPins_event _ _ _ hET, card_testPins] at hb
  change (∑ ω, if ∀ i ∈ T, ¬ HasHit (π ω) E i then
    pinDensity μ π (E ∪ (T : Set V)) ω else 0) ≤ returnFraction μ π E T ^ T.card at hb
  calc
    _ ≤ ∑ ω, (2 : ℝ) ^ T.card * (if ∀ i ∈ T, ¬ HasHit (π ω) E i then
        pinDensity μ π (E ∪ (T : Set V)) ω else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      split_ifs
      · exact pinDensity_comparison μ π hμ hpos E T ω
      · simp
    _ = (2 : ℝ) ^ T.card * (∑ ω, if ∀ i ∈ T, ¬ HasHit (π ω) E i then
        pinDensity μ π (E ∪ (T : Set V)) ω else 0) := (Finset.mul_sum ..).symm
    _ ≤ (2 : ℝ) ^ T.card * returnFraction μ π E T ^ T.card :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := (mul_pow ..).symm

end Heisenberg.Pin

namespace Heisenberg.Pin
open Exposure
variable {V Ω Ψ : Type*} [Fintype V] [Fintype Ω] [Fintype Ψ]

lemma lawSymbol_reparam (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (e : Ψ ≃ Ω) :
    lawSymbol (μ ∘ e) (π ∘ e) = lawSymbol μ π := by
  exact e.sum_comp (fun ω => MvPolynomial.C (μ ω : ℂ) * permutationSymbol (π ω))

lemma stable_array (n : ℕ) (a b : Fin n → V) (p : Fin n → ℝ)
    (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) :
    Stable (lawSymbol (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => orderedProduct n (fun i => if c i then Equiv.swap (a i) (b i) else 1))) := by
  classical
  induction n with
  | zero => simpa [lawSymbol,orderedProduct] using stable_permutationSymbol (1 : Equiv.Perm V)
  | succ n ih =>
    have ht := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => p i.succ) (fun i => hp i.succ)
    have hh := stable_lawSymbol_bernoulli
      (fun c : Fin n → Bool => ∏ i,if c i then p i.succ else 1-p i.succ)
      (fun c => orderedProduct n (fun i => if c i then Equiv.swap (a i.succ) (b i.succ) else 1))
      ht (a 0) (b 0) (hp 0).1 (hp 0).2
    rw [←lawSymbol_reparam _ _ (splitArray n)] at hh
    convert hh using 1
    congr 1
    funext c
    exact Fin.prod_univ_succ _

end Heisenberg.Pin

namespace Heisenberg.LayeredExchange
attribute [-instance] instDecidableEqProd
open Exposure Pin Return
variable {V : Type*} [Fintype V]

theorem stable_wiring {n : ℕ} (s : Equiv.Perm (Fin n))
    (a b : Fin n → V) (p : Fin n → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) :
    Stable (lawSymbol (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => wiring s (fun i => if c i then Equiv.swap (a i) (b i) else 1))) := by
  classical
  have h := stable_array n (fun i => (i,a i)) (fun i => (i,b i)) p hp
  have hh := stable_rename_outputs h (Equiv.prodCongr s (Equiv.refl V))
  rw [←lawSymbol_deterministic_output] at hh
  convert hh using 1
  apply congrArg (lawSymbol _)
  funext c
  rw [wiring,fibers_ordered_product]
  congr 1
  congr 1
  funext i
  cases c i <;> simp only [Bool.false_eq_true,ite_false,ite_true,fibers_swap]
  · simp [fibers_one]
  · ext z <;> simp only [Equiv.swap_apply_def] <;> split_ifs <;> rfl

lemma layerWeight_nonneg {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) :
    ∀ c,0 ≤ layerWeight p c := by
  intro c
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [(hp i).1,(hp i).2]

lemma layerWeight_sum {n : ℕ} (p : Fin n → ℝ) : (∑ c,layerWeight p c)=1 := by
  unfold layerWeight
  rw [←Fintype.prod_sum (fun i (c : Bool) => if c then p i else 1-p i)]
  simp

lemma coinWiring_stable {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (p : Fin n → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) :
    Stable (lawSymbol (layerWeight p) (coinWiring s a b)) := stable_wiring s a b p hp

attribute [local irreducible] pinDensity returnFraction lawSymbol wiring fibers layerWeight coinWiring

end Heisenberg.LayeredExchange
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_TwoEndedReturns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Pin
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

theorem finite_pin_induction (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0 ≤ μ ω) (hpos : 0 < ∑ ω,μ ω) (hs : Stable (lawSymbol μ π))
    (E₀ : Set V) (admissible : Finset V → Prop) (p : ℝ) (_hp : 0 ≤ p)
    (hstep : ∀ E : Set V,E₀ ⊆ E → ∀ T : Finset V,T.Nonempty →
      admissible T → Disjoint E (T : Set V) →
      (∀ U : Finset V,admissible U → Disjoint (E∪(T:Set V)) (U:Set V) →
        (∑ ω,if ∀ i∈U,¬HasHit (π ω) (E∪(T:Set V)) i then
          pinDensity μ π (E∪(T:Set V)) ω else 0) ≤ p^U.card) →
      2*returnFraction μ π E T ≤ p) :
    ∀ E : Set V,E₀ ⊆ E → ∀ T : Finset V,admissible T → Disjoint E (T:Set V) →
      (∑ ω,if ∀ i∈T,¬HasHit (π ω) E i then pinDensity μ π E ω else 0) ≤ p^T.card := by
  classical
  let Good := fun E : Set V=>∀ T : Finset V,admissible T → Disjoint E (T:Set V) →
    (∑ ω,if ∀ i∈T,¬HasHit (π ω) E i then pinDensity μ π E ω else 0) ≤ p^T.card
  suffices h : ∀ n : ℕ,∀ E : Set V,(unpinned E).card=n → E₀⊆E → Good E by
    intro E hE
    exact h _ E rfl hE
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E hcard hE T hT hET
    by_cases hn : T.Nonempty
    · have hproper : unpinned (E∪(T:Set V)) ⊂ unpinned E := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro i hi
          have hh : i∉E ∧ i∉T := by simpa [unpinned] using hi
          simpa [unpinned] using hh.1
        · intro heq
          obtain ⟨j,hj⟩:=hn
          have hjE : j∉E := fun h=>Set.disjoint_left.mp hET h hj
          have hh : j∈unpinned (E∪(T:Set V)) := by rw [heq]; simpa [unpinned] using hjE
          have hh' : j∉T := (by simpa [unpinned] using hh : j∉E ∧ j∉T).2
          exact hh' hj
      have hlt : (unpinned (E∪(T:Set V))).card < n := by
        rw [←hcard]
        exact Finset.card_lt_card hproper
      have hgood : Good (E∪(T:Set V)) := ih _ hlt _ rfl
        (fun i hi=>Or.inl (hE hi))
      have hr:=hstep E hE T hn hT hET hgood
      have htest:=finite_simultaneous_pin_test μ π hμ hpos hs E T hn hET
      apply htest.trans
      apply pow_le_pow_left₀ _ hr
      apply mul_nonneg (by norm_num)
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro ω _
      split_ifs
      · exact pinDensity_nonneg μ π hμ hpos _ _
      · exact le_refl 0
    · have ht : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst T
      simpa using (pinDensity_sum μ π hμ hpos E).le

end Heisenberg.Pin

end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundaryWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {V : Type*} [Fintype V]

lemma cycle_boundary_witness (π : Equiv.Perm V) (B C : Set V)
    (hC : ∀ z,∃ n : ℕ,(π^n) z∈C) {z : V} (hz : z∈B) :
    ∃ w,π.SameCycle z w ∧ w∈B ∧ (w∈C ∨ π w∉B) := by
  by_contra hn
  have hn' : ∀ w,π.SameCycle z w → w∈B → w∉C ∧ π w∈B := by
    intro w hw hB
    constructor
    · intro hc; exact hn ⟨w,hw,hB,Or.inl hc⟩
    · by_contra hb; exact hn ⟨w,hw,hB,Or.inr hb⟩
  have hb : ∀ n : ℕ,(π^n) z∈B := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact (hn' _ ((Equiv.Perm.SameCycle.refl π z).pow_right (n:=n)) ih).2
  obtain ⟨n,hnC⟩:=hC z
  exact (hn' _ ((Equiv.Perm.SameCycle.refl π z).pow_right (n:=n)) (hb n)).1 hnC

attribute [local instance] OAI.Heisenberg.Surface.instFintypeClasses
lemma hitClasses_le_witnesses (π : Equiv.Perm V) (B C : Set V)
    (hC : ∀ z,∃ n : ℕ,(π^n) z∈C) :
    (hitClasses π B).card ≤ (witnesses π B C).card := by
  have hh : hitClasses π B⊆(witnesses π B C).image (classOf π) := by
    intro c hc
    obtain ⟨z,hz,rfl⟩:=(Finset.mem_filter.mp hc).2
    obtain ⟨w,hw,hB,hW⟩:=cycle_boundary_witness π B C hC hz
    refine Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hB,hW⟩,?_⟩
    exact ((classOf_eq_iff π z w).mpr hw).symm
  exact (Finset.card_le_card hh).trans Finset.card_image_le

lemma witness_count (π : Equiv.Perm V) (B C : Set V) :
    (witnesses π B C).card ≤ (Finset.univ.filter fun z=>z∈B∩C).card+
      (Finset.univ.filter fun z=>z∈B ∧ π z∉B).card := by
  apply le_trans (Finset.card_le_card (show witnesses π B C⊆
    (Finset.univ.filter fun z=>z∈B∩C)∪(Finset.univ.filter fun z=>z∈B ∧ π z∉B) from ?_))
    (Finset.card_union_le _ _)
  intro z hz
  rcases (Finset.mem_filter.mp hz).2 with ⟨hb,hc|he⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hc⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,he⟩)

lemma missing_add_hit (π : Equiv.Perm V) (B : Set V) :
    missingCount π B+(hitClasses π B).card=missingCount π ∅ := by
  have hmiss : missingCount π B=(Finset.univ.filter fun c : Classes π=>¬∃ z∈B,classOf π z=c).card := by
    unfold missingCount
    rw [Nat.card_eq_fintype_card]
    convert Fintype.card_subtype (fun c : Classes π=>∀ z∈B,c≠classOf π z) using 1
    congr 1
    ext c
    simp [not_exists,not_and,eq_comm]
  have hempty : missingCount π ∅=Fintype.card (Classes π) := by
    unfold missingCount
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _=>by simp))
  rw [hmiss,hempty]
  simpa [not_not,Finset.card_univ,hitClasses] using (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun c : Classes π=>¬∃ z∈B,classOf π z=c))

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundaryPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

lemma pin_weight_surface (π : Equiv.Perm V) (B : Set V) :
    (2:ℝ)^missingCount π B=(2:ℝ)^missingCount π ∅ *
      Real.exp (-(Real.log 2)*((hitClasses π B).card:ℝ)) := by
  have hpow : Real.exp (Real.log 2*((hitClasses π B).card:ℝ))=(2:ℝ)^(hitClasses π B).card := by
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [neg_mul,Real.exp_neg,hpow,←missing_add_hit π B,pow_add]
  field_simp

lemma partition_surface_identity (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (B : Set V) :
    pinPartition μ π B/pinPartition μ π ∅=
      ∑ ω,pinDensity μ π ∅ ω*Real.exp (-(Real.log 2)*((hitClasses (π ω) B).card:ℝ)) := by
  unfold pinPartition
  simp_rw [pin_weight_surface (B:=B)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  unfold pinDensity pinPartition
  ring

theorem partition_surface_lower (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (B : Set V)
    (C : ℝ) (hC : (∑ ω,pinDensity μ π ∅ ω*((hitClasses (π ω) B).card:ℝ))≤C) :
    Real.exp (-(Real.log 2)*C) ≤ pinPartition μ π B/pinPartition μ π ∅ := by
  have hj:=convexOn_exp.map_sum_le (t:=Finset.univ)
    (p:=fun ω=>-(Real.log 2)*((hitClasses (π ω) B).card:ℝ))
    (fun ω _=>pinDensity_nonneg μ π hμ hpos ∅ ω)
    (pinDensity_sum μ π hμ hpos ∅) (fun _ _=>Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have he : (∑ ω,pinDensity μ π ∅ ω*(-(Real.log 2)*((hitClasses (π ω) B).card:ℝ)))=
      -(Real.log 2)*(∑ ω,pinDensity μ π ∅ ω*((hitClasses (π ω) B).card:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [he,←partition_surface_identity μ π B] at hj
  apply (Real.exp_le_exp.mpr ?_).trans hj
  exact mul_le_mul_of_nonpos_left hC (neg_nonpos.mpr (Real.log_nonneg (by norm_num)))

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SlotColorTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Matrix.Norms.Operator
namespace Heisenberg.SlotColor
variable {V : Type*}

lemma permute_mul (π ρ : Equiv.Perm V) : permute (π*ρ) = permute π * permute ρ := by
  ext c i
  rfl

lemma permute_fixed (π : Equiv.Perm V) (c : Color (V:=V)) :
    permute π c = c ↔ ∀ i, c (π i) = c i := by
  constructor
  · intro h i
    have he := congrFun h (π i)
    simpa using he.symm
  · intro h
    ext i
    have he := h (π.symm i)
    simpa using he.symm

variable [Fintype V]

lemma matrix_one : matrix (1 : Equiv.Perm V) = 1 := by
  ext c b
  have he : permute (1 : Equiv.Perm V) b = b := by ext i; rfl
  simp [matrix,he,Matrix.one_apply,eq_comm]

lemma matrix_mul (π ρ : Equiv.Perm V) : matrix (π*ρ) = matrix π * matrix ρ := by
  ext c b
  simp only [matrix,Matrix.mul_apply,permute_mul,Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (permute ρ b)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

lemma trace_diagonal (π : Equiv.Perm V) (f : Color (V:=V) → ℝ) :
    Matrix.trace (matrix π * Matrix.diagonal f) =
      ∑ c, if ∀ i, c (π i) = c i then f c else 0 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_diagonal,matrix,permute_fixed]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

end Heisenberg.SlotColor
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinnedColors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V : Type*} [Fintype V]

attribute [local instance] OAI.Heisenberg.Surface.instFintypeMissingClasses
lemma card_pinnedColor (π : Equiv.Perm V) (P : Set V) :
    Fintype.card (PinnedColor π P)=2^missingCount π P := by
  rw [Fintype.card_congr (pinnedColorEquiv π P),Fintype.card_fun,Fintype.card_bool]
  rw [missingCount,Nat.card_eq_fintype_card]

lemma sum_halfSpin_bit {X : Type*} [Fintype X] (x : X) :
    (∑ ε : X → Bool,halfSpin (ε x))=0 := by
  let e : Equiv.Perm (X → Bool):=Equiv.piCongrRight (fun i=>if i=x then Equiv.boolNot else Equiv.refl Bool)
  have hn (ε : X → Bool) : halfSpin (e ε x)= -halfSpin (ε x) := by
    have he : e ε x= !(ε x) := by simp [e]
    rw [he]
    cases ε x <;> norm_num [halfSpin]
  have hh:=Equiv.sum_comp e (fun ε : X → Bool=>halfSpin (ε x))
  simp_rw [hn,Finset.sum_neg_distrib] at hh
  linarith

lemma missing_iff_nohit (π : Equiv.Perm V) (P : Set V) (i : V) :
    (∀ j∈P,classOf π i≠classOf π j) ↔ ¬HasHit π P i := by
  rw [hasHit_iff_cycle]
  simp only [not_exists,not_and]
  constructor
  · intro h j hj hs; exact h j hj ((classOf_eq_iff π i j).mpr hs)
  · intro h j hj he; exact h j hj ((classOf_eq_iff π i j).mp he)

theorem sum_pinned_spin (π : Equiv.Perm V) (P : Set V) (i : V) :
    (∑ c : PinnedColor π P,halfSpin (c.val i))=
      if HasHit π P i then (2:ℝ)^missingCount π P/2 else 0 := by
  rw [←(pinnedColorEquiv π P).symm.sum_comp (fun c=>halfSpin (c.val i))]
  by_cases hh : HasHit π P i
  · have hm : ¬∀ j∈P,classOf π i≠classOf π j := fun h=>(missing_iff_nohit π P i).mp h hh
    simp [hh,pinnedColorEquiv,hm,halfSpin,Fintype.card_bool,missingCount,
      Nat.card_eq_fintype_card,div_eq_mul_inv]
  · have hm:=(missing_iff_nohit π P i).mpr hh
    rw [ite_eq_right hh]
    change (∑ ε : MissingClasses π P → Bool, halfSpin (if h : ∀ j∈P,classOf π i≠classOf π j then ε ⟨classOf π i,h⟩ else true))=0
    simp only [dite_eq_left hm]
    with_reducible convert sum_halfSpin_bit (X:=MissingClasses π P) ⟨classOf π i,hm⟩ using 1
    congr! 20

theorem pinned_trace (π : Equiv.Perm V) (P : Set V) (f : (V → Bool) → ℝ) :
    Matrix.trace (SlotColor.matrix π * Matrix.diagonal (fun c=>if ∀ i∈P,c i=true then f c else 0))=
      ∑ c : PinnedColor π P,f c.val := by
  rw [SlotColor.trace_diagonal]
  have he : (∑ c : V → Bool,if ∀ i,c (π i)=c i then (if ∀ i∈P,c i=true then f c else 0) else 0)=
      ∑ c : V → Bool,if (∀ i,c (π i)=c i) ∧ (∀ i∈P,c i=true) then f c else 0 := by
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp_all
  rw [he,←Finset.sum_filter]
  exact Finset.sum_subtype _ (fun c=>by simp) f

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinnedMagnetization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

omit [Fintype V] in
lemma cutSpin_le (C : Finset V) (c : V → Bool) : cutSpin C c≤C.card/2 := by
  calc
    _ ≤ ∑ _i∈C,(1:ℝ)/2 := by
      apply Finset.sum_le_sum
      intro i _
      cases c i <;> norm_num [halfSpin]
    _ = _ := by simp [div_eq_mul_inv]

lemma sum_pinned_cutSpin (π : Equiv.Perm V) (P : Set V) (C : Finset V) :
    (∑ c : PinnedColor π P,cutSpin C c.val)=
      (2:ℝ)^missingCount π P/2 * ∑ i∈C,if HasHit π P i then (1:ℝ) else 0 := by
  unfold cutSpin
  rw [Finset.sum_comm]
  simp_rw [sum_pinned_spin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma pinned_color_normalization (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (P : Set V) :
    (∑ ω,∑ _c : PinnedColor (π ω) P,μ ω/pinPartition μ π P)=1 := by
  simp_rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_pinnedColor]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  have he : (∑ ω,(2:ℝ)^missingCount (π ω) P*μ ω)=pinPartition μ π P := by
    unfold pinPartition
    apply Finset.sum_congr rfl
    intro ω _
    ring
  simp_rw [←mul_div_assoc]
  rw [←Finset.sum_div,he,div_self (ne_of_gt (pinPartition_pos μ π hμ hpos P))]

lemma mean_pinned_cutSpin (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (P : Set V) (C : Finset V)
    (p : ℝ) (hmiss : ∀ i∈C,(∑ ω,if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0)≤p) :
    (1-p)*C.card/2 ≤ ∑ ω,∑ c : PinnedColor (π ω) P,
      μ ω/pinPartition μ π P*cutSpin C c.val := by
  have he : (∑ ω,∑ c : PinnedColor (π ω) P,μ ω/pinPartition μ π P*cutSpin C c.val)=
      (∑ i∈C,(1-(∑ ω,if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0))/2) := by
    simp_rw [←Finset.mul_sum,sum_pinned_cutSpin,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hh (ω : Ω) : μ ω/pinPartition μ π P*((2:ℝ)^missingCount (π ω) P/2 *
        (if HasHit (π ω) P i then 1 else 0))=
        (pinDensity μ π P ω-(if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0))/2 := by
      unfold pinDensity
      split_ifs <;> simp_all
      ring
    simp_rw [hh]
    rw [←Finset.sum_div,Finset.sum_sub_distrib,pinDensity_sum μ π hμ hpos P]
  rw [he]
  calc
    _ = ∑ _i∈C,(1-p)/2 := by simp [div_eq_mul_inv]; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi=>by linarith [hmiss i hi])

theorem pinned_cut_tail (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (P : Set V) (C : Finset V)
    (hC : C.Nonempty) (p : ℝ) (hp : p≤1/4)
    (hmiss : ∀ i∈C,(∑ ω,if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0)≤p) :
    (1:ℝ)/2 ≤ ∑ ω,∑ c : PinnedColor (π ω) P,
      if C.card/4≤cutSpin C c.val then μ ω/pinPartition μ π P else 0 := by
  have hZ:=pinPartition_pos μ π hμ hpos P
  have hmean:=mean_pinned_cutSpin μ π hμ hpos P C p hmiss
  have hn:=pinned_color_normalization μ π hμ hpos P
  have hu : (∑ ω,∑ c : PinnedColor (π ω) P,μ ω/pinPartition μ π P*cutSpin C c.val)≤
      C.card/4+(C.card/4)*(∑ ω,∑ c : PinnedColor (π ω) P,
      if C.card/4≤cutSpin C c.val then μ ω/pinPartition μ π P else 0) := by
    calc
      _ ≤ ∑ ω,∑ c : PinnedColor (π ω) P,((μ ω/pinPartition μ π P)*(C.card/4)+
          C.card/4*(if C.card/4≤cutSpin C c.val then μ ω/pinPartition μ π P else 0)) := by
        apply Finset.sum_le_sum
        intro ω _
        apply Finset.sum_le_sum
        intro c _
        have hw:=div_nonneg (hμ ω) hZ.le
        split_ifs with hh
        · have hh':=mul_le_mul_of_nonneg_left (cutSpin_le C c.val) hw
          nlinarith
        · have hh':=mul_le_mul_of_nonneg_left (le_of_not_ge hh) hw
          nlinarith
      _ = _ := by
        simp_rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
        rw [hn]
        ring
  have hcard : (0:ℝ)<C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hprod:=mul_le_mul_of_nonneg_right hp hcard.le
  nlinarith

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SurfaceTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

lemma pinned_sum_le_trace (π : Equiv.Perm V) (P : Set V) (f : (V → Bool) → ℝ)
    (hf : ∀ c,0≤f c) :
    (∑ c : PinnedColor π P,f c.val)≤Matrix.trace (SlotColor.matrix π * Matrix.diagonal f) := by
  rw [←pinned_trace,SlotColor.trace_diagonal,SlotColor.trace_diagonal]
  apply Finset.sum_le_sum
  intro c _
  split_ifs <;> simp_all

lemma normalized_pinned_tail (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (P : Set V) (C : Finset V) :
    (∑ ω,∑ c : PinnedColor (π ω) P,if C.card/4≤cutSpin C c.val then μ ω/pinPartition μ π P else 0)=
    (∑ ω,μ ω*∑ c : PinnedColor (π ω) P,if C.card/4≤cutSpin C c.val then (1:ℝ) else 0)/pinPartition μ π P := by
  simp_rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

theorem color_surface_tail (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (P : Set V) (C : Finset V)
    (hC : C.Nonempty) (p : ℝ) (hp : p≤1/4)
    (hmiss : ∀ i∈C,(∑ ω,if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0)≤p)
    (K : ℝ) (hK : (∑ ω,pinDensity μ π ∅ ω*((hitClasses (π ω) P).card:ℝ))≤K) :
    Real.exp (-(Real.log 2)*K)/2 ≤ colorTail μ π C/pinPartition μ π ∅ := by
  have hpin:=pinned_cut_tail μ π hμ hpos P C hC p hp hmiss
  rw [normalized_pinned_tail] at hpin
  have hZP:=pinPartition_pos μ π hμ hpos P
  have hZ0:=pinPartition_pos μ π hμ hpos ∅
  have hsum : (∑ ω,μ ω*∑ c : PinnedColor (π ω) P,if C.card/4≤cutSpin C c.val then (1:ℝ) else 0)≤colorTail μ π C := by
    apply Finset.sum_le_sum
    intro ω _
    exact mul_le_mul_of_nonneg_left (pinned_sum_le_trace (π ω) P (fun c=>if C.card/4≤cutSpin C c then 1 else 0) (fun c=>by split_ifs <;> norm_num)) (hμ ω)
  have hpin' : pinPartition μ π P/2≤colorTail μ π C := by
    have hh:=(le_div_iff₀ hZP).mp hpin
    linarith
  have hsurface:=partition_surface_lower μ π hμ hpos P K hK
  have hh:=div_le_div_of_nonneg_right hpin' hZ0.le
  rw [div_right_comm] at hh
  linarith

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CutColors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open Heisenberg.LayeredExchange
variable {V : Type*} [Fintype V]

attribute [local instance] OAI.cutDecEq
lemma trace_closed_colors (π : Equiv.Perm V) (f : (V → Bool) → ℝ) :
    Matrix.trace (SlotColor.matrix π*Matrix.diagonal f)=∑ c : SlotColor.ClosedColor π,f c.val := by
  rw [SlotColor.trace_diagonal,←Finset.sum_filter]
  exact Finset.sum_subtype _ (fun c=>by simp) f

theorem trace_wiring_cut (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (f : (V → Bool) → ℝ) :
    Matrix.trace (SlotColor.matrix (wiring (finRotate (n+1)) σ)*
      Matrix.diagonal (fun c=>f (fun v=>c (0,v))))=
    Matrix.trace (SlotColor.matrix (transport (finRotate (n+1)) σ 0 (n+1))*Matrix.diagonal f) := by
  have hleft:=trace_closed_colors (wiring (finRotate (n+1)) σ) (fun c=>f (fun v=>c (0,v)))
  have hright:=trace_closed_colors (transport (finRotate (n+1)) σ 0 (n+1)) f
  calc _ = ∑ c : SlotColor.ClosedColor (wiring (finRotate (n+1)) σ), f (fun v=>c.val (0,v)) := by
         with_reducible convert hleft using 1
       _ = ∑ c : SlotColor.ClosedColor (transport (finRotate (n+1)) σ 0 (n+1)),f c.val := by
         with_reducible convert (cutColorEquiv n σ).sum_comp (fun c=>f c.val) using 1
         congr! 20
       _ = _ := by with_reducible convert hright.symm using 1

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
attribute [-instance] instDecidableEqFin
namespace Heisenberg.Cycle
open Heisenberg.Return
variable {V : Type*} [Fintype V]
lemma missing_iff_not_hit (π : Equiv.Perm V) (P : Set V) (v : V) :
    v∈MissingSet π P ↔ ¬HasHit π P v := by
  simp only [MissingSet,Set.mem_ofPred_eq,hasHit_iff_cycle]
  simp only [not_exists,not_and,ne_eq,classOf_eq_iff]
end Heisenberg.Cycle

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return Heisenberg.Serial Heisenberg.SparseWitness
variable {V : Type} [Fintype V]

attribute [local instance] OAI.pinDecEq
omit [Fintype V] in
lemma coinWiring_eq_history {m : ℕ} (s : Equiv.Perm (Fin m)) (a b : Fin m → V) :
    LayeredExchange.coinWiring s a b=layerHistory s (fun i=>Equiv.swap (a i) (b i)) := by
  funext c
  apply congrArg (LayeredExchange.wiring s)
  funext i
  cases c i <;> rfl

omit [Fintype V] in
lemma layerMass_pinDensity {m : ℕ} (s : Equiv.Perm (Fin m)) (a b : Fin m → V)
    (P : Set (Fin m×V)) (p : Fin m → ℝ) (c : Fin m → Bool) :
    layerMass s a b P p c=pinDensity (LayeredExchange.layerWeight p)
      (LayeredExchange.coinWiring s a b) P c := by
  simp only [layerMass,layerPartition,layerWeight,pinDensity,pinPartition,LayeredExchange.layerWeight,Bernoulli.weight,layerHistory,LayeredExchange.coinWiring,swap_classical]

omit [Fintype V] in
lemma growth_subtype {X : Type} [PseudoMetricSpace X] (loc : V → X)
    (α L : ℝ) (J : Finset V) (hg : localGrowth loc α L J) :
    ∀ z r,0 ≤ r → ((Finset.univ.filter (fun j : J=>dist (loc j.val) z ≤ r)).card:ℝ) ≤ L*(1+r)^α := by
  intro z r hr
  have he : (Finset.univ.filter (fun j : J=>dist (loc j.val) z ≤ r)).card=
      (J.filter (fun j=>dist (loc j) z ≤ r)).card := by
    rw [←Finset.card_image_of_injective _ Subtype.val_injective]
    congr 1
    ext j
    simp [and_comm]
  rw [he]
  exact hg z r hr

lemma cut_moment_of_induction {X : Type} [PseudoMetricSpace X] {m : ℕ}
    (loc : V → X) (α L : ℝ) (s : Equiv.Perm (Fin m)) (a b : Fin m → V)
    (P : Set (Fin m×V)) (rates : Fin m → ℝ) (p : ℝ)
    (hIH : ∀ U : Finset (Fin m×V),cutAdmissible loc α L U → Disjoint P (U:Set (Fin m×V)) →
      (∑ c,if ∀ j∈U,¬HasHit (LayeredExchange.coinWiring s a b c) P j then
        pinDensity (LayeredExchange.layerWeight rates) (LayeredExchange.coinWiring s a b) P c else 0) ≤ p^U.card) :
    ∀ t U,localGrowth loc α L U → (∀ j∈U,(t,j)∉P) →
      (∑ c,if ∀ j∈U,(t,j)∈MissingSet (layerHistory s (fun i=>Equiv.swap (a i) (b i)) c) P then
        layerMass s a b P rates c else 0) ≤ p^U.card := by
  intro t U hU hP
  have hh:=hIH (U.image (fun j=>(t,j))) ⟨t,U,rfl,hU⟩ (by
    apply Set.disjoint_left.mpr
    intro z hz hzu
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hzu
    exact hP j hj hz)
  have hinj : Function.Injective (fun j : V=>(t,j)) := fun _ _ h=>(Prod.mk.inj h).2
  simpa only [Finset.card_image_of_injective _ hinj,Finset.forall_mem_image,
    missing_iff_not_hit,layerMass_pinDensity,layerHistory,LayeredExchange.coinWiring] using hh

lemma returnFraction_layer {m : ℕ} (s : Equiv.Perm (Fin m)) (a b : Fin m → V)
    (rates : Fin m → ℝ) (E : Set (Fin m×V)) (U : Finset (Fin m×V)) :
    returnFraction (LayeredExchange.layerWeight rates) (LayeredExchange.coinWiring s a b) E U=
      (∑ c,layerMass s a b (E∪(U:Set (Fin m×V))) rates c *
        returnCount (layerHistory s (fun i=>Equiv.swap (a i) (b i)) c) (E∪(U:Set (Fin m×V))) (testPins E U))/U.card := by
  unfold returnFraction returnCount
  rw [coinWiring_eq_history]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [layerMass_pinDensity,coinWiring_eq_history]
  split_ifs <;> simp_all only [mul_one,mul_zero]

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RegularPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
attribute [-instance] instDecidableEqFin
namespace Heisenberg.Exposure
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.LatticeRegular Heisenberg.SparseWitness Heisenberg.Cycle

attribute [local irreducible] Pin.pinDensity LayeredExchange.layerWeight LayeredExchange.coinWiring cutAdmissible layerMass layerHistory MissingSet Return.HasHit localGrowth

lemma exists_witness_scale : ∃ b : ℕ,100 ≤ b ∧ 2 ≤ (b:ℝ)^((1:ℝ)/100) := by
  obtain ⟨b,hb⟩:=exists_nat_ge (max (2^100:ℝ) 100)
  refine ⟨b,?_,?_⟩
  · exact_mod_cast (le_max_right _ _).trans hb
  · have hh:=Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 2^100)
        ((le_max_left _ _).trans hb) (by norm_num : (0:ℝ) ≤ 1/100)
    have he : ((2:ℝ)^100)^((1:ℝ)/100)=2 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
      norm_num
    rwa [he] at hh

attribute [local instance] OAI.regDecEq
theorem regularity_of_pin_induction (d M : ℕ) (L : ℝ) (hL : (2*(d+1):ℕ) ≤ L) :
    ∃ p₀>0,∃ C≥0,∀ (B : Type) [Fintype B] [Nonempty B]
      (Λ : Finset (Site (d+1))) (m : ℕ) (s : Equiv.Perm (Fin m))
      (a b : Fin m → Slots (B:=B) Λ) (P : Set (Fin m×Slots (B:=B) Λ))
      (rates : Fin m → ℝ) (_hrates : ∀ i,0≤rates i ∧ rates i≤1) (p : ℝ),
      0≤p → p≤p₀ →
      (∀ U : Finset (Fin m×Slots (B:=B) Λ),
        cutAdmissible (fun v : Slots (B:=B) Λ=>v.1.val) ((1:ℝ)/100) L U →
        Disjoint P (U:Set (Fin m×Slots (B:=B) Λ)) →
        (∑ c,if ∀ j∈U,¬Return.HasHit (LayeredExchange.coinWiring s a b c) P j then
          Pin.pinDensity (LayeredExchange.layerWeight rates) (LayeredExchange.coinWiring s a b) P c else 0) ≤ p^U.card) →
      ∀ t x R,(∑ c,layerMass s a b P rates c *
        (if ¬Regular (blocked Λ (holeCut s (fun i=>Equiv.swap (a i) (b i)) c P t)) x R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0)) ≤
          C*((1+(R:ℝ))^(d+1)*p^(2*(d+1))+1/(1+(R:ℝ))) := by
  obtain ⟨b,hb,hba⟩:=exists_witness_scale
  obtain ⟨p₀,hp₀,C,hC,hr⟩:=uniform_layer_regularity d M b hb ((1:ℝ)/100) L
    (1/(100*(d+1:ℝ))) 1 (by norm_num) hL hba (by positivity) (by norm_num)
  refine ⟨p₀,hp₀,C,hC,?_⟩
  intro B _ _ Λ m s a b P rates hrates p hp hpp hIH t x R
  have hcut:=cut_moment_of_induction (fun v : Slots (B:=B) Λ=>v.1.val) ((1:ℝ)/100) L s a b P rates p (by
    intro U hU hdis
    have h1:=hIH U
    have h2:=h1 hU
    have h3:=h2 hdis
    with_reducible convert h3 using 1 ; congr! 20) t
  have hh:=hr (Fin m) (Slots (B:=B) Λ) (fun v=>v.1.val) s a b P rates hrates t p hp hpp hcut x R
  simp only [layerBlocked_frame,Real.rpow_neg_one,←one_div,mul_ite,mul_one,mul_zero] at hh ⊢
  with_reducible convert hh using 1 ; congr! 20

end Heisenberg.Exposure
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BootstrapParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter Topology
namespace Heisenberg.Bootstrap

lemma nat_rpow_tendsto_zero (e : ℝ) (he : e < 0) :
    Tendsto (fun n : ℕ=>(n:ℝ)^e) atTop (𝓝 0) := by
  have hh:=tendsto_rpow_neg_atTop (neg_pos.mpr he)
  simpa only [Function.comp_def,neg_neg] using hh.comp (tendsto_natCast_atTop_atTop (R:=ℝ))

lemma exponent_split (x a b : ℝ) (hx : 0 < x) :
    x^a=x^b*x^(a-b) := by rw [←Real.rpow_add hx]; congr 1; ring

theorem choose_parameters (d : ℕ) (hd : 3 ≤ d) (M : ℕ)
    (B F G p₀ : ℝ) (_hB : 0 ≤ B) (hF : 0 ≤ F) (hG : 0 ≤ G) (hp₀ : 0 < p₀) :
    ∃ (p s : ℝ) (R : ℕ),0 < p ∧ p < 1/4 ∧ p ≤ p₀ ∧ 0 < s ∧
      s=p^(-(11/10:ℝ)) ∧ 1 ≤ R ∧ M ≤ R ∧ 8*B*Real.exp 1*s ≤ R ∧
      2*(G*((1+(R:ℝ))^d*p^(2*d)+1/(1+(R:ℝ)))+1/(1+(R:ℝ)))+
        8*F*(1+(R:ℝ))^((1:ℝ)/100)/s < p/4 := by
  obtain ⟨K,hK⟩:=exists_nat_gt (max (8*B*Real.exp 1) 1)
  have hK1 : 1 ≤ K := by
    have hh : (1:ℝ) < K := (le_max_right _ _).trans_lt hK
    exact_mod_cast hh.le
  have hKb : 8*B*Real.exp 1 ≤ K := (le_max_left _ _).trans hK.le
  let A:=2*G*((K:ℝ)+1)^d
  let C:=2*(G+1)
  let D:=8*F*((K:ℝ)+1)^((1:ℝ)/100)
  let e:ℝ:=(10/11:ℝ)-(9/11)*(d:ℝ)
  have he : e < 0 := by
    have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
    dsimp only [e]
    linarith
  have ht : Tendsto (fun n : ℕ=>A*(n:ℝ)^e+C*(n:ℝ)^(-(1/11:ℝ))+
      D*(n:ℝ)^(-(89/1100:ℝ))) atTop (𝓝 0) := by
    simpa using (((nat_rpow_tendsto_zero e he).const_mul A).add
      ((nat_rpow_tendsto_zero (-(1/11:ℝ)) (by norm_num)).const_mul C)).add
      ((nat_rpow_tendsto_zero (-(89/1100:ℝ)) (by norm_num)).const_mul D)
  have hp := nat_rpow_tendsto_zero (-(10/11:ℝ)) (by norm_num)
  have ev := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).and
    ((hp.eventually (gt_mem_nhds hp₀)).and
      ((hp.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).and
        (eventually_ge_atTop (max M 1))))
  obtain ⟨r,hrerror,hrp,hrsmall,hr⟩:=ev.exists
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr1
  have hrpos : 0 < (r:ℝ) := lt_of_lt_of_le zero_lt_one hrR
  let p:ℝ:=(r:ℝ)^(-(10/11:ℝ))
  let R:ℕ:=K*r
  have hp : 0 < p := Real.rpow_pos_of_pos hrpos _
  have hRr : r ≤ R := by dsimp [R]; nlinarith
  have hR : (r:ℝ) ≤ R := by exact_mod_cast hRr
  have hRup : 1+(R:ℝ) ≤ ((K:ℝ)+1)*r := by dsimp [R]; push_cast; nlinarith
  have hrpow : (r:ℝ)^d*p^(2*d)=(r:ℝ)^(-(9/11:ℝ)*(d:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_natCast p]
    dsimp only [p]
    rw [←Real.rpow_mul hrpos.le,←Real.rpow_add hrpos]
    congr 1
    push_cast
    ring
  have hreg : (1+(R:ℝ))^d*p^(2*d) ≤ ((K:ℝ)+1)^d*(r:ℝ)^(-(9/11:ℝ)*(d:ℝ)) := by
    calc
      _ ≤ (((K:ℝ)+1)*r)^d*p^(2*d) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hRup d) (by positivity)
      _ = _ := by rw [mul_pow,mul_assoc,hrpow]
  have htail : 1/(1+(R:ℝ)) ≤ (r:ℝ)^(-1:ℝ) := by
    rw [Real.rpow_neg_one]
    rw [←one_div]
    exact one_div_le_one_div_of_le hrpos (by linarith)
  have hflow : (1+(R:ℝ))^((1:ℝ)/100)/(r:ℝ) ≤
      ((K:ℝ)+1)^((1:ℝ)/100)*(r:ℝ)^(-(99/100:ℝ)) := by
    calc
      _ ≤ (((K:ℝ)+1)*r)^((1:ℝ)/100)/(r:ℝ) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hRup (by norm_num)) hrpos.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) hrpos.le,mul_div_assoc,←Real.rpow_sub_one hrpos.ne']
        congr 2
        norm_num
  refine ⟨p,(r:ℝ),R,hp,hrsmall,hrp.le,hrpos,?_,(hr1.trans hRr),?_,?_,?_⟩
  · dsimp only [p]
    rw [←Real.rpow_mul hrpos.le]
    norm_num
  · exact (le_max_left _ _).trans (hr.trans hRr)
  · dsimp [R]
    push_cast
    nlinarith
  · have hmain : 2*(G*((1+(R:ℝ))^d*p^(2*d)+1/(1+(R:ℝ)))+1/(1+(R:ℝ)))+
        8*F*(1+(R:ℝ))^((1:ℝ)/100)/(r:ℝ) ≤
        A*(r:ℝ)^(-(9/11:ℝ)*(d:ℝ))+C*(r:ℝ)^(-1:ℝ)+D*(r:ℝ)^(-(99/100:ℝ)) := by
      have h1:=mul_le_mul_of_nonneg_left hreg hG
      have h2:=mul_le_mul_of_nonneg_left htail hG
      have h3:=mul_le_mul_of_nonneg_left hflow (by positivity : 0 ≤ 8*F)
      dsimp only [A,C,D]
      rw [←mul_div_assoc] at h3
      nlinarith
    apply hmain.trans_lt
    have he' : (-(9/11:ℝ)*(d:ℝ))-(-(10/11:ℝ))=e := by dsimp [e]; ring
    rw [exponent_split (r:ℝ) (-(9/11:ℝ)*(d:ℝ)) (-(10/11:ℝ)) hrpos,
      exponent_split (r:ℝ) (-1:ℝ) (-(10/11:ℝ)) hrpos,
      exponent_split (r:ℝ) (-(99/100:ℝ)) (-(10/11:ℝ)) hrpos,he']
    have h1 : (-1:ℝ)-(-(10/11:ℝ))=-(1/11:ℝ) := by norm_num
    have h2 : (-(99/100:ℝ))-(-(10/11:ℝ))=-(89/1100:ℝ) := by norm_num
    rw [h1,h2]
    change _ < p/4
    calc
      _ = p*(A*(r:ℝ)^e+C*(r:ℝ)^(-(1/11:ℝ))+D*(r:ℝ)^(-(89/1100:ℝ))) := by dsimp [p]; ring
      _ < p*(1/4) := mul_lt_mul_of_pos_left hrerror hp
      _ = _ := by ring

end Heisenberg.Bootstrap
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin
namespace Heisenberg.Bootstrap
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular Heisenberg.Cycle Heisenberg.Pin

attribute [local irreducible] Pin.pinDensity LayeredExchange.layerWeight LayeredExchange.coinWiring Heisenberg.Exposure.layerMass Heisenberg.Exposure.layerHistory Heisenberg.Cycle.MissingSet Heisenberg.Return.HasHit Heisenberg.Exposure.exposedSweep

attribute [local instance] OAI.meshDecEq
lemma image_testPins {X : Type*} (E : Set X) (U : Finset X) :
    (testPins E U).image Subtype.val=U := by
  ext x
  simp only [Finset.mem_image,mem_testPins]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact hi
  · intro hx; exact ⟨⟨x,Or.inr hx⟩,hx,rfl⟩

theorem mesh_pin_bound (d : ℕ) (hd : 2≤d) (B : Type) [Fintype B] [Nonempty B]
    (L : ℝ) (hL : (2*(d+1):ℕ)≤L) :
    ∃ p s : ℝ,0<p ∧ p<1/4 ∧ 0<s ∧ s=p^(-(11/10:ℝ)) ∧
      ∀ (Λ F : Finset (Site (d+1))) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2),
        ∀ᶠ δ in 𝓝 (0:ℝ),0<δ →
        ∀ (N Q : ℕ) (_hQ : 0<Q) (_hqQ : q≤Q) (_hdiv : Q∣N+1)
          (a b : Fin (N+1) → Slots (B:=B) Λ)
          (_hab : ∀ j : Fin (N+1),j.val%Q<q → a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q))
          (_hsite : ∀ j : Fin (N+1),q≤j.val%Q → (a j).1.val=(b j).1.val)
          (rates : Fin (N+1) → ℝ) (_hp : ∀ j,0≤rates j ∧ rates j≤1)
          (_hrate : ∀ j : Fin (N+1),j.val%Q<q → rates j=δ/2),
          F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
          2*(⌊s/δ⌋₊+1)*Q ≤ N+1 →
          ∀ E : Set (Fin (N+1)×Slots (B:=B) Λ), (∀ z,z.2.1.val∉F → z∈E) →
          ∀ U : Finset (Fin (N+1)×Slots (B:=B) Λ),
          cutAdmissible (fun v : Slots (B:=B) Λ=>v.1.val) ((1:ℝ)/100) L U →
          Disjoint E (U:Set (Fin (N+1)×Slots (B:=B) Λ)) →
          (∑ c,if ∀ j∈U,¬Return.HasHit (LayeredExchange.coinWiring (finRotate (N+1)) a b c) E j then
            pinDensity (LayeredExchange.layerWeight rates) (LayeredExchange.coinWiring (finRotate (N+1)) a b) E c else 0) ≤ p^U.card := by
  have hL0 : 0≤L := le_trans (Nat.cast_nonneg _) hL
  obtain ⟨M,C,hC,hret⟩:=periodic_return_estimate d hd L hL0
  obtain ⟨p₀,hp₀,G,hG,hreg⟩:=regularity_of_pin_induction d M L hL
  obtain ⟨p,s,R,hp,hps,hpp,hs,hsp,hR1,_hRM,hclock,herr⟩:=
    choose_parameters (d+1) (by omega) M (4*(d+1)*(Fintype.card B)^2:ℕ) C G p₀
      (by positivity) hC hG hp₀
  refine ⟨p,s,hp,hps,hs,hsp,?_⟩
  intro Λ F q _ edge a₀ b₀ ha₀ hb₀
  let ρ : ℝ:=G*((1+(R:ℝ))^(d+1)*p^(2*(d+1))+1/(1+(R:ℝ)))
  filter_upwards [hret p s R ρ hp hs hR1 herr B Λ F q edge a₀ b₀ ha₀ hb₀ hclock] with δ hδret
  intro hδ N Q hQ hqQ hdiv a b hab hsite rates hrates hrate hF hframe hroom
  let E₀ : Set (Fin (N+1)×Slots (B:=B) Λ):={z | z.2.1.val∉F}
  let μ:=LayeredExchange.layerWeight rates
  let π:=LayeredExchange.coinWiring (finRotate (N+1)) a b
  have hμ : ∀ c,0≤μ c:=LayeredExchange.layerWeight_nonneg rates hrates
  have hpos : 0<∑ c,μ c := by
    have hsum : (∑ c,μ c)=1 := by
      with_reducible convert LayeredExchange.layerWeight_sum rates using 1
      congr! 20
    rw [hsum]
    norm_num
  have hstable : Stable (lawSymbol μ π) := by
    with_reducible convert LayeredExchange.coinWiring_stable (finRotate (N+1)) a b rates hrates using 1
    congr! 20
  have hh:=finite_pin_induction μ π hμ hpos hstable E₀
    (cutAdmissible (fun v : Slots (B:=B) Λ=>v.1.val) ((1:ℝ)/100) L) p hp.le ?_
  · intro E hE U hU hdis
    have hEE : E₀⊆E := by intro z hz; exact hE z hz
    with_reducible convert hh E hEE U hU hdis using 1
    congr! 20
  · intro E hE U hUne hU hdis hIH
    obtain ⟨t,J,rfl,hg⟩:=hU
    have hinj : Function.Injective (fun j : Slots (B:=B) Λ=>(t,j)):=fun _ _ h=>(Prod.mk.inj h).2
    have hJpos : J.Nonempty := by simpa only [Finset.image_nonempty] using hUne
    let U:=J.image (fun j=>(t,j))
    let P:=E∪(U:Set (Fin (N+1)×Slots (B:=B) Λ))
    have hdis' : Disjoint E (U:Set (Fin (N+1)×Slots (B:=B) Λ)) := by
      with_reducible convert hdis using 1
      congr! 20
    have hJP : ∀ j∈J,(t,j)∈P := by
      intro j hj
      exact Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    have hJF : ∀ j∈J,j.1.val∈F := by
      intro j hj
      by_contra hn
      have he : (t,j)∈E := hE hn
      exact Set.disjoint_left.mp hdis' he (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    have hP : ∀ z,z.2.1.val∉F → z∈P := fun z hz=>Or.inl (hE hz)
    have hTJ : (testPins E U).image Subtype.val=Heisenberg.Serial.targetsAt N t J := by
      with_reducible convert image_testPins E U using 1
      · congr! 20
      · unfold Heisenberg.Serial.targetsAt U
        congr! 20
    have hb : ∀ u x,(∑ c,layerMass (finRotate (N+1)) a b P rates c *
      (if ¬Regular (blocked Λ (holeCut (finRotate (N+1)) (fun i=>Equiv.swap (a i) (b i)) c P u))
        x R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0))≤ρ := by
      intro u x
      have hr:=hreg B Λ (N+1) (finRotate (N+1)) a b P rates hrates p hp.le hpp ?_ u x R
      · with_reducible convert hr using 1
      · intro V hV hv
        have hv' : Disjoint (E∪((J.image (fun j=>(t,j))):Set (Fin (N+1)×Slots (B:=B) Λ))) (V:Set (Fin (N+1)×Slots (B:=B) Λ)) := by
          with_reducible convert hv using 1
        with_reducible convert hIH V hV (by with_reducible convert hv' using 1; congr! 20) using 1
        congr! 20
    have hcount:=hδret hδ N Q hQ hqQ hdiv a b hab hsite rates hrates hrate P hP t (testPins E U) J
      (by with_reducible convert hTJ using 1) hJpos hJF hJP hF hframe
      (by with_reducible convert growth_subtype _ _ _ J hg using 1) hroom (by with_reducible convert hb using 1)
    rw [returnFraction_layer]
    have hfinal : 2*((∑ c,layerMass (finRotate (N+1)) a b P rates c *
      returnCount (layerHistory (finRotate (N+1)) (fun i=>Equiv.swap (a i) (b i)) c) P (testPins E U))/U.card)≤p := by
      have hcard : U.card=J.card := Finset.card_image_of_injective _ hinj
      rw [hcard]
      have hcardpos : (0:ℝ)<J.card := by exact_mod_cast Finset.card_pos.mpr hJpos
      have hdivcount:=(div_le_iff₀ hcardpos).mpr hcount
      nlinarith
    with_reducible convert hfinal using 1
    congr! 20

end Heisenberg.Bootstrap
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundaryMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Exposure
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype V] in
lemma swap_preserves_boundary (a b : V) (D : Set V) (h : a∈D ↔ b∈D) (v : V) :
    Equiv.swap a b v ∈ D ↔ v∈D := by
  simp only [Equiv.swap_apply_def]
  split_ifs with h₁ h₂
  · subst v; exact h.symm
  · subst v; exact h
  · rfl

theorem mesh_boundary_count (s : Equiv.Perm T) (a b : T → V) (D : Set V)
    (K : Finset T) (hK : ∀ t,t∉K → (a t∈D ↔ b t∈D))
    (t₀ : T) (hs : ∀ t,∃ n : ℕ,(s^n) t=t₀) (c : T → Bool) :
    (hitClasses (layerHistory s (fun t=>Equiv.swap (a t) (b t)) c) {z | z.2∈D}).card ≤
      (Finset.univ.filter fun v : V=>v∈D).card+2*(K.filter fun t=>c t=true).card := by
  let π:=layerHistory s (fun t=>Equiv.swap (a t) (b t)) c
  let B : Set (T×V):={z | z.2∈D}
  let C : Set (T×V):={z | z.1=t₀}
  have hC : ∀ z,∃ n : ℕ,(π^n) z∈C := by
    intro z
    obtain ⟨n,hn⟩:=hs z.1
    refine ⟨n,?_⟩
    change ((wiring s (fun t=>if c t then Equiv.swap (a t) (b t) else 1)^n) z).1=t₀
    rw [wiring_pow]
    exact hn
  have hn:=(hitClasses_le_witnesses π B C hC).trans (witness_count π B C)
  have hbase : (Finset.univ.filter fun z : T×V=>z∈B∩C).card=
      (Finset.univ.filter fun v : V=>v∈D).card := by
    have he : (Finset.univ.filter fun z : T×V=>z∈B∩C)=
        (Finset.univ.filter fun v : V=>v∈D).image (fun v=>(t₀,v)) := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_inter_iff,
        Finset.mem_image,B,C,Set.mem_ofPred_eq]
      aesop
    rw [he,Finset.card_image_of_injective _ (fun _ _ h=>(Prod.mk.inj h).2)]
  have hsub : (Finset.univ.filter fun z : T×V=>z∈B ∧ π z∉B) ⊆
      (K.filter fun t=>c t=true).biUnion (fun t=>{(t,a t),(t,b t)}) := by
    intro z hz
    obtain ⟨hzD,hout⟩:=(Finset.mem_filter.mp hz).2
    have hout' : (if c z.1 then Equiv.swap (a z.1) (b z.1) z.2 else z.2)∉D := by
      change ((if c z.1 then Equiv.swap (a z.1) (b z.1) else 1) z.2)∉D at hout
      by_cases hh : c z.1=true <;> simpa [hh] using hout
    have hc : c z.1=true := by
      by_contra hc
      have hh : z.2∉D := by simpa [hc] using hout'
      exact hh hzD
    have hKz : z.1∈K := by
      by_contra hnK
      have hh:=(swap_preserves_boundary (a z.1) (b z.1) D (hK z.1 hnK) z.2).mpr hzD
      simp only [hc,ite_true] at hout'
      exact hout' hh
    have hzab : z.2=a z.1 ∨ z.2=b z.1 := by
      by_contra hh
      have hh':=not_or.mp hh
      simp only [hc,ite_true,Equiv.swap_apply_of_ne_of_ne hh'.1 hh'.2] at hout'
      exact hout' hzD
    refine Finset.mem_biUnion.mpr ⟨z.1,Finset.mem_filter.mpr ⟨hKz,hc⟩,?_⟩
    rcases hzab with h|h <;> simp [←h]
  have hexit : (Finset.univ.filter fun z : T×V=>z∈B ∧ π z∉B).card≤
      2*(K.filter fun t=>c t=true).card := by
    apply (Finset.card_le_card hsub).trans
    apply (Finset.card_biUnion_le).trans
    calc
      _ ≤ ∑ _t∈K.filter (fun t=>c t=true),2 := by
        apply Finset.sum_le_sum
        intro t _
        simpa using Finset.card_insert_le (t,a t) {(t,b t)}
      _ = _ := by simp [Nat.mul_comm]
  rw [hbase] at hn
  exact hn.trans (Nat.add_le_add_left hexit _)

lemma mean_active_marks (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (K : Finset T) :
    (∑ c,layerMass s a b P p c * ((K.filter fun t=>c t=true).card:ℝ)) ≤ ∑ t∈K,2*p t := by
  have he (c : T → Bool) : ((K.filter fun t=>c t=true).card:ℝ)=
      ∑ t∈K,if c t=true then (1:ℝ) else 0 := by simp
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  have hh:=layer_factorial_bound s a b P p hp {t}
  simpa only [Finset.mem_singleton,forall_eq,Finset.prod_singleton,mul_ite,mul_one,mul_zero] using hh

theorem mean_boundary_cycles (s : Equiv.Perm T) (a b : T → V) (D : Set V)
    (K : Finset T) (hK : ∀ t,t∉K → (a t∈D ↔ b t∈D))
    (t₀ : T) (hs : ∀ t,∃ n : ℕ,(s^n) t=t₀)
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (P : Set (T×V)) :
    (∑ c,layerMass s a b P p c *
      ((hitClasses (layerHistory s (fun t=>Equiv.swap (a t) (b t)) c) {z | z.2∈D}).card:ℝ)) ≤
      (Finset.univ.filter fun v : V=>v∈D).card+4*∑ t∈K,p t := by
  have hb : (∑ c,layerMass s a b P p c *
      ((hitClasses (layerHistory s (fun t=>Equiv.swap (a t) (b t)) c) {z | z.2∈D}).card:ℝ)) ≤
      ∑ c,layerMass s a b P p c *
      ((Finset.univ.filter fun v : V=>v∈D).card+2*((K.filter fun t=>c t=true).card:ℝ)) := by
    apply Finset.sum_le_sum
    intro c _
    apply mul_le_mul_of_nonneg_left _ (layerMass_nonneg s a b P p hp c)
    exact_mod_cast mesh_boundary_count s a b D K hK t₀ hs c
  simp_rw [mul_add,Finset.sum_add_distrib,←mul_assoc] at hb
  rw [←Finset.sum_mul,layerMass_sum s a b P p hp,one_mul] at hb
  have he : (∑ c,layerMass s a b P p c * 2 * ((K.filter fun t=>c t=true).card:ℝ))=
      2*∑ c,layerMass s a b P p c * ((K.filter fun t=>c t=true).card:ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [he] at hb
  have hm:=mean_active_marks s a b P p hp K
  rw [←Finset.mul_sum] at hm
  linarith

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return Heisenberg.LayeredExchange Heisenberg.Exposure Heisenberg.LatticeRegular Heisenberg.SpatialFrame Heisenberg.Geometry

lemma growth_singleton {X Y : Type*} [PseudoMetricSpace X] (loc : Y → X)
    (α L : ℝ) (hα : 0≤α) (hL : 1≤L) (y : Y) : localGrowth loc α L {y} := by
  intro x r hr
  have hh : (1:ℝ)≤(1+r)^α := Real.one_le_rpow (by linarith) hα
  have hc : ((({y}:Finset Y).filter fun v=>dist (loc v) x≤r).card:ℝ)≤1 := by
    exact_mod_cast (Finset.card_filter_le ({y}:Finset Y) _)
  exact hc.trans (by nlinarith)

lemma rotation_reaches_zero (n : ℕ) (t : Fin (n+1)) : ∃ k : ℕ,((finRotate (n+1))^k) t=0 := by
  have h : (finRotate (n+1)).SameCycle 0 t := by
    refine ⟨(t.val:ℤ),?_⟩
    rw [zpow_natCast,rotate_pow_zero]
    simp
  exact h.symm.exists_nat_pow_eq

attribute [local instance] OAI.surfaceDecEq
lemma pinPartition_empty_trace {V Ω : Type*} [Fintype V] [Fintype Ω]
    (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) :
    pinPartition μ π ∅=∑ ω,μ ω*Matrix.trace (SlotColor.matrix (π ω)) := by
  unfold pinPartition
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  have hh:=pinned_trace (π ω) ∅ (fun _=>1)
  have hcard:=card_pinnedColor (π ω) ∅
  simpa only [Set.mem_empty_iff_false,IsEmpty.forall_iff,implies_true,ite_true,
    Matrix.diagonal_one,Matrix.mul_one,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,hcard,Nat.cast_pow,Nat.cast_ofNat] using hh.symm

lemma cut_card {V : Type*} [Fintype V] (n : ℕ) :
    (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v))).card=Fintype.card V := by
  rw [Finset.card_image_of_injective _ (fun _ _ h=>(Prod.mk.inj h).2),Finset.card_univ]

lemma cut_spin {V : Type*} [Fintype V] (n : ℕ) (c : Fin (n+1)×V → Bool) :
    cutSpin (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v))) c=SlotColor.magnetization (fun v=>c (0,v)) := by
  rw [cutSpin,Finset.sum_image (fun _ _ _ _ h=>(Prod.mk.inj h).2)]
  rfl

attribute [local irreducible] colorTail coinWiring Heisenberg.LayeredExchange.layerWeight pinDensity

theorem mesh_surface_tail (d : ℕ) (hd : 2≤d) (B : Type) [Fintype B] [Nonempty B] :
    ∃ p s : ℝ,0<p ∧ p<1/4 ∧ 0<s ∧ s=p^(-(11/10:ℝ)) ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2),
        ∀ᶠ δ in 𝓝 (0:ℝ),0<δ →
        ∀ (N Q : ℕ) (_hQ : 0<Q) (_hqQ : q≤Q) (_hdiv : Q∣N+1)
          (a b : Fin (N+1) → Slots (B:=B) Λ)
          (_hab : ∀ j : Fin (N+1),j.val%Q<q → a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q))
          (_hsite : ∀ j : Fin (N+1),q≤j.val%Q → (a j).1.val=(b j).1.val)
          (rates : Fin (N+1) → ℝ) (_hp : ∀ j,0≤rates j ∧ rates j≤1)
          (_hrate : ∀ j : Fin (N+1),j.val%Q<q → rates j=δ/2),
          F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
          2*(⌊s/δ⌋₊+1)*Q ≤ N+1 →
          let K:=Finset.univ.filter (fun j : Fin (N+1)=>j.val%Q<q ∧ ((a j).1.val∉F ∨ (b j).1.val∉F))
          let C:=Finset.univ.image (fun v : Slots (B:=B) Λ=>((0:Fin (N+1)),v))
          Real.exp (-(Real.log 2)*(((Finset.univ.filter (fun v : Slots (B:=B) Λ=>v.1.val∉F)).card:ℝ)+2*δ*K.card))/2 ≤
            colorTail (layerWeight rates) (coinWiring (finRotate (N+1)) a b) C/
              pinPartition (layerWeight rates) (coinWiring (finRotate (N+1)) a b) ∅ := by
  obtain ⟨p,s,hp,hpq,hs,hsp,hbound⟩:=Heisenberg.Bootstrap.mesh_pin_bound d hd B (2*(d+1):ℕ) (by rfl)
  refine ⟨p,s,hp,hpq,hs,hsp,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀
  filter_upwards [hbound Λ F q edge a₀ b₀ ha₀ hb₀] with δ hδ
  intro hδpos N Q hQ hqQ hdiv a b hab hsite rates hrates hrate hF hframe hroom K C
  let D : Set (Slots (B:=B) Λ):={v | v.1.val∉F}
  let P : Set (Fin (N+1)×Slots (B:=B) Λ):={z | z.2∈D}
  let μ:=layerWeight rates
  let π:=coinWiring (finRotate (N+1)) a b
  have hμ:=layerWeight_nonneg rates hrates
  have hpos : 0<∑ c,μ c := by
    have hh:=layerWeight_sum rates
    with_reducible convert (show (0:ℝ)<1 by norm_num) using 1
    with_reducible convert hh using 1
    congr! 20
  have hC : C.Nonempty := by
    obtain ⟨x,hx⟩:=hΛ
    exact Finset.image_nonempty.mpr ⟨(⟨x,hx⟩,Classical.choice (inferInstance : Nonempty B)),Finset.mem_univ _⟩
  apply color_surface_tail μ π hμ hpos P C hC p hpq.le
  · intro i _
    by_cases hi : i∈P
    · simp only [hasHit_of_mem (π _) hi,not_true_eq_false,ite_false,Finset.sum_const_zero]
      exact hp.le
    · have hh:=hδ hδpos N Q hQ hqQ hdiv a b hab hsite rates hrates hrate hF hframe hroom P
        (fun z hz=>hz) {i} ?_ ?_
      · simpa only [Finset.mem_singleton,forall_eq,Finset.card_singleton,pow_one] using hh
      · refine ⟨i.1,{i.2},by simp,?_⟩
        exact growth_singleton _ _ _ (by norm_num) (by exact_mod_cast (show 1≤2*(d+1) by omega)) _
      · simpa only [Finset.coe_singleton] using Set.disjoint_singleton_right.mpr hi
  · have hK : ∀ t,t∉K → (a t∈D ↔ b t∈D) := by
      intro t ht
      by_cases hspatial : t.val%Q<q
      · have hh : (a t).1.val∈F ∧ (b t).1.val∈F := by
          simpa only [K,Finset.mem_filter,Finset.mem_univ,true_and,hspatial,true_and,not_or,not_not] using ht
        simp [D,hh.1,hh.2]
      · change ((a t).1.val∉F)↔((b t).1.val∉F)
        rw [hsite t (by omega)]
    have hh:=mean_boundary_cycles (finRotate (N+1)) a b D K hK 0 (rotation_reaches_zero N) rates hrates ∅
    have hr : (∑ t∈K,rates t)=δ/2*K.card := by
      calc _ = ∑ _t∈K,δ/2 := by
             apply Finset.sum_congr rfl
             intro t ht
             exact hrate t (Finset.mem_filter.mp ht).2.1
           _ = _ := by simp; ring
    rw [hr] at hh
    simp_rw [layerMass_pinDensity] at hh
    have he : (4:ℝ)*(δ/2*K.card)=2*δ*K.card := by ring
    rw [he] at hh
    dsimp only [μ,π,P,D]
    dsimp only [D] at hh
    with_unfolding_all convert hh using 1 <;> congr! 20
    all_goals exact Exposure.coinWiring_eq_history _ _ _

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open LayeredExchange
variable {V : Type} [Fintype V]

attribute [local instance] OAI.meshProductDecEq
lemma transport_matrix_prefix (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (k : ℕ) :
    SlotColor.matrix (transport (finRotate (n+1)) σ 0 k)=
      MeshPair.prefixMatrix (fun j : ℕ=>SlotColor.matrix (σ (j : Fin (n+1)))) k := by
  induction k with
  | zero=>exact SlotColor.matrix_one
  | succ k ih=>rw [transport_succ_zero,SlotColor.matrix_mul,MeshPair.prefixMatrix,ih]

lemma transport_matrix_product (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) :
    SlotColor.matrix (transport (finRotate (n+1)) σ 0 (n+1))=
      Serial.product (n+1) (fun j=>SlotColor.matrix (σ j)) := by
  rw [transport_matrix_prefix]
  have hh:=Serial.prefix_product (fun j : ℕ=>SlotColor.matrix (σ (j : Fin (n+1)))) (n+1)
  with_reducible convert hh using 1; congr! 10
  simp

lemma mean_transport (n : ℕ) (a b : Fin (n+1) → V) (rates : Fin (n+1) → ℝ) :
    (∑ c : Fin (n+1) → Bool,layerWeight rates c •
      SlotColor.matrix (transport (finRotate (n+1)) (fun t=>if c t then Equiv.swap (a t) (b t) else 1) 0 (n+1)))=
    Serial.product (n+1) (fun j=>colorCoin (a j) (b j) (rates j)) := by
  simp_rw [transport_matrix_product]
  unfold layerWeight
  have hh:=Serial.mean_product (V:=V → Bool) (n+1)
    (fun (j : Fin (n+1)) (z : Bool)=>if z then rates j else 1-rates j)
    (fun j z=>SlotColor.matrix (if z then Equiv.swap (a j) (b j) else 1))
  change _=_ at hh
  with_reducible convert hh using 1 <;> congr! 5
  all_goals simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false,SlotColor.matrix_one,colorCoin]
  all_goals first | rfl | exact add_comm _ _

lemma trace_mean_test {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ)
    (M : Ω → Matrix V V ℝ) (D : Matrix V V ℝ) :
    (∑ ω,μ ω*Matrix.trace (M ω*D))=Matrix.trace ((∑ ω,μ ω • M ω)*D) := by
  simp only [Finset.sum_mul,Matrix.smul_mul,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul]

theorem mesh_trace_product (n : ℕ) (a b : Fin (n+1) → V) (rates : Fin (n+1) → ℝ)
    (f : (V → Bool) → ℝ) :
    (∑ c : Fin (n+1) → Bool,layerWeight rates c * Matrix.trace
      (SlotColor.matrix (coinWiring (finRotate (n+1)) a b c)*Matrix.diagonal (fun x=>f (fun v=>x (0,v)))))=
    Matrix.trace (Serial.product (n+1) (fun j=>colorCoin (a j) (b j) (rates j))*Matrix.diagonal f) := by
  unfold coinWiring
  simp_rw [trace_wiring_cut]
  rw [trace_mean_test,mean_transport]

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshCutProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open LayeredExchange
variable {V : Type} [Fintype V]

attribute [local instance] OAI.meshCPDecEq
lemma cut_test_eq (n : ℕ) :
    (fun c : Fin (n+1)×V → Bool=>if (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v))).card/4≤
      cutSpin (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v))) c then (1:ℝ) else 0)=
    (fun c : Fin (n+1)×V → Bool=>if (Fintype.card V:ℝ)/4≤SlotColor.magnetization (fun v=>c (0,v)) then (1:ℝ) else 0) := by
  funext c
  rw [cut_card,cut_spin]

attribute [local irreducible] colorTail coinWiring layerWeight
lemma mesh_cut_product (n : ℕ) (a b : Fin (n+1) → V) (rates : Fin (n+1) → ℝ) :
    colorTail (layerWeight rates) (coinWiring (finRotate (n+1)) a b)
      (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v)))=
    Matrix.trace (Serial.product (n+1) (fun j=>colorCoin (a j) (b j) (rates j))*
      Matrix.diagonal (fun c : V → Bool=>if (Fintype.card V:ℝ)/4≤SlotColor.magnetization c then (1:ℝ) else 0)) := by
  unfold colorTail
  rw [cut_test_eq]
  exact mesh_trace_product n a b rates (fun c : V → Bool=>if (Fintype.card V:ℝ)/4≤SlotColor.magnetization c then (1:ℝ) else 0)

lemma mesh_partition_product (n : ℕ) (a b : Fin (n+1) → V) (rates : Fin (n+1) → ℝ) :
    Heisenberg.Pin.pinPartition (layerWeight rates) (coinWiring (finRotate (n+1)) a b) ∅=
    Matrix.trace (Serial.product (n+1) (fun j=>colorCoin (a j) (b j) (rates j))) := by
  rw [pinPartition_empty_trace]
  have hh:=mesh_trace_product n a b rates (fun _=>1)
  simpa only [Matrix.diagonal_one,Matrix.mul_one] using hh

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshMatrixSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open Heisenberg.Cycle Pin Return LayeredExchange Exposure LatticeRegular SpatialFrame Heisenberg.Geometry

attribute [local instance] OAI.matrixSurfaceDecEq
theorem mesh_matrix_surface_oai (d : ℕ) (hd : 2≤d) (B : Type) [Fintype B] [Nonempty B] :
    ∃ s : ℝ,0<s ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2),
        ∀ᶠ δ in 𝓝 (0:ℝ),0<δ →
        ∀ (L Q : ℕ) (_hL : 0<L) (_hQ : 0<Q) (_hqQ : q≤Q) (_hdiv : Q∣L)
          (a b : Fin L → Slots (B:=B) Λ)
          (_hab : ∀ j : Fin L,j.val%Q<q → a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q))
          (_hsite : ∀ j : Fin L,q≤j.val%Q → (a j).1.val=(b j).1.val)
          (rates : Fin L → ℝ) (_hp : ∀ j,0≤rates j ∧ rates j≤1)
          (_hrate : ∀ j : Fin L,j.val%Q<q → rates j=δ/2),
          F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
          2*(⌊s/δ⌋₊+1)*Q ≤ L →
          let K:=Finset.univ.filter (fun j : Fin L=>j.val%Q<q ∧ ((a j).1.val∉F ∨ (b j).1.val∉F))
          let T:=Serial.product L (fun j=>colorCoin (a j) (b j) (rates j))
          Real.exp (-(Real.log 2)*(((Finset.univ.filter (fun v : Slots (B:=B) Λ=>v.1.val∉F)).card:ℝ)+2*δ*K.card))/2 *
            Matrix.trace T ≤ Matrix.trace (T*tailProjection (Slots (B:=B) Λ)) := by
  obtain ⟨p,s,_hp,_hpq,hs,_hsp,hbound⟩:=mesh_surface_tail d hd B
  refine ⟨s,hs,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀
  filter_upwards [hbound Λ F hΛ q edge a₀ b₀ ha₀ hb₀] with δ hδ
  intro hδpos L Q hL hQ hqQ hdiv a b hab hsite rates hp hrate hF hf hroom K T
  cases L with
  | zero=>omega
  | succ N=>
    have hh:=hδ hδpos N Q hQ hqQ hdiv a b hab hsite rates hp hrate hF hf hroom
    have hsum : (∑ ω,layerWeight rates ω)=1 := by
      with_reducible convert layerWeight_sum rates using 1
      congr! 20
    have hpos:=pinPartition_pos (layerWeight rates) (coinWiring (finRotate (N+1)) a b)
      (layerWeight_nonneg rates hp) (by rw [hsum]; norm_num) ∅
    dsimp only at hh
    rw [mesh_cut_product,mesh_partition_product] at hh
    rw [mesh_partition_product] at hpos
    exact (le_div_iff₀ hpos).mp hh

end Heisenberg.Surface
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.Surface.mesh_matrix_surface_oai := @OAI.Heisenberg.Surface.mesh_matrix_surface_oai

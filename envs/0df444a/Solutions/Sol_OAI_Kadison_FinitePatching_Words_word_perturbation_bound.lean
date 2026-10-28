-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.Words.word_perturbation_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:41:11.754698+00:00
-- url     : https://prove2.me/submissions/a4fe67d4-6bb9-4a02-a917-b2242e279e32

import Mathlib
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C045
import Theorems.Thm_OAI_Kadison_FinitePatching_trace_centered_compression_bound
import Theorems.Thm_OAI_Kadison_FinitePatching_trace_word_second_order_bound

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma norm_nonneg (a : A) : 0≤norm τ a := _root_.norm_nonneg _

lemma norm_sq (a : A) : norm τ a^2=(τ (star a*a)).re := by
  rw [norm,InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]
  rfl

lemma norm_add (a b : A) : norm τ (a+b)≤norm τ a+norm τ b := by
  simpa only [norm,map_add] using norm_add_le (τ.toPreGNS a) (τ.toPreGNS b)

lemma norm_smul (c : ℂ) (a : A) : norm τ (c • a)=‖c‖*norm τ a := by
  simp only [norm,map_smul,_root_.norm_smul]

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma norm_star (a : A) : norm τ (star a)=norm τ a := by
  apply (sq_eq_sq₀ (norm_nonneg τ _) (norm_nonneg τ _)).mp
  rw [norm_sq,norm_sq,star_star,hτ]

include hτ in
lemma norm_trace_mul (a b : A) : ‖τ (a*b)‖≤norm τ a*norm τ b := by
  have h := norm_inner_le_norm (𝕜:=ℂ) (τ.toPreGNS (star a)) (τ.toPreGNS b)
  change ‖τ (star (star a)*b)‖≤norm τ (star a)*norm τ b at h
  simpa only [star_star,norm_star τ hτ] using h

lemma norm_projection_sq {p : A} (hp : IsStarProjection p) : norm τ p^2=(τ p).re := by
  rw [norm_sq,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerCenteredEstimates
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

open TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

lemma projection_trace_real {p : A} (hp : IsStarProjection p) : τ p=((τ p).re:ℂ) := by
  apply Complex.ext
  · rfl
  have h := (τ.map_nonneg hp.nonneg).2
  simpa only [Complex.zero_im,Complex.ofReal_im] using h.symm

lemma projection_trace_norm {p : A} (hp : IsStarProjection p) : ‖τ p‖=(τ p).re := by
  calc
    _=‖((τ p).re:ℂ)‖ := congrArg (fun z : ℂ => ‖z‖) (projection_trace_real τ hp)
    _=(τ p).re := by
      rw [Complex.norm_real,Real.norm_of_nonneg (τ.map_nonneg hp.nonneg).1]

lemma compress_center {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) (b : A) :
    q*b*q=q*cornerCenter τ p b*q+cornerScalar τ p b • q := by
  have h1 := (hq.le_iff_mul_eq_left hp).mp hqp
  have h2 := (hq.le_iff_mul_eq_right hp).mp hqp
  simp only [cornerCenter,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  have h3 : q*(p*b*p)*q=q*b*q := by
    calc
      _=(q*p)*b*(p*q) := by noncomm_ring
      _=_ := by rw [h1,h2]
  rw [h3,h1,hq.isIdempotentElem.eq,sub_add_cancel]

lemma compressed_bound {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) (b : A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
    norm τ (q*b*q)*norm τ q ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re := by
  have hsmall' : norm τ (q*cornerCenter τ p b*q) ≤ δ*norm τ q := by
    apply (sq_le_sq₀ (norm_nonneg τ _) (mul_nonneg hδ (norm_nonneg τ _))).mp
    rw [mul_pow,norm_projection_sq τ hq]
    exact hsmall
  have hh : norm τ (q*b*q) ≤ (δ+‖cornerScalar τ p b‖)*norm τ q := by
    rw [compress_center τ hp hq hqp b]
    calc
      _ ≤ norm τ (q*cornerCenter τ p b*q)+norm τ (cornerScalar τ p b • q) :=
        norm_add τ _ _
      _ ≤ δ*norm τ q+‖cornerScalar τ p b‖*norm τ q := by
        rw [TracialL2.norm_smul]
        exact add_le_add hsmall' le_rfl
      _=_ := by ring
  calc
    _ ≤ ((δ+‖cornerScalar τ p b‖)*norm τ q)*norm τ q :=
      mul_le_mul_of_nonneg_right hh (norm_nonneg τ _)
    _ = (δ+‖cornerScalar τ p b‖)*(norm τ q)^2 := by ring
    _ = _ := by rw [norm_projection_sq τ hq]

include hτ in
lemma trace_single_support_bound {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p) (b : A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
    ‖τ (q*b)‖ ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re := by
  have he : τ (q*b)=τ ((q*b*q)*q) := by
    rw [mul_assoc (q*b),hq.isIdempotentElem.eq,hτ (q*b),←mul_assoc,hq.isIdempotentElem.eq]
  rw [he]
  exact (norm_trace_mul τ hτ _ _).trans (compressed_bound τ hp hq hqp b hδ hsmall)

lemma cornerScalar_complement_bound {f : A} (hf : IsStarProjection f) (b : A)
    {t B : ℝ} (ht : 0<t) (htr : t ≤ (τ (1-f)).re)
    (hb : ‖τ b‖ ≤ B) (hfb : ‖τ (f*b)‖ ≤ B) :
    ‖cornerScalar τ (1-f) b‖ ≤ 2*B/t := by
  have hnum : ‖τ ((1-f)*b)‖ ≤ 2*B := by
    rw [sub_mul,one_mul,map_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have hden : 0<(τ (1-f)).re := ht.trans_le htr
  rw [cornerScalar,norm_div,projection_trace_norm τ hf.one_sub]
  exact (div_le_div_of_nonneg_right hnum hden.le).trans
    (div_le_div_of_nonneg_left (by linarith [_root_.norm_nonneg (τ b)]) ht htr)

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteWordTelescoping
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.FinitePatching

variable {A I : Type*} [NormedRing A]

lemma wordProduct_append (a : I → A) (l r : List I) :
    wordProduct a (l++r)=wordProduct a l*wordProduct a r := by
  simp [wordProduct,List.map_append,List.prod_append]

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable (A : Type*) [CStarAlgebra A]

namespace PartialUnitary

variable {A}

lemma power_norm (v : PartialUnitary A) (k : ℤ) : ‖v.power k‖ ≤ 1 := by
  have hp (a : A) (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a^(n+1)‖ ≤ 1 :=
    (norm_pow_le' a (Nat.succ_pos n)).trans (pow_le_one₀ (_root_.norm_nonneg _) ha)
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact v.projection.norm_le _
    | succ n => exact hp _ v.norm_le_one _
  | negSucc n => exact hp _ (by simpa using v.norm_le_one) _

lemma val_mul_zero {v w : PartialUnitary A} (h : v.support*w.support=0) : v.val*w.val=0 :=
  by simpa [power] using power_mul_power_zero h 1 1

lemma pow_add_of_mul_zero {a b : A} (hab : a*b=0) (hba : b*a=0) (n : ℕ) :
    (a+b)^(n+1)=a^(n+1)+b^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a^(n+1)*b=0 := by rw [pow_succ,mul_assoc,hab,mul_zero]
    have h2 : b^(n+1)*a=0 := by rw [pow_succ,mul_assoc,hba,mul_zero]
    rw [pow_succ,ih,add_mul,mul_add,mul_add,h1,h2]
    simp only [add_zero,zero_add,←pow_succ]

lemma add_power (v w : PartialUnitary A) (h : v.support*w.support=0) (k : ℤ) :
    (v.add w h).power k=v.power k+w.power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      exact pow_add_of_mul_zero (val_mul_zero h) (val_mul_zero (orthogonal_support_symm h)) n
  | negSucc n =>
    change (star (v.val+w.val))^(n+1)=(star v.val)^(n+1)+(star w.val)^(n+1)
    rw [star_add]
    apply pow_add_of_mul_zero
    · simpa only [StarMul.star_mul,star_zero] using congrArg star (val_mul_zero (orthogonal_support_symm h))
    · simpa only [StarMul.star_mul,star_zero] using congrArg star (val_mul_zero h)

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A]

lemma valid_of_internal (s : List (Letter J K)) (i : Letter J K)
    (hs : ∀ j∈s,NonzeroSlot j.2) : Valid (s++[i]) := by
  revert hs
  induction s with
  | nil =>
    intro hs a b c he hc
    have hlen := congrArg List.length he
    simp only [List.nil_append,List.length_cons,List.length_nil,List.length_append] at hlen
    have hcl : 0 < c.length := List.length_pos_iff.mpr hc
    omega
  | cons j s ih =>
    intro hs a b c he hc
    cases a with
    | nil =>
      have hh := List.cons.inj he
      have hb : j=b := hh.1
      subst b
      exact hs j (by simp)
    | cons a t =>
      have hh := List.cons.inj he
      exact ih (fun z hz => hs z (by simp [hz])) t b c hh.2 hc

lemma internal_prefix {l s t : List (Letter J K)} {i : Letter J K}
    (hv : Valid l) (he : l=s++i::t) : ∀ j∈s,NonzeroSlot j.2 := by
  intro j hj
  obtain ⟨a,b,rfl⟩ := List.mem_iff_append.mp hj
  apply hv a j (b++i::t)
  · simpa only [List.append_assoc,List.cons_append] using he
  · simp

lemma internal_middle {l s t r : List (Letter J K)} {i j : Letter J K}
    (hv : Valid l) (he : l=s++i::(t++j::r)) : ∀ b∈t,NonzeroSlot b.2 := by
  intro b hb
  have hp := internal_prefix hv (show l=(s++[i]++t)++j::r by
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using he)
  exact hp b (by simp [hb])

lemma tail_nil_of_not_nonzero {l s t : List (Letter J K)} {i : Letter J K}
    (hv : Valid l) (he : l=s++i::t) (hi : ¬NonzeroSlot i.2) : t=[] := by
  by_contra ht
  exact hi (hv s i t he ht)

variable (x : J → A) (k : K → ℤ)

lemma word_append (v : PartialUnitary A) (s t : List (Letter J K)) :
    word x k v (s++t)=word x k v s*word x k v t := wordProduct_append _ _ _

@[simp] lemma word_open_last (v : PartialUnitary A) (s : List (Letter J K)) (j : J) :
    word x k v (s++[(j,none)])=word x k v s*x j := by
  simp [word_append,letter,slotPower]

@[simp] lemma word_support_last (v : PartialUnitary A) (s : List (Letter J K)) (j : J) :
    word x k v (s++[(j,some none)])=word x k v s*x j*v.support := by
  simp [word_append,letter,slotPower,mul_assoc]

lemma slotPower_norm (v : PartialUnitary A) (s : Slot K) : ‖slotPower k v s‖ ≤ 1 := by
  cases s with
  | none => exact (IsStarProjection.one A).norm_le _
  | some s =>
    cases s with
    | none => exact v.projection.norm_le _
    | some i => exact v.power_norm _

lemma letter_norm (hx : ∀ j,‖x j‖ ≤ 1) (v : PartialUnitary A) (i : Letter J K) :
    ‖letter x k v i‖ ≤ 1 :=
  (_root_.norm_mul_le _ _).trans ((mul_le_mul (hx _) (slotPower_norm k v _)
    (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul (1:ℝ)))

lemma word_norm (hx : ∀ j,‖x j‖ ≤ 1) (v : PartialUnitary A) (l : List (Letter J K)) :
    ‖word x k v l‖ ≤ 1 := by
  induction l with
  | nil => exact (IsStarProjection.one A).norm_le _
  | cons i l ih =>
    rw [word_cons]
    exact (_root_.norm_mul_le _ _).trans ((mul_le_mul (letter_norm x k hx v i) ih
      (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul (1:ℝ)))

lemma slotPower_add (v w : PartialUnitary A) (h : v.support*w.support=0) (s : Slot K) :
    slotPower k (v.add w h) s=slotPower k v s+slotIncrement k w s := by
  cases s with
  | none => simp [slotPower,slotIncrement]
  | some s =>
    cases s with
    | none => rfl
    | some i => exact v.add_power w h _

lemma letter_add (v w : PartialUnitary A) (h : v.support*w.support=0) (i : Letter J K) :
    letter x k (v.add w h) i=letter x k v i+newLetter x k w i := by
  simp only [letter,newLetter,slotPower_add,mul_add]

lemma word_add (v w : PartialUnitary A) (h : v.support*w.support=0) (l : List (Letter J K)) :
    word x k (v.add w h) l=wordProduct (fun i => letter x k v i+newLetter x k w i) l := by
  unfold word
  congr 1
  funext i
  exact letter_add x k v w h i

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialWordPerturbation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

include hτ in
lemma open_scalar_bound {v : PartialUnitary A} {N : ℕ} {B η : ℝ}
    (hbound : MomentBound τ x k v N B) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
    (s : List (Letter J K)) (j : J) (hlen : s.length+1 ≤ N)
    (hs : ∀ i∈s,NonzeroSlot i.2) :
    ‖cornerScalar τ (1-v.support) (word x k v s*x j)‖ ≤ 2*B/η := by
  apply cornerScalar_complement_bound τ v.projection _ hη hrest
  · have hh := hbound.2 (s++[(j,none)]) (by simp)
      (by simpa only [List.length_append,List.length_singleton] using hlen)
      (valid_of_internal s _ hs)
    simpa only [word_open_last] using hh
  · have hh := hbound.2 (s++[(j,some none)]) (by simp)
      (by simpa only [List.length_append,List.length_singleton] using hlen)
      (valid_of_internal s _ hs)
    rw [word_support_last,hτ] at hh
    exact hh

omit [PartialOrder A] [StarOrderedRing A] in
lemma slotIncrement_left (w : PartialUnitary A) (s : Slot K) :
    w.support*slotIncrement k w s=slotIncrement k w s := by
  cases s with
  | none => simp [slotIncrement]
  | some s =>
    cases s with
    | none => exact w.projection.isIdempotentElem.eq
    | some i => exact w.support_power _

omit [PartialOrder A] [StarOrderedRing A] in
lemma slotIncrement_right (w : PartialUnitary A) (s : Slot K) :
    slotIncrement k w s*w.support=slotIncrement k w s := by
  cases s with
  | none => simp [slotIncrement]
  | some s =>
    cases s with
    | none => exact w.projection.isIdempotentElem.eq
    | some i => exact w.power_support _

omit [PartialOrder A] [StarOrderedRing A] in
lemma slotIncrement_norm (w : PartialUnitary A) (s : Slot K) :
    ‖slotIncrement k w s‖ ≤ 1 := by
  cases s with
  | none => simp [slotIncrement]
  | some s =>
    cases s with
    | none => exact w.projection.norm_le _
    | some i => exact w.power_norm _

include hτ in
theorem word_perturbation_bound_oai (hx : ∀ j,‖x j‖ ≤ 1)
    (v w : PartialUnitary A) (horth : v.support*w.support=0)
    (hqp : w.support ≤ 1-v.support) {N : ℕ} {B δ η : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
    (hbound : MomentBound τ x k v N B)
    (hsmall : ∀ (s : List (Letter J K)) (j : J), s.length ≤ N →
      TracialL2.norm τ (w.support*cornerCenter τ (1-v.support) (word x k v s*x j)*w.support)^2 ≤
        δ^2*(τ w.support).re)
    (hphase : ∀ (s t : List (Letter J K)) (j : J) (i : K),
      s.length ≤ N → t.length ≤ N →
      ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ δ*(τ w.support).re)
    (l : List (Letter J K)) (hlen : l.length ≤ N) (hv : Valid l) :
    ‖τ (word x k (v.add w horth) l)-τ (word x k v l)‖ ≤
      ((l.length:ℝ)+(l.length:ℝ)^2)*(δ+2*B/η)*(τ w.support).re := by
  have hqt : 0 ≤ (τ w.support).re := (τ.map_nonneg w.projection.nonneg).1
  have hc : 0 ≤ δ+2*B/η := by positivity
  have hS : 0 ≤ (δ+2*B/η)*(τ w.support).re := mul_nonneg hc hqt
  have hlen1 : ∀ s i t,l=s++i::t → s.length+1 ≤ N ∧ t.length ≤ N := by
    intro s i t he
    have hh : s.length+1+t.length ≤ N := by
      simpa only [he,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hlen
    omega
  have hsingle : ∀ s i t,l=s++i::t →
      ‖τ (wordProduct (letter x k v) s*newLetter x k w i*wordProduct (letter x k v) t)‖ ≤
        (δ+2*B/η)*(τ w.support).re := by
    intro s i t he
    rcases i with ⟨j,i⟩
    cases i with
    | none => simp [newLetter,slotIncrement,hS]
    | some i =>
      cases i with
      | none =>
        have ht : t=[] := tail_nil_of_not_nonzero hv he (by simp [NonzeroSlot])
        subst t
        have hs := internal_prefix hv he
        have hsc := open_scalar_bound τ hτ x k hbound hη hrest s j (hlen1 s _ [] he).1 hs
        have hh := trace_single_support_bound τ hτ v.projection.one_sub w.projection hqp
          (word x k v s*x j) hδ (hsmall s j (by have hh := (hlen1 s _ [] he).1; omega))
        have hcq := mul_le_mul_of_nonneg_right (add_le_add (le_refl δ) hsc) hqt
        calc
          _=‖τ (w.support*(word x k v s*x j))‖ := by
            simp only [wordProduct_nil,mul_one,newLetter,slotIncrement,←mul_assoc]
            rw [hτ]
            simp only [word,mul_assoc]
          _ ≤ (δ+‖cornerScalar τ (1-v.support) (word x k v s*x j)‖)*(τ w.support).re := hh
          _ ≤ _ := hcq
      | some i =>
        have hp := hphase s t j i (by have hh := (hlen1 s _ t he).1; omega)
          (hlen1 s _ t he).2
        have heq : τ (wordProduct (letter x k v) s*newLetter x k w (j,some (some i))*
            wordProduct (letter x k v) t)=
            τ (w.power (k i)*(word x k v t*word x k v s*x j)) := by
          change τ (word x k v s*(x j*w.power (k i))*word x k v t)=_
          calc
            _=τ ((word x k v s*x j)*(w.power (k i)*word x k v t)) := by congr 1; noncomm_ring
            _=τ ((w.power (k i)*word x k v t)*(word x k v s*x j)) := hτ _ _
            _=_ := by congr 1; noncomm_ring
        rw [heq]
        exact hp.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hqt)
  have hdouble : ∀ s i t j r,l=s++i::(t++j::r) →
      ‖τ (wordProduct (letter x k v) s*newLetter x k w i*
        wordProduct (letter x k v) t*newLetter x k w j*
        wordProduct (fun b => letter x k v b+newLetter x k w b) r)‖ ≤
          (δ+2*B/η)*(τ w.support).re := by
    intro s i t j r he
    have htlen : t.length+1 ≤ N := by
      have hh := hlen
      rw [he,List.length_append,List.length_cons,List.length_append,List.length_cons] at hh
      omega
    have hts := internal_middle hv he
    have hsc := open_scalar_bound τ hτ x k hbound hη hrest t j.1 htlen hts
    have han : ‖word x k v s*x i.1‖ ≤ 1 :=
      (_root_.norm_mul_le _ _).trans ((mul_le_mul (word_norm x k hx v s) (hx _)
        (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul (1:ℝ)))
    have hh := trace_centered_compression_bound τ hτ v.projection.one_sub w.projection hqp
      (slotIncrement_right k w i.2) (slotIncrement_left k w j.2)
      han (word_norm x k hx (v.add w horth) r)
      (slotIncrement_norm k w i.2) (slotIncrement_norm k w j.2)
      hδ (hsmall t j.1 (by omega))
    have heq : wordProduct (letter x k v) s*newLetter x k w i*
        wordProduct (letter x k v) t*newLetter x k w j*
        wordProduct (fun b => letter x k v b+newLetter x k w b) r=
        (word x k v s*x i.1)*slotIncrement k w i.2*(word x k v t*x j.1)*
          slotIncrement k w j.2*word x k (v.add w horth) r := by
      rw [word_add]
      simp only [newLetter,word,mul_assoc]
    rw [heq]
    exact hh.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl δ) hsc) hqt)
  rw [word_add]
  exact (trace_word_second_order_bound τ.toLinearMap (letter x k v) (newLetter x k w)
    l hS hS hsingle hdouble).trans_eq (by ring)

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.FinitePatching.Words.word_perturbation_bound_oai.{u_1, u_2, u_3} := @OAI.Kadison.FinitePatching.Words.word_perturbation_bound_oai.{u_1, u_2, u_3}

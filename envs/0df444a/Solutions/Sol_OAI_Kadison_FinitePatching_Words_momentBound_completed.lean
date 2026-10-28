-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.Words.momentBound_completed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:50:51.18399+00:00
-- url     : https://prove2.me/submissions/0e7987d1-371f-495a-b0e7-40567584fcec

import Mathlib
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C045
import Definitions.Def_OAIQ039C046

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end

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

lemma norm_mul_left (a b : A) : norm τ (a*b)≤‖a‖*norm τ b := by
  change ‖τ.leftMulMapPreGNS a (τ.toPreGNS b)‖≤‖a‖*‖τ.toPreGNS b‖
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (LinearMap.mkContinuous_norm_le _ (_root_.norm_nonneg _) _) (_root_.norm_nonneg _))

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma norm_star (a : A) : norm τ (star a)=norm τ a := by
  apply (sq_eq_sq₀ (norm_nonneg τ _) (norm_nonneg τ _)).mp
  rw [norm_sq,norm_sq,star_star,hτ]

include hτ in
lemma norm_mul_right (a b : A) : norm τ (a*b)≤norm τ a*‖b‖ := by
  calc
    _=norm τ (star b*star a) := by rw [←star_mul,norm_star τ hτ]
    _≤‖star b‖*norm τ (star a) := norm_mul_left τ _ _
    _=_ := by rw [_root_.norm_star,norm_star τ hτ,mul_comm]

include hτ in
lemma norm_trace_mul (a b : A) : ‖τ (a*b)‖≤norm τ a*norm τ b := by
  have h := norm_inner_le_norm (𝕜:=ℂ) (τ.toPreGNS (star a)) (τ.toPreGNS b)
  change ‖τ (star (star a)*b)‖≤norm τ (star a)*norm τ b at h
  simpa only [star_star,norm_star τ hτ] using h

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryOrder
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

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma star_mul_of_le {v w : PartialUnitary A} (h : v ≤ w) :
    star v.val*w.val=v.support := by
  calc
    _=star (w.val*v.support)*w.val := by rw [h.2]
    _=v.support*w.support := by
      rw [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,mul_assoc,w.star_mul]
    _=v.support := (v.projection.le_iff_mul_eq_left w.projection).mp h.1

lemma star_sub_mul_sub {v w : PartialUnitary A} (h : v ≤ w) :
    star (w.val-v.val)*(w.val-v.val)=w.support-v.support := by
  have h' : star w.val*v.val=v.support := by
    simpa only [StarMul.star_mul,star_star,v.projection.isSelfAdjoint.star_eq] using
      congrArg star (star_mul_of_le h)
  rw [star_sub,sub_mul,mul_sub,mul_sub,w.star_mul,v.star_mul,star_mul_of_le h,h']
  noncomm_ring

lemma norm_sub_sq (τ : A →ₚ[ℂ] ℂ) {v w : PartialUnitary A} (h : v ≤ w) :
    TracialL2.norm τ (w.val-v.val)^2=(τ w.support).re-(τ v.support).re := by
  rw [TracialL2.norm_sq,star_sub_mul_sub h,map_sub,Complex.sub_re]

lemma le_add (v w : PartialUnitary A) (h : v.support*w.support=0) : v ≤ v.add w h := by
  refine ⟨le_add_of_nonneg_right w.projection.nonneg,?_⟩
  change (v.val+w.val)*v.support=v.val
  have hz := power_mul_power_zero (orthogonal_support_symm h) 1 0
  simp [power] at hz
  rw [add_mul,v.mul_support,hz,add_zero]

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryCompletion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma le_completed (v : PartialUnitary A) : v ≤ v.completed := v.le_add _ _

lemma completion_norm_sub (τ : A →ₚ[ℂ] ℂ) (hone : τ 1=1) (v : PartialUnitary A) :
    TracialL2.norm τ (v.completed.val-v.val)=Real.sqrt (1-(τ v.support).re) := by
  have hh := norm_sub_sq τ v.le_completed
  rw [completed_support,hone,Complex.one_re] at hh
  rw [←hh,Real.sqrt_sq (TracialL2.norm_nonneg τ _)]

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

variable (x : J → A) (k : K → ℤ)

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

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Continuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma norm_mul_sub_mul (a b c d : A) :
    norm τ (a*b-c*d) ≤ norm τ (a-c)*‖b‖+‖c‖*norm τ (b-d) := by
  have he : a*b-c*d=(a-c)*b+c*(b-d) := by noncomm_ring
  rw [he]
  exact (norm_add τ _ _).trans
    (add_le_add (norm_mul_right τ hτ _ _) (norm_mul_left τ _ _))

lemma norm_one (hone : τ 1=1) : norm τ (1:A)=1 := by
  have hh := norm_sq τ (1:A)
  simp only [star_one,mul_one,hone,Complex.one_re] at hh
  nlinarith [norm_nonneg τ (1:A)]

include hτ in
lemma norm_trace_le (hone : τ 1=1) (a : A) : ‖τ a‖ ≤ norm τ a := by
  simpa only [mul_one,norm_one τ hone] using norm_trace_mul τ hτ a 1

include hτ in
lemma norm_pow_sub_pow (a b : A) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    norm τ (a^n-b^n) ≤ (n:ℝ)*norm τ (a-b) := by
  induction n with
  | zero => simp [norm]
  | succ n ih =>
    have hbn : ‖b^n‖ ≤ 1 := by
      cases n with
      | zero => simpa only [pow_zero] using (IsStarProjection.one A).norm_le 1
      | succ n =>
        exact (norm_pow_le' b (Nat.succ_pos n)).trans
          (pow_le_one₀ (_root_.norm_nonneg _) hb)
    calc
      _=norm τ (a^n*a-b^n*b) := by rw [pow_succ,pow_succ]
      _ ≤ norm τ (a^n-b^n)*‖a‖+‖b^n‖*norm τ (a-b) := norm_mul_sub_mul τ hτ _ _ _ _
      _ ≤ (n:ℝ)*norm τ (a-b)+norm τ (a-b) := by
        exact add_le_add
          ((mul_le_mul_of_nonneg_left ha (norm_nonneg τ _)).trans (by simpa using ih))
          (mul_le_of_le_one_left (norm_nonneg τ _) hbn)
      _=_ := by rw [Nat.cast_succ]; ring

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialWordContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma PartialUnitary.support_norm_sub (v w : PartialUnitary A) :
    TracialL2.norm τ (v.support-w.support) ≤ 2*TracialL2.norm τ (v.val-w.val) := by
  rw [←v.star_mul,←w.star_mul]
  have hh := TracialL2.norm_mul_sub_mul τ hτ (star v.val) v.val (star w.val) w.val
  rw [←star_sub,TracialL2.norm_star τ hτ,_root_.norm_star] at hh
  exact hh.trans (by
    have h1 := mul_le_of_le_one_right (TracialL2.norm_nonneg τ (v.val-w.val)) v.norm_le_one
    have h2 := mul_le_of_le_one_left (TracialL2.norm_nonneg τ (v.val-w.val)) w.norm_le_one
    linarith)

include hτ in
lemma PartialUnitary.power_norm_sub (v w : PartialUnitary A) (k : ℤ) :
    TracialL2.norm τ (v.power k-w.power k) ≤ ((k.natAbs:ℝ)+2)*TracialL2.norm τ (v.val-w.val) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => simpa only [PartialUnitary.power,Int.natAbs_ofNat',Nat.cast_zero,zero_add] using
        support_norm_sub τ hτ v w
    | succ n =>
      have hh := TracialL2.norm_pow_sub_pow τ hτ v.val w.val v.norm_le_one w.norm_le_one (n+1)
      change TracialL2.norm τ (v.val^(n+1)-w.val^(n+1)) ≤ _
      simp only [Int.natAbs_ofNat']
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (TracialL2.norm_nonneg τ _))
  | negSucc n =>
    have hh := TracialL2.norm_pow_sub_pow τ hτ (star v.val) (star w.val)
      (by simpa using v.norm_le_one) (by simpa using w.norm_le_one) (n+1)
    rw [←star_sub,TracialL2.norm_star τ hτ] at hh
    change TracialL2.norm τ ((star v.val)^(n+1)-(star w.val)^(n+1)) ≤ _
    simp only [Int.natAbs_negSucc]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (TracialL2.norm_nonneg τ _))

namespace Words

variable (x : J → A) (k : K → ℤ)

include hτ in
lemma slotPower_norm_sub (v w : PartialUnitary A) (s : Slot K) :
    TracialL2.norm τ (slotPower k v s-slotPower k w s) ≤
      (slotCost k s:ℝ)*TracialL2.norm τ (v.val-w.val) := by
  cases s with
  | none => simp [slotPower,slotCost,TracialL2.norm]
  | some s =>
    cases s with
    | none => exact v.support_norm_sub τ hτ w
    | some i => simpa only [slotPower,slotCost,Nat.cast_add,Nat.cast_ofNat] using
        v.power_norm_sub τ hτ w (k i)

include hτ in
lemma letter_norm_sub (hx : ∀ j,‖x j‖ ≤ 1) (v w : PartialUnitary A) (i : Letter J K) :
    TracialL2.norm τ (letter x k v i-letter x k w i) ≤
      (slotCost k i.2:ℝ)*TracialL2.norm τ (v.val-w.val) := by
  simp only [letter,←mul_sub]
  exact (TracialL2.norm_mul_left τ _ _).trans
    ((mul_le_of_le_one_left (TracialL2.norm_nonneg τ _) (hx i.1)).trans
      (slotPower_norm_sub τ hτ k v w i.2))

include hτ in
lemma word_norm_sub (hx : ∀ j,‖x j‖ ≤ 1) (v w : PartialUnitary A) (l : List (Letter J K)) :
    TracialL2.norm τ (word x k v l-word x k w l) ≤
      (wordCost k l:ℝ)*TracialL2.norm τ (v.val-w.val) := by
  induction l with
  | nil => simp [wordCost,TracialL2.norm]
  | cons i l ih =>
    rw [word_cons,word_cons]
    have hh := TracialL2.norm_mul_sub_mul τ hτ (letter x k v i) (word x k v l)
      (letter x k w i) (word x k w l)
    have h1 := (mul_le_of_le_one_right (TracialL2.norm_nonneg τ _)
      (word_norm x k hx v l)).trans (letter_norm_sub τ hτ x k hx v w i)
    have h2 := (mul_le_of_le_one_left (TracialL2.norm_nonneg τ _)
      (letter_norm x k hx w i)).trans ih
    exact hh.trans ((add_le_add h1 h2).trans_eq (by
      simp only [wordCost,List.map_cons,List.sum_cons,Nat.cast_add]; ring))

include hτ in
lemma trace_word_norm_sub (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (v w : PartialUnitary A) (l : List (Letter J K)) :
    ‖τ (word x k v l)-τ (word x k w l)‖ ≤
      (wordCost k l:ℝ)*TracialL2.norm τ (v.val-w.val) := by
  rw [←map_sub]
  exact (TracialL2.norm_trace_le τ hτ hone _).trans (word_norm_sub τ hτ x k hx v w l)

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestCompletion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

include hτ in
lemma momentBound_completed_oai (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (v : PartialUnitary A) {N : ℕ} {B C : ℝ}
    (hB : MomentBound τ x k v N B)
    (hpower : ∀ i,((k i).natAbs:ℝ)+2 ≤ C)
    (hword : ∀ l : List (Letter J K),l.length ≤ N → (wordCost k l:ℝ) ≤ C) :
    MomentBound τ x k v.completed N (B+C*Real.sqrt (1-(τ v.support).re)) := by
  have he := v.completion_norm_sub τ hone
  constructor
  · intro i
    have hd : ‖τ (v.completed.power (k i))-τ (v.power (k i))‖ ≤
        C*Real.sqrt (1-(τ v.support).re) := by
      rw [←map_sub]
      exact (TracialL2.norm_trace_le τ hτ hone _).trans
        ((v.completed.power_norm_sub τ hτ v (k i)).trans (by
          rw [he]
          exact mul_le_mul_of_nonneg_right (hpower i) (Real.sqrt_nonneg _)))
    exact (norm_le_insert (τ (v.power (k i))) (τ (v.completed.power (k i)))).trans
      (by simpa only [norm_sub_rev] using add_le_add (hB.1 i) hd)
  · intro l hl hlen hvalid
    have hd : ‖τ (word x k v.completed l)-τ (word x k v l)‖ ≤
        C*Real.sqrt (1-(τ v.support).re) := by
      exact (trace_word_norm_sub τ hτ x k hone hx v.completed v l).trans (by
        rw [he]
        exact mul_le_mul_of_nonneg_right (hword l hlen) (Real.sqrt_nonneg _))
    exact (norm_le_insert (τ (word x k v l)) (τ (word x k v.completed l))).trans
      (by simpa only [norm_sub_rev] using add_le_add (hB.2 l hl hlen hvalid) hd)

end Kadison.FinitePatching.Words

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.FinitePatching.Words.momentBound_completed_oai.{u_1, u_2, u_3} := @OAI.Kadison.FinitePatching.Words.momentBound_completed_oai.{u_1, u_2, u_3}

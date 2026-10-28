-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.admissible_chain_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:56:32.459472+00:00
-- url     : https://prove2.me/submissions/7495a9e9-3574-4a28-b2ff-c4e66bbbceb8

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_FinitePatching_PartialUnitary_chain_upper_with_L2_and_membership

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

include hτ in
lemma tendsto_trace {ι : Type*} {l : Filter ι} {a : ι → A} {x : A}
    (hone : τ 1=1) (ha : Tendsto (fun i => norm τ (a i-x)) l (𝓝 0)) :
    Tendsto (fun i => τ (a i)) l (𝓝 (τ x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i => _root_.norm_nonneg _) (fun i => by
    simpa only [map_sub] using norm_trace_le τ hτ hone (a i-x)) ha

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialWordContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
lemma momentBound_limit {I : Type*} {f : Filter I} [NeBot f]
    (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (v : I → PartialUnitary A) (w : PartialUnitary A) (B : I → ℝ) (b : ℝ) (N : ℕ)
    (hv : Tendsto (fun i => TracialL2.norm τ ((v i).val-w.val)) f (𝓝 0))
    (hB : Tendsto B f (𝓝 b)) (hb : ∀ i,MomentBound τ x k (v i) N (B i)) :
    MomentBound τ x k w N b := by
  have hpow (i : K) : Tendsto (fun j => τ ((v j).power (k i))) f (𝓝 (τ (w.power (k i)))) := by
    apply TracialL2.tendsto_trace τ hτ hone
    have hh := hv.const_mul ((k i).natAbs+2:ℝ)
    rw [mul_zero] at hh
    exact squeeze_zero (fun _ => TracialL2.norm_nonneg τ _) (fun j =>
      (v j).power_norm_sub τ hτ w (k i)) hh
  refine ⟨fun i => le_of_tendsto_of_tendsto (hpow i |>.norm) hB
    (Eventually.of_forall fun j => (hb j).1 i),?_⟩
  intro l hl hlen hvalid
  have hw : Tendsto (fun j => τ (word x k (v j) l)) f (𝓝 (τ (word x k w l))) := by
    apply TracialL2.tendsto_trace τ hτ hone
    have hh := hv.const_mul (wordCost k l:ℝ)
    rw [mul_zero] at hh
    exact squeeze_zero (fun _ => TracialL2.norm_nonneg τ _) (fun j => word_norm_sub τ hτ x k hx
      (v j) w l) hh
  exact le_of_tendsto_of_tendsto hw.norm hB (Eventually.of_forall fun j => (hb j).2 l hl hlen hvalid)

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteWordMaximalPatching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
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

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {J K : Type*} (x : J → M) (k : K → ℤ)

include hτ in
lemma admissible_chain_upper_oai (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (N : ℕ) (ε η : ℝ) (c : Set (PartialUnitary M))
    (hcs : c ⊆ Admissible M R τ x k N ε η) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    ∃ v∈Admissible M R τ x k N ε η,∀ w∈c,w ≤ v := by
  obtain ⟨v,hv,hmem,ω,hω,htr,hl2⟩ :=
    PartialUnitary.chain_upper_with_L2_and_membership M τ hnormal c hc hne
  have hl2' : Tendsto (fun w : c => TracialL2.norm τ (w.val.val-v.val)) (ω : Filter c) (𝓝 0) := by
    apply hl2.congr'
    exact Eventually.of_forall fun w => by
      simp only [TracialL2.norm,map_sub,norm_sub_rev]
  have hB : Tendsto (fun w : c => momentBudget ε (budgetSlope N η) (τ w.val.support).re)
      (ω : Filter c) (𝓝 (momentBudget ε (budgetSlope N η) (τ v.support).re)) := by
    exact ((Real.continuous_exp.tendsto _).comp (htr.const_mul (budgetSlope N η))).const_mul ε
  refine ⟨v,⟨hmem R (fun w hw => (hcs hw).1),?_,?_⟩,hv⟩
  · exact le_of_tendsto_of_tendsto htr tendsto_const_nhds
      (Eventually.of_forall fun w : c => (hcs w.property).2.1)
  · exact momentBound_limit τ hτ x k hone hx (fun w : c => w.val) v _ _ N hl2' hB
      (fun w => (hcs w.property).2.2)

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.FinitePatching.admissible_chain_upper_oai.{u_1, u_2, u_3} := @OAI.Kadison.FinitePatching.admissible_chain_upper_oai.{u_1, u_2, u_3}

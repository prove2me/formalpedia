-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.Words.moment_limit_of_dense_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:40:49.645289+00:00
-- url     : https://prove2.me/submissions/013771a0-91bf-4671-97a7-995182011ead

import Mathlib
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C045

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
-- module Solutions.OAIQ039_CM.Commutator_PartialWordReindex
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

namespace Kadison.FinitePatching.Words

variable {A J K J' K' : Type*} [CStarAlgebra A]

lemma valid_cons_iff (i : Letter J K) (l : List (Letter J K)) :
    Valid (i::l) ↔ Valid l ∧ (l≠[] → NonzeroSlot i.2) := by
  constructor
  · intro h
    constructor
    · intro s j t he ht
      exact h (i::s) j t (by simpa only [List.cons_append] using congrArg (List.cons i) he) ht
    · intro hl
      exact h [] i l rfl hl
  · rintro ⟨hl,hi⟩ s j t he ht
    cases s with
    | nil =>
      have hh := List.cons.inj he
      obtain ⟨rfl,rfl⟩ := hh
      exact hi ht
    | cons a s =>
      have hh := List.cons.inj he
      exact hl s j t hh.2 ht

lemma valid_map (f : J' → J) (g : K' → K) {l : List (Letter J' K')} (h : Valid l) :
    Valid (l.map (mapLetter f g)) := by
  induction l with
  | nil =>
    intro s i t he ht
    have hh := congrArg List.length he
    simp only [List.map_nil,List.length_nil,List.length_append,List.length_cons] at hh
    omega
  | cons i l ih =>
    rw [List.map_cons,valid_cons_iff]
    have hh := (valid_cons_iff i l).mp h
    refine ⟨ih hh.1,?_⟩
    intro hn
    have hl : l≠[] := by intro he; subst l; exact hn rfl
    obtain ⟨k,hk⟩ := hh.2 hl
    refine ⟨g k,?_⟩
    simp [mapLetter,hk]

lemma slotPower_reindex (k : K → ℤ) (g : K' → K) (v : PartialUnitary A) (s : Slot K') :
    slotPower k v (s.map (Option.map g))=slotPower (k ∘ g) v s := by
  cases s with
  | none => rfl
  | some s => cases s <;> rfl

lemma letter_reindex (x : J → A) (k : K → ℤ) (f : J' → J) (g : K' → K)
    (v : PartialUnitary A) (i : Letter J' K') :
    letter x k v (mapLetter f g i)=letter (x ∘ f) (k ∘ g) v i := by
  exact congrArg (x (f i.1)*·) (slotPower_reindex k g v i.2)

lemma word_reindex (x : J → A) (k : K → ℤ) (f : J' → J) (g : K' → K)
    (v : PartialUnitary A) (l : List (Letter J' K')) :
    word x k v (l.map (mapLetter f g))=word (x ∘ f) (k ∘ g) v l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons,word_cons,letter_reindex,ih]

end Kadison.FinitePatching.Words

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

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WordCoefficientContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma word_coefficients_norm_sub (x y : J → A) (k : K → ℤ)
    (hx : ∀ j,‖x j‖ ≤ 1) (hy : ∀ j,‖y j‖ ≤ 1)
    {δ : ℝ} (hxy : ∀ j,TracialL2.norm τ (x j-y j) ≤ δ)
    (v : PartialUnitary A) (l : List (Letter J K)) :
    TracialL2.norm τ (word x k v l-word y k v l) ≤ (l.length:ℝ)*δ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hh : TracialL2.norm τ (letter x k v i-letter y k v i) ≤ δ := by
      change TracialL2.norm τ (x i.1*slotPower k v i.2-y i.1*slotPower k v i.2) ≤ δ
      rw [←sub_mul]
      exact (TracialL2.norm_mul_right τ hτ _ _).trans
        ((mul_le_of_le_one_right (TracialL2.norm_nonneg τ _) (slotPower_norm k v _)).trans (hxy _))
    rw [word_cons,word_cons]
    have h1 := TracialL2.norm_mul_sub_mul τ hτ (letter x k v i) (word x k v l)
      (letter y k v i) (word y k v l)
    have h2 := add_le_add
      ((mul_le_of_le_one_right (TracialL2.norm_nonneg τ _) (word_norm x k hx v l)).trans hh)
      ((mul_le_of_le_one_left (TracialL2.norm_nonneg τ _) (letter_norm y k hy v i)).trans ih)
    apply h1.trans (h2.trans_eq _)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

include hτ in
lemma trace_word_coefficients_norm_sub (hone : τ 1=1)
    (x y : J → A) (k : K → ℤ) (hx : ∀ j,‖x j‖ ≤ 1) (hy : ∀ j,‖y j‖ ≤ 1)
    {δ : ℝ} (hxy : ∀ j,TracialL2.norm τ (x j-y j) ≤ δ)
    (v : PartialUnitary A) (l : List (Letter J K)) :
    ‖τ (word x k v l)-τ (word y k v l)‖ ≤ (l.length:ℝ)*δ := by
  rw [←map_sub]
  exact (TracialL2.norm_trace_le τ hτ hone _).trans
    (word_coefficients_norm_sub τ hτ x y k hx hy hxy v l)

include hτ in
lemma moment_limit_of_dense_coefficients_oai (hone : τ 1=1)
    (x : ℕ → A) (k : K → ℤ) (hx : ∀ j,‖x j‖ ≤ 1)
    (hden : ∀ a : A,‖a‖ ≤ 1 → τ a=0 → ∀ ε : ℝ,0<ε → ∃ j,TracialL2.norm τ (a-x j)<ε)
    (v : ℕ → PartialUnitary A)
    (hlim : ∀ l : List (Letter ℕ K),l≠[] → Valid l →
      Tendsto (fun n => τ (word x k (v n) l)) atTop (𝓝 0))
    (y : J → A) (hy : ∀ j,‖y j‖ ≤ 1) (hcy : ∀ j,τ (y j)=0)
    (l : List (Letter J K)) (hl : l≠[]) (hv : Valid l) :
    Tendsto (fun n => τ (word y k (v n) l)) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(2*((l.length:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  choose f hf using (fun j => hden (y j) (hy j) (hcy j) δ hδ)
  have he : (l.length:ℝ)*δ ≤ ε/2 := by
    have hh : 2*((l.length:ℝ)+1)*δ=ε := by dsimp [δ]; field_simp
    nlinarith
  have hsmall := (hlim (l.map (mapLetter f id)) (by simpa using hl) (valid_map f id hv)).eventually
    (Metric.ball_mem_nhds (0:ℂ) (half_pos hε))
  filter_upwards [hsmall] with n hn
  have hh : ‖τ (word (x ∘ f) k (v n) l)‖<ε/2 := by
    simpa only [Metric.mem_ball,dist_zero_right,word_reindex,Function.comp_id] using hn
  have hd := trace_word_coefficients_norm_sub τ hτ hone y (x ∘ f) k hy
    (fun j => hx (f j)) (fun j => (hf j).le) (v n) l
  rw [dist_zero_right]
  have htri := norm_le_norm_sub_add (τ (word y k (v n) l)) (τ (word (x ∘ f) k (v n) l))
  linarith

end Kadison.FinitePatching.Words

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.FinitePatching.Words.moment_limit_of_dense_coefficients_oai.{u_1, u_2, u_3} := @OAI.Kadison.FinitePatching.Words.moment_limit_of_dense_coefficients_oai.{u_1, u_2, u_3}

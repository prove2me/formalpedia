-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.exists_countable_unitary_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:52:17.632645+00:00
-- url     : https://prove2.me/submissions/6a74a5bf-a604-4e8c-88f6-9ce6c58c3e28

import Mathlib
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_FinitePatching_exists_full_unitary_finite_tests

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

variable [PartialOrder A]

lemma momentBound_reindex (τ : A →ₚ[ℂ] ℂ) (x : J → A) (k : K → ℤ)
    (f : J' → J) (g : K' → K) (v : PartialUnitary A) {N : ℕ} {B : ℝ}
    (h : MomentBound τ x k v N B) : MomentBound τ (x ∘ f) (k ∘ g) v N B := by
  refine ⟨fun i => h.1 (g i),?_⟩
  intro l hn hl hv
  rw [←word_reindex]
  exact h.2 _ (by intro he; apply hn; exact List.length_eq_zero_iff.mp (by simpa only [List.length_map,List.length_nil] using congrArg List.length he)) (by simpa only [List.length_map] using hl)
    (valid_map f g hv)

end Kadison.FinitePatching.Words

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableUnitaryTests
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
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

section Reindex

variable {A : Type*} [CStarAlgebra A]

lemma eventually_letter_truncate (x : ℕ → A) (k : ℕ → ℤ) (v : ℕ → PartialUnitary A)
    (i : Letter ℕ ℕ) : ∀ᶠ n : ℕ in atTop,
    letter (fun j => x (min j n)) (fun j => k (min j n)) (v n) i=letter x k (v n) i := by
  rcases i with ⟨j,s⟩
  cases s with
  | none =>
    filter_upwards [eventually_ge_atTop j] with n hn
    simp [letter,slotPower,min_eq_left hn]
  | some s =>
    cases s with
    | none =>
      filter_upwards [eventually_ge_atTop j] with n hn
      simp [letter,slotPower,min_eq_left hn]
    | some i =>
      filter_upwards [eventually_ge_atTop j,eventually_ge_atTop i] with n hn hi
      simp [letter,slotPower,min_eq_left hn,min_eq_left hi]

lemma eventually_word_truncate (x : ℕ → A) (k : ℕ → ℤ) (v : ℕ → PartialUnitary A)
    (l : List (Letter ℕ ℕ)) : ∀ᶠ n : ℕ in atTop,
    word (fun j => x (min j n)) (fun j => k (min j n)) (v n) l=word x k (v n) l := by
  induction l with
  | nil => exact Eventually.of_forall (fun _ => rfl)
  | cons i l ih =>
    filter_upwards [eventually_letter_truncate x k v i,ih] with n hn hl
    simp only [word_cons,hn,hl]

end Reindex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_countable_unitary_tests_oai
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (x : ℕ → M) (k : ℕ → ℤ) (hx : ∀ j,‖x j‖ ≤ 1)
    (hcenter : ∀ j,τ (x j)=0) (hk : ∀ i,k i≠0) :
    ∃ u : ℕ → unitary M, (∀ n, ((u n:M) : H →L[ℂ] H)∈R) ∧
      (∀ i,Tendsto (fun n => τ ((PartialUnitary.ofUnitary (u n)).power (k i))) atTop (𝓝 0)) ∧
      (∀ l : List (Letter ℕ ℕ), l≠[] → Valid l →
        Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) := by
  classical
  have hfinite (n : ℕ) := exists_full_unitary_finite_tests M R hRM τ hτ stage hmono
    hnormal hfaith hone hirr hgrow hstage hdiffuse
    (fun j : Fin (n+1) => x j) (fun i : Fin (n+1) => k i)
    (fun j => hx j) (fun j => hcenter j) (fun i => hk i) n
    (pow_pos (by norm_num : (0:ℝ)<1/2) n)
  choose u huR hu using hfinite
  have hbound (n : ℕ) : MomentBound τ (fun j => x (min j n)) (fun i => k (min i n))
      (PartialUnitary.ofUnitary (u n)) n ((1/2:ℝ)^n) := by
    let f : ℕ → Fin (n+1) := fun j => ⟨min j n,Nat.lt_succ_of_le (min_le_right _ _)⟩
    exact momentBound_reindex τ _ _ f f _ (hu n)
  have hlim : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨u,huR,?_,?_⟩
  · intro i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [eventually_ge_atTop i] with n hn
    simpa only [min_eq_left hn] using (hbound n).1 i
  · intro l hl hv
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [eventually_ge_atTop l.length,
      eventually_word_truncate x k (fun n => PartialUnitary.ofUnitary (u n)) l] with n hn he
    rw [←he]
    exact (hbound n).2 l hl hn hv

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.FinitePatching.exists_countable_unitary_tests_oai.{u_1, u_2} := @OAI.Kadison.FinitePatching.exists_countable_unitary_tests_oai.{u_1, u_2}

-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.exists_all_unitary_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:50:52.079671+00:00
-- url     : https://prove2.me/submissions/c1436d72-2a68-492f-989a-2332fcb18b06

import Mathlib
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_FinitePatching_Words_moment_limit_of_dense_coefficients
import Theorems.Thm_OAI_Kadison_FinitePatching_exists_countable_unitary_tests

section
-- module Solutions.OAIQ039_CM.Commutator_CenteredContractionDensity
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

namespace Kadison.TracialL2

open TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma exists_centered_contraction_dense_sequence [TopologicalSpace.SeparableSpace τ.GNS] :
    ∃ x : ℕ → A, (∀ j,‖x j‖ ≤ 1) ∧ (∀ j,τ (x j)=0) ∧
      ∀ a : A,‖a‖ ≤ 1 → τ a=0 → ∀ ε : ℝ,0<ε → ∃ j,norm τ (a-x j)<ε := by
  classical
  let C := {a : A // ‖a‖ ≤ 1 ∧ τ a=0}
  let S : Set τ.GNS := Set.range (fun a : C => algebraVector τ a.val)
  have : Nonempty S :=
    ⟨⟨algebraVector τ 0,⟨⟨0,by simp⟩,rfl⟩⟩⟩
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq S
  choose x hx using (fun n => (u n).property)
  refine ⟨fun n => (x n).val,fun n => (x n).property.1,fun n => (x n).property.2,?_⟩
  intro a ha hc ε hε
  obtain ⟨j,hj⟩ := hu.exists_dist_lt ⟨algebraVector τ a,⟨⟨a,ha,hc⟩,rfl⟩⟩ hε
  refine ⟨j,?_⟩
  change dist (algebraVector τ a) (u j).val<ε at hj
  rw [←hx j,dist_eq_norm,←map_sub] at hj
  simpa only [algebraVector_apply,UniformSpace.Completion.norm_coe,norm] using hj

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
-- module Solutions.OAIQ039_CM.Commutator_AllUnitaryTests
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

lemma integerEnumeration_surjective : Function.Surjective integerEnumeration := by
  let := Encodable.ofCountable NonzeroInteger
  intro k
  refine ⟨Encodable.encode k,?_⟩
  simp [integerEnumeration,Encodable.encodek]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_all_unitary_tests_oai [TopologicalSpace.SeparableSpace τ.GNS]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    ∃ u : ℕ → unitary M, (∀ n, ((u n:M) : H →L[ℂ] H)∈R) ∧
      (∀ k : ℤ,k≠0 → Tendsto (fun n => τ ((PartialUnitary.ofUnitary (u n)).power k)) atTop (𝓝 0)) ∧
      (∀ (J K : Type) (x : J → M) (k : K → ℤ), (∀ j,‖x j‖≤1) →
        (∀ j,τ (x j)=0) → (∀ i,k i≠0) →
        ∀ l : List (Letter J K), l≠[] → Valid l →
          Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) := by
  classical
  obtain ⟨x,hx,hxc,hxd⟩ := TracialL2.exists_centered_contraction_dense_sequence τ
  obtain ⟨u,huR,hpow,hword⟩ := exists_countable_unitary_tests M R hRM τ hτ stage hmono
    hnormal hfaith hone hirr hgrow hstage hdiffuse x (fun i => (integerEnumeration i).val)
    hx hxc (fun i => (integerEnumeration i).property)
  refine ⟨u,huR,?_,?_⟩
  · intro k hk
    obtain ⟨i,hi⟩ := integerEnumeration_surjective ⟨k,hk⟩
    simpa only [hi] using hpow i
  · intro J K y k hy hyc hk l hl hv
    choose g hg using (fun i => integerEnumeration_surjective ⟨k i,hk i⟩)
    have hl' (l' : List (Letter ℕ K)) (hne : l'≠[]) (hvl : Valid l') :
        Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l')) atTop (𝓝 0) := by
      have hh := hword (l'.map (mapLetter id g)) (by simpa using hne) (valid_map id g hvl)
      have he : (fun i => (integerEnumeration i).val) ∘ g=k := by
        funext i
        exact congrArg Subtype.val (hg i)
      simpa only [word_reindex,Function.comp_id,he] using hh
    exact moment_limit_of_dense_coefficients τ hτ hone x k hx hxd
      (fun n => PartialUnitary.ofUnitary (u n)) hl' y hy hyc l hl hv

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.FinitePatching.exists_all_unitary_tests_oai.{u_1, u_2} := @OAI.Kadison.FinitePatching.exists_all_unitary_tests_oai.{u_1, u_2}

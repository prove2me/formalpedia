-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.pullUnitary_moment_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:26:29.091772+00:00
-- url     : https://prove2.me/submissions/c2456e34-46f4-4601-b49a-93be1986766d

import Mathlib
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C035

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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

variable {A B J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace PartialUnitary

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_power (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) (k : ℤ) :
    φ (v.power k)=(v.map φ).power k := by
  cases k with
  | ofNat n => cases n <;> simp [power,map]
  | negSucc n => simp [power,map,map_star]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_ofUnitary (φ : A →⋆ₐ[ℂ] B) (u : unitary A) :
    (ofUnitary u).map φ=ofUnitary ⟨φ u,Unitary.map_mem φ u.property⟩ := by
  apply ext
  rfl

end PartialUnitary

namespace Words

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_slotPower (φ : A →⋆ₐ[ℂ] B) (k : K → ℤ) (v : PartialUnitary A) (s : Slot K) :
    φ (slotPower k v s)=slotPower k (v.map φ) s := by
  cases s with
  | none => exact map_one φ
  | some s =>
    cases s with
    | none => rfl
    | some i => exact v.map_power φ (k i)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_letter (φ : A →⋆ₐ[ℂ] B) (x : J → A) (k : K → ℤ) (v : PartialUnitary A) (i : Letter J K) :
    φ (letter x k v i)=letter (φ ∘ x) k (v.map φ) i := by
  simp only [letter,map_mul,map_slotPower,Function.comp_apply]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_word (φ : A →⋆ₐ[ℂ] B) (x : J → A) (k : K → ℤ) (v : PartialUnitary A) (l : List (Letter J K)) :
    φ (word x k v l)=word (φ ∘ x) k (v.map φ) l := by
  induction l with
  | nil => exact map_one φ
  | cons i l ih => simp only [word_cons,map_mul,map_letter,ih]

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryEquivMoments
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

lemma map_pullUnitary (e : A ≃⋆ₐ[ℂ] B) (u : unitary B) :
    (PartialUnitary.ofUnitary (pullUnitary e u)).map e.toStarAlgHom=PartialUnitary.ofUnitary u := by
  rw [PartialUnitary.map_ofUnitary]
  congr 1
  apply Subtype.ext
  exact e.apply_symm_apply u

lemma word_pullUnitary {J K : Type} (e : A ≃⋆ₐ[ℂ] B) (u : unitary B)
    (x : J → A) (k : K → ℤ) (l : List (Letter J K)) :
    e (word x k (PartialUnitary.ofUnitary (pullUnitary e u)) l)=
      word (e ∘ x) k (PartialUnitary.ofUnitary u) l := by
  rw [show e (word x k (PartialUnitary.ofUnitary (pullUnitary e u)) l)=
    word (e ∘ x) k ((PartialUnitary.ofUnitary (pullUnitary e u)).map e.toStarAlgHom) l from
    map_word e.toStarAlgHom x k _ l,map_pullUnitary]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma pullUnitary_moment_limits_oai (e : A ≃⋆ₐ[ℂ] B) (τ : A →ₚ[ℂ] ℂ) (σ : B →ₚ[ℂ] ℂ)
    (htrace : ∀ a,σ (e a)=τ a) (u : ℕ → unitary B)
    (hu : ∀ (J : Type) (x : J → B),(∀ j,‖x j‖≤1) → (∀ j,σ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => σ (word x signPower (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    ∀ (J : Type) (x : J → A),(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => τ (word x signPower (PartialUnitary.ofUnitary (pullUnitary e (u n))) l)) atTop (𝓝 0) := by
  intro J x hx hxc l hl hv
  have hh := hu J (e ∘ x) (fun j => by simpa only [Function.comp_apply,StarAlgEquiv.norm_map] using hx j)
    (fun j => (htrace (x j)).trans (hxc j)) l hl hv
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [←htrace,word_pullUnitary]

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.pullUnitary_moment_limits_oai := @OAI.Kadison.TracialSequence.pullUnitary_moment_limits_oai

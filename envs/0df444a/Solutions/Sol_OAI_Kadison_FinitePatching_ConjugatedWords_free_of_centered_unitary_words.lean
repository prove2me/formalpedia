-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.ConjugatedWords.free_of_centered_unitary_words
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:39:21.085809+00:00
-- url     : https://prove2.me/submissions/197f71d2-7a23-4456-9c1a-49b988c1f4ef

import Mathlib
import Definitions.Def_OAIQ039C035

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryHom
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

namespace Kadison.FinitePatching

variable {A B J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace PartialUnitary

omit [PartialOrder A] [StarOrderedRing A] in
lemma ofUnitary_power_one (u : unitary A) : (ofUnitary u).power 1=(u:A) := by
  simp [power,ofUnitary]

omit [PartialOrder A] [StarOrderedRing A] in
lemma ofUnitary_power_neg_one (u : unitary A) : (ofUnitary u).power (-1)=star (u:A) := by
  change star (u:A)^1=star (u:A)
  simp

end PartialUnitary

end Kadison.FinitePatching

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

end Kadison.FinitePatching.Words

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConjugatedWordAlgebra
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

namespace Kadison.FinitePatching.ConjugatedWords

open Words

variable {B J : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma transition_power (u : unitary B) (c d : Bool) :
    slotPower signPower (PartialUnitary.ofUnitary u) (transition c d)=
      star (leftUnitary u c:B)*(leftUnitary u d:B) := by
  cases c <;> cases d <;>
    simp [transition,signPower,slotPower,leftUnitary,
      PartialUnitary.ofUnitary_power_one,PartialUnitary.ofUnitary_power_neg_one,
      u.property.1]

lemma encode_ne_nil (color : J → Bool) (σ : Bool) {l : List J} (hl : l≠[]) :
    encode color σ l≠[] := by
  intro he
  have hh := congrArg List.length he
  simp only [encode_length,List.length_nil,List.length_eq_zero_iff] at hh
  exact hl hh

lemma encode_valid (color : J → Bool) (σ : Bool) {l : List J}
    (hl : l.IsChain (fun a b => color a≠color b)) : Valid (encode color σ l) := by
  induction l with
  | nil =>
    intro s i t he ht
    have hh := congrArg List.length he
    simp only [encode,List.length_nil,List.length_append,List.length_cons] at hh
    omega
  | cons a l ih =>
    rw [encode,valid_cons_iff]
    refine ⟨ih hl.tail,?_⟩
    intro hne
    cases l with
    | nil => exact (hne rfl).elim
    | cons b l =>
      have hab := (List.isChain_cons_cons.mp hl).1
      refine ⟨color a,?_⟩
      change (if color a=color b then (none : Slot Bool) else some (some (color a)))=some (some (color a))
      exact ite_eq_right hab

omit [PartialOrder B] [StarOrderedRing B] in
lemma word_encode (u : unitary B) (x : J → B) (color : J → Bool)
    (σ : Bool) (l : List J) :
    word x signPower (PartialUnitary.ofUnitary u) (encode color σ l)=
      star (leftUnitary u (front color σ l):B)*
        (l.map (fun a => (leftUnitary u (color a):B)*x a*star (leftUnitary u (color a):B))).prod*
        (leftUnitary u σ:B) := by
  induction l with
  | nil => simp only [encode,word_nil,List.map_nil,List.prod_nil,front,mul_one]; exact (leftUnitary u σ).property.1.symm
  | cons a l ih =>
    simp only [encode,word_cons,letter,transition_power,ih,List.map_cons,List.prod_cons,front]
    let v := leftUnitary u (color a)
    let w := leftUnitary u (front color σ l)
    let z := (l.map (fun a => (leftUnitary u (color a):B)*x a*star (leftUnitary u (color a):B))).prod
    change x a*(star (v:B)*(w:B))*(star (w:B)*z*(leftUnitary u σ:B))=
      star (v:B)*((v:B)*x a*star (v:B)*z)*(leftUnitary u σ:B)
    calc
      _=x a*star (v:B)*((w:B)*star (w:B))*z*(leftUnitary u σ:B) := by noncomm_ring
      _=x a*star (v:B)*z*(leftUnitary u σ:B) := by rw [w.property.2,mul_one]
      _=(star (v:B)*(v:B))*(x a*star (v:B)*z)*(leftUnitary u σ:B) := by rw [v.property.1,one_mul]
      _=_ := by noncomm_ring

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConjugatedFreeness
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

namespace Kadison.FinitePatching.ConjugatedWords

open Words

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (φ : A →⋆ₐ[ℂ] B) (u : unitary B)

variable (S : StarSubalgebra ℂ B) (ρ : B →ₗ[ℂ] ℂ)

omit [PartialOrder B] [StarOrderedRing B] in
lemma trace_unitary_conjugation (hρ : ∀ a∈S,∀ b∈S,ρ (a*b)=ρ (b*a))
    (v : unitary B) (hv : (v:B)∈S) (a : B) (ha : a∈S) :
    ρ ((v:B)*a*star (v:B))=ρ a := by
  calc
    _ = ρ ((a*star (v:B))*(v:B)) := by
      rw [mul_assoc]
      exact hρ _ hv _ (S.mul_mem ha (S.star_mem' hv))
    _ = ρ a := by rw [mul_assoc,v.property.1,mul_one]

omit [PartialOrder B] [StarOrderedRing B] in
include S in
theorem free_of_centered_unitary_words_oai (τ : A →ₗ[ℂ] ℂ)
    (hu : (u:B)∈S) (hφ : ∀ a,φ a∈S)
    (hρ : ∀ a∈S,∀ b∈S,ρ (a*b)=ρ (b*a))
    (htrace : ∀ a,ρ (φ a)=τ a)
    (hword : ∀ (J : Type) (x : J → A),(∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        ρ (word (φ ∘ x) signPower (PartialUnitary.ofUnitary u) l)=0) :
    FreeMoments.Free (pair φ u) ρ := by
  classical
  let J := FreeMoments.Letter (pair φ u) ρ
  have hpre (a : J) : ∃ x : A,τ x=0 ∧
      a.val=if a.color then φ x else (u:B)*φ x*star (u:B) := by
    cases hc : a.color with
    | false =>
      obtain ⟨x,hx⟩ := (show a.val∈((Unitary.conjStarAlgAut ℂ B u).toStarAlgHom.comp φ).range from by
        simpa only [pair,hc,Bool.false_eq_true,ite_false] using a.mem)
      have he : (u:B)*φ x*star (u:B)=a.val := hx
      refine ⟨x,?_,by simpa only [hc,Bool.false_eq_true,ite_false] using he.symm⟩
      rw [←htrace,←trace_unitary_conjugation S ρ hρ u hu (φ x) (hφ x),he]
      exact a.centered
    | true =>
      obtain ⟨x,hx⟩ := (show a.val∈φ.range from by simpa only [pair,hc,ite_true] using a.mem)
      change φ x=a.val at hx
      refine ⟨x,?_,by simpa only [hc,ite_true] using hx.symm⟩
      rw [←htrace,hx]
      exact a.centered
  choose x hxc hx using hpre
  have hval (a : J) : (leftUnitary u a.color:B)*φ (x a)*star (leftUnitary u a.color:B)=a.val := by
    cases hc : a.color <;> simpa [leftUnitary,hc] using (hx a).symm
  have hmem (a : J) : a.val∈S := by
    rw [←hval a]
    have hleft : (leftUnitary u a.color:B)∈S := by
      cases a.color <;> simp only [leftUnitary] <;> first | exact hu | exact S.one_mem
    exact S.mul_mem (S.mul_mem hleft (hφ _)) (S.star_mem' hleft)
  intro w hw hne
  have hwmem : FreeMoments.word w∈S := by
    clear hw hne
    induction w with
    | nil => exact S.one_mem
    | cons a l ih => exact S.mul_mem (hmem a) ih
  cases w with
  | nil => exact (hne rfl).elim
  | cons a l =>
    let σ := a.color
    let c : J → Bool := FreeMoments.Letter.color
    have hv := encode_valid c σ (show (a::l).IsChain (fun a b : J => c a≠c b) from hw)
    have hz := hword J x hxc (encode c σ (a::l)) (encode_ne_nil c σ (by simp)) hv
    rw [word_encode] at hz
    have he : ((a::l).map (fun a => (leftUnitary u (c a):B)*(φ ∘ x) a*star (leftUnitary u (c a):B))).prod=
        FreeMoments.word (a::l) := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro j _
      exact hval j
    rw [he] at hz
    change ρ (star (leftUnitary u σ:B)*FreeMoments.word (a::l)*(leftUnitary u σ:B))=0 at hz
    have hleft : (star (leftUnitary u σ):B)∈S := by
      apply S.star_mem'
      cases σ <;> simp only [leftUnitary] <;> first | exact hu | exact S.one_mem
    have ht := trace_unitary_conjugation S ρ hρ (star (leftUnitary u σ)) hleft _ hwmem
    simp only [Unitary.coe_star,star_star] at ht
    exact ht.symm.trans hz

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FinitePatching.ConjugatedWords.free_of_centered_unitary_words_oai := @OAI.Kadison.FinitePatching.ConjugatedWords.free_of_centered_unitary_words_oai

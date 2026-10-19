-- Prove2me | solution 1 for OAI.UniversalFInfinity.CountableOvergroup.countable_embeds_three_generated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:53:29.997922+00:00
-- url     : https://prove2.me/submissions/c4cf621e-c21b-4088-80a2-db45e1e64fd1

import Mathlib
import Definitions.Def_OAIQWUFI006

section
-- module Solutions.OAIQW_UniversalFInfinity.UniversalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x
noncomputable section

namespace UniversalFInfinity.CountableOvergroup
open Monoid
variable {C : Type u} [Group C] (c : ℕ → C)

lemma embed_injective : Function.Injective (embed c) :=
  (HNNExtension.of_injective (φ := associated c)).comp Coprod.inl_injective

lemma closure_three_of_generates (hc : Subgroup.closure (Set.range c) = ⊤) :
    Subgroup.closure ({a c,p c,t c} : Set (Overgroup c)) = ⊤ := by
  let S := Subgroup.closure ({a c,p c,t c} : Set (Overgroup c))
  have ha : a c ∈ S := Subgroup.subset_closure (by simp)
  have hp : p c ∈ S := Subgroup.subset_closure (by simp)
  have ht : t c ∈ S := Subgroup.subset_closure (by simp)
  have hgen : Set.range c ⊆ S.comap (embed c) := by
    rintro _ ⟨i,rfl⟩
    change embed c (c i) ∈ S
    rw [generator_formula]
    have hv := S.mul_mem (S.mul_mem (S.pow_mem ha i) hp) (S.inv_mem (S.pow_mem ha i))
    exact S.mul_mem (S.mul_mem (S.mul_mem ht hv) (S.inv_mem ht)) (S.inv_mem hv)
  have htop : ⊤ ≤ S.comap (embed c) := by
    rw [← hc]
    exact (Subgroup.closure_le _).mpr hgen
  have hcS (g : C) : embed c g ∈ S := htop (Subgroup.mem_top g)
  have hfS (g : FreeConjugates.Two) :
      (HNNExtension.of (Coprod.inr g) : Overgroup c) ∈ S := by
    induction g using FreeGroup.induction_on with
    | C1 => simp
    | of b => cases b <;> assumption
    | inv_of g hg => simpa only [map_inv] using S.inv_mem hg
    | mul g h hg hh => simpa only [map_mul] using S.mul_mem hg hh
  apply top_unique
  intro g hg
  clear hg
  change g ∈ S
  induction g using HNNExtension.induction_on with
  | of g =>
    induction g using Coprod.induction_on with
    | inl g => exact hcS g
    | inr g => exact hfS g
    | mul g h hg hh => simpa only [map_mul] using S.mul_mem hg hh
  | t => exact ht
  | mul g h hg hh => exact S.mul_mem hg hh
  | inv g hg => exact S.inv_mem hg

lemma closure_three (hc : Function.Surjective c) :
    Subgroup.closure ({a c,p c,t c} : Set (Overgroup c)) = ⊤ :=
  closure_three_of_generates c (by rw [Set.range_eq_univ.mpr hc,Subgroup.closure_univ])

lemma finitely_generated (hc : Function.Surjective c) : Group.FG (Overgroup c) :=
  Group.fg_iff.mpr ⟨{a c,p c,t c},closure_three c hc,by simp⟩

theorem countable_embeds_three_generated_oai [Countable C] :
    ∃ (V : Type u) (_ : Group V) (_ : Group.FG V),
      ∃ e : C →* V, Function.Injective e := by
  obtain ⟨c,hc⟩ := exists_surjective_nat C
  exact ⟨Overgroup c,inferInstance,finitely_generated c hc,embed c,embed_injective c⟩

end UniversalFInfinity.CountableOvergroup

end
end UniversalFinitelyPresentedProof

end OAI
end

theorem solution.{u} : type_of% @OAI.UniversalFInfinity.CountableOvergroup.countable_embeds_three_generated_oai.{u} := @OAI.UniversalFInfinity.CountableOvergroup.countable_embeds_three_generated_oai.{u}

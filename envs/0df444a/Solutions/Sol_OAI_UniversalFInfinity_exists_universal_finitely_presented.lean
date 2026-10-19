-- Prove2me | solution 1 for OAI.UniversalFInfinity.exists_universal_finitely_presented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:57:47.251208+00:00
-- url     : https://prove2.me/submissions/346bb79b-8593-4bf9-930d-9af8e2366257

import Mathlib
import Definitions.Def_OAIQWUFI008
import Theorems.Thm_OAI_Higman_NormalWords_embeds_presentation

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

end UniversalFInfinity.CountableOvergroup

namespace UniversalFInfinity.ThreePresentation
open Monoid

variable (rels : Set (FreeGroup ℕ))

lemma fromC_of (i : ℕ) : fromC rels (PresentedGroup.of i) =
    (PresentedGroup.mk (substitute '' rels))
      (T * conjugate i * T⁻¹ * (conjugate i)⁻¹) := by
  change (PresentedGroup.mk _) (substitute (FreeGroup.of i)) = _
  rw [substitute,FreeGroup.lift_apply_of]

lemma toV_comp_fromC : (toV rels).comp (fromC rels) =
    CountableOvergroup.embed (PresentedGroup.of (rels := rels)) := by
  apply PresentedGroup.ext
  intro i
  rw [MonoidHom.comp_apply,fromC_of]
  change (FreeGroup.lift (generator rels))
    (T * conjugate i * T⁻¹ * (conjugate i)⁻¹) = _
  simp only [map_mul,map_inv,conjugate,map_pow,T,A,P,FreeGroup.lift_apply_of,generator]
  exact (CountableOvergroup.generator_formula _ i).symm

theorem fromC_injective : Function.Injective (fromC rels) := by
  apply Function.Injective.of_comp (f := toV rels)
  rw [← MonoidHom.coe_comp,toV_comp_fromC]
  exact CountableOvergroup.embed_injective _

end UniversalFInfinity.ThreePresentation

namespace UniversalFInfinity.RecursiveUniversal

lemma retract_embed (P : Code) : (retract P).comp (embed P) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  change FreeGroup.lift (project P) (FreeGroup.map (Nat.pair (Encodable.encode P))
    (FreeGroup.of i)) = PresentedGroup.of i
  simp [project]

lemma embed_injective (P : Code) : Function.Injective (embed P) := by
  apply Function.Injective.of_comp (f := retract P)
  rw [← MonoidHom.coe_comp,retract_embed]
  exact Function.injective_id

lemma renameRetract_comp {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    (renameRetract i s).comp (rename i s) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro a
  change FreeGroup.lift (renameValues i s) (FreeGroup.map i (FreeGroup.of a)) =
    PresentedGroup.of a
  simp [renameValues,i.injective.extend_apply]

lemma rename_injective {α β : Type*} (i : α ↪ β) (s : Set (FreeGroup α)) :
    Function.Injective (rename i s) := by
  apply Function.Injective.of_comp (f := renameRetract i s)
  rw [← MonoidHom.coe_comp,renameRetract_comp]
  exact Function.injective_id

lemma code_exists (s : Set (FreeGroup ℕ)) (hs : s.Finite) : ∃ P : Code, relations P = s := by
  classical
  refine ⟨hs.toFinset.toList.map FreeGroup.toWord,?_⟩
  ext r
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hw
    rw [FreeGroup.mk_toWord]
    exact hs.mem_toFinset.mp (Finset.mem_toList.mp hq)
  · intro hr
    refine ⟨r.toWord,?_,FreeGroup.mk_toWord⟩
    exact List.mem_map.mpr ⟨r,Finset.mem_toList.mpr (hs.mem_toFinset.mpr hr),rfl⟩

theorem universal {G : Type*} [Group G] [Group.IsFinitelyPresented G] :
    ∃ h : G →* Universal, Function.Injective h := by
  classical
  obtain ⟨n,s,hs,⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := G)
  let i : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  obtain ⟨P,hP⟩ := code_exists (FreeGroup.map i '' s) (hs.image _)
  let eP : PresentedGroup (FreeGroup.map i '' s) ≃* PresentedGroup (relations P) :=
    QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure hP.symm)
  exact ⟨(embed P).comp (eP.toMonoidHom.comp ((rename i s).comp e.toMonoidHom)),
    (embed_injective P).comp (eP.injective.comp ((rename_injective i s).comp e.injective))⟩

lemma rawAt_primrec : Primrec₂ rawAt := by
  unfold rawAt
  exact (Primrec.list_getD []).comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const [])) Primrec.snd

lemma colour_primrec : Primrec₂ colour := by
  unfold Primrec₂ colour
  apply Primrec.list_map Primrec.snd
  exact (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)

theorem relator_primrec : Primrec relator := by
  unfold relator
  exact colour_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (rawAt_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

end UniversalFInfinity.RecursiveUniversal

namespace UniversalFInfinity.RecursiveUniversalThree
open ThreePresentation

lemma mk_positive (i : ℕ) : FreeGroup.mk (positive i) = A ^ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [positive,List.replicate_succ]
    change A * FreeGroup.mk (positive i) = A ^ (i+1)
    rw [ih,pow_succ']

lemma mk_v (i : ℕ) : FreeGroup.mk (v i) = conjugate i := by
  simp only [v,← FreeGroup.mul_mk,← FreeGroup.inv_mk,mk_positive,conjugate]
  rfl

lemma mk_replacement (i : ℕ) : FreeGroup.mk (replacement i) =
    substitute (FreeGroup.of i) := by
  simp only [replacement,← FreeGroup.mul_mk,← FreeGroup.inv_mk,mk_v,
    substitute,FreeGroup.lift_apply_of]
  rfl

lemma mk_substituteRaw (w : RecursiveUniversal.Word) : FreeGroup.mk (substituteRaw w) =
    substitute (FreeGroup.mk w) := by
  induction w with
  | nil => exact (map_one substitute).symm
  | cons x w ih =>
    rcases x with ⟨i,b⟩
    cases b with
    | false =>
      change FreeGroup.mk (FreeGroup.invRev (replacement i) ++ substituteRaw w) =
        substitute ((FreeGroup.of i)⁻¹ * FreeGroup.mk w)
      rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,mk_replacement,map_mul,map_inv,ih]
    | true =>
      change FreeGroup.mk (replacement i ++ substituteRaw w) =
        substitute (FreeGroup.of i * FreeGroup.mk w)
      rw [← FreeGroup.mul_mk,mk_replacement,map_mul,ih]

lemma enumerated_relations : Set.range (fun k => FreeGroup.mk (enumerator k)) =
    substitute '' RecursiveUniversal.allRelations := by
  ext r
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨FreeGroup.mk (RecursiveUniversal.relator k),⟨k,rfl⟩,(mk_substituteRaw _).symm⟩
  · rintro ⟨_,⟨k,rfl⟩,rfl⟩
    exact ⟨k,mk_substituteRaw _⟩

lemma invRev_primrec : Primrec (@FreeGroup.invRev Alphabet) := by
  unfold FreeGroup.invRev
  apply Primrec.list_reverse.comp
  apply Primrec.list_map Primrec.id
  exact (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.dom_bool Bool.not).comp (Primrec.snd.comp Primrec.snd))

lemma positive_primrec : Primrec positive := by
  have h : Primrec (fun i : ℕ => (List.range i).map (fun _ => ((Sum.inl false,true) : Alphabet × Bool))) :=
    Primrec.list_map Primrec.list_range (Primrec₂.const _)
  apply h.of_eq
  intro i
  simp only [List.map_const',List.length_range,positive]

lemma v_primrec : Primrec v :=
  Primrec.list_append.comp
    (Primrec.list_append.comp positive_primrec (Primrec.const _))
    (invRev_primrec.comp positive_primrec)

lemma replacement_primrec : Primrec replacement :=
  Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.const _) v_primrec) (Primrec.const _))
    (invRev_primrec.comp v_primrec)

lemma substituteRaw_primrec : Primrec substituteRaw := by
  have h : Primrec (fun x : ℕ × Bool =>
      if x.2 then replacement x.1 else FreeGroup.invRev (replacement x.1)) := by
    apply (Primrec.cond Primrec.snd (replacement_primrec.comp Primrec.fst)
      (invRev_primrec.comp (replacement_primrec.comp Primrec.fst))).of_eq
    intro x
    cases x.2 <;> rfl
  exact Primrec.list_flatMap Primrec.id (h.comp Primrec.snd)

theorem enumerator_primrec : Primrec enumerator :=
  substituteRaw_primrec.comp RecursiveUniversal.relator_primrec

theorem universal {G : Type*} [Group G] [Group.IsFinitelyPresented G] :
    ∃ h : G →* Universal, Function.Injective h := by
  obtain ⟨e,he⟩ := RecursiveUniversal.universal (G := G)
  let q := QuotientGroup.quotientMulEquivOfEq
    (congrArg Subgroup.normalClosure enumerated_relations.symm)
  exact ⟨q.toMonoidHom.comp ((ThreePresentation.fromC _).comp e),
    q.injective.comp ((ThreePresentation.fromC_injective _).comp he)⟩

end UniversalFInfinity.RecursiveUniversalThree

namespace UniversalFInfinity
universe z

theorem exists_universal_finitely_presented_oai :
    ∃ (U : Type) (_ : Group U) (_ : Group.IsFinitelyPresented U),
      ∀ (G : Type z) [Group G] [Group.IsFinitelyPresented G],
        ∃ i : G →* U, Function.Injective i := by
  obtain ⟨U,gU,fpU,i,hi⟩ := Higman.NormalWords.embeds_presentation
    RecursiveUniversalThree.enumerator RecursiveUniversalThree.enumerator_primrec.to_comp
  refine ⟨U,gU,fpU,?_⟩
  intro G _ _
  obtain ⟨j,hj⟩ := RecursiveUniversalThree.universal (G := G)
  exact ⟨i.comp j,hi.comp hj⟩

end UniversalFInfinity

end
end UniversalFinitelyPresentedProof

end OAI
end

theorem solution.{z} : type_of% @OAI.UniversalFInfinity.exists_universal_finitely_presented_oai.{z} := @OAI.UniversalFInfinity.exists_universal_finitely_presented_oai.{z}

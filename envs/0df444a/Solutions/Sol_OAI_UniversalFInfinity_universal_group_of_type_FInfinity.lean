-- Prove2me | solution 1 for OAI.UniversalFInfinity.universal_group_of_type_FInfinity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:57:48.701985+00:00
-- url     : https://prove2.me/submissions/60a998ce-43e5-451d-938b-7b141293c00c

import Mathlib
import Definitions.Def_UniversalFInfinity
import Definitions.Def_OAIQWUFI008
import Theorems.Thm_OAI_Higman_NormalWords_embeds_presentation
import Theorems.Thm_OAI_UniversalFInfinity_Brown_geometric_lifted_of_uniform
import Theorems.Thm_OAI_UniversalFInfinity_Milnor_contractible

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

end
end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.FiniteEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity

section

variable {K D V : Type*} [Field K] [Ring D] [Algebra K D] [Group V]

lemma diagramElement_eq (e : D) (v : V) :
    diagramElement (K := K) e v =
      1 + e ⊗ₜ[K] (MonoidAlgebra.of K V v - 1) := by
  simp only [diagramElement, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  rw [← Algebra.TensorProduct.one_def]
  abel

lemma diagramElement_orthogonal_mul (e p : D) (hep : e * p = 0) (v w : V) :
    diagramElement (K := K) e v * diagramElement (K := K) p w =
      1 + e ⊗ₜ[K] (MonoidAlgebra.of K V v - 1) +
        p ⊗ₜ[K] (MonoidAlgebra.of K V w - 1) := by
  rw [diagramElement_eq, diagramElement_eq]
  simp only [add_mul, mul_add, one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul,
    hep, TensorProduct.zero_tmul, add_zero]

lemma diagramElement_commute (e p : D) (hep : e * p = 0) (hpe : p * e = 0)
    (v w : V) :
    Commute (diagramElement (K := K) e v) (diagramElement (K := K) p w) := by
  show _ * _ = _ * _
  rw [diagramElement_orthogonal_mul e p hep, diagramElement_orthogonal_mul p e hpe]
  abel

lemma diagramElement_add (e p : D) (hep : e * p = 0) (v : V) :
    diagramElement (K := K) (e + p) v =
      diagramElement (K := K) e v * diagramElement (K := K) p v := by
  rw [diagramElement_orthogonal_mul e p hep, diagramElement_eq,
    TensorProduct.add_tmul, add_assoc]

lemma diagramHom_commute (e p : D) (he : e * e = e) (hp : p * p = p)
    (hep : e * p = 0) (hpe : p * e = 0) (v w : V) :
    Commute (diagramHom (K := K) e he v) (diagramHom (K := K) p hp w) := by
  apply Units.ext
  exact diagramElement_commute e p hep hpe v w

lemma diagramHom_identity_injective [Nontrivial D] :
    Function.Injective (diagramHom (K := K) (1 : D) (one_mul _) :
      V →* (ModelAlgebra K D V)ˣ) := by
  intro v w h
  have h' := congrArg Units.val h
  simp only [diagramHom_identity_val] at h'
  have h'' := Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap K D)) h'
  exact MonoidAlgebra.of_injective h''

end

namespace FiniteEnvelope

variable {I X : Type*}

variable (r : Set (FreeGroup X)) (S : Set (I × I)) (T : Set (I × I × I))

lemma copy_same (s : S) : copy r S T s.val.1 = copy r S T s.val.2 := by
  apply PresentedGroup.ext
  intro x
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨.inr (.inl (s, x)), rfl⟩

lemma copy_of_commute (t : T) (x y : X) :
    Commute (copy r S T t.val.1 (.of x)) (copy r S T t.val.2.1 (.of y)) := by
  change PresentedGroup.mk _ (_ * _) = PresentedGroup.mk _ (_ * _)
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨.inr (.inr (.inl (t, x, y))), rfl⟩

lemma copy_of_sum (t : T) (x : X) :
    copy r S T t.val.2.2 (.of x) =
      copy r S T t.val.1 (.of x) * copy r S T t.val.2.1 (.of x) := by
  change PresentedGroup.mk _ _ = PresentedGroup.mk _ (_ * _)
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨.inr (.inr (.inr (t, x))), rfl⟩

variable {r S T}

lemma commute_of_generators {G : Type*} [Group G]
    (f g : PresentedGroup r →* G)
    (h : ∀ x y : X, Commute (f (.of x)) (g (.of y)))
    (u v : PresentedGroup r) : Commute (f u) (g v) := by
  have h₁ (x : X) (v : PresentedGroup r) : Commute (f (.of x)) (g v) := by
    have hv := PresentedGroup.generated_by r
      ((Subgroup.centralizer {f (.of x)}).comap g)
      (fun y => Subgroup.mem_centralizer_singleton_iff.mpr (h x y).eq.symm) v
    exact (Subgroup.mem_centralizer_singleton_iff.mp hv).symm
  have hu := PresentedGroup.generated_by r
    ((Subgroup.centralizer {g v}).comap f)
    (fun x => Subgroup.mem_centralizer_singleton_iff.mpr (h₁ x v).eq) u
  exact Subgroup.mem_centralizer_singleton_iff.mp hu

lemma copy_commute (t : T) (u v : PresentedGroup r) :
    Commute (copy r S T t.val.1 u) (copy r S T t.val.2.1 v) :=
  commute_of_generators _ _ (copy_of_commute r S T t) u v

lemma copy_sum (t : T) (u : PresentedGroup r) :
    copy r S T t.val.2.2 u = copy r S T t.val.1 u * copy r S T t.val.2.1 u := by
  have h : copy r S T t.val.2.2 =
      commutingProduct (copy r S T t.val.1) (copy r S T t.val.2.1) (copy_commute t) := by
    apply PresentedGroup.ext
    exact copy_of_sum r S T t
  exact DFunLike.congr_fun h u

variable {G : Type*} [Group G]
variable (h : I → PresentedGroup r →* G)
variable (hsame : ∀ s : S, h s.val.1 = h s.val.2)
variable (hcomm : ∀ t : T, ∀ u v, Commute (h t.val.1 u) (h t.val.2.1 v))
variable (hsum : ∀ t : T, ∀ u, h t.val.2.2 u = h t.val.1 u * h t.val.2.1 u)

include hsame hcomm hsum

lemma copy_injective_of_model (i : I) (hi : Function.Injective (h i)) :
    Function.Injective (copy r S T i) := by
  have hc := modelMap_copy h hsame hcomm hsum i
  intro u v huv
  apply hi
  have hv := congrArg (modelMap h hsame hcomm hsum) huv
  simpa only [← MonoidHom.comp_apply, hc] using hv

end FiniteEnvelope

namespace TwoEnvelope

variable {K₂ K₃ D₂ D₃ : Type}
variable [Field K₂] [Field K₃] [Ring D₂] [Ring D₃]
variable [Algebra K₂ D₂] [Algebra K₃ D₃]
variable (P₂ : FiniteIdempotentSystem D₂) (P₃ : FiniteIdempotentSystem D₃)

variable (V : Type) [Group V]

variable {P₂ P₃ V}

lemma family_common (s : common P₂ P₃) :
    family (K₂ := K₂) (K₃ := K₃) P₂ P₃ V s.val.1 = family P₂ P₃ V s.val.2 := by
  rcases s with ⟨s, hs⟩
  have hs' : s = (.inl P₂.identity, .inr P₃.identity) := hs
  subst s
  rfl

lemma family_commute (t : triples P₂ P₃) (u v : V) :
    Commute (family (K₂ := K₂) (K₃ := K₃) P₂ P₃ V t.val.1 u)
      (family P₂ P₃ V t.val.2.1 v) := by
  rcases t with ⟨⟨e, p, s⟩, ht⟩
  rcases e with e | e <;> rcases p with p | p <;> rcases s with s | s <;>
    simp only [triples, Set.mem_ofPred_eq] at ht
  · rcases ht with ⟨hep, hpe, _⟩
    exact (diagramHom_commute (K := K₂) e.val p.val (P₂.isIdempotent e)
      (P₂.isIdempotent p) hep hpe u v).map
      (diagramHom (K := K₃) (1 : D₃) (one_mul _))
  · rcases ht with ⟨hep, hpe, _⟩
    exact diagramHom_commute (K := K₃) e.val p.val (P₃.isIdempotent e)
      (P₃.isIdempotent p) hep hpe _ _

lemma family_sum (t : triples P₂ P₃) (u : V) :
    family (K₂ := K₂) (K₃ := K₃) P₂ P₃ V t.val.2.2 u =
      family P₂ P₃ V t.val.1 u * family P₂ P₃ V t.val.2.1 u := by
  rcases t with ⟨⟨e, p, s⟩, ht⟩
  rcases e with e | e <;> rcases p with p | p <;> rcases s with s | s <;>
    simp only [triples, Set.mem_ofPred_eq] at ht
  · rcases ht with ⟨hep, _hpe, hs⟩
    change diagramHom (K := K₃) (1 : D₃) (one_mul _) (diagramHom s.val _ u) = _
    have heq : diagramHom (K := K₂) s.val (P₂.isIdempotent s) u =
        diagramHom e.val (P₂.isIdempotent e) u * diagramHom p.val (P₂.isIdempotent p) u := by
      apply Units.ext
      change diagramElement (K := K₂) s.val u = _
      rw [hs]
      exact diagramElement_add _ _ hep u
    rw [heq, map_mul]
    rfl
  · rcases ht with ⟨hep, _hpe, hs⟩
    apply Units.ext
    let w := diagramHom (K := K₂) (1 : D₂) (one_mul _) u
    change diagramElement (K := K₃) s.val w =
      diagramElement e.val w * diagramElement p.val w
    rw [hs]
    exact diagramElement_add _ _ hep _

lemma family_identity_injective [Nontrivial D₂] [Nontrivial D₃] :
    Function.Injective (family (K₂ := K₂) (K₃ := K₃) P₂ P₃ V (.inl P₂.identity)) :=
  (diagramHom_identity_injective (K := K₃) (D := D₃)).comp
    (diagramHom_identity_injective (K := K₂) (D := D₂))

variable (K₂ K₃ P₂ P₃ V)
include K₂ K₃

theorem finite_envelope [Nontrivial D₂] [Nontrivial D₃] [Group.IsFinitelyPresented V] :
    ∃ (W : Type) (_ : Group W), Group.IsFinitelyPresented W ∧
      ∃ k : Index P₂ P₃ → V →* W,
        k (.inl P₂.identity) = k (.inr P₃.identity) ∧
        Function.Injective (k (.inl P₂.identity)) ∧
        (∀ t : triples P₂ P₃, ∀ u v,
          Commute (k t.val.1 u) (k t.val.2.1 v)) ∧
        (∀ t : triples P₂ P₃, ∀ u,
          k t.val.2.2 u = k t.val.1 u * k t.val.2.1 u) := by
  obtain ⟨n, r, hr, ⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := V)
  let : Finite r := hr
  let k (i : Index P₂ P₃) :=
    (FiniteEnvelope.copy r (common P₂ P₃) (triples P₂ P₃) i).comp e.toMonoidHom
  refine ⟨FiniteEnvelope.Envelope r (common P₂ P₃) (triples P₂ P₃),
    inferInstance, inferInstance, k, ?_, ?_, ?_, ?_⟩
  · have hc := FiniteEnvelope.copy_same r (common P₂ P₃) (triples P₂ P₃)
      ⟨(.inl P₂.identity, .inr P₃.identity), rfl⟩
    exact congrArg (fun φ => φ.comp e.toMonoidHom) hc
  · have hi := FiniteEnvelope.copy_injective_of_model
      (family (K₂ := K₂) (K₃ := K₃) P₂ P₃ (PresentedGroup r))
      family_common family_commute family_sum (.inl P₂.identity) family_identity_injective
    exact hi.comp e.injective
  · intro t u v
    exact FiniteEnvelope.copy_commute t (e u) (e v)
  · intro t u
    exact FiniteEnvelope.copy_sum t (e u)

end TwoEnvelope
end UniversalFInfinity

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Idempotents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity

namespace ConcreteEnvelopes

open PrefixAlgebra IdempotentSystems

theorem finite_envelope (V : Type) [Group V] [Group.IsFinitelyPresented V] :
    ∃ (W : Type) (_ : Group W), Group.IsFinitelyPresented W ∧
      ∃ k : Index → V →* W, IsDiagram k ∧
        Function.Injective (k (.inl P₂.identity)) := by
  obtain ⟨W, hW, hfp, k, hc, hi, hcomm, hsum⟩ :=
    TwoEnvelope.finite_envelope (ZMod 2) (ZMod 3) P₂ P₃ V
  exact ⟨W, hW, hfp, k, ⟨hc, hcomm, hsum⟩, hi⟩

theorem self_maps (U : Type) [Group U] [Group.IsFinitelyPresented U]
    (hU : IsUniversal U) :
    ∃ k : Index → U →* U, IsDiagram k ∧
      Function.Injective (k (.inl P₂.identity)) := by
  obtain ⟨W, hW, hfp, k, hk, hi⟩ := finite_envelope U
  let := hW
  let := hfp
  obtain ⟨κ, hκ⟩ := hU W
  refine ⟨fun E => κ.comp (k E), ⟨?_, ?_, ?_⟩, hκ.comp hi⟩
  · rw [hk.common]
  · intro E u v
    exact (hk.commute E u v).map κ
  · intro E u
    simp only [MonoidHom.comp_apply, hk.sum E, map_mul]

end ConcreteEnvelopes
end UniversalFInfinity

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.SphereHomotopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Milnor

open Set Metric Topology Cellular UniversalFInfinity.Simplicial ConcreteEnvelopes
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]
  [TopologicalSpace G] [DiscreteTopology G]

local instance (priority := 2000) instDecidableEqProdNat_solutions_15_r3f1a60_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
omit [Group.IsFinitelyPresented G] [TopologicalSpace G] [DiscreteTopology G] in
lemma stage_bounded_dimension (S : Shapes G) :
    ∃ d : ℕ, Skeleton (univ : Set (Stage G S)) d = univ := by
  classical
  let d := (basedShapes G S).sup Finset.card
  refine ⟨d,Set.eq_univ_of_forall (fun x => ?_)⟩
  have hx : x ∈ (univ : Set (Stage G S)) := Set.mem_univ _
  rw [←CWComplex.iUnion_openCell_eq_complex (C := (univ : Set (Stage G S)))] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨n,i,hi⟩ := hx
  obtain ⟨g,s,hs,his⟩ := i.1.2.2
  have hn : n < d := by
    have hcard := Finset.card_le_card his
    rw [translate_card] at hcard
    rw [i.2] at hcard
    have hd := Finset.le_sup (f := Finset.card) hs
    omega
  exact CWComplex.skeletonLT_mono (C := (univ : Set (Stage G S)))
    (m := (n : ℕ∞)+1) (n := (d : ℕ∞)) (by exact_mod_cast Nat.succ_le_of_lt hn)
    (CWComplex.closedCell_subset_skeletonLT n i (CWComplex.openCell_subset_closedCell n i hi))

omit [Group.IsFinitelyPresented G] [TopologicalSpace G] [DiscreteTopology G] in
lemma Represents.comp {S T R : Shapes G} {f g : G →* G}
    {q : C(Stage G S,Stage G T)} {r : C(Stage G T,Stage G R)}
    (hr : Represents g r) (hq : Represents f q) : Represents (g.comp f) (r.comp q) := by
  intro x
  rw [show (r.comp q) x = r (q x) from rfl,hr,hq,←Finsupp.mapDomain_comp]
  rfl

variable (k : Index → G →* G) (hk : IsDiagram k)
lemma ghostMap_represents (S : Shapes G) (n : ℕ) :
    Represents (k (.inl P₂.identity)) (ghostMap k hk S n) :=
  (uniform_diagram_sphere_ghost k hk (ghostShapes k hk S n) (n+1)).choose_spec.choose_spec.1
lemma ghostMap_kills (S : Shapes G) (n : ℕ) : KillsSpheres (ghostMap k hk S n) (n+1) :=
  (uniform_diagram_sphere_ghost k hk (ghostShapes k hk S n) (n+1)).choose_spec.choose_spec.2

lemma ghostComposite_represents (S : Shapes G) (n : ℕ) :
    Represents (iterateHom (k (.inl P₂.identity)) n)
      (towerComposite (fun i => Stage G (ghostShapes k hk S i)) (ghostMap k hk S)
        (ContinuousMap.id (Stage G S)) n) := by
  induction n with
  | zero => exact Represents.id S
  | succ n ih =>
    exact (ghostMap_represents k hk S n).comp ih

include hk in

theorem diagram_uniform_stage_nullhomotopy (S : Shapes G) :
    ∃ (d : ℕ) (T : Shapes G) (q : C(Stage G S,Stage G T)) (z : Stage G T),
      Represents (iterateHom (k (.inl P₂.identity)) d) q ∧
      Nonempty (q.Homotopy (ContinuousMap.const _ z)) := by
  obtain ⟨d,hd⟩ := stage_bounded_dimension S
  let Y : ℕ → Type := fun i => Stage G (ghostShapes k hk S i)
  let q := ghostMap k hk S
  let a := towerComposite Y q (ContinuousMap.id (Stage G S)) d
  let b := towerComposite Y q (ContinuousMap.const (Stage G S) (stagePoint G S)) d
  have hb : ∀ x,b x = a (stagePoint G S) := by
    intro x
    change towerComposite Y q (ContinuousMap.const (Stage G S) (stagePoint G S)) d x =
      towerComposite Y q (ContinuousMap.id (Stage G S)) d (stagePoint G S)
    clear hd a b
    induction d with
    | zero => rfl
    | succ d ih => exact congrArg (q d) ih
  refine ⟨d,ghostShapes k hk S d,a,a (stagePoint G S),ghostComposite_represents k hk S d,?_⟩
  have H := towerHomotopy Y q (ContinuousMap.id (Stage G S))
    (ContinuousMap.const (Stage G S) (stagePoint G S)) (ghostMap_kills k hk S) d hd
  exact ⟨H.cast rfl (ContinuousMap.ext hb)⟩
end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.GraphBundles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

omit [TopologicalSpace C] [DiscreteTopology C] in
lemma edge_preimage_vertices (S : Set (C × A)) (c : C) :
    (fun z : I × B => edge τ L R c z.1 z.2) ⁻¹'
      ((fun z : C × A => vertex τ L R z.1 z.2) '' S) =
    ({0} ×ˢ ((fun x => (c,L c x)) ⁻¹' S)) ∪
      ({1} ×ˢ ((fun x => (τ c,R c x)) ⁻¹' S)) := by
  classical
  ext ⟨t,x⟩
  change edge τ L R c t x ∈ ((fun z : C × A => vertex τ L R z.1 z.2) '' S) ↔
    (t = 0 ∧ (c,L c x) ∈ S) ∨ (t = 1 ∧ (τ c,R c x) ∈ S)
  by_cases h0 : t = 0
  · subst t
    rw [edge_zero]
    simp only [true_and,zero_ne_one,false_and,or_false]
    constructor
    · rintro ⟨a,ha,he⟩
      have heq : a = (c,L c x) := Sum.inl.inj he
      exact heq ▸ ha
    · intro h; exact ⟨(c,L c x),h,rfl⟩
  · by_cases h1 : t = 1
    · subst t
      rw [edge_one]
      simp only [one_ne_zero,false_and,true_and,false_or]
      constructor
      · rintro ⟨a,ha,he⟩
        have heq : a = (τ c,R c x) := Sum.inl.inj he
        exact heq ▸ ha
      · intro h; exact ⟨(τ c,R c x),h,rfl⟩
    · have ht : ∃ z : Inner,t = ⟨z.1,z.2.1.le,z.2.2.le⟩ :=
        ⟨⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
          lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩,rfl⟩
      obtain ⟨s,rfl⟩ := ht
      rw [edge_inner]
      simp only [h0,h1,false_and,or_self,iff_false]
      rintro ⟨a,_,he⟩
      change (Sum.inl a : Core (C := C) (A := A) (B := B)) = Sum.inr (c,(s,x)) at he
      cases he

lemma base_closedEmbedding : IsClosedEmbedding (fun z : C × A => vertex τ L R z.1 z.2) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap (continuous_vertex τ L R)
    Sum.inl_injective
  intro S hS
  apply (isClosed_iff τ L R _).mpr
  constructor
  · intro c
    have he : (vertex τ L R c) ⁻¹' ((fun z : C × A => vertex τ L R z.1 z.2) '' S) =
        (fun x => (c,x)) ⁻¹' S := by
      ext x
      change (∃ a ∈ S, (Sum.inl a : Space τ L R) = Sum.inl (c,x)) ↔ (c,x) ∈ S
      simp only [Sum.inl.injEq]
      constructor
      · rintro ⟨a,ha,he⟩; cases he; exact ha
      · intro h; exact ⟨(c,x),h,rfl⟩
    rw [he]
    exact hS.preimage (continuous_const.prodMk continuous_id)
  · intro c
    rw [edge_preimage_vertices]
    exact (isClosed_singleton.prod (hS.preimage (continuous_const.prodMk (L c).continuous))).union
      (isClosed_singleton.prod (hS.preimage (continuous_const.prodMk (R c).continuous)))

omit [TopologicalSpace C] [DiscreteTopology C] in
lemma interior_preimage [DecidableEq C] (c d : C) (s : Inner) (x : B) :
    (fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' {interior τ L R d s x} =
      (if c = d then {((⟨s.1,s.2.1.le,s.2.2.le⟩ : I),x)} else ∅ : Set (I × B)) := by
  classical
  ext ⟨t,y⟩
  change edge τ L R c t y = interior τ L R d s x ↔ _
  have hright : (t,y) ∈ (if c = d then {((⟨s.1,s.2.1.le,s.2.2.le⟩ : I),x)} else ∅ : Set (I × B)) ↔
      c = d ∧ t.1 = s.1 ∧ y = x := by
    split_ifs with h
    · simp only [Set.mem_singleton_iff,Prod.mk.injEq,h,true_and]
      exact and_congr Subtype.ext_iff Iff.rfl
    · simp only [Set.mem_empty_iff_false,h,false_and]
  rw [hright]
  by_cases h0 : t = 0
  · subst t
    rw [edge_zero]
    constructor
    · intro h
      change (Sum.inl (c,L c y) : Core (C := C) (A := A) (B := B)) = Sum.inr (d,(s,x)) at h
      cases h
    · rintro ⟨_,h,_⟩; exact False.elim (s.2.1.ne' h.symm)
  · by_cases h1 : t = 1
    · subst t
      rw [edge_one]
      constructor
      · intro h
        change (Sum.inl (τ c,R c y) : Core (C := C) (A := A) (B := B)) = Sum.inr (d,(s,x)) at h
        cases h
      · rintro ⟨_,h,_⟩; exact False.elim (s.2.2.ne h.symm)
    · have ht : ∃ z : Inner,t = ⟨z.1,z.2.1.le,z.2.2.le⟩ :=
        ⟨⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
          lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩,rfl⟩
      obtain ⟨s',rfl⟩ := ht
      rw [edge_inner]
      constructor
      · intro h
        have he : (c,(s',y)) = (d,(s,x)) := Sum.inr.inj h
        exact ⟨congrArg Prod.fst he,congrArg (fun z => z.2.1.1) he,
          congrArg (fun z => z.2.2) he⟩
      · rintro ⟨rfl,hs,rfl⟩
        have he : s' = s := Subtype.ext hs
        rw [he]
end

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B] [T1Space B]
variable (τ : C → C) (L R : C → C(B,A))

lemma selection_closed {J : Type z} (c : J → C) (hc : Function.Injective c)
    (s : J → Inner) (x : J → B) (S : Set (Space τ L R))
    (hS : S ⊆ Set.range (fun j => interior τ L R (c j) (s j) (x j))) : IsClosed S := by
  classical
  apply (isClosed_iff τ L R S).mpr
  constructor
  · intro d
    have he : (vertex τ L R d) ⁻¹' S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨j,hj⟩ := hS ha
      change (Sum.inr (c j,(s j,x j)) : Core (C := C) (A := A) (B := B)) = Sum.inl (d,a) at hj
      cases hj
    rw [he]; exact isClosed_empty
  · intro d
    have hfinite : ((fun z : I × B => edge τ L R d z.1 z.2) ⁻¹' S).Finite := by
      by_cases hex : ∃ j,c j = d
      · obtain ⟨j,hj⟩ := hex
        apply (Set.finite_singleton (((⟨(s j).1,(s j).2.1.le,(s j).2.2.le⟩ : I),x j))).subset
        intro z hz
        obtain ⟨i,hi⟩ := hS hz
        have hmem : z ∈ (fun z : I × B => edge τ L R d z.1 z.2) ⁻¹'
            {interior τ L R (c i) (s i) (x i)} := hi.symm
        rw [interior_preimage] at hmem
        split_ifs at hmem with hdi
        · have hij : i = j := hc (hdi.symm.trans hj.symm)
          simpa only [hij] using hmem
        · exact False.elim hmem
      · have he : (fun z : I × B => edge τ L R d z.1 z.2) ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          obtain ⟨i,hi⟩ := hS hz
          have hmem : z ∈ (fun z : I × B => edge τ L R d z.1 z.2) ⁻¹'
              {interior τ L R (c i) (s i) (x i)} := hi.symm
          rw [interior_preimage,ite_eq_right (fun h => hex ⟨i,h.symm⟩)] at hmem
          exact hmem
        rw [he]; exact Set.finite_empty
    exact hfinite.isClosed

theorem compact_finitely_many_edges {K : Set (Space τ L R)} (hK : IsCompact K) :
    {c : C | ∃ (s : Inner) (x : B), interior τ L R c s x ∈ K}.Finite := by
  classical
  let J := {c : C | ∃ (s : Inner) (x : B), interior τ L R c s x ∈ K}
  let s : J → Inner := fun j => j.2.choose
  let x : J → B := fun j => j.2.choose_spec.choose
  let y : J → Space τ L R := fun j => interior τ L R j.1 (s j) (x j)
  have hyK (j : J) : y j ∈ K := j.2.choose_spec.choose_spec
  have hinj : Function.Injective y := by
    intro i j hij
    apply Subtype.ext
    have he : (i.1,(s i,x i)) = (j.1,(s j,x j)) := Sum.inr.inj hij
    exact congrArg Prod.fst he
  have hall : ∀ S ⊆ Set.range y, IsClosed S :=
    selection_closed τ L R Subtype.val Subtype.val_injective s x
  have hcompact : IsCompact (Set.range y) :=
    hK.of_isClosed_subset (hall _ subset_rfl) (Set.range_subset_iff.mpr hyK)
  have hdiscrete : IsDiscrete (Set.range y) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hall S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdiscrete
  have : Finite J := (Set.finite_range_iff hinj).mp hrange
  exact Set.toFinite J

end

open Set Topology
open scoped unitInterval
universe u v w
variable {C : Type u} {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

lemma edge_eq_vertex (c d : C) (t : I) (x : B) (y : A) :
    edge τ L R c t x = vertex τ L R d y ↔
    (t = 0 ∧ c = d ∧ L c x = y) ∨ (t = 1 ∧ τ c = d ∧ R c x = y) := by
  by_cases h0 : t = 0
  · subst t
    rw [edge_zero,vertex_eq_vertex]
    simp only [true_and,zero_ne_one,false_and,or_false]
  · by_cases h1 : t = 1
    · subst t
      rw [edge_one,vertex_eq_vertex]
      simp only [true_and,one_ne_zero,false_and,false_or]
    · let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
        lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
      have he : edge τ L R c t x = interior τ L R c s x := edge_inner τ L R c s x
      rw [he]
      simp only [interior_ne_vertex,h0,h1,false_and,or_self]

lemma edgeImage_vertex_slice [DecidableEq C] (c d : C) (S : Set (I × B)) :
    (vertex τ L R d) ⁻¹' ((fun z : I × B => edge τ L R c z.1 z.2) '' S) =
      (if d = c then (L c) '' ((fun x : B => ((0:I),x)) ⁻¹' S) else ∅) ∪
      (if d = τ c then (R c) '' ((fun x : B => ((1:I),x)) ⁻¹' S) else ∅) := by
  classical
  ext y
  change (∃ z ∈ S,edge τ L R c z.1 z.2 = vertex τ L R d y) ↔ _
  constructor
  · rintro ⟨⟨t,x⟩,hx,he⟩
    rcases (edge_eq_vertex τ L R c d t x y).mp he with ⟨rfl,hcd,hx'⟩ | ⟨rfl,hcd,hx'⟩
    · exact Or.inl (by rw [ite_eq_left hcd.symm]; exact ⟨x,hx,hx'⟩)
    · exact Or.inr (by rw [ite_eq_left hcd.symm]; exact ⟨x,hx,hx'⟩)
  · intro h
    rcases h with h|h
    · split_ifs at h with hcd
      · obtain ⟨x,hx,hx'⟩ := h
        exact ⟨(0,x),hx,(edge_eq_vertex τ L R c d 0 x y).mpr (Or.inl ⟨rfl,hcd.symm,hx'⟩)⟩
      · exact False.elim h
    · split_ifs at h with hcd
      · obtain ⟨x,hx,hx'⟩ := h
        exact ⟨(1,x),hx,(edge_eq_vertex τ L R c d 1 x y).mpr (Or.inr ⟨rfl,hcd.symm,hx'⟩)⟩
      · exact False.elim h

lemma edgeImage_vertex_closed (c d : C) (S : Set (I × B)) (hS : IsClosed S)
    (hL : IsClosedMap (L c)) (hR : IsClosedMap (R c)) :
    IsClosed ((vertex τ L R d) ⁻¹' ((fun z : I × B => edge τ L R c z.1 z.2) '' S)) := by
  classical
  rw [edgeImage_vertex_slice]
  apply IsClosed.union
  · split_ifs
    · exact hL _ (hS.preimage (continuous_const.prodMk continuous_id))
    · exact isClosed_empty
  · split_ifs
    · exact hR _ (hS.preimage (continuous_const.prodMk continuous_id))
    · exact isClosed_empty
end UniversalFInfinity.GraphBundle

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.GraphActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w
variable {C : Type u} {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

lemma edgeImage_edge_slice [DecidableEq C] (c d : C) (S : Set (I × B)) :
    (fun z : I × B => edge τ L R d z.1 z.2) ⁻¹'
      ((fun z : I × B => edge τ L R c z.1 z.2) '' S) =
      (if d = c then S else ∅) ∪
      ({0} ×ˢ ((L d) ⁻¹' ((vertex τ L R d) ⁻¹'
        ((fun z : I × B => edge τ L R c z.1 z.2) '' S)))) ∪
      ({1} ×ˢ ((R d) ⁻¹' ((vertex τ L R (τ d)) ⁻¹'
        ((fun z : I × B => edge τ L R c z.1 z.2) '' S)))) := by
  classical
  ext ⟨t,x⟩
  constructor
  · intro hz
    by_cases h0 : t = 0
    · subst t
      change edge τ L R d 0 x ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S) at hz
      exact Or.inl (Or.inr ⟨rfl,by
        change vertex τ L R d (L d x) ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S)
        rw [edge_zero] at hz; exact hz⟩)
    · by_cases h1 : t = 1
      · subst t
        change edge τ L R d 1 x ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S) at hz
        exact Or.inr ⟨rfl,by
          change vertex τ L R (τ d) (R d x) ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S)
          rw [edge_one] at hz; exact hz⟩
      · let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
          lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
        have he : edge τ L R d t x = interior τ L R d s x := edge_inner τ L R d s x
        obtain ⟨z,hz,hze⟩ := hz
        have hm : z ∈ (fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' {interior τ L R d s x} := hze.trans he
        rw [interior_preimage] at hm
        split_ifs at hm with hcd
        · change z = (t,x) at hm
          exact Or.inl (Or.inl (by rw [ite_eq_left hcd.symm]; exact hm ▸ hz))
        · exact False.elim hm
  · rintro ((hz|hz)|hz)
    · split_ifs at hz with hdc
      · subst d; exact ⟨(t,x),hz,rfl⟩
      · exact False.elim hz
    · rcases hz with ⟨h0,hx⟩
      change t = 0 at h0
      subst t
      change edge τ L R d 0 x ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S)
      rw [edge_zero]
      exact hx
    · rcases hz with ⟨h1,hx⟩
      change t = 1 at h1
      subst t
      change edge τ L R d 1 x ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S)
      rw [edge_one]
      exact hx

lemma edge_injective (c : C) (hτ : τ c ≠ c) (hL : Function.Injective (L c))
    (hR : Function.Injective (R c)) : Function.Injective (fun z : I × B => edge τ L R c z.1 z.2) := by
  classical
  rintro ⟨t,x⟩ ⟨s,y⟩ he
  by_cases h0 : t = 0
  · subst t
    have he' : edge τ L R c s y = vertex τ L R c (L c x) := he.symm.trans (edge_zero τ L R c x)
    rcases (edge_eq_vertex τ L R c c s y (L c x)).mp he' with ⟨rfl,_,hy⟩|⟨_,ht,_⟩
    · exact Prod.ext rfl (hL hy).symm
    · exact False.elim (hτ ht)
  · by_cases h1 : t = 1
    · subst t
      have he' : edge τ L R c s y = vertex τ L R (τ c) (R c x) := he.symm.trans (edge_one τ L R c x)
      rcases (edge_eq_vertex τ L R c (τ c) s y (R c x)).mp he' with ⟨_,ht,_⟩|⟨rfl,_,hy⟩
      · exact False.elim (hτ ht.symm)
      · exact Prod.ext rfl (hR hy).symm
    · let r : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
        lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
      have ht : edge τ L R c t x = interior τ L R c r x := edge_inner τ L R c r x
      have hm : (s,y) ∈ (fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' {interior τ L R c r x} := he.symm.trans ht
      rw [interior_preimage,ite_eq_left rfl] at hm
      exact (show (s,y) = (t,x) from hm).symm

variable [TopologicalSpace C] [DiscreteTopology C]
lemma edge_closedMap (c : C) (hL : IsClosedMap (L c)) (hR : IsClosedMap (R c)) :
    IsClosedMap (fun z : I × B => edge τ L R c z.1 z.2) := by
  classical
  intro S hS
  apply (isClosed_iff τ L R _).mpr
  refine ⟨fun d => edgeImage_vertex_closed τ L R c d S hS hL hR,fun d => ?_⟩
  rw [edgeImage_edge_slice]
  apply IsClosed.union
  · apply IsClosed.union
    · split_ifs; exact hS; exact isClosed_empty
    · exact isClosed_singleton.prod ((edgeImage_vertex_closed τ L R c d S hS hL hR).preimage (L d).continuous)
  · exact isClosed_singleton.prod ((edgeImage_vertex_closed τ L R c (τ d) S hS hL hR).preimage (R d).continuous)

lemma edge_closedEmbedding (c : C) (hτ : τ c ≠ c) (hL : IsClosedEmbedding (L c))
    (hR : IsClosedEmbedding (R c)) : IsClosedEmbedding (fun z : I × B => edge τ L R c z.1 z.2) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap (edgeMap τ L R c).continuous
    (edge_injective τ L R c hτ hL.injective hR.injective)
    (edge_closedMap τ L R c hL.isClosedMap hR.isClosedMap)
end

open Set Topology
open scoped unitInterval
universe u v w z
end UniversalFInfinity.GraphBundle

namespace UniversalFInfinity.GraphBundle

open Set Topology
open scoped unitInterval
universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} [TopologicalSpace C] [DiscreteTopology C] [MulAction G C]
variable {A : Type w} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A)) (hτ : ∀ (g : G) c,τ (g • c) = g • τ c)
variable (a : G → C → C(A,A))
variable (ha : ∀ (g : G) c x,a g (τ c) (F c x) = F (g • c) (a g c x))
variable (a_one : ∀ c x,a 1 c x = x)
variable (a_mul : ∀ (g h : G) c x,a (g*h) c x = a g (h • c) (a h c x))

lemma graphAction_continuous : @ContinuousConstSMul G (Space τ (fun _ => .id A) F) _
    (graphAction τ F hτ a ha a_one a_mul).toSMul :=
by
  let := graphAction τ F hτ a ha a_one a_mul
  exact ⟨fun g => (actionMap τ F hτ a ha g).continuous⟩
end UniversalFInfinity.GraphBundle

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.AscendingTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.AscendingTorus

section
open Monoid Coprod Multiplicative
universe u
variable {U : Type u} [Group U]

lemma of_mem_normalForms (f : Monoid.End U) (u : U) : of f u ∈ normalForms f :=
  ⟨0,0,u,by simp⟩

lemma stable_mem_normalForms (f : Monoid.End U) : stable f ∈ normalForms f :=
  ⟨1,0,1,by simp⟩

theorem normal_form (f : Monoid.End U) (x : Torus f) :
    ∃ (p q : ℕ) (u : U), x = stable f ^ p * of f u * (stable f ^ q)⁻¹ := by
  change x ∈ normalForms f
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (relations f) x
  induction w using Coprod.induction_on with
  | inl u => exact of_mem_normalForms f u
  | inr z =>
    have hz : inr z = (letter (U := U)) ^ toAdd z := by
      rw [letter,← map_zpow]
      congr 1
      change z = ofAdd ((toAdd z) • (1 : ℤ))
      simp
    rw [hz,map_zpow]
    exact (normalForms f).zpow_mem (stable_mem_normalForms f) _
  | mul x y hx hy =>
    rw [map_mul]
    exact (normalForms f).mul_mem hx hy

end

section
open Monoid Multiplicative
universe u
variable {U : Type u} [Group U]

lemma coset_mul_of (f : Monoid.End U) (x : Torus f) (u : U) :
    coset f (x * of f u) = coset f x :=
  QuotientGroup.mk_mul_of_mem x ⟨u,rfl⟩

lemma next_iterate_coset (f : Monoid.End U) (k : ℕ) (x : Torus f) :
    (next f)^[k] (coset f x) = coset f (x * stable f ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,next_coset,pow_succ,mul_assoc]

lemma reaches_base_ray (f : Monoid.End U) (c : Coset f) :
    ∃ (p q : ℕ), (next f)^[q] c = (next f)^[p] (coset f 1) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨p,q,u,hx⟩ := normal_form f x
  refine ⟨p,q,?_⟩
  change (next f)^[q] (coset f x) = _
  rw [next_iterate_coset,next_iterate_coset,hx,mul_assoc,
    inv_mul_cancel,mul_one,one_mul,coset_mul_of]

lemma common_descendant (f : Monoid.End U) (c d : Coset f) :
    ∃ (p q : ℕ), (next f)^[p] c = (next f)^[q] d := by
  obtain ⟨p,q,hc⟩ := reaches_base_ray f c
  obtain ⟨r,s,hd⟩ := reaches_base_ray f d
  refine ⟨r+q,p+s,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,hc,hd,
    ← Function.iterate_add_apply,← Function.iterate_add_apply,Nat.add_comm r p]

lemma height_next (f : Monoid.End U) (c : Coset f) :
    cosetHeight f (next f c) = cosetHeight f c + 1 := by
  induction c using QuotientGroup.induction_on with
  | H x =>
    change cosetHeight f (next f (coset f x)) = cosetHeight f (coset f x) + 1
    rw [next_coset,cosetHeight_coset,cosetHeight_coset,map_mul,height_stable]
    rfl

end

open Monoid Multiplicative
end UniversalFInfinity.AscendingTorus

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TorusBundles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Milnor
open Set Topology
universe u v
variable {G : Type u} [Group G] {H : Type v} [Group H]
omit [Group G] [Group H] in
lemma map_leftInverse (φ : G → H) (ψ : H → G) (h : Function.LeftInverse ψ φ) :
    Function.LeftInverse (map ψ id Function.injective_id) (map φ id Function.injective_id) := by
  intro x
  rw [map_comp]
  have he : ψ ∘ φ = id := funext h
  rw [he]
  exact map_id x
omit [Group H] in
lemma map_closedEmbedding (φ : G → H) (hφ : Function.Injective φ) :
    IsClosedEmbedding (map φ id Function.injective_id) := by
  obtain ⟨ψ,hψ⟩ := hφ.hasLeftInverse
  exact (map_leftInverse φ ψ hψ).isClosedEmbedding
    (map ψ id Function.injective_id).continuous (map φ id Function.injective_id).continuous

lemma smulMap_closedEmbedding (g : G) : IsClosedEmbedding (smulMap g) := by
  exact (Homeomorph.smul g).isClosedEmbedding
end UniversalFInfinity.Milnor

namespace UniversalFInfinity.TorusGeometry
open Set Topology AscendingTorus
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

lemma transition_embedding (hf : Function.Injective f) (c : Coset f) :
    IsClosedEmbedding (transition f c) :=
  (Milnor.smulMap_closedEmbedding _).comp (Milnor.map_closedEmbedding f hf)

variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instMulActionTorusSpace
instance action_continuous : ContinuousConstSMul (Torus f) (Space f) :=
  GraphBundle.graphAction_continuous (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) (coordinateAction_one f hf) (coordinateAction_mul f hf)
lemma smul_vertex (g : Torus f) (c : Coset f) (x : Milnor.Space U) :
    g • vertex f c x = vertex f (g • c) (actionOffset f g c • x) := rfl
lemma smul_edge (g : Torus f) (c : Coset f) (t : unitInterval) (x : Milnor.Space U) :
    g • GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) c t x =
      GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) (g • c) t (actionOffset f g c • x) :=
  GraphBundle.actionMap_edge (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) g c t x
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.GraphBundle

open Set Topology
open scoped unitInterval
universe u v w
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B] [T1Space B]
variable (τ : C → C) (L R : C → C(B,A))

theorem compact_coordinates (hτ : ∀ c,τ c ≠ c)
    (hL : ∀ c,IsClosedEmbedding (L c)) (hR : ∀ c,IsClosedEmbedding (R c))
    {K : Set (Space τ L R)} (hK : IsCompact K) :
    ∃ (KA : Set A) (KB : Set B), IsCompact KA ∧ IsCompact KB ∧
      (∀ c x,vertex τ L R c x ∈ K → x ∈ KA) ∧
      (∀ c s x,interior τ L R c s x ∈ K → x ∈ KB) := by
  let KA := Prod.snd '' ((fun z : C × A => vertex τ L R z.1 z.2) ⁻¹' K)
  let J := {c : C | ∃ s x,interior τ L R c s x ∈ K}
  let KB := ⋃ c ∈ J, Prod.snd '' ((fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' K)
  have hJ : J.Finite := compact_finitely_many_edges τ L R hK
  have hA : IsCompact KA :=
    ((base_closedEmbedding τ L R).isProperMap.isCompact_preimage hK).image continuous_snd
  have hB : IsCompact KB := by
    apply hJ.isCompact_biUnion
    intro c _
    exact ((edge_closedEmbedding τ L R c (hτ c) (hL c) (hR c)).isProperMap.isCompact_preimage hK).image continuous_snd
  refine ⟨KA,KB,hA,hB,?_,?_⟩
  · intro c x hx
    exact ⟨(c,x),hx,rfl⟩
  · intro c s x hx
    apply Set.mem_iUnion₂.mpr
    refine ⟨c,⟨s,x,hx⟩,?_⟩
    refine ⟨(⟨s.1,s.2.1.le,s.2.2.le⟩,x),?_,rfl⟩
    change edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ x ∈ K
    rwa [edge_inner]
end UniversalFInfinity.GraphBundle

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor UniversalFInfinity.Simplicial AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instDecidableEqProdNat_solutions
lemma stageFull_vertex (S : Shapes U) (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    stageFull f S (GraphBundle.vertex _ _ _ c x) = vertex f c (Milnor.stageFull U _ x) := rfl
lemma stageFull_interior (S : Shapes U) (c : Coset f) (t : GraphBundle.Inner) (x : Milnor.Stage U S) :
    stageFull f S (GraphBundle.interior _ _ _ c t x) = GraphBundle.interior _ _ _ c t (Milnor.stageFull U _ x) := rfl
lemma stageFull_edge (S : Shapes U) (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    stageFull f S (GraphBundle.edge _ _ _ c t x) = GraphBundle.edge _ _ _ c t (Milnor.stageFull U _ x) :=
  GraphBundle.inclusion_edge _ _ _ _ _ _ _ _ _ c t x

lemma next_ne (c : Coset f) : next f c ≠ c := by
  intro h
  have he := height_next f c
  rw [h] at he
  omega

theorem compact_controlled (hf : Function.Injective f) {K : Set (Space f)} (hK : IsCompact K) :
    ∃ S : Shapes U, K ⊆ Set.range (stageFull f S) := by
  obtain ⟨KA,KB,hA,hB,hVA,hEB⟩ := GraphBundle.compact_coordinates (next f)
    (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f) (next_ne f)
    (fun _ => IsClosedEmbedding.id) (transition_embedding f hf) hK
  obtain ⟨S,hS⟩ := Milnor.compact_controlled U hA
  obtain ⟨T,hT⟩ := Milnor.compact_controlled U hB
  let R := S ∪ T
  refine ⟨R,?_⟩
  intro x hx
  change GraphBundle.Core (C := Coset f) (A := Milnor.Space U) (B := Milnor.Space U) at x
  cases x with
  | inl x =>
    obtain ⟨y,hy⟩ := hS (hVA x.1 x.2 hx)
    let z := stageIncl U S (vertexShapes f R) (Finset.subset_union_left.trans (vertexShapes_left f R)) y
    exact ⟨GraphBundle.vertex _ _ _ x.1 z,congrArg (vertex f x.1) hy⟩
  | inr x =>
    obtain ⟨y,hy⟩ := hT (hEB x.1 x.2.1 x.2.2 hx)
    let z := stageIncl U T R Finset.subset_union_right y
    exact ⟨GraphBundle.interior _ _ _ x.1 x.2.1 z,
      congrArg (GraphBundle.interior _ _ _ x.1 x.2.1) hy⟩
end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)

attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instMulActionTorusSpace_1
lemma stage_range_smul (S : Shapes U) (g : Torus f) {x : Space f}
    (hx : x ∈ Set.range (stageFull f S)) : g • x ∈ Set.range (stageFull f S) := by
  obtain ⟨a,rfl⟩ := hx
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at a
  cases a with
  | inl a =>
    refine ⟨GraphBundle.vertex _ _ _ (g • a.1) (actionOffset f g a.1 • a.2),?_⟩
    change vertex f (g • a.1) (Milnor.stageFull U _ (actionOffset f g a.1 • a.2)) =
      g • vertex f a.1 (Milnor.stageFull U _ a.2)
    rw [smul_vertex,Milnor.stageFull_smul]
  | inr a =>
    refine ⟨GraphBundle.interior _ _ _ (g • a.1) a.2.1 (actionOffset f g a.1 • a.2.2),?_⟩
    change stageFull f S (GraphBundle.interior (next f) (fun _ => left f S) (right f S)
      (g • a.1) a.2.1 (actionOffset f g a.1 • a.2.2)) =
      g • stageFull f S (GraphBundle.interior (next f) (fun _ => left f S) (right f S) a.1 a.2.1 a.2.2)
    rw [stageFull_interior,stageFull_interior,Milnor.stageFull_smul]
    let t : unitInterval := ⟨a.2.1.1,a.2.1.2.1.le,a.2.1.2.2.le⟩
    have h1 : GraphBundle.interior (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)
        a.1 a.2.1 (Milnor.stageFull U _ a.2.2) =
        GraphBundle.edge (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)
        a.1 t (Milnor.stageFull U _ a.2.2) := (GraphBundle.edge_inner _ _ _ _ _ _).symm
    rw [h1,smul_edge,GraphBundle.edge_inner]

lemma compact_orbit_controlled {K : Set (Space f)} (hK : IsCompact K) :
    ∃ S : Shapes U, ∀ g : Torus f, (g • ·) '' K ⊆ Set.range (stageFull f S) := by
  obtain ⟨S,hS⟩ := compact_controlled f hf hK
  refine ⟨S,?_⟩
  intro g x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact stage_range_smul f S g (hS hy)

variable {X : Type v} [TopologicalSpace X] [MulAction (Torus f) X]
lemma equivariant_controlled (hX : Milnor.CompactFundamentalSet (Torus f) (X := X))
    (a : C(X,Space f)) (he : ∀ (g : Torus f) x,a (g • x) = g • a x) :
    ∃ S : Shapes U, Set.range a ⊆ Set.range (stageFull f S) := by
  obtain ⟨K,hK,hcov⟩ := hX
  obtain ⟨S,hS⟩ := compact_orbit_controlled f (hK.image a.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [he]
  exact hS g ⟨a y,⟨y,hy,rfl⟩,rfl⟩

end UniversalFInfinity.TorusGeometry

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A))

lemma shift_vertex (c : C) (x : A) :
    shift τ F (vertex τ (fun _ => .id A) F c x) = vertex τ (fun _ => .id A) F (τ c) (F c x) := rfl
end

open Set Topology
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A))

lemma shiftIterate_vertex (n : ℕ) (c : C) (x : A) :
    shiftIterate τ F n (vertex τ (fun _ => .id A) F c x) =
      vertex τ (fun _ => .id A) F (τ^[n] c) (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change shift τ F (shiftIterate τ F n (vertex τ (fun _ => .id A) F c x)) = _
    rw [ih,shift_vertex,Function.iterate_succ_apply']
    rfl
lemma shiftIterate_edge (n : ℕ) (c : C) (t : I) (x : A) :
    shiftIterate τ F n (edge τ (fun _ => .id A) F c t x) =
      edge τ (fun _ => .id A) F (τ^[n] c) t (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change shift τ F (shiftIterate τ F n (edge τ (fun _ => .id A) F c t x)) = _
    rw [ih,shift_edge,Function.iterate_succ_apply']
    rfl
end UniversalFInfinity.GraphBundle

namespace UniversalFInfinity.DirectedTree
universe u v
variable {C : Type u} {G : Type v} [Group G]
variable (τ : C → C) (h : C → ℤ) (hτ : ∀ c, h (τ c) = h c + 1)

include hτ in
lemma height_iterate (c : C) (n : ℕ) : h (τ^[n] c) = h c + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',hτ,ih]; push_cast; omega

variable (w : C → G)

lemma rayProduct_add (c : C) (n k : ℕ) :
    rayProduct τ w c (n+k) = rayProduct τ w c n * rayProduct τ w (τ^[n] c) k := by
  induction k with
  | zero => simp [rayProduct]
  | succ k ih =>
    rw [Nat.add_succ,rayProduct,ih,rayProduct,mul_assoc]
    congr 2
    rw [Function.iterate_add_apply]
    exact congrArg w ((Function.Commute.iterate_iterate (Function.Commute.refl τ) n k).eq c)

lemma rayProduct_first (c : C) (n : ℕ) :
    rayProduct τ w c (n+1) = w c * rayProduct τ w (τ c) n := by
  simpa only [Nat.add_comm 1 n,rayProduct,Function.iterate_zero,Function.id_def,one_mul,
    Function.iterate_one] using rayProduct_add τ w c 1 n

include h hτ in

lemma route_independent (c d : C) (p q p' q' : ℕ)
    (he : τ^[p] c = τ^[q] d) (he' : τ^[p'] c = τ^[q'] d) :
    rayProduct τ w c p * (rayProduct τ w d q)⁻¹ =
      rayProduct τ w c p' * (rayProduct τ w d q')⁻¹ := by
  have hlen : (p:ℤ) + q' = (p':ℤ) + q := by
    have ha := congrArg h he
    have hb := congrArg h he'
    rw [height_iterate τ h hτ,height_iterate τ h hτ] at ha hb
    omega
  have hlen' : p + q' = p' + q := by omega
  have enlarge (a b : C) (i j k : ℕ) (hab : τ^[i] a = τ^[j] b) :
      rayProduct τ w a i * (rayProduct τ w b j)⁻¹ =
      rayProduct τ w a (i+k) * (rayProduct τ w b (j+k))⁻¹ := by
    rw [rayProduct_add,rayProduct_add,hab,mul_inv_rev]
    group
  rw [enlarge c d p q q' he,enlarge c d p' q' q he',hlen',Nat.add_comm q' q]

variable (hc : ∀ c d, ∃ p q : ℕ, τ^[p] c = τ^[q] d) (root : C)

include h hτ in
lemma potential_route (c : C) (p q : ℕ) (he : τ^[p] root = τ^[q] c) :
    potential τ w hc root c = rayProduct τ w root p * (rayProduct τ w c q)⁻¹ := by
  exact route_independent τ h hτ w root c _ _ p q (hc root c).choose_spec.choose_spec he

include h hτ in

lemma potential_edge (c : C) : potential τ w hc root c * w c = potential τ w hc root (τ c) := by
  obtain ⟨p,q,he⟩ := hc root (τ c)
  have he' : τ^[p] root = τ^[q+1] c := by simpa only [Function.iterate_succ_apply] using he
  rw [potential_route τ h hτ w hc root c p (q+1) he',
    potential_route τ h hτ w hc root (τ c) p q he,rayProduct_first]
  group

end UniversalFInfinity.DirectedTree

namespace UniversalFInfinity.DirectedGraph
open Set Topology Attachment
open scoped unitInterval
universe u
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C] (τ : C → C)
variable (h : C → ℤ) (hτ : ∀ c, h (τ c) = h c + 1)
variable (hc : ∀ c d, ∃ p q : ℕ, τ^[p] c = τ^[q] d) (root : C)

include h hτ in
omit [DiscreteTopology C] in
lemma treeClass_edge (c : C) : (treeClass τ hc root c).trans (edgeClass τ c) =
    treeClass τ hc root (τ c) := by
  have he := DirectedTree.potential_edge τ h hτ (edgeWeight τ hc root) hc root c
  have he' := congrArg MulOpposite.unop he
  simp only [MulOpposite.unop_mul,FundamentalGroup.mul_def,edgeWeight,MulOpposite.unop_op] at he'
  have hh := congrArg (fun (k : FundamentalGroup (Graph τ) (vertex τ root)) =>
    k.trans (initialClass τ hc root (τ c))) he'
  simpa only [treeClass,Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.trans_refl] using hh

include h hτ in
omit [DiscreteTopology C] in
lemma treePath_edge (c : C) : ((treePath τ hc root c).trans (edge τ c)).Homotopic
    (treePath τ hc root (τ c)) := by
  apply Path.Homotopic.Quotient.exact
  change (Path.Homotopic.Quotient.mk (treePath τ hc root c)).trans (edgeClass τ c) = _
  unfold treePath
  rw [(Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root c)).choose_spec,
    (Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root (τ c))).choose_spec]
  exact treeClass_edge τ h hτ hc root c

include hτ hc root in

lemma tree_contractible : ContractibleSpace (Graph τ) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨vertex τ root,⟨graphNullhomotopy τ (.id _) (vertex τ root)
    (treePath τ hc root) ?_⟩⟩
  intro c
  simpa only [ContinuousMap.coe_id,Path.map_id] using treePath_edge τ h hτ hc root c
end UniversalFInfinity.DirectedGraph

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))
variable {Y : Type z} [TopologicalSpace Y]

lemma treeProjection_vertex (c : C) (x : A) :
    treeProjection τ L R (vertex τ L R c x) = DirectedGraph.vertex τ c := rfl
lemma treeProjection_edge (c : C) (t : I) (x : B) :
    treeProjection τ L R (edge τ L R c t x) = DirectedGraph.edge τ c t :=
  lift_edge τ L R _ _ _ _ c (t,x)

lemma treePathMap_vertex (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C) :
    treePathMap τ y p (DirectedGraph.vertex τ c) = y c := rfl
lemma treePathMap_edge (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C) (t : I) :
    treePathMap τ y p (DirectedGraph.edge τ c t) = p c t := by
  change Attachment.lift _ _ _ _ (Attachment.cell _ c (Cayley.edgeParam t)) = _
  rw [Attachment.lift_cell]
  change p c (Cayley.edgeTime (Cayley.edgeParam t)) = p c t
  rw [Cayley.edgeTime_param]

lemma nullhomotopic_of_fiber_constant (h : C → ℤ) (hτ : ∀ c,h (τ c) = h c+1)
    (hc : ∀ c d,∃ m n : ℕ,τ^[m] c = τ^[n] d) (root : C)
    (f : C(Space τ L R,Y)) (y : C → Y) (p : ∀ c,Path (y c) (y (τ c)))
    (hv : ∀ c x,f (vertex τ L R c x) = y c)
    (he : ∀ c t x,f (edge τ L R c t x) = p c t) : f.Nullhomotopic := by
  have := DirectedGraph.tree_contractible τ h hτ hc root
  have hf : f = (treePathMap τ y p).comp (treeProjection τ L R) := by
    apply hom_ext τ L R
    · intro c x
      simpa only [ContinuousMap.comp_apply,treeProjection_vertex,treePathMap_vertex] using hv c x
    · intro c z
      simpa only [ContinuousMap.comp_apply,treeProjection_edge,treePathMap_edge] using he c z.1 z.2
  rw [hf]
  have hn := (id_nullhomotopic (DirectedGraph.Graph τ)).comp_right (treePathMap τ y p)
  exact hn.comp_left (treeProjection τ L R)
end

open Set Topology
open scoped unitInterval
universe u v w z r
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))
variable {Y : Type z} [TopologicalSpace Y] {Z : Type r} [TopologicalSpace Z]
variable (f : C(Space τ L R,Y)) (y : C → Y)
variable (V : ∀ c,(f.comp (vertexMap τ L R c)).Homotopy (.const _ (y c)))
variable (a b : C → C(Z,Y)) (e : ∀ c z,Path (a c z) (b c z))
variable (he : ∀ c,Continuous (fun p : Z × I => e c p.1 p.2))
variable (H : C → C(I × B,Z))
variable (Q : C → C(B,C(I,C(I,Y))))
variable (hleft : ∀ c t x,a c (H c (t,x)) = V c (t,L c x))
variable (qleft : ∀ c x t,Q c x t 0 = b c (H c (t,x)))
variable (qright : ∀ c x t,Q c x t 1 = V (τ c) (t,R c x))

variable (e0 : ∀ c x s,e c (H c (0,x)) s = f (edge τ L R c s x))
variable (q0 : ∀ c x s,Q c x 0 s = f (vertex τ L R (τ c) (R c x)))
variable (p : ∀ c,Path (y c) (y (τ c)))
variable (e1 : ∀ c x s,gluedPath τ L R f y V a b e H Q qleft qright c (1,x) s = p c s)

include he hleft e0 q0 e1 in

theorem nullhomotopic_of_coherent_contraction
    (height : C → ℤ) (hτ : ∀ c,height (τ c) = height c+1)
    (hc : ∀ c d,∃ m n : ℕ,τ^[m] c = τ^[n] d) (root : C) : f.Nullhomotopic := by
  have hn := nullhomotopic_of_fiber_constant τ L R height hτ hc root
    (collapsed τ L R y p) y p (fun _ _ => rfl) (collapsed_edge τ L R y p)
  obtain ⟨z,⟨K⟩⟩ := hn
  refine ⟨z,⟨?_⟩⟩
  have J := coherentHomotopy τ L R f y V a b e he H Q hleft qleft qright e0 q0 p e1
  have P := (ContinuousMap.Homotopy.refl f).comp (pauseHomotopy τ L R)
  exact P.symm.trans (J.trans K)
end UniversalFInfinity.GraphBundle

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.ControlledCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.SphereTopology
open Set Topology
open scoped unitInterval
universe u v w
variable {B : Type u} [TopologicalSpace B] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z] {n : ℕ} [Nonempty (Sphere n)]

lemma parametric_extension (q : C(Y,Z)) (z : Z) (H : q.Homotopy (.const _ z))
    (a : C(B × Sphere n,Y)) :
    ∃ F : C(B × Disk n,Z), ∀ b x,F (b,boundary n x) = q (a (b,x)) := by
  let k : C(B × (I × Sphere n),B × Disk n) :=
    ⟨Prod.map id (cone n),continuous_fst.prodMk ((cone n).continuous.comp continuous_snd)⟩
  have hk : IsProperMap k := isProperMap_id.prodMap (cone n).continuous.isProperMap
  have hsurj : Function.Surjective k := Function.Surjective.prodMap Function.surjective_id (cone_surjective n)
  have hquot : IsQuotientMap k := hk.isClosedMap.isQuotientMap hk.continuous hsurj
  let v : C(B × (I × Sphere n),Z) :=
    ⟨fun p => H.symm (p.2.1,a (p.1,p.2.2)),H.symm.continuous.comp
      (continuous_snd.fst.prodMk (a.continuous.comp (continuous_fst.prodMk continuous_snd.snd)))⟩
  have hv : Function.FactorsThrough v k := by
    intro p r hpr
    have hb : p.1 = r.1 := congrArg (fun x : B × Disk n => x.1) hpr
    have hc : cone n p.2 = cone n r.2 := congrArg (fun x : B × Disk n => x.2) hpr
    have ht : p.2.1 = r.2.1 := Subtype.ext ((cone_norm p.2).symm.trans
      ((congrArg (fun x : Disk n => ‖x.1‖) hc).trans (cone_norm r.2)))
    by_cases hzero : (p.2.1:ℝ) = 0
    · have hp : p.2.1 = 0 := Subtype.ext hzero
      have hr : r.2.1 = 0 := ht.symm.trans hp
      change H.symm (p.2.1,a (p.1,p.2.2)) = H.symm (r.2.1,a (r.1,r.2.2))
      rw [hp,hr,H.symm.apply_zero,H.symm.apply_zero]
      rfl
    · have hs : p.2.2 = r.2.2 := by
        apply Subtype.ext
        have heq := congrArg (fun x : Disk n => x.1) hc
        change (p.2.1:ℝ) • p.2.2.1 = (r.2.1:ℝ) • r.2.2.1 at heq
        rw [←ht] at heq
        exact (smul_right_injective _ hzero) heq
      exact congrArg v (Prod.ext hb (Prod.ext ht hs))
  let F := hquot.lift v hv
  refine ⟨F,?_⟩
  intro b x
  have hh := ContinuousMap.congr_fun (hquot.lift_comp v hv) (b,(1,x))
  have hc : cone n (1,x) = boundary n x := by apply Subtype.ext; simp [cone,boundary]
  change F (b,cone n (1,x)) = H.symm (1,a (b,x)) at hh
  simpa only [hc,H.symm.apply_one,ContinuousMap.comp_apply] using hh
end UniversalFInfinity.SphereTopology

namespace UniversalFInfinity.Cellular

section
open Set Topology
open scoped unitInterval
universe u v
variable {B : Type u} [TopologicalSpace B] {Y : Type v} [TopologicalSpace Y] {n : ℕ}
variable (a : C(B,C(Sphere n,C(I,Y)))) (b : C(B,C(Disk n,Y × Y)))
variable (h : ∀ v x,pathEndpoint (a v x) = b v (boundary n x))

lemma familyFaceMap_eq (i : Option Bool) (p : familyCylinderFace (B := B) (n := n) i) :
    familyFaceMap a b i p = faceMap (a p.1.1) (b p.1.1) i ⟨p.1.2,p.2⟩ := by
  cases i with
  | none => rfl
  | some c => cases c <;> rfl

include h in
lemma familyCylinder_continuous : Continuous (fun p : B × Sphere (n+1) => cylinderBoundaryMap (a p.1) (b p.1) (h p.1) p.2) := by
  let S := familyCylinderFace (B := B) (n := n)
  have hc : ∀ i j p (hi : p ∈ S i) (hj : p ∈ S j), familyFaceMap a b i ⟨p,hi⟩ = familyFaceMap a b j ⟨p,hj⟩ := by
    intro i j p hi hj
    rw [familyFaceMap_eq,familyFaceMap_eq]
    exact faceMap_compat (a p.1) (b p.1) (h p.1) i j p.2 hi hj
  have hcover : ⋃ i,S i = univ := by
    apply Set.eq_univ_of_forall
    intro p
    have hp : p.2 ∈ ⋃ i,cylinderFace n i := by rw [cylinderFace_cover]; exact mem_univ _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  have hclosed : ∀ i,IsClosed (S i) := fun i => (cylinderFace_closed n i).preimage continuous_snd
  have he : Set.liftCover S (fun i => familyFaceMap a b i) hc hcover =
      (fun p : B × Sphere (n+1) => cylinderBoundaryMap (a p.1) (b p.1) (h p.1) p.2) := by
    funext p
    have hp : p ∈ ⋃ i,S i := by rw [hcover]; exact mem_univ _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    rw [Set.liftCover_coe (S := S) (f := fun i => familyFaceMap a b i) (hf := hc) (hS := hcover) ⟨p,hi⟩,
      familyFaceMap_eq]
    exact (cylinderBoundaryMap_face (a p.1) (b p.1) (h p.1) i ⟨p.2,hi⟩).symm
  rw [←he]
  exact continuous_liftCover S _ hc hcover hclosed
end

section
open Set Metric Topology
open scoped unitInterval
universe u v w
variable {B : Type u} [TopologicalSpace B] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]
lemma family_cylinder_filling {n : ℕ} (q : C(Y,Z)) (z : Z) (H : q.Homotopy (.const _ z))
    (a : C(B,C(Sphere n,C(I,Y)))) (b : C(B,C(Disk n,Y × Y)))
    (h : ∀ v x,pathEndpoint (a v x) = b v (boundary n x)) :
    ∃ e : C(B,C(Disk n,C(I,Z))),
      (∀ v x t,e v (boundary n x) t = q (a v x t)) ∧
      ∀ v x,pathEndpoint (e v x) = (q (b v x).1,q (b v x).2) := by
  let : Nonempty (Sphere (n+1)) := SphereTopology.sphere_nonempty n
  let a' : C(B × Sphere (n+1),Y) := ⟨_,familyCylinder_continuous a b h⟩
  obtain ⟨F,hF⟩ := SphereTopology.parametric_extension q z H a'
  change ∀ v x,F (v,boundary (n+1) x) = q (a' (v,x)) at hF
  let e : C(B,C(Disk n,C(I,Z))) :=
    (F.comp ⟨fun p : (B × Disk n) × I => (p.1.1,diskCons p.1.2 p.2),
      continuous_fst.fst.prodMk (continuous_diskCons.comp (continuous_fst.snd.prodMk continuous_snd))⟩).curry.curry
  refine ⟨e,?_,?_⟩
  · intro v x t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]; exact x.2
    change F (v,diskCons (boundary n x) t) = q (a v x t)
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF]
    change q (cylinderBoundaryMap (a v) (b v) (h v) s) = _
    rw [cylinderBoundaryMap_face (a v) (b v) (h v) none ⟨s,hs⟩]
    change q (a v (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t))) = q (a v x t)
    rw [diskTime_cons]; congr 2
  · intro v x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1; norm_num [diskCons]
      change F (v,diskCons x 0) = q (b v x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF]
      change q (cylinderBoundaryMap (a v) (b v) (h v) s) = _
      rw [cylinderBoundaryMap_face (a v) (b v) (h v) (some false) ⟨s,hs⟩]
      change q (b v (diskTail (diskCons x 0))).1 = q (b v x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1; norm_num [diskCons]
      change F (v,diskCons x 1) = q (b v x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF]
      change q (cylinderBoundaryMap (a v) (b v) (h v) s) = _
      rw [cylinderBoundaryMap_face (a v) (b v) (h v) (some true) ⟨s,hs⟩]
      change q (b v (diskTail (diskCons x 1))).2 = q (b v x).2
      rw [diskTail_cons]
end

section
open Set Metric Topology
open scoped unitInterval
universe u v w
variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]
lemma family_square_filling {n : ℕ} (q : C(Y,Z)) (z : Z) (H : q.Homotopy (.const _ z))
    (a : C(X,C(Sphere n,C(I,C(I,Y)))))
    (b c : C(X,C(Disk n,C(I,Y) × C(I,Y))))
    (hs : ∀ v x,pathEndpoint (a v x) = b v (boundary n x))
    (ht : ∀ v x s,pathEndpoint (a v x s) = ((c v (boundary n x)).1 s,(c v (boundary n x)).2 s))
    (h0 : ∀ v x,pathEndpoint ((b v x).1) = ((c v x).1 0,(c v x).2 0))
    (h1 : ∀ v x,pathEndpoint ((b v x).2) = ((c v x).1 1,(c v x).2 1)) :
    ∃ e : C(X,C(Disk n,C(I,C(I,Z)))),
      (∀ v x s t,e v (boundary n x) s t = q (a v x s t)) ∧
      (∀ v x t,e v x 0 t = q ((b v x).1 t)) ∧
      (∀ v x t,e v x 1 t = q ((b v x).2 t)) ∧
      (∀ v x s,e v x s 0 = q ((c v x).1 s)) ∧
      (∀ v x s,e v x s 1 = q ((c v x).2 s)) := by
  let A : C(X,C(Sphere (n+1),C(I,Y))) := ContinuousMap.curry ⟨_,familyCylinder_continuous a b hs⟩
  let B : C(X,C(Disk (n+1),Y × Y)) := ContinuousMap.curry
    ⟨fun p => ((c p.1 (diskTail p.2)).1 (diskTime p.2),(c p.1 (diskTail p.2)).2 (diskTime p.2)),by
      have hc : Continuous (fun p : X × Disk (n+1) => c p.1 (diskTail p.2)) :=
        continuous_eval.comp ((c.continuous.comp continuous_fst).prodMk (continuous_diskTail.comp continuous_snd))
      exact (continuous_eval.comp ((continuous_fst.comp hc).prodMk (continuous_diskTime.comp continuous_snd))).prodMk
        (continuous_eval.comp ((continuous_snd.comp hc).prodMk (continuous_diskTime.comp continuous_snd)))⟩
  have hAB : ∀ v x,pathEndpoint (A v x) = B v (boundary (n+1) x) := by
    intro v x
    rcases sphere_split x with hx|hx|hx
    · have hx' : x ∈ cylinderFace n (some false) := hx
      rw [show A v x = faceMap (a v) (b v) (some false) ⟨x,hx'⟩ from
        cylinderBoundaryMap_face (a v) (b v) (hs v) (some false) ⟨x,hx'⟩]
      change pathEndpoint ((b v (diskTail (boundary (n+1) x))).1) =
        ((c v (diskTail (boundary (n+1) x))).1 (diskTime (boundary (n+1) x)),
        (c v (diskTail (boundary (n+1) x))).2 (diskTime (boundary (n+1) x)))
      rw [faceTime_eq_zero x hx]; exact h0 v _
    · have hx' : x ∈ cylinderFace n (some true) := hx
      rw [show A v x = faceMap (a v) (b v) (some true) ⟨x,hx'⟩ from
        cylinderBoundaryMap_face (a v) (b v) (hs v) (some true) ⟨x,hx'⟩]
      change pathEndpoint ((b v (diskTail (boundary (n+1) x))).2) =
        ((c v (diskTail (boundary (n+1) x))).1 (diskTime (boundary (n+1) x)),
        (c v (diskTail (boundary (n+1) x))).2 (diskTime (boundary (n+1) x)))
      rw [faceTime_eq_one x hx]; exact h1 v _
    · have hx' : x ∈ cylinderFace n none := hx
      rw [show A v x = faceMap (a v) (b v) none ⟨x,hx'⟩ from
        cylinderBoundaryMap_face (a v) (b v) (hs v) none ⟨x,hx'⟩]
      exact ht v (faceSphere ⟨x,hx'⟩) (faceTime none ⟨x,hx'⟩)
  obtain ⟨d,hd,hp⟩ := family_cylinder_filling q z H A B hAB
  let e : C(X,C(Disk n,C(I,C(I,Z)))) :=
    (ContinuousMap.mk (fun p : (X × Disk n) × I => d p.1.1 (diskCons p.1.2 p.2))
      (continuous_eval.comp ((d.continuous.comp continuous_fst.fst).prodMk
        (continuous_diskCons.comp (continuous_fst.snd.prodMk continuous_snd))))).curry.curry
  refine ⟨e,?_,?_,?_,?_,?_⟩
  · intro v x s t
    let z' : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x s⟩
    have hz : z' ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) s)).1 ∈ sphere 0 1
      rw [diskTail_cons]; exact x.2
    change d v (diskCons (boundary n x) s) t = q (a v x s t)
    rw [show diskCons (boundary n x) s = boundary (n+1) z' from rfl,hd]
    rw [show A v z' = faceMap (a v) (b v) none ⟨z',hz⟩ from
      cylinderBoundaryMap_face (a v) (b v) (hs v) none ⟨z',hz⟩]
    change q (a v (faceSphere ⟨z',hz⟩) (diskTime (diskCons (boundary n x) s)) t) = _
    rw [diskTime_cons]; congr 2
  · intro v x t
    let z' : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
    have hz : z' ∈ cylinderFace n (some false) := by
      change (diskCons x 0).1 0 = -1; norm_num [diskCons]
    change d v (diskCons x 0) t = q ((b v x).1 t)
    rw [show diskCons x 0 = boundary (n+1) z' from rfl,hd]
    rw [show A v z' = faceMap (a v) (b v) (some false) ⟨z',hz⟩ from
      cylinderBoundaryMap_face (a v) (b v) (hs v) (some false) ⟨z',hz⟩]
    change q ((b v (diskTail (diskCons x 0))).1 t) = _
    rw [diskTail_cons]
  · intro v x t
    let z' : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
    have hz : z' ∈ cylinderFace n (some true) := by
      change (diskCons x 1).1 0 = 1; norm_num [diskCons]
    change d v (diskCons x 1) t = q ((b v x).2 t)
    rw [show diskCons x 1 = boundary (n+1) z' from rfl,hd]
    rw [show A v z' = faceMap (a v) (b v) (some true) ⟨z',hz⟩ from
      cylinderBoundaryMap_face (a v) (b v) (hs v) (some true) ⟨z',hz⟩]
    change q ((b v (diskTail (diskCons x 1))).2 t) = _
    rw [diskTail_cons]
  · intro v x s
    have h := congrArg Prod.fst (hp v (diskCons x s))
    change d v (diskCons x s) 0 = _
    simpa only [pathEndpoint,ContinuousMap.coe_mk,B,ContinuousMap.curry_apply,
      diskTail_cons,diskTime_cons] using h
  · intro v x s
    have h := congrArg Prod.snd (hp v (diskCons x s))
    change d v (diskCons x s) 1 = _
    simpa only [pathEndpoint,ContinuousMap.coe_mk,B,ContinuousMap.curry_apply,
      diskTail_cons,diskTime_cons] using h

lemma SquareBoundary.fill_after_nullhomotopy (D : SquareBoundary X Y)
    (q : C(Y,Z)) (z : Z) (H : q.Homotopy (.const _ z)) :
    ∃ Q : C(X,C(I,C(I,Z))),
      (∀ x t,Q x 0 t = q ((D.b x).1 t)) ∧
      (∀ x t,Q x 1 t = q ((D.b x).2 t)) ∧
      (∀ x s,Q x s 0 = q ((D.c x).1 s)) ∧
      (∀ x s,Q x s 1 = q ((D.c x).2 s)) := by
  let : IsEmpty (Sphere 0) := ⟨fun x => by
    have hx : x.1 = 0 := Subsingleton.elim _ _
    have h := x.2
    change ‖x.1‖ = 1 at h
    rw [hx,norm_zero] at h
    exact zero_ne_one h⟩
  let a : C(X,C(Sphere 0,C(I,C(I,Y)))) := .const _ ⟨isEmptyElim,continuous_of_discreteTopology⟩
  let b : C(X,C(Disk 0,C(I,Y) × C(I,Y))) := ContinuousMap.curry (D.b.comp .fst)
  let c : C(X,C(Disk 0,C(I,Y) × C(I,Y))) := ContinuousMap.curry (D.c.comp .fst)
  obtain ⟨e,_,h0,h1,h2,h3⟩ := family_square_filling q z H a b c (fun _ x => isEmptyElim x)
    (fun _ x => isEmptyElim x) (fun x _ => D.zero x) (fun x _ => D.one x)
  let x0 : Disk 0 := ⟨0,by simp⟩
  exact ⟨⟨fun x => e x x0,(continuous_eval_const x0).comp e.continuous⟩,
    fun x t => h0 x x0 t,fun x t => h1 x x0 t,fun x s => h2 x x0 s,fun x s => h3 x x0 s⟩
end

open Set Topology
open scoped unitInterval
universe u v w
variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]
variable (a b : C(I × X,Y)) (A B : Y)
variable (h0 : ∀ x,a (0,x) = b (0,x)) (ha : ∀ x,a (1,x) = A) (hb : ∀ x,b (1,x) = B)

include h0 ha hb in

lemma connector_after_nullhomotopy (x0 : X) (q : C(Y,Z)) (z : Z)
    (H : q.Homotopy (.const _ z)) :
    ∃ (P : Path A B) (Q : C(X,C(I,C(I,Z)))),
      (∀ x t,Q x 0 t = q (a (0,x))) ∧
      (∀ x t,Q x 1 t = q (P t)) ∧
      (∀ x s,Q x s 0 = q (a (s,x))) ∧
      (∀ x s,Q x s 1 = q (b (s,x))) := by
  obtain ⟨Q,hQ0,hQ1,hQ2,hQ3⟩ := (connectorSquare a b A B h0 ha hb x0).fill_after_nullhomotopy q z H
  exact ⟨connectorTop a b A B h0 ha hb x0,Q,hQ0,hQ1,hQ2,hQ3⟩
end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TorusHomotopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor AscendingTorus Cellular
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

variable (S T : Shapes U) (n : ℕ)
variable (q : C(Milnor.Stage U (vertexShapes f S),Milnor.Stage U T)) (z : Milnor.Stage U T)
variable (H : q.Homotopy (.const _ z))
variable (hq : ∀ x,Milnor.stageFull U T (q x) =
  Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x))

lemma firstH_one (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    firstH f S T n q z H c (1,x) = forwardOffset f n c • z := by
  change forwardOffset f n c • H (1,x) = _
  rw [H.apply_one]; rfl

include hq in
lemma square_start (c : Coset f) (x : Milnor.Stage U S) :
    squareLeft f S T n q z H c (0,x) = squareRight f S T n q z H c (0,x) := by
  apply (Milnor.stageFull_embedding U _).injective
  change Milnor.stageFull U _ (right f T (idx f n c) (firstH f S T n q z H c (0,left f S x))) =
    Milnor.stageFull U _ (left f T (firstH f S T n q z H (next f c) (0,right f S c x)))
  rw [right_full,left_full_eq,firstH_zero _ _ _ _ _ _ _ hq,firstH_zero _ _ _ _ _ _ _ hq,left_full_eq,right_full]
  exact (GraphBundle.forward_natural _ _ n c _).symm
lemma squareLeft_one (c : Coset f) (x : Milnor.Stage U S) :
    squareLeft f S T n q z H c (1,x) = right f T (idx f n c) (forwardOffset f n c • z) := by
  exact congrArg (right f T (idx f n c)) (firstH_one f S T n q z H c (left f S x))
lemma squareRight_one (c : Coset f) (x : Milnor.Stage U S) :
    squareRight f S T n q z H c (1,x) = left f T (forwardOffset f n (next f c) • z) := by
  exact congrArg (left f T) (firstH_one f S T n q z H (next f c) (right f S c x))

variable (Z : Shapes U) (e : ℕ)
variable (r : C(Milnor.Stage U (vertexShapes f T),Milnor.Stage U Z)) (w : Milnor.Stage U Z)
variable (J : r.Homotopy (.const _ w))
variable (hr : ∀ x,Milnor.stageFull U Z (r x) =
  Milnor.map (iterateHom f e) id Function.injective_id (Milnor.stageFull U _ x))

lemma secondH_one (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    secondH f S T n q z H Z e r c (1,x) =
      forwardOffset f e (idx f n c) • r (left f T (forwardOffset f n c • z)) := by
  change forwardOffset f e (idx f n c) • r (left f T (firstH f S T n q z H c (1,x))) = _
  rw [firstH_one]

include hq J in
lemma twoGhost_square (c : Coset f) :
    ∃ (P : Path (right f T (idx f n c) (forwardOffset f n c • z))
        (left f T (forwardOffset f n (next f c) • z)))
      (Q : C(Milnor.Stage U S,C(I,C(I,Milnor.Stage U Z)))),
      (∀ x t,Q x 0 t = r (squareLeft f S T n q z H c (0,x))) ∧
      (∀ x t,Q x 1 t = r (P t)) ∧
      (∀ x s,Q x s 0 = r (squareLeft f S T n q z H c (s,x))) ∧
      (∀ x s,Q x s 1 = r (squareRight f S T n q z H c (s,x))) := by
  exact connector_after_nullhomotopy (squareLeft f S T n q z H c) (squareRight f S T n q z H c)
    _ _ (square_start f S T n q z H hq c) (squareLeft_one f S T n q z H c)
    (squareRight_one f S T n q z H c) (Milnor.stagePoint U S) r w J

include hr in
lemma final_natural (c : Coset f) (x : Milnor.Stage U T) :
    left f Z (forwardOffset f e (idx f n (next f c)) • r (right f T (idx f n c) x)) =
      right f Z (finalIndex f n e c) (forwardOffset f e (idx f n c) • r (left f T x)) := by
  apply (Milnor.stageFull_embedding U _).injective
  rw [left_full_eq,right_full,Milnor.stageFull_smul,Milnor.stageFull_smul,hr,hr,right_full,left_full_eq]
  rw [←forward_eq,←forward_eq,idx_next]
  exact GraphBundle.forward_natural _ _ e (idx f n c) _

lemma shifted_stage_vertex (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    shifted_stage f S T n q z H Z e r hq hr (GraphBundle.vertex _ _ _ c x) =
      finalLower f n Z e c (secondH f S T n q z H Z e r c (0,x)) := rfl
lemma shifted_stage_edge (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    shifted_stage f S T n q z H Z e r hq hr (GraphBundle.edge _ _ _ c t x) =
      GraphBundle.edge (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c) t
        (secondH f S T n q z H Z e r c (0,left f S x)) :=
  GraphBundle.lift_edge _ _ _ _ _ _ _ c (t,x)

include hq hr J in

theorem shifted_stage_nullhomotopic :
    (shifted_stage f S T n q z H Z e r hq hr).Nullhomotopic := by
  choose P Q hQ0 hQ1 hQL hQR using twoGhost_square f S T n q z H hq Z r w J
  let a := shifted_stage f S T n q z H Z e r hq hr
  let y (c : Coset f) := finalLower f n Z e c (finalPoint f T n z Z e r c)
  let V (c : Coset f) : (a.comp (GraphBundle.vertexMap (next f) (fun _ => left f S) (right f S) c)).Homotopy (.const _ (y c)) :=
    { toFun tx := finalLower f n Z e c (secondH f S T n q z H Z e r c tx)
      continuous_toFun := (finalLower f n Z e c).continuous.comp (secondH f S T n q z H Z e r c).continuous
      map_zero_left x := rfl
      map_one_left x := congrArg (finalLower f n Z e c) (secondH_one f S T n q z H Z e r c x) }
  let E (c : Coset f) (x : Milnor.Stage U Z) : Path (finalLower f n Z e c x) (finalUpper f n Z e c x) :=
    GraphBundle.edgePath (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c) x
  let K (c : Coset f) : C(I × Milnor.Stage U S,Milnor.Stage U Z) :=
    (secondH f S T n q z H Z e r c).comp (.prodMap (.id I) (left f S))
  let D (c : Coset f) : C(Milnor.Stage U S,C(I,C(I,Stage f Z))) :=
    ContinuousMap.curry (ContinuousMap.curry ((finalHigh f n Z e c).comp
      ((stageSmul U Z (forwardOffset f e (idx f n (next f c)))).comp ((Q c).uncurry.uncurry))))
  have he (c : Coset f) : Continuous (fun p : Milnor.Stage U Z × I => E c p.1 p.2) :=
    (GraphBundle.edgeMap (next f) (fun _ => left f Z) (right f Z) _).continuous.comp continuous_swap
  have hdleft (c : Coset f) (x : Milnor.Stage U S) (s : I) :
      D c x s 0 = finalUpper f n Z e c (K c (s,x)) := by
    change finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c x s 0) = _
    rw [hQL]
    exact congrArg (GraphBundle.vertex (next f) (fun _ => left f Z) (right f Z) (next f (finalIndex f n e c)))
      (final_natural f T n Z e r hr c (firstH f S T n q z H c (s,left f S x)))
  have hdright (c : Coset f) (x : Milnor.Stage U S) (s : I) :
      D c x s 1 = V (next f c) (s,right f S c x) := by
    change finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c x s 1) = _
    rw [hQR]
    change GraphBundle.vertex _ _ _ (next f (finalIndex f n e c)) _ =
      GraphBundle.vertex _ _ _ (finalIndex f n e (next f c)) _
    rw [finalIndex_next]
    rfl
  let p (c : Coset f) : Path (y c) (y (next f c)) :=
    (GraphBundle.gluedPath (next f) (fun _ => left f S) (right f S) a y V
      (finalLower f n Z e) (finalUpper f n Z e) E K D hdleft hdright c (1,Milnor.stagePoint U S)).cast
      (congrArg (finalLower f n Z e c) (secondH_one f S T n q z H Z e r c (left f S (Milnor.stagePoint U S))).symm)
      ((V (next f c)).apply_one (right f S c (Milnor.stagePoint U S))).symm
  apply GraphBundle.nullhomotopic_of_coherent_contraction (next f) (fun _ => left f S) (right f S)
    a y V (finalLower f n Z e) (finalUpper f n Z e) E he K D (fun _ _ _ => rfl) hdleft hdright
    (fun c x s => ?_) (fun c x s => ?_) p (fun c x s => ?_)
    (cosetHeight f) (height_next f) (common_descendant f) (QuotientGroup.mk (1 : Torus f))
  · exact (shifted_stage_edge f S T n q z H hq Z e r hr c s x).symm
  · change finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c x 0 s) = _
    rw [hQ0,square_start f S T n q z H hq c x]
    change GraphBundle.vertex _ _ _ (next f (finalIndex f n e c)) _ =
      GraphBundle.vertex _ _ _ (finalIndex f n e (next f c)) _
    rw [finalIndex_next]
    rfl
  · change ((E c (K c (1,x))).trans _ ) s =
      ((E c (K c (1,Milnor.stagePoint U S))).trans _) s
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs
    · change GraphBundle.edge _ _ _ _ _ (secondH f S T n q z H Z e r c (1,left f S x)) =
        GraphBundle.edge _ _ _ _ _ (secondH f S T n q z H Z e r c (1,left f S (Milnor.stagePoint U S)))
      rw [secondH_one,secondH_one]
    · change finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c x 1 _) =
        finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c (Milnor.stagePoint U S) 1 _)
      rw [hQ1,hQ1]
end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
local instance (priority := 2000) instDecidableEqProdNat_solutions_1_r3f1a60_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
variable (S T : Shapes U) (n : ℕ)
variable (q : C(Milnor.Stage U (vertexShapes f S),Milnor.Stage U T)) (z : Milnor.Stage U T)
variable (H : q.Homotopy (.const _ z))
variable (hq : ∀ x,Milnor.stageFull U T (q x) =
  Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x))
variable (Z : Shapes U) (e : ℕ)
variable (r : C(Milnor.Stage U (vertexShapes f T),Milnor.Stage U Z))
variable (hr : ∀ x,Milnor.stageFull U Z (r x) =
  Milnor.map (iterateHom f e) id Function.injective_id (Milnor.stageFull U _ x))
lemma shifted_stage_full :
    (stageFull f Z).comp (shifted_stage f S T n q z H Z e r hq hr) =
      (GraphBundle.shiftIterate (next f) (transition f) e).comp
        ((GraphBundle.shiftIterate (next f) (transition f) n).comp (stageFull f S)) := by
  apply GraphBundle.hom_ext
  · intro c x
    change stageFull f Z (shifted_stage f S T n q z H Z e r hq hr (GraphBundle.vertex _ _ _ c x)) = _
    rw [shifted_stage_vertex]
    change stageFull f Z (GraphBundle.vertex _ _ _ (finalIndex f n e c)
      (left f Z (secondH f S T n q z H Z e r c (0,x)))) = _
    rw [stageFull_vertex,left_full_eq,secondH_full _ _ _ _ _ _ _ _ _ _ hr,
      firstH_zero _ _ _ _ _ _ _ hq]
    change GraphBundle.vertex _ _ _ (finalIndex f n e c) _ =
      GraphBundle.shiftIterate (next f) (transition f) e
        (GraphBundle.shiftIterate (next f) (transition f) n
          (stageFull f S (GraphBundle.vertex _ _ _ c x)))
    rw [stageFull_vertex,vertex,GraphBundle.shiftIterate_vertex,GraphBundle.shiftIterate_vertex]
    rfl
  · intro c tx
    change stageFull f Z (shifted_stage f S T n q z H Z e r hq hr (GraphBundle.edge _ _ _ c tx.1 tx.2)) = _
    rw [shifted_stage_edge,stageFull_edge,secondH_full _ _ _ _ _ _ _ _ _ _ hr,
      firstH_zero _ _ _ _ _ _ _ hq,left_full_eq]
    change GraphBundle.edge _ _ _ (finalIndex f n e c) tx.1 _ =
      GraphBundle.shiftIterate (next f) (transition f) e
        (GraphBundle.shiftIterate (next f) (transition f) n
          (stageFull f S (GraphBundle.edge _ _ _ c tx.1 tx.2)))
    rw [stageFull_edge,GraphBundle.shiftIterate_edge,GraphBundle.shiftIterate_edge]
    rfl
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.PathFamilies
open Set Topology
open scoped unitInterval
variable {Y : Type*} [TopologicalSpace Y] {x y z : Y}
lemma diagonalSquare_mem (p : Path x y) (q : Path y z) (s t : I) {K : Set Y}
    (hp : Set.range p ⊆ K) (hq : Set.range q ⊆ K) : diagonalSquare p q (s,t) ∈ K := by
  apply (Set.union_subset hp hq)
  rw [←Path.trans_range,←Path.extend_range]
  exact Set.mem_range_self (((s:ℝ)+(t:ℝ))/2)
end UniversalFInfinity.PathFamilies

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instDecidableEqProdNat_solutions_2
lemma stageInclusion_full (S T : Shapes U) (h : S ⊆ T) (x : Stage f S) :
    stageFull f T (stageInclusion f S T h x) = stageFull f S x := factorStage_spec f _ _ _ x

lemma edge_mem_stage (S : Shapes U) (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) c t (Milnor.stageFull U S x) ∈
      Set.range (stageFull f S) := ⟨GraphBundle.edge _ _ _ c t x,stageFull_edge f S c t x⟩

lemma shiftHomotopy_controlled (S : Shapes U) (t : I) (x : Stage f S) :
    GraphBundle.shiftHomotopy (next f) (transition f) (t,stageFull f S x) ∈
      Set.range (stageFull f (vertexShapes f S)) := by
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at x
  cases x with
  | inl x => exact edge_mem_stage f _ x.1 t x.2
  | inr x =>
    change PathFamilies.diagonalSquare (GraphBundle.edgePath (next f) (fun _ => ContinuousMap.id _) (transition f) x.1 (Milnor.stageFull U S x.2.2))
      (GraphBundle.edgePath (next f) (fun _ => ContinuousMap.id _) (transition f) (next f x.1)
        (transition f x.1 (Milnor.stageFull U S x.2.2)))
      (t,⟨x.2.1.1,x.2.1.2.1.le,x.2.1.2.2.le⟩) ∈ _
    apply PathFamilies.diagonalSquare_mem
    · rintro y ⟨s,rfl⟩
      exact stage_range_mono f (vertexShapes_left f S) (edge_mem_stage f S x.1 s x.2.2)
    · rintro y ⟨s,rfl⟩
      exact edge_mem_stage f _ (next f x.1) s (right f S x.1 x.2.2)

lemma shiftIterateHomotopy_controlled (S : Shapes U) (n : ℕ) :
    ∃ T : Shapes U, ∀ (t : I) (x : Stage f S),
      GraphBundle.shiftIterateHomotopy (next f) (transition f) n (t,stageFull f S x) ∈
        Set.range (stageFull f T) := by
  induction n with
  | zero => exact ⟨S,fun _ x => ⟨x,rfl⟩⟩
  | succ n ih =>
    obtain ⟨T,hT⟩ := ih
    refine ⟨vertexShapes f T,?_⟩
    intro t x
    change ((GraphBundle.shiftIterateHomotopy (next f) (transition f) n).trans
      ((GraphBundle.shiftHomotopy (next f) (transition f)).compContinuousMap
        (GraphBundle.shiftIterate (next f) (transition f) n))) (t,stageFull f S x) ∈ _
    refine (congrArg (· ∈ Set.range (stageFull f (vertexShapes f T)))
      (ContinuousMap.Homotopy.trans_apply
        (GraphBundle.shiftIterateHomotopy (next f) (transition f) n)
        ((GraphBundle.shiftHomotopy (next f) (transition f)).compContinuousMap
          (GraphBundle.shiftIterate (next f) (transition f) n))
        (t,stageFull f S x))).mpr ?_
    split_ifs
    · exact stage_range_mono f (vertexShapes_left f T) (hT _ x)
    · have hx := hT 1 x
      rw [ContinuousMap.Homotopy.apply_one] at hx
      obtain ⟨y,hy⟩ := hx
      change GraphBundle.shiftHomotopy (next f) (transition f) (_,GraphBundle.shiftIterate (next f) (transition f) n (stageFull f S x)) ∈ _
      rw [←hy]
      exact shiftHomotopy_controlled f T _ y

end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instDecidableEqProdNat_solutions_3
lemma doubleShiftHomotopy_controlled (S : Shapes U) (n e : ℕ) :
    ∃ R : Shapes U, ∀ (t : I) (x : Stage f S),
      ((GraphBundle.shiftIterateHomotopy (next f) (transition f) n).trans
        ((GraphBundle.shiftIterateHomotopy (next f) (transition f) e).compContinuousMap
          (GraphBundle.shiftIterate (next f) (transition f) n))) (t,stageFull f S x) ∈
        Set.range (stageFull f R) := by
  obtain ⟨A,hA⟩ := shiftIterateHomotopy_controlled f S n
  obtain ⟨B,hB⟩ := shiftIterateHomotopy_controlled f A e
  refine ⟨A ∪ B,?_⟩
  intro t x
  refine (congrArg (· ∈ Set.range (stageFull f (A ∪ B)))
    (ContinuousMap.Homotopy.trans_apply
      (GraphBundle.shiftIterateHomotopy (next f) (transition f) n)
      ((GraphBundle.shiftIterateHomotopy (next f) (transition f) e).compContinuousMap
        (GraphBundle.shiftIterate (next f) (transition f) n))
      (t,stageFull f S x))).mpr ?_
  split_ifs
  · exact stage_range_mono f Finset.subset_union_left (hA _ x)
  · have hx := hA 1 x
    rw [ContinuousMap.Homotopy.apply_one] at hx
    obtain ⟨y,hy⟩ := hx
    change GraphBundle.shiftIterateHomotopy (next f) (transition f) e
      (_,GraphBundle.shiftIterate (next f) (transition f) n (stageFull f S x)) ∈ _
    rw [←hy]
    exact stage_range_mono f Finset.subset_union_right (hB _ y)

theorem uniform_stage_nullhomotopy
    (hghost : ∀ S : Shapes U, ∃ (n : ℕ) (T : Shapes U)
      (q : C(Milnor.Stage U S,Milnor.Stage U T)) (z : Milnor.Stage U T),
      (∀ x,Milnor.stageFull U T (q x) =
        Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U S x)) ∧
      Nonempty (q.Homotopy (.const _ z))) (S : Shapes U) :
    ∃ (R : Shapes U) (hSR : S ⊆ R), (stageInclusion f S R hSR).Nullhomotopic := by
  obtain ⟨n,T,q,z,hq,⟨H⟩⟩ := hghost (vertexShapes f S)
  obtain ⟨e,Z,r,w,hr,⟨J⟩⟩ := hghost (vertexShapes f T)
  obtain ⟨B,hB⟩ := doubleShiftHomotopy_controlled f S n e
  let R := S ∪ Z ∪ B
  have hSR : S ⊆ R := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hZR : Z ⊆ R := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hBR : B ⊆ R := Finset.subset_union_right
  let a := stageInclusion f S R hSR
  let b := (stageInclusion f Z R hZR).comp (shifted_stage f S T n q z H Z e r hq hr)
  let K := ((GraphBundle.shiftIterateHomotopy (next f) (transition f) n).trans
    ((GraphBundle.shiftIterateHomotopy (next f) (transition f) e).compContinuousMap
      (GraphBundle.shiftIterate (next f) (transition f) n))).compContinuousMap (stageFull f S)
  have ha : (stageFull f S) = (stageFull f R).comp a := by
    apply ContinuousMap.ext; intro x
    exact (stageInclusion_full f S R hSR x).symm
  have hb : (GraphBundle.shiftIterate (next f) (transition f) e).comp
      ((GraphBundle.shiftIterate (next f) (transition f) n).comp (stageFull f S)) =
      (stageFull f R).comp b := by
    rw [←shifted_stage_full f S T n q z H hq Z e r hr]
    apply ContinuousMap.ext; intro x
    exact (stageInclusion_full f Z R hZR _).symm
  let K' : ((stageFull f R).comp a).Homotopy ((stageFull f R).comp b) := K.cast ha hb
  have hc (t : I) (x : Stage f S) : K' (t,x) ∈ Set.range (stageFull f R) :=
    stage_range_mono f hBR (hB t x)
  let L := homotopyFactor f R a b K' hc
  have hn := shifted_stage_nullhomotopic f S T n q z H hq Z e r w J hr
  obtain ⟨v,⟨M⟩⟩ := hn
  refine ⟨R,hSR,stageInclusion f Z R hZR v,⟨?_⟩⟩
  exact L.trans ((ContinuousMap.Homotopy.refl (stageInclusion f Z R hZR)).comp M)
end UniversalFInfinity.TorusGeometry

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TorusSpheres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Milnor
open Set Topology UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v w
variable {G : Type u} {H : Type v}

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_16
lemma map_natural (φ φ' : G → H) (δ : G → G) (θ : H → H)
    (h : ∀ x,φ' (δ x) = θ (φ x)) (α : ℕ → ℕ) (hα : Function.Injective α) (x : Space G) :
    map φ' α hα (map δ id Function.injective_id x) =
      map θ id Function.injective_id (map φ α hα x) := by
  rw [map_comp,map_comp]
  exact congrArg (fun φ => map φ α hα x) (funext h)

lemma mixedHomotopy_natural (φ ψ φ' ψ' : G → H) (δ : G → G) (θ : H → H)
    (hφ : ∀ x,φ' (δ x) = θ (φ x)) (hψ : ∀ x,ψ' (δ x) = θ (ψ x)) (t : I) (x : Space G) :
    mixedHomotopy φ' ψ' (t,map δ id Function.injective_id x) =
      map θ id Function.injective_id (mixedHomotopy φ ψ (t,x)) := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (map φ' evenLayer evenLayer_injective (map δ id Function.injective_id x)).1 +
    (t:ℝ) • (map ψ' oddLayer oddLayer_injective (map δ id Function.injective_id x)).1 =
      ((1-(t:ℝ)) • (map φ evenLayer evenLayer_injective x).1 +
        (t:ℝ) • (map ψ oddLayer oddLayer_injective x).1).mapDomain (fun v => (v.1,θ v.2))
  rw [map_natural _ _ _ _ hφ,map_natural _ _ _ _ hψ,Finsupp.mapDomain_add,
    Finsupp.mapDomain_smul,Finsupp.mapDomain_smul]
  rfl

lemma bridge_natural (φ ψ φ' ψ' : G → H) (δ : G → G) (θ : H → H)
    (hφ : ∀ x,φ' (δ x) = θ (φ x)) (hψ : ∀ x,ψ' (δ x) = θ (ψ x)) (t : I) (x : Space G) :
    bridge φ' ψ' (t,map δ id Function.injective_id x) =
      map θ id Function.injective_id (bridge φ ψ (t,x)) := by
  simp only [bridge,ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact mixedHomotopy_natural φ φ φ' φ' δ θ hφ hφ _ x
  · exact mixedHomotopy_natural ψ φ ψ' φ' δ θ hψ hφ _ x
end UniversalFInfinity.Milnor

namespace UniversalFInfinity.TorusGeometry
open Set Topology AscendingTorus
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

lemma toMilnor_edge (c : Coset f) (t : I) (x : Milnor.Space U) :
    toMilnor f (GraphBundle.edge _ _ _ c t x) = edgeToMilnor f c (t,x) :=
  GraphBundle.lift_edge _ _ _ _ _ _ _ c (t,x)

lemma lowerLabel_action (g : Torus f) (c : Coset f) (u : U) :
    lowerLabel f (g • c) (actionOffset f g c * u) = g * lowerLabel f c u := by
  unfold lowerLabel
  rw [map_mul,←mul_assoc,origin_action,mul_assoc]
lemma upperLabel_action (hf : Function.Injective f) (g : Torus f) (c : Coset f) (u : U) :
    upperLabel f (g • c) (actionOffset f g c * u) = g * upperLabel f c u := by
  unfold upperLabel
  rw [map_mul,←mul_assoc,←actionOffset_next f hf,mul_assoc,next_smul]
  exact lowerLabel_action f g (next f c) (cosetOffset f c * f u)

variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instMulActionTorusSpace_2
lemma toMilnor_equivariant (g : Torus f) (x : Space f) :
    toMilnor f (g • x) = g • toMilnor f x := by
  change GraphBundle.Core (C := Coset f) (A := Milnor.Space U) (B := Milnor.Space U) at x
  cases x with
  | inl x =>
    change vertexToMilnor f (g • x.1) (actionOffset f g x.1 • x.2) = g • vertexToMilnor f x.1 x.2
    exact Milnor.map_natural (lowerLabel f x.1) (lowerLabel f (g • x.1))
      (actionOffset f g x.1 * ·) (g * ·) (lowerLabel_action f g x.1) _ _ x.2
  | inr x =>
    let t : I := ⟨x.2.1.1,x.2.1.2.1.le,x.2.1.2.2.le⟩
    have hx : (Sum.inr x : Space f) = GraphBundle.edge (next f) (fun _ => ContinuousMap.id _)
        (transition f) x.1 t x.2.2 := (GraphBundle.edge_inner _ _ _ _ _ _).symm
    rw [hx,smul_edge,toMilnor_edge,toMilnor_edge]
    exact Milnor.bridge_natural (lowerLabel f x.1) (upperLabel f x.1)
      (lowerLabel f (g • x.1)) (upperLabel f (g • x.1)) (actionOffset f g x.1 * ·) (g * ·)
      (lowerLabel_action f g x.1) (upperLabel_action f hf g x.1) _ x.2.2
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.GraphBundle
open Set Topology Cellular
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A)) (z : A)
variable (H : (ContinuousMap.id A).Homotopy (.const _ z))

omit [TopologicalSpace C] [DiscreteTopology C] in
lemma contractionSquare_filling (c : C) :
    ∃ Q : C(A,C(I,C(I,A))),
      (∀ x t,Q x 0 t = F c x) ∧
      (∀ x t,Q x 1 t = H (t,F c z)) ∧
      (∀ x s,Q x s 0 = F c (H (s,x))) ∧
      (∀ x s,Q x s 1 = H (s,F c x)) :=
  (contractionSquare F z H c).fill_after_nullhomotopy (.id A) z H

include z H in

theorem homogeneous_contractible
    (height : C → ℤ) (hτ : ∀ c,height (τ c) = height c+1)
    (hc : ∀ c d,∃ m n : ℕ,τ^[m] c = τ^[n] d) (root : C) :
    ContractibleSpace (Space τ (fun _ => ContinuousMap.id A) F) := by
  choose Q hQ0 hQ1 hQL hQR using contractionSquare_filling F z H
  let L : C → C(A,A) := fun _ => .id A
  let W := Space τ L F
  let y : C → W := fun c => vertex τ L F c z
  let V (c : C) : ((ContinuousMap.id W).comp (vertexMap τ L F c)).Homotopy (.const _ (y c)) :=
    (ContinuousMap.Homotopy.refl (vertexMap τ L F c)).comp H
  let b (c : C) : C(A,W) := (vertexMap τ L F (τ c)).comp (F c)
  let E (c : C) (x : A) : Path (vertex τ L F c x) (b c x) := edgePath τ L F c x
  let J (c : C) : C(A,C(I,C(I,W))) := ContinuousMap.curry (ContinuousMap.curry
    ((vertexMap τ L F (τ c)).comp ((Q c).uncurry.uncurry)))
  let P (c : C) : Path (b c z) (y (τ c)) :=
    { toFun t := vertex τ L F (τ c) (H (t,F c z))
      continuous_toFun := (vertexMap τ L F (τ c)).continuous.comp
        (H.continuous.comp (continuous_id.prodMk continuous_const))
      source' := congrArg (vertex τ L F (τ c)) (H.apply_zero (F c z))
      target' := congrArg (vertex τ L F (τ c)) (H.apply_one (F c z)) }
  let p (c : C) : Path (y c) (y (τ c)) := (E c z).trans (P c)
  have he (c : C) : Continuous (fun a : A × I => E c a.1 a.2) :=
    (edgeMap τ L F c).continuous.comp continuous_swap
  have hleft (c : C) (t : I) (x : A) : vertexMap τ L F c (H (t,x)) = V c (t,L c x) := rfl
  have hleftQ (c : C) (x : A) (t : I) : J c x t 0 = b c (H (t,x)) :=
    congrArg (vertex τ L F (τ c)) (hQL c x t)
  have hrightQ (c : C) (x : A) (t : I) : J c x t 1 = V (τ c) (t,F c x) :=
    congrArg (vertex τ L F (τ c)) (hQR c x t)
  apply (contractible_iff_id_nullhomotopic _).mpr
  apply nullhomotopic_of_coherent_contraction τ L F (.id W) y V (vertexMap τ L F) b E he
    (fun _ => H.toContinuousMap) J hleft hleftQ hrightQ
    (fun c x s => ?_) (fun c x s => ?_) p (fun c x s => ?_) height hτ hc root
  · change edge τ L F c s (H (0,x)) = edge τ L F c s x
    rw [H.apply_zero]; rfl
  · exact congrArg (vertex τ L F (τ c)) (hQ0 c x s)
  · change ((E c (H (1,x))).trans (connectorPath τ L F (.id W) y V b
        (fun _ => H.toContinuousMap) J hleftQ hrightQ c (1,x))) s = ((E c z).trans (P c)) s
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs
    · change edge τ L F c _ (H (1,x)) = edge τ L F c _ z
      rw [H.apply_one]; rfl
    · exact congrArg (vertex τ L F (τ c)) (hQ1 c x _)
end UniversalFInfinity.GraphBundle

namespace UniversalFInfinity.TorusGeometry
open Set Topology Milnor AscendingTorus
variable {U : Type*} [Group U] (f : Monoid.End U)

lemma contractible : ContractibleSpace (Space f) := by
  have h := (contractible_iff_id_nullhomotopic (Milnor.Space U)).mp (Milnor.contractible (G := U))
  obtain ⟨z,⟨H⟩⟩ := h
  exact GraphBundle.homogeneous_contractible (next f) (transition f) z H
    (cosetHeight f) (height_next f) (common_descendant f) (coset f 1)
end UniversalFInfinity.TorusGeometry
namespace UniversalFInfinity.Milnor
open Set Metric Topology Cellular
universe u
variable (G : Type u) [Group G]

local instance (priority := 2000) instDecidableEqProdNat_solutions_17_r3f1a60_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
lemma stageCell_dimension_bound (S : Shapes G) (n : ℕ) (i : StageCell G S n) :
    n < (basedShapes G S).sup Finset.card := by
  obtain ⟨g,s,hs,his⟩ := i.1.2.2
  have hcard := Finset.card_le_card his
  rw [translate_card,i.2] at hcard
  have hd := Finset.le_sup (f := Finset.card) hs
  omega

lemma stageEquivariant_bounded (S : Shapes G) :
    let : CWComplex (univ : Set (Stage G S)) := stageEquivariantCW G S
    ∃ d : ℕ, Skeleton (univ : Set (Stage G S)) d = univ := by
  let : CWComplex (univ : Set (Stage G S)) := stageEquivariantCW G S
  refine ⟨(basedShapes G S).sup Finset.card,Set.eq_univ_of_forall (fun x => ?_)⟩
  have hx : x ∈ (univ : Set (Stage G S)) := mem_univ _
  rw [←CWComplex.iUnion_openCell_eq_complex (C := (univ : Set (Stage G S)))] at hx
  simp only [mem_iUnion] at hx
  obtain ⟨n,i,hi⟩ := hx
  have hn := stageCell_dimension_bound G S n (cellCoordinates G S n i)
  exact CWComplex.skeletonLT_mono (C := (univ : Set (Stage G S)))
    (m := (n : ℕ∞)+1) (n := (((basedShapes G S).sup Finset.card : ℕ) : ℕ∞))
    (by exact_mod_cast Nat.succ_le_of_lt hn)
    (CWComplex.closedCell_subset_skeletonLT n i (CWComplex.openCell_subset_closedCell n i hi))

lemma stage_compactFundamentalSet (S : Shapes G) : CompactFundamentalSet G (X := Stage G S) := by
  let : CWComplex (univ : Set (Stage G S)) := stageEquivariantCW G S
  let σ : ∀ n, (G × CellOrbits G S n) ≃ RelCWComplex.cell (univ : Set (Stage G S)) n :=
    fun _ => Equiv.refl _
  have hσ : ∀ n (g h : G) (i : CellOrbits G S n) (x : Fin n → ℝ),
    RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x := by
    intro n g h i x
    exact mul_smul g h _
  obtain ⟨d,hd⟩ := stageEquivariant_bounded G S
  obtain ⟨K,hK,hcov⟩ := skeleton_compact_representatives σ hσ d
  refine ⟨Subtype.val '' K,hK.image continuous_subtype_val,?_⟩
  intro x
  have hx : x ∈ Skeleton (univ : Set (Stage G S)) d := by rw [hd]; trivial
  obtain ⟨g,y,hy,he⟩ := hcov ⟨x,hx⟩
  refine ⟨g,y.1,⟨y,hy,rfl⟩,?_⟩
  exact congrArg Subtype.val he
end UniversalFInfinity.Milnor
namespace UniversalFInfinity.TorusGeometry
open Set Topology AscendingTorus
open scoped unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)

attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instMulActionTorusSpace_3
lemma exists_moveOffset (c d : Coset f) (u : U) :
    ∃ g : Torus f, g • c = d ∧ actionOffset f g c = u := by
  let g := origin f d * of f u * (origin f c)⁻¹
  have hg : g * origin f c = origin f d * of f u := by simp [g,mul_assoc]
  have hgc : g • c = d := by
    rw [←coset_origin f c,smul_coset,hg,←coset_origin f d]
    apply QuotientGroup.eq.mpr
    refine ⟨u⁻¹,?_⟩
    simp [map_inv,mul_assoc]
  refine ⟨g,hgc,?_⟩
  apply of_injective f hf
  apply mul_left_cancel (a := origin f d)
  have h := origin_action f g c
  rw [hgc,hg] at h
  exact h

lemma stage_compact_representatives (S : Milnor.Shapes U) :
    ∃ K : Set (Space f), IsCompact K ∧
      ∀ x : Stage f S, ∃ g : Torus f, ∃ y ∈ K, stageFull f S x = g • y := by
  obtain ⟨A,hA,hAcov⟩ := Milnor.stage_compactFundamentalSet U (vertexShapes f S)
  obtain ⟨B,hB,hBcov⟩ := Milnor.stage_compactFundamentalSet U S
  let c := coset f 1
  let v : C(Milnor.Stage U (vertexShapes f S),Space f) :=
    (GraphBundle.vertexMap _ _ _ c).comp (Milnor.stageFull U (vertexShapes f S))
  let e : C(I × Milnor.Stage U S,Space f) :=
    (GraphBundle.edgeMap _ _ _ c).comp
      (ContinuousMap.prodMap (.id I) (Milnor.stageFull U S))
  let K := v '' A ∪ e '' (univ ×ˢ B)
  have hK : IsCompact K := (hA.image v.continuous).union ((isCompact_univ.prod hB).image e.continuous)
  refine ⟨K,hK,?_⟩
  intro x
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at x
  cases x with
  | inl x =>
    obtain ⟨u,y,hy,he⟩ := hAcov x.2
    obtain ⟨g,hg,ho⟩ := exists_moveOffset f c x.1 u
    refine ⟨g,v y,Or.inl ⟨y,hy,rfl⟩,?_⟩
    change vertex f x.1 (Milnor.stageFull U _ x.2) = g • vertex f c (Milnor.stageFull U _ y)
    rw [smul_vertex,hg,ho,he,Milnor.stageFull_smul]
  | inr x =>
    obtain ⟨u,y,hy,he⟩ := hBcov x.2.2
    obtain ⟨g,hg,ho⟩ := exists_moveOffset f c x.1 u
    let t : I := ⟨x.2.1.1,x.2.1.2.1.le,x.2.1.2.2.le⟩
    refine ⟨g,e (t,y),Or.inr ⟨(t,y),⟨mem_univ _,hy⟩,rfl⟩,?_⟩
    change stageFull f S (GraphBundle.interior _ _ _ x.1 x.2.1 x.2.2) = _
    rw [stageFull_interior]
    change GraphBundle.interior _ _ _ x.1 x.2.1 (Milnor.stageFull U _ x.2.2) =
      g • GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) c t (Milnor.stageFull U S y)
    rw [smul_edge,hg,ho,GraphBundle.edge_inner,he,Milnor.stageFull_smul]

lemma toMilnor_controlled (S : Milnor.Shapes U) :
    ∃ T : Milnor.Shapes (Torus f), Set.range ((toMilnor f).comp (stageFull f S)) ⊆
      Set.range (Milnor.stageFull (Torus f) T) := by
  obtain ⟨K,hK,hcov⟩ := stage_compact_representatives f S
  obtain ⟨T,hT⟩ := Milnor.compact_orbit_controlled (Torus f) (hK.image (toMilnor f).continuous)
  refine ⟨T,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,he⟩ := hcov x
  change toMilnor f (stageFull f S x) ∈ _
  rw [he,toMilnor_equivariant]
  exact hT g ⟨toMilnor f y,⟨y,hy,rfl⟩,rfl⟩
end UniversalFInfinity.TorusGeometry
namespace UniversalFInfinity.SphereTopology
open Set Topology Cellular
lemma sphereFillable_of_contractible {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y] :
    SphereFillable Y := by
  obtain ⟨z,⟨H⟩⟩ := id_nullhomotopic Y
  intro n a
  cases n with
  | zero => exact fill_zero a
  | succ n =>
    let := sphere_nonempty n
    obtain ⟨e,he⟩ := extends_of_nullhomotopic (H.compContinuousMap a).symm
    exact ⟨e,fun x => ContinuousMap.congr_fun he x⟩
end UniversalFInfinity.SphereTopology

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology AscendingTorus Cellular
open scoped unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
variable [hfi : Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)

attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instMulActionTorusSpace_4
attribute [local instance] OAI.UniversalFInfinity.TorusGeometry.instDecidableEqProdNat_solutions_4
omit hfi in

theorem milnor_uniform_nullhomotopy [Fact (Function.Injective f)]
    (hgraph : ∀ S : Milnor.Shapes U, ∃ (R : Milnor.Shapes U) (hSR : S ⊆ R),
      (stageInclusion f S R hSR).Nullhomotopic)
    (S : Milnor.Shapes (Torus f)) :
    ∃ (R : Milnor.Shapes (Torus f)) (hSR : S ⊆ R),
      (Milnor.stageIncl (Torus f) S R hSR).Nullhomotopic := by
  let G := Torus f
  let : CWComplex (univ : Set (Milnor.Stage G S)) := Milnor.stageEquivariantCW G S
  let κ : ∀ n, (G × Milnor.CellOrbits G S n) ≃ RelCWComplex.cell (univ : Set (Milnor.Stage G S)) n :=
    fun _ => Equiv.refl _
  have hκ : ∀ n (g h : G) (i : Milnor.CellOrbits G S n) (x : Fin n → ℝ),
    RelCWComplex.map n (κ n (g*h,i)) x = g • RelCWComplex.map n (κ n (h,i)) x := by
    intro n g h i x
    exact mul_smul g h _
  obtain ⟨d,hd⟩ := Milnor.stageEquivariant_bounded G S
  let back : C(Milnor.Stage G S,Skeleton (univ : Set (Milnor.Stage G S)) d) :=
    ⟨fun x => ⟨x,by rw [hd]; trivial⟩,continuous_id.subtype_mk (fun x => by rw [hd]; trivial)⟩
  have hback (g : G) (x : Milnor.Stage G S) :
      back (g • x) = skeletonTranslate κ hκ d g (back x) := rfl
  let : ContractibleSpace (Space f) := contractible f
  have hfill := SphereTopology.sphereFillable_of_contractible (Y := Space f)
  obtain ⟨e,he⟩ := exists_equivariant_map_on_skeleton κ hκ d (fun n _ => hfill n)
  let e' := e.comp back
  have he' (g : G) x : e' (g • x) = g • e' x := by
    change e (back (g • x)) = g • e (back x)
    rw [hback,he]
  obtain ⟨A,hA⟩ := equivariant_controlled f (Milnor.stage_compactFundamentalSet G S) e' he'
  let q := factorStage f e' A hA
  obtain ⟨B,hAB,z,⟨J⟩⟩ := hgraph A
  obtain ⟨T,hT⟩ := toMilnor_controlled f B
  let tmap := Milnor.factorStage G ((toMilnor f).comp (stageFull f B)) T hT
  let a := (Milnor.stageFull G S).comp (skeletonInclusion (C := (univ : Set (Milnor.Stage G S))) d)
  let b := (toMilnor f).comp e
  have ha (g : G) x : a (skeletonTranslate κ hκ d g x) = g • a x := Milnor.stageFull_smul G S g x.1
  have hb (g : G) x : b (skeletonTranslate κ hκ d g x) = g • b x := by
    change toMilnor f (e (skeletonTranslate κ hκ d g x)) = g • toMilnor f (e x)
    rw [he,toMilnor_equivariant]
  obtain ⟨H,hH⟩ := exists_equivariant_homotopy_on_skeleton κ hκ d (Milnor.sphereFillable (1:G)) a b ha hb
  obtain ⟨Q,hQ⟩ := Milnor.controlled_skeleton_homotopy κ hκ d a b H hH
  let R := S ∪ T ∪ Q
  have hSR : S ⊆ R := Finset.subset_union_left.trans Finset.subset_union_left
  have hTR : T ⊆ R := Finset.subset_union_right.trans Finset.subset_union_left
  have hQR : Q ⊆ R := Finset.subset_union_right
  let out := (Milnor.stageIncl G T R hTR).comp tmap
  let inc := Milnor.stageIncl G S R hSR
  let target := out.comp ((stageInclusion f A B hAB).comp q)
  let H' := H.compContinuousMap back
  have hHR : Set.range H'.toContinuousMap ⊆ Set.range (Milnor.stageFull G R) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := hQ (Set.mem_range_self (x.1,back x.2))
    exact ⟨Milnor.stageIncl G Q R hQR y,hy⟩
  let HTmap := Milnor.factorStage G H'.toContinuousMap R hHR
  have hout (y : Stage f B) : Milnor.stageFull G R (out y) = toMilnor f (stageFull f B y) := by
    change Milnor.stageFull G T (tmap y) = _
    exact Milnor.factorStage_spec G _ T hT y
  let HT : inc.Homotopy target :=
    { toContinuousMap := HTmap
      map_zero_left := fun x => by
        apply (Milnor.stageFull_embedding G R).injective
        change Milnor.stageFull G R (HTmap (0,x)) = Milnor.stageFull G R (inc x)
        rw [Milnor.factorStage_spec]
        change H' (0,x) = _
        rw [H'.apply_zero]
        rfl
      map_one_left := fun x => by
        apply (Milnor.stageFull_embedding G R).injective
        change Milnor.stageFull G R (HTmap (1,x)) = Milnor.stageFull G R (out (stageInclusion f A B hAB (q x)))
        rw [Milnor.factorStage_spec]
        change H' (1,x) = _
        rw [H'.apply_one,hout,stageInclusion_full,factorStage_spec]
        rfl }
  refine ⟨R,hSR,out z,⟨?_⟩⟩
  exact HT.trans ((ContinuousMap.Homotopy.refl out).comp (J.compContinuousMap q))
end

open Set Topology AscendingTorus ConcreteEnvelopes
variable {U : Type} [Group U] [Group.IsFinitelyPresented U]
  [TopologicalSpace U] [DiscreteTopology U]
variable (k : Index → U →* U) (hk : IsDiagram k)

local instance (priority := 2000) instDecidableEqProdNat_solutions_5_r3f1a60_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
include hk in
lemma diagram_graph_uniform_nullhomotopy (S : Milnor.Shapes U) :
    let f : Monoid.End U := k (.inl P₂.identity)
    ∃ (R : Milnor.Shapes U) (hSR : S ⊆ R),
      (stageInclusion f S R hSR).Nullhomotopic := by
  apply uniform_stage_nullhomotopy
  intro A
  obtain ⟨n,T,q,z,hq,H⟩ := Milnor.diagram_uniform_stage_nullhomotopy k hk A
  refine ⟨n,T,q,z,?_,H⟩
  intro x
  apply Subtype.ext
  exact hq x

include hk in

theorem diagram_milnor_uniform_nullhomotopy
    [Fact (Function.Injective (k (.inl P₂.identity)))]
    (S : Milnor.Shapes (Torus (k (.inl P₂.identity)))) :
    ∃ (R : Milnor.Shapes (Torus (k (.inl P₂.identity)))) (hSR : S ⊆ R),
      (Milnor.stageIncl (Torus (k (.inl P₂.identity))) S R hSR).Nullhomotopic :=
  @milnor_uniform_nullhomotopy U _ (k (.inl P₂.identity))
    ⟨(Fact.out : Function.Injective (k (.inl P₂.identity)))⟩
    (diagram_graph_uniform_nullhomotopy k hk) S
end UniversalFInfinity.TorusGeometry

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct
open Set Metric Topology

namespace UniversalFInfinity
noncomputable section
universe u

theorem universal_group_of_type_FInfinity_oai :
    ∃ (H : Type u) (groupH : Group H),
      @HasTypeFInfinity H groupH ∧
      ∀ (G : Type u) [Group G] [Group.IsFinitelyPresented G],
        ∃ φ : G →* H, Function.Injective φ := by
  obtain ⟨U,gU,fpU,i,hi⟩ := Higman.NormalWords.embeds_presentation
    RecursiveUniversalThree.enumerator RecursiveUniversalThree.enumerator_primrec.to_comp
  let : Group U := gU
  let : Group.IsFinitelyPresented U := fpU
  have hU : ConcreteEnvelopes.IsUniversal U := by
    intro V _ _
    obtain ⟨j,hj⟩ := RecursiveUniversalThree.universal (G := V)
    exact ⟨i.comp j,hi.comp hj⟩
  obtain ⟨k,hk,hk_inj⟩ := ConcreteEnvelopes.self_maps U hU
  let : Fact (Function.Injective (k (.inl ConcreteEnvelopes.P₂.identity))) := ⟨hk_inj⟩
  let : TopologicalSpace U := ⊥
  let : DiscreteTopology U := ⟨rfl⟩
  let f := k (.inl ConcreteEnvelopes.P₂.identity)
  let H₀ := AscendingTorus.Torus f
  let : TopologicalSpace H₀ := ⊥
  let : DiscreteTopology H₀ := ⟨rfl⟩
  refine ⟨ULift.{u} H₀,inferInstance,?_,?_⟩
  · exact Brown.geometric_lifted_of_uniform
      (TorusGeometry.diagram_milnor_uniform_nullhomotopy k hk)
  · intro G _ _
    obtain ⟨j,hj⟩ := RecursiveUniversalThree.universal (G := G)
    refine ⟨MulEquiv.ulift.symm.toMonoidHom.comp ((AscendingTorus.of f).comp (i.comp j)),?_⟩
    exact MulEquiv.ulift.symm.injective.comp ((AscendingTorus.of_injective f hk_inj).comp
      (hi.comp hj))
end
end UniversalFInfinity

end OAI
end

theorem solution.{u} : type_of% @OAI.UniversalFInfinity.universal_group_of_type_FInfinity_oai.{u} := @OAI.UniversalFInfinity.universal_group_of_type_FInfinity_oai.{u}

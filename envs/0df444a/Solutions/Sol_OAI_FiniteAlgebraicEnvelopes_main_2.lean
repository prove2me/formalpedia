-- Prove2me | solution 2 for OAI.FiniteAlgebraicEnvelopes.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T20:05:56.91955+00:00
-- url     : https://prove2.me/submissions/fe0150e7-5498-43c5-870b-41dfe93ba97a

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_OAIFAE004
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_TwistedBrinThompson_finitelyPresented
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_envelope

section
-- module Solutions.OAIFAE.CantorBricks
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.Prefix.instCountable _root_.OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.Table.correctionIndex_finite _root_.OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.Table.familyIndex_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Cantor prefixes, bricks, charts, finite-table group, localization, and displacement.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

theorem embedding_injective [FaithfulSMul Γ X] :
    Function.Injective (embedding (Γ:=Γ) (X:=X)) := by
  intro g h he
  exact twist_injective (congrArg Subtype.val he)

lemma bitFlip_table (x : X) : Nonempty (Table (Γ:=Γ) (bitFlip x)) := by
  classical
  refine ⟨⟨Bool,inferInstance,Prefix.oneBit x,fun b => Prefix.oneBit x (!b),
    fun _ => 1,?_,?_,?_⟩⟩
  · intro z
    refine ⟨z x 0,(Prefix.mem_oneBit x _ z).mpr rfl,?_⟩
    intro b hb
    exact ((Prefix.mem_oneBit x b z).mp hb).symm
  · intro z
    refine ⟨!(z x 0),(Prefix.mem_oneBit x _ z).mpr (by simp),?_⟩
    intro b hb
    have he := (Prefix.mem_oneBit x (!b) z).mp hb
    simpa using congrArg Bool.not he.symm
  · intro b z
    funext y n
    by_cases hy : y=x
    · subst y
      cases n <;> simp [Prefix.attach,Stream'.cons]
    · simp [Prefix.attach,hy]

lemma bitFlip_ne_one (x : X) : bitFlip x ≠ 1 := by
  classical
  intro he
  have h := congrFun (congrFun (Equiv.congr_fun he (fun _ _ => false)) x) 0
  change (if x=x ∧ (0 : ℕ)=0 then !false else false)=false at h
  simp at h

instance group_nontrivial [Nonempty X] : Nontrivial (group (Γ:=Γ) (X:=X)) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let f : group (Γ:=Γ) (X:=X) := ⟨bitFlip x,Subgroup.subset_closure (bitFlip_table x)⟩
  refine ⟨⟨f,1,?_⟩⟩
  intro he
  exact bitFlip_ne_one x (congrArg Subtype.val he)

end

universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type u}

lemma box_mem (z : Cube X) (s : Finset X) (n : ℕ) : ∃ w,(box z s n).attach w=z := by
  apply (mem_range_iff _ _).mpr
  intro x
  by_cases hx : x∈s <;> simp [hx]

lemma agree_before {p : Prefix X} {z w : Cube X}
    (hz : ∃ a,p.attach a=z) (hw : ∃ a,p.attach a=w)
    (x : X) (n : ℕ) (hn : n<(p.word x).length) : z x n=w x n := by
  have he := ((mem_range_iff p z).mp hz x).trans ((mem_range_iff p w).mp hw x).symm
  have he' := congrArg (fun (l : List Bool) => l[n]?) he
  rw [Stream'.getElem?_take hn,Stream'.getElem?_take hn] at he'
  exact Option.some.inj he'

end Prefix

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

namespace Table
variable {f : Equiv.Perm (Cube X)}

lemma image_refinement (A : Table (Γ:=Γ) f) (i : A.index) (r : Prefix X) :
    f '' Set.range ((A.source i).comp r).attach =
      Set.range ((A.target i).comp (twistPrefix (A.label i) r)).attach := by
  ext z
  constructor
  · rintro ⟨w,⟨v,rfl⟩,rfl⟩
    exact ⟨twist (A.label i) v,(A.refined_chart i r v).symm⟩
  · rintro ⟨w,rfl⟩
    refine ⟨((A.source i).comp r).attach (twist (A.label i)⁻¹ w),⟨_,rfl⟩,?_⟩
    rw [A.refined_chart,twist_twist_inv]

/-- Every nonidentity table displaces a nonempty dyadic brick. -/
theorem exists_displaced_brick (A : Table (Γ:=Γ) f) (hf : f≠1) :
    ∃ p : Prefix X, Disjoint (Set.range p.attach) (f '' Set.range p.attach) := by
  have hpoint : ∃ z : Cube X, f z≠z := by
    by_contra hn
    apply hf
    apply Equiv.ext
    intro z
    exact not_not.mp (fun hz => hn ⟨z,hz⟩)
  obtain ⟨z,hz⟩ := hpoint
  have hcoord : ∃ x n, f z x n≠z x n := by
    by_contra hn
    apply hz
    funext x n
    exact not_not.mp (fun he => hn ⟨x,n,he⟩)
  obtain ⟨x,n,hneq⟩ := hcoord
  obtain ⟨i,⟨v,hv⟩,_⟩ := A.source_cover z
  let r := Prefix.box v {x,(A.label i)⁻¹ • x} (n+1)
  let p := (A.source i).comp r
  let q := (A.target i).comp (twistPrefix (A.label i) r)
  have hzmem : ∃ w,p.attach w=z := by
    obtain ⟨w,hw⟩ := Prefix.box_mem v {x,(A.label i)⁻¹ • x} (n+1)
    exact ⟨w,by dsimp only [p]; rw [Prefix.comp_attach,hw,hv]⟩
  have hfzmem : ∃ w,q.attach w=f z := by
    obtain ⟨w,hw⟩ := hzmem
    exact ⟨twist (A.label i) w,by rw [← A.refined_chart i r w,hw]⟩
  have hpLength : n<(p.word x).length := by
    simp only [p,Prefix.comp_word,List.length_append,r,Prefix.box_word,
      Finset.mem_insert_self,ite_true,Stream'.length_take]
    omega
  have hqLength : n<(q.word x).length := by
    simp only [q,Prefix.comp_word,List.length_append,twistPrefix_word,r,Prefix.box_word,
      Finset.mem_insert,Finset.mem_singleton,or_true,ite_true,Stream'.length_take]
    omega
  refine ⟨p,Set.disjoint_left.mpr ?_⟩
  intro w hw hw'
  have hqr : w∈Set.range q.attach := by
    rw [← A.image_refinement i r]
    exact hw'
  exact hneq ((Prefix.agree_before hfzmem hqr x n hqLength).trans
    (Prefix.agree_before hzmem hw x n hpLength).symm)

end Table

theorem exists_displaced_brick {f : group (Γ:=Γ) (X:=X)} (hf : f≠1) :
    ∃ p : Prefix X, Disjoint (Set.range p.attach) (f.val '' Set.range p.attach) := by
  obtain ⟨A⟩ := (mem_group_iff_table f.val).mp f.property
  exact A.exists_displaced_brick (fun h => hf (Subtype.ext h))

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.DisplacementCommutator
universe u v
variable {G : Type u} [Group G] {Y : Type v}

variable (ρ : G →* Equiv.Perm Y)

lemma supported_inv {s : Set Y} {g : G} (hg : Supported ρ s g) : Supported ρ s g⁻¹ := by
  intro x hx
  rw [map_inv]
  exact (ρ g).injective (by simpa using (hg x hx).symm)

lemma supported_conjugate {s : Set Y} {g : G} (hg : Supported ρ s g) (n : G) :
    Supported ρ (ρ n '' s) (n*g*n⁻¹) := by
  intro x hx
  have hn : (ρ n).symm x∉s := by
    intro hs
    exact hx ⟨(ρ n).symm x,hs,(ρ n).apply_symm_apply x⟩
  simp only [map_mul,map_inv,Equiv.Perm.mul_apply]
  change ρ n (ρ g ((ρ n).symm x))=x
  rw [hg _ hn,Equiv.apply_symm_apply]

lemma commute_of_disjoint_support (hρ : Function.Injective ρ)
    {s t : Set Y} {a b : G} (ha : Supported ρ s a) (hb : Supported ρ t b)
    (hst : Disjoint s t) : Commute a b := by
  apply hρ
  simp only [map_mul]
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases hx : x∈s
  · exact Or.inr (hb x (fun ht => Set.disjoint_left.mp hst hx ht))
  · exact Or.inl (ha x hx)

lemma commutator_factor {a b c : G} (hc : Commute c b) :
    (a*c)*b*(a*c)⁻¹*b⁻¹ = a*b*a⁻¹*b⁻¹ := by
  calc
    (a*c)*b*(a*c)⁻¹*b⁻¹ = a*(c*b*c⁻¹)*a⁻¹*b⁻¹ := by group
    _ = a*b*a⁻¹*b⁻¹ := by rw [hc.eq]; simp

/-- Double-commutator localization. All commutators supported in a displaced
set lie in the normal subgroup containing the displacing element. -/
theorem local_commutator_mem (hρ : Function.Injective ρ)
    (N : Subgroup G) [N.Normal] {n a b : G} (hn : n∈N) {s : Set Y}
    (hdis : Disjoint s (ρ n '' s)) (ha : Supported ρ s a) (hb : Supported ρ s b) :
    a*b*a⁻¹*b⁻¹∈N := by
  let c := n*a⁻¹*n⁻¹
  have hc : Commute c b := commute_of_disjoint_support ρ hρ
    (supported_conjugate ρ (supported_inv ρ ha) n) hb hdis.symm
  let d := a*n*a⁻¹*n⁻¹
  have hd : d∈N := N.mul_mem ((inferInstance : N.Normal).conj_mem n hn a) (N.inv_mem hn)
  have he : d*b*d⁻¹*b⁻¹∈N := by
    have hm := N.mul_mem hd
      ((inferInstance : N.Normal).conj_mem d⁻¹ (N.inv_mem hd) b)
    simpa only [mul_assoc] using hm
  have hd' : d=a*c := by dsimp [d,c]; group
  rw [hd',commutator_factor hc] at he
  exact he

end FiniteAlgebraicEnvelopes.DisplacementCommutator

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma localize_supported (p : Prefix X) (f : group (Γ:=Γ) (X:=X)) :
    DisplacementCommutator.Supported (group (Γ:=Γ) (X:=X)).subtype
      (Set.range p.attach) (localize p f) := by
  intro z hz
  exact localizePerm_outside p f.val hz

/-- A nontrivial normal subgroup contains all commutators of a whole localized
copy of the group. No simplicity assumption is used. -/
theorem normal_contains_local_commutators (N : Subgroup (group (Γ:=Γ) (X:=X))) [N.Normal]
    (hN : N≠⊥) : ∃ p : Prefix X, ∀ a b : group (Γ:=Γ) (X:=X),
      localize p (a*b*a⁻¹*b⁻¹)∈N := by
  have hx : ∃ n∈N,n≠1 := by
    by_contra hh
    apply hN
    apply le_antisymm _ bot_le
    intro n hn
    rw [Subgroup.mem_bot]
    by_contra hne
    exact hh ⟨n,hn,hne⟩
  obtain ⟨n,hn,hne⟩ := hx
  obtain ⟨p,hp⟩ := exists_displaced_brick hne
  refine ⟨p,fun a b => ?_⟩
  simp only [map_mul,map_inv]
  exact DisplacementCommutator.local_commutator_mem _ Subtype.val_injective N hn hp
    (localize_supported p a) (localize_supported p b)

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.WordProblem
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.bigAlgebra_countable _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.columnSpace_countable _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.hFG _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.hMonoidWithZero _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.kFG _root_.OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.kMonoidWithZero _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Effective finite presentations, decidable word problem in simple groups, and the reverse implication.
-/

namespace FiniteAlgebraicEnvelopes

universe u

namespace WordProblem

open Primrec

theorem reduceStep_primrec (n : ℕ) : Primrec (@reduceStep n) := by
  unfold reduceStep
  refine Primrec.list_casesOn (h := fun (p q : (Fin n × Bool) × Word n) =>
    if p.1.1 = q.1.1 ∧ p.1.2 = !q.1.2 then q.2 else p.1 :: q.1 :: q.2)
    Primrec.snd (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) ?_
  unfold Primrec₂
  apply Primrec.ite
  · apply PrimrecPred.and
    · exact Primrec.eq.comp (Primrec.fst.comp <| Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp <| Primrec.fst.comp Primrec.snd)
    · exact Primrec.eq.comp (Primrec.snd.comp <| Primrec.fst.comp Primrec.fst)
        (Primrec.not.comp <| Primrec.snd.comp <| Primrec.fst.comp Primrec.snd)
  · exact Primrec.snd.comp Primrec.snd
  · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem reduce_primrec (n : ℕ) : Primrec (@FreeGroup.reduce (Fin n) _) := by
  have h := Primrec.list_rec (h := fun (_ : Word n) p => reduceStep (p.1, p.2.2))
    Primrec.id (Primrec.const [])
    ((reduceStep_primrec n).comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)))
  exact h

theorem mk_factorWord {n m} (r : Fin m → Word n) (c : Factor n m) :
    FreeGroup.mk (factorWord r c) = factorValue r c := by
  simp only [factorWord, factorValue, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  cases c.2.2 <;> rfl

theorem mk_certificateWord {n m} (r : Fin m → Word n) (cs : Certificate n m) :
    FreeGroup.mk (certificateWord r cs) = certificateValue r cs := by
  induction cs with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons c cs ih =>
    simpa only [certificateWord, certificateValue, List.map_cons, List.flatten_cons,
      List.prod_cons, ← FreeGroup.mul_mk, mk_factorWord] using
      congrArg (factorValue r c * ·) ih

theorem factorValue_flip {n m} (r : Fin m → Word n) (c : Factor n m) :
    factorValue r (flipFactor c) = (factorValue r c)⁻¹ := by
  rcases c with ⟨w, i, b⟩
  cases b <;> simp [factorValue, flipFactor]

theorem certificateValue_inv {n m} (r : Fin m → Word n) (cs : Certificate n m) :
    certificateValue r (cs.reverse.map flipFactor) = (certificateValue r cs)⁻¹ := by
  simp only [certificateValue, List.map_map, List.prod_inv_reverse, List.map_reverse,
    Function.comp_def, factorValue_flip]

theorem certificateValue_mem {n m} (r : Fin m → Word n) (cs : Certificate n m) :
    certificateValue r cs ∈ Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (r i)) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  apply (inferInstance : (Subgroup.normalClosure
    (Set.range fun i => FreeGroup.mk (r i))).Normal).conj_mem
  split <;> rename_i hb
  · exact Subgroup.subset_normalClosure ⟨c.2.1, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure ⟨c.2.1, rfl⟩)

theorem mem_normalClosure_iff_certificate {n m} (r : Fin m → Word n)
    (g : FreeGroup (Fin n)) :
    g ∈ Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (r i)) ↔
      ∃ cs : Certificate n m, certificateValue r cs = g := by
  refine ⟨fun hg => ?_, fun ⟨cs, heq⟩ => heq ▸ certificateValue_mem r cs⟩
  apply Subgroup.closure_induction (k := Group.conjugatesOfSet _)
    (p := fun x _ => ∃ cs : Certificate n m, certificateValue r cs = x) ?_ ?_ ?_ ?_ hg
  · intro x hx
    obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
    refine ⟨[(FreeGroup.toWord c, i, true)], ?_⟩
    simp [certificateValue, factorValue, FreeGroup.mk_toWord]
  · exact ⟨[], rfl⟩
  · rintro x y _ _ ⟨cx, rfl⟩ ⟨cy, rfl⟩
    exact ⟨cx ++ cy, by simp [certificateValue]⟩
  · rintro x _ ⟨cx, rfl⟩
    exact ⟨cx.reverse.map flipFactor, certificateValue_inv r cx⟩

theorem factorWord_primrec (n m : ℕ) : Primrec₂ (@factorWord n m) := by
  unfold factorWord Primrec₂
  apply Primrec.list_append.comp
  · apply Primrec.list_append.comp
    · exact Primrec.fst.comp Primrec.snd
    · apply Primrec.ite (Primrec.eq.comp (Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)
        (Primrec.const true))
      · exact Primrec.fin_app.comp Primrec.fst (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd)
      · exact (invRev_primrec n).comp (Primrec.fin_app.comp Primrec.fst
          (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd))
  · exact (invRev_primrec n).comp (Primrec.fst.comp Primrec.snd)

theorem certificateWord_primrec (n m : ℕ) : Primrec₂ (@certificateWord n m) := by
  unfold certificateWord Primrec₂
  apply Primrec.list_flatten.comp
  exact Primrec.list_map Primrec.snd ((factorWord_primrec n m).comp (Primrec.fst.comp Primrec.fst)
    Primrec.snd)

/-- The certificate verifier is primitive recursive, including free reduction. -/
theorem verifies_primrec (n m : ℕ) : PrimrecPred
    (fun p : (Fin m → Word n) × Word n × Certificate n m =>
      certificateValue p.1 p.2.2 = FreeGroup.mk p.2.1) := by
  refine (Primrec.eq.comp
    ((reduce_primrec n).comp ((certificateWord_primrec n m).comp Primrec.fst
      (Primrec.snd.comp Primrec.snd)))
    ((reduce_primrec n).comp (Primrec.fst.comp Primrec.snd))).of_eq ?_
  intro p
  exact ⟨fun h => (mk_certificateWord p.1 p.2.2).symm.trans (FreeGroup.reduce.exact h),
    fun h => FreeGroup.reduce.sound ((mk_certificateWord p.1 p.2.2).trans h)⟩

/-- Unbounded search over encoded certificates gives a genuine semidecision. -/
theorem re_exists {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α × β → Prop} (hp : ComputablePred p) : REPred (fun a => ∃ b, p (a,b)) := by
  obtain ⟨d, hc⟩ := hp
  let _ := d
  let test (a : α) (k : ℕ) : Bool :=
    ((Encodable.decode (α := β) k).map (fun b => decide (p (a,b)))).getD false
  have ht : Computable₂ test :=
    Computable.option_getD
      (Computable.option_map (Computable.decode.comp Computable.snd)
        (hc.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)).to₂)
      (Computable.const false)
  refine (Partrec.dom_re (Partrec.rfind ht.partrec₂)).of_eq ?_
  intro a
  simp only [Nat.rfind_dom]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := β) k with
    | none => simp [test, hd] at hk
    | some b => exact ⟨b, by simpa [test, hd] using hk⟩
  · rintro ⟨b, hb⟩
    exact ⟨Encodable.encode b, by simp [test, Encodable.encodek, hb]⟩

/-- Normal closure of any finite tuple of formal relators is uniformly r.e. -/
theorem normalClosure_re (n m : ℕ) : REPred
    (fun p : (Fin m → Word n) × Word n =>
      FreeGroup.mk p.2 ∈ Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (p.1 i))) := by
  have hp : ComputablePred (fun p : ((Fin m → Word n) × Word n) × Certificate n m =>
      certificateValue p.1.1 p.2 = FreeGroup.mk p.1.2) :=
    ((verifies_primrec n m).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).computablePred
  exact (re_exists hp).of_eq fun p => (mem_normalClosure_iff_certificate p.1 (FreeGroup.mk p.2)).symm

/-- Add one relator, uniformly effectively in that relator. -/
theorem consRelators_primrec {n m} (r : Fin m → Word n) :
    Primrec (fun w : Word n => Fin.cons (α := fun _ : Fin (m+1) => Word n) w r) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.swap
  apply Primrec.fin_curry₁.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Primrec.id
  · exact Primrec.const (r j)

/-- In a simple quotient, adjoining a nontrivial word to the defining relators
kills every element, while adjoining a trivial word changes nothing. -/
theorem nontrivial_iff_normalClosure {H : Type*} [Group H] [IsSimpleGroup H]
    {n m} (φ : FreeGroup (Fin n) →* H) (hφ : Function.Surjective φ)
    (r : Fin m → Word n)
    (hr : Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (r i)) = φ.ker)
    (v : Word n) (hv : φ (FreeGroup.mk v) ≠ 1) (w : Word n) :
    φ (FreeGroup.mk w) ≠ 1 ↔
      FreeGroup.mk v ∈ Subgroup.normalClosure
        (Set.range fun i => FreeGroup.mk (Fin.cons (α := fun _ : Fin (m+1) => Word n) w r i)) := by
  let S := Set.range fun i => FreeGroup.mk (r i)
  have hset : (Set.range fun i => FreeGroup.mk (Fin.cons (α := fun _ : Fin (m+1) => Word n) w r i)) =
      insert (FreeGroup.mk w) S := by
    rw [show (fun i => FreeGroup.mk (Fin.cons (α := fun _ : Fin (m+1) => Word n) w r i)) =
      Fin.cons (α := fun _ : Fin (m+1) => FreeGroup (Fin n)) (FreeGroup.mk w) (fun i => FreeGroup.mk (r i)) by
        funext i; refine Fin.cases rfl (fun _ => rfl) i, Fin.range_cons]
  rw [hset]
  let N := Subgroup.normalClosure (insert (FreeGroup.mk w) S)
  have hker : φ.ker ≤ N := by
    rw [← hr]
    exact Subgroup.normalClosure_mono (Set.subset_insert _ _)
  have hwn : FreeGroup.mk w ∈ N := Subgroup.subset_normalClosure (Set.mem_insert _ _)
  constructor
  · intro hw
    have hn := (inferInstance : N.Normal).map φ hφ
    have htop : N.map φ = ⊤ := by
      rcases hn.eq_bot_or_eq_top with hb | ht
      · have he := (N.map_eq_bot_iff.mp hb) hwn
        exact False.elim (hw he)
      · exact ht
    have : N = ⊤ := by
      rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]
    change FreeGroup.mk v ∈ N
    rw [this]; trivial
  · intro hvn hw
    have hle : N ≤ φ.ker := Subgroup.normalClosure_le_normal (by
      intro x hx
      rcases hx with rfl | hx
      · exact hw
      · rw [← hr]
        exact Subgroup.subset_normalClosure hx)
    exact hv (hle hvn)

/-- Parallel enumeration of the two normal-closure certificates decides equality. -/
theorem simple_presentation_computable {H : Type*} [Group H] [IsSimpleGroup H]
    {n m} (φ : FreeGroup (Fin n) →* H) (hφ : Function.Surjective φ)
    (r : Fin m → Word n)
    (hr : Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (r i)) = φ.ker) :
    ComputablePred (fun w : Word n => φ (FreeGroup.mk w) = 1) := by
  obtain ⟨a, ha⟩ := exists_ne (1 : H)
  obtain ⟨g, rfl⟩ := hφ a
  let v := FreeGroup.toWord g
  have hv : φ (FreeGroup.mk v) ≠ 1 := by simpa only [v, FreeGroup.mk_toWord] using ha
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  constructor
  · have hh := (normalClosure_re n m).comp
      (Computable.pair (Computable.const r) Computable.id)
    exact REPred.of_eq hh fun w => by
      dsimp only [Function.comp_def, id]
      rw [hr]; rfl
  · have hh := (normalClosure_re n (m+1)).comp
      (Computable.pair (consRelators_primrec r).to_comp (Computable.const v))
    exact REPred.of_eq hh fun w =>
      (nontrivial_iff_normalClosure φ hφ r hr v hv w).symm

theorem hom_mk_eval {H : Type*} [Group H] {n} (φ : FreeGroup (Fin n) →* H)
    (w : Word n) : φ (FreeGroup.mk w) = evalWord (fun i => φ (FreeGroup.of i)) w := by
  rw [evalWord_eq_lift]
  exact FreeGroup.lift_unique φ (fun _ => rfl)

/-- The classical converse in Theorem 1.1, for the ambient simple group. -/
theorem finitelyPresentedSimple_wordProblem (H : Type*) [Group H]
    [Group.IsFinitelyPresented H] [IsSimpleGroup H] : HasDecidableWordProblem H := by
  classical
  obtain ⟨n, φ, hφ, S, hS, hker⟩ := Group.IsFinitelyPresented.out (G := H)
  let := hS.fintype
  let m := Fintype.card S
  let e : S ≃ Fin m := Fintype.equivFin S
  let r : Fin m → Word n := fun i => FreeGroup.toWord (e.symm i).val
  have hrel : (Set.range fun i => FreeGroup.mk (r i)) = S := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      simpa only [r, FreeGroup.mk_toWord] using (e.symm i).property
    · intro hg
      refine ⟨e ⟨g, hg⟩, ?_⟩
      simp only [r, Equiv.symm_apply_apply, FreeGroup.mk_toWord]
  refine ⟨n, (fun i => φ (FreeGroup.of i)), ?_, ?_⟩
  · rw [← FreeGroup.range_lift_eq_closure]
    have he : FreeGroup.lift (fun i => φ (FreeGroup.of i)) = φ := by ext i; simp
    rw [he]
    exact MonoidHom.range_eq_top.mpr hφ
  · exact (simple_presentation_computable φ hφ r (hrel.symm ▸ hker)).of_eq
      fun w => by rw [hom_mk_eval]

theorem substitute_primrec {n m} (r : Fin n → Word m) : Primrec (substitute r) := by
  unfold substitute
  apply Primrec.list_flatten.comp
  apply Primrec.list_map Primrec.id
  apply Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true))
  · exact Primrec.fin_app.comp (Primrec.const r) (Primrec.fst.comp Primrec.snd)
  · exact (invRev_primrec m).comp (Primrec.fin_app.comp (Primrec.const r)
      (Primrec.fst.comp Primrec.snd))

theorem evalWord_substitute {H : Type*} [Group H] {n m}
    (s : Fin m → H) (r : Fin n → Word m) (w : Word n) :
    evalWord s (substitute r w) = evalWord (fun i => evalWord s (r i)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change evalWord s ((if a.2 then r a.1 else FreeGroup.invRev (r a.1)) ++ substitute r w) =
      (if a.2 then evalWord s (r a.1) else (evalWord s (r a.1))⁻¹) *
        evalWord (fun i => evalWord s (r i)) w
    rw [evalWord_append, ih]
    congr 1
    cases a with
    | mk i b => cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, evalWord_invRev]

theorem evalWord_map {G H : Type*} [Group G] [Group H] {n} (f : G →* H)
    (s : Fin n → G) (w : Word n) : f (evalWord s w) = evalWord (fun i => f (s i)) w := by
  simp only [evalWord, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro a _
  split <;> simp_all only [map_inv]

/-- Word problem descends along embeddings of finitely generated groups. -/
theorem wordProblem_of_injective {G H : Type*} [Group G] [Group H] [Group.FG G]
    (f : G →* H) (hf : Function.Injective f) (hH : HasDecidableWordProblem H) :
    HasDecidableWordProblem G := by
  classical
  obtain ⟨m, t, ht, hc⟩ := hH
  obtain ⟨S, hSgen, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let := hSfin.fintype
  let n := Fintype.card S
  let e : S ≃ Fin n := Fintype.equivFin S
  let s : Fin n → G := fun i => (e.symm i).val
  have hs : Set.range s = S := by
    ext g
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (e.symm i).property,
      fun hg => ⟨e ⟨g, hg⟩, by simp [s]⟩⟩
  have hsurj := FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr ht
  choose v hv using fun i : Fin n => hsurj (f (s i))
  let r : Fin n → Word m := fun i => FreeGroup.toWord (v i)
  have hr (i) : evalWord t (r i) = f (s i) := by
    rw [evalWord_eq_lift]
    change FreeGroup.lift t (FreeGroup.mk (FreeGroup.toWord (v i))) = _
    rw [FreeGroup.mk_toWord, hv]
  refine ⟨n, s, hs ▸ hSgen, ?_⟩
  have hh : ComputablePred (fun w : Word n => evalWord t (substitute r w) = 1) :=
    ⟨inferInstance, hc.decide.comp (substitute_primrec r).to_comp⟩
  exact hh.of_eq fun w => by
    rw [evalWord_substitute, show (fun i => evalWord t (r i)) = (fun i => f (s i)) from funext hr,
      ← evalWord_map, ← map_one f]
    exact hf.eq_iff

end WordProblem

/-- The complete reverse implication of the main theorem. -/
theorem main_reverse (G : Type u) [Group G] [Group.FG G]
    (hG : EmbedsInFinitelyPresentedSimpleGroup G) : HasDecidableWordProblem G := by
  obtain ⟨H, hH, hfp, hsimple, f, hf⟩ := hG
  let _ := hH
  let _ := hfp
  let _ := hsimple
  exact WordProblem.wordProblem_of_injective f hf (WordProblem.finitelyPresentedSimple_wordProblem H)

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.TwistedSimplicity
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.Table.familyIndex_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Partition refinement, simplicity, faithful group embedding, and countability.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

namespace Partition

lemma exists_other (P : Partition X) (i : P.index) (hi : P.brick i≠Prefix.empty) :
    ∃ j : P.index,j≠i := by
  by_contra hn
  apply hi
  apply Prefix.eq_of_range_eq
  ext z
  constructor
  · intro _; exact ⟨z,Prefix.empty_attach z⟩
  · intro _
    obtain ⟨j,hj,_⟩ := P.cover z
    have hji : j=i := by by_contra hh; exact hn ⟨j,hh⟩
    simpa [hji] using hj

lemma compressIndex_apply (P : Partition X) (i j : P.index) (hji : j≠i) (b : Bool) :
    compressIndex P i j hji b (Sum.inl ⟨i,Ne.symm hji⟩)=Sum.inr b := by
  unfold compressIndex splitShift
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
  change Equiv.swap (Sum.inl (⟨j,hji⟩ : {k : P.index // k≠i})) (Sum.inr b)
    (Sum.inl ⟨Equiv.swap i j i,_⟩)=Sum.inr b
  have he : (⟨Equiv.swap i j i,by simpa using hji⟩ : {k : P.index // k≠i})=⟨j,hji⟩ := by
    apply Subtype.ext
    simp
  rw [he,Equiv.swap_apply_left]

end Partition

/-- Every proper brick can be compressed into either dyadic half by an element
of the actual finite-table group. -/
theorem exists_compressor (p : Prefix X) (hp : p≠Prefix.empty) (x : X) (b : Bool) :
    ∃ h : group (Γ:=Γ) (X:=X), ∀ z,
      h.val (p.attach z)=(p.comp (Prefix.oneBit x b)).attach z := by
  obtain ⟨P,i,hi⟩ := p.hasPartition
  obtain ⟨j,hji⟩ := P.exists_other i (by rwa [hi])
  let Q := P.refinement (Partition.bit x) j
  let R := P.refinement (Partition.bit x) i
  let e := P.compressIndex i j hji b
  refine ⟨Q.changeChart R e,fun z => ?_⟩
  have he := Q.changeChart_apply (Γ:=Γ) R e (Sum.inl ⟨i,Ne.symm hji⟩) z
  change (Q.changeChart R e).val ((P.brick i).attach z)=
    (R.brick (e (Sum.inl ⟨i,Ne.symm hji⟩))).attach z at he
  rw [Partition.compressIndex_apply] at he
  change (Q.changeChart R e).val ((P.brick i).attach z)=
    ((P.brick i).comp (Prefix.oneBit x b)).attach z at he
  simpa [hi] using he

/-- Uniform conjugacy of a proper local copy with either half-copy. -/
theorem exists_localize_half_conjugacy (p : Prefix X) (hp : p≠Prefix.empty)
    (x : X) (b : Bool) : ∃ h : group (Γ:=Γ) (X:=X), ∀ f,
      h * localize p f * h⁻¹=localize (p.comp (Prefix.oneBit x b)) f := by
  obtain ⟨h,hh⟩ := exists_compressor (Γ:=Γ) p hp x b
  exact ⟨h,fun f => localize_conj h hh f⟩

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma Prefix.oneBit_ne_empty (x : X) (b : Bool) : Prefix.oneBit x b≠Prefix.empty := by
  intro he
  have hh := congrArg (fun p : Prefix X => p.word x) he
  simp [Prefix.empty] at hh

namespace Table
variable {f : Equiv.Perm (Cube X)}

/-- A coordinate unused by the finite prefix data exists in the infinite cube. -/
lemma exists_fresh [Infinite X] (A : Table (Γ:=Γ) f) :
    ∃ x : X, ∀ i,(A.source i).word x=[] ∧ (A.target i).word x=[] := by
  let := A.finite
  have hs := Set.finite_iUnion (fun i => (A.source i).finite_support.union (A.target i).finite_support)
  obtain ⟨x,hx⟩ := hs.exists_notMem
  refine ⟨x,fun i => ?_⟩
  have hi : x∉{x | (A.source i).word x≠[]} ∪ {x | (A.target i).word x≠[]} := by
    intro h
    exact hx (Set.mem_iUnion.mpr ⟨i,h⟩)
  simpa using hi

lemma untwisted_commutes_attach (A : Table (Γ:=Γ) f) (hA : ∀ i,A.label i=1)
    (x : X) (hx : ∀ i,(A.source i).word x=[] ∧ (A.target i).word x=[])
    (b : Bool) (z : Cube X) :
    f ((Prefix.oneBit x b).attach z)=(Prefix.oneBit x b).attach (f z) := by
  obtain ⟨i,⟨w,rfl⟩,_⟩ := A.source_cover z
  rw [← Prefix.comp_attach,← Prefix.comp_oneBit_comm (hx i).1,Prefix.comp_attach,A.chart,
    hA i,twist_one]
  change (A.target i).attach ((Prefix.oneBit x b).attach w)=_
  rw [← Prefix.comp_attach,Prefix.comp_oneBit_comm (hx i).2,Prefix.comp_attach,A.chart,
    hA i,twist_one]
  rfl

end Table

lemma Untwisted.exists_diagonal [Infinite X] {f : group (Γ:=Γ) (X:=X)}
    (hf : Untwisted f) : ∃ x,f=diagonal x f := by
  obtain ⟨A,hA⟩ := hf
  obtain ⟨x,hx⟩ := A.exists_fresh
  refine ⟨x,Subtype.ext (Equiv.ext (fun z => ?_))⟩
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit x).cover z
  change f.val ((Prefix.oneBit x b).attach w)=
    (diagonal x f).val ((Prefix.oneBit x b).attach w)
  rw [diagonal_attach]
  exact A.untwisted_commutes_attach hA x hx b w

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Every twisted table differs from two half-copies of itself by an untwisted
finite table. This is a literal table construction, not an abelianized identity. -/
theorem exists_untwisted_correction [Infinite X] (f : group (Γ:=Γ) (X:=X)) :
    ∃ x : X, Untwisted (f * (diagonal x f)⁻¹) := by
  obtain ⟨A⟩ := (mem_group_iff_table _).mp f.property
  obtain ⟨x,hx⟩ := A.exists_fresh
  exact ⟨x,A.correction x (fun i => (hx i).1),fun _ => rfl⟩

end

section
universe u v w
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
variable {H : Type w} [CommGroup H]

lemma map_localize_half (h : group (Γ:=Γ) (X:=X) →* H) (p : Prefix X)
    (hp : p≠Prefix.empty) (x : X) (b : Bool) (f : group (Γ:=Γ) (X:=X)) :
    h (localize (p.comp (Prefix.oneBit x b)) f)=h (localize p f) := by
  obtain ⟨a,ha⟩ := exists_localize_half_conjugacy (Γ:=Γ) p hp x b
  have hh := congrArg h (ha f)
  simpa [map_mul,map_inv,mul_comm,mul_left_comm,mul_assoc] using hh.symm

lemma map_localize_diagonal (h : group (Γ:=Γ) (X:=X) →* H) (p : Prefix X)
    (hp : p≠Prefix.empty) (x : X) (f : group (Γ:=Γ) (X:=X)) :
    h (localize p (diagonal x f))=h (localize p f)*h (localize p f) := by
  rw [diagonal,map_mul,map_mul,← localize_comp,← localize_comp,
    map_localize_half h p hp,map_localize_half h p hp]

lemma eq_one_of_square_eq_self {a : H} (ha : a=a*a) : a=1 := by
  have he := congrArg (fun b => a⁻¹*b) ha
  simpa [mul_assoc] using he.symm

lemma map_localize_untwisted_eq_one [Infinite X] (h : group (Γ:=Γ) (X:=X) →* H)
    (p : Prefix X) (hp : p≠Prefix.empty) {f : group (Γ:=Γ) (X:=X)} (hf : Untwisted f) :
    h (localize p f)=1 := by
  obtain ⟨x,hx⟩ := hf.exists_diagonal
  apply eq_one_of_square_eq_self
  calc
    _ = h (localize p (diagonal x f)) := congrArg (fun g => h (localize p g)) hx
    _ = _ := map_localize_diagonal h p hp x f

lemma map_untwisted_eq_one [Infinite X] (h : group (Γ:=Γ) (X:=X) →* H)
    {f : group (Γ:=Γ) (X:=X)} (hf : Untwisted f) : h f=1 := by
  obtain ⟨x,hx⟩ := hf.exists_diagonal
  calc
    _ = h (diagonal x f) := congrArg h hx
    _ = 1 := by
      rw [diagonal,map_mul,
        map_localize_untwisted_eq_one h _ (Prefix.oneBit_ne_empty x false) hf,
        map_localize_untwisted_eq_one h _ (Prefix.oneBit_ne_empty x true) hf,one_mul]

lemma map_localize_eq_one [Infinite X] (h : group (Γ:=Γ) (X:=X) →* H)
    (p : Prefix X) (hp : p≠Prefix.empty) (f : group (Γ:=Γ) (X:=X)) :
    h (localize p f)=1 := by
  obtain ⟨x,hx⟩ := exists_untwisted_correction f
  have hh := map_localize_untwisted_eq_one h p hp hx
  simp only [map_mul,map_inv] at hh
  rw [map_localize_diagonal h p hp x f] at hh
  exact eq_one_of_square_eq_self (mul_inv_eq_one.mp hh)

/-- Every commutative image of the infinite-coordinate twisted table group is
trivial. The proof uses actual finite table label cancellation and compression. -/
theorem map_eq_one [Infinite X] (h : group (Γ:=Γ) (X:=X) →* H)
    (f : group (Γ:=Γ) (X:=X)) : h f=1 := by
  obtain ⟨x,hx⟩ := exists_untwisted_correction f
  have hh := map_untwisted_eq_one h hx
  have hd : h (diagonal x f)=1 := by
    rw [diagonal,map_mul,
      map_localize_eq_one h _ (Prefix.oneBit_ne_empty x false),
      map_localize_eq_one h _ (Prefix.oneBit_ne_empty x true),one_mul]
  simpa only [map_mul,map_inv,hd,inv_one,mul_one] using hh

instance infinite_group_perfect [Infinite X] : Group.IsPerfect (group (Γ:=Γ) (X:=X)) where
  commutator_eq_top := by
    apply top_unique
    intro f _
    rw [← Abelianization.ker_of]
    exact map_eq_one Abelianization.of f

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Partition

lemma size_refinement_bit (P : Partition X) (j : P.index) (x : X) :
    (P.refinement (bit x) j).size=P.size+1 := by
  let := P.finite
  have hp : 0<Fintype.card P.index := Fintype.card_pos_iff.mpr ⟨j⟩
  change Fintype.card ({k : P.index // k≠j} ⊕ Bool)=Fintype.card P.index+1
  rw [Fintype.card_sum,Fintype.card_subtype_compl (fun k => k=j),Fintype.card_subtype_eq,
    Fintype.card_bool]
  omega

/-- Add arbitrarily many complement bricks while leaving a proper selected brick
unchanged. -/
lemma pad (P : Partition X) (i : P.index) (hi : P.brick i≠Prefix.empty) (x : X) (n : ℕ) :
    ∃ Q : Partition X, ∃ j : Q.index, Q.brick j=P.brick i ∧ Q.size=P.size+n := by
  induction n with
  | zero => exact ⟨P,i,rfl,by omega⟩
  | succ n ih =>
      obtain ⟨Q,j,hj,hn⟩ := ih
      obtain ⟨k,hkj⟩ := Q.exists_other j (by rwa [hj])
      refine ⟨Q.refinement (bit x) k,Sum.inl ⟨j,Ne.symm hkj⟩,hj,?_⟩
      rw [size_refinement_bit,hn]
      omega

end Partition

/-- Any two proper finite dyadic bricks are related by an actual untwisted finite
table chart, with no equal-volume or equal-depth restriction. -/
theorem exists_brick_extension [Nonempty X] (p q : Prefix X)
    (hp : p≠Prefix.empty) (hq : q≠Prefix.empty) :
    ∃ h : group (Γ:=Γ) (X:=X), ∀ z,h.val (p.attach z)=q.attach z := by
  obtain ⟨P,i,hi⟩ := p.hasPartition
  obtain ⟨Q,j,hj⟩ := q.hasPartition
  let x : X := Classical.choice inferInstance
  obtain ⟨P',i',hi',hP'⟩ := P.pad i (by rwa [hi]) x Q.size
  obtain ⟨Q',j',hj',hQ'⟩ := Q.pad j (by rwa [hj]) x P.size
  let := P'.finite
  let := Q'.finite
  have hc : Fintype.card P'.index=Fintype.card Q'.index := by
    change P'.size=Q'.size
    omega
  let e : P'.index ≃ Q'.index := Fintype.equivOfCardEq hc
  let e' : P'.index ≃ Q'.index := e.trans (Equiv.swap (e i') j')
  have he : e' i'=j' := by simp [e']
  refine ⟨P'.changeChart Q' e',fun z => ?_⟩
  have hh := P'.changeChart_apply (Γ:=Γ) Q' e' i' z
  rwa [he,hi',hj',hi,hj] at hh

lemma normal_transport_localize [Nonempty X]
    (N : Subgroup (group (Γ:=Γ) (X:=X))) [N.Normal]
    (p q : Prefix X) (hp : p≠Prefix.empty) (hq : q≠Prefix.empty)
    (f : group (Γ:=Γ) (X:=X)) (hf : localize p f∈N) : localize q f∈N := by
  obtain ⟨h,hh⟩ := exists_brick_extension (Γ:=Γ) p q hp hq
  rw [← localize_conj h hh f]
  exact (inferInstance : N.Normal).conj_mem _ hf h

end

section
universe u v
attribute [local instance] Classical.propDecidable
open scoped commutatorElement
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Perfection upgrades the localized double-commutator conclusion to a full
local copy inside every nontrivial normal subgroup. -/
lemma normal_contains_local_copy [Infinite X]
    (N : Subgroup (group (Γ:=Γ) (X:=X))) [N.Normal] (hN : N≠⊥) :
    ∃ p : Prefix X, ∀ f : group (Γ:=Γ) (X:=X),localize p f∈N := by
  obtain ⟨p,hp⟩ := normal_contains_local_commutators N hN
  have hc : commutator (group (Γ:=Γ) (X:=X))≤N.comap (localize p) := by
    rw [commutator_eq_closure,Subgroup.closure_le]
    rintro f ⟨a,b,rfl⟩
    exact hp a b
  exact ⟨p,fun f => hc (Group.IsPerfect.mem_commutator (g:=f))⟩

/-- Simplicity of the actual twisted finite-table permutation group on an
infinite coordinate set. No finite-presentation or simplicity endpoint is
assumed. -/
theorem normal_eq_top [Infinite X]
    (N : Subgroup (group (Γ:=Γ) (X:=X))) [N.Normal] (hN : N≠⊥) : N=⊤ := by
  obtain ⟨p,hp⟩ := normal_contains_local_copy N hN
  by_cases he : p=Prefix.empty
  · apply top_unique
    intro f _
    simpa [he] using hp f
  have hloc (q : Prefix X) (hq : q≠Prefix.empty) (f : group (Γ:=Γ) (X:=X)) :
      localize q f∈N := normal_transport_localize N p q he hq f (hp f)
  have hdiag (x : X) (f : group (Γ:=Γ) (X:=X)) : diagonal x f∈N :=
    N.mul_mem (hloc _ (Prefix.oneBit_ne_empty x false) f)
      (hloc _ (Prefix.oneBit_ne_empty x true) f)
  have hunt (f : group (Γ:=Γ) (X:=X)) (hf : Untwisted f) : f∈N := by
    obtain ⟨x,hx⟩ := hf.exists_diagonal
    rw [hx]
    exact hdiag x f
  apply top_unique
  intro f _
  obtain ⟨x,hx⟩ := exists_untwisted_correction f
  have hr := hunt _ hx
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using N.mul_mem hr (hdiag x f)

instance infinite_group_simple [Infinite X] : IsSimpleGroup (group (Γ:=Γ) (X:=X)) where
  eq_bot_or_eq_top_of_normal N hnormal := by
    let := hnormal
    by_cases hN : N=⊥
    · exact Or.inl hN
    · exact Or.inr (normal_eq_top N hN)

end

universe u v
attribute [local instance] Classical.propDecidable

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Intermediate simple overgroups, finite-presentation transport, and Boone–Higman equivalence.
-/

namespace FiniteAlgebraicEnvelopes
universe u

/-- Forward direction of the Boone–Higman equivalence, using the proved action
envelope and the complete finite presentation of its concrete simple endpoint. -/
theorem main_forward (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) : EmbedsInFinitelyPresentedSimpleGroup G := by
  obtain ⟨Γ,hΓ,X,hX,hfp,hcount,hinf,hfaith,htwo,hstab,f,hf⟩ := envelope G hG
  let := hfp
  let := hcount
  let := hinf
  let := hfaith
  refine ⟨TwistedBrinThompson.group (Γ:=Γ) (X:=X),inferInstance,
    TwistedBrinThompson.finitelyPresented htwo hstab,inferInstance,
    (TwistedBrinThompson.embedding (X:=X)).comp f,?_⟩
  exact TwistedBrinThompson.embedding_injective.comp hf

/-- Manuscript Theorem 1.1, with arbitrary finitely generated input, including
finite and trivial input groups, and genuine algorithmic word-problem decidability. -/
theorem main_oai (G : Type u) [Group G] [Group.FG G] :
    HasDecidableWordProblem G ↔ EmbedsInFinitelyPresentedSimpleGroup G :=
  ⟨main_forward G, main_reverse G⟩

end FiniteAlgebraicEnvelopes

end

end OAI
end

theorem solution.{u} : type_of% @OAI.FiniteAlgebraicEnvelopes.main_oai.{u} := @OAI.FiniteAlgebraicEnvelopes.main_oai.{u}

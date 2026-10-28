-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.isSimpleGroup_group
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T20:39:12.295068+00:00
-- url     : https://prove2.me/submissions/2976c55c-4433-4b06-b2dd-4460778340df

import Mathlib
import Definitions.Def_OAIFAE004

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
-- module Solutions.OAIFAE.Forward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v

/-- The twisted Brin–Thompson group of an action on an infinite set is simple
(OpenAI's instance `infinite_group_simple`, stated as a theorem). -/
theorem isSimpleGroup_group_oai {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X] [Infinite X] :
    IsSimpleGroup (group (Γ:=Γ) (X:=X)) :=
  infinite_group_simple

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.isSimpleGroup_group_oai.{u, v} := @OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.isSimpleGroup_group_oai.{u, v}

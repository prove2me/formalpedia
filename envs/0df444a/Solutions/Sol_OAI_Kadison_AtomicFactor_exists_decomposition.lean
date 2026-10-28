-- Prove2me | solution 1 for OAI.Kadison.AtomicFactor.exists_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:33:51.100249+00:00
-- url     : https://prove2.me/submissions/8f754bbd-32ed-486e-8e23-90ac190c1fe5

import Mathlib
import Definitions.Def_OAIQ039C046

section
-- module Solutions.OAIQ039_CM.Commutator_OrthogonalLinkFamily
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

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

lemma exists_maximal_orthogonalLinks :
    ∃ S : Set (Link M e f),Maximal (OrthogonalLinks M e f) S := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c,?_,fun s hs => Set.subset_sUnion_of_mem hs⟩
  intro v hv w hw hne
  obtain ⟨s,hs,hvs⟩ := hv
  obtain ⟨t,ht,hwt⟩ := hw
  rcases hchain.total hs ht with hst|hts
  · exact hc ht (hst hvs) hwt hne
  · exact hc hs hvs (hts hwt) hne

lemma familySpace_generator (S : Set (Link M e f)) {v : Link M e f} (hv : v∈S) (ξ : H) :
    v.val ξ∈familySpace M e f S :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v,hv,ξ,rfl⟩)

lemma familySpace_invariant (S : Set (Link M e f)) {a : H →L[ℂ] H}
    (ha : a∈Set.centralizer (M : Set (H →L[ℂ] H))) :
    ∀ x∈familySpace M e f S,a x∈familySpace M e f S := by
  intro x hx
  apply closure_minimal (t:={x | a x∈familySpace M e f S}) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage a.continuous) hx
  change Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x} ≤
    (familySpace M e f S).comap a.toLinearMap
  apply Submodule.span_le.mpr
  rintro y ⟨v,hv,ξ,rfl⟩
  have he : a (v.val ξ)=v.val (a ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ) (ha v.val v.mem).symm
  change a (v.val ξ)∈familySpace M e f S
  rw [he]
  exact familySpace_generator M e f S hv _

lemma familySpace_projection_mem (S : Set (Link M e f)) :
    (familySpace M e f S).starProjection∈M := by
  change (familySpace M e f S).starProjection∈M.carrier
  rw [←M.centralizer_centralizer']
  intro a ha
  have hsa : star a∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
    intro b hb
    simpa only [star_mul,star_star] using congrArg star (ha (star b) (M.star_mem' hb)).symm
  exact (projection_commutes_of_invariant _ a (familySpace_invariant M e f S ha)
    (familySpace_invariant M e f S hsa)).symm

lemma familySpace_projection_mul (S : Set (Link M e f)) {v : Link M e f} (hv : v∈S) :
    (familySpace M e f S).starProjection*v.val=v.val := by
  ext ξ
  exact Submodule.starProjection_eq_self_iff.mpr (familySpace_generator M e f S hv ξ)

lemma familySpace_target_mul (S : Set (Link M e f)) (hf : IsStarProjection f) :
    f*(familySpace M e f S).starProjection=(familySpace M e f S).starProjection := by
  have hfix : ∀ x∈familySpace M e f S,f x=x := by
    intro x hx
    apply closure_minimal (t:={x | f x=x}) ?_
      (isClosed_eq f.continuous continuous_id) hx
    have hspan : Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x} ≤
        LinearMap.ker (f-1).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro y ⟨v,hv,ξ,rfl⟩
      change f (v.val ξ)-v.val ξ=0
      rw [show f (v.val ξ)=v.val ξ from congrArg (fun T : H →L[ℂ] H => T ξ) (v.target_mul hf),sub_self]
    intro y hy
    have he := hspan hy
    exact sub_eq_zero.mp he
  ext x
  exact hfix _ ((familySpace M e f S).starProjection_apply_mem x)

theorem maximal_family_spans (hM : FactorCorner.IsFactor M)
    (heM : e∈M) (hfM : f∈M) (he : IsStarProjection e) (hf : IsStarProjection f) (hne : e≠0)
    (S : Set (Link M e f)) (hS : Maximal (OrthogonalLinks M e f) S) :
    (familySpace M e f S).starProjection=f := by
  let q := (familySpace M e f S).starProjection
  have hq : IsStarProjection q := isStarProjection_starProjection
  have hqM : q∈M := familySpace_projection_mem M e f S
  have hfq : f*q=q := familySpace_target_mul M e f S hf
  have hqf : q*f=q := by simpa only [star_mul,hq.isSelfAdjoint.star_eq,hf.isSelfAdjoint.star_eq] using congrArg star hfq
  have hr : IsStarProjection (f-q) := hq.sub_of_mul_eq_left hf hqf
  by_contra hqne
  have hrne : f-q≠0 := by
    intro hz
    exact hqne (sub_eq_zero.mp hz).symm
  obtain ⟨w,hwM,hwne,hwtr,hwsrc,hwtgt⟩ :=
    FactorCorner.exists_linking_partialIsometry M hM heM (M.sub_mem hfM hqM) he hr hne hrne
  let w' : Link M e (f-q) := ⟨w,hwM,hwtr,hwsrc,hwtgt⟩
  have hrw : (f-q)*w=w := w'.target_mul hr
  have hwf : w*star w≤f := hwtgt.trans (sub_le_self _ hq.nonneg)
  let v : Link M e f := ⟨w,hwM,hwtr,hwsrc,hwf⟩
  have hvorth (u : Link M e f) (hu : u∈S) : star u.val*w=0 := by
    have hqu : q*u.val=u.val := familySpace_projection_mul M e f S hu
    have hsuq : star u.val*q=star u.val := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq] using congrArg star hqu
    have huf : star u.val*f=star u.val := by
      simpa only [star_mul,hf.isSelfAdjoint.star_eq] using congrArg star (u.target_mul hf)
    calc
      _=star u.val*((f-q)*w) := by rw [hrw]
      _=0 := by rw [←mul_assoc,mul_sub,huf,hsuq,sub_self,zero_mul]
  have hins : OrthogonalLinks M e f (insert v S) := by
    intro a ha b hb hne'
    rcases ha with rfl|ha <;> rcases hb with rfl|hb
    · exact (hne' rfl).elim
    · simpa only [star_mul,star_star,star_zero] using congrArg star (hvorth b hb)
    · exact hvorth a ha
    · exact hS.1 ha hb hne'
  have hvS : v∈S := hS.2 hins (Set.subset_insert v S) (Set.mem_insert v S)
  have hqw : q*w=w := familySpace_projection_mul M e f S hvS
  have hqr : q*(f-q)=0 := by rw [mul_sub,hqf,hq.isIdempotentElem.eq,sub_self]
  have : q*w=0 := by calc
    _=q*((f-q)*w) := by rw [hrw]
    _=0 := by rw [←mul_assoc,hqr,zero_mul]
  exact hwne (hqw.symm.trans this)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicDecomposition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

universe u

namespace Kadison.AtomicFactor

open PartialIsometryOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_decomposition_oai (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    {p : H →L[ℂ] H} (hp : IsMinimalProjection M p) : Nonempty (Decomposition M p) := by
  classical
  obtain ⟨S,hS⟩ := exists_maximal_orthogonalLinks M p 1
  let T : Set (Link M p 1) := {v | v∈S ∧ v.val≠0}
  have hTS : T⊆S := fun _ h => h.1
  have hT : OrthogonalLinks M p 1 T := fun _ hv _ hw hne => hS.1 (hTS hv) (hTS hw) hne
  have hspaces : familySpace M p 1 T=familySpace M p 1 S := by
    apply le_antisymm
    · apply Submodule.topologicalClosure_mono
      apply Submodule.span_mono
      rintro x ⟨v,hv,ξ,rfl⟩
      exact ⟨v,hTS hv,ξ,rfl⟩
    · apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro x ⟨v,hv,ξ,rfl⟩
        change v.val ξ∈familySpace M p 1 T
        by_cases hz : v.val=0
        · rw [hz]
          exact (familySpace M p 1 T).zero_mem
        · exact familySpace_generator M p 1 T ⟨hv,hz⟩ ξ
      · exact Submodule.isClosed_topologicalClosure _
  have hspan : (familySpace M p 1 T).starProjection=1 := by
    have he : (familySpace M p 1 T).starProjection=(familySpace M p 1 S).starProjection := by
      congr 1
    rw [he]
    exact maximal_family_spans M p 1 hM hp.1 M.one_mem hp.2.1 (IsStarProjection.one _) hp.2.2.1 S hS
  refine ⟨⟨T,fun i => i.val.val,fun i => i.val.mem,?_,?_,?_,?_⟩⟩
  · intro i
    rcases hp.2.2.2 i.val.initial (M.mul_mem (M.star_mem' i.val.mem) i.val.mem)
      i.val.initial_projection i.val.source_le with hz|hz
    · have he := i.val.mul_initial
      rw [hz,mul_zero] at he
      exact (i.property.2 he.symm).elim
    · exact hz
  · intro i j hne
    exact family_cross M p 1 T hT hne
  · intro i
    exact i.val.mul_source hp.2.1
  · intro x
    simpa only [finiteProjection,Link.final,one_apply_eq_self] using
      finiteProjection_tendsto M p 1 T hT (IsStarProjection.one _) hspan x

end Kadison.AtomicFactor

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.AtomicFactor.exists_decomposition_oai.{u} := @OAI.Kadison.AtomicFactor.exists_decomposition_oai.{u}

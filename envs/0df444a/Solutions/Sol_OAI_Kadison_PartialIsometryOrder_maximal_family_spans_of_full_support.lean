-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.maximal_family_spans_of_full_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:30:53.578866+00:00
-- url     : https://prove2.me/submissions/5f9731d3-f6c9-4e76-9635-23a645ca4e72

import Mathlib
import Definitions.Def_OAIQ039C033

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

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FullCentralSupportLinks
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FactorCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_nonzero_corner_of_full_support (M : VonNeumannAlgebra H)
    {e f : H →L[ℂ] H} (hsupport : (supportSpace M e).starProjection=1) (hff : f≠0) :
    ∃ a∈M, f*a*e≠0 := by
  by_contra! h
  have hz : ∀ x∈supportSpace M e, f x=0 := by
    intro x hx
    apply closure_minimal (t := {x | f x=0}) ?_
      (isClosed_eq f.continuous continuous_const) hx
    have hspan : Submodule.span ℂ {x | ∃ a∈M, ∃ ξ : H, a (e ξ)=x} ≤ LinearMap.ker f.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro y ⟨a,ha,ξ,rfl⟩
      exact congrArg (fun T : H →L[ℂ] H => T ξ) (h a ha)
    exact hspan
  apply hff
  ext x
  have hm := (supportSpace M e).starProjection_apply_mem x
  rw [hsupport] at hm
  exact hz x hm

theorem exists_linking_partialIsometry_of_full_support (M : VonNeumannAlgebra H)
    {e f : H →L[ℂ] H} (he : e∈M) (hfM : f∈M)
    (hpe : IsStarProjection e) (hpf : IsStarProjection f)
    (hsupport : (supportSpace M e).starProjection=1) (hnf : f≠0) :
    ∃ v∈M, v≠0 ∧ v*star v*v=v ∧ star v*v≤e ∧ v*star v≤f := by
  obtain ⟨a,ha,hna⟩ := exists_nonzero_corner_of_full_support M hsupport hnf
  let x := f*a*e
  have hx : x∈M := M.mul_mem (M.mul_mem hfM ha) he
  have hfx : f*x=x := by dsimp only [x]; rw [←mul_assoc,←mul_assoc,hpf.isIdempotentElem.eq]
  have hxe : x*e=x := by dsimp only [x]; rw [mul_assoc,hpe.isIdempotentElem.eq]
  refine ⟨Polar.partialIsometry x,Polar.partialIsometry_mem_vonNeumann M hx,?_,
    Polar.partialIsometry_triple x,?_,?_⟩
  · intro hzero
    apply hna
    have hfact := Polar.factorization x
    rw [hzero,zero_mul] at hfact
    exact hfact.symm
  · rw [Polar.partialIsometry_initial]
    exact Polar.rightSupport_le x e hpe hxe
  · exact Polar.leftSupport_le x f hpf hfx

end Kadison.FactorCorner

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

theorem maximal_family_spans_of_full_support_oai
    (hsupport : (FactorCorner.supportSpace M e).starProjection=1)
    (heM : e∈M) (hfM : f∈M) (he : IsStarProjection e) (hf : IsStarProjection f)
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
    FactorCorner.exists_linking_partialIsometry_of_full_support M heM (M.sub_mem hfM hqM) he hr hsupport hrne
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

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.maximal_family_spans_of_full_support_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.maximal_family_spans_of_full_support_oai.{u_1}

-- Prove2me | solution 1 for OAI.Kadison.NormalRepresentation.exists_orthogonal_links
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:42:52.798784+00:00
-- url     : https://prove2.me/submissions/608c3989-d816-4aea-8f97-b4fc978f8fb4

import Mathlib
import Definitions.Def_OAIQ039C062
import Theorems.Thm_OAI_Kadison_NormalRepresentation_diagonal_factor
import Theorems.Thm_OAI_Kadison_NormalRepresentation_right_mem_commutant

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertBiprodProjections
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace H] [CompleteSpace G] in
lemma left_commutes (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block S T*left=left*block S T := by
  rw [left,←block_mul,←block_mul]
  simp

omit [CompleteSpace H] [CompleteSpace G] in
lemma right_ne_zero [Nontrivial G] : right (H:=H) (G:=G)≠0 := by
  obtain ⟨x,hx⟩ := exists_ne (0:G)
  intro hz
  apply hx
  have he := congrArg (fun T : Space H G →L[ℂ] Space H G => (T (inr x)).ofLp.2) hz
  change x=0 at he
  exact he

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiagonalBlockCommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

variable (h : Set.centralizer (Set.centralizer (Set.range (diagHom φ ψ)))=Set.range (diagHom φ ψ))

lemma left_mem_diagonal_commutant :
    left (H:=H) (G:=G)∈(BicommutantRange.ofStarHom (H:=Space H G) (diagHom φ ψ) h).commutant := by
  rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
  rintro _ ⟨a,rfl⟩
  exact left_commutes _ _

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrthogonalLinkFamily
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
-- module Solutions.OAIQ039_CM.Commutator_RepresentedFactorTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.FactorCorner

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H)

lemma commutant_factor (hM : IsFactor M) : IsFactor M.commutant := by
  intro z hz hzc
  have hzM : z∈M := by
    have hc : z∈M.commutant.commutant := by
      rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
      exact hzc
    simpa only [VonNeumannAlgebra.commutant_commutant] using hc
  apply hM z hzM
  simpa only [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant] using hz

end Kadison.FactorCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalRepresentationLinks
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

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma gns_nontrivial (h1 : τ 1=1) : Nontrivial τ.GNS := by
  let v := TracialGNS.algebraVector τ (1:M)
  have hv : inner ℂ v v=1 := by
    rw [TracialGNS.inner_algebraVector]
    simpa using h1
  have hne : v≠0 := by
    intro h
    rw [h,inner_zero_left] at hv
    exact zero_ne_one hv
  exact ⟨⟨v,0,hne⟩⟩

lemma left_mem_commutant (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    left (H:=H) (G:=τ.GNS)∈(diagonalAlgebra M τ hnormal).commutant :=
  left_mem_diagonal_commutant (A:=M) (H:=H) (G:=τ.GNS)
    M.toStarSubalgebra.subtype τ.gnsStarAlgHom (NormalOperatorHom.diagonal_gns_range M τ hnormal)

theorem exists_orthogonal_links_oai (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hM : FactorCorner.IsFactor M) (h1 : τ 1=1) :
    ∃ S : Set (Link (diagonalAlgebra M τ hnormal).commutant
      (right (H:=H) (G:=τ.GNS)) left),
      OrthogonalLinks _ _ _ S ∧ (familySpace _ _ _ S).starProjection=left := by
  let : Nontrivial τ.GNS := gns_nontrivial M τ h1
  obtain ⟨S,hS⟩ := exists_maximal_orthogonalLinks (diagonalAlgebra M τ hnormal).commutant
    (right (H:=H) (G:=τ.GNS)) left
  refine ⟨S,hS.1,?_⟩
  exact maximal_family_spans _ _ _
    (FactorCorner.commutant_factor _ (diagonal_factor M τ hnormal hM))
    (right_mem_commutant M τ hnormal) (left_mem_commutant M τ hnormal)
    right_projection left_projection right_ne_zero S hS

end Kadison.NormalRepresentation

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalRepresentation.exists_orthogonal_links_oai.{u_1} := @OAI.Kadison.NormalRepresentation.exists_orthogonal_links_oai.{u_1}

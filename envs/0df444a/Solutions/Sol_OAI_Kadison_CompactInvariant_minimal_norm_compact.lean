-- Prove2me | solution 1 for OAI.Kadison.CompactInvariant.minimal_norm_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:10:58.49007+00:00
-- url     : https://prove2.me/submissions/448a863d-3da3-4e6d-bafd-154607378c31

import Mathlib
import Definitions.Def_OAIQ039C004

section
-- module Solutions.OAIQ039_CM.Commutator_BaireSmallPiece
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Set TopologicalSpace

namespace Kadison.BaireSmallPiece

variable {X E : Type*} [TopologicalSpace X] [T2Space X] [MetricSpace E]

theorem exists_open_piece (j : X → E) {C : Set X} (hC : IsCompact C)
    (hne : C.Nonempty) (hsep : IsSeparable (j '' C))
    (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y ≤ r})
    (ε : ℝ) (hε : 0<ε) :
    ∃ U : Set X,IsOpen U ∧ (C∩U).Nonempty ∧
      ∀ x∈C∩U,∀ y∈C∩U,dist (j x) (j y)<ε := by
  classical
  obtain ⟨D,hDc,hD⟩ := hsep
  have : Countable D := hDc.to_subtype
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have : Nonempty C := hne.to_subtype
  let A : D → Set C := fun d => {x | dist (j x) d≤ε/4}
  have hAc (d : D) : IsClosed (A d) := (hball d (ε/4)).preimage continuous_subtype_val
  have hAu : ⋃ d,A d=univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    have hx : j x∈closure D := hD ⟨x,x.property,rfl⟩
    obtain ⟨d,hd,hxd⟩ := Metric.mem_closure_iff.mp hx (ε/4) (by positivity)
    exact mem_iUnion.mpr ⟨⟨d,hd⟩,hxd.le⟩
  obtain ⟨d,hd⟩ := nonempty_interior_of_iUnion_of_closed hAc hAu
  obtain ⟨U,hU,hUi⟩ := isOpen_induced_iff.mp (show IsOpen (interior (A d)) from isOpen_interior)
  refine ⟨U,hU,?_,?_⟩
  · obtain ⟨x,hx⟩ := hd
    refine ⟨x,x.property,?_⟩
    have hx' : x∈Subtype.val ⁻¹' U := by rw [hUi]; exact hx
    exact hx'
  · intro x hx y hy
    have hxd : dist (j x) d≤ε/4 := by
      change (⟨x,hx.1⟩ : C)∈A d
      apply interior_subset (s:=A d)
      rw [←hUi]
      exact (show (⟨x,hx.1⟩ : C)∈Subtype.val ⁻¹' U from hx.2)
    have hyd : dist (j y) d≤ε/4 := by
      change (⟨y,hy.1⟩ : C)∈A d
      apply interior_subset (s:=A d)
      rw [←hUi]
      exact (show (⟨y,hy.1⟩ : C)∈Subtype.val ⁻¹' U from hy.2)
    calc
      dist (j x) (j y) ≤ dist (j x) d+dist (d : E) (j y) := dist_triangle _ _ _
      _ ≤ ε/4+ε/4 := add_le_add hxd (by simpa only [dist_comm] using hyd)
      _ < ε := by linarith

end Kadison.BaireSmallPiece

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MinimalOrbit
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Set

namespace Kadison.CompactInvariant

variable {G X : Type*} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X]

omit [T2Space X] in
lemma invariant_closure {S : Set X} (hS : Invariant (G:=G) S) :
    Invariant (G:=G) (closure S) := by
  intro g x hx
  apply closure_mono (show (fun y : X => g • y) '' S⊆S from by
    rintro _ ⟨y,hy,rfl⟩; exact hS g y hy)
  exact mem_closure_image (continuous_const_smul g).continuousAt hx

omit [TopologicalSpace X] [T2Space X] [ContinuousConstSMul G X] in
lemma invariant_orbit (x : X) : Invariant (G:=G) (MulAction.orbit G x) := by
  intro g y hy
  obtain ⟨h,rfl⟩ := hy
  exact ⟨g*h,mul_smul g h x⟩

omit [T2Space X] in
lemma minimal_orbit_closure {C K : Set X}
    (hK : Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧ Invariant (G:=G) S) K)
    {x : X} (hx : x∈K) : closure (MulAction.orbit G x)=K := by
  have ho : MulAction.orbit G x⊆K := by
    rintro y ⟨g,rfl⟩
    exact hK.prop.2.2.2 g x hx
  have hs : closure (MulAction.orbit G x)⊆K := closure_minimal ho hK.prop.2.2.1
  apply hs.antisymm
  apply hK.le_of_le _ hs
  exact ⟨hs.trans hK.prop.1,⟨x,subset_closure ⟨1,one_smul G x⟩⟩,isClosed_closure,
    invariant_closure (invariant_orbit x)⟩

omit [T2Space X] in
lemma minimal_finite_open_cover {C K : Set X} (hcomp : IsCompact K)
    (hK : Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧ Invariant (G:=G) S) K)
    {U : Set X} (hU : IsOpen U) (hne : (K∩U).Nonempty) :
    ∃ t : Finset G,K⊆⋃ g∈t,(fun x : X => g • x) ⁻¹' U := by
  apply hcomp.elim_finite_subcover (fun g : G => (fun x : X => g • x) ⁻¹' U)
    (fun g => hU.preimage (continuous_const_smul g))
  intro x hx
  obtain ⟨y,hyK,hyU⟩ := hne
  have hycl : y∈closure (MulAction.orbit G x) := by
    rw [minimal_orbit_closure hK hx]
    exact hyK
  obtain ⟨z,hzU,hzorbit⟩ := mem_closure_iff.mp hycl U hU hyU
  obtain ⟨g,rfl⟩ := hzorbit
  exact mem_iUnion.mpr ⟨g,hzU⟩

end Kadison.CompactInvariant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MinimalNormCompact
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Set TopologicalSpace

namespace Kadison.CompactInvariant

variable {G X E : Type*} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [MetricSpace E] [CompleteSpace E]

theorem minimal_norm_compact_oai (j : X ≃ E) (hj : Continuous j.symm)
    (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y ≤ r})
    (hiso : ∀ g : G,∀ x y : X,dist (j (g • x)) (j (g • y))=dist (j x) (j y))
    {C K : Set X} (hcomp : IsCompact K)
    (hK : Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧ Invariant (G:=G) S) K)
    (hsep : IsSeparable (j '' K)) : IsCompact (j '' K) := by
  classical
  have hclosed : IsClosed (j '' K) := by
    have he : j '' K=j.symm ⁻¹' K := by
      ext y
      simp only [mem_image,mem_preimage]
      constructor
      · rintro ⟨x,hx,rfl⟩; simpa only [j.symm_apply_apply] using hx
      · intro hy; exact ⟨j.symm y,hy,j.apply_symm_apply y⟩
    rw [he]
    exact hK.prop.2.2.1.preimage hj
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_,hclosed.isComplete⟩
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨U,hU,hUn,hd⟩ := BaireSmallPiece.exists_open_piece j hcomp hK.prop.2.1 hsep hball ε hε
  obtain ⟨u,huK,huU⟩ := hUn
  obtain ⟨t,ht⟩ := minimal_finite_open_cover hcomp hK hU ⟨u,huK,huU⟩
  let T : Set E := (fun g : G => j (g⁻¹ • u)) '' (t : Set G)
  refine ⟨T,t.finite_toSet.image _,?_⟩
  rintro y ⟨x,hx,rfl⟩
  obtain ⟨g,hg,hgx⟩ := mem_iUnion₂.mp (ht hx)
  refine mem_iUnion₂.mpr ⟨j (g⁻¹ • u),⟨g,hg,rfl⟩,?_⟩
  change dist (j x) (j (g⁻¹ • u))<ε
  rw [←hiso g x (g⁻¹ • u)]
  simp only [smul_inv_smul]
  exact hd (g • x) ⟨hK.prop.2.2.2 g x hx,hgx⟩ u ⟨huK,huU⟩

end Kadison.CompactInvariant

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.CompactInvariant.minimal_norm_compact_oai.{u_1, u_2, u_3} := @OAI.Kadison.CompactInvariant.minimal_norm_compact_oai.{u_1, u_2, u_3}

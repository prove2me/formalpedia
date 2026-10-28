-- Prove2me | solution 1 for OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:00:05.944986+00:00
-- url     : https://prove2.me/submissions/b44f08db-f8a8-4cd1-9d85-7504333220ab

import Mathlib
import Definitions.Def_OAIQ66So016
import Definitions.Def_OAIQ66So031
import Theorems.Thm_OAI_TwistedBrin_Basis_CutBasis_lower_exactSet
import Theorems.Thm_OAI_TwistedBrin_Basis_CutBasis_sublevel_cocycle_trivial

section
-- module Solutions.OAIQ066_SO.FiniteType_ClassifyingSpaces
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace FiniteExtension
universe u
variable {L : Type u} [Group L] (K : Subgroup L) [K.Normal]

lemma rels_finite [Finite (Q K)] (S : Set K) (hS : S.Finite) : (rels K S).Finite :=
  ((Set.finite_singleton _).union (Set.finite_range _)).union
    ((Set.finite_univ.prod hS).image _)

theorem finitelyPresented [Finite (Q K)] [Group.IsFinitelyPresented K] :
    Group.IsFinitelyPresented L := by
  obtain ⟨n,φ,hφ,_⟩ := (inferInstance : Group.IsFinitelyPresented K).out
  have : Group.FG K := Group.fg_of_surjective hφ
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG K)
  have : Group.IsFinitelyPresented (Presented K S) :=
    Group.IsFinitelyPresented.quotient (N K S) ⟨rels K S,rels_finite K S hfin,rfl⟩
  exact Group.IsFinitelyPresented.equiv (presentationEquiv K S hS)
end FiniteExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SurjectiveTrivialInduction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace SurjectiveTrivialInduction
open _root_.CategoryTheory _root_.OAI.CategoryTheory _root_.Representation _root_.OAI.Representation
attribute [-instance] AddCommGroup.toIntModule
end SurjectiveTrivialInduction

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace ProductGroupHomology
section
attribute [-instance] AddCommGroup.toIntModule

open scoped MonoidalCategory
end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

attribute [instance] AddCommGroup.toIntModule

namespace ActionPresentation
section
universe u v w
variable {Q : Type u} {G : Type v} [Group Q] [Group G]

lemma ker_retraction_fg [Group.FG Q] (p : Q →* G) (s : G →* Q)
    (hs : p.comp s = MonoidHom.id G) : p.ker.IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG Q)
  let D : Set Q := (fun q => q * (s (p q))⁻¹) '' S
  let N := Subgroup.normalClosure D
  have hN : N ≤ p.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨q,hq,rfl⟩
    have hsq : p (s (p q)) = p q := DFunLike.congr_fun hs _
    simp [MonoidHom.mem_ker,hsq]
  refine ⟨D,hfin.image _, le_antisymm ?_ ?_⟩
  · exact hN
  · let f := QuotientGroup.mk' N
    have hf : ∀ q ∈ S, f q = f (s (p q)) := by
      intro q hq
      have hd : q * (s (p q))⁻¹ ∈ N := Subgroup.subset_normalClosure ⟨q,hq,rfl⟩
      exact mul_inv_eq_one.mp (by simpa [f] using (QuotientGroup.eq_one_iff _).mpr hd)
    have he : f = f.comp (s.comp p) := by
      apply MonoidHom.ext
      intro q
      have hq : q ∈ Subgroup.closure S := by rw [hS]; trivial
      induction hq using Subgroup.closure_induction with
      | mem q hq => exact hf q hq
      | one => simp
      | mul a b ha hb ia ib => simpa using congrArg₂ (· * ·) ia ib
      | inv a ha ia => simpa using congrArg Inv.inv ia
    intro q hq
    apply (QuotientGroup.eq_one_iff q).mp
    have hp : p q = 1 := hq
    simpa [f,hp] using DFunLike.congr_fun he q

lemma finitelyPresented_retract [Group.IsFinitelyPresented Q]
    (p : Q →* G) (s : G →* Q) (hs : p.comp s = MonoidHom.id G) :
    Group.IsFinitelyPresented G := by
  obtain ⟨n,f,hf,hker⟩ := (inferInstance : Group.IsFinitelyPresented Q).out
  let : Group.FG Q := Group.fg_of_surjective hf
  exact Group.IsFinitelyPresented.of_surjective p
    (fun g => ⟨s g,DFunLike.congr_fun hs g⟩) (ker_retraction_fg p s hs)

variable {F : Type*} {H : Type*} {R : Type*} [Group F] [Group H] [Group R]

lemma descend_comp (f : F →* H) (hf : Function.Surjective f)
    (g : F →* R) (hg : f.ker ≤ g.ker) : (descend f hf g hg).comp f = g := by
  ext x
  have he : (QuotientGroup.quotientKerEquivOfSurjective f hf) (QuotientGroup.mk x) = f x := rfl
  have hi := congrArg (QuotientGroup.quotientKerEquivOfSurjective f hf).symm he
  simp only [MulEquiv.symm_apply_apply] at hi
  change (QuotientGroup.lift f.ker g hg)
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x)) = g x
  rw [← hi]
  rfl

namespace LiftModel
variable {p : Q →* G} {f : H →* G} (M : LiftModel p f)
lemma obstruction_finite : M.obstruction.Finite := M.finite.image _
lemma obstruction_ker : M.obstruction ⊆ p.ker := by
  rintro q ⟨r,hr,rfl⟩
  have hk : M.present r = 1 := by
    apply (MonoidHom.mem_ker).mp
    rw [← M.kernel]
    exact Subgroup.subset_normalClosure hr
  change p (M.lift r) = 1
  simpa [hk] using DFunLike.congr_fun M.commutes r
lemma hom_comp (q : Q →* R) (hq : ∀ r ∈ M.obstruction, q r = 1) :
    (M.hom q hq).comp M.present = q.comp M.lift := descend_comp _ _ _ _
lemma hom_commutes (q : Q →* R) (hq : ∀ r ∈ M.obstruction, q r = 1)
    (p' : R →* G) (hp' : p'.comp q = p) : p'.comp (M.hom q hq) = f := by
  ext h
  obtain ⟨r,rfl⟩ := M.surjective h
  change p' (M.hom q hq (M.present r)) = f (M.present r)
  have hh := DFunLike.congr_fun (M.hom_comp q hq) r
  change M.hom q hq (M.present r) = q (M.lift r) at hh
  rw [hh]
  exact (DFunLike.congr_fun hp' (M.lift r)).trans (DFunLike.congr_fun M.commutes r)
end LiftModel

lemma killProjection_surj (p : Q →* G) (hp : Function.Surjective p)
    (S : Set Q) (hS : S ⊆ p.ker) : Function.Surjective (killProjection p S hS) := by
  intro g
  obtain ⟨q,rfl⟩ := hp g
  exact ⟨QuotientGroup.mk q,rfl⟩
lemma kill_finitelyPresented [Group.IsFinitelyPresented Q] (S : Set Q) (hS : S.Finite) :
    Group.IsFinitelyPresented (Q ⧸ Subgroup.normalClosure S) :=
  Group.IsFinitelyPresented.quotient (Subgroup.normalClosure S) ⟨S,hS,rfl⟩

end

universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
lemma fg_of_fp [Group.IsFinitelyPresented G] : Group.FG G := by
  obtain ⟨n,f,hf,_⟩ := (inferInstance : Group.IsFinitelyPresented G).out
  exact Group.fg_of_surjective hf

lemma commute_of_generators {Q : Type w} [Group Q] (f : G →* Q) (g : H →* Q)
    (S : Set G) (T : Set H) (hS : Subgroup.closure S = ⊤) (hT : Subgroup.closure T = ⊤)
    (h : ∀ x ∈ S, ∀ y ∈ T, Commute (f x) (g y)) : ∀ x y, Commute (f x) (g y) := by
  intro x
  have hx : x ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    intro y
    have hy : y ∈ Subgroup.closure T := by rw [hT]; trivial
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => simp
    | mul y z hy hz iy iz => simpa only [map_mul] using iy.mul_right iz
    | inv y hy iy => simpa only [map_inv] using iy.inv_right
  | one => intro y; simp
  | mul x z hx hz ix iz => intro y; simpa only [map_mul] using (ix y).mul_left (iz y)
  | inv x hx ix => intro y; simpa only [map_inv] using (ix y).inv_left

lemma product_finitelyPresented [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  classical
  let : Group.FG G := fg_of_fp
  let : Group.FG H := fg_of_fp
  obtain ⟨S,hS,hs⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  obtain ⟨T,hT,ht⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let P := Monoid.Coprod G H
  let i : G →* P := Monoid.Coprod.inl
  let j : H →* P := Monoid.Coprod.inr
  let p : P →* G × H := Monoid.Coprod.lift (MonoidHom.inl G H) (MonoidHom.inr G H)
  have pi (g : G) : p (i g) = (g,1) := rfl
  have pj (h : H) : p (j h) = (1,h) := rfl
  let R : Set P := (fun z : G × H => i z.1 * j z.2 * (j z.2 * i z.1)⁻¹) '' (S ×ˢ T)
  have hR : R.Finite := (hs.prod ht).image _
  have hk : R ⊆ p.ker := by
    rintro _ ⟨⟨g,h⟩,⟨hg,hh⟩,rfl⟩
    change p (i g * j h * (j h * i g)⁻¹) = 1
    rw [map_mul,map_mul,map_inv,map_mul,pi,pj]
    ext <;> simp
  let Q := P ⧸ Subgroup.normalClosure R
  let q : P →* Q := QuotientGroup.mk' _
  let a := q.comp i
  let b := q.comp j
  have hc : ∀ g h, Commute (a g) (b h) := by
    apply commute_of_generators a b S T hS hT
    intro g hg h hh
    have hr : i g * j h * (j h * i g)⁻¹ ∈ Subgroup.normalClosure R :=
      Subgroup.subset_normalClosure ⟨(g,h),⟨hg,hh⟩,rfl⟩
    have he := (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure R) _).mpr hr
    change a g * b h = b h * a g
    change q (i g * j h * (j h * i g)⁻¹) = 1 at he
    rw [map_mul,map_mul,map_inv,map_mul] at he
    exact mul_inv_eq_one.mp he
  let s : G × H →* Q := a.noncommCoprod b hc
  let π := killProjection p R hk
  have hsec : π.comp s = MonoidHom.id (G × H) := by
    apply MonoidHom.ext
    intro z
    change p (i z.1 * j z.2) = z
    rw [map_mul,pi,pj]
    exact Prod.ext (mul_one _) (one_mul _)
  let : Group.IsFinitelyPresented Q := kill_finitelyPresented R hR
  exact finitelyPresented_retract π s hsec

lemma finite_pi_finitelyPresented {I : Type u} [Finite I] (K : I → Type v)
    [∀ i, Group (K i)] [∀ i, Group.IsFinitelyPresented (K i)] :
    Group.IsFinitelyPresented (∀ i, K i) := by
  classical
  let := Fintype.ofFinite I
  suffices h : ∀ n (K : Fin n → Type v) [∀ i, Group (K i)]
      [∀ i, Group.IsFinitelyPresented (K i)], Group.IsFinitelyPresented (∀ i, K i) by
    let e := Fintype.equivFin I
    let e' : (∀ i, K i) ≃* (∀ i, K (e.symm i)) :=
      { (Equiv.piCongrLeft K e.symm).symm with map_mul' := fun _ _ => rfl }
    let := h (Fintype.card I) (fun i => K (e.symm i))
    exact Group.IsFinitelyPresented.equiv e'.symm
  intro n
  induction n with
  | zero => intro K _ _; infer_instance
  | succ n ih =>
    intro K _ _
    let e : (∀ i, K i) ≃* K 0 × (∀ i : Fin n, K i.succ) :=
      { toFun f := (f 0,fun i => f i.succ)
        invFun p := Fin.cases p.1 p.2
        left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
        right_inv p := rfl
        map_mul' _ _ := rfl }
    let := ih (fun i => K i.succ)
    let := product_finitelyPresented (G := K 0) (H := ∀ i : Fin n, K i.succ)
    exact Group.IsFinitelyPresented.equiv e.symm
end ActionPresentation

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductGroupHomology
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.LocalEmbedding.instCoeFunForallBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
namespace ProductGroupHomology
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin

lemma continuous_get (n : ℕ) : Continuous (fun x : Cantor => x.get n) := continuous_apply n

end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma isOpen_brick (p : Prefix S) : IsOpen p.brick := by
  classical
  let : Finite {s : S // p s ≠ []} := p.finite_support.to_subtype
  let I := (s : {s : S // p s ≠ []}) × Fin (p s.1).length
  have he : p.brick = ⋂ j : I, {x | (x j.1.1).get j.2 = (p j.1.1)[j.2]} := by
    ext x
    simp only [mem_brick_iff_get,mem_iInter,mem_ofPred_eq]
    constructor
    · intro h j; exact h j.1.1 j.2 j.2.isLt
    · intro h s n hn
      have hs : p s ≠ [] := by intro he; simp [he] at hn
      exact h ⟨⟨s,hs⟩,⟨n,hn⟩⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_discrete {(p j.1.1)[j.2]}).preimage
    ((continuous_get (j.2.val)).comp (continuous_apply j.1.1))

end TwistedBrin.Prefix

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma finite_grid_refinement (I : Finset (Box S)) (p : Box S → Prefix S)
    (hc : ∀ x, ∃ i ∈ I, x ∈ (p i).brick) :
    ∃ b : S →₀ ℕ, ∀ z : Prefix.Grid b, ∃ i ∈ I,
      Prefix.Extends (p i) (Prefix.gridPrefix b z) := by
  classical
  let b : S →₀ ℕ := ∑ i ∈ I, (p i).lengths
  refine ⟨b,?_⟩
  intro z
  let x : Box S := (Prefix.gridPrefix b z).chart (fun _ _ => false)
  obtain ⟨i,hi,hix⟩ := hc x
  refine ⟨i,hi,Prefix.extends_of_mem_of_length_le hix (Prefix.chart_mem_brick _ _) ?_⟩
  intro s
  rw [Prefix.gridPrefix_length]
  change (p i).lengths s ≤ b s
  have hl : (p i).lengths ≤ ∑ j ∈ I, (p j).lengths :=
    Finset.single_le_sum (f := fun j => (p j).lengths) (fun _ _ s => Nat.zero_le _) hi
  exact hl s

end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderBasedComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderBasedComplex

variable {B : Type*} (C : Data B)

lemma d_vertex {b : B} (hb : C.degree b = 0) : C.d (Finsupp.single b 1) = 0 := by
  classical
  apply Finsupp.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have H := C.lowers b t ht
  omega

lemma linear_eq_on_support {M : Type*} [AddCommGroup M]
    (f g : (B →₀ ℤ) →ₗ[ℤ] M) (c : B →₀ ℤ)
    (h : ∀ b ∈ c.support, f (Finsupp.single b 1) = g (Finsupp.single b 1)) : f c = g c := by
  classical
  conv_lhs => rw [← Finsupp.sum_single c]
  conv_rhs => rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have he : Finsupp.single b (c b) = (c b) • Finsupp.single b 1 := by simp
  rw [he, LinearMap.map_smul, LinearMap.map_smul, h b hb]

end OrderBasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChains
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains

variable (G : Type*)

lemma degree_cone (a : G) (s : Simplex G) :
    degree G (simplexCone G a s) = degree G s + 1 := rfl

lemma boundary_vertices (s t : Simplex G)
    (ht : t ∈ (boundary G (Finsupp.single s 1)).support) :
    vertices G t ⊆ vertices G s := (boundary_faces G s t ht).2

lemma cone_mem_degreeModule {n : ℕ} (a : G) {c : Chain G}
    (hc : c ∈ degreeModule G n) : cone G a c ∈ degreeModule G (n+1) := by
  refine supported_cone G (Q := fun s => degree G s = n+1) a ?_ hc
  intro s hs
  rw [degree_cone, hs]

end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChains
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
lemma cone_carrier (x : P) {c : Chain P} (hc : c ∈ carrier P x) :
    cone P x c ∈ carrier P x := by
  refine supported_cone P (P := fun s => Descending P s ∧ ∀ v ∈ vertices P s, v ≤ x)
    (Q := fun s => Descending P s ∧ ∀ v ∈ vertices P s, v ≤ x) x ?_ hc
  intro s hs
  constructor
  · change (x :: list P s).Pairwise _
    rw [List.pairwise_cons]
    exact ⟨fun v hv => hs.2 v ((mem_list P s v).mp hv),hs.1⟩
  · rw [vertices_cone]
    intro v hv
    rcases hv with rfl | hv
    · exact le_rfl
    · exact hs.2 v hv
end

open OrderListChains
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactInOfTop
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace OrderBasedComplex
section
variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (point : B → M) (fill : B → ℕ → M → M)

lemma chosen_vertex {b : B} (hb : C.degree b = 0) :
    chosenExtend C point fill (Finsupp.single b 1) = point b := by
  simp only [chosenExtend,Finsupp.linearCombination_single,one_smul]
  rw [chosenBasis,ite_eq_left hb]
lemma chosen_positive {b : B} (hb : C.degree b ≠ 0) :
    chosenExtend C point fill (Finsupp.single b 1) =
      fill b (C.degree b-1) (chosenExtend C point fill (C.d (Finsupp.single b 1))) := by
  simp only [chosenExtend,Finsupp.linearCombination_single,one_smul]
  rw [chosenBasis,ite_eq_right hb]
  congr 1
  simp only [Finsupp.linearCombination_apply,Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => C.d (Finsupp.single b 1) t • chosenBasis C point fill t)

variable (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ)
  (D : ℕ → Submodule ℤ M) (P : B → Prop) (K : B → Submodule ℤ M) (N : ℕ)
  (hP : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → P t)
  (hface : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
  (hpoint : ∀ b, P b → point b ∈ K b ∧ point b ∈ D 0 ∧ d (point b) = 0 ∧ aug (point b) = 1)
  (hfill : ∀ b, P b → ∀ n ≤ N, ∀ z : M, z ∈ K b → z ∈ D n → d z = 0 → aug z = 0 →
    fill b n z ∈ K b ∧ fill b n z ∈ D (n+1) ∧ d (fill b n z) = z ∧ aug (fill b n z) = 0)

include hP hface hpoint hfill in
lemma chosen_spec (b : B) (hb : P b) (hbn : C.degree b ≤ N+1) :
    chosenExtend C point fill (Finsupp.single b 1) ∈ K b ∧
    chosenExtend C point fill (Finsupp.single b 1) ∈ D (C.degree b) ∧
    d (chosenExtend C point fill (Finsupp.single b 1)) =
      chosenExtend C point fill (C.d (Finsupp.single b 1)) ∧
    aug (chosenExtend C point fill (Finsupp.single b 1)) = C.aug (Finsupp.single b 1) := by
  suffices ∀ m b, C.degree b = m → P b → m ≤ N+1 →
      chosenExtend C point fill (Finsupp.single b 1) ∈ K b ∧
      chosenExtend C point fill (Finsupp.single b 1) ∈ D (C.degree b) ∧
      d (chosenExtend C point fill (Finsupp.single b 1)) =
        chosenExtend C point fill (C.d (Finsupp.single b 1)) ∧
      aug (chosenExtend C point fill (Finsupp.single b 1)) = C.aug (Finsupp.single b 1) by
    exact this _ b rfl hb hbn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro b hm hb hbn
    by_cases hz : C.degree b = 0
    · rw [chosen_vertex C point fill hz,hz,d_vertex C hz,map_zero,C.aug_single,ite_eq_left hz]
      exact hpoint b hb
    · have hs (t : B) (ht : t ∈ (C.d (Finsupp.single b 1)).support) :=
        ih (C.degree t) (by have hh := C.lowers b t ht; omega) t rfl
          (hP b t hb ht) (by have hh := C.lowers b t ht; omega)
      let z := chosenExtend C point fill (C.d (Finsupp.single b 1))
      have hzK : z ∈ K b := by
        apply map_mem_of_support
        intro t ht
        exact hface b t hb ht (hs t ht).1
      have hzD : z ∈ D (C.degree b-1) := by
        apply map_mem_of_support
        intro t ht
        have hh := C.lowers b t ht
        have he : C.degree b - 1 = C.degree t := by omega
        rw [he]
        exact (hs t ht).2.1
      have hzd : d z = 0 := by
        have he := linear_eq_on_support (d.comp (chosenExtend C point fill))
          ((chosenExtend C point fill).comp C.d) (C.d (Finsupp.single b 1))
          (fun t ht => (hs t ht).2.2.1)
        change d z = _ at he
        simpa only [LinearMap.comp_apply,C.d_squared,map_zero] using he
      have hza : aug z = 0 := by
        have he := linear_eq_on_support (aug.comp (chosenExtend C point fill)) C.aug
          (C.d (Finsupp.single b 1)) (fun t ht => (hs t ht).2.2.2)
        change aug z = _ at he
        simpa only [C.aug_d] using he
      obtain ⟨hK,hD,hd,ha⟩ := hfill b hb (C.degree b-1) (by omega) z hzK hzD hzd hza
      rw [chosen_positive C point fill hz]
      refine ⟨hK,?_,hd,?_⟩
      · have he : C.degree b - 1 + 1 = C.degree b := by omega
        simpa only [he] using hD
      · rw [C.aug_single,ite_eq_right hz]
        exact ha

end

variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (fill : B → ℕ → M → M) (F G : (B →₀ ℤ) →ₗ[ℤ] M)

lemma chosenHomotopy_equation (b : B) :
    chosenHomotopy C fill F G (Finsupp.single b 1) =
      fill b (C.degree b) (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
        chosenHomotopy C fill F G (C.d (Finsupp.single b 1))) := by
  simp only [chosenHomotopy,Finsupp.linearCombination_single,one_smul]
  rw [chosenHomotopyBasis]
  congr 2
  simp only [Finsupp.linearCombination_apply,Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => C.d (Finsupp.single b 1) t • chosenHomotopyBasis C fill F G t)

variable (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ)
  (D : ℕ → Submodule ℤ M) (P : B → Prop) (K : B → Submodule ℤ M) (N : ℕ)
  (hP : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → P t)
  (hface : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
  (hF : ∀ b, P b → C.degree b ≤ N → F (Finsupp.single b 1) ∈ K b ∧
    F (Finsupp.single b 1) ∈ D (C.degree b) ∧ d (F (Finsupp.single b 1)) = F (C.d (Finsupp.single b 1)) ∧
    aug (F (Finsupp.single b 1)) = C.aug (Finsupp.single b 1))
  (hG : ∀ b, P b → C.degree b ≤ N → G (Finsupp.single b 1) ∈ K b ∧
    G (Finsupp.single b 1) ∈ D (C.degree b) ∧ d (G (Finsupp.single b 1)) = G (C.d (Finsupp.single b 1)) ∧
    aug (G (Finsupp.single b 1)) = C.aug (Finsupp.single b 1))
  (hfill : ∀ b, P b → ∀ n ≤ N, ∀ z : M, z ∈ K b → z ∈ D n → d z = 0 → aug z = 0 →
    fill b n z ∈ K b ∧ fill b n z ∈ D (n+1) ∧ d (fill b n z) = z ∧ aug (fill b n z) = 0)

include hP hface hF hG hfill in
lemma chosenHomotopy_spec (b : B) (hb : P b) (hbn : C.degree b ≤ N) :
    chosenHomotopy C fill F G (Finsupp.single b 1) ∈ K b ∧
    chosenHomotopy C fill F G (Finsupp.single b 1) ∈ D (C.degree b+1) ∧
    d (chosenHomotopy C fill F G (Finsupp.single b 1)) +
      chosenHomotopy C fill F G (C.d (Finsupp.single b 1)) =
      F (Finsupp.single b 1) - G (Finsupp.single b 1) ∧
    aug (chosenHomotopy C fill F G (Finsupp.single b 1)) = 0 := by
  suffices ∀ m b, C.degree b = m → P b → m ≤ N →
      chosenHomotopy C fill F G (Finsupp.single b 1) ∈ K b ∧
      chosenHomotopy C fill F G (Finsupp.single b 1) ∈ D (C.degree b+1) ∧
      d (chosenHomotopy C fill F G (Finsupp.single b 1)) +
        chosenHomotopy C fill F G (C.d (Finsupp.single b 1)) =
        F (Finsupp.single b 1) - G (Finsupp.single b 1) ∧
      aug (chosenHomotopy C fill F G (Finsupp.single b 1)) = 0 by
    exact this _ b rfl hb hbn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro b hm hb hbn
    have hbn' : C.degree b ≤ N := by omega
    have hfs := hF b hb hbn'
    have hgs := hG b hb hbn'
    have hs (t : B) (ht : t ∈ (C.d (Finsupp.single b 1)).support) :=
      ih (C.degree t) (by have hh := C.lowers b t ht; omega) t rfl
        (hP b t hb ht) (by have hh := C.lowers b t ht; omega)
    let H := chosenHomotopy C fill F G
    let z := F (Finsupp.single b 1) - G (Finsupp.single b 1) - H (C.d (Finsupp.single b 1))
    have hzK : z ∈ K b := by
      apply (K b).sub_mem ((K b).sub_mem hfs.1 hgs.1)
      apply map_mem_of_support
      intro t ht
      exact hface b t hb ht (hs t ht).1
    have hzD : z ∈ D (C.degree b) := by
      apply (D _).sub_mem ((D _).sub_mem hfs.2.1 hgs.2.1)
      apply map_mem_of_support
      intro t ht
      rw [← C.lowers b t ht]
      exact (hs t ht).2.1
    have hzd : d z = 0 := by
      have he := linear_eq_on_support (d.comp H) (F-G-H.comp C.d)
        (C.d (Finsupp.single b 1)) (fun t ht => by
          have hh := (hs t ht).2.2.1
          change d (H (Finsupp.single t 1)) = _
          simpa only [LinearMap.sub_apply,LinearMap.comp_apply] using eq_sub_of_add_eq hh)
      simp only [LinearMap.sub_apply,LinearMap.comp_apply,C.d_squared,map_zero,sub_zero] at he
      dsimp only [z]
      rw [map_sub,map_sub,hfs.2.2.1,hgs.2.2.1,he,sub_self]
    have hza : aug z = 0 := by
      have he := linear_eq_on_support (aug.comp H) 0 (C.d (Finsupp.single b 1))
        (fun t ht => (hs t ht).2.2.2)
      dsimp only [z]
      rw [map_sub,map_sub,hfs.2.2.2,hgs.2.2.2,sub_self]
      change 0 - (aug.comp H) (C.d (Finsupp.single b 1)) = 0
      rw [he,LinearMap.zero_apply,sub_zero]
    obtain ⟨hK,hD,hd,ha⟩ := hfill b hb (C.degree b) hbn' z hzK hzD hzd hza
    rw [chosenHomotopy_equation]
    refine ⟨hK,hD,?_,ha⟩
    rw [hd]
    dsimp only [z,H]
    abel
end OrderBasedComplex

namespace OrderListChains
variable (P : Type*)
lemma augmentation_of_positive {n : ℕ} (hn : 0 < n) {c : Chain P}
    (hc : Homogeneous P n c) : augmentation P c = 0 := by
  have he := OrderBasedComplex.linear_eq_on_support (augmentation P) 0 c (fun s hs => by
    rw [augmentation_single,ite_eq_right,LinearMap.zero_apply]
    intro h
    have hh := hc s hs
    simp only [degree,h,List.length_nil] at hh
    omega)
  exact he
end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsOnSet
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
lemma onSet_mono {U V : Set P} (h : U ⊆ V) : onSet P U ≤ onSet P V :=
  fun _ hc _ hs => ⟨(hc hs).1, fun _ hx => h ((hc hs).2 hx)⟩
lemma onSet_le_module (U : Set P) : onSet P U ≤ module P :=
  fun _ hc _ hs => (hc hs).1
lemma project_val (P : Type*) [Preorder P] {U : Set P} (u : U) {x : P} (hx : x ∈ U) :
    (project P U u x).val = x := by
  classical
  simp [project,hx]
lemma project_include {U : Set P} (u v : U) : project P U u v = v := by
  apply Subtype.ext
  exact project_val P u v.property

lemma cone_onSet_top {U : Set P} (u : P) (hu : u ∈ U) (ht : ∀ x ∈ U, x ≤ u)
    {c : Chain P} (hc : c ∈ onSet P U) : cone P u c ∈ onSet P U := by
  change Supported P (fun s => Descending P s ∧ vertices P s ⊆ U) (cone P u c)
  refine supported_cone P (P := fun s => Descending P s ∧ vertices P s ⊆ U) u ?_ hc
  intro s hs
  constructor
  · change (u :: list P s).Pairwise _
    rw [List.pairwise_cons]
    exact ⟨fun x hx => ht x (hs.2 ((mem_list P s x).mp hx)),hs.1⟩
  · rw [vertices_cone]
    exact Set.insert_subset hu hs.2
lemma exactSet_of_top {U : Set P} (u : P) (hu : u ∈ U) (ht : ∀ x ∈ U, x ≤ u)
    (n : ℕ) : ExactSet P U n := by
  intro c hc hn hd ha
  refine ⟨cone P u c,cone_onSet_top P u hu ht hc,cone_mem_degreeModule P _ hn,?_⟩
  rw [boundary_cone,hd,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]

lemma cycleFill_spec {U : Set P} {n : ℕ} (hU : ExactSet P U n) {c : Chain P}
    (hc : c ∈ onSet P U) (hn : Homogeneous P n c) (hd : boundary P c = 0)
    (ha : augmentation P c = 0) :
    cycleFill P U n c ∈ onSet P U ∧ Homogeneous P (n+1) (cycleFill P U n c) ∧
    boundary P (cycleFill P U n c) = c ∧ augmentation P (cycleFill P U n c) = 0 := by
  have he := hU c hc hn hd ha
  classical
  simp only [cycleFill,dite_eq_left he]
  exact ⟨(Classical.choose_spec he).1,(Classical.choose_spec he).2.1,
    (Classical.choose_spec he).2.2,augmentation_of_positive P (n := n+1) (by omega) (Classical.choose_spec he).2.1⟩

end

open OrderListChains
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsVertexSupport
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
variable (P : Type*)
lemma mem_vertexSupport {c : Chain P} {x : P} : x ∈ vertexSupport P c ↔
    ∃ s ∈ c.support, x ∈ vertices P s := by
  classical
  simp only [vertexSupport,Finset.mem_biUnion,List.mem_toFinset,mem_list]
end OrderListChains

namespace OrderChains

section
open OrderListChains
variable (P : Type*) [Preorder P]
theorem carrier_fill (U V : Set P) (K L : Simplex P → Set P) (N : ℕ)
    (hKne : ∀ s, Descending P s → vertices P s ⊆ U → (K s).Nonempty)
    (hKV : ∀ s, Descending P s → vertices P s ⊆ U → K s ⊆ V)
    (hLU : ∀ s, Descending P s → vertices P s ⊆ U → L s ⊆ U)
    (hKL : ∀ s, Descending P s → vertices P s ⊆ U → K s ⊆ L s)
    (hself : ∀ s, Descending P s → vertices P s ⊆ U → vertices P s ⊆ L s)
    (hfaceK : ∀ s t, Descending P s → vertices P s ⊆ U →
      t ∈ (boundary P (Finsupp.single s 1)).support → K t ⊆ K s)
    (hfaceL : ∀ s t, Descending P s → vertices P s ⊆ U →
      t ∈ (boundary P (Finsupp.single s 1)).support → L t ⊆ L s)
    (hKexact : ∀ s, Descending P s → vertices P s ⊆ U → ∀ k ≤ N, ExactSet P (K s) k)
    (hLexact : ∀ s, Descending P s → vertices P s ⊆ U → ∀ k ≤ N, ExactSet P (L s) k)
    (hVU : V ⊆ U)
    (hLV : ∀ s, Descending P s → vertices P s ⊆ V → L s ⊆ V)
    {n : ℕ} (hnN : n ≤ N) (c b : Chain P)
    (hcV : c ∈ onSet P V) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0)
    (hb : b ∈ onSet P U) (hbn : Homogeneous P (n+1) b) (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P V ∧ Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  classical
  have _ := hLU
  have _ := ha
  have hc : c ∈ onSet P U := onSet_mono P hVU hcV
  let valid : Simplex P → Prop := fun s => Descending P s ∧ vertices P s ⊆ U
  let p : Simplex P → P := fun s => if h : valid s then (hKne s h.1 h.2).choose else s.1
  let point : Simplex P → Chain P := fun s => vertex P (p s)
  let fill := fun s k z => cycleFill P (K s) k z
  let F := OrderBasedComplex.chosenExtend (based P) point fill
  have hvalid : ∀ s t, valid s → t ∈ (boundary P (Finsupp.single s 1)).support → valid t := by
    intro s t hs ht
    exact ⟨hs.1.boundary P ht,(boundary_vertices P s t ht).trans hs.2⟩
  have hpoint (s : Simplex P) (hs : valid s) : point s ∈ onSet P (K s) ∧
      point s ∈ degreeModule P 0 ∧ boundary P (point s) = 0 ∧ augmentation P (point s) = 1 := by
    have hp : p s ∈ K s := by
      dsimp only [p]
      rw [dite_eq_left hs]
      exact (hKne s hs.1 hs.2).choose_spec
    refine ⟨?_,?_,boundary_vertex P _,augmentation_vertex P _⟩
    · apply supported_single
      exact ⟨List.pairwise_singleton _ _,by rw [vertices_vertex]; exact Set.singleton_subset_iff.mpr hp⟩
    · change Homogeneous P 0 (Finsupp.single (simplexVertex P (p s)) 1)
      exact supported_single P (P := fun t => degree P t = 0) rfl 1
  have hfill (s : Simplex P) (hs : valid s) (k : ℕ) (hk : k ≤ N) (z : Chain P)
      (hz : z ∈ onSet P (K s)) (hzdeg : z ∈ degreeModule P k)
      (hzd : boundary P z = 0) (hza : augmentation P z = 0) :=
    cycleFill_spec P (hKexact s hs.1 hs.2 k hk) hz hzdeg hzd hza
  have hF (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N+1) :
      F (Finsupp.single s 1) ∈ onSet P (K s) ∧
      F (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P (F (Finsupp.single s 1)) = F (boundary P (Finsupp.single s 1)) ∧
      augmentation P (F (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact OrderBasedComplex.chosen_spec (based P) point fill (boundary P) (augmentation P)
      (degreeModule P) valid (fun s => onSet P (K s)) N hvalid
      (fun s t hs ht => onSet_mono P (hfaceK s t hs.1 hs.2 ht)) hpoint hfill s hs hdeg
  let fillL := fun s k z => cycleFill P (L s) k z
  let H := OrderBasedComplex.chosenHomotopy (based P) fillL LinearMap.id F
  have hI (s : Simplex P) (hs : valid s) (_ : degree P s ≤ N) :
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ onSet P (L s) ∧
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) = (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (boundary P (Finsupp.single s 1)) ∧
      augmentation P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact ⟨supported_single P ⟨hs.1,hself s hs.1 hs.2⟩ 1,
      supported_single P (P := fun t => degree P t = degree P s) rfl 1,rfl,rfl⟩
  have hFL (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N) :=
    hF s hs (by omega)
  have hH (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N) :
      H (Finsupp.single s 1) ∈ onSet P (L s) ∧
      H (Finsupp.single s 1) ∈ degreeModule P (degree P s+1) ∧
      boundary P (H (Finsupp.single s 1)) + H (boundary P (Finsupp.single s 1)) =
        Finsupp.single s 1 - F (Finsupp.single s 1) ∧
      augmentation P (H (Finsupp.single s 1)) = 0 := by
    apply OrderBasedComplex.chosenHomotopy_spec (based P) fillL LinearMap.id F (boundary P)
      (augmentation P) (degreeModule P) valid (fun s => onSet P (L s)) N hvalid
      (fun s t hs ht => onSet_mono P (hfaceL s t hs.1 hs.2 ht)) hI ?_ ?_ s hs hdeg
    · intro t ht htd
      exact ⟨onSet_mono P (hKL t ht.1 ht.2) (hFL t ht htd).1,(hFL t ht htd).2⟩
    · intro t ht k hk z hz hzdeg hzd hza
      exact cycleFill_spec P (hLexact t ht.1 ht.2 k hk) hz hzdeg hzd hza
  have hsd (s : Simplex P) (hs : s ∈ c.support) : degree P s ≤ N := (hn s hs).le.trans hnN
  have hbdg (s : Simplex P) (hs : s ∈ b.support) : degree P s ≤ N+1 := by rw [hbn s hs]; omega
  refine ⟨F b + H c, (onSet P V).add_mem ?_ ?_, supported_add P ?_ ?_, ?_⟩
  · apply OrderBasedComplex.map_mem_of_support
    intro t ht
    exact onSet_mono P (hKV t (hb ht).1 (hb ht).2) (hF t (hb ht) (hbdg t ht)).1
  · apply OrderBasedComplex.map_mem_of_support
    intro t ht
    exact onSet_mono P (hLV t (hcV ht).1 (hcV ht).2) (hH t (hc ht) (hsd t ht)).1
  · apply OrderBasedComplex.map_mem_of_support F (degreeModule P (n+1))
    intro t ht
    rw [← hbn t ht]
    exact (hF t (hb ht) (hbdg t ht)).2.1
  · apply OrderBasedComplex.map_mem_of_support H (degreeModule P (n+1))
    intro t ht
    rw [← hn t ht]
    exact (hH t (hc ht) (hsd t ht)).2.1
  · have hFb := OrderBasedComplex.linear_eq_on_support ((boundary P).comp F) (F.comp (boundary P)) b
      (fun t ht => (hF t (hb ht) (hbdg t ht)).2.2.1)
    have hHc := OrderBasedComplex.linear_eq_on_support ((boundary P).comp H+H.comp (boundary P))
      (LinearMap.id-F) c (fun t ht => (hH t (hc ht) (hsd t ht)).2.2.1)
    simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
      hd,map_zero,add_zero] at hHc
    simp only [LinearMap.comp_apply,hbd] at hFb
    rw [map_add,hFb,hHc]
    abel
end

open OrderListChains
variable (P : Type*) [PartialOrder P]

lemma lowerCarrier_face (r : P → ℕ) (hr : StrictMono r) (h : ℕ)
    {s t : Simplex P} (hs : Descending P s)
    (hsU : vertices P s ⊆ {x | r x ≤ h+1})
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    lowerCarrier P r h t ⊆ lowerCarrier P r h s := by
  classical
  have hv := boundary_vertices P s t ht
  have hts := hs.le_head P (hv (head_mem_vertices P t))
  have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
  have htr := hr.monotone hts
  have hdt := hs.boundary P ht
  unfold lowerCarrier
  split_ifs with hT hS hS
  · have he : t.1 = s.1 := by
      apply le_antisymm hts
      by_contra hn
      have hh := hr (lt_of_le_not_ge hts hn)
      omega
    simpa only [he] using (Set.Subset.rfl : Set.Iio s.1 ⊆ Set.Iio s.1)
  · omega
  · intro x hx
    have hxt := hdt.le_head P hx
    apply lt_of_le_of_ne (hxt.trans hts)
    intro he
    have hh := hr.monotone hxt
    rw [he] at hh
    omega
  · exact hv

lemma lowerStar_face (r : P → ℕ) (hr : StrictMono r) (h : ℕ)
    {s t : Simplex P} (hs : Descending P s)
    (hsU : vertices P s ⊆ {x | r x ≤ h+1})
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    lowerStar P r h t ⊆ lowerStar P r h s := by
  classical
  have hv := boundary_vertices P s t ht
  have hts := hs.le_head P (hv (head_mem_vertices P t))
  have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
  have htr := hr.monotone hts
  unfold lowerStar
  split_ifs with hT hS hS
  · exact fun _ hx => hx.trans hts
  · omega
  · exact fun _ hx => hs.le_head P (hv hx)
  · exact hv

theorem lower_filling (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, r a = h+1 → ∃ x, x < a)
    (hex : ∀ a, r a = h+1 → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (c b : Chain P)
    (hc : c ∈ onSet P {x | r x ≤ h}) (hcn : Homogeneous P n c)
    (hcd : boundary P c = 0) (hca : augmentation P c = 0)
    (hb : b ∈ onSet P {x | r x ≤ h+1}) (hbn : Homogeneous P (n+1) b)
    (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P {x | r x ≤ h} ∧
      Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  classical
  apply carrier_fill P {x | r x ≤ h+1} {x | r x ≤ h}
    (lowerCarrier P r h) (lowerStar P r h) N
    ?_ ?_ ?_ ?_ ?_ (fun _ _ hs hsU ht => lowerCarrier_face P r hr h hs hsU ht)
    (fun _ _ hs hsU ht => lowerStar_face P r hr h hs hsU ht) ?_ ?_ ?_ ?_
    hnN c b hc hcn hcd hca hb hbn hbd
  · intro s _ _
    unfold lowerCarrier
    split_ifs with he
    · exact hne s.1 he
    · exact ⟨s.1,head_mem_vertices P s⟩
  · intro s hs hsU x hx
    have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
    unfold lowerCarrier at hx
    split_ifs at hx with he
    · have hh := hr hx
      change r x ≤ h
      omega
    · have hh := hr.monotone (hs.le_head P hx)
      change r x ≤ h
      omega
  · intro s hs hsU x hx
    unfold lowerStar at hx
    split_ifs at hx with he
    · have hh := hr.monotone hx
      change r x ≤ h+1
      omega
    · exact hsU hx
  · intro s _ _ x hx
    unfold lowerCarrier lowerStar at *
    split_ifs at *
    · exact hx.le
    · exact hx
  · intro s hs _
    unfold lowerStar
    split_ifs
    · exact fun _ hx => hs.le_head P hx
    · exact Set.Subset.rfl
  · intro s hs _ k hk
    unfold lowerCarrier
    split_ifs with he
    · exact hex s.1 he k hk
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
  · intro s hs _ k _
    unfold lowerStar
    split_ifs
    · exact exactSet_of_top P (U := Set.Iic s.1) s.1 le_rfl (fun _ hx => hx) k
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
  · intro x hx
    change r x ≤ h+1
    change r x ≤ h at hx
    omega
  · intro s _ hsV
    have hsr := hsV (head_mem_vertices P s)
    have he : r s.1 ≠ h+1 := by change r s.1 ≤ h at hsr; omega
    simpa only [lowerStar,ite_eq_right he] using hsV
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinRangeChartRestricts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma mem_ofPartition {I : Type*} [Fintype I] (p : I → Prefix S)
    (hp : IsPartition p) (i : I) :
    GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ (p i)) ∈ (ofPartition ρ p hp).pieces := by
  classical
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

end Basis
end TwistedBrin

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace Basis

lemma transition_germBrick {B C : Basis ρ} (e : B ≃ C) (b : B) :
    GermBrick.groupEquiv ρ (transitionElement ρ e) b.1 = (e b).1 := by
  rw [← GermBrick.mk_representative ρ b.1,← GermBrick.mk_representative ρ (e b).1]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ _ _) = GermBrick.mk ρ _
  congr 1
  apply LocalEmbedding.ext
  exact transition_chart ρ e b

lemma translate_transition {B C : Basis ρ} (e : B ≃ C) :
    translate ρ (transitionElement ρ e) B = C := by
  classical
  apply Basis.ext
  apply Finset.ext
  intro b
  change b ∈ B.pieces.map (GermBrick.groupEquiv ρ (transitionElement ρ e)).toEmbedding ↔ _
  constructor
  · intro hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb
    change GermBrick.groupEquiv ρ (transitionElement ρ e) a ∈ C.pieces
    rw [transition_germBrick ρ e ⟨a,ha⟩]
    exact (e ⟨a,ha⟩).property
  · intro hb
    obtain ⟨a,ha⟩ := e.surjective ⟨b,hb⟩
    exact Finset.mem_map.mpr ⟨a.1,a.property,(transition_germBrick ρ e a).trans (congrArg Subtype.val ha)⟩

lemma orbit_of_rank_eq {B C : Basis ρ} (hr : rank ρ B = rank ρ C) :
    ∃ g : localGroup ρ, g • B = C := by
  have hc : Fintype.card B = Fintype.card C := by simpa only [rank_eq_card] using hr
  let e := Classical.choice (Fintype.card_eq.mp hc)
  exact ⟨transitionElement ρ e,translate_transition ρ e⟩

end Basis
end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasis
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma rank_expand (B : Basis ρ) (P : B → Pattern S) :
    rank ρ (expand ρ B P) = ∑ b : B, Fintype.card (Pattern.Leaves (P b)) := by
  rw [expand,rank_ofChartPartition,Fintype.card_sigma]

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPrefix
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma rectangular_length (b : S →₀ ℕ) (i : Leaves (rectangular b)) (s : S) :
    (leafPrefix (rectangular b) i s).length = b s := by
  classical
  have h := uniform_length (Finsupp.toMultiset b).toList i s
  rw [← Multiset.coe_count,Multiset.coe_toList,Finsupp.count_toMultiset] at h
  exact h

end TwistedBrin.Pattern

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma eq_of_mem_of_length_eq {p q : Prefix S} {x : Box S}
    (hp : x ∈ p.brick) (hq : x ∈ q.brick) (hl : ∀ s, (p s).length = (q s).length) : p = q := by
  apply Prefix.ext
  intro s
  rw [← (mem_brick_iff p x).mp hp s,← (mem_brick_iff q x).mp hq s,hl]

lemma eq_gridPrefix_of_lengths {p : Prefix S} {b : S →₀ ℕ} (hl : ∀ s, (p s).length = b s)
    {x : Box S} (hx : x ∈ p.brick) : p = gridPrefix b (gridPoint b x) :=
  eq_of_mem_of_length_eq hx (mem_gridPrefix b x) (fun s => (hl s).trans (gridPrefix_length _ _ _).symm)

end TwistedBrin.Prefix

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma rectangular_prefix (b : S →₀ ℕ) (i : Leaves (rectangular b)) :
    ∃ z : Prefix.Grid b, leafPrefix (rectangular b) i = Prefix.gridPrefix b z :=
  ⟨_,Prefix.eq_gridPrefix_of_lengths (rectangular_length b i)
    (Prefix.chart_mem_brick _ (fun _ _ => false))⟩

end TwistedBrin.Pattern

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

lemma rectangular_standard (h : LocalEmbedding ρ) :
    ∃ w : S →₀ ℕ, ∀ i : Pattern.Leaves (Pattern.rectangular w),
      ∃ (q : Prefix S) (a : A),
        comp ρ h (ofPrefix ρ (Pattern.leafPrefix (Pattern.rectangular w) i)) =
          comp ρ (ofPrefix ρ q) (global ρ a) := by
  classical
  choose p q a hp he using h.locally_standard
  have hcover : (Set.univ : Set (Box S)) ⊆ ⋃ x, (p x).brick := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hp x⟩
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (p x).brick) (fun x => (p x).isOpen_brick) hcover
  have hc : ∀ x, ∃ i ∈ I, x ∈ (p i).brick := by
    intro x
    simpa only [Set.mem_iUnion,exists_prop] using hI (Set.mem_univ x)
  obtain ⟨w,hw⟩ := finite_grid_refinement I p hc
  refine ⟨w,?_⟩
  intro j
  obtain ⟨z,hz⟩ := Pattern.rectangular_prefix w j
  obtain ⟨x,_,hx⟩ := hw z
  refine ⟨(q x).append (((p x).suffix (Prefix.gridPrefix w z)).permute (ρ (a x))),a x,?_⟩
  apply LocalEmbedding.ext
  intro y
  change h ((Pattern.leafPrefix (Pattern.rectangular w) j).chart y) = _
  rw [hz]
  nth_rw 1 [← Prefix.append_suffix hx]
  change h (((p x).append ((p x).suffix (Prefix.gridPrefix w z))).chart y) =
    ((q x).append (((p x).suffix (Prefix.gridPrefix w z)).permute (ρ (a x)))).chart
      (twist ρ (a x) y)
  have he' (x y) : h ((p x).chart y) = (q x).chart (twist ρ (a x) y) := he x y
  rw [Prefix.chart_append,he',twist_chart,← Prefix.chart_append]

end LocalEmbedding
namespace Basis

lemma exists_standard_cut_patterns (B : Basis ρ) :
    ∃ P : B → Pattern S, ∀ i : Σ b : B, Pattern.Leaves (P b),
      ∃ (q : Prefix S) (a : A), expandedChart ρ B P i =
        LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ q) (LocalEmbedding.global ρ a) := by
  choose w hw using fun b : B => LocalEmbedding.rectangular_standard ρ (chart ρ B b)
  exact ⟨fun b => Pattern.rectangular (w b),fun i => hw i.1 i.2⟩

lemma cutRefines_grid_from_patterns (B : Basis ρ) (P : B → Pattern S)
    (q : (Σ b : B, Pattern.Leaves (P b)) → Prefix S)
    (a : (Σ b : B, Pattern.Leaves (P b)) → A)
    (he : ∀ i, expandedChart ρ B P i =
      LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ (q i)) (LocalEmbedding.global ρ (a i)))
    (w : S →₀ ℕ) (hw : ∀ i, (q i).lengths ≤ w) : CutRefines ρ B (grid ρ w) := by
  classical
  let R := fun i : Σ b : B, Pattern.Leaves (P b) =>
    Pattern.rectangular (w - (q i).lengths)
  let Q := fun b : B => Pattern.graft (P b)
    (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))
  apply Nonempty.intro
  apply Forest.of_mem ρ Q
  rintro ⟨b,k⟩
  obtain ⟨⟨j,l⟩,rfl⟩ := (Pattern.graftLeaves (P b)
    (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))).surjective k
  obtain ⟨l,rfl⟩ := (Pattern.relabelLeaves (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩)).surjective l
  let i : Σ b : B, Pattern.Leaves (P b) := ⟨b,j⟩
  let r := Pattern.leafPrefix (R i) l
  have hlen : ∀ s, ((q i).append r s).length = w s := by
    intro s
    change ((q i s) ++ (Pattern.leafPrefix (Pattern.rectangular (w - (q i).lengths)) l s)).length = w s
    rw [List.length_append,Pattern.rectangular_length,Finsupp.tsub_apply]
    exact Nat.add_sub_of_le (hw i s)
  obtain ⟨z,hz⟩ : ∃ z : Prefix.Grid w, (q i).append r = Prefix.gridPrefix w z :=
    ⟨_,Prefix.eq_gridPrefix_of_lengths hlen (Prefix.chart_mem_brick _ (fun _ _ => false))⟩
  have hc : GermBrick.mk ρ (expandedChart ρ B Q
      ⟨b,Pattern.graftLeaves (P b)
        (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))
        ⟨j,Pattern.relabelLeaves (ρ (a i)⁻¹) (R i) l⟩⟩) =
      GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ ((q i).append r)) := by
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ _))) = _
    rw [Pattern.graft_prefix,Pattern.relabel_prefix,LocalEmbedding.ofPrefix_append,
      ← LocalEmbedding.comp_assoc]
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (expandedChart ρ B P i)
      (LocalEmbedding.ofPrefix ρ (r.permute (ρ (a i)⁻¹)))) = _
    rw [he,LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix,twist_prefix_inv,
      ← LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,GermBrick.mk_gauge]
  rw [hc,hz]
  exact mem_ofPartition ρ _ _ z

end Basis
end TwistedBrin

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma cut_grid_cofinal (B : Basis ρ) :
    ∃ w : S →₀ ℕ, ∀ t, w ≤ t → CutRefines ρ B (grid ρ t) := by
  classical
  obtain ⟨P,hP⟩ := exists_standard_cut_patterns ρ B
  choose q a he using hP
  let w := ∑ i : Σ b : B, Pattern.Leaves (P b), (q i).lengths
  refine ⟨w,fun t ht => cutRefines_grid_from_patterns ρ B P q a he t ?_⟩
  intro i
  exact le_trans (Finset.single_le_sum (f := fun i => (q i).lengths)
    (fun _ _ s => Nat.zero_le _) (Finset.mem_univ i)) ht

theorem cut_directed (B C : Basis ρ) :
    ∃ D : Basis ρ, CutRefines ρ B D ∧ CutRefines ρ C D := by
  obtain ⟨b,hb⟩ := cut_grid_cofinal ρ B
  obtain ⟨c,hc⟩ := cut_grid_cofinal ρ C
  exact ⟨grid ρ (b+c),hb _ (fun s => Nat.le_add_right _ _),
    hc _ (fun s => Nat.le_add_left _ _)⟩

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisTranslateEquiv
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

namespace Merge
variable {ρ} {C : Basis ρ}

lemma rank_lower (m : Merge ρ C) : rank ρ m.lower + 1 = rank ρ C := by
  classical
  rw [lower,rank_ofChartPartition,rank_eq_card]
  have hc := Fintype.card_congr m.leafEquiv
  simp only [Fintype.card_sum,Fintype.card_bool] at hc
  change Fintype.card (Option m.Rest) + 1 = Fintype.card C
  rw [Fintype.card_option]
  omega

lemma lower_cutRefines (m : Merge ρ C) : CutRefines ρ m.lower C := by
  classical
  let P : m.Roots → Pattern S := fun r => match r with
    | none => .split m.coordinate .leaf .leaf
    | some _ => .leaf
  apply cutRefines_ofChartPartition ρ m.rootChart m.rootPartition C P
  intro r j
  cases r with
  | none =>
    cases j with
    | inl j =>
      simp [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,m.left_eq]
    | inr j =>
      simp [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,m.right_eq]
  | some r =>
    simp [P,Pattern.leafPrefix,rootChart,LocalEmbedding.ofPrefix_empty,
      LocalEmbedding.comp_identity,chart_germ]

lemma lower_ne (m : Merge ρ C) : m.lower ≠ C := by
  intro he
  have hr := m.rank_lower
  rw [he] at hr
  omega

end Merge
end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPattern
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Oligomorphic.finite_palette (h : Oligomorphic ρ) (n : ℕ) :
    ∃ U : Finset S, ∀ F : Finset S, F.card ≤ n →
      ∃ a : A, F.map (ρ a).toEmbedding ⊆ U := by
  classical
  choose R hR using h
  let U := (Finset.range (n+1)).biUnion (fun k => (R k).biUnion id)
  refine ⟨U,fun F hF => ?_⟩
  obtain ⟨E,hE,a,ha⟩ := hR F.card F rfl
  refine ⟨a,?_⟩
  rw [ha]
  intro s hs
  exact Finset.mem_biUnion.mpr ⟨F.card,Finset.mem_range.mpr (by omega),
    Finset.mem_biUnion.mpr ⟨E,hE,hs⟩⟩

end TwistedBrin

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma nodes_add_one (P : Pattern S) : nodes P + 1 = Fintype.card (Leaves P) := by
  induction P with
  | leaf => change 0 + 1 = Fintype.card Unit; simp
  | split s P Q ihP ihQ =>
    change nodes P + nodes Q + 1 + 1 = Fintype.card (Leaves P ⊕ Leaves Q)
    rw [Fintype.card_sum,← ihP,← ihQ]
    omega

lemma depth_le_nodes (P : Pattern S) : depth P ≤ nodes P := by
  induction P with
  | leaf => rfl
  | split s P Q ihP ihQ => simp only [depth,nodes]; omega

lemma coordinates_card_le (P : Pattern S) : (coordinates P).card ≤ nodes P := by
  classical
  induction P with
  | leaf => simp [coordinates,nodes]
  | split s P Q ihP ihQ =>
    have h₁ := Finset.card_insert_le s (coordinates P ∪ coordinates Q)
    have h₂ := Finset.card_union_le (coordinates P) (coordinates Q)
    simp only [coordinates,nodes]
    omega

lemma coordinates_relabel (σ : Equiv.Perm S) (P : Pattern S) :
    coordinates (relabel σ P) = (coordinates P).map σ.toEmbedding := by
  classical
  induction P with
  | leaf => simp [relabel,coordinates]
  | split s P Q ihP ihQ => simp [relabel,coordinates,ihP,ihQ,Finset.map_union]

lemma mem_bounded (U : Finset S) (n : ℕ) (P : Pattern S)
    (hP : coordinates P ⊆ U) (hd : depth P ≤ n) : P ∈ bounded U n := by
  classical
  induction n generalizing P with
  | zero =>
    cases P with
    | leaf => simp [bounded]
    | split s P Q => simp only [depth] at hd; omega
  | succ n ih =>
    cases P with
    | leaf => simp [bounded]
    | split s P Q =>
      have hs : s ∈ U := hP (by simp [coordinates])
      have hP' : coordinates P ⊆ U := fun x hx => hP (by simp [coordinates,hx])
      have hQ' : coordinates Q ⊆ U := fun x hx => hP (by simp [coordinates,hx])
      have hdP : depth P ≤ n := by simp only [depth] at hd; omega
      have hdQ : depth Q ≤ n := by simp only [depth] at hd; omega
      simp only [bounded,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_image]
      exact Or.inr ⟨s,hs,P,ih P hP' hdP,Q,ih Q hQ' hdQ,rfl⟩

lemma finite_orbit_representatives {A : Type v} [Group A] (ρ : A →* Equiv.Perm S)
    (h : Oligomorphic ρ) (n : ℕ) :
    ∃ R : Finset (Pattern S), ∀ P : Pattern S, Fintype.card (Leaves P) ≤ n →
      ∃ a : A, relabel (ρ a) P ∈ R := by
  classical
  obtain ⟨U,hU⟩ := h.finite_palette ρ n
  refine ⟨bounded U n,fun P hP => ?_⟩
  have hn : nodes P ≤ n := by have := nodes_add_one P; omega
  obtain ⟨a,ha⟩ := hU (coordinates P) ((coordinates_card_le P).trans hn)
  refine ⟨a,mem_bounded U n _ ?_ ?_⟩
  · rwa [coordinates_relabel]
  · rw [depth_relabel]
    exact (depth_le_nodes P).trans hn

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma translate_twistPieces_expand (B : Basis ρ) (P : B → Pattern S) (a : B → A) :
    translate ρ (twistPiecesHom ρ B a) (expand ρ B P) =
      expand ρ B (fun b => Pattern.relabel (ρ (a b)) (P b)) := by
  classical
  apply Basis.ext
  ext c
  change (c ∈ (Finset.univ.image (fun i => GermBrick.mk ρ (expandedChart ρ B P i))).map _) ↔
    c ∈ Finset.univ.image _
  simp only [Finset.mem_map,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨d,⟨i,rfl⟩,rfl⟩
    exact ⟨⟨i.1,Pattern.relabelLeaves (ρ (a i.1)) (P i.1) i.2⟩,
      (twistPieces_expanded_germ ρ B P a i).symm⟩
  · rintro ⟨⟨b,j⟩,rfl⟩
    obtain ⟨k,rfl⟩ := (Pattern.relabelLeaves (ρ (a b)) (P b)).surjective j
    exact ⟨_,⟨⟨b,k⟩,rfl⟩,twistPieces_expanded_germ ρ B P a ⟨b,k⟩⟩

lemma Forest.expand_eq {B C : Basis ρ} (F : Forest ρ B C) : expand ρ B F.pattern = C := by
  classical
  apply Basis.ext
  ext c
  change c ∈ Finset.univ.image _ ↔ c ∈ C.pieces
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    rw [F.chart_eq]
    exact (F.leaves i).property
  · intro hc
    obtain ⟨i,hi⟩ := F.leaves.surjective ⟨c,hc⟩
    exact ⟨i,(F.chart_eq i).trans (congrArg Subtype.val hi)⟩

lemma Forest.leaves_le_rank {B C : Basis ρ} (F : Forest ρ B C) (b : B) :
    Fintype.card (Pattern.Leaves (F.pattern b)) ≤ rank ρ C := by
  have hr : rank ρ C = ∑ b : B, Fintype.card (Pattern.Leaves (F.pattern b)) :=
    (congrArg (rank ρ) (F.expand_eq ρ)).symm.trans (rank_expand ρ B F.pattern)
  rw [hr]
  exact Finset.single_le_sum (f := fun b : B => Fintype.card (Pattern.Leaves (F.pattern b)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

lemma outgoing_finite_orbit_representatives (h : Oligomorphic ρ) (B : Basis ρ) (n : ℕ) :
    ∃ R : Finset (Basis ρ), ∀ C : Basis ρ, CutRefines ρ B C → rank ρ C ≤ n →
      ∃ a : B → A, translate ρ (twistPiecesHom ρ B a) C ∈ R := by
  classical
  obtain ⟨T,hT⟩ := Pattern.finite_orbit_representatives ρ h n
  let R := (Finset.univ : Finset (B → {P // P ∈ T})).image
    (fun f => expand ρ B (fun b => (f b).val))
  refine ⟨R,fun C hBC hC => ?_⟩
  obtain ⟨F⟩ := hBC
  choose a ha using fun b => hT (F.pattern b) ((F.leaves_le_rank ρ b).trans hC)
  refine ⟨a,?_⟩
  rw [← F.expand_eq ρ,translate_twistPieces_expand]
  exact Finset.mem_image.mpr ⟨fun b => ⟨_,ha b⟩,Finset.mem_univ _,rfl⟩

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinGermBrick
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.GermBrick
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma restricts_iff_chart {b c : GermBrick ρ} (h : LocalEmbedding ρ) (hb : mk ρ h = b) :
    Restricts ρ c b ↔ ∃ p : Prefix S, c = mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.ofPrefix ρ p)) := by
  constructor
  · rintro ⟨k,p,hk,rfl⟩
    obtain ⟨a,rfl⟩ := (mk_eq_iff ρ k h).mp (hk.symm.trans hb.symm)
    refine ⟨p.permute (ρ a),?_⟩
    rw [LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix,
      ← LocalEmbedding.comp_assoc,mk_gauge]
  · rintro ⟨p,rfl⟩
    exact ⟨h,p,hb.symm,rfl⟩

lemma eq_of_common_restriction_of_region_eq {b c d : GermBrick ρ}
    (hc : Restricts ρ c b) (hd : Restricts ρ d b) (he : region ρ c = region ρ d) : c = d := by
  obtain ⟨p,rfl⟩ := (restricts_iff_chart ρ (representative ρ b) (mk_representative ρ b)).mp hc
  obtain ⟨q,rfl⟩ := (restricts_iff_chart ρ (representative ρ b) (mk_representative ρ b)).mp hd
  have hpq : p.brick = q.brick := by
    change Set.range ((representative ρ b) ∘ p.chart) =
      Set.range ((representative ρ b) ∘ q.chart) at he
    rw [Set.range_comp,Set.range_comp] at he
    exact (Set.image_injective.mpr (representative ρ b).injective) he
  rw [Prefix.brick_injective hpq]

end TwistedBrin.GermBrick

namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma mem_descendants (C : Basis ρ) (d : GermBrick ρ) (c : C) :
    c ∈ descendants ρ C d ↔ GermBrick.region ρ c.val ⊆ GermBrick.region ρ d := by
  classical
  simp [descendants]

lemma region_iff_descendants {D C : Basis ρ} (hDC : D ≤ C) (d : D) (x : Box S) :
    x ∈ GermBrick.region ρ d.val ↔
    ∃ c : C, c ∈ descendants ρ C d.val ∧ x ∈ GermBrick.region ρ c.val := by
  constructor
  · intro hx
    obtain ⟨c,hc,_⟩ := C.partition x
    obtain ⟨e,he⟩ := hDC c
    have hxe := GermBrick.region_subset_of_restricts ρ he hc
    have hed : e = d := (D.partition x).unique hxe hx
    subst e
    exact ⟨c,(mem_descendants ρ C d.val c).mpr (GermBrick.region_subset_of_restricts ρ he),hc⟩
  · rintro ⟨c,hc,hx⟩
    exact (mem_descendants ρ C d.val c).mp hc hx

lemma region_eq_of_descendants_eq {D E C : Basis ρ} (hDC : D ≤ C) (hEC : E ≤ C)
    (d : D) (e : E) (he : descendants ρ C d.val = descendants ρ C e.val) :
    GermBrick.region ρ d.val = GermBrick.region ρ e.val := by
  ext x
  rw [region_iff_descendants ρ hDC,region_iff_descendants ρ hEC,he]

lemma germ_eq_of_region_eq_above {B D E : Basis ρ} (hBD : B ≤ D) (hBE : B ≤ E)
    (d : D) (e : E) (he : GermBrick.region ρ d.val = GermBrick.region ρ e.val) : d.val = e.val := by
  obtain ⟨b,hb⟩ := hBD d
  obtain ⟨c,hc⟩ := hBE e
  obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ d.val
  have hbx := GermBrick.region_subset_of_restricts ρ hb hx
  have hcx := GermBrick.region_subset_of_restricts ρ hc (he ▸ hx)
  have hbc : b = c := (B.partition x).unique hbx hcx
  subst c
  exact GermBrick.eq_of_common_restriction_of_region_eq ρ hb hc he

lemma intervalCode_injective (B C : Basis ρ) :
    Function.Injective (fun D : {D : Basis ρ // B ≤ D ∧ D ≤ C} => intervalCode ρ C D.val) := by
  classical
  have help : ∀ (D E : Basis ρ), B ≤ D → D ≤ C → B ≤ E → E ≤ C →
      intervalCode ρ C D = intervalCode ρ C E → D.pieces ⊆ E.pieces := by
    intro D E hBD hDC hBE hEC he d hd
    have hm : descendants ρ C d ∈ intervalCode ρ C E := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨⟨d,hd⟩,Finset.mem_univ _,rfl⟩
    obtain ⟨e,_,hed⟩ := Finset.mem_image.mp hm
    have hr := region_eq_of_descendants_eq ρ hDC hEC ⟨d,hd⟩ e hed.symm
    have hg := germ_eq_of_region_eq_above ρ hBD hBE ⟨d,hd⟩ e hr
    change d = e.val at hg
    rw [hg]
    exact e.property
  intro D E he
  apply Subtype.ext
  apply Basis.ext
  exact Finset.Subset.antisymm
    (help D.val E.val D.property.1 D.property.2 E.property.1 E.property.2 he)
    (help E.val D.val E.property.1 E.property.2 D.property.1 D.property.2 he.symm)

theorem finite_interval (B C : Basis ρ) : Finite {D : Basis ρ // B ≤ D ∧ D ≤ C} :=
  Finite.of_injective _ (intervalCode_injective ρ B C)

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma rank_rankModel (B : Basis ρ) : rank ρ (rankModel ρ (rank ρ B)) = rank ρ B := by
  classical
  simp only [rankModel,dite_eq_left (show ∃ C : Basis ρ, rank ρ C = rank ρ B from ⟨B,rfl⟩)]
  exact Classical.choose_spec (show ∃ C : Basis ρ, rank ρ C = rank ρ B from ⟨B,rfl⟩)

lemma rank_finite_orbit_representatives (n : ℕ) :
    ∃ R : Finset (Basis ρ), ∀ B : Basis ρ, rank ρ B ≤ n →
      ∃ g : localGroup ρ, translate ρ g B ∈ R := by
  classical
  refine ⟨(Finset.range (n+1)).image (rankModel ρ),fun B hB => ?_⟩
  obtain ⟨g,hg⟩ := orbit_of_rank_eq ρ (rank_rankModel ρ B).symm
  refine ⟨g,Finset.mem_image.mpr ⟨rank ρ B,Finset.mem_range.mpr (by omega),?_⟩⟩
  exact hg.symm

lemma twistPieces_translate_self (B : Basis ρ) (a : B → A) :
    translate ρ (twistPiecesHom ρ B a) B = B := by
  exact MulAction.mem_stabilizer_iff.mp
    (rigid_le_vertexStabilizer ρ B (twistPiecesHom_mem_rigidStabilizer ρ B a))

lemma pair_finite_orbit_representatives (h : Oligomorphic ρ) (n : ℕ) :
    ∃ R : Finset (Basis ρ × Basis ρ), ∀ B C : Basis ρ,
      CutRefines ρ B C → rank ρ C ≤ n →
      ∃ g : localGroup ρ, (translate ρ g B,translate ρ g C) ∈ R := by
  classical
  obtain ⟨T,hT⟩ := rank_finite_orbit_representatives ρ n
  choose Q hQ using fun B : Basis ρ => outgoing_finite_orbit_representatives ρ h B n
  let R := T.biUnion (fun B => (Q B).image (fun C => (B,C)))
  refine ⟨R,fun B C hBC hC => ?_⟩
  have hB : rank ρ B ≤ n := (rank_mono ρ (le_of_cutRefines ρ hBC)).trans hC
  obtain ⟨g,hg⟩ := hT B hB
  obtain ⟨a,ha⟩ := hQ (translate ρ g B) (translate ρ g C)
    (translate_cutRefines ρ g hBC) (by simpa only [rank_translate] using hC)
  refine ⟨twistPiecesHom ρ (translate ρ g B) a * g,?_⟩
  rw [translate_mul,translate_mul,twistPieces_translate_self]
  exact Finset.mem_biUnion.mpr ⟨translate ρ g B,hg,Finset.mem_image.mpr ⟨_,ha,rfl⟩⟩

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPatternFactor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace CutInterval
variable {ρ} {B C : Basis ρ}
instance instFinite : Finite (CutInterval ρ B C) := by
  let := finite_interval ρ B C
  exact Finite.of_injective
    (fun D : CutInterval ρ B C =>
      (⟨D.val,le_of_cutRefines ρ D.lower,le_of_cutRefines ρ D.upper⟩ :
        {E : Basis ρ // B ≤ E ∧ E ≤ C}))
    (fun _ _ h => ext (congrArg Subtype.val h))

end CutInterval

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactInOfDirected
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
theorem exactIn_of_directed [Nonempty P]
    (hdir : ∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z) (n : ℕ) : ExactIn P n := by
  classical
  have hfin (F : Finset P) : ∃ z : P, ∀ x ∈ F, x ≤ z := by
    induction F using Finset.induction_on with
    | empty => exact ⟨Classical.choice ‹Nonempty P›,by simp⟩
    | @insert x F hx ih =>
      obtain ⟨y,hy⟩ := ih
      obtain ⟨z,hxz,hyz⟩ := hdir x y
      exact ⟨z,fun a ha => (Finset.mem_insert.mp ha).elim (fun he => he ▸ hxz)
        (fun haF => (hy a haF).trans hyz)⟩
  intro c hc hn hd ha
  obtain ⟨z,hz⟩ := hfin (vertexSupport P c)
  have hcz : c ∈ carrier P z := fun s hs => ⟨hc hs,fun x hx =>
    hz x ((mem_vertexSupport P).mpr ⟨s,hs,hx⟩)⟩
  refine ⟨cone P z c,carrier_le_module P z (cone_carrier P z hcz),
    cone_mem_degreeModule P z hn,?_⟩
  rw [boundary_cone,hd,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]
end

section
open OrderListChains
variable (P : Type*) [PartialOrder P]
theorem lower_filling_many (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, h < r a → ∃ x, x < a)
    (hex : ∀ a, h < r a → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P)
    (hc : c ∈ onSet P {x | r x ≤ h}) (hcn : Homogeneous P n c)
    (hcd : boundary P c = 0) (hca : augmentation P c = 0)
    (k : ℕ) (b : Chain P)
    (hb : b ∈ onSet P {x | r x ≤ h+k}) (hbn : Homogeneous P (n+1) b)
    (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P {x | r x ≤ h} ∧
      Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  induction k generalizing b with
  | zero => exact ⟨b,by simpa only [Nat.add_zero] using hb,hbn,hbd⟩
  | succ k ih =>
    obtain ⟨b',hb',hbn',hbd'⟩ := lower_filling P r hr (h+k) N
      (fun a ha => hne a (by omega))
      (fun a ha => hex a (by omega)) hnN c b
      (onSet_mono P (fun x hx => by change r x ≤ h+k; change r x ≤ h at hx; omega) hc)
      hcn hcd hca (by simpa only [Nat.add_assoc] using hb) hbn hbd
    exact ih b' hb' hbn' hbd'

theorem exactSet_sublevel (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, h < r a → ∃ x, x < a)
    (hex : ∀ a, h < r a → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (hall : ExactIn P n) :
    ExactSet P {x | r x ≤ h} n := by
  classical
  intro c hc hn hd ha
  obtain ⟨b,hb,hbn,hbd⟩ := hall c (onSet_le_module P _ hc) hn hd ha
  let k := (vertexSupport P b).sup r
  have hb' : b ∈ onSet P {x | r x ≤ h+k} := by
    intro s hs
    refine ⟨hb hs,fun x hx => ?_⟩
    have hxr : r x ≤ k := Finset.le_sup ((mem_vertexSupport P).mpr ⟨s,hs,hx⟩)
    change r x ≤ h+k
    omega
  exact lower_filling_many P r hr h N hne hex hnN c hc hn hd ha k b hb' hbn hbd
end

open OrderListChains
variable (P : Type*) [Preorder P]

theorem constant_of_exact_zero {U : Set P} (hU : ExactSet P U 0) {Y : Type*}
    (f : P → Y) (hf : ∀ x ∈ U, ∀ y ∈ U, x ≤ y → f x = f y)
    {x y : P} (hx : x ∈ U) (hy : y ∈ U) : f x = f y := by
  classical
  let ev : Chain P →ₗ[ℤ] (Y →₀ ℤ) :=
    Finsupp.linearCombination ℤ (fun s : Simplex P => Finsupp.single (f s.1) 1)
  have hev (z : P) : ev (vertex P z) = Finsupp.single (f z) 1 := by
    simp [ev,vertex,simplexVertex]
  have hvm (z : P) (hz : z ∈ U) : vertex P z ∈ onSet P U := by
    apply supported_single
    exact ⟨by simp [Descending,list,simplexVertex],by simpa [vertices,simplexVertex]⟩
  have hvn (z : P) : Homogeneous P 0 (vertex P z) := by
    apply supported_single
    rfl
  obtain ⟨b,hb,hbn,hbd⟩ := hU (vertex P x-vertex P y)
    ((onSet P U).sub_mem (hvm x hx) (hvm y hy)) (supported_sub P (hvn x) (hvn y))
    (by simp) (by simp)
  have he : ev (boundary P b) = 0 := by
    have hh := OrderBasedComplex.linear_eq_on_support (ev.comp (boundary P)) 0 b (by
      rintro ⟨a,l⟩ hs
      have hl : l.length = 1 := hbn (a,l) hs
      obtain ⟨d,hd⟩ := List.length_eq_one_iff.mp hl
      subst l
      have hds : d ≤ a := (hb hs).1.le_head P (Or.inr (by simp))
      have hda := hf d ((hb hs).2 (Or.inr (by simp))) a
        ((hb hs).2 (head_mem_vertices P _)) hds
      rw [LinearMap.comp_apply,LinearMap.zero_apply,single_cons]
      change ev (boundary P (cone P a (vertex P d))) = 0
      rw [boundary_cone,boundary_vertex,map_zero,sub_zero,K_apply,augmentation_vertex,one_smul,
        map_sub,hev,hev,hda,sub_self])
    exact hh
  rw [hbd,map_sub,hev,hev,sub_eq_zero] at he
  by_contra hn
  have hh := congrArg (fun t : Y →₀ ℤ => t (f x)) he
  simp [hn] at hh
end OrderChains

universe u v

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PosetTransport
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace PosetTransport
section
universe u v w
variable {P : Type u} [Preorder P] {Q : Type v} [Preorder Q]
variable {H : Type w} [Group H]
lemma Connected.constant (h : Connected P) {Y : Type*} (f : P → Y)
    (hf : ∀ {x y}, x ≤ y → f x = f y) (x y : P) : f x = f y := by
  induction h x y with
  | refl => rfl
  | @tail b d hxb hbd ih =>
    exact ih.trans (hbd.elim hf (fun hh => (hf hh).symm))

lemma connected_of_constant
    (h : ∀ f : P → Bool, (∀ {x y}, x ≤ y → f x = f y) → ∀ x y, f x = f y) :
    Connected P := by
  classical
  intro x y
  let f (z : P) : Bool := decide (Relation.ReflTransGen Adj x z)
  have hf : ∀ {a b : P}, a ≤ b → f a = f b := by
    intro a b hab
    have he : Relation.ReflTransGen Adj x a ↔ Relation.ReflTransGen Adj x b := by
      constructor
      · intro ha
        exact ha.tail (show Adj a b from Or.inl hab)
      · intro hb
        exact hb.tail (show Adj b a from Or.inr hab)
    simp only [f,he]
  have he := h f hf x y
  have hx : f x = true := by
    simp only [f,decide_eq_true_eq]
    exact Relation.ReflTransGen.refl
  have hy : f y = true := he.symm.trans hx
  exact of_decide_eq_true hy

end

open OrderListChains OrderChains
end PosetTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisGroundMatching
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace CutBasis
lemma strictMono_rank : StrictMono (fun B : CutBasis ρ => rank ρ B.val) := by
  intro B C h
  apply rank_strictMono ρ
  exact lt_of_le_of_ne (le_of_cutRefines ρ h.le) (fun he => h.ne (ext he))
lemma directed (B C : CutBasis ρ) : ∃ D, B ≤ D ∧ C ≤ D := by
  obtain ⟨D,hBD,hCD⟩ := cut_directed ρ B.val C.val
  exact ⟨⟨D⟩,hBD,hCD⟩
lemma lower_nonempty [Nonempty S] (C : CutBasis ρ) (h : 2 ≤ rank ρ C.val) :
    ∃ B : CutBasis ρ, B < C := by
  let M := groundMatching C.val (Classical.choice ‹Nonempty S›) 1 (by simpa using h)
  let e := M.edge 0
  exact ⟨⟨e.lower⟩,lt_of_le_of_ne e.lower_cutRefines (fun he => e.lower_ne (congrArg CutBasis.val he))⟩

theorem sublevel_exact [Nonempty S] (n h : ℕ) (hh : 2*(2*2^(n+2)+1) ≤ h) :
    ExactSet (CutBasis ρ) {B | rank ρ B.val ≤ h} n := by
  apply exactSet_sublevel (CutBasis ρ) (fun B => rank ρ B.val) strictMono_rank h n
    (fun C hC => lower_nonempty C (by omega)) ?_ le_rfl
    (exactIn_of_directed (CutBasis ρ) directed n)
  intro C hC k hk
  apply lower_exactSet C k
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.add_le_add_right hk 2)
  omega
end CutBasis
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisMatching
attribute [-instance] _root_.OAI.EquivariantOrderChains.covariantPosetAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace ActionTransport
section
open PosetTransport
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q]

theorem section_of_cocycle [Nonempty P] (hconn : Connected P)
    (hmono : ∀ g : G, Monotone (g • · : P → P))
    (p : Q →* G) (t : P → G) (d : Gauge p t) (c : Cocycle P Q)
    (hc : c.Trivial)
    (proj : ∀ {x y} (h : x ≤ y), p (c.edge h) = (t x)⁻¹ * t y)
    (equiv : ∀ g {x y} (h : x ≤ y), c.edge (hmono g h) =
      d.value g x * c.edge h * (d.value g y)⁻¹) :
    ∃ s : G →* Q, p.comp s = MonoidHom.id G := by
  classical
  obtain ⟨v,hv⟩ := hc
  let b : P := Classical.choice inferInstance
  let F (g : G) (x : P) : Q := v (g • x) * d.value g x * (v x)⁻¹
  have hF (g : G) (x y : P) : F g x = F g y := by
    apply hconn.constant (F g) ?_ x y
    intro a b hab
    have hv' := hv (hmono g hab)
    rw [equiv g hab] at hv'
    have hvab := hv hab
    dsimp [F]
    rw [← hv',← hvab]
    group
  have hproj (x y : P) : p (v x) * (t x)⁻¹ = p (v y) * (t y)⁻¹ := by
    apply hconn.constant (fun z => p (v z) * (t z)⁻¹) ?_ x y
    intro a b hab
    have hp := congrArg p (hv hab)
    rw [map_mul,proj hab] at hp
    rw [← hp]
    group
  let f : G →* Q := {
    toFun := fun g => F g b
    map_one' := by simp [F,d.one]
    map_mul' := by
      intro g h
      have hh := hF g (h • b) b
      dsimp [F] at hh ⊢
      rw [mul_smul,d.mul,← hh]
      group }
  let k := p (v b) * (t b)⁻¹
  have hf (g : G) : p (f g) = k * g * k⁻¹ := by
    change p (v (g • b) * d.value g b * (v b)⁻¹) = _
    rw [map_mul,map_mul,map_inv,d.projects]
    have hh := hproj (g • b) b
    calc
      _ = (p (v (g • b)) * (t (g • b))⁻¹) * g * t b * (p (v b))⁻¹ := by group
      _ = (p (v b) * (t b)⁻¹) * g * t b * (p (v b))⁻¹ := by rw [hh]
      _ = k * g * k⁻¹ := by dsimp [k]; group
  let j : G →* G := {
    toFun := fun g => k⁻¹ * g * k
    map_one' := by group
    map_mul' := by intros; group }
  refine ⟨f.comp j,?_⟩
  ext g
  change p (f (k⁻¹ * g * k)) = g
  rw [hf]
  group

end

section
open PosetTransport
open scoped Pointwise
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]

variable [IsMonotoneAction G P]

lemma eq_top_of_frames [Nonempty P] (hconn : Connected P)
    (F : Frames G P) (E : Frames G (Edge P)) (K : Subgroup G)
    (hstab : ∀ i, F.stab i ≤ K)
    (hend : ∀ i, F.element (E.rep i).val.1 ∈ K ∧ F.element (E.rep i).val.2 ∈ K) :
    K = ⊤ := by
  classical
  let c (x : P) : Set G := F.element x • (K : Set G)
  have hcos (g : G) (x : P) :
      F.element (g • x) • (K : Set G) = (g * F.element x) • (K : Set G) := by
    apply (leftCoset_eq_iff K).mpr
    exact hstab _ (by simpa only [mul_assoc] using F.difference_mem g x)
  have hc (x y : P) : c x = c y := by
    apply hconn.constant c ?_ x y
    intro a b hab
    let e : Edge P := ⟨(a,b),hab⟩
    let i := E.index e
    let g := E.element e
    have ha : g • (E.rep i).val.1 = a := congrArg (fun e : Edge P => e.val.1) (E.frame e)
    have hb : g • (E.rep i).val.2 = b := congrArg (fun e : Edge P => e.val.2) (E.frame e)
    dsimp [c]
    rw [← ha,← hb,hcos,hcos]
    apply (leftCoset_eq_iff K).mpr
    convert K.mul_mem (K.inv_mem (hend i).1) (hend i).2 using 1; group
  let b : P := Classical.choice inferInstance
  have h0 : F.element (F.rep (F.index b)) ∈ K := by
    apply hstab (F.index b)
    rw [Frames.mem_stab]
    simpa only [F.index_rep] using F.frame (F.rep (F.index b))
  apply top_unique
  intro g _
  have he := hc (g • F.rep (F.index b)) (F.rep (F.index b))
  dsimp [c] at he
  rw [hcos] at he
  have hh := (leftCoset_eq_iff K).mp he
  have hg : (F.element (F.rep (F.index b)))⁻¹ * g⁻¹ * F.element (F.rep (F.index b)) ∈ K := by
    simpa only [mul_inv_rev] using hh
  have hi := K.mul_mem (K.mul_mem h0 hg) (K.inv_mem h0)
  have hgi : g⁻¹ ∈ K := by convert hi using 1; group
  simpa only [inv_inv] using K.inv_mem hgi

lemma fg_of_frames [Nonempty P] (hconn : Connected P)
    (F : Frames G P) (E : Frames G (Edge P))
    [Finite F.Index] [Finite E.Index] (hstab : ∀ i, (F.stab i).FG) : Group.FG G := by
  classical
  choose S hS using hstab
  let T : Set G := (⋃ i, (S i : Set G)) ∪
    Set.range (fun i => F.element (E.rep i).val.1) ∪
    Set.range (fun i => F.element (E.rep i).val.2)
  have hfin : T.Finite := ((Set.finite_iUnion fun i => (S i).finite_toSet).union
    (Set.finite_range _)).union (Set.finite_range _)
  have htop : Subgroup.closure T = ⊤ := by
    apply eq_top_of_frames hconn F E
    · intro i
      rw [← hS i]
      apply Subgroup.closure_mono
      intro g hg
      exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i,hg⟩))
    · intro i
      constructor
      · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨i,rfl⟩))
      · exact Subgroup.subset_closure (Or.inr ⟨i,rfl⟩)
  exact Group.fg_iff.mpr ⟨T,htop,hfin⟩
end

section
open PosetTransport
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q]

variable [IsMonotoneAction G P]
variable {p : Q →* G}

lemma rawEdge_projects (F : Frames G P) (E : Frames G (Edge P))
    (p : Q →* G) (d : Gauge p F.element) (L : E.Index → Q)
    (hL : ∀ i, p (L i) = (F.element (E.rep i).val.1)⁻¹ * F.element (E.rep i).val.2)
    (e : Edge P) : p (rawEdge F E d L e) = (F.element e.val.1)⁻¹ * F.element e.val.2 := by
  have h1 := congrArg (fun e : Edge P => e.val.1) (E.frame e)
  have h2 := congrArg (fun e : Edge P => e.val.2) (E.frame e)
  change E.element e • (E.rep (E.index e)).val.1 = e.val.1 at h1
  change E.element e • (E.rep (E.index e)).val.2 = e.val.2 at h2
  simp only [rawEdge,edgeTransport,map_mul,map_inv,d.projects,hL,h1,h2]
  group

lemma edgeTransport_stabilizer (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q)
    (coherent : ∀ i k, k ∈ E.stab i →
      d.value k (E.rep i).val.1 * L i = L i * d.value k (E.rep i).val.2)
    (i : E.Index) (g k : G) (hk : k ∈ E.stab i) :
    edgeTransport F E d L i (g*k) = edgeTransport F E d L i g := by
  have h1 := congrArg (fun e : Edge P => e.val.1) hk
  have h2 := congrArg (fun e : Edge P => e.val.2) hk
  change k • (E.rep i).val.1 = (E.rep i).val.1 at h1
  change k • (E.rep i).val.2 = (E.rep i).val.2 at h2
  simp only [edgeTransport,d.mul,h1,h2]
  rw [mul_assoc (d.value g _),coherent i k hk]
  group

lemma rawEdge_equivariant (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q)
    (coherent : ∀ i k, k ∈ E.stab i →
      d.value k (E.rep i).val.1 * L i = L i * d.value k (E.rep i).val.2)
    (g : G) (e : Edge P) : rawEdge F E d L (g • e) =
      d.value g e.val.1 * rawEdge F E d L e * (d.value g e.val.2)⁻¹ := by
  have hk := E.difference_mem g e
  let k := (E.element (g • e))⁻¹ * g * E.element e
  have he : E.element (g • e) * k = g * E.element e := by dsimp [k]; group
  have hh := edgeTransport_stabilizer F E d L coherent (E.index e) (E.element (g • e)) k hk
  rw [he] at hh
  have h1 := congrArg (fun e : Edge P => e.val.1) (E.frame e)
  have h2 := congrArg (fun e : Edge P => e.val.2) (E.frame e)
  change E.element e • (E.rep (E.index e)).val.1 = e.val.1 at h1
  change E.element e • (E.rep (E.index e)).val.2 = e.val.2 at h2
  simp only [rawEdge,E.index_smul]
  rw [← hh]
  simp only [edgeTransport,d.mul,h1,h2]
  group
end

open PosetTransport
universe u v w z
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q] {R : Type z} [Group R]
variable [IsMonotoneAction G P]

lemma rawEdge_map (F : Frames G P) (E : Frames G (Edge P))
    {p : Q →* G} (d : Gauge p F.element) (L : E.Index → Q)
    (q : Q →* R) (p' : R →* G) (hp' : p'.comp q = p) (e : Edge P) :
    rawEdge F E (d.map q p' hp') (fun i => q (L i)) e = q (rawEdge F E d L e) := by
  simp only [rawEdge,edgeTransport,Gauge.map,map_mul,map_inv]
end ActionTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ActionTransport
attribute [-instance] _root_.OAI.EquivariantOrderChains.covariantPosetAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace ActionTransport
section
open PosetTransport ActionPresentation
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q]
omit [Preorder P] in
lemma exists_liftedFrames [Preorder P] (F : Frames G P) [Finite F.Index]
    (hFP : ∀ i, Group.IsFinitelyPresented (F.stab i))
    (p : Q →* G) (hp : Function.Surjective p) :
    ∃ (S : Set Q) (_ : S.Finite) (hS : S ⊆ p.ker),
      Nonempty (LiftedFrames F (killProjection p S hS)) := by
  classical
  let M (i : F.Index) : LiftModel p (F.stab i).subtype := by
    letI := hFP i
    exact liftModel p hp (F.stab i).subtype
  let S : Set Q := ⋃ i, (M i).obstruction
  have hS : S ⊆ p.ker := by
    intro q hq
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
    exact (M i).obstruction_ker hi
  let q := QuotientGroup.mk' (Subgroup.normalClosure S)
  have hq : ∀ i r, r ∈ (M i).obstruction → q r = 1 := by
    intro i r hr
    apply (QuotientGroup.eq_one_iff r).mpr
    exact Subgroup.subset_normalClosure (Set.mem_iUnion.mpr ⟨i,hr⟩)
  refine ⟨S,Set.finite_iUnion (fun i => (M i).obstruction_finite),hS,?_⟩
  refine ⟨⟨fun i => (M i).hom q (hq i),?_⟩⟩
  intro i h
  exact DFunLike.congr_fun ((M i).hom_commutes q (hq i) (killProjection p S hS) rfl) h
end

section
open PosetTransport ActionPresentation
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q] [IsMonotoneAction G P]
variable {p : Q →* G} {t : P → G}

lemma coherent_of_generators (d : Gauge p t) (e : Edge P) (L : Q)
    (S : Set (MulAction.stabilizer G e)) (hS : Subgroup.closure S = ⊤)
    (hrel : ∀ h ∈ S, d.value h.val e.val.1 * L = L * d.value h.val e.val.2) :
    ∀ h : MulAction.stabilizer G e, d.value h.val e.val.1 * L = L * d.value h.val e.val.2 := by
  have he : edgeLeftHom d e = edgeRightHom d e L := by
    apply MonoidHom.eq_of_eqOn_dense hS
    intro h hh
    change d.value h.val e.val.1 = L * d.value h.val e.val.2 * L⁻¹
    rw [← hrel h hh]
    group
  intro h
  have hh := DFunLike.congr_fun he h
  change d.value h.val e.val.1 = L * d.value h.val e.val.2 * L⁻¹ at hh
  rw [hh]
  group

lemma edge_defect_projects (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q)
    (hL : ∀ i, p (L i) = (F.element (E.rep i).val.1)⁻¹ * F.element (E.rep i).val.2)
    (i : E.Index) (h : E.stab i) :
    p (d.value h.val (E.rep i).val.1 * L i * (d.value h.val (E.rep i).val.2)⁻¹ * (L i)⁻¹) = 1 := by
  have h1 := congrArg (fun e : Edge P => e.val.1) h.property
  have h2 := congrArg (fun e : Edge P => e.val.2) h.property
  change h.val • (E.rep i).val.1 = (E.rep i).val.1 at h1
  change h.val • (E.rep i).val.2 = (E.rep i).val.2 at h2
  simp only [map_mul,map_inv,d.projects,hL,h1,h2]
  group

theorem finite_flat_quotient (F : Frames G P) (E : Frames G (Edge P))
    (T : Frames G (Triangle P)) [Finite F.Index] [Finite E.Index] [Finite T.Index]
    (hEFG : ∀ i, Group.FG (E.stab i)) (p : Q →* G) (hp : Function.Surjective p)
    (d : Gauge p F.element) :
    ∃ (S : Set Q) (_ : S.Finite) (hS : S ⊆ p.ker),
      ∃ c : Cocycle P (Q ⧸ Subgroup.normalClosure S),
        (∀ {x y} (h : x ≤ y), killProjection p S hS (c.edge h) = (F.element x)⁻¹ * F.element y) ∧
        (∀ g {x y} (h : x ≤ y), c.edge (act_mono g h) =
          (d.map (QuotientGroup.mk' _) (killProjection p S hS) rfl).value g x * c.edge h *
          ((d.map (QuotientGroup.mk' _) (killProjection p S hS) rfl).value g y)⁻¹) := by
  classical
  choose L hL using fun i : E.Index => hp ((F.element (E.rep i).val.1)⁻¹ * F.element (E.rep i).val.2)
  choose A hA using fun i => (hEFG i).out
  let c₀ := rawEdge F E d L
  let defect (i : E.Index) (h : E.stab i) :=
    d.value h.val (E.rep i).val.1 * L i * (d.value h.val (E.rep i).val.2)⁻¹ * (L i)⁻¹
  let D₁ : Set Q := ⋃ i, defect i '' (A i : Set (E.stab i))
  let D₂ : Set Q := Set.range (fun i => c₀ (Edge.diag (F.rep i)))
  let D₃ : Set Q := Set.range (fun i => c₀ (T.rep i).e01 * c₀ (T.rep i).e12 * (c₀ (T.rep i).e02)⁻¹)
  let S := D₁ ∪ D₂ ∪ D₃
  have hfin : S.Finite := ((Set.finite_iUnion fun i => (A i).finite_toSet.image (defect i)).union
    (Set.finite_range _)).union (Set.finite_range _)
  have hproj (e : Edge P) : p (c₀ e) = (F.element e.val.1)⁻¹ * F.element e.val.2 :=
    rawEdge_projects F E p d L hL e
  have hS : S ⊆ p.ker := by
    rintro r ((hr | hr) | hr)
    · obtain ⟨i,h,hh,rfl⟩ := Set.mem_iUnion.mp hr
      exact edge_defect_projects F E d L hL i h
    · obtain ⟨i,rfl⟩ := hr
      change p (c₀ (Edge.diag (F.rep i))) = 1
      rw [hproj]
      exact inv_mul_cancel _
    · obtain ⟨i,rfl⟩ := hr
      change p (c₀ (T.rep i).e01 * c₀ (T.rep i).e12 * (c₀ (T.rep i).e02)⁻¹) = 1
      simp only [map_mul,map_inv]
      rw [hproj (T.rep i).e01,hproj (T.rep i).e12,hproj (T.rep i).e02]
      dsimp only [Triangle.e01,Triangle.e12,Triangle.e02]
      group
  let q := QuotientGroup.mk' (Subgroup.normalClosure S)
  let p' := killProjection p S hS
  let d' := d.map q p' rfl
  let c' : Edge P → Q ⧸ Subgroup.normalClosure S := fun e => q (c₀ e)
  have hkill (r : Q) (hr : r ∈ S) : q r = 1 :=
    (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure hr)
  have hcoh : ∀ i k, k ∈ E.stab i →
      d'.value k (E.rep i).val.1 * q (L i) = q (L i) * d'.value k (E.rep i).val.2 := by
    intro i k hk
    apply coherent_of_generators d' (E.rep i) (q (L i)) (A i : Set (E.stab i)) (hA i) ?_ ⟨k,hk⟩
    intro h hh
    have hd := hkill (defect i h) (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i,h,hh,rfl⟩)))
    change q (d.value h.val (E.rep i).val.1 * L i * (d.value h.val (E.rep i).val.2)⁻¹ * (L i)⁻¹) = 1 at hd
    apply mul_inv_eq_one.mp
    simpa only [d',Gauge.map,map_mul,map_inv,mul_inv_rev,mul_assoc] using hd
  have heq (g : G) (e : Edge P) : c' (g • e) = d'.value g e.val.1 * c' e * (d'.value g e.val.2)⁻¹ := by
    have hh := rawEdge_equivariant F E d' (fun i => q (L i)) hcoh g e
    change q (rawEdge F E d L (g • e)) =
      d'.value g e.val.1 * q (rawEdge F E d L e) * (d'.value g e.val.2)⁻¹
    rw [← rawEdge_map F E d L q p' rfl (g • e),← rawEdge_map F E d L q p' rfl e]
    exact hh
  have hdiag (i : F.Index) : c' (Edge.diag (F.rep i)) = 1 :=
    hkill _ (Or.inl (Or.inr ⟨i,rfl⟩))
  have htri (i : T.Index) : c' (T.rep i).e01 * c' (T.rep i).e12 = c' (T.rep i).e02 := by
    apply mul_inv_eq_one.mp
    have hh := hkill _ (Or.inr ⟨i,rfl⟩)
    simpa only [map_mul,map_inv] using hh
  refine ⟨S,hfin,hS,cocycleOfFlat F T d' c' heq hdiag htri,?_,?_⟩
  · intro x y h
    exact hproj ⟨(x,y),h⟩
  · intro g x y h
    exact heq g ⟨(x,y),h⟩
end

section
open PosetTransport ActionPresentation
universe u v
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable [IsMonotoneAction G P]

theorem finitelyPresented_of_frames [Nonempty P] (hconn : Connected P)
    (hsc : ∀ (R : Type) (_ : Group R) (c : Cocycle P R), c.Trivial)
    (F : Frames G P) (E : Frames G (Edge P)) (T : Frames G (Triangle P))
    [Finite F.Index] [Finite E.Index] [Finite T.Index]
    (hV : ∀ i, Group.IsFinitelyPresented (F.stab i))
    (hE : ∀ i, Group.FG (E.stab i)) : Group.IsFinitelyPresented G := by
  classical
  have hVG (i : F.Index) : (F.stab i).FG := by
    obtain ⟨n,f,hf,_⟩ := (hV i).out
    exact (Group.fg_iff_subgroup_fg _).mp (Group.fg_of_surjective hf)
  let : Group.FG G := fg_of_frames hconn F E hVG
  obtain ⟨α,hα,p₀,hp₀⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp
    (inferInstance : Group.FG G)
  let : Finite α := hα
  obtain ⟨S₁,hs₁,hker₁,⟨J⟩⟩ := exists_liftedFrames F hV p₀ hp₀
  let Q₁ := FreeGroup α ⧸ Subgroup.normalClosure S₁
  let : Group.IsFinitelyPresented Q₁ := kill_finitelyPresented S₁ hs₁
  let p₁ : Q₁ →* G := killProjection p₀ S₁ hker₁
  have hp₁ : Function.Surjective p₁ := killProjection_surj p₀ hp₀ S₁ hker₁
  obtain ⟨S₂,hs₂,hker₂,c,hproj,heq⟩ := finite_flat_quotient F E T hE p₁ hp₁ J.gauge
  let Q₂ := Q₁ ⧸ Subgroup.normalClosure S₂
  let : Group.IsFinitelyPresented Q₂ := kill_finitelyPresented S₂ hs₂
  let p₂ : Q₂ →* G := killProjection p₁ S₂ hker₂
  let d₂ := J.gauge.map (QuotientGroup.mk' (Subgroup.normalClosure S₂)) p₂ rfl
  obtain ⟨s,hs⟩ := section_of_cocycle hconn act_mono p₂ F.element d₂ c
    (hsc Q₂ inferInstance c) hproj heq
  exact finitelyPresented_retract p₂ s hs
end

universe u v w
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

lemma finite_orbits_of_cover (T : Set X) (hT : T.Finite)
    (hcov : ∀ x : X, ∃ g : G, g • x ∈ T) : Finite (MulAction.orbitRel.Quotient G X) := by
  classical
  let : Finite T := hT.to_subtype
  apply Finite.of_surjective (fun x : T => (⟦x.val⟧ : MulAction.orbitRel.Quotient G X))
  intro q
  obtain ⟨g,hg⟩ := hcov q.out
  exact ⟨⟨g • q.out,hg⟩,by simp only [MulAction.orbitRel.Quotient.quotient_smul_eq,Quotient.out_eq]⟩

lemma finite_orbits_of_map {Y : Type w} [MulAction G Y]
    [Finite (MulAction.orbitRel.Quotient G Y)] (f : X → Y)
    (heq : ∀ (g : G) x, f (g • x) = g • f x) (hfin : ∀ y, Finite {x // f x = y}) :
    Finite (MulAction.orbitRel.Quotient G X) := by
  classical
  let F := orbitFrames G Y
  let : Finite F.Index := inferInstanceAs (Finite (MulAction.orbitRel.Quotient G Y))
  let (i : F.Index) : Finite {x // f x = F.rep i} := hfin _
  have hs : Function.Surjective (fun z : Σ i : F.Index, {x // f x = F.rep i} =>
      (⟦z.2.val⟧ : MulAction.orbitRel.Quotient G X)) := by
    intro q
    let x := q.out
    let g := F.element (f x)
    have hf : f (g⁻¹ • x) = F.rep (F.index (f x)) := by
      rw [heq,inv_smul_eq_iff]
      exact (F.frame (f x)).symm
    refine ⟨⟨F.index (f x),⟨g⁻¹ • x,hf⟩⟩,?_⟩
    simp only [MulAction.orbitRel.Quotient.quotient_smul_eq]
    exact Quotient.out_eq q
  exact Finite.of_surjective _ hs
end ActionTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisCutBasis
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
lemma sublevel_val_injective (h : ℕ) : Function.Injective (fun B : Sublevel (ρ := ρ) h => B.val.val) := by
  intro B C he
  exact Subtype.ext (ext he)
lemma vertex_finite_orbits (h : ℕ) :
    Finite (MulAction.orbitRel.Quotient (localGroup ρ) (Sublevel (ρ := ρ) h)) := by
  classical
  obtain ⟨R,hR⟩ := rank_finite_orbit_representatives ρ h
  let T : Set (Sublevel (ρ := ρ) h) := (fun B => B.val.val) ⁻¹' (R : Set (Basis ρ))
  have hT : T.Finite := R.finite_toSet.preimage (sublevel_val_injective h).injOn
  apply finite_orbits_of_cover T hT
  intro B
  exact hR B.val.val B.property
lemma edge_finite_orbits (ho : Oligomorphic ρ) (h : ℕ) :
    Finite (MulAction.orbitRel.Quotient (localGroup ρ) (Edge (Sublevel (ρ := ρ) h))) := by
  classical
  obtain ⟨R,hR⟩ := pair_finite_orbit_representatives ρ ho h
  let f : Edge (Sublevel (ρ := ρ) h) → Basis ρ × Basis ρ := fun e => (e.val.1.val.val,e.val.2.val.val)
  have hi : Function.Injective f := by
    intro e d he
    apply Subtype.ext
    exact Prod.ext (sublevel_val_injective h (congrArg Prod.fst he))
      (sublevel_val_injective h (congrArg Prod.snd he))
  apply finite_orbits_of_cover (f ⁻¹' (R : Set (Basis ρ × Basis ρ))) (R.finite_toSet.preimage hi.injOn)
  intro e
  exact hR _ _ e.property e.val.2.property
lemma triangle_finite_orbits (ho : Oligomorphic ρ) (h : ℕ) :
    Finite (MulAction.orbitRel.Quotient (localGroup ρ) (Triangle (Sublevel (ρ := ρ) h))) := by
  let := edge_finite_orbits ho h
  apply finite_orbits_of_map (Triangle.e02 (P := Sublevel (ρ := ρ) h)) (fun _ _ => rfl)
  intro e
  let B := e.val.1.val.val
  let C := e.val.2.val.val
  let := finite_interval ρ B C
  let f : {t : Triangle (Sublevel (ρ := ρ) h) // t.e02 = e} →
      {D : Basis ρ // B ≤ D ∧ D ≤ C} := fun t => ⟨t.val.val.2.1.val.val,by
    have hb := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.1.val.val) t.property
    have hc := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.2.val.val) t.property
    change t.val.val.1.val.val = B at hb
    change t.val.val.2.2.val.val = C at hc
    exact ⟨hb ▸ le_of_cutRefines ρ t.val.property.1,hc ▸ le_of_cutRefines ρ t.val.property.2⟩⟩
  apply Finite.of_injective f
  intro s t he
  apply Subtype.ext
  apply Subtype.ext
  have hp : s.val.e02 = t.val.e02 := s.property.trans t.property.symm
  have ha := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.1) hp
  have hb := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.2) hp
  exact Prod.ext ha (Prod.ext (sublevel_val_injective h (congrArg Subtype.val he)) hb)

lemma sublevel_connected [Nonempty S] (h : ℕ) (hh : 18 ≤ h) : Connected (Sublevel (ρ := ρ) h) := by
  apply connected_of_constant
  intro f hf x y
  let U := rankBelow (fun B : CutBasis ρ => rank ρ B.val) h
  have he := OrderChains.constant_of_exact_zero (CutBasis ρ) (sublevel_exact 0 h (by simpa using hh))
    (fun B => f (OrderChains.project (CutBasis ρ) U x B)) (fun B hB C hC hBC => by
      apply hf
      change (OrderChains.project (CutBasis ρ) U x B).val ≤ (OrderChains.project (CutBasis ρ) U x C).val
      rw [OrderChains.project_val (CutBasis ρ) x hB,OrderChains.project_val (CutBasis ρ) x hC]
      exact hBC)
    x.property y.property
  simpa only [OrderChains.project_include] using he
end TwistedBrin.Basis.CutBasis

namespace FiniteExtension
variable {L : Type*} [Group L] (K : Subgroup L) [K.Normal]
lemma finitelyGenerated [Finite (L ⧸ K)] [Group.FG K] : Group.FG L := by
  classical
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG K)
  let T : Set L := K.subtype '' S ∪ Set.range (sectionMap K)
  have ht : T.Finite := (hfin.image _).union (Set.finite_range _)
  have hK (k : K) : (k : L) ∈ Subgroup.closure T := by
    have hk : k ∈ Subgroup.closure S := by rw [hS]; trivial
    induction hk using Subgroup.closure_induction with
    | mem k hk => exact Subgroup.subset_closure (Or.inl ⟨k,hk,rfl⟩)
    | one => exact (Subgroup.closure T).one_mem
    | mul k l hk hl ik il => exact (Subgroup.closure T).mul_mem ik il
    | inv k hk ik => exact (Subgroup.closure T).inv_mem ik
  have htop : Subgroup.closure T = ⊤ := by
    apply top_le_iff.mp
    intro x hx
    have ht := (Subgroup.closure T).mul_mem (hK (factor K x))
      (Subgroup.subset_closure (Or.inr ⟨pi K x,rfl⟩))
    simpa only [factor,mul_assoc,inv_mul_cancel,mul_one] using ht
  exact Group.fg_iff.mpr ⟨T,htop,ht⟩
end FiniteExtension

namespace TwistedBrin.Basis
open ActionPresentation
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
lemma vertex_finitelyPresented (hρ : Function.Injective ρ) [Group.IsFinitelyPresented A] (B : Basis ρ) :
    Group.IsFinitelyPresented (vertexStabilizer ρ B) := by
  let := finite_pi_finitelyPresented (fun _ : B => A)
  let := Group.IsFinitelyPresented.equiv (vertexKernelEquiv ρ hρ B)
  let := (vertexPermutationHom ρ B).ker.fintypeQuotientOfFiniteIndex
  exact FiniteExtension.finitelyPresented (vertexPermutationHom ρ B).ker
lemma pair_finitelyGenerated (hρ : Function.Injective ρ)
    (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F)) {B C : Basis ρ}
    (hBC : CutRefines ρ B C) : Group.FG (pairStabilizer ρ B C) := by
  let F := hBC.some
  let (b : B) : Group.FG (pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) := hS _
  let e := F.pairKernelEquiv ρ hρ
  let : Group.FG (pairPermutationHom ρ B C).ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  let := (pairPermutationHom ρ B C).ker.fintypeQuotientOfFiniteIndex
  exact FiniteExtension.finitelyGenerated (pairPermutationHom ρ B C).ker
end TwistedBrin.Basis

namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
lemma sublevel_vertex_stabilizer (h : ℕ) (B : Sublevel (ρ := ρ) h) :
    MulAction.stabilizer (localGroup ρ) B = vertexStabilizer ρ B.val.val := by
  ext g
  change (g • B = B) ↔ translate ρ g B.val.val = B.val.val
  exact ⟨fun he => congrArg (fun C : Sublevel (ρ := ρ) h => C.val.val) he,
    fun he => sublevel_val_injective h he⟩
lemma sublevel_edge_stabilizer (h : ℕ) (e : Edge (Sublevel (ρ := ρ) h)) :
    MulAction.stabilizer (localGroup ρ) e = pairStabilizer ρ e.val.1.val.val e.val.2.val.val := by
  ext g
  change (g • e = e) ↔ g ∈ vertexStabilizer ρ e.val.1.val.val ∧ g ∈ vertexStabilizer ρ e.val.2.val.val
  rw [← sublevel_vertex_stabilizer h e.val.1,← sublevel_vertex_stabilizer h e.val.2]
  change (g • e = e) ↔ (g • e.val.1 = e.val.1) ∧ (g • e.val.2 = e.val.2)
  exact ⟨fun he => ⟨congrArg (fun d : Edge (Sublevel (ρ := ρ) h) => d.val.1) he,
    congrArg (fun d : Edge (Sublevel (ρ := ρ) h) => d.val.2) he⟩,
    fun he => Subtype.ext (Prod.ext he.1 he.2)⟩

theorem localGroup_finitelyPresented_oai [Nonempty S] (hρ : Function.Injective ρ)
    (ho : Oligomorphic ρ) [Group.IsFinitelyPresented A]
    (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F)) :
    Group.IsFinitelyPresented (localGroup ρ) := by
  let P := Sublevel (ρ := ρ) 18
  let : Nonempty P := ⟨⟨⟨trivial ρ⟩,by
    change rank ρ (trivial ρ) ≤ 18
    simp [rank,trivial]⟩⟩
  let F := orbitFrames (localGroup ρ) P
  let E := orbitFrames (localGroup ρ) (Edge P)
  let T := orbitFrames (localGroup ρ) (Triangle P)
  let : Finite F.Index := vertex_finite_orbits 18
  let : Finite E.Index := edge_finite_orbits ho 18
  let : Finite T.Index := triangle_finite_orbits ho 18
  apply finitelyPresented_of_frames (sublevel_connected 18 le_rfl)
    (fun R _ c => sublevel_cocycle_trivial 18 le_rfl c) F E T
  · intro i
    change Group.IsFinitelyPresented (MulAction.stabilizer (localGroup ρ) (F.rep i))
    rw [sublevel_vertex_stabilizer]
    exact vertex_finitelyPresented ρ hρ _
  · intro i
    change Group.FG (MulAction.stabilizer (localGroup ρ) (E.rep i))
    rw [sublevel_edge_stabilizer]
    exact pair_finitelyGenerated ρ hρ hS (E.rep i).property
end TwistedBrin.Basis.CutBasis

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented_oai.{u, v} := @OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented_oai.{u, v}

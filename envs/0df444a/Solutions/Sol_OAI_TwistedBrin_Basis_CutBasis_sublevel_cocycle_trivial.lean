-- Prove2me | solution 1 for OAI.TwistedBrin.Basis.CutBasis.sublevel_cocycle_trivial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:03:23.012656+00:00
-- url     : https://prove2.me/submissions/c9ff0d67-62ef-43a7-8602-195d3003d6a1

import Mathlib
import Definitions.Def_OAIQ66So016
import Definitions.Def_OAIQ66So031

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

variable {M : Type*} [AddCommGroup M]
  (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) (T : B → Contraction d aug)

lemma extend_vertex {b : B} (hb : C.degree b = 0) :
    extend C d aug T (Finsupp.single b 1) = (T b).point := by
  rw [extend_single, extendBasis, ite_eq_left hb]

lemma extend_positive {b : B} (hb : C.degree b ≠ 0) :
    extend C d aug T (Finsupp.single b 1) =
      (T b).cone (extend C d aug T (C.d (Finsupp.single b 1))) := by
  rw [extend_single, extendBasis, ite_eq_right hb]
  congr 1
  simp only [extend, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => (C.d (Finsupp.single b 1)) t • extendBasis C d aug T t)

lemma aug_extend (c : B →₀ ℤ) : aug (extend C d aug T c) = C.aug c := by
  have h : aug ∘ₗ extend C d aug T = C.aug := by
    apply Finsupp.lhom_ext
    intro b r
    have hr : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    simp only [LinearMap.comp_apply, hr, LinearMap.map_smul]
    congr 1
    rw [C.aug_single]
    by_cases hb : C.degree b = 0
    · rw [extend_vertex C d aug T hb, (T b).aug_point, ite_eq_left hb]
    · rw [extend_positive C d aug T hb, (T b).aug_cone, ite_eq_right hb]
  exact LinearMap.congr_fun h c

theorem d_extend (c : B →₀ ℤ) : d (extend C d aug T c) = extend C d aug T (C.d c) := by
  have hb (n : ℕ) (b : B) (hn : C.degree b = n) :
      d (extend C d aug T (Finsupp.single b 1)) =
        extend C d aug T (C.d (Finsupp.single b 1)) := by
    induction n using Nat.strong_induction_on generalizing b with
    | h n ih =>
      by_cases hz : C.degree b = 0
      · rw [extend_vertex C d aug T hz, (T b).d_point, d_vertex C hz, map_zero]
      · rw [extend_positive C d aug T hz]
        have hc : d (extend C d aug T (C.d (Finsupp.single b 1))) = 0 := by
          have he := linear_eq_on_support (d ∘ₗ extend C d aug T)
            (extend C d aug T ∘ₗ C.d) (C.d (Finsupp.single b 1)) (by
              intro t ht
              have hd := C.lowers b t ht
              exact ih (C.degree t) (by omega) t rfl)
          simpa only [LinearMap.comp_apply, C.d_squared, map_zero] using he
        have he := (T b).identity (extend C d aug T (C.d (Finsupp.single b 1)))
        simpa only [hc, map_zero, add_zero, aug_extend, C.aug_d, zero_smul, sub_zero] using he
  have h : d ∘ₗ extend C d aug T = extend C d aug T ∘ₗ C.d := by
    apply Finsupp.lhom_ext
    intro b r
    have hr : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    simp only [LinearMap.comp_apply, hr, LinearMap.map_smul, hb (C.degree b) b rfl]
  exact LinearMap.congr_fun h c

theorem extend_mem (K : B → Submodule ℤ M)
    (hpoint : ∀ b, C.degree b = 0 → (T b).point ∈ K b)
    (hcone : ∀ b c, c ∈ K b → (T b).cone c ∈ K b)
    (hface : ∀ b t, t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
    (b : B) : extend C d aug T (Finsupp.single b 1) ∈ K b := by
  suffices ∀ n b, C.degree b = n → extend C d aug T (Finsupp.single b 1) ∈ K b by
    exact this (C.degree b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hn
    by_cases hz : C.degree b = 0
    · rw [extend_vertex C d aug T hz]
      exact hpoint b hz
    · rw [extend_positive C d aug T hz]
      apply hcone
      apply map_mem_of_support
      intro t ht
      apply hface b t ht
      apply ih (C.degree t) _ t rfl
      have hd := C.lowers b t ht
      omega

theorem extend_degree (D : ℕ → Submodule ℤ M)
    (hpoint : ∀ b, C.degree b = 0 → (T b).point ∈ D 0)
    (hcone : ∀ b n c, c ∈ D n → (T b).cone c ∈ D (n+1))
    (b : B) : extend C d aug T (Finsupp.single b 1) ∈ D (C.degree b) := by
  suffices ∀ n b, C.degree b = n → extend C d aug T (Finsupp.single b 1) ∈ D n by
    exact this (C.degree b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hn
    by_cases hz : C.degree b = 0
    · rw [extend_vertex C d aug T hz, ← hn, hz]
      exact hpoint b hz
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have he : n = m+1 := by omega
      rw [extend_positive C d aug T hz, he]
      apply hcone
      apply map_mem_of_support
      intro t ht
      have hd := C.lowers b t ht
      have htdeg : C.degree t = m := by omega
      exact ih m (by omega) t htdeg

variable (F G : (B →₀ ℤ) →ₗ[ℤ] M)

lemma homotopy_equation (b : B) :
    homotopy C d aug T F G (Finsupp.single b 1) =
      (T b).cone (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
        homotopy C d aug T F G (C.d (Finsupp.single b 1))) := by
  rw [homotopy, Finsupp.linearCombination_single, one_smul, homotopyBasis]
  congr 2
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => (C.d (Finsupp.single b 1)) t • homotopyBasis C d aug T F G t)

lemma aug_homotopy (c : B →₀ ℤ) : aug (homotopy C d aug T F G c) = 0 := by
  have he : aug ∘ₗ homotopy C d aug T F G = 0 := by
    apply Finsupp.lhom_ext
    intro b r
    have hr : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hr, LinearMap.map_smul,
      homotopy_equation, (T b).aug_cone, smul_zero]
  exact LinearMap.congr_fun he c

theorem d_homotopy
    (hF : ∀ c, d (F c) = F (C.d c))
    (hG : ∀ c, d (G c) = G (C.d c))
    (haug : ∀ c, aug (F c) = aug (G c)) (c : B →₀ ℤ) :
    d (homotopy C d aug T F G c) + homotopy C d aug T F G (C.d c) = F c - G c := by
  have hb (n : ℕ) (b : B) (hn : C.degree b = n) :
      d (homotopy C d aug T F G (Finsupp.single b 1)) +
        homotopy C d aug T F G (C.d (Finsupp.single b 1)) =
        F (Finsupp.single b 1) - G (Finsupp.single b 1) := by
    induction n using Nat.strong_induction_on generalizing b with
    | h n ih =>
      have hdH : d (homotopy C d aug T F G (C.d (Finsupp.single b 1))) =
          F (C.d (Finsupp.single b 1)) - G (C.d (Finsupp.single b 1)) := by
        have he := linear_eq_on_support
          (d ∘ₗ homotopy C d aug T F G + homotopy C d aug T F G ∘ₗ C.d)
          (F - G) (C.d (Finsupp.single b 1)) (by
            intro t ht
            have hd := C.lowers b t ht
            exact ih (C.degree t) (by omega) t rfl)
        simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
          C.d_squared, map_zero, add_zero] using he
      have hcycle : d (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
          homotopy C d aug T F G (C.d (Finsupp.single b 1))) = 0 := by
        rw [map_sub, map_sub, hF, hG, hdH, sub_self]
      have hzero : aug (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
          homotopy C d aug T F G (C.d (Finsupp.single b 1))) = 0 := by
        rw [map_sub, map_sub, haug, sub_self, aug_homotopy, sub_self]
      have he := (T b).identity (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
          homotopy C d aug T F G (C.d (Finsupp.single b 1)))
      rw [hcycle, map_zero, add_zero, hzero, zero_smul, sub_zero] at he
      rw [homotopy_equation, he]
      abel
  have he : d ∘ₗ homotopy C d aug T F G + homotopy C d aug T F G ∘ₗ C.d = F - G := by
    apply Finsupp.lhom_ext
    intro b r
    have hr : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      hr, LinearMap.map_smul, ← smul_add, ← smul_sub, hb (C.degree b) b rfl]
  exact LinearMap.congr_fun he c

theorem homotopy_degree (D : ℕ → Submodule ℤ M)
    (hF : ∀ b, F (Finsupp.single b 1) ∈ D (C.degree b))
    (hG : ∀ b, G (Finsupp.single b 1) ∈ D (C.degree b))
    (hcone : ∀ b n c, c ∈ D n → (T b).cone c ∈ D (n+1))
    (b : B) : homotopy C d aug T F G (Finsupp.single b 1) ∈ D (C.degree b + 1) := by
  suffices ∀ n b, C.degree b = n →
      homotopy C d aug T F G (Finsupp.single b 1) ∈ D (n+1) by
    exact this (C.degree b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hn
    rw [homotopy_equation]
    apply hcone
    apply (D n).sub_mem
    · exact (D n).sub_mem (hn ▸ hF b) (hn ▸ hG b)
    · apply map_mem_of_support
      intro t ht
      have hd := C.lowers b t ht
      have he : C.degree t + 1 = n := by omega
      rw [← he]
      exact ih (C.degree t) (by omega) t rfl

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

lemma vertex_mem_degreeModule (a : G) : vertex G a ∈ degreeModule G 0 :=
  supported_single G (P := fun s => degree G s = 0) rfl 1

end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsBased
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
variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) (T : B → Contraction d aug)

lemma homotopy_mem_on (F G : (B →₀ ℤ) →ₗ[ℤ] M) (P : B → Prop)
    (hP : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → P t)
    (K : B → Submodule ℤ M)
    (hF : ∀ b, P b → F (Finsupp.single b 1) ∈ K b)
    (hG : ∀ b, P b → G (Finsupp.single b 1) ∈ K b)
    (hcone : ∀ b, P b → ∀ c, c ∈ K b → (T b).cone c ∈ K b)
    (hface : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
    (b : B) (hb : P b) : homotopy C d aug T F G (Finsupp.single b 1) ∈ K b := by
  have help (n : ℕ) : ∀ b, C.degree b = n → P b →
      homotopy C d aug T F G (Finsupp.single b 1) ∈ K b := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hn hp
      rw [homotopy_equation]
      apply hcone b hp
      apply (K b).sub_mem ((K b).sub_mem (hF b hp) (hG b hp))
      apply map_mem_of_support
      intro t ht
      apply hface b t hp ht
      have hlt := C.lowers b t ht
      exact ih (C.degree t) (by omega) t rfl (hP b t hp ht)
  exact help (C.degree b) b rfl hb
end OrderBasedComplex

namespace OrderListChains
variable (V : Type*)

lemma finiteVertices_card_le (s : Simplex V) : (finiteVertices V s).card ≤ degree V s + 1 := by
  classical
  exact List.toFinset_card_le (list V s)
lemma finiteVertices_boundary {s t : Simplex V}
    (ht : t ∈ (boundary V (Finsupp.single s 1)).support) :
    finiteVertices V t ⊆ finiteVertices V s := by
  intro v hv
  rw [mem_finiteVertices] at hv ⊢
  exact boundary_vertices V s t ht hv

end OrderListChains

namespace SteinChains
section
open OrderListChains
variable (V : Type*)

lemma boundary_bary (c : Chain V) : boundary (Face V) (bary V c) = bary V (boundary V c) :=
  OrderBasedComplex.d_extend _ _ _ _ _
lemma augmentation_bary (c : Chain V) : augmentation (Face V) (bary V c) = augmentation V c :=
  OrderBasedComplex.aug_extend _ _ _ _ _
lemma bary_degree {n : ℕ} {c : Chain V} (hc : Homogeneous V n c) :
    Homogeneous (Face V) n (bary V c) := by
  apply OrderBasedComplex.map_mem_of_support (bary V) (degreeModule (Face V) n) c
  intro s hs
  rw [← hc s hs]
  exact OrderBasedComplex.extend_degree _ _ _ _ (degreeModule (Face V))
    (fun _ _ => vertex_mem_degreeModule _ _) (fun _ _ _ h => cone_mem_degreeModule _ _ h) s

lemma faceCarrier_mono {T U : Finset V} (h : T ⊆ U) : faceCarrier V T ≤ faceCarrier V U := by
  intro c hc s hs
  exact ⟨(hc hs).1,fun F hF => ((hc hs).2 F hF).trans h⟩

lemma vertex_mem_faceCarrier (F : Face V) : vertex (Face V) F ∈ faceCarrier V F.val := by
  apply supported_single
  constructor
  · simp [Descending]
  · intro E hE
    have hh : E = F := by simpa [vertices,simplexVertex] using hE
    subst E
    exact Finset.Subset.refl _

lemma cone_mem_faceCarrier (F : Face V) {c : Chain (Face V)}
    (hc : c ∈ faceCarrier V F.val) : cone (Face V) F c ∈ faceCarrier V F.val := by
  apply supported_cone (Face V) (P := fun s => Descending V s ∧
    ∀ E ∈ vertices (Face V) s, E.val ⊆ F.val) (Q := fun s => Descending V s ∧
    ∀ E ∈ vertices (Face V) s, E.val ⊆ F.val) F _ hc
  intro s hs
  constructor
  · change (F :: list (Face V) s).Pairwise _
    rw [List.pairwise_cons]
    exact ⟨fun E hE => hs.2 E ((mem_list _ s E).mp hE),hs.1⟩
  · rw [vertices_cone]
    intro E hE
    rcases hE with rfl | hE
    · exact Finset.Subset.refl _
    · exact hs.2 E hE

lemma bary_mem_faceCarrier (s : Simplex V) :
    bary V (Finsupp.single s 1) ∈ faceCarrier V (finiteVertices V s) := by
  apply OrderBasedComplex.extend_mem _ _ _ _ (fun s => faceCarrier V (finiteVertices V s))
  · intro s _
    exact vertex_mem_faceCarrier V (simplexFace V s)
  · intro s c hc
    exact cone_mem_faceCarrier V (simplexFace V s) hc
  · intro s t ht
    exact faceCarrier_mono V (finiteVertices_boundary V ht)

lemma choose_mem (F : Face V) : choose V F ∈ F.val := F.property.choose_spec

lemma mem_unionFace (s : Simplex (Face V)) (v : V) :
    v ∈ (unionFace V s).val ↔ ∃ F ∈ vertices (Face V) s, v ∈ F.val := by
  classical
  simp only [unionFace,Finset.mem_biUnion,mem_finiteVertices]

lemma face_subset_unionFace (s : Simplex (Face V)) (F : Face V)
    (hF : F ∈ vertices (Face V) s) : F.val ⊆ (unionFace V s).val :=
  fun _ hv => (mem_unionFace V s _).mpr ⟨F,hF,hv⟩

lemma unionFace_mono {s t : Simplex (Face V)}
    (h : vertices (Face V) s ⊆ vertices (Face V) t) :
    (unionFace V s).val ⊆ (unionFace V t).val := by
  intro v hv
  obtain ⟨F,hF,hv⟩ := (mem_unionFace V s v).mp hv
  exact (mem_unionFace V t v).mpr ⟨F,h hF,hv⟩

lemma Descending.face_le_head {s : Simplex (Face V)} (h : Descending V s)
    {F : Face V} (hF : F ∈ vertices (Face V) s) : F ≤ s.1 := by
  rcases hF with rfl | hF
  · exact le_refl _
  · exact (List.pairwise_cons.mp h).1 F hF

lemma Descending.unionFace_eq {s : Simplex (Face V)} (h : Descending V s) :
    unionFace V s = s.1 := by
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨F,hF,hv⟩ := (mem_unionFace V s v).mp hv
    exact h.face_le_head V hF hv
  · exact face_subset_unionFace V s s.1 (head_mem_vertices _ _)

lemma Descending.boundary {s t : Simplex (Face V)} (h : Descending V s)
    (ht : t ∈ (boundary (Face V) (Finsupp.single s 1)).support) : Descending V t :=
  h.sublist (boundary_sublist (Face V) s t ht)

lemma selected_vertices_subset (s : Simplex (Face V)) :
    finiteVertices V (choose V s.1,s.2.map (choose V)) ⊆ (unionFace V s).val := by
  intro v hv
  rw [mem_finiteVertices] at hv
  rcases hv with rfl | hv
  · exact face_subset_unionFace V s s.1 (head_mem_vertices _ _) (choose_mem V _)
  · obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hv
    exact face_subset_unionFace V s F (Or.inr hF) (choose_mem V _)

lemma barySelect_mem_carrier (s : Simplex (Face V)) :
    barySelect V (Finsupp.single s 1) ∈ faceCarrier V (unionFace V s).val := by
  change bary V (mapChain _ _ (Finsupp.single s 1)) ∈ _
  rw [mapChain_single]
  exact faceCarrier_mono V (selected_vertices_subset V s) (bary_mem_faceCarrier V _)

lemma boundary_backHomotopy (c : Chain (Face V)) :
    boundary (Face V) (backHomotopy V c) + backHomotopy V (boundary (Face V) c) =
      c - barySelect V c := by
  apply OrderBasedComplex.d_homotopy
  · intro d; rfl
  · intro d
    change boundary _ (bary V (mapChain _ _ d)) = bary V (mapChain _ _ (boundary _ d))
    rw [boundary_bary,boundary_mapChain]
  · intro d
    change augmentation _ d = augmentation _ (bary V (mapChain _ _ d))
    rw [augmentation_bary,augmentation_mapChain]

lemma backHomotopy_mem_carrier {s : Simplex (Face V)} (hs : Descending V s) :
    backHomotopy V (Finsupp.single s 1) ∈ faceCarrier V (unionFace V s).val := by
  apply OrderBasedComplex.homotopy_mem_on (based (Face V)) (boundary (Face V))
    (augmentation (Face V)) (fun s => contraction (Face V) (unionFace V s))
    LinearMap.id (barySelect V) (Descending V)
    (fun _ _ h ht => h.boundary V ht) (fun s => faceCarrier V (unionFace V s).val)
    _ _ _ _ s hs
  · intro s hs
    apply supported_single
    exact ⟨hs,fun F hF => face_subset_unionFace V s F hF⟩
  · intro s _
    exact barySelect_mem_carrier V s
  · intro s _ c hc
    exact cone_mem_faceCarrier V (unionFace V s) hc
  · intro s t _ ht
    exact faceCarrier_mono V (unionFace_mono V (boundary_vertices (Face V) s t ht))

lemma select_degree {n : ℕ} {c : Chain (Face V)} (hc : Homogeneous (Face V) n c) :
    Homogeneous V n (select V c) := by
  apply supported_linearMap (Face V) (P := fun s => degree (Face V) s = n)
    (Q := fun s => degree V s = n) (select V) _ hc
  intro s hs
  change Supported V _ (mapChain _ _ (Finsupp.single s 1))
  rw [mapChain_single]
  apply supported_single
  simpa [degree] using hs

lemma backHomotopy_degree {n : ℕ} {c : Chain (Face V)} (hc : Homogeneous (Face V) n c) :
    Homogeneous (Face V) (n+1) (backHomotopy V c) := by
  apply OrderBasedComplex.map_mem_of_support (backHomotopy V) (degreeModule (Face V) (n+1)) c
  intro s hs
  rw [← hc s hs]
  apply OrderBasedComplex.homotopy_degree (based (Face V)) (boundary (Face V))
    (augmentation (Face V)) (fun s => contraction (Face V) (unionFace V s))
    LinearMap.id (barySelect V) (degreeModule (Face V))
  · intro t
    exact supported_single (Face V) (P := fun s => degree (Face V) s = degree (Face V) t) rfl 1
  · intro t
    apply bary_degree
    apply select_degree
    exact supported_single (Face V) (P := fun s => degree (Face V) s = degree (Face V) t) rfl 1
  · intro t n d hd
    exact cone_mem_degreeModule _ _ hd
end

open OrderListChains
variable (V : Type*)

namespace Complex
variable (K : Complex V)

lemma carrier_le {F : Finset V} (hF : F ∈ K.faces) :
    faceCarrier V F ≤ K.faceModule V := by
  intro c hc s hs
  exact ⟨(hc hs).1,fun E hE => K.down hF ((hc hs).2 E hE)⟩

lemma bary_mem {c : Chain V} (hc : c ∈ K.tupleModule V) :
    bary V c ∈ K.faceModule V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  exact K.carrier_le V (hc hs) (bary_mem_faceCarrier V s)

lemma unionFace_mem {s : Simplex (Face V)}
    (hs : Descending V s ∧ ∀ F ∈ vertices (Face V) s, F.val ∈ K.faces) :
    (unionFace V s).val ∈ K.faces := by
  rw [hs.1.unionFace_eq V]
  exact hs.2 _ (head_mem_vertices _ _)

lemma select_mem {c : Chain (Face V)} (hc : c ∈ K.faceModule V) :
    select V c ∈ K.tupleModule V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  change Supported V _ (mapChain _ _ (Finsupp.single s 1))
  rw [mapChain_single]
  exact supported_single V (K.down (K.unionFace_mem V (hc hs))
    (selected_vertices_subset V s)) 1

lemma backHomotopy_mem {c : Chain (Face V)} (hc : c ∈ K.faceModule V) :
    backHomotopy V c ∈ K.faceModule V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  exact K.carrier_le V (K.unionFace_mem V (hc hs))
    (backHomotopy_mem_carrier V (hc hs).1)

theorem face_cycle_bounds {n : ℕ}
    (hfill : ∀ c : Chain V, c ∈ K.tupleModule V → Homogeneous V n c →
      boundary V c = 0 → augmentation V c = 0 →
      ∃ d : Chain V, d ∈ K.tupleModule V ∧ Homogeneous V (n+1) d ∧ boundary V d = c)
    {c : Chain (Face V)} (hc : c ∈ K.faceModule V)
    (hn : Homogeneous (Face V) n c) (hd : boundary (Face V) c = 0)
    (ha : augmentation (Face V) c = 0) :
    ∃ d : Chain (Face V), d ∈ K.faceModule V ∧ Homogeneous (Face V) (n+1) d ∧
      boundary (Face V) d = c := by
  have hsd : boundary V (select V c) = 0 := by
    change boundary V (mapChain _ _ c) = 0
    rw [boundary_mapChain,hd,map_zero]
  have hsa : augmentation V (select V c) = 0 := by
    change augmentation V (mapChain _ _ c) = 0
    rw [augmentation_mapChain,ha]
  obtain ⟨d,hdK,hdn,hdd⟩ := hfill (select V c) (K.select_mem V hc)
    (select_degree V hn) hsd hsa
  refine ⟨backHomotopy V c + bary V d,
    (K.faceModule V).add_mem (K.backHomotopy_mem V hc) (K.bary_mem V hdK),
    supported_add _ (backHomotopy_degree V hn) (bary_degree V hdn),?_⟩
  have hH := boundary_backHomotopy V c
  rw [hd,map_zero,add_zero] at hH
  rw [map_add,hH,boundary_bary,hdd]
  change c - barySelect V c + barySelect V c = c
  abel
end Complex

open Classical in
lemma finiteVertices_cone (v : V) (s : Simplex V) :
    finiteVertices V (simplexCone V v s) = insert v (finiteVertices V s) := by
  classical
  ext w
  simp only [mem_finiteVertices,vertices_cone,Set.mem_insert_iff,Finset.mem_insert]

lemma cone_mem_boundary {T : Finset V} {v : V} (hv : v ∈ T) {n : ℕ}
    (hn : n+2 < T.card) {c : Chain V}
    (hc : c ∈ (boundaryComplex V T).tupleModule V) (hd : Homogeneous V n c) :
    cone V v c ∈ (boundaryComplex V T).tupleModule V := by
  classical
  change Supported V (fun s => finiteVertices V s ⊆ T ∧ (finiteVertices V s).card < T.card) (cone V v c)
  refine supported_cone V (P := fun s => finiteVertices V s ⊆ T ∧ degree V s = n)
    (Q := fun s => finiteVertices V s ⊆ T ∧ (finiteVertices V s).card < T.card) v ?_ ?_
  · intro s hs
    rw [finiteVertices_cone]
    refine ⟨Finset.insert_subset hv hs.1,?_⟩
    have hcard := Finset.card_insert_le v (finiteVertices V s)
    have hb := finiteVertices_card_le V s
    rw [hs.2] at hb
    omega
  · intro s hs
    exact ⟨(hc hs).1,hd s hs⟩

theorem boundary_face_cycle_bounds {T : Finset V} {n : ℕ} (hn : n+2 < T.card)
    {c : Chain (Face V)} (hc : c ∈ (boundaryComplex V T).faceModule V)
    (hd : Homogeneous (Face V) n c) (hz : boundary (Face V) c = 0)
    (ha : augmentation (Face V) c = 0) :
    ∃ d : Chain (Face V), d ∈ (boundaryComplex V T).faceModule V ∧
      Homogeneous (Face V) (n+1) d ∧ boundary (Face V) d = c := by
  apply Complex.face_cycle_bounds V (boundaryComplex V T) _ hc hd hz ha
  intro c hc hd hz ha
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  refine ⟨cone V v c,cone_mem_boundary V hv hn hc hd,cone_mem_degreeModule V v hd,?_⟩
  rw [boundary_cone,hz,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]

end SteinChains

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
lemma carrier_mono {x y : P} (h : x ≤ y) : carrier P x ≤ carrier P y :=
  fun _ hc _ hs => ⟨(hc hs).1,fun v hv => ((hc hs).2 v hv).trans h⟩
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

variable {Q : Type*} [Preorder Q]
lemma comparison_boundary (f g : P →o Q) (c : Chain P) :
    boundary Q (comparison P f g c) + comparison P f g (boundary P c) =
      mapChain P f c - mapChain P g c := by
  apply OrderBasedComplex.d_homotopy
  · exact fun c => boundary_mapChain P f c
  · exact fun c => boundary_mapChain P g c
  · intro c
    rw [augmentation_mapChain,augmentation_mapChain]
lemma comparison_mem (f g : P →o Q) (hfg : ∀ x, f x ≤ g x)
    {c : Chain P} (hc : c ∈ module P) : comparison P f g c ∈ module Q := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  apply carrier_le_module Q (g s.1)
  apply OrderBasedComplex.homotopy_mem_on (based P) (boundary Q) (augmentation Q)
    (fun s => contraction Q (g s.1)) (mapChain P f) (mapChain P g) (Descending P)
    (fun _ _ h ht => h.boundary P ht) (fun s => carrier Q (g s.1))
    _ _ _ _ s (hc hs)
  · intro s hs
    exact hs.map_carrier P f g hfg
  · intro s hs
    exact hs.map_carrier P g g (fun _ => le_rfl)
  · intro s _ c hc
    exact cone_carrier Q (g s.1) hc
  · intro s t hs ht
    exact carrier_mono Q (g.monotone (hs.le_head P
      (boundary_vertices P s t ht (head_mem_vertices P t))))
lemma comparison_degree (f g : P →o Q) {n : ℕ} {c : Chain P} (hc : Homogeneous P n c) :
    Homogeneous Q (n+1) (comparison P f g c) := by
  apply OrderBasedComplex.map_mem_of_support (comparison P f g) (degreeModule Q (n+1)) c
  intro s hs
  rw [← hc s hs]
  apply OrderBasedComplex.homotopy_degree (based P) (boundary Q) (augmentation Q)
    (fun s => contraction Q (g s.1)) (mapChain P f) (mapChain P g) (degreeModule Q)
  · intro s
    exact map_degree P f (supported_single P (P := fun t => degree P t = degree P s) rfl 1)
  · intro s
    exact map_degree P g (supported_single P (P := fun t => degree P t = degree P s) rfl 1)
  · intro s n c hc
    exact cone_mem_degreeModule Q _ hc

lemma mapChain_comp (P : Type*) [Preorder P] {Q : Type*} [Preorder Q]
    {R : Type*} (f : P → Q) (g : Q → R) (c : Chain P) :
    mapChain Q g (mapChain P f c) = mapChain P (g ∘ f) c := by
  have h : (mapChain Q g).comp (mapChain P f) = mapChain P (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply,mapChain_single,List.map_map,Function.comp_apply]
  exact LinearMap.congr_fun h c
lemma mapChain_id (P : Type*) [Preorder P] (c : Chain P) : mapChain P id c = c := by
  have h : mapChain P id = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [mapChain_single,id_eq,List.map_id,LinearMap.id_coe]
  exact LinearMap.congr_fun h c

theorem exactIn_of_comparison (i : Q →o P) (r : P →o Q)
    (hir : ∀ x, i (r x) ≤ x) {n : ℕ} (h : ExactIn Q n) : ExactIn P n := by
  intro c hc hn hd ha
  have hrd : boundary Q (mapChain P r c) = 0 := by
    rw [boundary_mapChain,hd,map_zero]
  have hra : augmentation Q (mapChain P r c) = 0 := by rw [augmentation_mapChain,ha]
  obtain ⟨d,hdQ,hdn,hdd⟩ := h (mapChain P r c) (map_mem P r hc) (map_degree P r hn) hrd hra
  let f := i.comp r
  refine ⟨mapChain Q i d - comparison P f OrderHom.id c,
    (module P).sub_mem (map_mem Q i hdQ) (comparison_mem P f OrderHom.id hir hc),
    supported_sub P (map_degree Q i hdn) (comparison_degree P f OrderHom.id hn),?_⟩
  have hH := comparison_boundary P f OrderHom.id c
  rw [hd,map_zero,add_zero] at hH
  rw [map_sub,boundary_mapChain,hdd,hH,mapChain_comp]
  have he : mapChain P (OrderHom.id : P →o P) c = c := mapChain_id P c
  rw [he]
  change mapChain P (i ∘ r) c - (mapChain P (i ∘ r) c - c) = c
  abel
end

open OrderListChains
variable {P Q : Type*} [Preorder P] [Preorder Q]
lemma exactIn_of_orderIso (e : P ≃o Q) {n : ℕ} (h : ExactIn Q n) : ExactIn P n :=
  exactIn_of_comparison P ⟨e.symm,e.symm.monotone⟩ ⟨e,e.monotone⟩ (fun x => le_of_eq (e.symm_apply_apply x)) h
end OrderChains

namespace SteinChains
open OrderListChains
variable (V : Type*) [Fintype V]

lemma properProject_val (v : V) (hv : 1 < Fintype.card V) (F : Face V)
    (hF : F.val ≠ Finset.univ) : (properProject V v hv F).val = F.val := by
  classical
  simp [properProject, hF]
lemma project_include (v : V) (hv : 1 < Fintype.card V) (F : ProperFace V) :
    properProject V v hv (properInclude V F) = F := by
  apply Subtype.ext
  exact properProject_val V v hv _ F.property.2

lemma properInclude_mem {c : Chain (ProperFace V)} (hc : c ∈ OrderChains.module (ProperFace V)) :
    mapChain (ProperFace V) (properInclude V) c ∈ (boundaryComplex V Finset.univ).faceModule V := by
  classical
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  rw [mapChain_single]
  apply supported_single
  refine ⟨OrderChains.Descending.map _ (properInclude V) (hc hs),?_⟩
  intro F hF
  have hproper (E : ProperFace V) : (properInclude V E).val ⊆ Finset.univ ∧
      (properInclude V E).val.card < Finset.univ.card :=
    ⟨Finset.subset_univ _,Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,E.property.2⟩)⟩
  rcases hF with rfl | hF
  · exact hproper s.1
  · obtain ⟨E,_,rfl⟩ := List.mem_map.mp hF
    exact hproper E

lemma properProject_mem (v : V) (hv : 1 < Fintype.card V) {c : Chain (Face V)}
    (hc : c ∈ (boundaryComplex V Finset.univ).faceModule V) :
    mapChain (Face V) (properProject V v hv) c ∈ OrderChains.module (ProperFace V) := by
  classical
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  rw [mapChain_single]
  apply supported_single
  change ((list (Face V) s).map (properProject V v hv)).Pairwise _
  rw [List.pairwise_map]
  apply (hc hs).1.imp_of_mem
  intro F E hF hE hEF
  change (properProject V v hv E).val ⊆ (properProject V v hv F).val
  have hne (D : Face V) (hD : D ∈ list (Face V) s) : D.val ≠ Finset.univ := by
    have hh := ((hc hs).2 D ((mem_list _ s D).mp hD)).2
    intro he
    rw [he] at hh
    exact (lt_irrefl _ hh)
  rw [properProject_val V v hv E (hne E hE),properProject_val V v hv F (hne F hF)]
  exact hEF

theorem properFace_exactIn {n : ℕ} (hn : n+2 < Fintype.card V) :
    OrderChains.ExactIn (ProperFace V) n := by
  classical
  have hv : 1 < Fintype.card V := by omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  intro c hc hcdeg hcd hca
  let e := properInclude V
  have hz : boundary (Face V) (mapChain _ e c) = 0 := by rw [boundary_mapChain,hcd,map_zero]
  have ha : augmentation (Face V) (mapChain _ e c) = 0 := by rw [augmentation_mapChain,hca]
  obtain ⟨d,hdK,hdn,hdd⟩ := boundary_face_cycle_bounds V
    (T := Finset.univ) (by simpa only [Finset.card_univ] using hn)
    (properInclude_mem V hc) (OrderChains.map_degree _ e hcdeg) hz ha
  refine ⟨mapChain (Face V) (properProject V v hv) d,properProject_mem V v hv hdK,
    OrderChains.map_degree _ _ hdn,?_⟩
  rw [boundary_mapChain,hdd,OrderChains.mapChain_comp]
  have he : properProject V v hv ∘ e = id := funext (project_include V v hv)
  rw [he,OrderChains.mapChain_id]
end SteinChains

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
namespace OrderChains
open OrderListChains
variable (P : Type*) [Preorder P]
theorem exactIn_of_top (t : P) (ht : ∀ x, x ≤ t) (n : ℕ) : ExactIn P n := by
  intro c hc hn hd ha
  have hct : c ∈ carrier P t := fun _ hs => ⟨hc hs,fun v _ => ht v⟩
  refine ⟨cone P t c,carrier_le_module P t (cone_carrier P t hct),
    cone_mem_degreeModule P t hn,?_⟩
  rw [boundary_cone,hd,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]
end OrderChains

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
lemma onSet_le_module (U : Set P) : onSet P U ≤ module P :=
  fun _ hc _ hs => (hc hs).1
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

namespace OrderChains

section
open OrderListChains
variable (P : Type*) [Preorder P] {Q : Type*} [Preorder Q]

theorem exactIn_of_upper_comparison (i : Q →o P) (r : P →o Q)
    (hir : ∀ x, x ≤ i (r x)) {n : ℕ} (h : ExactIn Q n) : ExactIn P n := by
  intro c hc hn hd ha
  have hrd : boundary Q (mapChain P r c) = 0 := by rw [boundary_mapChain,hd,map_zero]
  have hra : augmentation Q (mapChain P r c) = 0 := by rw [augmentation_mapChain,ha]
  obtain ⟨d,hdQ,hdn,hdd⟩ := h (mapChain P r c) (map_mem P r hc) (map_degree P r hn) hrd hra
  let f := i.comp r
  refine ⟨mapChain Q i d + comparison P OrderHom.id f c,
    (module P).add_mem (map_mem Q i hdQ) (comparison_mem P OrderHom.id f hir hc),
    supported_add P (map_degree Q i hdn) (comparison_degree P OrderHom.id f hn),?_⟩
  have hH := comparison_boundary P OrderHom.id f c
  rw [hd,map_zero,add_zero] at hH
  rw [map_add,boundary_mapChain,hdd,hH,mapChain_comp]
  have he : mapChain P (OrderHom.id : P →o P) c = c := mapChain_id P c
  rw [he]
  change mapChain P (i ∘ r) c + (c - mapChain P (i ∘ r) c) = c
  abel

theorem exactIn_of_bottom (b : P) (hb : ∀ x, b ≤ x) (n : ℕ) : ExactIn P n := by
  let i : PUnit.{1} →o P := ⟨fun _ => b,fun _ _ _ => le_rfl⟩
  let r : P →o PUnit.{1} := ⟨fun _ => PUnit.unit,fun _ _ _ => le_rfl⟩
  exact exactIn_of_comparison P i r hb (exactIn_of_top _ PUnit.unit (fun _ => le_rfl) n)

end

open OrderListChains
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinRangeChartRestricts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
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

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Basis.Merge
variable {C : Basis ρ}

lemma germ_mem_lower_iff (m : Merge ρ C) (g : GermBrick ρ) :
    g ∈ m.lower.pieces ↔ g = GermBrick.mk ρ m.joined ∨
      (g ∈ C.pieces ∧ g ≠ m.first.val ∧ g ≠ m.second.val) := by
  classical
  change g ∈ Finset.univ.image (fun r : m.Roots => GermBrick.mk ρ (m.rootChart r)) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨r,_,hr⟩
    cases r with
    | none => exact Or.inl hr.symm
    | some c =>
      have he : c.val.val = g := (chart_germ ρ C c.val).symm.trans hr
      refine Or.inr ⟨he ▸ c.val.property,?_,?_⟩
      · intro h; exact c.property.1 (Subtype.ext (he.trans h))
      · intro h; exact c.property.2 (Subtype.ext (he.trans h))
  · rintro (hg | ⟨hg,hf,hs⟩)
    · exact ⟨none,Finset.mem_univ _,hg.symm⟩
    · let c : C := ⟨g,hg⟩
      have hc : c ≠ m.first ∧ c ≠ m.second :=
        ⟨fun h => hf (congrArg Subtype.val h),fun h => hs (congrArg Subtype.val h)⟩
      exact ⟨some ⟨c,hc⟩,Finset.mem_univ _,chart_germ ρ C c⟩

end Basis.Merge
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPattern
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
namespace TwistedBrin.Pattern
variable {S : Type u}

lemma pruning_exists (P : Pattern S) (hP : P ≠ leaf) : Nonempty (Pruning P) := by
  induction P with
  | leaf => exact False.elim (hP rfl)
  | split s P Q ihP ihQ =>
    by_cases hp : P = leaf
    · subst P
      by_cases hq : Q = leaf
      · subst Q
        exact ⟨{
          shorter := leaf
          stem := Prefix.empty
          coordinate := s
          first := Sum.inl ()
          second := Sum.inr ()
          distinct := Sum.inl_ne_inr
          first_prefix := by simp [leafPrefix]
          second_prefix := by simp [leafPrefix]
          remaining := fun _ => Or.inl rfl }⟩
      · obtain ⟨T⟩ := ihQ hq
        refine ⟨{
          shorter := split s leaf T.shorter
          stem := (Prefix.cut s true).append T.stem
          coordinate := T.coordinate
          first := Sum.inr T.first
          second := Sum.inr T.second
          distinct := fun he => T.distinct (Sum.inr.inj he)
          first_prefix := ?_
          second_prefix := ?_
          remaining := ?_ }⟩
        · change (Prefix.cut s true).append (leafPrefix Q T.first) = _
          rw [T.first_prefix,Prefix.append_assoc]
        · change (Prefix.cut s true).append (leafPrefix Q T.second) = _
          rw [T.second_prefix,Prefix.append_assoc]
        · intro i
          cases i with
          | inl i =>
            exact Or.inr ⟨Sum.inl i,rfl,Sum.inl_ne_inr,Sum.inl_ne_inr⟩
          | inr i =>
            rcases T.remaining i with he | ⟨j,hj,hf,hs⟩
            · exact Or.inl (congrArg (Prefix.append (Prefix.cut s true)) he)
            · exact Or.inr ⟨Sum.inr j,congrArg (Prefix.append (Prefix.cut s true)) hj,
                fun h => hf (Sum.inr.inj h),fun h => hs (Sum.inr.inj h)⟩
    · obtain ⟨T⟩ := ihP hp
      refine ⟨{
        shorter := split s T.shorter Q
        stem := (Prefix.cut s false).append T.stem
        coordinate := T.coordinate
        first := Sum.inl T.first
        second := Sum.inl T.second
        distinct := fun he => T.distinct (Sum.inl.inj he)
        first_prefix := ?_
        second_prefix := ?_
        remaining := ?_ }⟩
      · change (Prefix.cut s false).append (leafPrefix P T.first) = _
        rw [T.first_prefix,Prefix.append_assoc]
      · change (Prefix.cut s false).append (leafPrefix P T.second) = _
        rw [T.second_prefix,Prefix.append_assoc]
      · intro i
        cases i with
        | inl i =>
          rcases T.remaining i with he | ⟨j,hj,hf,hs⟩
          · exact Or.inl (congrArg (Prefix.append (Prefix.cut s false)) he)
          · exact Or.inr ⟨Sum.inl j,congrArg (Prefix.append (Prefix.cut s false)) hj,
              fun h => hf (Sum.inl.inj h),fun h => hs (Sum.inl.inj h)⟩
        | inr i =>
          exact Or.inr ⟨Sum.inr i,rfl,Sum.inr_ne_inl,Sum.inr_ne_inl⟩

end TwistedBrin.Pattern

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Basis.Forest
variable {B C : Basis ρ}

lemma cutRefines_pruned (F : Forest ρ B C) (b : B) (T : Pattern.Pruning (F.pattern b)) :
    CutRefines ρ B (F.prunedMerge b T).lower := by
  classical
  let m := F.prunedMerge b T
  let Q := Function.update F.pattern b T.shorter
  have hmem (i : F.Index) (hf : i ≠ ⟨b,T.first⟩) (hs : i ≠ ⟨b,T.second⟩) :
      GermBrick.mk ρ (expandedChart ρ B F.pattern i) ∈ m.lower.pieces := by
    rw [F.chart_eq]
    apply (m.germ_mem_lower_iff _).mpr
    refine Or.inr ⟨(F.leaves i).property,?_,?_⟩
    · intro he
      exact hf (F.leaves.injective (Subtype.ext he))
    · intro he
      exact hs (F.leaves.injective (Subtype.ext he))
  apply Nonempty.intro
  apply Forest.of_mem ρ Q
  rintro ⟨c,j⟩
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B c)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (Q c) j))) ∈ m.lower.pieces
  by_cases hc : c = b
  · subst c
    have hT (R : Pattern S) (hR : R = T.shorter) (i : Pattern.Leaves R) :
        GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
          (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix R i))) ∈ m.lower.pieces := by
      subst R
      rcases T.remaining i with he | ⟨k,hk,hf,hs⟩
      · rw [he]
        exact (m.germ_mem_lower_iff _).mpr (Or.inl rfl)
      · rw [hk]
        exact hmem ⟨b,k⟩ (by
          intro h; exact hf (by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h)) (by
          intro h; exact hs (by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h))
    exact hT (Q b) (Function.update_self b T.shorter F.pattern) j
  · have hT (R : Pattern S) (hR : R = F.pattern c) (i : Pattern.Leaves R) :
        GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B c)
          (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix R i))) ∈ m.lower.pieces := by
      subst R
      exact hmem ⟨c,i⟩ (fun h => hc (congrArg Sigma.fst h))
        (fun h => hc (congrArg Sigma.fst h))
    exact hT (Q c) (Function.update_of_ne hc T.shorter F.pattern) j

lemma exists_last_merge (F : Forest ρ B C) (hne : B ≠ C) :
    ∃ m : Merge ρ C, CutRefines ρ B m.lower := by
  classical
  have hn : ∃ b, F.pattern b ≠ .leaf := by
    by_contra h
    exact hne (F.eq_of_all_leaf (by simpa only [not_exists,not_not] using h))
  obtain ⟨b,hb⟩ := hn
  obtain ⟨T⟩ := Pattern.pruning_exists (F.pattern b) hb
  exact ⟨F.prunedMerge b T,F.cutRefines_pruned b T⟩

end Basis.Forest
end

end TwistedBrin

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
namespace TwistedBrin.Pattern
section
variable {S : Type u}

lemma uniform_card (L : List S) : Fintype.card (Leaves (uniform L)) = 2 ^ L.length := by
  induction L with
  | nil => change Fintype.card Unit = 1; exact Fintype.card_unique
  | cons s L ih =>
    change Fintype.card (Leaves (uniform L) ⊕ Leaves (uniform L)) = _
    rw [Fintype.card_sum,ih]
    simp [List.length_cons,pow_succ,Nat.mul_two]

end

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma rank_gridExpansion (B : Basis ρ) (K : B → Finset S) :
    rank ρ (gridExpansion ρ B K) = ∑ b : B, 2 ^ (K b).card := by
  rw [gridExpansion,rank_expand]
  simp_rw [Pattern.uniform_card,Finset.length_toList]

end TwistedBrin.Basis

namespace TwistedBrin.Basis

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace CutInterval
variable {ρ} {B C : Basis ρ}
lemma core_le (D : CutInterval ρ B C) : D.core ≤ D := firstCore_upper ρ D.lower
end CutInterval

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisFirstCut
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder
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
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma grid_rank_bound (B : Basis ρ) (K : B → Finset S) :
    rank ρ (gridExpansion ρ B K) + 1 ≤ rank ρ B + 2 ^ (∑ b : B, (K b).card) := by
  classical
  have bound : ∀ (t : Finset B), (∑ b ∈ t, 2 ^ (K b).card) + 1 ≤
      t.card + 2 ^ (∑ b ∈ t, (K b).card) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert b t hb ih =>
      rw [Finset.sum_insert hb,Finset.sum_insert hb,Finset.card_insert_of_notMem hb,
        Nat.pow_add]
      have hp : 1 ≤ 2 ^ (K b).card := Nat.one_le_pow _ _ (by omega)
      have hq : 1 ≤ 2 ^ (∑ x ∈ t, (K x).card) := Nat.one_le_pow _ _ (by omega)
      nlinarith
  rw [rank_gridExpansion,rank_eq_card]
  simpa only [Finset.card_univ] using bound Finset.univ

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)
lemma proper_to_of (D : ProperCutInterval ρ B C) :
    properToInterval h (properOfInterval h D) = properCore ρ D :=
  Subtype.ext (to_of h D.val)

end CutSelections
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactInOfDirected
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder
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
namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
lemma firstCut_card {B C : Basis ρ} (h : CutRefines ρ B C) :
    Fintype.card (FirstCut ρ h) = ∑ b : B, (firstCuts ρ h b).card := by
  classical
  unfold FirstCut
  simp only [Fintype.card_sigma,Fintype.card_coe]

lemma firstCut_nonempty {B C : Basis ρ} (h : CutRefines ρ B C) (hne : B ≠ C) :
    Nonempty (FirstCut ρ h) := by
  classical
  by_contra hn
  have he : firstCuts ρ h = fun _ => ∅ := by
    funext b
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    exact hn ⟨⟨b,⟨s,hs⟩⟩⟩
  apply firstCore_ne ρ h hne
  change gridExpansion ρ B (firstCuts ρ h) = B
  rw [he,gridExpansion_empty]

lemma firstCut_rank_bound {B C : Basis ρ} (h : CutRefines ρ B C)
    (htop : firstCore ρ h = C) :
    rank ρ C + 1 ≤ rank ρ B + 2 ^ Fintype.card (FirstCut ρ h) := by
  rw [firstCut_card]
  have hh := grid_rank_bound ρ B (firstCuts ρ h)
  change rank ρ (firstCore ρ h) + 1 ≤ _ at hh
  simpa only [htop] using hh

theorem properCutInterval_exactIn {B C : Basis ρ} (h : CutRefines ρ B C)
    (hne : B ≠ C) {n : ℕ}
    (hrank : rank ρ B + 2 ^ (n+2) ≤ rank ρ C) :
    OrderChains.ExactIn (ProperCutInterval ρ B C) n := by
  classical
  apply OrderChains.exactIn_of_comparison _ (CutSelections.properToInterval h)
    (CutSelections.properOfInterval h)
  · intro D
    rw [CutSelections.proper_to_of]
    exact D.val.core_le
  · by_cases htop : firstCore ρ h = C
    · apply OrderChains.exactIn_of_orderIso (CutSelections.properBooleanBoundary h htop)
      apply SteinChains.properFace_exactIn
      have hb := firstCut_rank_bound ρ h htop
      have hp : 2 ^ (n+2) < 2 ^ Fintype.card (FirstCut ρ h) := by omega
      by_contra hn
      have hh := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega :
        Fintype.card (FirstCut ρ h) ≤ n+2)
      omega
    · apply OrderChains.exactIn_of_orderIso (CutSelections.properBooleanFaces h htop)
      let := firstCut_nonempty ρ h hne
      apply OrderChains.exactIn_of_top _ ⟨Finset.univ,Finset.univ_nonempty.ne_empty⟩
      intro F
      exact Finset.subset_univ _
end

universe w
end TwistedBrin.Basis

namespace TwistedBrin.Pattern
variable {S : Type u}
lemma card_leaves_ge_two {P : Pattern S} (h : P ≠ .leaf) :
    2 ≤ Fintype.card (Leaves P) := by
  cases P with
  | leaf => exact False.elim (h rfl)
  | split s P Q =>
    change 2 ≤ Fintype.card (Leaves P ⊕ Leaves Q)
    rw [Fintype.card_sum]
    have hP := Fintype.card_pos (α := Leaves P)
    have hQ := Fintype.card_pos (α := Leaves Q)
    omega
end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Forest
variable {B C : Basis ρ}

lemma leaf_root_eq (F : Forest ρ B C) (b : B) (h : F.pattern b = .leaf)
    (j : Pattern.Leaves (F.pattern b)) : (F.leaves ⟨b,j⟩).val = b.val := by
  rw [← F.chart_eq ⟨b,j⟩]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (F.pattern b) j))) = b.val
  have hp : Pattern.leafPrefix (F.pattern b) j = Prefix.empty := by
    revert j
    rw [h]
    intro j
    rfl
  rw [hp,LocalEmbedding.ofPrefix_empty,LocalEmbedding.comp_identity,chart_germ]

lemma lost_leaves_bound (F : Forest ρ B C) :
    letI := Classical.decEq (GermBrick ρ)
    (C.pieces \ B.pieces).card ≤ 2 * (rank ρ C - rank ρ B) := by
  classical
  let T : B → Finset (GermBrick ρ) := fun b =>
    if F.pattern b = .leaf then ∅ else
      Finset.univ.image (fun j : Pattern.Leaves (F.pattern b) => (F.leaves ⟨b,j⟩).val)
  have hsub : C.pieces \ B.pieces ⊆ Finset.univ.biUnion T := by
    intro c hc
    obtain ⟨hcC,hcB⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨⟨b,j⟩,he⟩ := F.leaves.surjective ⟨c,hcC⟩
    have hn : F.pattern b ≠ .leaf := by
      intro hb
      have hh := F.leaf_root_eq b hb j
      have hcc : c = b.val := (congrArg Subtype.val he).symm.trans hh
      exact hcB (hcc ▸ b.property)
    apply Finset.mem_biUnion.mpr
    refine ⟨b,Finset.mem_univ _,?_⟩
    simp only [T,ite_eq_right hn]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,congrArg Subtype.val he⟩
  have hcard (b : B) : (T b).card + 2 ≤ 2 * Fintype.card (Pattern.Leaves (F.pattern b)) := by
    by_cases hb : F.pattern b = .leaf
    · simp [T,hb,Pattern.Leaves]
    · have hle : (T b).card ≤ Fintype.card (Pattern.Leaves (F.pattern b)) := by
        simpa only [T,ite_eq_right hb,Finset.card_univ] using
          (Finset.card_image_le (s := (Finset.univ : Finset (Pattern.Leaves (F.pattern b))))
            (f := fun j => (F.leaves ⟨b,j⟩).val))
      have htwo := Pattern.card_leaves_ge_two hb
      omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset B)) (fun b _ => hcard b)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hr : ∑ b : B, Fintype.card (Pattern.Leaves (F.pattern b)) = rank ρ C := by
    rw [rank_eq_card,← Fintype.card_sigma]
    exact Fintype.card_congr F.leaves
  rw [hr] at hsum
  have hi := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hbcard : (∑ _b : B, 2) = 2 * rank ρ B := by simp [rank_eq_card, Nat.mul_comm]
  rw [hbcard] at hsum
  omega
end Forest
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PosetTransport
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
namespace PosetTransport
section
universe u v w
variable {P : Type u} [Preorder P] {Q : Type v} [Preorder Q]
variable {H : Type w} [Group H]
namespace Cocycle
variable (c : Cocycle P H)
lemma trivial_pull (hc : c.Trivial) (f : Q →o P) : (c.pull f).Trivial := by
  obtain ⟨v,hv⟩ := hc
  exact ⟨v ∘ f,fun h => hv (f.monotone h)⟩
lemma square (f g : Q →o P) (h : ∀ x, f x ≤ g x) {x y : Q} (hxy : x ≤ y) :
    c.edge (h x) * c.edge (g.monotone hxy) =
      c.edge (f.monotone hxy) * c.edge (h y) := by
  rw [c.comp,c.comp]
lemma trivial_compare (f g : Q →o P) (h : ∀ x, f x ≤ g x)
    (hf : (c.pull f).Trivial) : (c.pull g).Trivial := by
  obtain ⟨v,hv⟩ := hf
  refine ⟨fun x => v x * c.edge (h x),?_⟩
  intro x y hxy
  change (v x * c.edge (h x)) * c.edge (g.monotone hxy) = v y * c.edge (h y)
  rw [mul_assoc,c.square f g h hxy,← mul_assoc]
  rw [show v x * c.edge (f.monotone hxy) = v y from hv hxy]
lemma trivial_compare_rev (f g : Q →o P) (h : ∀ x, f x ≤ g x)
    (hg : (c.pull g).Trivial) : (c.pull f).Trivial := by
  obtain ⟨v,hv⟩ := hg
  refine ⟨fun x => v x * (c.edge (h x))⁻¹,?_⟩
  intro x y hxy
  change (v x * (c.edge (h x))⁻¹) * c.edge (f.monotone hxy) =
    v y * (c.edge (h y))⁻¹
  apply mul_right_cancel (b := c.edge (h y))
  rw [mul_assoc,mul_assoc,← c.square f g h hxy,← mul_assoc (c.edge (h x))⁻¹,
    inv_mul_cancel,one_mul]
  simpa only [pull,mul_assoc,inv_mul_cancel,mul_one] using hv hxy
lemma trivial_of_bottom (t : P) (ht : ∀ x, t ≤ x) : c.Trivial := by
  exact ⟨fun x => c.edge (ht x),fun h => c.comp _ h⟩
end Cocycle

lemma Connected.constant (h : Connected P) {Y : Type*} (f : P → Y)
    (hf : ∀ {x y}, x ≤ y → f x = f y) (x y : P) : f x = f y := by
  induction h x y with
  | refl => rfl
  | @tail b d hxb hbd ih =>
    exact ih.trans (hbd.elim hf (fun hh => (hf hh).symm))
lemma connected_of_bottom (t : P) (ht : ∀ x, t ≤ x) : Connected P := by
  intro x y
  exact (Relation.ReflTransGen.single (show Adj x t from Or.inr (ht x))).trans
    (Relation.ReflTransGen.single (show Adj t y from Or.inl (ht y)))

theorem Cocycle.trivial_of_lower_fibers (c : Cocycle P H) (f : Q →o P)
    (hne : ∀ p : P, ∃ q : Q, f q ≤ p)
    (hconn : ∀ p : P, Connected {q : Q // f q ≤ p})
    (hq : (c.pull f).Trivial) : c.Trivial := by
  classical
  obtain ⟨v,hv⟩ := hq
  choose q hq using hne
  let rv (p : P) (x : {q : Q // f q ≤ p}) : H := v x.val * c.edge x.property
  have hrv (p : P) (x y : {q : Q // f q ≤ p}) : rv p x = rv p y := by
    apply (hconn p).constant (rv p) ?_ x y
    intro a b hab
    dsimp [rv]
    rw [← c.comp (f.monotone hab) b.property,← mul_assoc]
    rw [show v a.val * c.edge (f.monotone hab) = v b.val from hv hab]
  refine ⟨fun p => rv p ⟨q p,hq p⟩,?_⟩
  intro x y hxy
  change (v (q x) * c.edge (hq x)) * c.edge hxy = rv y ⟨q y,hq y⟩
  rw [mul_assoc,c.comp]
  exact hrv y ⟨q x,(hq x).trans hxy⟩ ⟨q y,hq y⟩

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

lemma Connected.of_orderIso (h : Connected P) (e : P ≃o Q) : Connected Q := by
  apply connected_of_constant
  intro f hf x y
  simpa only [Function.comp_apply,e.apply_symm_apply] using
    h.constant (f ∘ e) (fun hab => hf (e.monotone hab)) (e.symm x) (e.symm y)

theorem Cocycle.trivial_of_upper_fibers (c : Cocycle P H) (f : Q →o P)
    (hne : ∀ p : P, ∃ q : Q, p ≤ f q)
    (hconn : ∀ p : P, Connected {q : Q // p ≤ f q})
    (hq : (c.pull f).Trivial) : c.Trivial := by
  classical
  obtain ⟨v,hv⟩ := hq
  choose q hq using hne
  let rv (p : P) (x : {q : Q // p ≤ f q}) : H := v x.val * (c.edge x.property)⁻¹
  have hrv (p : P) (x y : {q : Q // p ≤ f q}) : rv p x = rv p y := by
    apply (hconn p).constant (rv p) ?_ x y
    intro a b hab
    dsimp [rv]
    apply mul_right_cancel (b := c.edge b.property)
    rw [mul_assoc,← c.comp a.property (f.monotone hab),
      ← mul_assoc (c.edge a.property)⁻¹,inv_mul_cancel,one_mul]
    simpa only [mul_assoc,inv_mul_cancel,mul_one,pull] using hv hab
  refine ⟨fun p => rv p ⟨q p,hq p⟩,?_⟩
  intro x y hxy
  have he := hrv x ⟨q x,hq x⟩ ⟨q y,hxy.trans (hq y)⟩
  change rv x ⟨q x,hq x⟩ * c.edge hxy = rv y ⟨q y,hq y⟩
  rw [he]
  dsimp [rv]
  rw [← c.comp hxy (hq y),mul_inv_rev,mul_assoc,mul_assoc,inv_mul_cancel,mul_one]

section Rank
variable {R : Type*} [PartialOrder R]

theorem Cocycle.trivial_rank_step (c : Cocycle R H) (r : R → ℕ) (hr : StrictMono r)
    (m : ℕ)
    (hupper : ∀ x, r x = m → Nonempty (Set.Ioi x) ∧ Connected (Set.Ioi x))
    (hm : (c.pull (rankEmbed r (m+1))).Trivial) :
    (c.pull (rankEmbed r m)).Trivial := by
  classical
  apply (c.pull (rankEmbed r m)).trivial_of_upper_fibers (rankStep r m)
  · intro p
    by_cases hp : m+1 ≤ r p.val
    · exact ⟨⟨p.val,hp⟩,le_refl _⟩
    · have he : r p.val = m := by have hh := p.property; change m ≤ r p.val at hh; omega
      obtain ⟨y⟩ := (hupper p.val he).1
      exact ⟨((rankFiberIso r hr m p he).symm y).val,
        ((rankFiberIso r hr m p he).symm y).property⟩
  · intro p
    by_cases hp : m+1 ≤ r p.val
    · exact connected_of_bottom (⟨⟨p.val,hp⟩,le_refl _⟩) (fun y => y.property)
    · have he : r p.val = m := by have hh := p.property; change m ≤ r p.val at hh; omega
      exact (hupper p.val he).2.of_orderIso (rankFiberIso r hr m p he).symm
  · exact hm

theorem Cocycle.trivial_of_rank (c : Cocycle R H) (r : R → ℕ) (hr : StrictMono r)
    (m : ℕ)
    (hupper : ∀ x, r x < m → Nonempty (Set.Ioi x) ∧ Connected (Set.Ioi x))
    (hm : (c.pull (rankEmbed r m)).Trivial) : c.Trivial := by
  induction m with
  | zero =>
    obtain ⟨v,hv⟩ := hm
    refine ⟨fun x => v ⟨x,Nat.zero_le _⟩,?_⟩
    intro x y h
    exact hv (x := ⟨x,Nat.zero_le _⟩) (y := ⟨y,Nat.zero_le _⟩) h
  | succ m ih =>
    apply ih (fun x hx => hupper x (Nat.lt_succ_of_lt hx))
    apply c.trivial_rank_step r hr m (fun x hx => hupper x (by omega)) hm
end Rank

lemma connected_of_directed (hd : ∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z) : Connected P := by
  intro x y
  obtain ⟨z,hxz,hyz⟩ := hd x y
  exact (Relation.ReflTransGen.single (show Adj x z from Or.inl hxz)).trans
    (Relation.ReflTransGen.single (show Adj z y from Or.inr hyz))
theorem Cocycle.trivial_of_directed [Nonempty P] (c : Cocycle P H)
    (hd : ∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z) : c.Trivial := by
  classical
  let b : P := Classical.choice ‹Nonempty P›
  let f : Set.Ici b →o P := ⟨Subtype.val,fun _ _ h => h⟩
  apply c.trivial_of_upper_fibers f
  · intro p
    obtain ⟨z,hbz,hpz⟩ := hd b p
    exact ⟨⟨z,hbz⟩,hpz⟩
  · intro p
    apply connected_of_directed
    intro x y
    obtain ⟨z,hxz,hyz⟩ := hd x.val.val y.val.val
    exact ⟨⟨⟨z,x.val.property.trans hxz⟩,x.property.trans hxz⟩,hxz,hyz⟩
  · exact (c.pull f).trivial_of_bottom ⟨b,le_refl b⟩ (fun x => x.property)

variable {R : Type*} [PartialOrder R]
namespace Cocycle
variable (r : R → ℕ) (hr : StrictMono r) (h : ℕ)
variable (c : Cocycle (rankBelow r h) H)
variable (hlink : ∀ a, h < r a → ∀ d : Cocycle (Set.Iio a) H, d.Trivial)
lemma fullExtension_pull : (fullExtension r hr h c hlink).pull (belowEmbed r h) = c := by
  apply Cocycle.ext
  intro x y hxy
  have hh := extensionLabel_stable r hr h c hlink (Nat.zero_le (r y.val))
    (show x.val ≤ y.val from hxy) (show r y.val ≤ h+0 from y.property)
  exact hh

include hr hlink in

theorem trivial_sublevel [Nonempty R]
    (hd : ∀ x y : R, ∃ z, x ≤ z ∧ y ≤ z) : c.Trivial := by
  have hf := (fullExtension r hr h c hlink).trivial_of_directed hd
  have hp := (fullExtension r hr h c hlink).trivial_pull hf (belowEmbed r h)
  rw [fullExtension_pull] at hp
  exact hp
end Cocycle
end

open OrderListChains OrderChains
variable (P : Type*) [Preorder P]
lemma connected_of_exactIn (h : ExactIn P 0) : Connected P := by
  have hu : ExactSet P Set.univ 0 := by
    intro c hc hn hd ha
    obtain ⟨d,hdM,hdn,hdd⟩ := h c (onSet_le_module P _ hc) hn hd ha
    exact ⟨d,fun s hs => ⟨hdM hs,Set.subset_univ _⟩,hdn,hdd⟩
  apply connected_of_constant
  intro f hf x y
  exact constant_of_exact_zero P hu f (fun _ _ _ _ h => hf h)
    (Set.mem_univ x) (Set.mem_univ y)
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
section
universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace Matching
variable {C : Basis ρ} {I : Type w} (M : Matching C I)

lemma available_present (B : Basis ρ) (N : Finset I) : M.Present B (M.available B N) :=
  fun i hi => ((M.mem_available B N i).mp hi).2

lemma available_subset (B : Basis ρ) (N : Finset I) : M.available B N ⊆ N :=
  fun i hi => ((M.mem_available B N i).mp hi).1

lemma unavailable_bound {B : Basis ρ} (F : Forest ρ B C) (N : Finset I) :
    N.card - (M.available B N).card ≤ 2 * (rank ρ C - rank ρ B) := by
  classical
  let T := N \ M.available B N
  have hp (i : T) : ∃ q : Bool, ((M.edge i.val).endpoint q).val ∉ B.pieces := by
    have hi := Finset.mem_sdiff.mp i.property
    by_contra hn
    push Not at hn
    exact hi.2 ((M.mem_available B N i.val).mpr ⟨hi.1,hn⟩)
  let f : T → ↥(C.pieces \ B.pieces) := fun i =>
    ⟨((M.edge i.val).endpoint (hp i).choose).val,
      Finset.mem_sdiff.mpr ⟨((M.edge i.val).endpoint (hp i).choose).property,(hp i).choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro i j hh
    apply Subtype.ext
    exact (M.endpoint_eq (congrArg (fun x : ↥(C.pieces \ B.pieces) => x.val) hh)).1
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hcard
  have he : T.card = N.card - (M.available B N).card :=
    Finset.card_sdiff_of_subset (M.available_subset B N)
  rw [he] at hcard
  exact hcard.trans F.lost_leaves_bound

lemma available_nonempty {B : Basis ρ} (hBC : CutRefines ρ B C) (N : Finset I)
    (hN : 2 * (rank ρ C - rank ρ B) < N.card) : (M.available B N).Nonempty := by
  have hb := M.unavailable_bound hBC.some N
  apply Finset.card_pos.mp
  omega

end Matching
end

universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace CutDown
variable {C : Basis ρ}
lemma strictMono_rank : StrictMono (fun B : CutDown C => rank ρ B.val) := by
  intro B D h
  apply rank_strictMono ρ
  exact lt_of_le_of_ne (le_of_cutRefines ρ h.le) (fun he => h.ne (ext he))

end CutDown

namespace Matching
variable {C : Basis ρ} {I : Type w} [Fintype I] (M : Matching C I)

lemma contractPair_le_base (m : ℕ) (x : M.Pair m) :
    M.contractPair m x ≤ x.base.val := M.contract_cutRefines _ _ x.present

lemma contractPair_le_ground (m : ℕ) (x : M.Pair m) :
    M.contractPair m x ≤ M.ground (M.selectedPair m x) :=
  M.contract_mono x.base.val.upper.some (cutRefines_refl ρ C) (Finset.Subset.refl _) x.present (M.present_top _)

lemma fiber_comparison (m : ℕ) (B : CutDown.Near C m)
    (x : {x : M.Pair m // M.projectPair m x ≤ B}) :
    x ≤ M.fiberInclusion m B (M.fiberResolution m B x) := ⟨x.property,Finset.Subset.refl _⟩

end Matching
end TwistedBrin.Basis

namespace TwistedBrin.Basis.Matching
open OrderListChains OrderChains
universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {C : Basis ρ} {I : Type w} [Fintype I] (M : Matching C I)

lemma fiber_exactIn (m : ℕ) (B : CutDown.Near C m)
    (hB : (M.available B.val.val Finset.univ).Nonempty) (n : ℕ) :
    ExactIn {x : M.Pair m // M.projectPair m x ≤ B} n := by
  classical
  apply exactIn_of_upper_comparison _ (M.fiberInclusion m B) (M.fiberResolution m B)
    (M.fiber_comparison m B)
  apply exactIn_of_bottom _ ⟨M.available B.val.val Finset.univ,hB,Finset.Subset.refl _⟩
  intro N
  exact N.property.2

lemma fiber_nonempty (m : ℕ) (B : CutDown.Near C m)
    (hB : (M.available B.val.val Finset.univ).Nonempty) :
    ∃ x : M.Pair m, M.projectPair m x ≤ B := by
  exact ⟨⟨B,M.available B.val.val Finset.univ,hB,M.available_present _ _⟩,le_rfl⟩

end TwistedBrin.Basis.Matching

namespace TwistedBrin.Basis.CutDown
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {C : Basis ρ}
lemma upper_nonempty (B : CutDown C) (h : rank ρ B.val + 2 ≤ rank ρ C) :
    ∃ D : CutDown C, B < D := by
  obtain ⟨e,he⟩ := B.upper.some.exists_last_merge B.ne
  refine ⟨⟨e.lower,e.lower_cutRefines,e.lower_ne⟩,lt_of_le_of_ne he ?_⟩
  intro hBD
  have hr := e.rank_lower
  have hv := congrArg CutDown.val hBD
  dsimp at hv
  rw [← hv] at hr
  omega

end TwistedBrin.Basis.CutDown

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
end CutBasis
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisMatching
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
namespace TwistedBrin.Basis.Matching
open PosetTransport
universe u v w t
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {C : Basis ρ} {I : Type w} [Fintype I] (M : Matching C I)
variable {H : Type t} [Group H]

theorem near_cocycle_trivial [Nonempty I] (m : ℕ)
    (hav : ∀ B : CutDown.Near C m, (M.available B.val.val Finset.univ).Nonempty)
    (c : Cocycle (CutDown C) H) : (c.pull (CutDown.nearInclude C m)).Trivial := by
  classical
  let a := CutDown.nearInclude C m
  let p := M.projectPair m
  let q := M.contractPair m
  let s := M.selectedPair m
  let g := M.ground
  have hg : (c.pull g).Trivial :=
    (c.pull g).trivial_of_bottom ⟨Finset.univ,Finset.univ_nonempty⟩
      (fun _ => Finset.subset_univ _)
  have ht : (c.pull (g.comp s)).Trivial := (c.pull g).trivial_pull hg s
  have hq : (c.pull q).Trivial :=
    c.trivial_compare_rev q (g.comp s) (M.contractPair_le_ground m) ht
  have hf : (c.pull (a.comp p)).Trivial :=
    c.trivial_compare q (a.comp p) (M.contractPair_le_base m) hq
  exact (c.pull a).trivial_of_lower_fibers p
    (fun B => M.fiber_nonempty m B (hav B))
    (fun B => connected_of_exactIn _ (M.fiber_exactIn m B (hav B) 0)) hf
end TwistedBrin.Basis.Matching

namespace TwistedBrin.Basis.CutDown
open PosetTransport OrderChains
universe u v t
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {H : Type t} [Group H]

theorem cocycle_trivial_high_rank [Nonempty S] (C : Basis ρ)
    (hC : 18 ≤ rank ρ C) (c : Cocycle (CutDown C) H) : c.Trivial := by
  classical
  let m := rank ρ C - 4
  let M := groundMatching C (Classical.choice ‹Nonempty S›) 9 (by omega)
  have hav (B : Near C m) : (M.available B.val.val Finset.univ).Nonempty := by
    apply M.available_nonempty B.val.upper
    simp only [Finset.card_univ,Fintype.card_fin]
    have hb := B.property
    change m ≤ rank ρ B.val.val at hb
    dsimp [m] at hb
    omega
  apply c.trivial_of_rank (fun B => rank ρ B.val) strictMono_rank m
  · intro B hB
    have hr : rank ρ B.val + 4 ≤ rank ρ C := by dsimp [m] at hB; omega
    obtain ⟨D,hD⟩ := upper_nonempty B (by omega)
    refine ⟨⟨⟨D,hD⟩⟩,?_⟩
    apply connected_of_exactIn
    exact exactIn_of_orderIso B.upperInterval
      (properCutInterval_exactIn ρ B.upper B.ne (n := 0) (by simpa using hr))
  · exact M.near_cocycle_trivial m hav c
end TwistedBrin.Basis.CutDown

namespace TwistedBrin.Basis.CutBasis
open PosetTransport
universe u v t
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {H : Type t} [Group H]

theorem sublevel_cocycle_trivial_oai [Nonempty S] (h : ℕ) (hh : 18 ≤ h)
    (c : Cocycle (rankBelow (fun B : CutBasis ρ => rank ρ B.val) h) H) : c.Trivial := by
  apply Cocycle.trivial_sublevel (fun B : CutBasis ρ => rank ρ B.val) strictMono_rank h c
  · intro C hC d
    let e : Set.Iio C ≃o CutDown C.val := lowerEquiv C
    let i : Set.Iio C →o CutDown C.val := ⟨e,e.monotone⟩
    let j : CutDown C.val →o Set.Iio C := ⟨e.symm,e.symm.monotone⟩
    have ht := CutDown.cocycle_trivial_high_rank C.val (by omega) (d.pull j)
    have hp := (d.pull j).trivial_pull ht i
    obtain ⟨v,hv⟩ := hp
    refine ⟨v,?_⟩
    intro x y hxy
    simpa only [Cocycle.pull,i,j,OrderHom.coe_mk,OrderIso.symm_apply_apply] using hv hxy
  · exact directed
end TwistedBrin.Basis.CutBasis

end

end OAI
end

theorem solution.{u, v, t} : type_of% @OAI.TwistedBrin.Basis.CutBasis.sublevel_cocycle_trivial_oai.{u, v, t} := @OAI.TwistedBrin.Basis.CutBasis.sublevel_cocycle_trivial_oai.{u, v, t}

-- Prove2me | solution 1 for OAI.SimpleFInftyOvergroups.SplittingTorusModel.products
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T02:52:31.581374+00:00
-- url     : https://prove2.me/submissions/d6fd0a3d-2b26-43a9-937d-2eef635ca2a4

import Mathlib
import Definitions.Def_OAIQ66So030
import Theorems.Thm_OAI_ListChains_uniform_fillings_from_partial_homotopy
import Theorems.Thm_OAI_ProductFiniteResolution_finite_free_resolution_of_products
import Theorems.Thm_OAI_RegularProduct_coset_parent_local_nilpotence

section
-- module Solutions.OAIQ066_SO.FiniteType_BasedComplex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BasedComplex

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

end BasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FreeTensor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains

variable (G : Type*)

lemma degree_cone (a : G) (s : Simplex G) :
    degree G (simplexCone G a s) = degree G s + 1 := rfl

lemma vertex_mem_vertexModule {V : Set G} {a : G} (ha : a ∈ V) :
    vertex G a ∈ vertexModule G V := by
  apply (mem_vertexModule G).mpr
  apply supported_single
  rw [vertices_vertex]
  exact Set.singleton_subset_iff.mpr ha

lemma cone_mem_vertexModule {V : Set G} {a : G} (ha : a ∈ V) {c : Chain G}
    (hc : c ∈ vertexModule G V) : cone G a c ∈ vertexModule G V := by
  apply (mem_vertexModule G).mpr
  refine supported_cone G (Q := fun s => vertices G s ⊆ V) a ?_
    ((mem_vertexModule G).mp hc)
  intro s hs
  rw [vertices_cone]
  exact Set.insert_subset ha hs

lemma cone_mem_degreeModule {n : ℕ} (a : G) {c : Chain G}
    (hc : c ∈ degreeModule G n) : cone G a c ∈ degreeModule G (n+1) := by
  refine supported_cone G (Q := fun s => degree G s = n+1) a ?_ hc
  intro s hs
  rw [degree_cone, hs]

lemma vertex_mem_degreeModule (a : G) : vertex G a ∈ degreeModule G 0 :=
  supported_single G (P := fun s => degree G s = 0) rfl 1

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*)

lemma augmentation_eq_zero_of_degree {n : ℕ} (hn : n ≠ 0) {c : Chain G}
    (hc : c ∈ degreeModule G n) : augmentation G c = 0 := by
  have he := BasedComplex.linear_eq_on_support (augmentation G)
    (0 : Chain G →ₗ[ℤ] ℤ) c (by
      intro s hs
      have hd : degree G s ≠ 0 := by rw [hc hs]; exact hn
      change (based G).aug (Finsupp.single s 1) = 0
      rw [(based G).aug_single]
      change (if degree G s = 0 then (1 : ℤ) else 0) = 0
      rw [ite_eq_right hd])
  exact he

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsHasPropagation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains

section

variable (G : Type*) [Group G] (a : G)

omit [Group G] in
lemma boundary_eq_zero_of_degree_zero {c : Chain G} (hc : c ∈ degreeModule G 0) :
    boundary G c = 0 := by
  have he := BasedComplex.linear_eq_on_support (boundary G) (0 : Chain G →ₗ[ℤ] Chain G) c (by
    intro s hs
    exact BasedComplex.d_vertex (based G) (hc hs))
  exact he

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsMapChainComp
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*)

variable [Group G]

open scoped Pointwise

lemma subset_symmetricClosure (S : Set G) : S ⊆ symmetricClosure G S :=
  fun _ h => Set.mem_insert_of_mem _ (Or.inl h)

lemma isBound_symmetricClosure {S : Set G} (hS : S.Finite) :
    IsBound G (symmetricClosure G S) where
  finite := (hS.union hS.inv).insert 1
  one_mem := Set.mem_insert _ _
  inv_mem := by
    intro a ha
    rcases ha with rfl | ha | ha
    · simpa only [symmetricClosure,inv_one] using (Set.mem_insert (1 : G) (S ∪ S⁻¹))
    · exact Set.mem_insert_of_mem _ (Or.inr (by simpa using ha))
    · exact Set.mem_insert_of_mem _ (Or.inl ha)

end

section

variable (G : Type*) [Group G]

lemma mem_pathSubgroup_of_mem {A : Set G} (h1 : (1 : G) ∈ A) {g : G}
    (hg : g ∈ A) (hgi : g⁻¹ ∈ A) : g ∈ pathSubgroup G A := by
  refine ⟨cone G 1 (vertex G g),cone_mem_degreeModule G 1 (vertex_mem_degreeModule G g),?_,?_⟩
  · refine vertexModule_le_controlledModule G (V := {1,g}) ?_
      (cone_mem_vertexModule G (Set.mem_insert _ _)
        (vertex_mem_vertexModule G (Set.mem_insert_of_mem _ rfl)))
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simpa only [inv_one,one_mul] using h1
    · simpa only [inv_one,one_mul] using hg
    · simpa only [mul_one] using hgi
    · simpa only [inv_mul_cancel] using h1
  · rw [boundary_cone,boundary_vertex,map_zero,sub_zero,K_apply,augmentation_vertex,one_smul]

lemma path_of_mem_closure {A : Set G} (hA : IsBound G A) {g : G}
    (hg : g ∈ Subgroup.closure A) : FillsAt G A 0 (vertex G g - vertex G 1) :=
  ((Subgroup.closure_le (pathSubgroup G A)).mpr (fun a ha =>
    mem_pathSubgroup_of_mem G hA.one_mem ha (hA.inv_mem a ha))) hg

omit [Group G] in
lemma inDegree_eq_zero {n m : ℕ} (hnm : m ≠ n) (v : Simplex G → Chain G)
    {c : Chain G} (hc : c ∈ degreeModule G m) : inDegree G n v c = 0 := by
  apply BasedComplex.linear_eq_on_support (inDegree G n v) (0 : Chain G →ₗ[ℤ] Chain G) c
  intro s hs
  have hd : degree G s = m := hc hs
  simp only [inDegree_single,hd,ite_eq_right hnm,LinearMap.zero_apply]

omit [Group G] in
lemma inDegree_mem_degree {n : ℕ} (v : Simplex G → Chain G)
    (hv : ∀ s, degree G s = n → v s ∈ degreeModule G (n+1))
    {m : ℕ} {c : Chain G} (hc : c ∈ degreeModule G m) :
    inDegree G n v c ∈ degreeModule G (m+1) := by
  apply BasedComplex.map_mem_of_support (inDegree G n v) _ c
  intro s hs
  rw [inDegree_single]
  split_ifs with he
  · rw [← hc hs,he]
    exact hv s he
  · exact Submodule.zero_mem _

lemma inDegree_mem_controlled {n : ℕ} (v : Simplex G → Chain G) {A B : Set G}
    (hv : ∀ s, degree G s = n → hasPropagation G A s → v s ∈ controlledModule G B)
    {c : Chain G} (hc : c ∈ controlledModule G A) :
    inDegree G n v c ∈ controlledModule G B := by
  apply BasedComplex.map_mem_of_support (inDegree G n v) _ c
  intro s hs
  rw [inDegree_single]
  split_ifs with he
  · exact hv s he (hc hs)
  · exact Submodule.zero_mem _

theorem controlledNullBelow_one_of_paths (f : G →* G) (A B : Set G)
    (hB : IsBound G B) (hf : ∀ g, f g ∈ Subgroup.closure B) :
    Nonempty (ControlledNullBelow G f A 1) := by
  classical
  choose p hpd hpb hp using fun g => path_of_mem_closure G hB (hf g)
  let v : Simplex G → Chain G := fun s => p s.1
  let J := inDegree G 0 v
  refine ⟨⟨B,hB,J,?_,?_,?_,?_⟩⟩
  · intro m c hc
    exact inDegree_mem_degree G v (fun s _ => hpd s.1) hc
  · intro c hc
    exact inDegree_mem_controlled G v (fun s _ _ => hpb s.1) hc
  · intro m hm c hc
    exact inDegree_eq_zero G (by omega) v hc
  · intro m hm c hc _
    have hm0 : m = 0 := by omega
    subst m
    rw [boundary_eq_zero_of_degree_zero G hc,map_zero,add_zero]
    apply BasedComplex.linear_eq_on_support (boundary G ∘ₗ J) (mapChain G f - K G 1) c
    intro s hs
    have hdeg : degree G s = 0 := hc hs
    have ht : s.2 = [] := List.length_eq_zero_iff.mp hdeg
    have he : Finsupp.single s 1 = vertex G s.1 := by cases s; simp_all [vertex,simplexVertex]
    change boundary G (J (Finsupp.single s 1)) = _
    rw [inDegree_single,ite_eq_left hdeg]
    change boundary G (p s.1) = mapChain G f (Finsupp.single s 1) - K G 1 (Finsupp.single s 1)
    rw [hp,he,mapChain_vertex,K_apply,augmentation_vertex,one_smul]

theorem controlledNullBelow_one_of_factorization {P : Type*} [Group P] [Group.FG P]
    (a : G →* P) (b : P →* G) (A : Set G) :
    Nonempty (ControlledNullBelow G (b.comp a) A 1) := by
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG P)
  let B := symmetricClosure G (b '' S)
  apply controlledNullBelow_one_of_paths G (b.comp a) A B
    (isBound_symmetricClosure G (hfin.image b))
  intro g
  apply Subgroup.closure_mono (subset_symmetricClosure G (b '' S))
  rw [← MonoidHom.map_closure,hS]
  exact Subgroup.mem_map.mpr ⟨a g,Subgroup.mem_top _,rfl⟩

end

variable (G : Type*) [Group G]

omit [Group G] in
lemma K_eq_zero_of_degree {n : ℕ} (hn : n ≠ 0) (a : G) {c : Chain G}
    (hc : c ∈ degreeModule G n) : K G a c = 0 := by
  rw [K_apply,augmentation_eq_zero_of_degree G hn hc,zero_smul]

omit [Group G] in

lemma inDegree_boundary_eq_zero {n m : ℕ} (hm : m ≤ n) (v : Simplex G → Chain G)
    {c : Chain G} (hc : c ∈ degreeModule G m) : inDegree G n v (boundary G c) = 0 := by
  cases m with
  | zero => rw [boundary_eq_zero_of_degree_zero G hc,map_zero]
  | succ m => exact inDegree_eq_zero G (by omega) v (boundary_mem_degreeModule G hc)

lemma ControlledNullBelow.obstruction_cycle {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) (hn : 0 < n) {c : Chain G}
    (hc : c ∈ degreeModule G n) (ha : c ∈ controlledModule G A) :
    boundary G (mapChain G f c - H.homotopy (boundary G c)) = 0 := by
  have hbd : boundary G c ∈ degreeModule G (n-1) := by
    apply boundary_mem_degreeModule G
    simpa only [Nat.sub_add_cancel hn] using hc
  have he := H.equation (n-1) (by omega) (boundary G c) hbd (boundary_mem_controlledModule G ha)
  simp only [boundary_boundary,map_zero,add_zero,K_boundary,sub_zero] at he
  rw [map_sub,boundary_mapChain,he,sub_self]

lemma ControlledNullBelow.obstruction_degree {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) (hn : 0 < n) {c : Chain G}
    (hc : c ∈ degreeModule G n) :
    mapChain G f c - H.homotopy (boundary G c) ∈ degreeModule G n := by
  have hn' : n-1+1 = n := Nat.sub_add_cancel hn
  have hbd : boundary G c ∈ degreeModule G (n-1) := by
    apply boundary_mem_degreeModule G
    rwa [hn']
  exact Submodule.sub_mem _ (mapChain_mem_degree G f hc) (by simpa only [hn'] using H.degree _ _ hbd)

lemma ControlledNullBelow.obstruction_controlled {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) {c : Chain G} (ha : c ∈ controlledModule G A) :
    mapChain G f c - H.homotopy (boundary G c) ∈ controlledModule G (f '' A ∪ H.bound) := by
  exact Submodule.sub_mem _
    (controlledModule_mono G Set.subset_union_left (mapChain_mem_controlled G G f ha))
    (controlledModule_mono G Set.subset_union_right (H.controlled _ (boundary_mem_controlledModule G ha)))

theorem ControlledNullBelow.extend {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) (hn : 0 < n)
    (g : G →* G) {B : Set G} (hB : IsBound G B)
    (hfill : ∀ c, c ∈ degreeModule G n → c ∈ controlledModule G (f '' A ∪ H.bound) →
      boundary G c = 0 → FillsAt G B n (mapChain G g c)) :
    Nonempty (ControlledNullBelow G (g.comp f) A (n+1)) := by
  classical
  let S := {s : Simplex G // ListChains.degree G s = n ∧ hasPropagation G A s}
  let r (s : Simplex G) := mapChain G f (Finsupp.single s 1) - H.homotopy (boundary G (Finsupp.single s 1))
  have hr (s : S) : FillsAt G B n (mapChain G g (r s)) := by
    have hd : Finsupp.single s.val 1 ∈ degreeModule G n := FreeTensor.single_mem_supported {s : Simplex G | ListChains.degree G s = n} s.property.1 1
    have ha : Finsupp.single s.val 1 ∈ controlledModule G A := FreeTensor.single_mem_supported _ s.property.2 1
    exact hfill _ (H.obstruction_degree G hn hd) (H.obstruction_controlled G ha) (H.obstruction_cycle G hn hd ha)
  choose v hvd hva hvb using hr
  let v' (s : Simplex G) : Chain G := if h : ListChains.degree G s = n ∧ hasPropagation G A s then v ⟨s,h⟩ else 0
  let L := inDegree G n v'
  let Q := H.postcompose G g
  have hv'd (s : Simplex G) (_hs : ListChains.degree G s = n) : v' s ∈ degreeModule G (n+1) := by
    dsimp only [v']
    split_ifs with h
    · exact hvd ⟨s,h⟩
    · exact Submodule.zero_mem _
  have hv'a (s : Simplex G) (hd : ListChains.degree G s = n) (ha : hasPropagation G A s) :
      v' s ∈ controlledModule G B := by
    dsimp only [v']
    rw [dite_eq_left ⟨hd,ha⟩]
    exact hva ⟨s,hd,ha⟩
  have hLd (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      L c ∈ degreeModule G (m+1) := inDegree_mem_degree G v' hv'd hc
  have hLa (c : Chain G) (hc : c ∈ controlledModule G A) :
      L c ∈ controlledModule G B := inDegree_mem_controlled G v' hv'a hc
  refine ⟨⟨Q.bound ∪ B,Q.isBound.union G hB,Q.homotopy + L,?_,?_,?_,?_⟩⟩
  · intro m c hc
    exact Submodule.add_mem _ (Q.degree m c hc) (hLd m c hc)
  · intro c hc
    exact Submodule.add_mem _
      (controlledModule_mono G Set.subset_union_left (Q.controlled c hc))
      (controlledModule_mono G Set.subset_union_right (hLa c hc))
  · intro m hm c hc
    simp only [LinearMap.add_apply,Q.zero m (by omega) c hc]
    rw [inDegree_eq_zero G (by omega) v' hc,add_zero]
  · intro m hm c hc ha
    by_cases hmn : m < n
    · have hLc : L c = 0 := inDegree_eq_zero G (by omega) v' hc
      have hLdc : L (boundary G c) = 0 := inDegree_boundary_eq_zero G (by omega) v' hc
      simpa only [LinearMap.add_apply,hLc,hLdc,add_zero] using Q.equation m hmn c hc ha
    · have heqn : m = n := by omega
      subst m
      apply BasedComplex.linear_eq_on_support
        (boundary G ∘ₗ (Q.homotopy + L) + (Q.homotopy + L) ∘ₗ boundary G)
        (mapChain G (g.comp f) - K G 1) c
      intro s hs
      have hd : ListChains.degree G s = n := hc hs
      have hpa : hasPropagation G A s := ha hs
      have hsd : Finsupp.single s 1 ∈ degreeModule G n := FreeTensor.single_mem_supported {s : Simplex G | ListChains.degree G s = n} hd 1
      have hQ := Q.zero n le_rfl (Finsupp.single s 1) hsd
      have hL : L (boundary G (Finsupp.single s 1)) = 0 := inDegree_boundary_eq_zero G le_rfl v' hsd
      have hK := K_eq_zero_of_degree G (by omega : n ≠ 0) 1 hsd
      have hLv : L (Finsupp.single s 1) = v ⟨s,hd,hpa⟩ := by
        simp only [L,inDegree_single,ite_eq_left hd]
        exact dite_eq_left (show ListChains.degree G s = n ∧ hasPropagation G A s from ⟨hd,hpa⟩)
      simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,hQ,zero_add,hL,add_zero,hK,sub_zero,hLv]
      rw [hvb]
      change mapChain G g (mapChain G f (Finsupp.single s 1) - H.homotopy (boundary G (Finsupp.single s 1))) +
        mapChain G g (H.homotopy (boundary G (Finsupp.single s 1))) = _
      rw [map_sub,sub_add_cancel,mapChain_comp]
      rfl

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G : Type*) [Group G]

lemma iterateHom_add (f : G →* G) (k l : ℕ) :
    iterateHom G f (k+l) = (iterateHom G f k).comp (iterateHom G f l) := by
  induction k with
  | zero => simp only [Nat.zero_add, iterateHom_zero, MonoidHom.id_comp]
  | succ k ih =>
    rw [Nat.succ_add,iterateHom,ih,iterateHom]
    rfl

theorem partial_homotopy_from_uniform (f : G →* G)
    (hbase : ∀ A, Nonempty (ControlledNullBelow G f A 1))
    (n : ℕ) (hn : 0 < n)
    (hfill : ∀ q, 0 < q → q < n → UniformFillings G f q)
    (A : Set G) (hA : IsBound G A) :
    ∃ k, Nonempty (ControlledNullBelow G (iterateHom G f k) A n) := by
  induction n with
  | zero => omega
  | succ q ih =>
    by_cases hq : q = 0
    · subst q
      exact ⟨1,by simpa only [iterateHom_one] using hbase A⟩
    · have hq' : 0 < q := by omega
      obtain ⟨k,⟨H⟩⟩ := ih hq' (fun j hj hjq => hfill j hj (by omega))
      obtain ⟨l,B,hB,hBl⟩ := hfill q hq' (by omega)
        ((iterateHom G f k) '' A ∪ H.bound)
        ((hA.image G (iterateHom G f k)).union G H.isBound)
      have hext := H.extend G hq' (iterateHom G f l) hB
        (fun c hcd hca hcz => hBl c hcd hca hcz (fun hq0 => (hq hq0).elim))
      exact ⟨l+k,by simpa only [iterateHom_add] using hext⟩

theorem uniform_fillings_of_factorization_and_splittings
    {P : Type*} [Group P] [Group.FG P] (a : G →* P) (b : P →* G)
    (F₂ : IdempotentSplittings G (ZMod 2) (b.comp a))
    (F₃ : IdempotentSplittings G (ZMod 3) (b.comp a)) :
    ∀ n, UniformFillings G (b.comp a) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hA
    by_cases hn : n = 0
    · subst n
      obtain ⟨H⟩ := controlledNullBelow_one_of_factorization G a b A
      refine ⟨1,H.bound,H.isBound,?_⟩
      intro z hzd hza hz hred
      refine ⟨H.homotopy z,H.degree 0 z hzd,H.controlled z hza,?_⟩
      have he := H.equation 0 (by decide) z hzd hza
      simpa only [hz,map_zero,add_zero,K_apply,hred rfl,zero_smul,sub_zero,iterateHom_one] using he
    · have hn' : 0 < n := by omega
      obtain ⟨k,⟨H⟩⟩ := partial_homotopy_from_uniform G (b.comp a)
        (controlledNullBelow_one_of_factorization G a b) n hn'
        (fun q _ hq => ih q hq) A hA
      obtain ⟨B,hB,hfill⟩ := uniform_fillings_from_partial_homotopy G F₂ F₃ hA hn' H
      refine ⟨1+k,B,hB,?_⟩
      intro z hzd hza hz _
      simpa only [iterateHom_add,iterateHom_one,MonoidHom.coe_comp] using hfill z hzd hza hz

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CategoryTheoryShortComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory

open CategoryTheory
namespace HomologyTransport
section
variable {R : Type} [CommRing R] {M N : ModuleCat R}

lemma iterate_commute (u : M ⟶ M) (v : N ⟶ N) (e : M ⟶ N)
    (h : u ≫ e = e ≫ v) (k : ℕ) (x : M) :
    e ((u : M → M)^[k] x) = (v : N → N)^[k] (e x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change (u ≫ e) ((u : M → M)^[k] x) = _
    rw [h]
    change v (e ((u : M → M)^[k] x)) = _
    rw [ih]

lemma localNilpotence_transfer (u : M ⟶ M) (v : N ⟶ N) (e : M ≅ N)
    (h : u ≫ e.hom = e.hom ≫ v)
    (hv : ∀ y : N, ∃ k : ℕ, (v : N → N)^[k] y = 0) :
    ∀ x : M, ∃ k : ℕ, (u : M → M)^[k] x = 0 := by
  intro x
  obtain ⟨k,hk⟩ := hv (e.hom x)
  refine ⟨k,?_⟩
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  rw [iterate_commute u v e.hom h,hk,map_zero]

end

open CategoryTheory
end HomologyTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardShapiro
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

namespace FunctionalTree
section

variable {R V M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma boundary_path (p : V → V) (n : ℕ) (v : V) (a : M) :
    boundary (R := R) p (path p n v a) =
      Finsupp.single v a - Finsupp.single (p^[n] v) a := by
  induction n with
  | zero => simp [path]
  | succ n ih =>
    rw [path,Finset.sum_range_succ]
    change boundary p (path p n v a + Finsupp.single (p^[n] v) a) = _
    rw [map_add,ih]
    simp only [boundary,LinearMap.sub_apply,LinearMap.id_apply,parentMap_single,
      Function.iterate_succ_apply']
    abel

lemma single_sub_single_mem_range (p : V → V)
    (merge : ∀ v w, ∃ n m : ℕ, p^[n] v = p^[m] w) (v w : V) (a : M) :
    Finsupp.single v a - Finsupp.single w a ∈ LinearMap.range (boundary (R := R) p) := by
  obtain ⟨n,m,h⟩ := merge v w
  refine ⟨path p n v a - path p m w a,?_⟩
  rw [map_sub,boundary_path,boundary_path,h]
  abel

lemma range_boundary_eq_ker_augmentation [Nonempty V] (p : V → V)
    (merge : ∀ v w, ∃ n m : ℕ, p^[n] v = p^[m] w) :
    LinearMap.range (boundary (R := R) (M := M) p) = LinearMap.ker augmentation := by
  classical
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact augmentation_boundary p a
  · intro a ha
    let w : V := Classical.choice inferInstance
    have hmem : (∑ v ∈ a.support, (Finsupp.single v (a v) - Finsupp.single w (a v))) ∈
        LinearMap.range (boundary (R := R) p) := by
      exact Submodule.sum_mem _ (fun v _ => single_sub_single_mem_range p merge v w (a v))
    rw [Finset.sum_sub_distrib] at hmem
    change (a.sum Finsupp.single - _) ∈ _ at hmem
    rw [Finsupp.sum_single] at hmem
    have hs : (∑ v ∈ a.support, Finsupp.single w (a v)) =
        Finsupp.single w (augmentation (R := R) a) := by
      rw [← Finsupp.single_finsetSum]
      rfl
    rw [hs,show augmentation (R := R) a = 0 from ha,Finsupp.single_zero,sub_zero] at hmem
    exact hmem

lemma boundary_injective (p : V → V) (height : V → ℤ)
    (raise : ∀ v, height (p v) = height v + 1) :
    Function.Injective (boundary (R := R) (M := M) p) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra hne
  have hs : a.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image a.support height hs
  have he : a = parentMap (R := R) p a := sub_eq_zero.mp ha
  have hv' : v ∈ (parentMap (R := R) p a).support := by rwa [← he]
  have him : v ∈ a.support.image p := Finsupp.mapDomain_support hv'
  obtain ⟨w,hw,hwv⟩ := Finset.mem_image.mp him
  have h := hmin w hw
  rw [← hwv,raise] at h
  omega

lemma augmentation_surjective [Nonempty V] :
    Function.Surjective (augmentation (R := R) (V := V) (M := M)) := by
  intro a
  exact ⟨Finsupp.single (Classical.choice inferInstance) a,augmentation_single _ _⟩

end

open _root_.CategoryTheory
variable {R G V : Type*} [CommRing R] [Group G] [MulAction G V]
variable (A : Rep R G)

variable (p : V → V) (peq : ∀ (g : G) (v : V), p (g • v) = g • p v)

lemma equivariantComplex_shortExact [Nonempty V]
    (merge : ∀ v w, ∃ n m : ℕ, p^[n] v = p^[m] w)
    (height : V → ℤ) (raise : ∀ v, height (p v) = height v + 1) :
    (equivariantComplex A p peq).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (CategoryTheory.ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep R G) (ModuleCat R))).mp
    rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact range_boundary_eq_ker_augmentation p merge
  · rw [Rep.mono_iff_injective]
    exact boundary_injective p height raise
  · rw [Rep.epi_iff_surjective]
    exact augmentation_surjective

end FunctionalTree

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardHomology
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
namespace StandardHomology
variable {R G : Type} [CommRing R] [Group G]

lemma coefficientMap_naturality {P Q : ChainComplex (Rep R G) ℕ}
    (u : P ⟶ Q) {A B : Rep R G} (α : A ⟶ B) :
    (((Rep.coinvariantsTensor R G).obj A).mapHomologicalComplex _).map u ≫
      coefficientMap Q α = coefficientMap P α ≫
        (((Rep.coinvariantsTensor R G).obj B).mapHomologicalComplex _).map u :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor R G).map α) _).naturality u

lemma inhomogeneousIso_naturality [DecidableEq G] {A B : Rep R G} (α : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) α ≫
      (groupHomology.inhomogeneousChainsIso B).hom =
    (groupHomology.inhomogeneousChainsIso A).hom ≫
      coefficientMap (Rep.barComplex R G) α := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s a
  change (groupHomology.inhomogeneousChainsIso B).hom.f n
    ((groupHomology.chainsMap (MonoidHom.id G) α).f n (Finsupp.single s a)) = _
  rw [groupHomology.chainsMap_f_single]
  change Rep.finsuppToCoinvariantsTensorFree B (Fin n → G)
      (Finsupp.single s (α a)) =
    (coefficientMap (Rep.barComplex R G) α).f n
      (Rep.finsuppToCoinvariantsTensorFree A (Fin n → G) (Finsupp.single s a))
  rw [Rep.finsuppToCoinvariantsTensorFree_single,Rep.finsuppToCoinvariantsTensorFree_single]
  rfl

lemma chainsIso_naturality {A B : Rep R G} (α : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) α ≫ (chainsIso B).hom =
    (chainsIso A).hom ≫ coefficientMap (Rep.standardComplex R G) α := by
  classical
  dsimp [chainsIso]
  rw [← Category.assoc,inhomogeneousIso_naturality,Category.assoc,
    ← coefficientMap_naturality,← Category.assoc]

lemma homologyIso_naturality {A B : Rep R G} (α : A ⟶ B) (n : ℕ) :
    (groupHomology.functor R G n).map α ≫ (homologyIso B n).hom =
      (homologyIso A n).hom ≫ HomologicalComplex.homologyMap
        (coefficientMap (Rep.standardComplex R G) α) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
      HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp,
    chainsIso_naturality]

end StandardHomology

open _root_.CategoryTheory _root_.OAI.CategoryTheory

namespace LocalNilpotence

variable {A : Type*} [AddCommGroup A]

lemma partialSum_sub_map (f : A →+ A) (n : ℕ) (x : A) :
    partialSum f n x - f (partialSum f n x) = x - (f : A → A)^[n] x := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [partialSum,map_add,Function.iterate_succ_apply']
    calc
      partialSum f n x + (f : A → A)^[n] x -
          (f (partialSum f n x) + f ((f : A → A)^[n] x)) =
        (partialSum f n x - f (partialSum f n x)) +
          ((f : A → A)^[n] x - f ((f : A → A)^[n] x)) := by abel
      _ = x - f ((f : A → A)^[n] x) := by rw [ih]; abel

lemma iterate_fixed (f : A →+ A) {x : A} (hx : f x = x) (n : ℕ) :
    (f : A → A)^[n] x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,hx]

theorem one_sub_bijective (f : A →+ A) (hf : IsLocallyNilpotent f) :
    Function.Bijective (AddMonoidHom.id A - f) := by
  constructor
  · intro x y hxy
    have he : f (x-y) = x-y := by
      change x - f x = y - f y at hxy
      rw [map_sub]
      have h := sub_eq_sub_iff_add_eq_add.mp hxy
      apply sub_eq_sub_iff_add_eq_add.mpr
      simpa only [add_comm] using h.symm
    obtain ⟨n,hn⟩ := hf (x-y)
    rw [iterate_fixed f he] at hn
    exact sub_eq_zero.mp hn
  · intro x
    obtain ⟨n,hn⟩ := hf x
    refine ⟨partialSum f n x,?_⟩
    change partialSum f n x - f (partialSum f n x) = x
    rw [partialSum_sub_map,hn,sub_zero]

end LocalNilpotence

open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace HomologyVanishingSequence
variable {R G : Type} [CommRing R] [Group G]
variable (S : ShortComplex (Rep R G)) (hS : S.ShortExact)

include hS

theorem vanishing (n : ℕ)
    (hsurj : Function.Surjective ((groupHomology.functor R G (n+1)).map S.f))
    (hinj : Function.Injective ((groupHomology.functor R G n).map S.f)) :
    ∀ x : groupHomology S.X₃ (n+1), x = 0 := by
  intro x
  let T := groupHomology.mapShortComplex₃ hS (i := n+1) (j := n) rfl
  have hex : T.Exact := groupHomology.mapShortComplex₃_exact hS rfl
  have hz : T.g x = 0 := by
    apply hinj
    have h := (groupHomology.mapShortComplex₁ hS (i := n+1) (j := n) rfl).zero_apply x
    change ((groupHomology.functor R G n).map S.f) (T.g x) = 0 at h
    exact h.trans (((groupHomology.functor R G n).map S.f).hom.map_zero).symm
  obtain ⟨z,hz⟩ := T.moduleCat_exact_iff.mp hex x hz
  obtain ⟨y,hy⟩ := hsurj z
  rw [← hz,← hy]
  exact (groupHomology.mapShortComplex₂ S (n+1)).zero_apply y

end HomologyVanishingSequence

namespace RegularProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))
variable (p : (G ⧸ S) → G ⧸ S) (peq : ∀ (g : G) (v : G ⧸ S), p (g • v)=g • p v)
variable (pbase : p (QuotientGroup.mk (1 : G)) = QuotientGroup.mk t)

include t ht pbase peq

lemma parent_local_nilpotence {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    ∀ x : groupHomology (CosetInduction.cosetRep S (rep G I)) (n+1),
    ∃ k : ℕ, ((groupHomology.functor ℤ G (n+1)).map
      (FunctionalTree.parentHom (rep G I) p peq) : _ → _)^[k] x = 0 := by
  apply HomologyTransport.localNilpotence_transfer _ _
    (StandardHomology.homologyIso (CosetInduction.cosetRep S (rep G I)) (n+1))
    (StandardHomology.homologyIso_naturality (FunctionalTree.parentHom (rep G I) p peq) (n+1))
  exact coset_parent_local_nilpotence G I S f t ht p peq pbase hf

lemma boundary_bijective {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    Function.Bijective ((groupHomology.functor ℤ G (n+1)).map
      (FunctionalTree.boundaryHom (rep G I) p peq)) := by
  have h := LocalNilpotence.one_sub_bijective
    (((groupHomology.functor ℤ G (n+1)).map
      (FunctionalTree.parentHom (rep G I) p peq)).hom.toAddMonoidHom)
    (parent_local_nilpotence G I S f t ht p peq pbase hf)
  rw [FunctionalTree.boundaryHom,CategoryTheory.Functor.map_sub,CategoryTheory.Functor.map_id]
  exact h

theorem vanishing {n : ℕ}
    (hf₁ : ListChains.UniformFillings S f (n+1))
    (hf₂ : ListChains.UniformFillings S f (n+2))
    [Nonempty (G ⧸ S)]
    (merge : ∀ v w, ∃ a b : ℕ, p^[a] v = p^[b] w)
    (height : (G ⧸ S) → ℤ) (raise : ∀ v, height (p v)=height v+1) :
    ∀ x : groupHomology (rep G I) (n+2), x=0 := by
  exact HomologyVanishingSequence.vanishing
    (FunctionalTree.equivariantComplex (rep G I) p peq)
    (FunctionalTree.equivariantComplex_shortExact (rep G I) p peq merge height raise)
    (n+1)
    (boundary_bijective G I S f t ht p peq pbase hf₂).surjective
    (boundary_bijective G I S f t ht p peq pbase hf₁).injective

end RegularProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNN
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace AscendingHNN
section

variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

lemma parent_iterate_mk (n : ℕ) (j : Torus f hf) :
    (parent f hf)^[n] (QuotientGroup.mk j) = QuotientGroup.mk (j * (stable f hf)^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply',ih,parent_mk,pow_succ,mul_assoc]

lemma parent_raises (v : Vertex f hf) :
    vertexHeight f hf (parent f hf v) = vertexHeight f hf v + 1 := by
  induction v using Quotient.inductionOn
  simp

lemma forward_meets_base (v : Vertex f hf) :
    ∃ n m : ℕ, (parent f hf)^[n] v =
      (parent f hf)^[m] (QuotientGroup.mk (1 : Torus f hf)) := by
  induction v using Quotient.inductionOn with
  | h j =>
    obtain ⟨p,q,u,hj⟩ := normal_form f hf j
    refine ⟨q,p,?_⟩
    rw [parent_iterate_mk,parent_iterate_mk,one_mul,hj]
    have he : ((stable f hf)^p * embed f hf u * ((stable f hf)^q)⁻¹) * (stable f hf)^q =
        (stable f hf)^p * embed f hf u := by group
    rw [he]
    exact QuotientGroup.mk_mul_of_mem _ ⟨u,rfl⟩

lemma forward_merge (v w : Vertex f hf) :
    ∃ n m : ℕ, (parent f hf)^[n] v = (parent f hf)^[m] w := by
  obtain ⟨n,m,hv⟩ := forward_meets_base f hf v
  obtain ⟨r,s,hw⟩ := forward_meets_base f hf w
  refine ⟨s+n,m+r,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,hv,hw,
    ← Function.iterate_add_apply,← Function.iterate_add_apply,Nat.add_comm s m]

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable {U : Type} [Group U] (f : U →* U) (hf : Function.Injective f)

lemma parent_smul (j : Torus f hf) (v : Vertex f hf) :
    parent f hf (j • v) = j • parent f hf v := by
  induction v using Quotient.inductionOn with
  | h k =>
    simp only [MulAction.Quotient.smul_mk,smul_eq_mul,parent_mk,mul_assoc]

end AscendingHNN

namespace ListChains
variable {G H : Type} [Group G] [Group H]
variable {K : Type} [CommRing K] {f : G →* G}

lemma uniformFillings_conjugate_of_factorization
    {P : Type} [Group P] [Group.FG P] (a : G →* P) (b : P →* G)
    (F₂ : IdempotentSplittings G (ZMod 2) (b.comp a))
    (F₃ : IdempotentSplittings G (ZMod 3) (b.comp a)) (e : G ≃* H) :
    ∀ n, UniformFillings H ((e.toMonoidHom.comp (b.comp a)).comp e.symm.toMonoidHom) n := by
  have h₂ : IdempotentSplittings H (ZMod 2)
      ((e.toMonoidHom.comp b).comp (a.comp e.symm.toMonoidHom)) := by
    simpa only [MonoidHom.comp_assoc] using F₂.conjugate e
  have h₃ : IdempotentSplittings H (ZMod 3)
      ((e.toMonoidHom.comp b).comp (a.comp e.symm.toMonoidHom)) := by
    simpa only [MonoidHom.comp_assoc] using F₃.conjugate e
  simpa only [MonoidHom.comp_assoc] using
    uniform_fillings_of_factorization_and_splittings H
      (a.comp e.symm.toMonoidHom) (e.toMonoidHom.comp b) h₂ h₃
end ListChains

namespace AscendingHNN
section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable {U P : Type} [Group U] [Group P] [Group.FG P]
variable (a : U →* P) (b : P →* U) (hf : Function.Injective (b.comp a))
variable (F₂ : ListChains.IdempotentSplittings U (ZMod 2) (b.comp a))
variable (F₃ : ListChains.IdempotentSplittings U (ZMod 3) (b.comp a))

omit [Group.FG P] in
lemma baseShift_relation (s : (embed (b.comp a) hf).range) :
    (s : Torus (b.comp a) hf) * stable (b.comp a) hf =
      stable (b.comp a) hf * (baseShift a b hf s : Torus (b.comp a) hf) := by
  have h := embed_mul_stable (b.comp a) hf ((baseEquiv a b hf).symm s)
  have he : embed (b.comp a) hf ((baseEquiv a b hf).symm s) = s :=
    congrArg Subtype.val ((baseEquiv a b hf).apply_symm_apply s)
  rw [he] at h
  exact h

include F₂ F₃ in

theorem regular_product_homology_vanishes (I : Type) (n : ℕ) :
    ∀ x : groupHomology (RegularProduct.rep (Torus (b.comp a) hf) I) (n+2), x=0 := by
  let S := (embed (b.comp a) hf).range
  let : Nonempty (Torus (b.comp a) hf ⧸ S) := ⟨QuotientGroup.mk (1 : Torus (b.comp a) hf)⟩
  have hfill := ListChains.uniformFillings_conjugate_of_factorization a b F₂ F₃ (baseEquiv a b hf)
  exact RegularProduct.vanishing (Torus (b.comp a) hf) I S (baseShift a b hf)
    (stable (b.comp a) hf) (baseShift_relation a b hf)
    (parent (b.comp a) hf) (parent_smul (b.comp a) hf)
    (by simpa only [one_mul] using parent_mk (b.comp a) hf 1)
    (hfill (n+1)) (hfill (n+2)) (forward_merge (b.comp a) hf)
    (vertexHeight (b.comp a) hf) (parent_raises (b.comp a) hf)

end

end AscendingHNN

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingTorus
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace AscendingTorus

open Monoid.Coprod Multiplicative

universe u

variable {U : Type u} [Group U]

variable {V : Type*} [Group V]

variable {P : Type*} [Group P]

theorem map_relation_eq_one_iff (f : U →* U)
    (q : Monoid.Coprod U (Multiplicative ℤ) →* V) (x : U) :
    q (relation f x) = 1 ↔
      q (inl x) = q (inr (ofAdd 1)) * q (inl (f x)) * (q (inr (ofAdd 1)))⁻¹ := by
  simp only [relation, map_mul, map_inv]
  rw [mul_inv_eq_iff_eq_mul, one_mul, mul_inv_eq_iff_eq_mul,
    ← eq_mul_inv_iff_mul_eq]

theorem normalClosure_relations_dense (f : U →* U) (S : Set U)
    (hS : Subgroup.closure S = ⊤) :
    relations f = Subgroup.normalClosure (relation f '' S) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    let N := Subgroup.normalClosure (relation f '' S)
    let q := QuotientGroup.mk' N
    have hconj : q.comp inl =
        (MulAut.conj (q (inr (ofAdd 1)))).toMonoidHom.comp ((q.comp inl).comp f) := by
      apply MonoidHom.eq_of_eqOn_dense hS
      intro x hx
      change q (inl x) = q (inr (ofAdd 1)) * q (inl (f x)) * (q (inr (ofAdd 1)))⁻¹
      apply (map_relation_eq_one_iff f q x).1
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨x, hx, rfl⟩)
    rintro _ ⟨x, rfl⟩
    apply (QuotientGroup.eq_one_iff _).1
    apply (map_relation_eq_one_iff f q x).2
    exact DFunLike.congr_fun hconj x
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, _, rfl⟩
    exact Subgroup.subset_normalClosure ⟨x, rfl⟩

theorem finitelyPresented (f : U →* U) [Group.IsFinitelyPresented U] :
    Group.IsFinitelyPresented (Torus f) := by
  obtain ⟨n, φ, hφ, _⟩ := (inferInstance : Group.IsFinitelyPresented U).out
  have : Group.FG U := Group.fg_of_surjective hφ
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG U)
  apply Group.IsFinitelyPresented.quotient
  exact ⟨relation f '' S, hfin.image _, (normalClosure_relations_dense f S hS).symm⟩

theorem finitelyPresented_of_factorization (f : U →* U)
    (a : U →* P) (b : P →* U) (hf : f = b.comp a)
    [Group.IsFinitelyPresented P] : Group.IsFinitelyPresented (Torus f) := by
  subst f
  have := finitelyPresented (a.comp b)
  exact Group.IsFinitelyPresented.equiv (interleaveEquiv a b).symm

end AscendingTorus

namespace AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

variable {P : Type*} [Group P] [Group.IsFinitelyPresented P]

theorem finitelyPresented_of_factorization (a : U →* P) (b : P →* U)
    (heq : f=b.comp a) : Group.IsFinitelyPresented (Torus f hf) := by
  let _ := AscendingTorus.finitelyPresented_of_factorization f a b heq
  exact Group.IsFinitelyPresented.equiv (presentationEquiv f hf).symm

end AscendingHNN

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCriterion
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace ProductCriterion
variable {k G I : Type} [CommRing k] [Group G]

lemma coordinates_bijective_of_iso {C : Rep k G} {α : Type} [Finite α]
    (e : C ≅ Rep.free k G α) : Function.Bijective (coordinates (I := I) C) := by
  classical
  let F := (Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)
  let E := F.mapIso e
  have hn (y : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants) :
      coordinates (Rep.free k G α) (E.hom y) = fun i => e.hom.hom (coordinates C y i) := by
    funext i
    exact coordinate_natural _ e.hom i y
  refine ⟨?_,?_⟩
  · intro x y h
    apply (ModuleCat.mono_iff_injective E.hom).mp inferInstance
    apply free_coordinates_injective α
    change coordinates (Rep.free k G α) (E.hom x) = coordinates (Rep.free k G α) (E.hom y)
    rw [hn,hn,h]
  · intro z
    obtain ⟨y,hy⟩ := free_coordinates_surjective (k := k) (G := G) (I := I) α
      (fun i => e.hom.hom (z i))
    refine ⟨E.inv y,?_⟩
    have hh := hn (E.inv y)
    have he : E.hom (E.inv y) = y := congrArg (fun f : F.obj (Rep.free k G α) ⟶ _ => f y)
      E.inv_hom_id
    rw [he] at hh
    funext i
    apply (Rep.mono_iff_injective e.hom).mp inferInstance
    exact (congrFun hh i).symm.trans (congrFun hy i)

theorem finite_free_products (P : ProjectiveResolution (Rep.trivial k G k))
    (hf : ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free k G α))
    (n : ℕ) : IsZero (groupHomology (RegularProductR.rep k G I) (n+1)) := by
  classical
  let F := (Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)
  have hb (j : ℕ) : Function.Bijective (coordinates (I := I) (P.complex.X j)) := by
    obtain ⟨α,hα,⟨e⟩⟩ := hf j
    let := hα
    exact coordinates_bijective_of_iso e
  have he : (P.complex.coinvariantsTensorObj (RegularProductR.rep k G I)).ExactAt (n+1) := by
    rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hp := (HomologicalComplex.exactAt_iff' P.complex (n+2) (n+1) n
      (by simp) (by simp)).mp (P.complex_exactAt_succ n)
    have hp' := (ShortComplex.moduleCat_exact_iff _).mp
      (hp.map (forget₂ (Rep k G) (ModuleCat k)))
    have hz (i : I) : (P.complex.d (n+1) n).hom (coordinate (P.complex.X (n+1)) i x) = 0 := by
      rw [← coordinate_natural (P.complex.X n) (P.complex.d (n+1) n) i x]
      change coordinate (P.complex.X n) i
        ((P.complex.coinvariantsTensorObj (RegularProductR.rep k G I)).d (n+1) n x) = 0
      change (P.complex.coinvariantsTensorObj (RegularProductR.rep k G I)).d (n+1) n x = 0 at hx
      rw [hx]
      exact (coordinate (P.complex.X n) i).map_zero
    choose y hy using fun i => hp' (coordinate (P.complex.X (n+1)) i x) (hz i)
    obtain ⟨a,ha⟩ := (hb (n+2)).surjective y
    refine ⟨a,(hb (n+1)).injective ?_⟩
    funext i
    change coordinate (P.complex.X (n+1)) i
      (tensorMap (P.complex.X (n+1)) (P.complex.d (n+2) (n+1)) a) = _
    rw [coordinate_natural]
    exact (congrArg (P.complex.d (n+2) (n+1)).hom (congrFun ha i)).trans (hy i)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp he).of_iso
    (groupHomologyIso (RegularProductR.rep k G I) (n+1) P)

end ProductCriterion

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
namespace ProductBrown
attribute [-instance] AddCommGroup.toIntModule
end ProductBrown

open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

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

universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
lemma fg_of_fp [Group.IsFinitelyPresented G] : Group.FG G := by
  obtain ⟨n,f,hf,_⟩ := (inferInstance : Group.IsFinitelyPresented G).out
  exact Group.fg_of_surjective hf

end ActionPresentation

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactSubtypeOfExactSet
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace SimpleFInftyOvergroups.SplittingTorusModel
variable {G : Type} [Group G]

theorem finitelyPresented (M : SplittingTorusModel G) : Group.IsFinitelyPresented G := by
  rcases M with @⟨U,P,gU,gP,hP,f,hf,α,b,hb,F₂,F₃,e⟩
  let := AscendingHNN.finitelyPresented_of_factorization f hf α b hb
  exact Group.IsFinitelyPresented.equiv e

theorem products₂ (M : SplittingTorusModel G) (I : Type) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (n+2)) := by
  rcases M with @⟨U,P,gU,gP,hP,f,hf,α,b,hb,F₂,F₃,e⟩
  subst f
  let := ActionPresentation.fg_of_fp (G := P)
  have hz : IsZero (groupHomology (RegularProduct.rep (AscendingHNN.Torus (b.comp α) hf) I) (n+2)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y => (AscendingHNN.regular_product_homology_vanishes α b hf F₂ F₃ I n x).trans
      (AscendingHNN.regular_product_homology_vanishes α b hf F₂ F₃ I n y).symm⟩
  exact hz.of_iso (RegularProductR.homologyRelabel e I (n+2)).symm

theorem products_oai (M : SplittingTorusModel G) (I : Type) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (n+1)) := by
  let := M.finitelyPresented
  obtain ⟨P,hP⟩ := ProductFiniteResolution.finite_free_resolution_of_products G (by
    intro J m hm
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hm
    simpa only [Nat.add_comm 2] using M.products₂ J j)
  exact ProductCriterion.finite_free_products (I := I) P hP n
end SimpleFInftyOvergroups.SplittingTorusModel

end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleFInftyOvergroups.SplittingTorusModel.products_oai := @OAI.SimpleFInftyOvergroups.SplittingTorusModel.products_oai

-- Prove2me | solution 1 for OAI.TwistedBrin.Basis.CutBasis.lower_exactSet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:03:00.539556+00:00
-- url     : https://prove2.me/submissions/3565a56e-5050-4d84-acd5-99d187ae1805

import Mathlib
import Definitions.Def_OAIQ66So031

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
lemma mapChain_eq_on {Q : Type*} (f g : P → Q) {c : Chain P}
    (h : ∀ s ∈ c.support, ∀ x ∈ vertices P s, f x = g x) :
    mapChain P f c = mapChain P g c := by
  apply OrderBasedComplex.linear_eq_on_support
  intro s hs
  rw [mapChain_single,mapChain_single]
  congr 2
  · exact h s hs _ (head_mem_vertices P s)
  · apply List.map_congr_left
    intro x hx
    exact h s hs x (Or.inr hx)
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
lemma map_onSet {Q : Type*} [Preorder Q] (f : P → Q) {U : Set P} {V : Set Q}
    (hf : ∀ x ∈ U, f x ∈ V) (hm : ∀ x ∈ U, ∀ y ∈ U, x ≤ y → f x ≤ f y)
    {c : Chain P} (hc : c ∈ onSet P U) : mapChain P f c ∈ onSet Q V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  rw [mapChain_single]
  apply supported_single
  constructor
  · change ((list P s).map f).Pairwise _
    rw [List.pairwise_map]
    apply (hc hs).1.imp_of_mem
    intro x y hx hy hxy
    exact hm y ((hc hs).2 ((mem_list P s y).mp hy))
      x ((hc hs).2 ((mem_list P s x).mp hx)) hxy
  · intro y hy
    rcases hy with rfl | hy
    · exact hf s.1 ((hc hs).2 (head_mem_vertices P s))
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      exact hf x ((hc hs).2 (Or.inr hx))

lemma project_val (P : Type*) [Preorder P] {U : Set P} (u : U) {x : P} (hx : x ∈ U) :
    (project P U u x).val = x := by
  classical
  simp [project,hx]
lemma exactSet_of_subtype {U : Set P} (u : U) {n : ℕ} (h : ExactIn U n) :
    ExactSet P U n := by
  intro c hc hn hd ha
  have hp := map_onSet P (project P U u) (V := Set.univ) (fun _ _ => Set.mem_univ _)
    (fun x hx y hy hxy => by
      change (project P U u x).val ≤ (project P U u y).val
      simpa only [project_val P u hx,project_val P u hy] using hxy) hc
  have hpd : boundary U (mapChain P (project P U u) c) = 0 := by
    rw [boundary_mapChain,hd,map_zero]
  have hpa : augmentation U (mapChain P (project P U u) c) = 0 := by
    rw [augmentation_mapChain,ha]
  obtain ⟨d,hdU,hdn,hdd⟩ := h _ (onSet_le_module U _ hp)
    (map_degree P _ hn) hpd hpa
  have hdset : d ∈ onSet U Set.univ := fun s hs => ⟨hdU hs,Set.subset_univ _⟩
  refine ⟨mapChain U Subtype.val d,map_onSet U Subtype.val
      (fun x _ => x.property) (fun _ _ _ _ hxy => hxy) hdset,map_degree U _ hdn,?_⟩
  rw [boundary_mapChain,hdd,mapChain_comp]
  have he := mapChain_eq_on P (Subtype.val ∘ project P U u) id
    (c := c) (fun s hs x hx => project_val P u ((hc hs).2 hx))
  rw [he,mapChain_id]

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

lemma exactSet_of_bottom {U : Set P} (u : P) (hu : u ∈ U)
    (hb : ∀ x ∈ U, u ≤ x) (n : ℕ) : ExactSet P U n := by
  let i : PUnit.{1} →o U := ⟨fun _ => ⟨u,hu⟩,fun _ _ _ => le_rfl⟩
  let r : U →o PUnit.{1} := ⟨fun _ => PUnit.unit,fun _ _ _ => le_rfl⟩
  apply exactSet_of_subtype P ⟨u,hu⟩
  apply exactIn_of_comparison U i r (fun x => hb x x.property)
  exact exactIn_of_top PUnit.{1} PUnit.unit (fun _ => le_rfl) n

lemma Descending.comparable {s : Simplex P} (hs : Descending P s) {x y : P}
    (hx : x ∈ vertices P s) (hy : y ∈ vertices P s) : x ≤ y ∨ y ≤ x := by
  have h (l : List P) (hl : l.Pairwise (fun a b => b ≤ a)) :
      ∀ x ∈ l, ∀ y ∈ l, x ≤ y ∨ y ≤ x := by
    induction l with
    | nil => simp
    | cons a l ih =>
      obtain ⟨hal,hl⟩ := List.pairwise_cons.mp hl
      intro x hx y hy
      rcases List.mem_cons.mp hx with rfl | hxTail
      · rcases List.mem_cons.mp hy with rfl | hyTail
        · exact Or.inl le_rfl
        · exact Or.inr (hal y hyTail)
      · rcases List.mem_cons.mp hy with rfl | hyTail
        · exact Or.inl (hal x hxTail)
        · exact ih hl x hxTail y hyTail
  exact h (list P s) hs x ((mem_list P s x).mpr hx) y ((mem_list P s y).mpr hy)

theorem carrier_move (U V : Set P) (K L : Simplex P → Set P) (N : ℕ)
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
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ onSet P U) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P V ∧ Homogeneous P n c' ∧ boundary P c' = 0 ∧
      augmentation P c' = 0 ∧ d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧
      boundary P d = c-c' := by
  classical
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
  have hsvalid (s : Simplex P) (hs : s ∈ c.support) : valid s := hc hs
  have hsd (s : Simplex P) (hs : s ∈ c.support) : degree P s ≤ N := (hn s hs).le.trans hnN
  refine ⟨F c,H c,?_,?_,?_,?_,?_,?_,?_⟩
  · apply OrderBasedComplex.map_mem_of_support
    intro s hs
    exact onSet_mono P (hKV s (hc hs).1 (hc hs).2) (hFL s (hsvalid s hs) (hsd s hs)).1
  · apply OrderBasedComplex.map_mem_of_support F (degreeModule P n)
    intro s hs
    rw [← hn s hs]
    exact (hFL s (hsvalid s hs) (hsd s hs)).2.1
  · have he := OrderBasedComplex.linear_eq_on_support ((boundary P).comp F) (F.comp (boundary P)) c
      (fun s hs => (hFL s (hsvalid s hs) (hsd s hs)).2.2.1)
    simpa only [LinearMap.comp_apply,hd,map_zero] using he
  · have he := OrderBasedComplex.linear_eq_on_support ((augmentation P).comp F) (augmentation P) c
      (fun s hs => (hFL s (hsvalid s hs) (hsd s hs)).2.2.2)
    simpa only [LinearMap.comp_apply,ha] using he
  · apply OrderBasedComplex.map_mem_of_support
    intro s hs
    exact onSet_mono P (hLU s (hc hs).1 (hc hs).2) (hH s (hsvalid s hs) (hsd s hs)).1
  · apply OrderBasedComplex.map_mem_of_support H (degreeModule P (n+1))
    intro s hs
    rw [← hn s hs]
    exact (hH s (hsvalid s hs) (hsd s hs)).2.1
  · have he := OrderBasedComplex.linear_eq_on_support ((boundary P).comp H+H.comp (boundary P))
      (LinearMap.id-F) c (fun s hs => (hH s (hsvalid s hs) (hsd s hs)).2.2.1)
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,hd,map_zero,add_zero,
      LinearMap.sub_apply,LinearMap.id_apply] using he
end

section
open OrderListChains
variable (P : Type*) [PartialOrder P]
lemma Descending.above_min {U : Set P} {a : P}
    (hmin : ∀ x ∈ U, x ≤ a → x = a) {s : Simplex P}
    (hs : Descending P s) (hsU : vertices P s ⊆ U) (ha : a ∈ vertices P s) :
    ∀ x ∈ vertices P s, a ≤ x := by
  intro x hx
  rcases hs.comparable P ha hx with h | h
  · exact h
  · rw [hmin x (hsU hx) h]
lemma deleteCarrier_face {U : Set P} {a : P} (hmin : ∀ x ∈ U, x ≤ a → x = a)
    {s t : Simplex P} (hs : Descending P s) (hsU : vertices P s ⊆ U)
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    deleteCarrier P U a t ⊆ deleteCarrier P U a s := by
  classical
  have hts := boundary_vertices P s t ht
  unfold deleteCarrier
  split_ifs with hat has has
  · exact Set.Subset.rfl
  · exact False.elim (has (hts hat))
  · intro x hx
    exact ⟨hsU (hts hx),lt_of_le_of_ne (hs.above_min P hmin hsU has x (hts hx))
      (fun h => hat (h ▸ hx))⟩
  · exact hts
lemma starCarrier_face {U : Set P} {a : P} (hmin : ∀ x ∈ U, x ≤ a → x = a)
    {s t : Simplex P} (hs : Descending P s) (hsU : vertices P s ⊆ U)
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    starCarrier P U a t ⊆ starCarrier P U a s := by
  classical
  have hts := boundary_vertices P s t ht
  unfold starCarrier
  split_ifs with hat has has
  · exact Set.Subset.rfl
  · exact False.elim (has (hts hat))
  · intro x hx
    exact ⟨hsU (hts hx),hs.above_min P hmin hsU has x (hts hx)⟩
  · exact hts

theorem delete_minimal (U : Set P) (a : P) (haU : a ∈ U)
    (hmin : ∀ x ∈ U, x ≤ a → x = a) (N : ℕ)
    (hup : ∃ x ∈ U, a < x)
    (hupper : ∀ k ≤ N, ExactSet P {x | x ∈ U ∧ a < x} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ onSet P U) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P (U \ {a}) ∧ Homogeneous P n c' ∧ boundary P c' = 0 ∧
      augmentation P c' = 0 ∧ d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧
      boundary P d = c-c' := by
  classical
  apply carrier_move P U (U \ {a}) (deleteCarrier P U a) (starCarrier P U a) N
    ?_ ?_ ?_ ?_ ?_ (fun _ _ hs hsU ht => deleteCarrier_face P hmin hs hsU ht)
    (fun _ _ hs hsU ht => starCarrier_face P hmin hs hsU ht) ?_ ?_ hnN c hc hn hd ha
  · intro s _ _
    unfold deleteCarrier
    split_ifs
    · exact hup
    · exact ⟨s.1,head_mem_vertices P s⟩
  · intro s _ hsU x hx
    unfold deleteCarrier at hx
    split_ifs at hx with has
    · exact ⟨hx.1,fun h => (ne_of_lt hx.2) h.symm⟩
    · exact ⟨hsU hx,fun h => has (h ▸ hx)⟩
  · intro s _ hsU x hx
    unfold starCarrier at hx
    split_ifs at hx
    · exact hx.1
    · exact hsU hx
  · intro s _ _
    unfold deleteCarrier starCarrier
    split_ifs
    · exact fun _ hx => ⟨hx.1,hx.2.le⟩
    · exact Set.Subset.rfl
  · intro s hs hsU
    unfold starCarrier
    split_ifs with has
    · exact fun x hx => ⟨hsU hx,hs.above_min P hmin hsU has x hx⟩
    · exact Set.Subset.rfl
  · intro s hs hsU k hk
    unfold deleteCarrier
    split_ifs
    · exact hupper k hk
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
  · intro s hs hsU k _
    unfold starCarrier
    split_ifs
    · exact exactSet_of_bottom P (U := {x | x ∈ U ∧ a ≤ x}) a ⟨haU,le_rfl⟩ (fun _ hx => hx.2) k
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
end

open OrderListChains
variable (P : Type*) [PartialOrder P]

theorem delete_finite_minimal (U : Set P) (T : Finset P) (N : ℕ)
    (hTU : ∀ a ∈ T, a ∈ U) (hmin : ∀ a ∈ T, ∀ x ∈ U, x ≤ a → x = a)
    (hup : ∀ a ∈ T, ∃ x ∈ U, a < x)
    (hupper : ∀ a ∈ T, ∀ k ≤ N, ExactSet P {x | x ∈ U ∧ a < x} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ onSet P U) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P (U \ (T : Set P)) ∧ Homogeneous P n c' ∧ boundary P c' = 0 ∧
      augmentation P c' = 0 ∧ d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧
      boundary P d = c-c' := by
  classical
  induction T using Finset.induction_on generalizing U c with
  | empty =>
    refine ⟨c,0,?_,hn,hd,ha,(onSet P U).zero_mem,supported_zero P _,?_⟩
    · simpa only [Finset.coe_empty,Set.sdiff_empty] using hc
    · simp
  | @insert a T hat ih =>
    have hTa : a ∈ insert a T := Finset.mem_insert_self _ _
    obtain ⟨c1,d1,hc1,hn1,hd1,ha1,hD1,hDn1,hdd1⟩ := delete_minimal P U a (hTU a hTa)
      (hmin a hTa) N (hup a hTa) (hupper a hTa) hnN c hc hn hd ha
    have hmem (b : P) (hb : b ∈ T) : b ∈ insert a T := Finset.mem_insert_of_mem hb
    have hne (b : P) (hb : b ∈ T) : b ≠ a := by intro he; exact hat (he ▸ hb)
    have havoid (b : P) (hb : b ∈ T) (x : P) (hxU : x ∈ U) (hbx : b < x) : x ≠ a := by
      intro he
      subst x
      exact hne b hb (hmin a hTa b (hTU b (hmem b hb)) hbx.le)
    have hset (b : P) (hb : b ∈ T) :
        {x | x ∈ U \ {a} ∧ b < x} = {x | x ∈ U ∧ b < x} := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,havoid b hb x hx.1 hx.2⟩,hx.2⟩⟩
    obtain ⟨c2,d2,hc2,hn2,hd2,ha2,hD2,hDn2,hdd2⟩ := ih (U \ {a})
      (fun b hb => ⟨hTU b (hmem b hb),hne b hb⟩)
      (fun b hb x hx hxb => hmin b (hmem b hb) x hx.1 hxb)
      (fun b hb => by
        obtain ⟨x,hx,hbx⟩ := hup b (hmem b hb)
        exact ⟨x,⟨hx,havoid b hb x hx hbx⟩,hbx⟩)
      (fun b hb k hk => by rw [hset b hb]; exact hupper b (hmem b hb) k hk)
      c1 hc1 hn1 hd1 ha1
    refine ⟨c2,d1+d2,?_,hn2,hd2,ha2,?_,supported_add P hDn1 hDn2,?_⟩
    · apply onSet_mono P _ hc2
      intro x hx
      refine ⟨hx.1.1,?_⟩
      intro hxi
      rcases Finset.mem_insert.mp hxi with he | he
      · exact hx.1.2 he
      · exact hx.2 he
    · exact (onSet P U).add_mem hD1 (onSet_mono P Set.sdiff_subset hD2)
    · rw [map_add,hdd1,hdd2]
      abel
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
variable (P : Type*) [PartialOrder P]
theorem raise_rank_step (r : P → ℕ) (hr : StrictMono r) (D : Set P) (m N : ℕ)
    (hup : ∀ a ∈ D, r a = m → ∃ x ∈ D, a < x)
    (hupper : ∀ a ∈ D, r a = m → ∀ k ≤ N, ExactSet P {x | x ∈ D ∧ a < x} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P)
    (hc : c ∈ onSet P {x | x ∈ D ∧ m ≤ r x}) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P {x | x ∈ D ∧ m+1 ≤ r x} ∧ Homogeneous P n c' ∧
      boundary P c' = 0 ∧ augmentation P c' = 0 ∧ d ∈ onSet P D ∧
      Homogeneous P (n+1) d ∧ boundary P d = c-c' := by
  classical
  let T := (vertexSupport P c).filter (fun x => r x = m)
  let U : Set P := {x | x ∈ D ∧ m+1 ≤ r x} ∪ (T : Set P)
  have hT (a : P) (ha : a ∈ T) : a ∈ D ∧ r a = m := by
    obtain ⟨hav,har⟩ := Finset.mem_filter.mp ha
    obtain ⟨s,hs,has⟩ := (mem_vertexSupport P).mp hav
    exact ⟨((hc hs).2 has).1,har⟩
  have hU (x : P) (hx : x ∈ U) : x ∈ D ∧ m ≤ r x := by
    rcases hx with hx | hx
    · exact ⟨hx.1,(Nat.le_succ m).trans hx.2⟩
    · exact ⟨(hT x hx).1,by rw [(hT x hx).2]⟩
  have hcU : c ∈ onSet P U := by
    intro s hs
    refine ⟨(hc hs).1,?_⟩
    intro x hx
    have hcx := (hc hs).2 hx
    by_cases he : r x = m
    · exact Or.inr (Finset.mem_filter.mpr ⟨(mem_vertexSupport P).mpr ⟨s,hs,hx⟩,he⟩)
    · exact Or.inl ⟨hcx.1,by have hh : m ≤ r x := hcx.2; omega⟩
  have hset (a : P) (ha : a ∈ T) :
      {x | x ∈ U ∧ a < x} = {x | x ∈ D ∧ a < x} := by
    ext x
    refine ⟨fun hx => ⟨(hU x hx.1).1,hx.2⟩,fun hx => ⟨?_,hx.2⟩⟩
    have hh := hr hx.2
    have he := (hT a ha).2
    exact Or.inl ⟨hx.1,by omega⟩
  obtain ⟨c',d,hc',hn',hd',ha',hD,hDn,hdd⟩ := delete_finite_minimal P U T N
    (fun _ ha => Or.inr ha)
    (fun a ha x hx hxa => by
      apply le_antisymm hxa
      by_contra hnle
      have hlt : x < a := lt_of_le_not_ge hxa hnle
      have hrr := hr hlt
      have hlow := (hU x hx).2
      have hea := (hT a ha).2
      omega)
    (fun a ha => by
      obtain ⟨x,hx,hax⟩ := hup a (hT a ha).1 (hT a ha).2
      have he : x ∈ {x | x ∈ U ∧ a < x} := by rw [hset a ha]; exact ⟨hx,hax⟩
      exact ⟨x,he.1,he.2⟩)
    (fun a ha k hk => by rw [hset a ha]; exact hupper a (hT a ha).1 (hT a ha).2 k hk)
    hnN c hcU hn hd ha
  refine ⟨c',d,onSet_mono P ?_ hc',hn',hd',ha',onSet_mono P (fun x hx => (hU x hx).1) hD,hDn,hdd⟩
  intro x hx
  rcases hx.1 with hxU | hxT
  · exact hxU
  · exact False.elim (hx.2 hxT)

theorem raise_rank (r : P → ℕ) (hr : StrictMono r) (D : Set P) (M N : ℕ)
    (hup : ∀ a ∈ D, r a < M → ∃ x ∈ D, a < x)
    (hupper : ∀ a ∈ D, r a < M → ∀ k ≤ N, ExactSet P {x | x ∈ D ∧ a < x} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ onSet P D) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P {x | x ∈ D ∧ M ≤ r x} ∧ Homogeneous P n c' ∧
      boundary P c' = 0 ∧ augmentation P c' = 0 ∧ d ∈ onSet P D ∧
      Homogeneous P (n+1) d ∧ boundary P d = c-c' := by
  have h : ∀ j ≤ M, ∃ c' d : Chain P, c' ∈ onSet P {x | x ∈ D ∧ j ≤ r x} ∧
      Homogeneous P n c' ∧ boundary P c' = 0 ∧ augmentation P c' = 0 ∧ d ∈ onSet P D ∧
      Homogeneous P (n+1) d ∧ boundary P d = c-c' := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨c,0,onSet_mono P (V := {x | x ∈ D ∧ 0 ≤ r x}) (fun x hx => ⟨hx,Nat.zero_le _⟩) hc,hn,hd,ha,
        (onSet P D).zero_mem,supported_zero P _,?_⟩
      simp
    | succ j ih =>
      intro hj
      obtain ⟨cj,dj,hcj,hnj,hdj,haj,hDj,hDnj,hddj⟩ := ih (by omega)
      obtain ⟨c',d',hc',hn',hd',ha',hD',hDn',hdd'⟩ := raise_rank_step P r hr D j N
        (fun a ha hr => hup a ha (by omega))
        (fun a ha hr k hk => hupper a ha (by omega) k hk) hnN cj hcj hnj hdj haj
      refine ⟨c',dj+d',hc',hn',hd',ha',(onSet P D).add_mem hDj hD',
        supported_add P hDnj hDn',?_⟩
      rw [map_add,hddj,hdd']
      abel
  exact h M le_rfl
end

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

theorem carrier_section (p : Q →o P) (N : ℕ)
    (hne : ∀ a : P, ∃ q : Q, p q ≤ a)
    (hex : ∀ a : P, ∀ k ≤ N, ExactSet Q {q | p q ≤ a} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ module P)
    (hn : Homogeneous P n c) (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ z : Chain Q, ∃ d : Chain P, z ∈ module Q ∧ Homogeneous Q n z ∧
      boundary Q z = 0 ∧ augmentation Q z = 0 ∧ d ∈ module P ∧
      Homogeneous P (n+1) d ∧ boundary P d = c - mapChain Q p z := by
  classical
  let K : Simplex P → Set Q := fun s => {q | p q ≤ s.1}
  let L : Simplex P → Set P := fun s => {x | x ≤ s.1}
  let point : Simplex P → Chain Q := fun s => vertex Q ((hne s.1).choose)
  let fill := fun s k z => cycleFill Q (K s) k z
  let F := OrderBasedComplex.chosenExtend (based P) point fill
  have hvalid : ∀ s t, Descending P s → t ∈ (boundary P (Finsupp.single s 1)).support →
      Descending P t := fun _ _ hs ht => hs.boundary P ht
  have hface : ∀ s t, Descending P s → t ∈ (boundary P (Finsupp.single s 1)).support →
      t.1 ≤ s.1 := fun s t hs ht => hs.le_head P (boundary_vertices P s t ht (head_mem_vertices P t))
  have hpoint (s : Simplex P) (_ : Descending P s) : point s ∈ onSet Q (K s) ∧
      point s ∈ degreeModule Q 0 ∧ boundary Q (point s) = 0 ∧ augmentation Q (point s) = 1 := by
    refine ⟨?_,?_,boundary_vertex Q _,augmentation_vertex Q _⟩
    · apply supported_single
      exact ⟨List.pairwise_singleton _ _,by
        rw [vertices_vertex]
        exact Set.singleton_subset_iff.mpr (hne s.1).choose_spec⟩
    · exact supported_single Q (P := fun t => degree Q t = 0) rfl 1
  have hfill (s : Simplex P) (_ : Descending P s) (k : ℕ) (hk : k ≤ N) (z : Chain Q)
      (hz : z ∈ onSet Q (K s)) (hzdeg : z ∈ degreeModule Q k)
      (hzd : boundary Q z = 0) (hza : augmentation Q z = 0) :=
    cycleFill_spec Q (hex s.1 k hk) hz hzdeg hzd hza
  have hF (s : Simplex P) (hs : Descending P s) (hdeg : degree P s ≤ N+1) :
      F (Finsupp.single s 1) ∈ onSet Q (K s) ∧
      F (Finsupp.single s 1) ∈ degreeModule Q (degree P s) ∧
      boundary Q (F (Finsupp.single s 1)) = F (boundary P (Finsupp.single s 1)) ∧
      augmentation Q (F (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact OrderBasedComplex.chosen_spec (based P) point fill (boundary Q) (augmentation Q)
      (degreeModule Q) (Descending P) (fun s => onSet Q (K s)) N hvalid
      (fun s t hs ht => onSet_mono Q (fun _ hx => hx.trans (hface s t hs ht))) hpoint hfill s hs hdeg
  let G := (mapChain Q p).comp F
  have hG (s : Simplex P) (hs : Descending P s) (hdeg : degree P s ≤ N) :
      G (Finsupp.single s 1) ∈ onSet P (L s) ∧
      G (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P (G (Finsupp.single s 1)) = G (boundary P (Finsupp.single s 1)) ∧
      augmentation P (G (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    have hh := hF s hs (by omega)
    refine ⟨map_onSet Q p (fun q hq => hq) (fun _ _ _ _ hxy => p.monotone hxy) hh.1,
      map_degree Q p hh.2.1,?_,?_⟩
    · change boundary P (mapChain Q p _) = mapChain Q p _
      rw [boundary_mapChain,hh.2.2.1]
    · change augmentation P (mapChain Q p _) = _
      rw [augmentation_mapChain,hh.2.2.2]
  let fillL := fun s k z => cycleFill P (L s) k z
  let H := OrderBasedComplex.chosenHomotopy (based P) fillL LinearMap.id G
  have hI (s : Simplex P) (hs : Descending P s) (_ : degree P s ≤ N) :
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ onSet P (L s) ∧
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) =
        (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (boundary P (Finsupp.single s 1)) ∧
      augmentation P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact ⟨supported_single P ⟨hs,fun _ hx => hs.le_head P hx⟩ 1,
      supported_single P (P := fun t => degree P t = degree P s) rfl 1,rfl,rfl⟩
  have hH (s : Simplex P) (hs : Descending P s) (hdeg : degree P s ≤ N) :
      H (Finsupp.single s 1) ∈ onSet P (L s) ∧
      H (Finsupp.single s 1) ∈ degreeModule P (degree P s+1) ∧
      boundary P (H (Finsupp.single s 1)) + H (boundary P (Finsupp.single s 1)) =
        Finsupp.single s 1 - G (Finsupp.single s 1) ∧
      augmentation P (H (Finsupp.single s 1)) = 0 := by
    apply OrderBasedComplex.chosenHomotopy_spec (based P) fillL LinearMap.id G (boundary P)
      (augmentation P) (degreeModule P) (Descending P) (fun s => onSet P (L s)) N hvalid
      (fun s t hs ht => onSet_mono P (fun _ hx => hx.trans (hface s t hs ht))) hI hG ?_ s hs hdeg
    intro t ht k hk z hz hzdeg hzd hza
    exact cycleFill_spec P (exactSet_of_top P (U := L t) t.1 le_rfl (fun _ hx => hx) k) hz hzdeg hzd hza
  have hsd (s : Simplex P) (hs : s ∈ c.support) : degree P s ≤ N := (hn s hs).le.trans hnN
  refine ⟨F c,H c,?_,?_,?_,?_,?_,?_,?_⟩
  · apply OrderBasedComplex.map_mem_of_support
    intro s hs
    exact onSet_le_module Q _ (hF s (hc hs) (by have hh := hsd s hs; omega)).1
  · apply OrderBasedComplex.map_mem_of_support F (degreeModule Q n)
    intro s hs
    rw [← hn s hs]
    exact (hF s (hc hs) (by have hh := hsd s hs; omega)).2.1
  · have he := OrderBasedComplex.linear_eq_on_support ((boundary Q).comp F) (F.comp (boundary P)) c
      (fun s hs => (hF s (hc hs) (by have hh := hsd s hs; omega)).2.2.1)
    simpa only [LinearMap.comp_apply,hd,map_zero] using he
  · have he := OrderBasedComplex.linear_eq_on_support ((augmentation Q).comp F) (augmentation P) c
      (fun s hs => (hF s (hc hs) (by have hh := hsd s hs; omega)).2.2.2)
    simpa only [LinearMap.comp_apply,ha] using he
  · apply OrderBasedComplex.map_mem_of_support
    intro s hs
    exact onSet_le_module P _ (hH s (hc hs) (hsd s hs)).1
  · apply OrderBasedComplex.map_mem_of_support H (degreeModule P (n+1))
    intro s hs
    rw [← hn s hs]
    exact (hH s (hc hs) (hsd s hs)).2.1
  · have he := OrderBasedComplex.linear_eq_on_support ((boundary P).comp H+H.comp (boundary P))
      (LinearMap.id-G) c (fun s hs => (hH s (hc hs) (hsd s hs)).2.2.1)
    change boundary P (H c) = c - G c
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,hd,map_zero,add_zero,
      LinearMap.sub_apply,LinearMap.id_apply] using he
end

open OrderListChains
end OrderChains

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
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisGroundMatching
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant
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

lemma ground_exactIn [Nonempty I] (n : ℕ) : ExactIn (GroundFaces (I := I)) n := by
  classical
  apply exactIn_of_bottom _ ⟨Finset.univ,Finset.univ_nonempty⟩
  intro N
  exact Finset.subset_univ _

theorem near_nullIn [Nonempty I] (m : ℕ)
    (hav : ∀ B : CutDown.Near C m, (M.available B.val.val Finset.univ).Nonempty)
    {n : ℕ} (c : Chain (CutDown.Near C m)) (hc : c ∈ module (CutDown.Near C m))
    (hn : Homogeneous _ n c) (hd : boundary _ c = 0) (ha : augmentation _ c = 0) :
    ∃ d : Chain (CutDown C), d ∈ module (CutDown C) ∧ Homogeneous _ (n+1) d ∧
      boundary _ d = mapChain _ (CutDown.nearInclude C m) c := by
  classical
  let P := CutDown.Near C m
  let Q := M.Pair m
  let D := CutDown C
  let G := GroundFaces (I := I)
  let a := CutDown.nearInclude C m
  let p := M.projectPair m
  let q := M.contractPair m
  let s := M.selectedPair m
  let g := M.ground
  let f := a.comp p
  let t := g.comp s
  obtain ⟨z,e,hz,hzn,hzd,hza,he,hen,hed⟩ := carrier_section P p n
    (fun B => M.fiber_nonempty m B (hav B))
    (fun B k _ => exactSet_of_subtype Q
      ⟨(M.fiber_nonempty m B (hav B)).choose,(M.fiber_nonempty m B (hav B)).choose_spec⟩
      (M.fiber_exactIn m B (hav B) k)) le_rfl c hc hn hd ha
  have hsz : mapChain Q s z ∈ module G := map_mem Q s hz
  have hszn : Homogeneous G n (mapChain Q s z) := map_degree Q s hzn
  have hszd : boundary G (mapChain Q s z) = 0 := by rw [boundary_mapChain,hzd,map_zero]
  have hsza : augmentation G (mapChain Q s z) = 0 := by rw [augmentation_mapChain,hza]
  obtain ⟨b,hb,hbn,hbd⟩ := ground_exactIn (I := I) n _ hsz hszn hszd hsza
  have hqf : ∀ x : Q, q x ≤ f x := M.contractPair_le_base m
  have hqt : ∀ x : Q, q x ≤ t x := M.contractPair_le_ground m
  have hHf := comparison_boundary Q q f z
  have hHt := comparison_boundary Q q t z
  rw [hzd,map_zero,add_zero] at hHf hHt
  refine ⟨mapChain P a e + mapChain G g b + comparison Q q t z - comparison Q q f z,
    (module D).sub_mem ((module D).add_mem
      ((module D).add_mem (map_mem P a he) (map_mem G g hb))
      (comparison_mem Q q t hqt hz)) (comparison_mem Q q f hqf hz),
    supported_sub D (supported_add D (supported_add D (map_degree P a hen)
      (map_degree G g hbn)) (comparison_degree Q q t hzn)) (comparison_degree Q q f hzn),?_⟩
  rw [map_sub,map_add,map_add,boundary_mapChain,boundary_mapChain,hed,hbd,hHt,hHf,
    map_sub,mapChain_comp,mapChain_comp]
  change mapChain P a c - mapChain Q f z + mapChain Q t z +
    (mapChain Q q z - mapChain Q t z) - (mapChain Q q z - mapChain Q f z) = _
  abel
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

theorem exactIn_high_rank [Nonempty S] (C : Basis ρ) (n : ℕ)
    (hC : 2 * (2 * 2^(n+2) + 1) ≤ rank ρ C) : ExactIn (CutDown C) n := by
  classical
  let L := 2^(n+2)
  let k := 2*L+1
  let m := rank ρ C - L
  have hk : 0 < k := by dsimp [k]; omega
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  let M := groundMatching C (Classical.choice ‹Nonempty S›) k hC
  have hL : 2 ≤ L := by
    dsimp [L]
    have hh := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n+2)
    simpa using hh
  have hLm : L ≤ rank ρ C := by dsimp [L] at *; omega
  have hml : m + L = rank ρ C := Nat.sub_add_cancel hLm
  have hav (B : Near C m) : (M.available B.val.val Finset.univ).Nonempty := by
    apply M.available_nonempty B.val.upper
    simp only [Finset.card_univ,Fintype.card_fin]
    have hb := B.property
    dsimp [k]
    omega
  let e := M.edge ⟨0,hk⟩
  let u : Near C m := ⟨⟨e.lower,e.lower_cutRefines,e.lower_ne⟩,by
    have he := e.rank_lower
    change m ≤ rank ρ e.lower
    omega⟩
  intro c hc hn hd ha
  have hcU : c ∈ onSet (CutDown C) Set.univ := fun s hs => ⟨hc hs,Set.subset_univ _⟩
  obtain ⟨c',d,hc',hn',hd',ha',hdD,hdn,hdd⟩ := raise_rank (CutDown C)
    (fun B => rank ρ B.val) strictMono_rank Set.univ m n
    (fun B _ hB => by
      obtain ⟨D,hD⟩ := upper_nonempty B (by omega)
      exact ⟨D,Set.mem_univ _,hD⟩)
    (fun B _ hB j hj => by
      have hrj : rank ρ B.val + 2^(j+2) ≤ rank ρ C := by
        have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.add_le_add_right hj 2)
        change 2^(j+2) ≤ L at hp
        omega
      have hx := properCutInterval_exactIn ρ B.upper B.ne hrj
      have hex : ExactIn {D : CutDown C // B < D} j :=
        exactIn_of_orderIso B.upperInterval hx
      obtain ⟨D,hD⟩ := upper_nonempty B (by omega)
      have hh := exactSet_of_subtype (CutDown C) ⟨D,hD⟩ hex
      have hset : {x : CutDown C | x ∈ Set.univ ∧ B < x} = {x | B < x} := by
        ext x
        simp only [Set.mem_ofPred_eq,Set.mem_univ,true_and]
      rw [hset]
      exact hh)
    le_rfl c hcU hn hd ha
  let U : Set (CutDown C) := {B | m ≤ rank ρ B.val}
  have hc'U : c' ∈ onSet (CutDown C) U :=
    onSet_mono _ (fun _ hx => hx.2) hc'
  let pr := project (CutDown C) U u
  have hpr := map_onSet (CutDown C) pr (U := U) (V := Set.univ) (fun _ _ => Set.mem_univ _)
    (fun x hx y hy hxy => by
      change (pr x).val ≤ (pr y).val
      change (project (CutDown C) U u x).val ≤ (project (CutDown C) U u y).val
      rw [project_val (CutDown C) (U := U) u hx,project_val (CutDown C) (U := U) u hy]
      exact hxy) hc'U
  have hprd : boundary (Near C m) (mapChain (CutDown C) pr c') = 0 := by
    change boundary U (mapChain (CutDown C) pr c') = 0
    rw [OrderListChains.boundary_mapChain,hd',map_zero]
  have hpra : augmentation (Near C m) (mapChain (CutDown C) pr c') = 0 := by
    change augmentation U (mapChain (CutDown C) pr c') = 0
    rw [OrderListChains.augmentation_mapChain,ha']
  obtain ⟨b,hb,hbn,hbd⟩ := M.near_nullIn m hav (mapChain _ pr c')
    (onSet_le_module _ _ hpr) (map_degree _ pr hn') hprd hpra
  have hbd' : boundary (CutDown C) b = c' := by
    rw [hbd]
    change mapChain U (fun x : U => x.val) (mapChain (CutDown C) pr c') = c'
    rw [OrderChains.mapChain_comp]
    have he := mapChain_eq_on (CutDown C) ((fun x : U => x.val) ∘ pr) id
      (c := c') (fun s hs x hx => project_val _ u ((hc'U hs).2 hx))
    rw [he,mapChain_id]
  refine ⟨d+b,(module _).add_mem (onSet_le_module _ _ hdD) hb,
    supported_add _ hdn hbn,?_⟩
  rw [map_add,hdd,hbd']
  abel
end TwistedBrin.Basis.CutDown

namespace TwistedBrin.Basis
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace CutBasis
lemma lower_nonempty [Nonempty S] (C : CutBasis ρ) (h : 2 ≤ rank ρ C.val) :
    ∃ B : CutBasis ρ, B < C := by
  let M := groundMatching C.val (Classical.choice ‹Nonempty S›) 1 (by simpa using h)
  let e := M.edge 0
  exact ⟨⟨e.lower⟩,lt_of_le_of_ne e.lower_cutRefines (fun he => e.lower_ne (congrArg CutBasis.val he))⟩
lemma lower_exactSet_oai [Nonempty S] (C : CutBasis ρ) (n : ℕ)
    (h : 2*(2*2^(n+2)+1) ≤ rank ρ C.val) : ExactSet (CutBasis ρ) (Set.Iio C) n := by
  have ht : 2 ≤ rank ρ C.val := by omega
  obtain ⟨B,hB⟩ := lower_nonempty C ht
  exact exactSet_of_subtype (CutBasis ρ) ⟨B,hB⟩
    (exactIn_of_orderIso (lowerEquiv C) (CutDown.exactIn_high_rank C.val n h))

end CutBasis
end TwistedBrin.Basis

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.TwistedBrin.Basis.CutBasis.lower_exactSet_oai.{u, v} := @OAI.TwistedBrin.Basis.CutBasis.lower_exactSet_oai.{u, v}

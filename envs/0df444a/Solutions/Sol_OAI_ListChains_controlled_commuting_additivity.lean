-- Prove2me | solution 1 for OAI.ListChains.controlled_commuting_additivity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T02:37:24.611381+00:00
-- url     : https://prove2.me/submissions/c354b699-0fb6-4673-a582-6321fe30a34d

import Mathlib
import Definitions.Def_OAIQ66So013
import Definitions.Def_OAIQ66So014

section
-- module Solutions.OAIQ066_SO.FiniteType_BasedComplex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
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

lemma homotopy_mem (K : B → Submodule ℤ M)
    (hF : ∀ b, F (Finsupp.single b 1) ∈ K b)
    (hG : ∀ b, G (Finsupp.single b 1) ∈ K b)
    (hcone : ∀ b c, c ∈ K b → (T b).cone c ∈ K b)
    (hface : ∀ b t, t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
    (b : B) : homotopy C d aug T F G (Finsupp.single b 1) ∈ K b := by
  suffices ∀ n b, C.degree b = n → homotopy C d aug T F G (Finsupp.single b 1) ∈ K b by
    exact this (C.degree b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hn
    rw [homotopy_equation]
    apply hcone
    apply (K b).sub_mem ((K b).sub_mem (hF b) (hG b))
    apply map_mem_of_support
    intro t ht
    apply hface b t ht
    apply ih (C.degree t) _ t rfl
    have hd := C.lowers b t ht
    omega

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

end BasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryFiniteStage
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains

variable (G : Type*)

lemma supported_mono {P Q : Simplex G → Prop} (hPQ : ∀ s, P s → Q s) {c : Chain G}
    (hc : Supported G P c) : Supported G Q c := fun s hs => hPQ s (hc s hs)

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FreeTensor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
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

lemma vertexModule_mono {V W : Set G} (h : V ⊆ W) : vertexModule G V ≤ vertexModule G W := by
  intro c hc
  exact (mem_vertexModule G).mpr
    (supported_mono G (fun _ hs => hs.trans h) ((mem_vertexModule G).mp hc))

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
-- module Solutions.OAIQ066_SO.FiniteType_FreeTensorPureMem
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G H : Type*)

lemma tensor_mem_degree {p q : ℕ} {x : Chain G} {y : Chain H}
    (hx : x ∈ degreeModule G p) (hy : y ∈ degreeModule H q) :
    tensor G H x y ∈ biDegreeModule G H (p+q) := by
  apply FreeTensor.pure_mem
  intro s hs t ht
  apply FreeTensor.single_mem_supported
  exact congrArg₂ (· + ·) (hx hs) (hy ht)

lemma tensor_mem_vertices {V : Set G} {W : Set H} {x : Chain G} {y : Chain H}
    (hx : x ∈ vertexModule G V) (hy : y ∈ vertexModule H W) :
    tensor G H x y ∈ biVertexModule G H V W := by
  apply FreeTensor.pure_mem
  intro s hs t ht
  apply FreeTensor.single_mem_supported
  exact ⟨hx hs, hy ht⟩

lemma biBoundary_vertices (s t : Simplex G × Simplex H)
    (ht : t ∈ (biBoundary G H (Finsupp.single s 1)).support) :
    vertices G t.1 ⊆ vertices G s.1 ∧ vertices H t.2 ⊆ vertices H s.2 := by
  suffices hc : biBoundary G H (Finsupp.single s 1) ∈
      biVertexModule G H (vertices G s.1) (vertices H s.2) by exact hc ht
  rw [← FreeTensor.pure_single_one, biBoundary_tensor]
  apply Submodule.add_mem
  · apply tensor_mem_vertices
    · exact fun _ hx => boundary_vertices G s.1 _ hx
    · exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1
  · apply tensor_mem_vertices
    · rw [sign_single]
      apply Submodule.smul_mem
      exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1
    · exact fun _ hy => boundary_vertices H s.2 _ hy

lemma biVertexModule_mono {V V' : Set G} {W W' : Set H} (hV : V ⊆ V') (hW : W ⊆ W') :
    biVertexModule G H V W ≤ biVertexModule G H V' W' := by
  intro c hc s hs
  exact ⟨(hc hs).1.trans hV, (hc hs).2.trans hW⟩

lemma K_mem_vertices {V : Set G} {a : G} (ha : a ∈ V) (c : Chain G) :
    K G a c ∈ vertexModule G V := by
  rw [K_apply]
  exact (vertexModule G V).smul_mem _ (vertex_mem_vertexModule G ha)

lemma biCone_mem_vertices {V : Set G} {W : Set H} {a : G} {b : H}
    (ha : a ∈ V) (hb : b ∈ W) {c : BiChain G H}
    (hc : c ∈ biVertexModule G H V W) : biCone G H a b c ∈ biVertexModule G H V W := by
  apply BasedComplex.map_mem_of_support (biCone G H a b) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, biCone_tensor]
  apply Submodule.add_mem
  · apply tensor_mem_vertices
    · apply cone_mem_vertexModule G ha
      exact FreeTensor.single_mem_supported _ (hc hs).1 1
    · exact FreeTensor.single_mem_supported _ (hc hs).2 1
  · apply tensor_mem_vertices
    · exact K_mem_vertices G ha _
    · apply cone_mem_vertexModule H hb
      exact FreeTensor.single_mem_supported _ (hc hs).2 1

lemma biCone_mem_degree {n : ℕ} (a : G) (b : H) {c : BiChain G H}
    (hc : c ∈ biDegreeModule G H n) : biCone G H a b c ∈ biDegreeModule G H (n+1) := by
  apply BasedComplex.map_mem_of_support (biCone G H a b) _ c
  intro s hs
  have hn : degree G s.1 + degree H s.2 = n := hc hs
  rw [← FreeTensor.pure_single_one, biCone_tensor]
  apply Submodule.add_mem
  · have he : n+1 = (degree G s.1+1) + degree H s.2 := by omega
    rw [he]
    apply tensor_mem_degree
    · apply cone_mem_degreeModule
      apply FreeTensor.single_mem_supported
      rfl
    · apply FreeTensor.single_mem_supported
      rfl
  · rw [K_apply, augmentation_single]
    by_cases hz : s.1.2 = []
    · rw [ite_eq_left hz, one_smul]
      have hd : degree G s.1 = 0 := by simp only [degree, hz, List.length_nil]
      have he : n+1 = 0 + (degree H s.2+1) := by omega
      rw [he]
      apply tensor_mem_degree
      · exact vertex_mem_degreeModule G a
      · apply cone_mem_degreeModule
        apply FreeTensor.single_mem_supported
        rfl
    · rw [ite_eq_right hz, zero_smul, map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _

lemma biBoundary_diagTensor (c : Chain G) :
    biBoundary G G (diagTensor G c) = diagTensor G (boundary G c) :=
  BasedComplex.d_extend ..

lemma biAugmentation_diagTensor (c : Chain G) :
    biAugmentation G G (diagTensor G c) = augmentation G c :=
  BasedComplex.aug_extend ..

lemma diagTensor_single_vertices (s : Simplex G) :
    diagTensor G (Finsupp.single s 1) ∈
      biVertexModule G G (vertices G s) (vertices G s) := by
  apply BasedComplex.extend_mem (K := fun s =>
    biVertexModule G G (vertices G s) (vertices G s))
  · intro s _
    apply tensor_mem_vertices
    · exact vertex_mem_vertexModule G (head_mem_vertices G s)
    · exact vertex_mem_vertexModule G (head_mem_vertices G s)
  · intro s c hc
    exact biCone_mem_vertices G G (head_mem_vertices G s) (head_mem_vertices G s) hc
  · intro s t ht
    exact biVertexModule_mono G G (boundary_vertices G s t ht) (boundary_vertices G s t ht)

lemma diagTensor_mem_degree {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    diagTensor G c ∈ biDegreeModule G G n := by
  apply BasedComplex.map_mem_of_support (diagTensor G) _ c
  intro s hs
  have hn : degree G s = n := hc hs
  rw [← hn]
  apply BasedComplex.extend_degree (D := biDegreeModule G G)
  · intro s _
    exact tensor_mem_degree G G (vertex_mem_degreeModule G s.1) (vertex_mem_degreeModule G s.1)
  · intro s n c hc
    exact biCone_mem_degree G G s.1 s.1 hc

lemma boundary_productComparison (c : BiChain G H) :
    boundary (G × H) (productComparison G H c) = productComparison G H (biBoundary G H c) :=
  BasedComplex.d_extend ..

lemma augmentation_productComparison (c : BiChain G H) :
    augmentation (G × H) (productComparison G H c) = biAugmentation G H c :=
  BasedComplex.aug_extend ..

lemma productComparison_single_vertices (s : Simplex G × Simplex H) :
    productComparison G H (Finsupp.single s 1) ∈
      vertexModule (G × H) (vertices G s.1 ×ˢ vertices H s.2) := by
  apply BasedComplex.extend_mem (K := fun s : Simplex G × Simplex H =>
    vertexModule (G × H) (vertices G s.1 ×ˢ vertices H s.2))
  · intro s _
    exact vertex_mem_vertexModule (G × H)
      (V := vertices G s.1 ×ˢ vertices H s.2)
      ⟨head_mem_vertices G s.1, head_mem_vertices H s.2⟩
  · intro s c hc
    exact cone_mem_vertexModule (G × H)
      (V := vertices G s.1 ×ˢ vertices H s.2)
      ⟨head_mem_vertices G s.1, head_mem_vertices H s.2⟩ hc
  · intro s t ht
    apply vertexModule_mono
    exact Set.prod_mono (biBoundary_vertices G H s t ht).1 (biBoundary_vertices G H s t ht).2

lemma productComparison_mem_vertices {V : Set G} {W : Set H} {c : BiChain G H}
    (hc : c ∈ biVertexModule G H V W) :
    productComparison G H c ∈ vertexModule (G × H) (V ×ˢ W) := by
  apply BasedComplex.map_mem_of_support (productComparison G H) _ c
  intro s hs
  apply vertexModule_mono (G × H) (Set.prod_mono (hc hs).1 (hc hs).2)
  exact productComparison_single_vertices G H s

lemma productComparison_mem_degree {n : ℕ} {c : BiChain G H}
    (hc : c ∈ biDegreeModule G H n) : productComparison G H c ∈ degreeModule (G × H) n := by
  apply BasedComplex.map_mem_of_support (productComparison G H) _ c
  intro s hs
  have hn : biDegree G H s = n := hc hs
  rw [← hn]
  apply BasedComplex.extend_degree (D := degreeModule (G × H))
  · intro s _
    exact vertex_mem_degreeModule (G × H) (s.1.1,s.2.1)
  · intro s n c hc
    exact cone_mem_degreeModule (G × H) (s.1.1,s.2.1) hc

end

variable (G : Type*)

lemma sign_squared (c : Chain G) : sign G (sign G c) = c := by
  have he : sign G ∘ₗ sign G = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, LinearMap.id_apply, sign_single,
      LinearMap.map_smul, smul_smul, ← mul_pow, mul_neg_one, neg_neg, one_pow, one_smul]
  exact LinearMap.congr_fun he c

lemma sign_eq_smul_of_degree {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    sign G c = (-1 : ℤ)^n • c := by
  have he := BasedComplex.linear_eq_on_support (sign G)
    ((-1 : ℤ)^n • (LinearMap.id : Chain G →ₗ[ℤ] Chain G)) c (by
      intro s hs
      rw [sign_single]
      change _ = (-1 : ℤ)^n • Finsupp.single s 1
      rw [hc hs])
  exact he

lemma sign_map_of_degree (F : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G n) (c : Chain G) :
    sign G (F c) = F (sign G c) := by
  have he : sign G ∘ₗ F = F ∘ₗ sign G := by
    apply Finsupp.lhom_ext
    intro s r
    have hs : Finsupp.single s r ∈ degreeModule G (degree G s) := by
      apply FreeTensor.single_mem_supported
      rfl
    simp only [LinearMap.comp_apply, sign_eq_smul_of_degree G (hF _ _ hs),
      sign_single, LinearMap.map_smul]
  exact LinearMap.congr_fun he c

lemma sign_map_of_raising (J : Chain G →ₗ[ℤ] Chain G)
    (hJ : ∀ n c, c ∈ degreeModule G n → J c ∈ degreeModule G (n+1)) (c : Chain G) :
    sign G (J c) = -J (sign G c) := by
  have he : sign G ∘ₗ J = -(J ∘ₗ sign G) := by
    apply Finsupp.lhom_ext
    intro s r
    have hs : Finsupp.single s r ∈ degreeModule G (degree G s) := by
      apply FreeTensor.single_mem_supported
      rfl
    simp only [LinearMap.comp_apply, LinearMap.neg_apply,
      sign_eq_smul_of_degree G (hJ _ _ hs), sign_single, LinearMap.map_smul,
      pow_succ, mul_neg_one, neg_smul]
  exact LinearMap.congr_fun he c

lemma tensorHomotopy_tensor (F F' J : Chain G →ₗ[ℤ] Chain G) (x y : Chain G) :
    tensorHomotopy G F F' J (tensor G G x y) =
      tensor G G (J x) (F y) + tensor G G (F' (sign G x)) (J y) := by
  simp only [tensorHomotopy, LinearMap.add_apply, tensorMap_tensor, LinearMap.comp_apply]

theorem boundary_tensorHomotopy (F F' J : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ c, boundary G (F c) = F (boundary G c))
    (hF' : ∀ c, boundary G (F' c) = F' (boundary G c))
    (hJ : ∀ c, boundary G (J c) + J (boundary G c) = F c - F' c)
    (hdegF' : ∀ n c, c ∈ degreeModule G n → F' c ∈ degreeModule G n)
    (hdegJ : ∀ n c, c ∈ degreeModule G n → J c ∈ degreeModule G (n+1))
    (c : BiChain G G) :
    biBoundary G G (tensorHomotopy G F F' J c) +
        tensorHomotopy G F F' J (biBoundary G G c) =
      tensorMap G G F F c - tensorMap G G F' F' c := by
  have hdJ (c : Chain G) : boundary G (J c) = F c - F' c - J (boundary G c) :=
    eq_sub_iff_add_eq.mpr (hJ c)
  have he : biBoundary G G ∘ₗ tensorHomotopy G F F' J +
      tensorHomotopy G F F' J ∘ₗ biBoundary G G =
        tensorMap G G F F - tensorMap G G F' F' := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      tensorHomotopy_tensor, biBoundary_tensor, tensorMap_tensor,
      map_add, LinearMap.add_apply, hF, hF', hdJ, boundary_sign,
      sign_map_of_degree G F' hdegF', sign_map_of_raising G J hdegJ, sign_squared,
      map_neg, map_sub, LinearMap.neg_apply, LinearMap.sub_apply]
    abel
  exact LinearMap.congr_fun he c

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*)

lemma projectLeft_tensor (x : Chain G) (y : Chain H) :
    projectLeft G H (tensor G H x y) = augmentation H y • x := by
  rw [projectLeft, FreeTensor.lift_pure]
  rfl

lemma projectRight_tensor (x : Chain G) (y : Chain H) :
    projectRight G H (tensor G H x y) = augmentation G x • y := by
  rw [projectRight, FreeTensor.lift_pure]
  rfl

lemma boundary_projectLeft (c : BiChain G H) :
    boundary G (projectLeft G H c) = projectLeft G H (biBoundary G H c) := by
  have he : boundary G ∘ₗ projectLeft G H = projectLeft G H ∘ₗ biBoundary G H := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, biBoundary_tensor, map_add, projectLeft_tensor,
      augmentation_boundary, zero_smul, add_zero, LinearMap.map_smul]
  exact LinearMap.congr_fun he c

lemma boundary_projectRight (c : BiChain G H) :
    boundary H (projectRight G H c) = projectRight G H (biBoundary G H c) := by
  have he : boundary H ∘ₗ projectRight G H = projectRight G H ∘ₗ biBoundary G H := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, biBoundary_tensor, map_add, projectRight_tensor,
      augmentation_boundary, augmentation_sign, zero_smul, zero_add, LinearMap.map_smul]
  exact LinearMap.congr_fun he c

lemma augmentation_projectLeft (c : BiChain G H) :
    augmentation G (projectLeft G H c) = biAugmentation G H c := by
  have he : augmentation G ∘ₗ projectLeft G H = biAugmentation G H := by
    apply FreeTensor.ext
    intro x y
    rw [LinearMap.comp_apply, projectLeft_tensor, LinearMap.map_smul,
      biAugmentation_tensor, smul_eq_mul, mul_comm]
  exact LinearMap.congr_fun he c

lemma augmentation_projectRight (c : BiChain G H) :
    augmentation H (projectRight G H c) = biAugmentation G H c := by
  have he : augmentation H ∘ₗ projectRight G H = biAugmentation G H := by
    apply FreeTensor.ext
    intro x y
    rw [LinearMap.comp_apply, projectRight_tensor, LinearMap.map_smul,
      biAugmentation_tensor, smul_eq_mul]
  exact LinearMap.congr_fun he c

lemma projectLeft_mem_vertices {V : Set G} {W : Set H} {c : BiChain G H}
    (hc : c ∈ biVertexModule G H V W) : projectLeft G H c ∈ vertexModule G V := by
  apply BasedComplex.map_mem_of_support (projectLeft G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectLeft_tensor]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs).1 1

lemma projectRight_mem_vertices {V : Set G} {W : Set H} {c : BiChain G H}
    (hc : c ∈ biVertexModule G H V W) : projectRight G H c ∈ vertexModule H W := by
  apply BasedComplex.map_mem_of_support (projectRight G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectRight_tensor]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs).2 1

lemma projectLeft_mem_degree {n : ℕ} {c : BiChain G H}
    (hc : c ∈ biDegreeModule G H n) : projectLeft G H c ∈ degreeModule G n := by
  apply BasedComplex.map_mem_of_support (projectLeft G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectLeft_tensor, augmentation_single]
  split_ifs with hz
  · rw [one_smul]
    apply FreeTensor.single_mem_supported
    have hn : degree G s.1 + degree H s.2 = n := hc hs
    change degree G s.1 = n
    simpa only [degree, hz, List.length_nil, add_zero] using hn
  · rw [zero_smul]
    exact Submodule.zero_mem _

lemma projectRight_mem_degree {n : ℕ} {c : BiChain G H}
    (hc : c ∈ biDegreeModule G H n) : projectRight G H c ∈ degreeModule H n := by
  apply BasedComplex.map_mem_of_support (projectRight G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectRight_tensor, augmentation_single]
  split_ifs with hz
  · rw [one_smul]
    apply FreeTensor.single_mem_supported
    have hn : degree G s.1 + degree H s.2 = n := hc hs
    change degree H s.2 = n
    simpa only [degree, hz, List.length_nil, zero_add] using hn
  · rw [zero_smul]
    exact Submodule.zero_mem _

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

lemma biBoundary_includeLeft (b : H) (c : Chain G) :
    biBoundary G H (includeLeft G H b c) = includeLeft G H b (boundary G c) := by
  simp only [includeLeft_apply, biBoundary_tensor, boundary_vertex, map_zero, add_zero]

lemma biBoundary_includeRight (a : G) (c : Chain H) :
    biBoundary G H (includeRight G H a c) = includeRight G H a (boundary H c) := by
  simp only [includeRight_apply, biBoundary_tensor, boundary_vertex, map_zero,
    LinearMap.zero_apply, sign_vertex, zero_add]

lemma biAugmentation_includeLeft (b : H) (c : Chain G) :
    biAugmentation G H (includeLeft G H b c) = augmentation G c := by
  rw [includeLeft_apply, biAugmentation_tensor, augmentation_vertex, mul_one]

lemma biAugmentation_includeRight (a : G) (c : Chain H) :
    biAugmentation G H (includeRight G H a c) = augmentation H c := by
  rw [includeRight_apply, biAugmentation_tensor, augmentation_vertex, one_mul]

end

variable (G H : Type*)

lemma boundary_localHomotopy (v : G → H) (F Q : Chain G →ₗ[ℤ] Chain H)
    (hF : ∀ c, boundary H (F c) = F (boundary G c))
    (hQ : ∀ c, boundary H (Q c) = Q (boundary G c))
    (ha : ∀ c, augmentation H (F c) = augmentation H (Q c)) (c : Chain G) :
    boundary H (localHomotopy G H v F Q c) +
      localHomotopy G H v F Q (boundary G c) = F c - Q c :=
  BasedComplex.d_homotopy (based G) (boundary H) (augmentation H)
    (fun s => contraction H (v s.1)) F Q hF hQ ha c

lemma localHomotopy_single_vertices (v : G → H) (F Q : Chain G →ₗ[ℤ] Chain H)
    (Φ : Set G → Set H) (hmono : Monotone Φ)
    (hv : ∀ V x, x ∈ V → v x ∈ Φ V)
    (hF : ∀ s, F (Finsupp.single s 1) ∈ vertexModule H (Φ (vertices G s)))
    (hQ : ∀ s, Q (Finsupp.single s 1) ∈ vertexModule H (Φ (vertices G s)))
    (s : Simplex G) : localHomotopy G H v F Q (Finsupp.single s 1) ∈
        vertexModule H (Φ (vertices G s)) := by
  apply BasedComplex.homotopy_mem (K := fun s => vertexModule H (Φ (vertices G s)))
  · exact hF
  · exact hQ
  · intro s c hc
    exact cone_mem_vertexModule H (hv _ _ (head_mem_vertices G s)) hc
  · intro s t ht
    exact vertexModule_mono H (hmono (boundary_vertices G s t ht))

lemma localHomotopy_mem_degree (v : G → H) (F Q : Chain G →ₗ[ℤ] Chain H)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule H n)
    (hQ : ∀ n c, c ∈ degreeModule G n → Q c ∈ degreeModule H n)
    {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    localHomotopy G H v F Q c ∈ degreeModule H (n+1) := by
  apply BasedComplex.map_mem_of_support (localHomotopy G H v F Q) _ c
  intro s hs
  have hn : degree G s = n := hc hs
  rw [← hn]
  apply BasedComplex.homotopy_degree (D := degreeModule H)
  · intro s
    apply hF
    apply FreeTensor.single_mem_supported
    rfl
  · intro s
    apply hQ
    apply FreeTensor.single_mem_supported
    rfl
  · intro s n c hc
    exact cone_mem_degreeModule H (v s.1) hc

lemma boundary_projectionHomotopyLeft (c : Chain G) :
    boundary G (projectionHomotopyLeft G c) + projectionHomotopyLeft G (boundary G c) =
      projectLeft G G (diagTensor G c) - c := by
  apply boundary_localHomotopy
  · intro c
    simp only [LinearMap.comp_apply, boundary_projectLeft, biBoundary_diagTensor]
  · intro c
    rfl
  · intro c
    simp only [LinearMap.comp_apply, augmentation_projectLeft, biAugmentation_diagTensor,
      LinearMap.id_apply]

lemma boundary_projectionHomotopyRight (c : Chain G) :
    boundary G (projectionHomotopyRight G c) + projectionHomotopyRight G (boundary G c) =
      projectRight G G (diagTensor G c) - c := by
  apply boundary_localHomotopy
  · intro c
    simp only [LinearMap.comp_apply, boundary_projectRight, biBoundary_diagTensor]
  · intro c
    rfl
  · intro c
    simp only [LinearMap.comp_apply, augmentation_projectRight, biAugmentation_diagTensor,
      LinearMap.id_apply]

lemma projectionHomotopyLeft_single_vertices (s : Simplex G) :
    projectionHomotopyLeft G (Finsupp.single s 1) ∈ vertexModule G (vertices G s) := by
  apply localHomotopy_single_vertices G G id _ _ id
  · exact monotone_id
  · intro _ _ h
    exact h
  · intro s
    exact projectLeft_mem_vertices G G (diagTensor_single_vertices G s)
  · intro s
    exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1

lemma projectionHomotopyRight_single_vertices (s : Simplex G) :
    projectionHomotopyRight G (Finsupp.single s 1) ∈ vertexModule G (vertices G s) := by
  apply localHomotopy_single_vertices G G id _ _ id
  · exact monotone_id
  · intro _ _ h
    exact h
  · intro s
    exact projectRight_mem_vertices G G (diagTensor_single_vertices G s)
  · intro s
    exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1

lemma projectionHomotopyLeft_mem_degree {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : projectionHomotopyLeft G c ∈ degreeModule G (n+1) := by
  apply localHomotopy_mem_degree G G _ _ _ _ _ hc
  · intro n c hc
    exact projectLeft_mem_degree G G (diagTensor_mem_degree G hc)
  · intro n c hc
    exact hc

lemma projectionHomotopyRight_mem_degree {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : projectionHomotopyRight G c ∈ degreeModule G (n+1) := by
  apply localHomotopy_mem_degree G G _ _ _ _ _ hc
  · intro n c hc
    exact projectRight_mem_degree G G (diagTensor_mem_degree G hc)
  · intro n c hc
    exact hc

lemma boundary_endpointHomotopyLeft (b : H) (c : Chain G) :
    boundary (G × H) (endpointHomotopyLeft G H b c) +
      endpointHomotopyLeft G H b (boundary G c) =
        productComparison G H (includeLeft G H b c) - mapChain G (fun a => (a,b)) c := by
  apply boundary_localHomotopy
  · intro c
    simp only [LinearMap.comp_apply, boundary_productComparison, biBoundary_includeLeft]
  · exact boundary_mapChain G _
  · intro c
    simp only [LinearMap.comp_apply, augmentation_productComparison,
      biAugmentation_includeLeft, augmentation_mapChain]

lemma boundary_endpointHomotopyRight (a : G) (c : Chain H) :
    boundary (G × H) (endpointHomotopyRight G H a c) +
      endpointHomotopyRight G H a (boundary H c) =
        productComparison G H (includeRight G H a c) - mapChain H (fun b => (a,b)) c := by
  apply boundary_localHomotopy
  · intro c
    simp only [LinearMap.comp_apply, boundary_productComparison, biBoundary_includeRight]
  · exact boundary_mapChain H _
  · intro c
    simp only [LinearMap.comp_apply, augmentation_productComparison,
      biAugmentation_includeRight, augmentation_mapChain]

lemma endpointHomotopyLeft_single_vertices (b : H) (s : Simplex G) :
    endpointHomotopyLeft G H b (Finsupp.single s 1) ∈
      vertexModule (G × H) (vertices G s ×ˢ {b}) := by
  apply localHomotopy_single_vertices G (G × H) (fun a => (a,b)) _ _ (fun V => V ×ˢ {b})
  · intro V W h
    exact Set.prod_mono h (Set.Subset.refl _)
  · intro V x hx
    exact ⟨hx,rfl⟩
  · intro s
    apply productComparison_mem_vertices G H
    apply tensor_mem_vertices
    · exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1
    · exact vertex_mem_vertexModule H rfl
  · intro s
    exact mapChain_mem_vertices G (fun a => (a,b))
      (V := vertices G s) (W := vertices G s ×ˢ {b}) (fun _ ha => ⟨ha,rfl⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma endpointHomotopyRight_single_vertices (a : G) (s : Simplex H) :
    endpointHomotopyRight G H a (Finsupp.single s 1) ∈
      vertexModule (G × H) ({a} ×ˢ vertices H s) := by
  apply localHomotopy_single_vertices H (G × H) (fun b => (a,b)) _ _ (fun V => {a} ×ˢ V)
  · intro V W h
    exact Set.prod_mono (Set.Subset.refl _) h
  · intro V x hx
    exact ⟨rfl,hx⟩
  · intro s
    apply productComparison_mem_vertices G H
    apply tensor_mem_vertices
    · exact vertex_mem_vertexModule G rfl
    · exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1
  · intro s
    exact mapChain_mem_vertices H (fun b => (a,b))
      (V := vertices H s) (W := {a} ×ˢ vertices H s) (fun _ ha => ⟨rfl,ha⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma endpointHomotopyLeft_mem_degree (b : H) {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : endpointHomotopyLeft G H b c ∈ degreeModule (G × H) (n+1) := by
  apply localHomotopy_mem_degree G (G × H) _ _ _ _ _ hc
  · intro n c hc
    apply productComparison_mem_degree G H
    simpa only [add_zero, includeLeft_apply] using tensor_mem_degree G H hc (vertex_mem_degreeModule H b)
  · intro n c hc
    exact mapChain_mem_degree G _ hc

lemma endpointHomotopyRight_mem_degree (a : G) {n : ℕ} {c : Chain H}
    (hc : c ∈ degreeModule H n) : endpointHomotopyRight G H a c ∈ degreeModule (G × H) (n+1) := by
  apply localHomotopy_mem_degree H (G × H) _ _ _ _ _ hc
  · intro n c hc
    apply productComparison_mem_degree G H
    simpa only [zero_add, includeRight_apply] using tensor_mem_degree G H (vertex_mem_degreeModule G a) hc
  · intro n c hc
    exact mapChain_mem_degree H _ hc

lemma tensorMap_mem_degree {G' H' : Type*}
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G' n)
    (hQ : ∀ n c, c ∈ degreeModule H n → Q c ∈ degreeModule H' n)
    {n : ℕ} {c : BiChain G H} (hc : c ∈ biDegreeModule G H n) :
    tensorMap G H F Q c ∈ biDegreeModule G' H' n := by
  apply BasedComplex.map_mem_of_support (tensorMap G H F Q) _ c
  intro s hs
  have hn : degree G s.1 + degree H s.2 = n := hc hs
  rw [← hn, ← FreeTensor.pure_single_one, tensorMap_tensor]
  apply tensor_mem_degree
  · apply hF
    apply FreeTensor.single_mem_supported
    rfl
  · apply hQ
    apply FreeTensor.single_mem_supported
    rfl

lemma tensorMap_mem_vertices {G' H' : Type*}
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    {V : Set G} {W : Set H} {V' : Set G'} {W' : Set H'}
    (hF : ∀ c, c ∈ vertexModule G V → F c ∈ vertexModule G' V')
    (hQ : ∀ c, c ∈ vertexModule H W → Q c ∈ vertexModule H' W')
    {c : BiChain G H} (hc : c ∈ biVertexModule G H V W) :
    tensorMap G H F Q c ∈ biVertexModule G' H' V' W' := by
  apply BasedComplex.map_mem_of_support (tensorMap G H F Q) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, tensorMap_tensor]
  apply tensor_mem_vertices
  · exact hF _ (FreeTensor.single_mem_supported _ (hc hs).1 1)
  · exact hQ _ (FreeTensor.single_mem_supported _ (hc hs).2 1)

lemma sign_map_of_degree_between (F : Chain G →ₗ[ℤ] Chain H)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule H n) (c : Chain G) :
    sign H (F c) = F (sign G c) := by
  have he : sign H ∘ₗ F = F ∘ₗ sign G := by
    apply Finsupp.lhom_ext
    intro s r
    have hs : Finsupp.single s r ∈ degreeModule G (degree G s) := by
      apply FreeTensor.single_mem_supported
      rfl
    simp only [LinearMap.comp_apply, sign_eq_smul_of_degree H (hF _ _ hs),
      sign_single, LinearMap.map_smul]
  exact LinearMap.congr_fun he c

lemma boundary_tensorMap {G' H' : Type*}
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    (hF : ∀ c, boundary G' (F c) = F (boundary G c))
    (hQ : ∀ c, boundary H' (Q c) = Q (boundary H c))
    (hdF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G' n)
    (c : BiChain G H) :
    biBoundary G' H' (tensorMap G H F Q c) = tensorMap G H F Q (biBoundary G H c) := by
  have he : biBoundary G' H' ∘ₗ tensorMap G H F Q =
      tensorMap G H F Q ∘ₗ biBoundary G H := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, tensorMap_tensor, biBoundary_tensor, map_add,
      hF, hQ, sign_map_of_degree_between G G' F hdF]
  exact LinearMap.congr_fun he c

lemma biAugmentation_tensorMap {G' H' : Type*}
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    (hF : ∀ c, augmentation G' (F c) = augmentation G c)
    (hQ : ∀ c, augmentation H' (Q c) = augmentation H c)
    (c : BiChain G H) : biAugmentation G' H' (tensorMap G H F Q c) = biAugmentation G H c := by
  have he : biAugmentation G' H' ∘ₗ tensorMap G H F Q = biAugmentation G H := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, tensorMap_tensor, biAugmentation_tensor, hF, hQ]
  exact LinearMap.congr_fun he c

lemma boundary_mappedDiagonalHomotopy (f : G → H) (c : Chain G) :
    boundary (H × H) (mappedDiagonalHomotopy G H f c) +
      mappedDiagonalHomotopy G H f (boundary G c) =
        mapChain G (fun a => (f a, f a)) c -
        productComparison H H (tensorMap G G (mapChain G f) (mapChain G f) (diagTensor G c)) := by
  apply boundary_localHomotopy
  · exact boundary_mapChain G _
  · intro c
    simp only [LinearMap.comp_apply, boundary_productComparison]
    rw [boundary_tensorMap G G _ _ (boundary_mapChain G f) (boundary_mapChain G f)
      (fun _ _ hc => mapChain_mem_degree G f hc), biBoundary_diagTensor]
  · intro c
    simp only [LinearMap.comp_apply, augmentation_mapChain, augmentation_productComparison]
    rw [biAugmentation_tensorMap G G _ _ (augmentation_mapChain G f)
      (augmentation_mapChain G f), biAugmentation_diagTensor]

lemma mappedDiagonalHomotopy_single_vertices (f : G → H) (s : Simplex G) :
    mappedDiagonalHomotopy G H f (Finsupp.single s 1) ∈
      vertexModule (H × H) ((f '' vertices G s) ×ˢ (f '' vertices G s)) := by
  apply localHomotopy_single_vertices G (H × H) (fun a => (f a, f a)) _ _
    (fun V => (f '' V) ×ˢ (f '' V))
  · intro V W h
    exact Set.prod_mono (Set.image_mono h) (Set.image_mono h)
  · intro V x hx
    exact ⟨Set.mem_image_of_mem f hx,Set.mem_image_of_mem f hx⟩
  · intro s
    exact mapChain_mem_vertices G (fun a => (f a, f a))
      (V := vertices G s) (W := (f '' vertices G s) ×ˢ (f '' vertices G s))
      (fun _ hx => ⟨Set.mem_image_of_mem f hx, Set.mem_image_of_mem f hx⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)
  · intro s
    apply productComparison_mem_vertices H H
    apply tensorMap_mem_vertices G G _ _ _ _ (diagTensor_single_vertices G s)
    · intro c hc
      exact mapChain_mem_vertices G f (fun _ hx => Set.mem_image_of_mem f hx) hc
    · intro c hc
      exact mapChain_mem_vertices G f (fun _ hx => Set.mem_image_of_mem f hx) hc

lemma mappedDiagonalHomotopy_mem_degree (f : G → H) {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) :
    mappedDiagonalHomotopy G H f c ∈ degreeModule (H × H) (n+1) := by
  apply localHomotopy_mem_degree G (H × H) _ _ _ _ _ hc
  · intro n c hc
    exact mapChain_mem_degree G _ hc
  · intro n c hc
    apply productComparison_mem_degree H H
    exact tensorMap_mem_degree G G _ _ (fun _ _ hc => mapChain_mem_degree G f hc)
      (fun _ _ hc => mapChain_mem_degree G f hc) (diagTensor_mem_degree G hc)

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsHasPropagation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*) [Group G] [Group H]

lemma sign_mem_controlledModule {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : sign G c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (sign G) _ c
  intro s hs
  rw [sign_single]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs) 1

lemma tensor_mem_controlled {A : Set G} {B : Set H} {x : Chain G} {y : Chain H}
    (hx : x ∈ controlledModule G A) (hy : y ∈ controlledModule H B) :
    tensor G H x y ∈ biControlledModule G H A B := by
  apply FreeTensor.pure_mem
  intro s hs t ht
  apply FreeTensor.single_mem_supported
  exact ⟨hx hs,hy ht⟩

lemma biVertexModule_le_controlledModule {V : Set G} {W : Set H} {A : Set G} {B : Set H}
    (ha : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ A)
    (hb : ∀ x ∈ W, ∀ y ∈ W, x⁻¹ * y ∈ B) :
    biVertexModule G H V W ≤ biControlledModule G H A B := by
  intro c hc s hs
  exact ⟨fun x hx y hy => ha x ((hc hs).1 hx) y ((hc hs).1 hy),
    fun x hx y hy => hb x ((hc hs).2 hx) y ((hc hs).2 hy)⟩

lemma vertexProduct_le_controlledModule {V : Set G} {W : Set H} {A : Set G} {B : Set H}
    (ha : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ A)
    (hb : ∀ x ∈ W, ∀ y ∈ W, x⁻¹ * y ∈ B) :
    vertexModule (G × H) (V ×ˢ W) ≤ controlledModule (G × H) (A ×ˢ B) := by
  apply vertexModule_le_controlledModule
  intro x hx y hy
  exact ⟨ha x.1 hx.1 y.1 hy.1, hb x.2 hx.2 y.2 hy.2⟩

lemma diagTensor_mem_controlled {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : diagTensor G c ∈ biControlledModule G G A A := by
  apply BasedComplex.map_mem_of_support (diagTensor G) _ c
  intro s hs
  exact biVertexModule_le_controlledModule G G (hc hs) (hc hs)
    (diagTensor_single_vertices G s)

lemma productComparison_mem_controlled {A : Set G} {B : Set H} {c : BiChain G H}
    (hc : c ∈ biControlledModule G H A B) :
    productComparison G H c ∈ controlledModule (G × H) (A ×ˢ B) := by
  apply BasedComplex.map_mem_of_support (productComparison G H) _ c
  intro s hs
  exact vertexProduct_le_controlledModule G H (hc hs).1 (hc hs).2
    (productComparison_single_vertices G H s)

lemma projectLeft_mem_controlled {A : Set G} {B : Set H} {c : BiChain G H}
    (hc : c ∈ biControlledModule G H A B) : projectLeft G H c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (projectLeft G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectLeft_tensor]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs).1 1

lemma projectRight_mem_controlled {A : Set G} {B : Set H} {c : BiChain G H}
    (hc : c ∈ biControlledModule G H A B) : projectRight G H c ∈ controlledModule H B := by
  apply BasedComplex.map_mem_of_support (projectRight G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectRight_tensor]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs).2 1

lemma tensorMap_mem_controlled {G' H' : Type*} [Group G'] [Group H']
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    {A : Set G} {B : Set H} {A' : Set G'} {B' : Set H'}
    (hF : ∀ c, c ∈ controlledModule G A → F c ∈ controlledModule G' A')
    (hQ : ∀ c, c ∈ controlledModule H B → Q c ∈ controlledModule H' B')
    {c : BiChain G H} (hc : c ∈ biControlledModule G H A B) :
    tensorMap G H F Q c ∈ biControlledModule G' H' A' B' := by
  apply BasedComplex.map_mem_of_support (tensorMap G H F Q) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, tensorMap_tensor]
  apply tensor_mem_controlled
  · exact hF _ (FreeTensor.single_mem_supported _ (hc hs).1 1)
  · exact hQ _ (FreeTensor.single_mem_supported _ (hc hs).2 1)

lemma projectionHomotopyLeft_mem_controlled {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : projectionHomotopyLeft G c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (projectionHomotopyLeft G) _ c
  intro s hs
  exact vertexModule_le_controlledModule G (hc hs)
    (projectionHomotopyLeft_single_vertices G s)

lemma projectionHomotopyRight_mem_controlled {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : projectionHomotopyRight G c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (projectionHomotopyRight G) _ c
  intro s hs
  exact vertexModule_le_controlledModule G (hc hs)
    (projectionHomotopyRight_single_vertices G s)

lemma endpointHomotopyLeft_mem_controlled (b : H) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) :
    endpointHomotopyLeft G H b c ∈ controlledModule (G × H) (A ×ˢ {1}) := by
  apply BasedComplex.map_mem_of_support (endpointHomotopyLeft G H b) _ c
  intro s hs
  apply vertexProduct_le_controlledModule G H (hc hs) _
    (endpointHomotopyLeft_single_vertices G H b s)
  rintro x rfl y rfl
  simp only [Set.mem_singleton_iff, inv_mul_cancel]

lemma endpointHomotopyRight_mem_controlled (a : G) {A : Set H} {c : Chain H}
    (hc : c ∈ controlledModule H A) :
    endpointHomotopyRight G H a c ∈ controlledModule (G × H) ({1} ×ˢ A) := by
  apply BasedComplex.map_mem_of_support (endpointHomotopyRight G H a) _ c
  intro s hs
  apply vertexProduct_le_controlledModule G H _ (hc hs)
    (endpointHomotopyRight_single_vertices G H a s)
  rintro x rfl y rfl
  simp only [Set.mem_singleton_iff, inv_mul_cancel]

lemma mappedDiagonalHomotopy_mem_controlled (f : G →* H) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : mappedDiagonalHomotopy G H f c ∈
      controlledModule (H × H) ((f '' A) ×ˢ (f '' A)) := by
  apply BasedComplex.map_mem_of_support (mappedDiagonalHomotopy G H f) _ c
  intro s hs
  exact vertexProduct_le_controlledModule H H (hom_image_propagation G H f (hc hs))
    (hom_image_propagation G H f (hc hs))
    (mappedDiagonalHomotopy_single_vertices G H f s)

end

section

variable (G : Type*) [Group G] (a : G)

theorem tensorMap_extreme_degrees_controlled {n : ℕ} (hn : 0 < n)
    (T : Chain G →ₗ[ℤ] Chain G)
    (A : Set G)
    (hT : ∀ m, m < n → ∀ c, c ∈ degreeModule G m →
      c ∈ controlledModule G A → T c = K G a c)
    {c : BiChain G G} (hc : c ∈ biDegreeModule G G n)
    (hca : c ∈ biControlledModule G G A A) :
    tensorMap G G T T c = includeRight G G a (T (projectRight G G c)) +
      includeLeft G G a (T (projectLeft G G c)) := by
  have he := BasedComplex.linear_eq_on_support (tensorMap G G T T)
    (includeRight G G a ∘ₗ T ∘ₗ projectRight G G +
      includeLeft G G a ∘ₗ T ∘ₗ projectLeft G G) c (by
      intro s hs
      have hdeg : degree G s.1 + degree G s.2 = n := hc hs
      have hx : Finsupp.single s.1 1 ∈ degreeModule G (degree G s.1) := by
        apply FreeTensor.single_mem_supported
        rfl
      have hy : Finsupp.single s.2 1 ∈ degreeModule G (degree G s.2) := by
        apply FreeTensor.single_mem_supported
        rfl
      have hxa : Finsupp.single s.1 1 ∈ controlledModule G A :=
        FreeTensor.single_mem_supported _ (hca hs).1 1
      have hya : Finsupp.single s.2 1 ∈ controlledModule G A :=
        FreeTensor.single_mem_supported _ (hca hs).2 1
      rw [← FreeTensor.pure_single_one]
      simp only [tensorMap_tensor, LinearMap.add_apply, LinearMap.comp_apply,
        projectRight_tensor, projectLeft_tensor, includeRight_apply, includeLeft_apply]
      by_cases hp : degree G s.1 = 0
      · have hq : degree G s.2 ≠ 0 := by omega
        have hax : augmentation G (Finsupp.single s.1 1) = 1 := by
          change (based G).aug (Finsupp.single s.1 1) = 1
          rw [(based G).aug_single]
          change (if degree G s.1 = 0 then (1 : ℤ) else 0) = 1
          rw [ite_eq_left hp]
        have hay : augmentation G (Finsupp.single s.2 1) = 0 :=
          augmentation_eq_zero_of_degree G hq hy
        rw [hT _ (by omega) _ hx hxa, K_apply, hax, hay, one_smul, zero_smul,
          map_zero, map_zero, LinearMap.zero_apply, add_zero]
        simp only [one_smul]
      · by_cases hq : degree G s.2 = 0
        · have hax : augmentation G (Finsupp.single s.1 1) = 0 :=
            augmentation_eq_zero_of_degree G hp hx
          have hay : augmentation G (Finsupp.single s.2 1) = 1 := by
            change (based G).aug (Finsupp.single s.2 1) = 1
            rw [(based G).aug_single]
            change (if degree G s.2 = 0 then (1 : ℤ) else 0) = 1
            rw [ite_eq_left hq]
          rw [hT _ (by omega) _ hy hya, K_apply, hax, hay, zero_smul, one_smul,
            map_zero, map_zero, zero_add]
          simp only [one_smul]
        · have hax : augmentation G (Finsupp.single s.1 1) = 0 :=
            augmentation_eq_zero_of_degree G hp hx
          have hay : augmentation G (Finsupp.single s.2 1) = 0 :=
            augmentation_eq_zero_of_degree G hq hy
          rw [hT _ (by omega) _ hx hxa, hT _ (by omega) _ hy hya, K_apply, K_apply, hax, hay]
          simp only [zero_smul, map_zero, LinearMap.zero_apply, add_zero])
  exact he

omit [Group G] in
lemma perturbedMap_apply (F J : Chain G →ₗ[ℤ] Chain G) (c : Chain G) :
    perturbedMap G F J c = F c - boundary G (J c) - J (boundary G c) := rfl

omit [Group G] in
lemma boundary_perturbedMap (F J : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ c, boundary G (F c) = F (boundary G c)) (c : Chain G) :
    boundary G (perturbedMap G F J c) = perturbedMap G F J (boundary G c) := by
  simp only [perturbedMap_apply, map_sub, boundary_boundary, map_zero, sub_zero, hF]

omit [Group G] in
lemma perturbation_homotopy (F J : Chain G →ₗ[ℤ] Chain G) (c : Chain G) :
    boundary G (J c) + J (boundary G c) = F c - perturbedMap G F J c := by
  rw [perturbedMap_apply]
  abel

omit [Group G] in
lemma boundary_eq_zero_of_degree_zero {c : Chain G} (hc : c ∈ degreeModule G 0) :
    boundary G c = 0 := by
  have he := BasedComplex.linear_eq_on_support (boundary G) (0 : Chain G →ₗ[ℤ] Chain G) c (by
    intro s hs
    exact BasedComplex.d_vertex (based G) (hc hs))
  exact he

omit [Group G] in
lemma perturbedMap_mem_degree (F J : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G n)
    (hJ : ∀ n c, c ∈ degreeModule G n → J c ∈ degreeModule G (n+1))
    {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    perturbedMap G F J c ∈ degreeModule G n := by
  rw [perturbedMap_apply]
  apply Submodule.sub_mem
  · exact Submodule.sub_mem _ (hF _ _ hc) (boundary_mem_degreeModule G (hJ _ _ hc))
  · cases n with
    | zero =>
      rw [boundary_eq_zero_of_degree_zero G hc, map_zero]
      exact Submodule.zero_mem _
    | succ n => exact hJ _ _ (boundary_mem_degreeModule G hc)

omit [Group G] in
lemma perturbedMap_eq_on_cycle (F J : Chain G →ₗ[ℤ] Chain G) {c : Chain G}
    (hc : boundary G c = 0) (hj : J c = 0) : perturbedMap G F J c = F c := by
  simp only [perturbedMap_apply, hc, hj, map_zero, sub_zero]

omit [Group G] in
lemma perturbedMap_eq_on_lower (F J : Chain G →ₗ[ℤ] Chain G) {c : Chain G}
    (h : boundary G (J c) + J (boundary G c) = F c - K G a c) :
    perturbedMap G F J c = K G a c := by
  rw [perturbedMap_apply]
  calc F c - boundary G (J c) - J (boundary G c) =
      F c - (boundary G (J c) + J (boundary G c)) := by abel
    _ = K G a c := by rw [h, sub_sub_cancel]

lemma perturbedMap_mem_controlled (F J : Chain G →ₗ[ℤ] Chain G) {A B : Set G}
    (hF : ∀ c, c ∈ controlledModule G A → F c ∈ controlledModule G B)
    (hJ : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G B)
    {c : Chain G} (hc : c ∈ controlledModule G A) :
    perturbedMap G F J c ∈ controlledModule G B := by
  rw [perturbedMap_apply]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ (hF _ hc)
    (boundary_mem_controlledModule G (hJ _ hc))) (hJ _ (boundary_mem_controlledModule G hc))

omit [Group G] in
lemma sign_mem_degree {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    sign G c ∈ degreeModule G n := by
  rw [sign_eq_smul_of_degree G hc]
  exact Submodule.smul_mem _ _ hc

omit [Group G] in
lemma tensorHomotopy_mem_degree (F Q J : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G n)
    (hQ : ∀ n c, c ∈ degreeModule G n → Q c ∈ degreeModule G n)
    (hJ : ∀ n c, c ∈ degreeModule G n → J c ∈ degreeModule G (n+1))
    {n : ℕ} {c : BiChain G G} (hc : c ∈ biDegreeModule G G n) :
    tensorHomotopy G F Q J c ∈ biDegreeModule G G (n+1) := by
  apply BasedComplex.map_mem_of_support (tensorHomotopy G F Q J) _ c
  intro s hs
  have hn : degree G s.1 + degree G s.2 = n := hc hs
  have hx : Finsupp.single s.1 1 ∈ degreeModule G (degree G s.1) := by
    apply FreeTensor.single_mem_supported
    rfl
  have hy : Finsupp.single s.2 1 ∈ degreeModule G (degree G s.2) := by
    apply FreeTensor.single_mem_supported
    rfl
  rw [← FreeTensor.pure_single_one, tensorHomotopy_tensor]
  apply Submodule.add_mem
  · have he : n+1 = (degree G s.1+1) + degree G s.2 := by omega
    rw [he]
    exact tensor_mem_degree G G (hJ _ _ hx) (hF _ _ hy)
  · have he : n+1 = degree G s.1 + (degree G s.2+1) := by omega
    rw [he]
    exact tensor_mem_degree G G (hQ _ _ (sign_mem_degree G hx)) (hJ _ _ hy)

lemma tensorHomotopy_mem_controlled (F Q J : Chain G →ₗ[ℤ] Chain G) {A B : Set G}
    (hF : ∀ c, c ∈ controlledModule G A → F c ∈ controlledModule G B)
    (hQ : ∀ c, c ∈ controlledModule G A → Q c ∈ controlledModule G B)
    (hJ : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G B)
    {c : BiChain G G} (hc : c ∈ biControlledModule G G A A) :
    tensorHomotopy G F Q J c ∈ biControlledModule G G B B := by
  change tensorMap G G J F c + tensorMap G G (Q ∘ₗ sign G) J c ∈ _
  refine Submodule.add_mem _ ?_ ?_
  · exact tensorMap_mem_controlled G G J F hJ hF hc
  · have hQs (x : Chain G) (hx : x ∈ controlledModule G A) :
        (Q ∘ₗ sign G) x ∈ controlledModule G B := hQ _ (sign_mem_controlledModule G hx)
    exact tensorMap_mem_controlled G G (Q ∘ₗ sign G) J hQs hJ hc

end

variable (G : Type*) [Group G]

theorem boundary_additivityFilling (a : G) (f : G → G)
    (J : Chain G →ₗ[ℤ] Chain G) {n : ℕ} (hn : 0 < n) (A : Set G)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    (hJzero : ∀ c, c ∈ degreeModule G n → J c = 0)
    (hJlower : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
      boundary G (J c) + J (boundary G c) = mapChain G f c - K G a c)
    {z : Chain G} (hzd : z ∈ degreeModule G n) (hza : z ∈ controlledModule G A)
    (hz : boundary G z = 0) :
    boundary (G × G) (additivityFilling G a f J z) =
      mapChain G (fun b => (f b,f b)) z -
      mapChain G (fun b => (a,b)) (mapChain G f z) -
      mapChain G (fun b => (b,a)) (mapChain G f z) := by
  let F := mapChain G f
  let Q := perturbedMap G F J
  let d := diagTensor G z
  let r := projectRight G G d
  let l := projectLeft G G d
  have hFdeg (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      F c ∈ degreeModule G m := mapChain_mem_degree G f hc
  have hQdeg (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      Q c ∈ degreeModule G m := perturbedMap_mem_degree G F J hFdeg hJdeg hc
  have hFb (c : Chain G) : boundary G (F c) = F (boundary G c) := boundary_mapChain G f c
  have hd : biBoundary G G d = 0 := by
    dsimp only [d]
    rw [biBoundary_diagTensor, hz, map_zero]
  have hr : boundary G r = 0 := by
    dsimp only [r]
    rw [boundary_projectRight, hd, map_zero]
  have hl : boundary G l = 0 := by
    dsimp only [l]
    rw [boundary_projectLeft, hd, map_zero]
  have hrdeg : r ∈ degreeModule G n := projectRight_mem_degree G G (diagTensor_mem_degree G hzd)
  have hldeg : l ∈ degreeModule G n := projectLeft_mem_degree G G (diagTensor_mem_degree G hzd)
  have hQr : Q r = F r := perturbedMap_eq_on_cycle G F J hr (hJzero _ hrdeg)
  have hQl : Q l = F l := perturbedMap_eq_on_cycle G F J hl (hJzero _ hldeg)
  have hextreme : tensorMap G G Q Q d = includeRight G G a (F r) + includeLeft G G a (F l) := by
    rw [tensorMap_extreme_degrees_controlled G a hn Q A
      (fun m hm c hc ha => perturbedMap_eq_on_lower G a F J (hJlower m hm c hc ha))
      (diagTensor_mem_degree G hzd) (diagTensor_mem_controlled G hza), hQr, hQl]
  have h0 : boundary (G × G) (mappedDiagonalHomotopy G G f z) =
      mapChain G (fun b => (f b,f b)) z - productComparison G G (tensorMap G G F F d) := by
    have h := boundary_mappedDiagonalHomotopy G G f z
    simpa only [hz, map_zero, add_zero] using h
  have h1 : biBoundary G G (tensorHomotopy G F Q J d) =
      tensorMap G G F F d - (includeRight G G a (F r) + includeLeft G G a (F l)) := by
    have h := boundary_tensorHomotopy G F Q J (boundary_mapChain G f)
      (boundary_perturbedMap G F J (boundary_mapChain G f))
      (perturbation_homotopy G F J) hQdeg hJdeg d
    simpa only [hd, map_zero, add_zero, hextreme] using h
  have hFr : boundary G (F r) = 0 := by rw [boundary_mapChain, hr, map_zero]
  have hFl : boundary G (F l) = 0 := by rw [boundary_mapChain, hl, map_zero]
  have h2 : boundary (G × G) (endpointHomotopyRight G G a (F r)) =
      productComparison G G (includeRight G G a (F r)) - mapChain G (fun b => (a,b)) (F r) := by
    simpa only [hFr, map_zero, add_zero] using boundary_endpointHomotopyRight G G a (F r)
  have h3 : boundary (G × G) (endpointHomotopyLeft G G a (F l)) =
      productComparison G G (includeLeft G G a (F l)) - mapChain G (fun b => (b,a)) (F l) := by
    simpa only [hFl, map_zero, add_zero] using boundary_endpointHomotopyLeft G G a (F l)
  have h4 : boundary G (projectionHomotopyRight G z) = r - z := by
    simpa only [hz, map_zero, add_zero] using boundary_projectionHomotopyRight G z
  have h5 : boundary G (projectionHomotopyLeft G z) = l - z := by
    simpa only [hz, map_zero, add_zero] using boundary_projectionHomotopyLeft G z
  change boundary (G × G) (mappedDiagonalHomotopy G G f z +
    productComparison G G (tensorHomotopy G F Q J d) + endpointHomotopyRight G G a (F r) +
    endpointHomotopyLeft G G a (F l) +
    mapChain G (fun b => (a,b)) (F (projectionHomotopyRight G z)) +
    mapChain G (fun b => (b,a)) (F (projectionHomotopyLeft G z))) = _
  simp only [map_add, boundary_productComparison, boundary_mapChain, hFb, h0, h1, h2, h3, h4, h5,
    map_sub]
  dsimp only [F]
  abel

omit [Group G] in
lemma additivityFilling_mem_degree (a : G) (f : G → G) (J : Chain G →ₗ[ℤ] Chain G)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    {n : ℕ} {z : Chain G} (hzd : z ∈ degreeModule G n) :
    additivityFilling G a f J z ∈ degreeModule (G × G) (n+1) := by
  have hFdeg (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      mapChain G f c ∈ degreeModule G m := mapChain_mem_degree G f hc
  have hQdeg (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      perturbedMap G (mapChain G f) J c ∈ degreeModule G m :=
    perturbedMap_mem_degree G _ _ hFdeg hJdeg hc
  simp only [additivityFilling, LinearMap.add_apply, LinearMap.comp_apply]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact mappedDiagonalHomotopy_mem_degree G G f hzd
          · exact productComparison_mem_degree G G
              (tensorHomotopy_mem_degree G _ _ _ hFdeg hQdeg hJdeg (diagTensor_mem_degree G hzd))
        · exact endpointHomotopyRight_mem_degree G G a
            (hFdeg _ _ (projectRight_mem_degree G G (diagTensor_mem_degree G hzd)))
      · exact endpointHomotopyLeft_mem_degree G G a
          (hFdeg _ _ (projectLeft_mem_degree G G (diagTensor_mem_degree G hzd)))
    · exact mapChain_mem_degree G _ (hFdeg _ _ (projectionHomotopyRight_mem_degree G hzd))
  · exact mapChain_mem_degree G _ (hFdeg _ _ (projectionHomotopyLeft_mem_degree G hzd))

lemma fixedLeftMap_mem_controlled (a : G) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) :
    mapChain G (fun b => (a,b)) c ∈ controlledModule (G × G) ({1} ×ˢ A) := by
  apply BasedComplex.map_mem_of_support (mapChain G (fun b => (a,b))) _ c
  intro s hs
  refine vertexProduct_le_controlledModule G G (V := {a}) (W := vertices G s) ?_ (hc hs) ?_
  · rintro x rfl y rfl
    simp only [Set.mem_singleton_iff, inv_mul_cancel]
  · exact mapChain_mem_vertices G (fun b => (a,b))
      (V := vertices G s) (W := {a} ×ˢ vertices G s) (fun _ hx => ⟨rfl,hx⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma fixedRightMap_mem_controlled (a : G) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) :
    mapChain G (fun b => (b,a)) c ∈ controlledModule (G × G) (A ×ˢ {1}) := by
  apply BasedComplex.map_mem_of_support (mapChain G (fun b => (b,a))) _ c
  intro s hs
  refine vertexProduct_le_controlledModule G G (V := vertices G s) (W := {a}) (hc hs) ?_ ?_
  · rintro x rfl y rfl
    simp only [Set.mem_singleton_iff, inv_mul_cancel]
  · exact mapChain_mem_vertices G (fun b => (b,a))
      (V := vertices G s) (W := vertices G s ×ˢ {a}) (fun _ hx => ⟨hx,rfl⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma additivityFilling_mem_controlled (a : G) (f : G →* G) (J : Chain G →ₗ[ℤ] Chain G)
    {A B : Set G} (hB : 1 ∈ B) (hf : f '' A ⊆ B)
    (hJ : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G B)
    {z : Chain G} (hz : z ∈ controlledModule G A) :
    additivityFilling G a f J z ∈ controlledModule (G × G) (B ×ˢ B) := by
  have hF (c : Chain G) (hc : c ∈ controlledModule G A) :
      mapChain G f c ∈ controlledModule G B :=
    controlledModule_mono G hf (mapChain_mem_controlled G G f hc)
  have hQ (c : Chain G) (hc : c ∈ controlledModule G A) :
      perturbedMap G (mapChain G f) J c ∈ controlledModule G B :=
    perturbedMap_mem_controlled G _ _ hF hJ hc
  have hsingleton : ({1} : Set G) ⊆ B := Set.singleton_subset_iff.mpr hB
  have hr := hF _ (projectRight_mem_controlled G G (diagTensor_mem_controlled G hz))
  have hl := hF _ (projectLeft_mem_controlled G G (diagTensor_mem_controlled G hz))
  simp only [additivityFilling, LinearMap.add_apply, LinearMap.comp_apply]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact controlledModule_mono (G × G) (Set.prod_mono hf hf)
              (mappedDiagonalHomotopy_mem_controlled G G f hz)
          · exact productComparison_mem_controlled G G
              (tensorHomotopy_mem_controlled G _ _ _ hF hQ hJ (diagTensor_mem_controlled G hz))
        · exact controlledModule_mono (G × G) (Set.prod_mono hsingleton (Set.Subset.refl _))
            (endpointHomotopyRight_mem_controlled G G a hr)
      · exact controlledModule_mono (G × G) (Set.prod_mono (Set.Subset.refl _) hsingleton)
          (endpointHomotopyLeft_mem_controlled G G a hl)
    · exact controlledModule_mono (G × G) (Set.prod_mono hsingleton (Set.Subset.refl _))
        (fixedLeftMap_mem_controlled G a (hF _ (projectionHomotopyRight_mem_controlled G hz)))
  · exact controlledModule_mono (G × G) (Set.prod_mono (Set.Subset.refl _) hsingleton)
      (fixedRightMap_mem_controlled G a (hF _ (projectionHomotopyLeft_mem_controlled G hz)))

lemma IsBound.prod {H : Type*} [Group H] {A : Set G} {B : Set H}
    (ha : IsBound G A) (hb : IsBound H B) : IsBound (G × H) (A ×ˢ B) where
  finite := ha.finite.prod hb.finite
  one_mem := ⟨ha.one_mem,hb.one_mem⟩
  inv_mem a h := ⟨ha.inv_mem a.1 h.1,hb.inv_mem a.2 h.2⟩

theorem controlled_product_additivity (f : G →* G) (J : Chain G →ₗ[ℤ] Chain G)
    {n : ℕ} (hn : 0 < n) {A C : Set G} (hA : IsBound G A) (hC : IsBound G C)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    (hJzero : ∀ c, c ∈ degreeModule G n → J c = 0)
    (hJcontrol : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G C)
    (hJlower : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
      boundary G (J c) + J (boundary G c) = mapChain G f c - K G 1 c) :
    ∃ B : Set (G × G), IsBound (G × G) B ∧
      ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
        ∃ w, w ∈ degreeModule (G × G) (n+1) ∧ w ∈ controlledModule (G × G) B ∧
          boundary (G × G) w = mapChain G (fun b => (f b,f b)) z -
            mapChain G (fun b => (1,b)) (mapChain G f z) -
            mapChain G (fun b => (b,1)) (mapChain G f z) := by
  let B := f '' A ∪ C
  have hB : IsBound G B := (hA.image G f).union G hC
  refine ⟨B ×ˢ B,hB.prod G hB,?_⟩
  intro z hzd hza hz
  refine ⟨additivityFilling G 1 f J z,additivityFilling_mem_degree G 1 f J hJdeg hzd,?_,?_⟩
  · exact additivityFilling_mem_controlled G 1 f J hB.one_mem Set.subset_union_left
      (fun c hc => controlledModule_mono G Set.subset_union_right (hJcontrol c hc)) hza
  · exact boundary_additivityFilling G 1 f J hn A hJdeg hJzero hJlower hzd hza hz

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsMapChainComp
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
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

theorem controlled_commuting_additivity_oai (f : G →* G) (J : Chain G →ₗ[ℤ] Chain G)
    {n : ℕ} (hn : 0 < n) {A C : Set G} (hA : IsBound G A) (hC : IsBound G C)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    (hJzero : ∀ c, c ∈ degreeModule G n → J c = 0)
    (hJcontrol : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G C)
    (hJlower : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
      boundary G (J c) + J (boundary G c) = mapChain G f c - K G 1 c)
    (h₁ h₂ : G →* G) (comm : ∀ x y, Commute (h₁ x) (h₂ y)) :
    ∃ B : Set G, IsBound G B ∧
      ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
        FillsAt G B n (mapChain G (fun x => h₁ (f x) * h₂ (f x)) z -
          mapChain G (h₁ ∘ f) z - mapChain G (h₂ ∘ f) z) := by
  obtain ⟨B,hB,hfill⟩ := controlled_product_additivity G f J hn hA hC
    hJdeg hJzero hJcontrol hJlower
  let μ := h₁.noncommCoprod h₂ comm
  refine ⟨μ '' B,hB.image (G × G) μ,?_⟩
  intro z hzd hza hz
  obtain ⟨w,hwd,hwb,hw⟩ := hfill z hzd hza hz
  refine ⟨mapChain (G × G) μ w,mapChain_mem_degree (G × G) μ hwd,
    mapChain_mem_controlled (G × G) G μ hwb,?_⟩
  rw [boundary_mapChain,hw,map_sub,map_sub]
  simp only [mapChain_comp,Function.comp_def,μ,MonoidHom.noncommCoprod_apply,map_one,
    one_mul,mul_one]
  abel

open scoped Pointwise

end

end ListChains

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ListChains.controlled_commuting_additivity_oai.{u_1} := @OAI.ListChains.controlled_commuting_additivity_oai.{u_1}

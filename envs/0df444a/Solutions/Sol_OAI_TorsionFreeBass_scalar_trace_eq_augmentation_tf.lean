-- Prove2me | solution 1 for OAI.TorsionFreeBass.scalar_trace_eq_augmentation_tf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:08:58.129682+00:00
-- url     : https://prove2.me/submissions/8d64437f-586b-406e-bb72-0bdc321d5206

import Mathlib
import Definitions.Def_BassTorsionFree
import Definitions.Def_OAIQ113B002
import Theorems.Thm_OAI_BassTrace_Sparse_GraphGeometry_global_zero_ball_mass_bound_tf
import Theorems.Thm_OAI_BassTrace_Sparse_vanishing_of_zero_strata_tf

section
-- module Solutions.OAIQ113_TFB.Compat
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceMeasurable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ExteriorChains
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Chains

open scoped BigOperators

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

lemma contraction_square (α : M →ₗ[R] R) (x : ExteriorAlgebra R M) :
    contraction α (contraction α x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft α x

variable (Y : Type*)

lemma boundary_square (x : Algebra Y) : boundary Y (boundary Y x) = 0 :=
  contraction_square _ x

end Chains

/-! Alternating functions on vertex labels extend to genuine linear maps on exterior chains. -/

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y : Type*}

lemma d_square (n : ℕ) (x : Degree Y (n+2)) : d n (d (n+1) x) = 0 := by
  ext
  exact Chains.boundary_square _ _

end ChainHomotopy

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BarycentricChains
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.Oriented.instCoeFunAltFunctionForallForallFin_2 _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y H : Type*} [LinearOrder Y]

open Classical in

lemma Complex.projection_wedge (K : Complex Y) (n : ℕ) (v : Fin n → Y) :
    (K.projection n (wedge n v) : Degree Y n) =
      if Finset.univ.image v ∈ K.faces then wedge n v else 0 := by
  classical
  rw [projection, AltFunction.lift_wedge]
  dsimp only [Complex.projectionValues]
  split_ifs <;> rfl

lemma Complex.projection_self (K : Complex Y) (n : ℕ) {x : Degree Y n}
    (hx : x ∈ K.chains n) : (K.projection n x : Degree Y n) = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [K.projection_wedge, ite_eq_left hv]
  | zero => simp only [map_zero, Submodule.coe_zero]
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, Submodule.coe_smul, hx]

variable [Group H] [MulAction H Y]

lemma Complex.image_mem_iff (K : Complex Y) (hK : K.IsInvariant (H := H))
    (h : H) (s : Finset Y) : s.image (fun y => h • y) ∈ K.faces ↔ s ∈ K.faces := by
  constructor
  · intro hs
    have he := hK h⁻¹ _ hs
    simpa only [Finset.image_image, Function.comp_def, inv_smul_smul, Finset.image_id'] using he
  · exact hK h s

lemma Complex.projection_relabel (K : Complex Y) (hK : K.IsInvariant (H := H))
    (n : ℕ) (h : H) (x : Degree Y n) :
    (K.projection n (relabel n (fun y => h • y) x) : Degree Y n) =
      relabel n (fun y => h • y) (K.projection n x : Degree Y n) := by
  classical
  have he : ((K.chains n).subtype.comp (K.projection n)).comp
      (relabel n (fun y => h • y)) =
      (relabel n (fun y => h • y)).comp ((K.chains n).subtype.comp (K.projection n)) := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, relabel_wedge,
      K.projection_wedge]
    have he : Finset.univ.image ((fun y => h • y) ∘ v) ∈ K.faces ↔
        Finset.univ.image v ∈ K.faces := by
      rw [← Finset.image_image]
      exact K.image_mem_iff hK h _
    by_cases hv : Finset.univ.image v ∈ K.faces
    · rw [ite_eq_left (he.mpr hv), ite_eq_left hv, relabel_wedge]
    · rw [ite_eq_right (mt he.mp hv), ite_eq_right hv, map_zero]
  exact LinearMap.congr_fun he x

end ChainHomotopy

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_LocalCuts
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma cutCell_reindex (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (e : I ≃ J) (s : J → Bool) :
    cutCell P (a ∘ e) (b ∘ e) (s ∘ e) = cutCell P a b s := by
  ext x
  have h (i : I) :
      signedForm (a ∘ e) (s ∘ e) i x ≤ signedBound (b ∘ e) (s ∘ e) i ↔
      signedForm a s (e i) x ≤ signedBound b s (e i) := Iff.rfl
  change (x ∈ P ∧ ∀ i, signedForm (a ∘ e) (s ∘ e) i x ≤
    signedBound (b ∘ e) (s ∘ e) i) ↔
    (x ∈ P ∧ ∀ j, signedForm a s j x ≤ signedBound b s j)
  simp only [h]
  constructor
  · rintro ⟨hx, hle⟩
    exact ⟨hx, fun j => by simpa using hle (e.symm j)⟩
  · rintro ⟨hx, hle⟩
    exact ⟨hx, fun i => hle (e i)⟩

lemma cutParents_reindex (A : Finset (Set V)) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (e : I ≃ J) : cutParents A (a ∘ e) (b ∘ e) = cutParents A a b := by
  classical
  apply Finset.ext
  intro Q
  rw [mem_cutParents, mem_cutParents]
  constructor
  · rintro ⟨P, hP, s, rfl, hn⟩
    let t : J → Bool := s ∘ e.symm
    have he : t ∘ e = s := by funext i; simp [t]
    rw [← he, cutCell_reindex] at hn ⊢
    exact ⟨P, hP, t, rfl, hn⟩
  · rintro ⟨P, hP, s, rfl, hn⟩
    refine ⟨P, hP, s ∘ e, ?_, hn⟩
    exact (cutCell_reindex P a b e s).symm

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GeometricSubcomplexes
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Local finiteness passes to a simplexwise finite subdivision. -/

namespace Sparse.Cuts

/-! Geometric subcomplexes used by the compatible-cut lemma. A marked subset
is a union of closed simplices, not necessarily the full complex induced by
its old vertices. Keeping this distinction is essential for unions of levels. -/

section

open Set Finset

section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma cutParents_singleton_finiteHull (K : Geometry.SimplicialComplex ℝ V)
    (s : Finset V) (hs : s ∈ K.faces) {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ∀ P ∈ cutParents {convexHull ℝ (s : Set V)} a b,
      ∃ t : Finset V, P = convexHull ℝ (t : Set V) := by
  classical
  let p : CutPatch K := ⟨{s},by simpa using hs⟩
  let L := finitePatch K p.val p.property
  have hsub : {convexHull ℝ (s : Set V)} ⊆
      complexParents L (finitePatch_finite K p.val p.property) := by
    intro P hP
    have hP' := Finset.mem_singleton.mp hP
    subst P
    exact (mem_complexParents _ _ _).mpr
      ⟨s,mem_finitePatch K p.val p.property (Finset.mem_singleton_self _),rfl⟩
  intro P hP
  exact cutParents_finiteHull_simplicial L (finitePatch_finite K p.val p.property) a b P
    (cutParents_mono hsub a b hP)

lemma canonicalCuts_linear_map (K : Geometry.SimplicialComplex ℝ V)
    (s : Finset V) (hs : s ∈ K.faces) (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (a' : J → W →ₗ[ℝ] ℝ) (b' : J → ℝ)
    (ha : ∀ i, (a' (e i)).comp f = a i) (hb : ∀ i, b' (e i) = b i) :
    chainFaces (faceClosure (cutParents {convexHull ℝ ((s.map ⟨f,hf⟩) : Set W)} a' b'))
      canonicalCenter =
      (fun t : Finset V => t.map ⟨f,hf⟩) ''
        chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)} a b)) canonicalCenter := by
  have hp : cutParents {convexHull ℝ ((s.map ⟨f,hf⟩) : Set W)} a' b' =
      (cutParents {convexHull ℝ (s : Set V)} a b).image (fun P => f '' P) := by
    rw [← cutParents_reindex _ a' b' e]
    have hcoe : convexHull ℝ ((s.map ⟨f,hf⟩) : Set W) = f '' convexHull ℝ (s : Set V) := by
      rw [Finset.coe_map]
      exact (f.toAffineMap.image_convexHull _).symm
    rw [hcoe,← Finset.image_singleton,cutParents_linear_image]
    congr 1
    · congr 1
      · exact funext ha
      · exact funext hb
  rw [hp]
  have hfinite := cutParents_singleton_finiteHull K s hs a b
  have hfaces := faceClosure_affine_map_injective f.toAffineMap hf _ hfinite
  change faceClosure ((cutParents {convexHull ℝ (s : Set V)} a b).image
    (fun P => f '' P)) = (faceClosure (cutParents {convexHull ℝ (s : Set V)} a b)).image
    (fun P => f '' P) at hfaces
  rw [hfaces]
  exact canonical_chainFaces_map_injective _ f.toAffineMap hf
    (faceClosure_finiteHull _ hfinite)

namespace LocalCutData

variable {K : Geometry.SimplicialComplex ℝ V} {K' : Geometry.SimplicialComplex ℝ W}
  {I J : Type*} (d : LocalCutData K I) (d' : LocalCutData K' J)

lemma globalComplex_map (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (hk : ∀ s ∈ K.faces, s.map ⟨f,hf⟩ ∈ K'.faces)
    (e : ∀ s, s ∈ K.faces → d.relevant s ≃ d'.relevant (s.map ⟨f,hf⟩))
    (ha : ∀ s hs i, (d'.form (e s hs i)).comp f = d.form i)
    (hb : ∀ s hs i, d'.level (e s hs i) = d.level i)
    {u : Finset V} (hu : u ∈ d.globalComplex.faces) :
    u.map ⟨f,hf⟩ ∈ d'.globalComplex.faces := by
  obtain ⟨s,hs,hus⟩ := d.globalComplex_carrier hu
  have hlocal : u ∈ (restrictComplex d.globalComplex (convexHull ℝ (s : Set V))).faces :=
    ⟨hu,Subset.trans (subset_convexHull ℝ _) hus⟩
  rw [d.globalComplex_restrict_faces s hs] at hlocal
  have hlocal' := Set.mem_image_of_mem (fun t : Finset V => t.map ⟨f,hf⟩) hlocal
  rw [← canonicalCuts_linear_map K s hs f hf (e s hs)
    (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i)
    (fun j : d'.relevant (s.map ⟨f,hf⟩) => d'.form j)
    (fun j : d'.relevant (s.map ⟨f,hf⟩) => d'.level j) (ha s hs) (hb s hs),
    ← d'.globalComplex_restrict_faces _ (hk s hs)] at hlocal'
  exact hlocal'.1

end LocalCutData

end

open Set Finset

end

open Set Finset

open scoped Classical

end Sparse.Cuts

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Subdivisions
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

open Set Finset

section

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [CompactSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

namespace SubdivisionFamily

lemma finite_faces_on (T : SubdivisionFamily X K) (s : Finset V) (hs : s ∈ K.faces) :
    (⋃ x, (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces).Finite := by
  let f := fun x => (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces
  have hf : (Set.range f).Finite := (T.localConstancy s hs).range_finite
  have hh : (⋃ F ∈ Set.range f, F).Finite := hf.biUnion (by
    rintro F ⟨x,rfl⟩
    exact (T.val x).finite s hs)
  apply hh.subset
  intro u hu
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hu
  exact Set.mem_iUnion₂.mpr ⟨f x,⟨x,rfl⟩,hx⟩

lemma countable_faces (T : SubdivisionFamily X K) (hK : K.faces.Countable) :
    (⋃ x, (T.val x).complex.faces).Countable := by
  have hh : (⋃ s ∈ K.faces, ⋃ x,
      (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces).Countable :=
    hK.biUnion (fun s hs => (T.finite_faces_on s hs).countable)
  apply hh.mono
  intro u hu
  obtain ⟨x,hxu⟩ := Set.mem_iUnion.mp hu
  obtain ⟨s,hs,hus⟩ := (T.val x).carrier u hxu
  exact Set.mem_iUnion₂.mpr ⟨s,hs,Set.mem_iUnion.mpr
    ⟨x,hxu,(subset_convexHull ℝ _).trans hus⟩⟩

lemma countable_vertices (T : SubdivisionFamily X K) (hK : K.faces.Countable) :
    (⋃ x, (T.val x).complex.vertices).Countable := by
  have hh : (⋃ s ∈ (⋃ x, (T.val x).complex.faces), (s : Set V)).Countable :=
    (T.countable_faces hK).biUnion (fun s _ => s.countable_toSet)
  apply hh.mono
  intro y hy
  obtain ⟨x,hxy⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion₂.mpr ⟨{y},Set.mem_iUnion.mpr ⟨x,hxy⟩,by simp⟩

lemma exists_generic_level (T : SubdivisionFamily X K) (hK : K.faces.Countable)
    {J : Type*} [Countable J] (a : J → V → ℝ) {r R : ℝ} (hr : r < R) :
    ∃ t ∈ Set.Ioo r R, ∀ x s, s ∈ (T.val x).complex.faces →
      ∀ j y, y ∈ s → a j y ≠ t := by
  let bad : Set ℝ := ⋃ j, a j '' (⋃ x, (T.val x).complex.vertices)
  have hb : bad.Countable := Set.countable_iUnion fun j => (T.countable_vertices hK).image (a j)
  obtain ⟨t,hnt,ht⟩ := hb.dense_compl ℝ |>.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hr)
  refine ⟨t,ht,?_⟩
  intro x s hs j y hy he
  apply hnt
  apply Set.mem_iUnion.mpr
  refine ⟨j,y,Set.mem_iUnion.mpr ⟨x,?_⟩,he⟩
  exact (T.val x).complex.down_closed hs (Finset.singleton_subset_iff.mpr hy)
    (Finset.singleton_nonempty _)

end SubdivisionFamily

end

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AffinePotentials
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite affine branch geometry for the exact transport metric and compatible cuts. -/

namespace BassTrace.Sparse

open Set Filter

open scoped Topology

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

section Potential

variable {V : Type*} [Fintype V] [MetricSpace V]

lemma potentialVertices_subset (l : V → ℝ) (hl : l ∈ potentialVertices) : l ∈ potentialSet :=
  (mem_potentialVertices l).mp hl |>.1

lemma centerPotential_mem [Nonempty V] {l : V → ℝ} (hl : LipschitzWith 1 l) :
    centerPotential l ∈ potentialSet := by
  classical
  have hc : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · simp only [centerPotential, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  · intro v w
    have h := hl.dist_le_mul v w
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    unfold centerPotential
    congr 1
    ring

omit [MetricSpace V] in
lemma potentialPairing_apply (k l : V → ℝ) :
    potentialPairing k l = ∑ v, k v * l v := by
  classical
  simp [potentialPairing]

omit [MetricSpace V] in
lemma pairing_centerPotential (k l : V → ℝ) (hk : ∑ v, k v = 0) :
    potentialPairing k (centerPotential l) = potentialPairing k l := by
  classical
  simp only [potentialPairing_apply, centerPotential, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hk, zero_mul, sub_zero]

end Potential

variable {Y : Type*} [MetricSpace Y] (S : Finset Y)

lemma exists_global_potential_extension {l : S → ℝ} (hl : l ∈ potentialSet) :
    ∃ f : Y → ℝ, LipschitzWith 1 f ∧ ∀ v : S, f v = l v := by
  classical
  let p : Y → ℝ := fun y => if h : y ∈ S then l ⟨y,h⟩ else 0
  have hp : LipschitzOnWith 1 p (S : Set Y) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    change v ∈ S at hv
    change w ∈ S at hw
    simpa only [p, dite_eq_left hv, dite_eq_left hw, Real.dist_eq, NNReal.coe_one, one_mul, Subtype.dist_eq]
      using hl.2 ⟨v,hv⟩ ⟨w,hw⟩
  obtain ⟨f, hf, hpf⟩ := hp.extend_real
  refine ⟨f, hf, fun v => ?_⟩
  have h := hpf v.2
  simpa [p, v.2, eq_comm] using h

lemma exists_global_vertex_maximizer (hne : S.Nonempty) (k : S → ℝ)
    (hk : ∑ v, k v = 0) :
    ∃ l ∈ (potentialVertices : Finset (S → ℝ)),
      (∃ f : Y → ℝ, LipschitzWith 1 f ∧ ∀ v : S, f v = l v) ∧
      ∀ f : Y → ℝ, LipschitzWith 1 f →
        (∑ v : S, k v * f v) ≤ ∑ v : S, k v * l v := by
  have : Nonempty S := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨⟨v,hv⟩⟩
  obtain ⟨l, hl, hmax⟩ := exists_potential_vertex_maximizer (potentialPairing k)
  refine ⟨l, hl, exists_global_potential_extension S (potentialVertices_subset l hl), ?_⟩
  intro f hf
  have hsub : LipschitzWith 1 (fun v : S => f v) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hf.dist_le_mul v.val w.val
  have hm := hmax (centerPotential (fun v : S => f v)) (centerPotential_mem hsub)
  rw [pairing_centerPotential k _ hk] at hm
  simpa only [potentialPairing_apply] using hm

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ProbabilityGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open Finset

open scoped BassTrace.Sparse

variable {Y : Type*} [MetricSpace Y]

namespace FinProbability

omit [MetricSpace Y] in
lemma expectation_on_finset (p : FinProbability Y) (S : Finset Y)
    (hp : p.coeff.support ⊆ S) (f : Y → ℝ) :
    p.expectation f = ∑ y : S, p.coeff y * f y := by
  rw [expectation,p.coeff.sum_of_support_subset hp _ (by intros; simp)]
  exact Finset.sum_subtype S (fun _ => Iff.rfl) _

omit [MetricSpace Y] in
lemma total_on_finset (p : FinProbability Y) (S : Finset Y)
    (hp : p.coeff.support ⊆ S) : ∑ y : S, p.coeff y = 1 := by
  simpa only [mul_one] using (p.expectation_on_finset S hp (fun _ => 1)).symm.trans
    (p.expectation_const 1)

omit [MetricSpace Y] in
lemma gap_on_finset (c p : FinProbability Y) (S : Finset Y)
    (hc : c.coeff.support ⊆ S) (hp : p.coeff.support ⊆ S) (f : Y → ℝ) :
    c.gap p f = ∑ y : S, (c.coeff y-p.coeff y)*f y := by
  rw [gap,c.expectation_on_finset S hc,p.expectation_on_finset S hp]
  simp only [sub_mul,Finset.sum_sub_distrib]

end FinProbability

omit [MetricSpace Y] in
lemma ballBranch_eq_pairing (S : Finset Y) (c p : FinProbability Y)
    (hp : p.coeff.support ⊆ S) (n : ℕ) (l : S → ℝ) :
    ballBranch S c n l p.coeff =
      (∑ y : S, (c.coeff y-p.coeff y)*l y) / Real.sqrt n := by
  rw [ballBranch_apply]
  simp_rw [div_mul_eq_mul_div,← Finset.sum_div,sub_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,p.total_on_finset S hp,mul_one]
  simp only [centerBranchValue,Finset.sum_sub_distrib]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

theorem exists_ballBranch_maximizer (S : Finset Y) (c p : FinProbability Y)
    (hc : c.coeff.support ⊆ S) (hp : p.coeff.support ⊆ S) (n : ℕ) :
    ∃ l ∈ (potentialVertices : Finset (S → ℝ)),
      FinProbability.rho n c p = ballBranch S c n l p.coeff ∧
      ∀ l' ∈ (potentialVertices : Finset (S → ℝ)),
        ballBranch S c n l' p.coeff ≤ FinProbability.rho n c p := by
  classical
  have hS : S.Nonempty := c.coeff_support_nonempty.mono hc
  let k : S → ℝ := fun y => c.coeff y-p.coeff y
  have hk : ∑ y, k y = 0 := by
    simp only [k,Finset.sum_sub_distrib,c.total_on_finset S hc,p.total_on_finset S hp,
      sub_self]
  obtain ⟨l,hl,⟨f,hf,hfl⟩,hmax⟩ := exists_global_vertex_maximizer S hS k hk
  have heq : c.transport p = ∑ y : S, k y*l y := by
    apply le_antisymm
    · apply FinProbability.transport_le
      intro g hg
      rw [c.gap_on_finset p S hc hp]
      exact hmax g hg
    · have hh := c.gap_le_transport p f hf
      rw [c.gap_on_finset p S hc hp] at hh
      simpa only [k,hfl] using hh
  refine ⟨l,hl,?_,?_⟩
  · rw [FinProbability.rho,heq,ballBranch_eq_pairing S c p hp]
  · intro l' hl'
    obtain ⟨g,hg,hgl⟩ := exists_global_potential_extension S (potentialVertices_subset l' hl')
    rw [ballBranch_eq_pairing S c p hp,FinProbability.rho]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hh := c.gap_le_transport p g hg
    rw [c.gap_on_finset p S hc hp] at hh
    simpa only [hgl] using hh

end

open Set Finset

open scoped BassTrace.Sparse

section

variable {Y : Type*}

lemma geometric_simplex_compact (s : Finset Y) :
    IsCompact (probabilitySet s) := by
  rw [← convexHull_single_eq_probabilitySet]
  exact (s.finite_toSet.image _).isCompact_convexHull ℝ

end

variable {Y : Type*} [MetricSpace Y]

lemma rho_eq_vertex_sup (S : Finset Y) (hS : S.Nonempty) (n : ℕ)
    (p q : FinProbability Y) (hp : p.coeff.support ⊆ S) (hq : q.coeff.support ⊆ S) :
    FinProbability.rho n p q =
      (potentialVertices : Finset (S → ℝ)).sup' (potentialVertices_nonempty S hS)
        (fun l => (∑ y : S, (p.coeff y-q.coeff y)*l y)/Real.sqrt n) := by
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer S p q hp hq n
  apply le_antisymm
  · rw [heq,ballBranch_eq_pairing S p q hq]
    exact Finset.le_sup' (fun l => (∑ y : S, (p.coeff y-q.coeff y)*l y)/Real.sqrt n) hl
  · apply (Finset.sup'_le_iff _ _).mpr
    intro l' hl'
    rw [← ballBranch_eq_pairing S p q hq]
    exact hmax l' hl'

lemma continuous_simplexProbability (S : Finset Y) (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) :
    let := FinProbability.rhoMetric n hn hd
    Continuous (simplexProbability S) := by
  let := FinProbability.rhoMetric n hn hd
  by_cases hS : S.Nonempty
  · rw [continuous_iff_continuous_dist]
    have heq : (fun p : probabilitySet S × probabilitySet S =>
        dist (simplexProbability S p.1) (simplexProbability S p.2)) =
        fun p => (potentialVertices : Finset (S → ℝ)).sup' (potentialVertices_nonempty S hS)
          (fun l => (∑ y : S, (p.1.val y-p.2.val y)*l y)/Real.sqrt n) := by
      funext p
      exact rho_eq_vertex_sup S hS n _ _ p.1.property.2.2 p.2.property.2.2
    rw [heq]
    apply Continuous.finset_sup'_apply
    intro l _
    apply Continuous.div_const
    apply continuous_finsetSum
    intro y _
    apply Continuous.mul_const
    apply Continuous.sub
    · exact (coordinateCLM (y : Y)).continuous.comp (continuous_subtype_val.comp continuous_fst)
    · exact (coordinateCLM (y : Y)).continuous.comp (continuous_subtype_val.comp continuous_snd)
  · have : IsEmpty (probabilitySet S) := ⟨fun v => hS
        ((simplexProbability S v).coeff_support_nonempty.mono v.property.2.2)⟩
    exact continuous_iff_continuousAt.mpr (fun v => isEmptyElim v)

lemma isCompact_probability_simplex (S : Finset Y) (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) :
    let := FinProbability.rhoMetric n hn hd
    IsCompact {p : FinProbability Y | p.coeff.support ⊆ S} := by
  let := FinProbability.rhoMetric n hn hd
  let : CompactSpace (probabilitySet S) := isCompact_iff_compactSpace.mp (geometric_simplex_compact S)
  have heq : {p : FinProbability Y | p.coeff.support ⊆ S} =
      Set.range (simplexProbability S) := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨p.coeff,p.nonneg,by simpa using p.total,hp⟩,rfl⟩
    · rintro ⟨v,rfl⟩
      exact v.property.2.2
  rw [heq]
  exact isCompact_range (continuous_simplexProbability S n hn hd)

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GraphRealization
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

section

open scoped BigOperators

open FinProbability

variable {Y : Type*} (Γ : SimpleGraph Y)

variable [DecidableEq Y] [Γ.LocallyFinite]

theorem finitely_many_meeting_top_simplices (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (s : ℝ) (hs : 0 ≤ s) :
    {σ | σ∈tops ∧ ∃ p : FinProbability Y, p.coeff.support ⊆ σ ∧
      @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s}.Finite := by
  let W := c.coeff.support.biUnion (neighborhood Γ (⌊s * Real.sqrt (n : ℝ)⌋₊+n))
  apply W.powerset.finite_toSet.subset
  rintro σ ⟨hσ,p,hp,hball⟩
  exact Finset.mem_powerset.mpr
    (meeting_simplex_vertices Γ hΓ hn c p σ (htop σ hσ).1 (htop σ hσ).2 hp s hs hball)

end

open Set Finset

end Sparse.GraphGeometry

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Topology

variable {Y : Type*} [DecidableEq Y] (Γ : SimpleGraph Y) [Γ.LocallyFinite]

lemma finitely_many_top_simplices_at (hΓ : Γ.Connected) {n : ℕ}
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) (v : Y) :
    {σ | σ ∈ tops ∧ v ∈ σ}.Finite := by
  apply (neighborhood Γ n v).powerset.finite_toSet.subset
  intro σ hσ
  apply Finset.mem_powerset.mpr
  intro w hw
  exact dist_le_mem_neighborhood Γ hΓ
    (connected_set_diameter Γ σ (htop σ hσ.1).1 (htop σ hσ.1).2 hσ.2 hw)

lemma locallyFinite_affine_top_simplices (hΓ : Γ.Connected) {n : ℕ}
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    LocallyFinite (fun σ : tops => {v : affineRealization tops | v.val ∈ probabilitySet σ.val}) := by
  intro p
  let q := affineProbability tops p
  obtain ⟨y,hy⟩ := q.coeff_support_nonempty
  have hpos : 0 < q.coeff y := lt_of_le_of_ne (q.nonneg y) (Finsupp.mem_support_iff.mp hy).symm
  let U : Set (affineRealization tops) := {v | 0 < v.val y}
  have hU : IsOpen U := isOpen_lt continuous_const
    ((coordinateCLM y).continuous.comp continuous_subtype_val)
  refine ⟨U,hU.mem_nhds hpos,?_⟩
  have hfin := finitely_many_top_simplices_at Γ hΓ tops htop y
  apply (hfin.preimage Subtype.val_injective.injOn).subset
  intro σ hσ
  obtain ⟨v,hv,hvU⟩ := hσ
  refine ⟨σ.property,hv.2.2 ?_⟩
  exact Finsupp.mem_support_iff.mpr (ne_of_gt hvU)

lemma continuous_affineProbability (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    Continuous (affineProbability tops) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  apply (locallyFinite_affine_top_simplices Γ hΓ tops htop).continuous
  · ext v
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    obtain ⟨σ,hσ,hv⟩ := Set.mem_iUnion₂.mp v.property
    exact ⟨⟨σ,hσ⟩,hv⟩
  · intro σ
    exact (geometric_simplex_compact σ.val).isClosed.preimage continuous_subtype_val
  · intro σ
    apply continuousOn_iff_continuous_domRestrict.mpr
    let f : {v : affineRealization tops | v.val ∈ probabilitySet σ.val} → probabilitySet σ.val :=
      fun v => ⟨v.val.val,v.property⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (continuous_simplexProbability σ.val n hn (graphMetric_discrete Γ hΓ)).comp hf

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_OrbitForms
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.FinProbability

open Set Finset

variable {Y Z W : Type*}

lemma push_support (e : Y ≃ Z) (p : FinProbability Y) :
    (push e p).coeff.support = p.coeff.support.map e.toEmbedding := rfl

lemma push_expectation (e : Y ≃ Z) (p : FinProbability Y) (f : Z → ℝ) :
    (push e p).expectation f = p.expectation (f ∘ e) := by
  classical
  unfold expectation Finsupp.sum
  rw [push_support,Finset.sum_map]
  simp

lemma push_gap (e : Y ≃ Z) (p q : FinProbability Y) (f : Z → ℝ) :
    (push e p).gap (push e q) f = p.gap q (f ∘ e) := by
  simp [gap,push_expectation]

lemma transport_push_le [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : LipschitzWith 1 e) (p q : FinProbability Y) :
    (push e p).transport (push e q) ≤ p.transport q := by
  apply transport_le
  intro f hf
  rw [push_gap]
  apply gap_le_transport
  simpa using hf.comp he

lemma transport_push [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : Isometry e) (p q : FinProbability Y) :
    (push e p).transport (push e q) = p.transport q := by
  apply le_antisymm (transport_push_le e he.lipschitz p q)
  have hei : Isometry e.symm := by
    intro z w
    simpa using (he (e.symm z) (e.symm w)).symm
  simpa using transport_push_le e.symm hei.lipschitz (push e p) (push e q)

lemma rho_push [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : Isometry e) (n : ℕ) (p q : FinProbability Y) :
    rho n (push e p) (push e q) = rho n p q := by
  simp [rho,transport_push e he]

end BassTrace.Sparse.FinProbability

namespace BassTrace.Sparse

open scoped Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

open scoped BassTrace.Sparse

lemma smul_probability_rho [PseudoMetricSpace Y]
    (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (h : H) (n : ℕ) (p q : FinProbability Y) :
    FinProbability.rho n (h • p) (h • q) = FinProbability.rho n p q :=
  FinProbability.rho_push (MulAction.toPerm h) (hi h) n p q

end BassTrace.Sparse

namespace BassTrace.Sparse.OrbitForms

open Set Finset

variable {H Y I : Type*} [Group H] [MulAction H Y]

variable (d : Data I Y)

variable [IsCancelSMul H Y]

variable [Fintype I]

lemma relevantEquiv_form (k : H) (s : Finset (Y →₀ ℝ)) (i : relevant (H := H) d s) :
    (form d (relevantEquiv d k s i).val).comp (push k).toLinearMap = form d i.val := by
  apply LinearMap.ext
  intro p
  exact form_translate d k i.val.1 i.val.2 p

end BassTrace.Sparse.OrbitForms

namespace BassTrace.Sparse.BallOrbitForms

open Set Finset

open scoped BassTrace.Sparse

variable {H Y C : Type*} [Group H] [MulAction H Y] [MetricSpace Y]

variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)

lemma branch_apply (h : H) (j : Index S) (p : FinProbability Y) :
    OrbitForms.form (data S c n) (h,j) p.coeff =
      ballBranch (S j.1) (c j.1) n j.2.val (h⁻¹ • p).coeff := by
  change ballBranch (S j.1) (c j.1) n j.2.val (OrbitForms.push h⁻¹ p.coeff) = _
  rw [push_coeff]

lemma exists_maximizer (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) :
    ∃ l : ↥(potentialVertices : Finset (S i → ℝ)),
      FinProbability.rho n (h • c i) p =
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff ∧
      ∀ l' : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l'⟩) p.coeff ≤
          FinProbability.rho n (h • c i) p := by
  have he : FinProbability.rho n (h • c i) p = FinProbability.rho n (c i) (h⁻¹ • p) := by
    simpa only [smul_inv_smul] using smul_probability_rho hi h n (c i) (h⁻¹ • p)
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer (S i) (c i) (h⁻¹ • p) (hc i) hp n
  refine ⟨⟨l,hl⟩,?_,?_⟩
  · rw [branch_apply,he]
    exact heq
  · intro l'
    rw [branch_apply,he]
    exact hmax _ l'.property

lemma distance_eq_iff (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) (t : ℝ) :
    FinProbability.rho n (h • c i) p = t ↔
      (∀ l : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff ≤ t) ∧
      ∃ l : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff = t := by
  obtain ⟨l,he,hm⟩ := exists_maximizer S c n hi hc h i p hp
  constructor
  · intro hh
    exact ⟨fun l' => hh ▸ hm l',l,he.symm.trans hh⟩
  · rintro ⟨hle,l',hlt⟩
    exact le_antisymm (he ▸ hle l) (hlt ▸ hm l')

end BassTrace.Sparse.BallOrbitForms

namespace BassTrace.Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse

variable {H Y I X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I]

variable (d : Data I Y) {t : ℝ} (ht : 0 < t)

lemma cuts_map {K L : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)} (k : H)
    (hKL : ∀ s ∈ K.faces, s.map (push k).toEmbedding ∈ L.faces)
    {s : Finset (Y →₀ ℝ)} (hs : s ∈ ((cuts (H := H) d ht).onComplex K).globalComplex.faces) :
    s.map (push k).toEmbedding ∈ ((cuts (H := H) d ht).onComplex L).globalComplex.faces := by
  apply Cuts.LocalCutData.globalComplex_map ((cuts (H := H) d ht).onComplex K)
    ((cuts (H := H) d ht).onComplex L) (push k).toLinearMap (push k).injective hKL
    (fun u _ => relevantEquiv d k u) _ _ hs
  · intro u _ j
    exact relevantEquiv_form d k u j
  · intros
    rfl

variable [TopologicalSpace X] [MulAction H X]

lemma refineFamily_equivariant {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    (T : Cuts.SubdivisionFamily X K) (hT : Equivariant (H := H) T) :
    Equivariant (H := H) ((cuts (H := H) d ht).refineFamily T) := by
  intro k x s hs
  exact cuts_map d ht k (hT k x) hs

end BassTrace.Sparse.OrbitForms

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BallGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Finite-center selection from compactness of closed original simplices, without a
cocompactness assumption on the continuous ambient space. -/

namespace Sparse

open Set

variable {H V I : Type*} [Group H] [PseudoMetricSpace V] [MulAction H V]

lemma finite_centers_of_compact {Q : Set V} (hQ : IsCompact Q) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset V, (C : Set V) ⊆ Q ∧ ∀ x ∈ Q, ∃ c ∈ C, dist x c < r := by
  classical
  obtain ⟨C,hC,hfin,hcov⟩ := hQ.elim_finite_subcover_image
    (b := Q) (c := fun c => Metric.ball c r) (fun _ _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨x,hx,by simpa using hr⟩)
  refine ⟨hfin.toFinset,by simpa using hC,?_⟩
  intro x hx
  obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hcov hx)
  exact ⟨c,by simpa using hc,hxc⟩

theorem exists_finite_orbit_centers (S : Set V) (P : I → Set V) (F : Finset I)
    (hcompact : ∀ i ∈ F, IsCompact (P i)) (hPS : ∀ i ∈ F, P i ⊆ S)
    (hcover : ∀ x ∈ S, ∃ h : H, ∃ i ∈ F, ∃ y ∈ P i, h • y = x)
    (hisom : ∀ h : H, Isometry (fun x : V => h • x)) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset V, (C : Set V) ⊆ S ∧
      ∀ x ∈ S, ∃ h : H, ∃ c ∈ C, dist x (h • c) < r := by
  have hQ : IsCompact (⋃ i ∈ F, P i) := F.finite_toSet.isCompact_biUnion hcompact
  obtain ⟨C,hC,hcov⟩ := finite_centers_of_compact hQ hr
  refine ⟨C,?_,?_⟩
  · intro c hc
    obtain ⟨i,hi,hci⟩ := Set.mem_iUnion₂.mp (hC hc)
    exact hPS i hi hci
  · intro x hx
    obtain ⟨h,i,hi,y,hy,rfl⟩ := hcover x hx
    obtain ⟨c,hc,hyc⟩ := hcov y (Set.mem_iUnion₂.mpr ⟨i,hi,hy⟩)
    exact ⟨h,c,hc,by simpa only [(hisom h).dist_eq] using hyc⟩

end Sparse

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*} [DecidableEq Y]

lemma supportPatch_marked (K : PreAbstractSimplicialComplex Y) (W : Finset Y) :
    Cuts.IsMarked (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (supportPatch K W) := by
  intro v hv
  obtain ⟨p,hp,hpK⟩ := (onFinsupp_space K) ▸ hv.1
  subst v
  refine ⟨p.coeff.support.image (fun y => Finsupp.single y (1:ℝ)),
    ⟨p.coeff.support,hpK,rfl⟩,?_,?_⟩
  · rw [Finset.coe_image,p.mem_geometric_simplex]
  · intro w hw
    have hw' := hw
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet] at hw'
    exact ⟨(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      ⟨p.coeff.support,hpK,rfl⟩ hw,hw'.2.2.trans hv.2⟩

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite]

lemma ballSupport_center (c : FinProbability Y) (n : ℕ) (R : ℝ) :
    c.coeff.support ⊆ ballSupport Γ c n R := Finset.subset_union_left

lemma ballSupport_contains (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
      (Γ.induce (σ : Set Y)).Connected)
    (c p : FinProbability Y) (hp : p.coeff.support ∈ K.faces)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ R) :
    p.coeff.support ⊆ ballSupport Γ c n R := by
  obtain ⟨σ,_,hs,hcard,hconn⟩ := hK _ hp
  exact hs.trans ((meeting_simplex_vertices Γ hΓ hn c p σ hcard hconn hs R hR hball).trans
    Finset.subset_union_right)

lemma onFinsupp_space_eq_affineRealization (K : PreAbstractSimplicialComplex Y) (n : ℕ)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      affineRealization (originalTops K n) := by
  ext v
  rw [onFinsupp_space]
  constructor
  · rintro ⟨p,rfl,hp⟩
    obtain ⟨σ,hσ,hs,hcard⟩ := hK _ hp
    exact Set.mem_iUnion₂.mpr ⟨σ,⟨hσ,hcard⟩,p.nonneg,by simpa using p.total,hs⟩
  · intro hv
    obtain ⟨σ,hσ,hv⟩ := Set.mem_iUnion₂.mp hv
    rw [probabilitySet_eq] at hv
    obtain ⟨p,rfl,hp⟩ := hv
    exact ⟨p,rfl,(K.isRelLowerSet_faces hσ.1).2 hp p.coeff_support_nonempty⟩

lemma continuous_pointProbability (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1)
    (hconn : ∀ σ ∈ originalTops K n, (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    Continuous (pointProbability K) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let e : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space →
      affineRealization (originalTops K n) := fun v =>
    ⟨v.val,(onFinsupp_space_eq_affineRealization K n hK) ▸ v.property⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have hc := (continuous_affineProbability Γ hΓ hn (originalTops K n)
    (fun σ hσ => ⟨hσ.2,hconn σ hσ⟩)).comp he
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  apply FinProbability.ext_coeff
  exact pointProbability_coeff K v

omit [Γ.LocallyFinite] in
lemma centerDistance_apply (hΓ : Γ.Connected) (K : PreAbstractSimplicialComplex Y)
    (n : ℕ) (c p : FinProbability Y) (hp : p.coeff.support ∈ K.faces) :
    centerDistance Γ hΓ K n c p.coeff =
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p := by
  have hv : p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
    rw [onFinsupp_space]
    exact ⟨p,rfl,hp⟩
  simp only [centerDistance,dite_eq_left hv]
  congr 1
  apply FinProbability.ext_coeff
  exact pointProbability_coeff K ⟨p.coeff,hv⟩

lemma continuousOn_centerDistance (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1)
    (hconn : ∀ σ ∈ originalTops K n, (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) :
    ContinuousOn (centerDistance Γ hΓ K n c)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc := (continuous_const (y := c)).dist (continuous_pointProbability Γ hΓ hn K hK hconn)
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  change centerDistance Γ hΓ K n c v.val = _
  simp only [centerDistance,dite_eq_left v.property]
  rfl

end Sparse.GraphGeometry

namespace Sparse.BallOrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [MetricSpace Y]

variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)

omit [Group H] [MulAction H Y] [DecidableEq Y] in
lemma mem_branches (h : H) (i : C) (j : H × Index S) :
    j ∈ branches S h i ↔ ∃ l : ↥(potentialVertices : Finset (S i → ℝ)), j=(h,⟨i,l⟩) := by
  simp [branches,eq_comm]

omit [DecidableEq Y] [MetricSpace Y] in
lemma inverse_support_iff (h : H) (p : FinProbability Y) (W : Finset Y) :
    (h⁻¹ • p).coeff.support ⊆ W ↔
      p.coeff.support ⊆ W.map (MulAction.toPerm h).toEmbedding := by
  have hh : p.coeff.support = (h⁻¹ • p).coeff.support.map (MulAction.toPerm h).toEmbedding := by
    rw [← smul_probability_support,smul_inv_smul]
  rw [hh,Finset.map_subset_map]

omit [MetricSpace Y] in
lemma translatedPatch_marked (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) :
    Cuts.IsMarked (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (translatedPatch S K h i) := GraphGeometry.supportPatch_marked _ _

omit [MetricSpace Y] in
lemma translatedPatch_mem (K : PreAbstractSimplicialComplex Y) (h : H) (i : C)
    (p : FinProbability Y) :
    p.coeff ∈ translatedPatch S K h i ↔
      p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∧
        (h⁻¹ • p).coeff.support ⊆ S i := by
  exact and_congr_right fun _ => (inverse_support_iff h p (S i)).symm

variable [IsCancelSMul H Y] [Fintype C]

lemma spherePatch_mem (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i)
    (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) (p : FinProbability Y)
    {t : ℝ} (ht : 0<t) :
    p.coeff ∈ ((OrbitForms.cuts (H := H) (data S c n) ht).spherePatch
        (translatedPatch S K h i) (branches S h i)) ↔
      p.coeff ∈ translatedPatch S K h i ∧ FinProbability.rho n (h • c i) p=t := by
  change (p.coeff ∈ translatedPatch S K h i ∧
      ∀ j ∈ branches S h i, OrbitForms.form (data S c n) j p.coeff ≤ t) ∧
      (∃ j ∈ branches S h i, OrbitForms.form (data S c n) j p.coeff=t) ↔ _
  constructor
  · rintro ⟨⟨hp,hle⟩,j,hj,he⟩
    obtain ⟨l,rfl⟩ := (mem_branches S h i j).mp hj
    refine ⟨hp,(distance_eq_iff S c n hi hc h i p ((translatedPatch_mem S K h i p).mp hp).2 t).mpr ?_⟩
    exact ⟨fun l' => hle _ ((mem_branches S h i _).mpr ⟨l',rfl⟩),l,he⟩
  · rintro ⟨hp,he⟩
    obtain ⟨hle,l,hl⟩ := (distance_eq_iff S c n hi hc h i p
      ((translatedPatch_mem S K h i p).mp hp).2 t).mp he
    refine ⟨⟨hp,?_⟩,(h,⟨i,l⟩),(mem_branches S h i _).mpr ⟨l,rfl⟩,hl⟩
    intro j hj
    obtain ⟨l',rfl⟩ := (mem_branches S h i j).mp hj
    exact hle l'

end Sparse.BallOrbitForms

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

section

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [Fintype C]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hn hK hact hi hm

omit [IsCancelSMul H Y] [Fintype C] in
lemma ballSupport_inverse (c : C → FinProbability Y) (h : H) (i : C)
    (p : FinProbability Y) (hp : p.coeff.support ∈ K.faces)
    {R : ℝ} (hR : 0≤R) (hball : FinProbability.rho n (h • c i) p ≤ R) :
    (h⁻¹ • p).coeff.support ⊆ ballSupport Γ (c i) n R := by
  subst mY
  let := graphMetric Γ hΓ
  have hp' : (h⁻¹ • p).coeff.support ∈ K.faces := by
    rw [smul_probability_support]
    exact hact h⁻¹ _ hp
  apply ballSupport_contains Γ hΓ hn K hK _ _ hp' hR
  have he := smul_probability_rho hi h⁻¹ n (h • c i) p
  rw [inv_smul_smul] at he
  rw [he]
  exact hball

lemma sphere_eq_patch (c : C → FinProbability Y) (h : H) (i : C)
    {R t : ℝ} (hR : 0≤R) (ht : 0<t) (htR : t≤R) :
    let S := fun i => ballSupport Γ (c i) n R
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∩
        {v | centerDistance Γ hΓ K n (h • c i) v=t} =
      (OrbitForms.cuts (H := H) (BallOrbitForms.data S c n) ht).spherePatch
        (BallOrbitForms.translatedPatch S K h i) (BallOrbitForms.branches S h i) := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  ext v
  constructor
  · rintro ⟨hv,he⟩
    change centerDistance Γ hΓ K n (h • c i) v = t at he
    let p := pointProbability K ⟨v,hv⟩
    have hp : p.coeff = v := pointProbability_coeff K _
    have hpK := pointProbability_face K ⟨v,hv⟩
    have he' : FinProbability.rho n (h • c i) p=t := by
      rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at he
      exact he
    rw [← hp]
    apply (BallOrbitForms.spherePatch_mem S c n hi (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mpr
    refine ⟨(BallOrbitForms.translatedPatch_mem S K h i p).mpr ⟨hp.symm ▸ hv,?_⟩,he'⟩
    exact ballSupport_inverse Γ hΓ rfl hn K hK hact hi c h i p hpK hR (he' ▸ htR)
  · intro hv
    have hvK : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := hv.1.1.1
    let p := pointProbability K ⟨v,hvK⟩
    have hp : p.coeff=v := pointProbability_coeff K _
    rw [← hp] at hv ⊢
    obtain ⟨_,he⟩ := (BallOrbitForms.spherePatch_mem S c n hi
      (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mp hv
    refine ⟨hp.symm ▸ hvK,?_⟩
    change centerDistance Γ hΓ K n (h • c i) p.coeff = t
    rw [centerDistance_apply Γ hΓ K n _ p (pointProbability_face K ⟨v,hvK⟩)]
    exact he

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

omit [Γ.LocallyFinite] [MetricSpace Y] in
lemma realizationDistance_center_triangle (n : ℕ) (c : FinProbability Y)
    (p : Y →₀ ℝ) (hp : p ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space)
    (q : Y →₀ ℝ) (hq : q ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    realizationDistance Γ hΓ K n p q ≤ centerDistance Γ hΓ K n c p +
      centerDistance Γ hΓ K n c q := by
  let := graphMetric Γ hΓ
  simp only [realizationDistance,centerDistance,dite_eq_left hp,dite_eq_left hq]
  exact (FinProbability.rho_triangle n _ c _).trans_eq (by rw [FinProbability.rho_comm n _ c])

omit [DecidableEq Y] [Γ.LocallyFinite] in
include hm hn in

lemma exists_orbit_center_cover
    (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset (FinProbability Y), (∀ c ∈ C, c.coeff.support ∈ K.faces) ∧
      ∀ p : FinProbability Y, p.coeff.support ∈ K.faces →
        ∃ h : H, ∃ c ∈ C, FinProbability.rho n p (h • c) < r := by
  subst mY
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let S : Set (FinProbability Y) := {p | p.coeff.support ∈ K.faces}
  let P : Finset Y → Set (FinProbability Y) := fun s => {p | p.coeff.support ⊆ s}
  obtain ⟨C,hC,hcov⟩ := exists_finite_orbit_centers (H := H) S P F
    (fun s _ => isCompact_probability_simplex s n hn (graphMetric_discrete Γ hΓ))
    (fun s hs p hp => (K.isRelLowerSet_faces (hF s hs)).2 hp p.coeff_support_nonempty)
    (by
      intro p hp
      obtain ⟨h,τ,hτ,he⟩ := hrep p.coeff.support hp
      refine ⟨h,τ,hτ,h⁻¹ • p,?_,smul_inv_smul h p⟩
      change (h⁻¹ • p).coeff.support ⊆ τ
      rw [BallOrbitForms.inverse_support_iff]
      exact he.subset)
    (fun h => Isometry.of_dist_eq (fun p q => smul_probability_rho hi h n p q)) hr
  exact ⟨C,hC,hcov⟩

end

variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

include hact in
lemma centerDistance_push (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
    (hi : ∀ h : H, @Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
      (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y => h • y))
    (n : ℕ) (h : H) (c : FinProbability Y) (v : Y →₀ ℝ)
    (hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    centerDistance Γ hΓ K n (h • c) (OrbitForms.push h v) =
      centerDistance Γ hΓ K n c v := by
  let := graphMetric Γ hΓ
  obtain ⟨p,rfl,hp⟩ := (onFinsupp_space K) ▸ hv
  have hhp : (h • p).coeff.support ∈ K.faces := by
    rw [smul_probability_support]
    exact hact h _ hp
  rw [BallOrbitForms.push_coeff,centerDistance_apply Γ hΓ K n _ _ hhp,
    centerDistance_apply Γ hΓ K n _ _ hp]
  exact smul_probability_rho hi h n c p

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AdmissibleCuts
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

section

variable {H Y C X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y] [Fintype C]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

omit [Group H] [MulAction H Y] [IsCancelSMul H Y] [Countable H] [Fintype C]
    [TopologicalSpace X] [CompactSpace X] [MulAction H X]
    [Γ.LocallyFinite] [MetricSpace Y] in
lemma onFinsupp_faces_countable :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces.Countable := by
  change (Finset.image (fun y => Finsupp.single y (1:ℝ)) '' K.faces).Countable
  exact (Set.to_countable K.faces).image _

include hm hn hK hact hi in

theorem admissibleStep_of_center_cover
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T) (hT : OrbitForms.Equivariant (H := H) T)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    (c : C → FinProbability Y) {R : ℝ} (hR : 0<R)
    (hcover : ∀ p : FinProbability Y, p.coeff.support ∈ K.faces →
      ∃ h : H, ∃ i : C, FinProbability.rho n p (h • c i) < R/2) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  let d := BallOrbitForms.data S c n
  obtain ⟨t,ht,hgen⟩ := T.exists_generic_level (onFinsupp_faces_countable K)
    (fun j : H × BallOrbitForms.Index S => OrbitForms.form d j) (by linarith : R/2<R)
  have ht0 : 0<t := lt_trans (by linarith) ht.1
  let D := OrbitForms.cuts (H := H) d ht0
  let A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P := by
    refine D.sphereStep T P (realizationDistance Γ hΓ K n) R t
      (fun i : H × C => centerDistance Γ hΓ K n (i.1 • c i.2))
      (fun i : H × C => BallOrbitForms.translatedPatch S K i.1 i.2)
      (fun i : H × C => BallOrbitForms.branches S i.1 i.2)
      (fun i => BallOrbitForms.translatedPatch_marked S K i.1 i.2)
      (fun i => sphere_eq_patch Γ hΓ rfl hn K hK hact hi c i.1 i.2 hR.le ht0 ht.2.le)
      (fun _ => rfl) ?_ ?_ ?_ ?_ ht.2.le
    · intro x F hF j
      obtain ⟨v,hv⟩ := (T.val x).complex.nonempty_of_mem_faces hF
      exact ⟨v,hv,hgen x F hF j v hv⟩
    · intro i
      apply continuousOn_centerDistance Γ hΓ hn K
        (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,_⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
      intro σ hσ
      obtain ⟨τ,_,hστ,hτ,hconn⟩ := hK σ hσ.1
      have hσcard : σ.card=n+1 := hσ.2
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by omega)
      rw [he]
      exact hconn
    · intro v hv
      let p := pointProbability K ⟨v,hv⟩
      obtain ⟨h,i,hpi⟩ := hcover p (pointProbability_face K ⟨v,hv⟩)
      refine ⟨(h,i),?_⟩
      change centerDistance Γ hΓ K n (h • c i) v < t
      have he : p.coeff = v := pointProbability_coeff K ⟨v,hv⟩
      rw [← he, centerDistance_apply Γ hΓ K n _ _ (pointProbability_face K ⟨v,hv⟩)]
      rw [FinProbability.rho_comm n (h • c i) p]
      exact hpi.trans ht.1
    · intro i p hp q hq
      exact realizationDistance_center_triangle Γ hΓ K n (i.1 • c i.2) p hp q hq
  refine ⟨A,OrbitForms.refineFamily_equivariant d ht0 T hT,?_⟩
  intro k x v hv
  change OrbitForms.push k v ∈ P.val (k • x) ∩
    ⋃ i : H × C, D.spherePatch (BallOrbitForms.translatedPatch S K i.1 i.2)
      (BallOrbitForms.branches S i.1 i.2)
  have hv' : v ∈ P.val x ∩
    ⋃ i : H × C, D.spherePatch (BallOrbitForms.translatedPatch S K i.1 i.2)
      (BallOrbitForms.branches S i.1 i.2) := hv
  obtain ⟨hPv,hv''⟩ := hv'
  obtain ⟨i,hi'⟩ := Set.mem_iUnion.mp hv''
  have hsp (j : H × C) := sphere_eq_patch Γ hΓ rfl hn K hK hact hi c
    j.1 j.2 hR.le ht0 ht.2.le
  have hvK := (hsp i).symm ▸ hi'
  refine ⟨hP k x v hPv,Set.mem_iUnion.mpr ⟨(k*i.1,i.2),?_⟩⟩
  rw [← hsp (k*i.1,i.2)]
  refine ⟨space_push K hact k v hvK.1,?_⟩
  change centerDistance Γ hΓ K n ((k*i.1) • c i.2) (OrbitForms.push k v) = t
  rw [mul_smul,centerDistance_push K hact Γ hΓ hi n k (i.1 • c i.2) v hvK.1]
  exact hvK.2

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi in

theorem exists_admissibleStep
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T) (hT : OrbitForms.Equivariant (H := H) T)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    {R : ℝ} (hR : 0<R) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero := by
  obtain ⟨C,_,hcov⟩ := exists_orbit_center_cover Γ hΓ hm hn K hi F hF hrep
    (by linarith : 0 < R/2)
  exact admissibleStep_of_center_cover Γ hΓ hm hn K hK hact hi T P hT hP
    (fun c : C => c.val) hR (by
      intro p hp
      obtain ⟨h,c,hc,hd⟩ := hcov p hp
      exact ⟨h,⟨c,hc⟩,hd⟩)

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TreeDeterminants
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceMeasurable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An oriented incidence matrix of a tree, with its root row deleted, is unimodular,
independently of a planar structure or ordering of children. -/

namespace BassTrace.Sparse

open MeasureTheory Set Finset

open scoped ENNReal

noncomputable section

lemma sum_barycentricParam {n : ℕ} (x : Fin n → ℝ) :
    ∑ i, barycentricParam x i = 1 := by
  rw [Fin.sum_univ_succ]
  simp

lemma barycentricParam_injective (n : ℕ) :
    Function.Injective (@barycentricParam n) := by
  intro x y h
  funext i
  exact congrFun h i.succ

lemma range_barycentricParam (n : ℕ) :
    Set.range (@barycentricParam n) = {p | ∑ i, p i = 1} := by
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact sum_barycentricParam x
  · intro hp
    refine ⟨fun i => p i.succ,?_⟩
    funext v
    induction v using Fin.cases with
    | zero =>
      change 1 - ∑ i : Fin n, p i.succ = p 0
      change ∑ i, p i = 1 at hp
      rw [Fin.sum_univ_succ] at hp
      linarith
    | succ v => rfl

lemma continuous_barycentricParam (n : ℕ) : Continuous (@barycentricParam n) := by
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => exact continuous_const.sub (continuous_finsetSum _ fun _ _ => continuous_apply _)
  | succ i => exact continuous_apply i

lemma treeParam_injective {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Function.Injective (treeParam T hT) := by
  intro x y h
  apply WithLp.ofLp_injective
  have he := barycentricParam_injective n h
  apply Matrix.mulVec_injective_iff_isUnit.mpr _ he
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT))

lemma range_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Set.range (treeParam T hT) = {p | ∑ i, p i = 1} := by
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin n) =>
      Matrix.toLin' (realTreeIncidence T hT) x.ofLp) := by
    apply Function.Surjective.comp _ (WithLp.ofLp_surjective 2)
    exact Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT)))
  rw [← range_barycentricParam n]
  exact hsurj.range_comp _

lemma continuous_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Continuous (treeParam T hT) :=
  (continuous_barycentricParam n).comp
    ((Matrix.toLin' (realTreeIncidence T hT)).continuous_of_finiteDimensional.comp (PiLp.continuous_ofLp _ _))

lemma treeArea_mono {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) {Q W : Set (Fin (n+1) → ℝ)} (h : Q ⊆ W) :
    treeArea T hT j Q ≤ treeArea T hT j W := measure_mono (Set.preimage_mono h)

lemma hausdorff_zero_eq_count {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (Q : Set E) : μH[0] Q = Measure.count Q := by
  classical
  have hf (s : Finset E) : μH[0] (s : Set E) = (s.card : ℝ≥0∞) := by
    rw [← sum_measure_singleton]
    simp
  by_cases hQ : Q.Finite
  · rw [← hQ.coe_toFinset,hf,Measure.count_apply_finset]
  · rw [Measure.count_apply_infinite hQ]
    apply top_unique
    apply le_of_tendsto' ENNReal.tendsto_nat_nhds_top
    intro n
    obtain ⟨s,hs,hcard⟩ := Set.Infinite.exists_subset_card_eq hQ n
    calc
      (n : ℝ≥0∞) = μH[0] (s : Set E) := by rw [hf,hcard]
      _ ≤ μH[0] Q := measure_mono hs

lemma treeArea_zero {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i, p i=1}) :
    treeArea T hT 0 Q = Measure.count Q := by
  rw [treeArea,Measure.euclideanHausdorffMeasure_zero,hausdorff_zero_eq_count]
  rw [← Measure.count_injective_image (treeParam_injective T hT)]
  rw [Set.image_preimage_eq_inter_range,range_treeParam,Set.inter_eq_self_of_subset_left hQ]

lemma nonempty_spanningTree {n : ℕ} {Γ : SimpleGraph (Fin (n+1))} (hΓ : Γ.Connected) :
    Nonempty (SpanningTree Γ) := by
  obtain ⟨T,hT,hTree⟩ := hΓ.exists_isTree_le
  exact ⟨⟨T,hT,hTree⟩⟩

lemma simplexArea_zero {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i, p i=1}) :
    simplexArea Γ 0 Q = Measure.count Q := by
  let := nonempty_spanningTree hΓ
  simp only [simplexArea,treeArea_zero _ _ Q hQ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_comm]; exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)

end

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TreeArea
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceMeasurable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open MeasureTheory Set Finset

open scoped ENNReal

section

lemma treeParam_treeCoordinates {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (p : Fin (n+1) → ℝ) (hp : ∑ i,p i=1) : treeParam T hT (treeCoordinates T hT p) = p := by
  obtain ⟨x,rfl⟩ := (show p ∈ Set.range (treeParam T hT) by rw [range_treeParam]; exact hp)
  rw [treeCoordinates_treeParam]

lemma treeParam_preimage_eq_image {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    treeParam T hT ⁻¹' Q = treeCoordinates T hT '' Q := by
  ext x
  constructor
  · intro hx
    exact ⟨treeParam T hT x,hx,treeCoordinates_treeParam T hT x⟩
  · rintro ⟨p,hp,rfl⟩
    simpa only [Set.mem_preimage,treeParam_treeCoordinates T hT p (hQ hp)] using hp

lemma convex_sum_one (n : ℕ) : Convex ℝ {p : Fin (n+1) → ℝ | ∑ i,p i=1} := by
  intro x hx y hy a b _ _ hab
  change ∑ i,(a • x + b • y) i = 1
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  change ∑ i,x i=1 at hx
  change ∑ i,y i=1 at hy
  rw [hx,hy]
  simpa using hab

lemma treeParam_preimage_simplex {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1) :
    treeParam T hT ⁻¹' convexHull ℝ (s : Set (Fin (n+1) → ℝ)) =
      convexHull ℝ (treeCoordinates T hT '' (s : Set (Fin (n+1) → ℝ))) := by
  rw [treeParam_preimage_eq_image T hT _ (convexHull_min (by exact hs) (convex_sum_one n))]
  exact (treeCoordinates T hT).toAffineMap.image_convexHull _

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma euclideanArea_eq_zero_of_dimH_lt {Q : Set E} {d : ℕ}
    (h : dimH Q < (d : ℝ≥0∞)) : μHE[d] Q = 0 := by
  have hh : μH[(d : ℝ)] Q = 0 := by
    apply hausdorffMeasure_of_dimH_lt (d := (d : NNReal))
    simpa using h
  rw [Measure.euclideanHausdorffMeasure_def,Measure.smul_apply,hh,smul_zero]

lemma euclideanArea_simplex_lt_top (s : Finset E) {d : ℕ} (hsd : s.card ≤ d+1) :
    μHE[d] (convexHull ℝ (s : Set E)) < ∞ := by
  classical
  by_cases hs : s.Nonempty
  · let Q := convexHull ℝ (s : Set E)
    let W := vectorSpan ℝ Q
    have hspan : W = vectorSpan ℝ (s : Set E) := by
      dsimp [W,Q]
      rw [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan]
    have hdim : Module.finrank ℝ W ≤ d := by
      rw [hspan]
      have hc : Fintype.card s = (s.card-1)+1 := by
        rw [Fintype.card_coe]
        have := Finset.card_pos.mpr hs
        omega
      have hr := finrank_vectorSpan_range_le ℝ ((↑) : s → E) hc
      rw [Subtype.range_coe_subtype] at hr
      exact hr.trans (by omega)
    have hQcv : Convex ℝ Q := convex_convexHull ℝ _
    have hQne : Q.Nonempty := convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    rcases lt_or_eq_of_le hdim with hlt|heq
    · rw [euclideanArea_eq_zero_of_dimH_lt (by
        rw [Real.Convex.dimH_eq_finrank_vectorSpan hQcv hQne]
        exact_mod_cast hlt)]
      exact ENNReal.zero_lt_top
    · obtain ⟨c,hc⟩ := hQne
      let f : W → E := fun w => (w : E)+c
      have hf : Isometry f := by
        apply Isometry.of_dist_eq
        intro u v
        simp only [f,dist_add_right,Subtype.dist_eq]
      have hQr : Q ⊆ Set.range f := by
        intro p hp
        refine ⟨⟨p-c,vsub_mem_vectorSpan ℝ hp hc⟩,?_⟩
        dsimp [f]
        abel
      have hcompact : IsCompact (f ⁻¹' Q) :=
        hf.isClosedEmbedding.isCompact_preimage (s.finite_toSet.isCompact_convexHull (𝕜 := ℝ))
      have hh := hf.euclideanHausdorffMeasure_preimage (d := d) Q
      rw [Set.inter_eq_self_of_subset_left hQr] at hh
      rw [← hh,← heq,InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact hcompact.measure_lt_top
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

lemma treeArea_simplex_lt_top {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1)
    {j : ℕ} (hc : s.card ≤ j+1) :
    treeArea T hT j (convexHull ℝ (s : Set (Fin (n+1) → ℝ))) < ∞ := by
  classical
  unfold treeArea
  rw [treeParam_preimage_simplex T hT s hs]
  rw [← Finset.coe_image]
  exact euclideanArea_simplex_lt_top _ ((Finset.card_image_le).trans hc)

lemma treeArea_iUnion_le {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I : Type*} (s : Finset I) (Q : I → Set (Fin (n+1) → ℝ)) (j : ℕ) :
    treeArea T hT j (⋃ i ∈ s, Q i) ≤ ∑ i ∈ s, treeArea T hT j (Q i) := by
  simp only [treeArea,Set.preimage_iUnion]
  exact measure_biUnion_finset_le s _

lemma treeArea_polyhedral_lt_top {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (F : Finset (Finset (Fin (n+1) → ℝ))) {j : ℕ}
    (hs : ∀ s ∈ F, ∀ p ∈ s, ∑ i,p i=1) (hc : ∀ s ∈ F, s.card ≤ j+1)
    {Q : Set (Fin (n+1) → ℝ)}
    (hQ : Q ⊆ ⋃ s ∈ F, convexHull ℝ (s : Set (Fin (n+1) → ℝ))) :
    treeArea T hT j Q < ∞ := by
  exact lt_of_le_of_lt ((treeArea_mono T hT j hQ).trans (treeArea_iUnion_le T hT F _ j))
    (ENNReal.sum_lt_top.mpr fun s h => treeArea_simplex_lt_top T hT s (hs s h) (hc s h))

lemma simplexArea_polyhedral_lt_top {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (F : Finset (Finset (Fin (n+1) → ℝ))) {j : ℕ}
    (hs : ∀ s ∈ F, ∀ p ∈ s, ∑ i,p i=1) (hc : ∀ s ∈ F, s.card ≤ j+1)
    {Q : Set (Fin (n+1) → ℝ)}
    (hQ : Q ⊆ ⋃ s ∈ F, convexHull ℝ (s : Set (Fin (n+1) → ℝ))) :
    simplexArea Γ j Q < ∞ := by
  classical
  let := nonempty_spanningTree hΓ
  unfold simplexArea
  apply ENNReal.div_lt_top
  · exact ne_of_lt (ENNReal.sum_lt_top.mpr fun T _ => treeArea_polyhedral_lt_top T.val T.property.2 F hs hc hQ)
  · exact_mod_cast Fintype.card_ne_zero

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MarkedArea
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.Cuts

open Set Finset MeasureTheory

open scoped ENNReal

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

variable {T : SubdivisionFamily X K} (P : MarkedFamily T)

lemma MarkedFamily.localArea_locallyConstant {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (s : Finset V) (hs : s ∈ K.faces)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) (j : ℕ) :
    IsLocallyConstant (P.localArea Γ η W j) :=
  (P.localConstancy_inter s hs W hW).comp (fun Q => simplexArea Γ j (η '' Q))

lemma MarkedFamily.localArea_lt_top {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (s : Finset V) (hs : s ∈ K.faces)
    (hη : ∀ p ∈ convexHull ℝ (s : Set V), ∑ i, η p i=1)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) (j : ℕ) (x : X)
    (hd : ∀ t ∈ (T.val x).complex.faces,
      convexHull ℝ (t : Set V) ⊆ P.val x → t.card ≤ j+1) :
    P.localArea Γ η W j x < ∞ := by
  classical
  let L := restrictComplex (geometricRestriction (T.val x).complex (P.val x))
    (convexHull ℝ (s : Set V))
  have hf : L.faces.Finite := ((T.val x).finite s hs).subset (fun _ h => ⟨h.1.1,h.2⟩)
  let F := hf.toFinset
  let A := F.image (fun t => t.image η)
  have hA : ∀ t ∈ A, ∀ p ∈ t, ∑ i,p i=1 := by
    rintro t ht p hp
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    have hl : u ∈ L.faces := hf.mem_toFinset.mp hu
    exact hη v (hl.2 hv)
  have hcard : ∀ t ∈ A, t.card ≤ j+1 := by
    rintro t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    have hl : u ∈ L.faces := hf.mem_toFinset.mp hu
    exact (Finset.card_image_le).trans (hd u hl.1.1 hl.1.2)
  apply simplexArea_polyhedral_lt_top Γ hΓ A hA hcard
  rintro _ ⟨p,hp,rfl⟩
  have hpL : p ∈ L.space := by
    change p ∈ (restrictComplex (geometricRestriction (T.val x).complex (P.val x))
      (convexHull ℝ (s : Set V))).space
    rw [P.trace_space s hs x]
    exact ⟨hp.1,hW hp.2⟩
  obtain ⟨u,hu,hpu⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hpL
  apply Set.mem_iUnion₂.mpr
  refine ⟨u.image η,Finset.mem_image.mpr ⟨u,hf.mem_toFinset.mpr hu,rfl⟩,?_⟩
  rw [Finset.coe_image]
  change η.toAffineMap p ∈ convexHull ℝ (η.toAffineMap '' (u : Set V))
  rw [← η.toAffineMap.image_convexHull]
  exact ⟨p,hpu,rfl⟩

end Sparse.Cuts

namespace Sparse

section

open Set MeasureTheory

open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
lemma IsLocallyConstant.lintegral_lt_top {f : X → ℝ≥0∞} (hf : IsLocallyConstant f)
    (hfin : ∀ x, f x < ∞) (μ : Measure X) [IsFiniteMeasure μ] :
    ∫⁻ x, f x ∂μ < ∞ := by
  classical
  let F := hf.range_finite.toFinset
  have hb (x : X) : f x ≤ ∑ t ∈ F,t :=
    show f x ≤ ∑ t ∈ hf.range_finite.toFinset, (fun t : ℝ≥0∞ => t) t from
      Finset.single_le_sum (f := fun t : ℝ≥0∞ => t) (fun _ _ => bot_le)
        (hf.range_finite.mem_toFinset.mpr (Set.mem_range_self x))
  apply lt_of_le_of_lt (lintegral_mono hb)
  rw [lintegral_const]
  apply ENNReal.mul_lt_top
  · apply ENNReal.sum_lt_top.mpr
    intro t ht
    obtain ⟨x,rfl⟩ := hf.range_finite.mem_toFinset.mp ht
    exact hfin x
  · exact measure_lt_top μ _

end

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical Pointwise

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

lemma simplexCoordinates_sum {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p ∈ convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    ∑ i, simplexCoordinates s hs p i = 1 := by
  have hprob : p ∈ probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  calc
    (∑ i, simplexCoordinates s hs p i) = ∑ y : s,p y :=
      (simplexEnumeration s hs).sum_comp (fun y : s => p y)
    _ = ∑ y ∈ s,p y := Finset.sum_attach s (fun y => p y)
    _ = 1 := (sum_coeff_of_support_subset s p hprob.2.2).trans hprob.2.1

omit [DecidableEq Y] in
lemma simplexGraph_connected {n : ℕ} (Γ : SimpleGraph Y) (s : Finset Y) (hs : s.card=n+1)
    (hΓ : (Γ.induce (s : Set Y)).Connected) : (simplexGraph Γ s hs).Connected := by
  let e : simplexGraph Γ s hs ≃g Γ.induce (s : Set Y) := {
    toEquiv := simplexEnumeration s hs
    map_rel_iff' := by intro a b; rfl }
  exact e.connected_iff.mpr hΓ

omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma originalArea_locallyConstant {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) : IsLocallyConstant (originalArea Γ Q σ j) :=
  Q.P.localArea_locallyConstant _ _ (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    _ intrinsicInterior_subset j

omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma originalArea_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (hΓ : (Γ.induce (σ.val : Set Y)).Connected) (j : ℕ) (x : X)
    (hd : ∀ t ∈ (Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ Q.P.val x → t.card ≤ j+1) :
    originalArea Γ Q σ j x < ∞ :=
  Q.P.localArea_lt_top _ (simplexGraph_connected Γ σ.val σ.property.2 hΓ) _
    (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    (fun _ hp => simplexCoordinates_sum σ.val σ.property.2 hp)
    _ intrinsicInterior_subset j x hd

end

lemma exists_nearMinimizer {A : Type*} [Nonempty A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) {ε : ℝ} (hε : 0<ε) :
    ∃ a, ∀ b, f a ≤ f b+ε := by
  have hb : BddBelow (Set.range f) := ⟨0,by rintro _ ⟨a,rfl⟩; exact hf a⟩
  obtain ⟨_,⟨a,rfl⟩,ha⟩ := exists_lt_of_csInf_lt (Set.range_nonempty f)
    (lt_add_of_pos_right (sInf (Set.range f)) hε)
  refine ⟨a,fun b => ?_⟩
  exact ha.le.trans (by simpa only [add_comm] using add_le_add_right (csInf_le hb (Set.mem_range_self b)) ε)

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_EquivariantSurgery
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.OrbitForms

open Set Finset

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}

variable (ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ) (R : ℝ)

omit [DecidableEq Y] in

theorem exists_nearMinimal_filtration {n : ℕ}
    (original : MarkedPair (H := H) (X := X) K)
    (htop : ∀ x, (original.T.val x).complex = K)
    (hspace : ∀ x, original.P.val x = K.space)
    (hex : ∀ Q : MarkedPair (H := H) (X := X) K, Nonempty (EquivariantStep ρ R Q))
    (cost : ℕ → MarkedPair (H := H) (X := X) K → ℝ)
    (hc : ∀ i Q, 0 ≤ cost i Q) {ε : ℝ} (hε : 0<ε) :
    ∃ Q : SeparatingFiltration (H := H) (X := X) K ρ R n,
      Q.NearMinimal ρ R cost ε := by
  let Pair := MarkedPair (H := H) (X := X) K
  have hm (i : ℕ) (Q : Pair) : ∃ A : EquivariantStep ρ R Q,
      ∀ B : EquivariantStep ρ R Q, cost i A.result ≤ cost i B.result+ε := by
    let := hex Q
    exact exists_nearMinimizer (fun A : EquivariantStep ρ R Q => cost i A.result)
      (fun A => hc i A.result) hε
  let step (i : ℕ) (Q : Pair) := (hm i Q).choose
  have hstep (i : ℕ) (Q : Pair) := (hm i Q).choose_spec
  let seq : ℕ → Pair := Nat.rec original (fun k Q => (step (n-(k+1)) Q).result)
  have hseq (k : ℕ) : seq (k+1) = (step (n-(k+1)) (seq k)).result := rfl
  let Q : SeparatingFiltration (H := H) (X := X) K ρ R n := {
    pair := fun i => seq (n-i)
    top := by intro x; rw [Nat.sub_self]; exact htop x
    top_space := by intro x; rw [Nat.sub_self]; exact hspace x
    finer := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.finer x
    nested := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.subset x
    drop := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.dimensionDrop x
    diameter := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.diameter x }
  refine ⟨Q,?_⟩
  intro i hi A
  change cost i (seq (n-i)) ≤ cost i A.result + ε
  rw [show n-i=(n-(i+1))+1 by omega,hseq,show n-(n-(i+1)+1)=i by omega]
  exact hstep i (seq (n-(i+1))) A

end Sparse.OrbitForms

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi in

theorem exists_normalized_nearMinimal
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    (μ : Measure X) (reps : Finset (SourceTop K n))
    {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) R
        (fun j P => (normalizedArea Γ μ reps P j).toReal) ε := by
  apply OrbitForms.exists_nearMinimal_filtration
    (realizationDistance Γ hΓ K n) R (originalMarkedPair K hact)
    (fun _ => rfl) (fun _ => rfl)
  · intro Q
    obtain ⟨A,hA,hP⟩ := exists_admissibleStep Γ hΓ hm hn K hK hact hi F hF hrep
      Q.T Q.P Q.equivariant Q.markedEquivariant hR
    exact ⟨⟨A,hA,hP⟩⟩
  · exact fun _ _ => ENNReal.toReal_nonneg
  · exact hε

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SimplexMeasures
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceMeasurable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open MeasureTheory Set Finset

open scoped ENNReal

lemma treeAreaMeasure_apply {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) :
    treeAreaMeasure T hT j Q = treeArea T hT j Q :=
  ((continuous_treeParam T hT).measurableEmbedding (treeParam_injective T hT)).map_apply _ _

lemma simplexAreaMeasure_apply {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (j : ℕ)
    (Q : Set (Fin (n+1) → ℝ)) : simplexAreaMeasure Γ j Q = simplexArea Γ j Q := by
  simp only [simplexAreaMeasure,Measure.smul_apply,Measure.finsetSum_apply,
    treeAreaMeasure_apply,smul_eq_mul,simplexArea,div_eq_mul_inv,mul_comm]

end

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

section

variable {Y : Type*} [DecidableEq Y]

lemma simplexEmbed_coordinates {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p.support ⊆ s) :
    simplexEmbed s hs (simplexCoordinates s hs p) = p := by
  let q := simplexEmbed s hs (simplexCoordinates s hs p)
  have hq := simplexEmbed_support s hs (simplexCoordinates s hs p)
  ext y
  by_cases hy : y∈s
  · obtain ⟨i,hi⟩ := (simplexEnumeration s hs).surjective ⟨y,hy⟩
    have h := congrFun (simplexCoordinates_embed s hs (simplexCoordinates s hs p)) i
    change q (simplexEnumeration s hs i).val = p (simplexEnumeration s hs i).val at h
    simpa only [hi] using h
  · exact (Finsupp.notMem_support_iff.mp (fun h => hy (hq h))).trans
      (Finsupp.notMem_support_iff.mp (fun h => hy (hp h))).symm

omit [DecidableEq Y] in
lemma simplexEmbed_injective {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    Function.Injective (simplexEmbed s hs) :=
  Function.HasLeftInverse.injective ⟨simplexCoordinates s hs,simplexCoordinates_embed s hs⟩

lemma simplexEmbed_preimage {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (Q : Set (Y →₀ ℝ)) (hQ : ∀ p∈Q,p.support⊆s) :
    simplexEmbed s hs ⁻¹' Q = simplexCoordinates s hs '' Q := by
  ext p
  constructor
  · intro hp
    exact ⟨simplexEmbed s hs p,hp,simplexCoordinates_embed s hs p⟩
  · rintro ⟨q,hq,rfl⟩
    change simplexEmbed s hs (simplexCoordinates s hs q)∈Q
    rw [simplexEmbed_coordinates s hs (hQ q hq)]
    exact hq

lemma originalAreaMeasure_apply {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (s : Finset Y) (hs : s.card=n+1) (j : ℕ)
    (Q : Set (Y →₀ ℝ)) (hQ : ∀ p∈Q,p.support⊆s) :
    originalAreaMeasure Γ s hs j Q = simplexArea Γ j (simplexCoordinates s hs '' Q) := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  unfold originalAreaMeasure
  have he : MeasurableEmbedding (simplexEmbed s hs) :=
    (simplexEmbed s hs).continuous_of_finiteDimensional.measurableEmbedding
      (simplexEmbed_injective s hs)
  rw [he.map_apply, simplexEmbed_preimage s hs Q hQ,simplexAreaMeasure_apply]

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

lemma support_of_mem_sourceInterior (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈sourceInterior s) : p.support⊆s := by
  have hh := intrinsicInterior_subset hp
  rw [show (simplexVertices s : Set (Y →₀ ℝ)) =
    (fun y => Finsupp.single y (1 : ℝ)) '' (s : Set Y) from Finset.coe_image] at hh
  rw [convexHull_single_eq_probabilitySet s] at hh
  exact hh.2.2

lemma originalArea_eq_measure {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (x : X) :
    originalArea Γ Q σ j x =
      originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
      (Q.P.val x ∩ sourceInterior σ.val) := by
  symm
  exact originalAreaMeasure_apply _ _ _ _ _
    (fun p hp => support_of_mem_sourceInterior σ.val hp.2)

end

open MeasureTheory Set Finset

open scoped ENNReal

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AreaSurgery
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open Finset Set MeasureTheory

open scoped Pointwise Classical BassTrace.Sparse ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.instMulActionSourceTop
omit hact in
lemma localOriginalArea_locallyConstant (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) :
    IsLocallyConstant (localOriginalArea Γ Q σ j W) :=
  Q.P.localArea_locallyConstant _ _ (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    _ (Set.inter_subset_left.trans intrinsicInterior_subset) j

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.instMulActionSourceTop_1
omit hact in
lemma localOriginalArea_eq_measure (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ j W x =
      originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
        ((Q.P.val x ∩ sourceInterior σ.val) ∩ W) := by
  rw [originalAreaMeasure_apply _ _ _ _ _
    (fun p hp => support_of_mem_sourceInterior σ.val hp.1.2),Set.inter_assoc]
  rfl

end

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GraphCounting
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceMeasurable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK in
lemma localTops_finite (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    (localTops (K := K) (n := n) Γ hΓ c b).Finite := by
  have hconn (σ : Finset Y) (hs : σ∈K.faces ∧ σ.card=n+1) :
      (Γ.induce (σ : Set Y)).Connected := by
    obtain ⟨τ,hτ,hστ,hcard,hct⟩ := hK σ hs.1
    have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,hs.2])
    exact he.symm ▸ hct
  have hfin := finitely_many_meeting_top_simplices Γ hΓ hn
    {σ : Finset Y | σ∈K.faces ∧ σ.card=n+1} (fun σ hs=>⟨hs.2,hconn σ hs⟩) c b hb
  apply (hfin.preimage (show Function.Injective (fun σ : SourceTop K n=>σ.val) from Subtype.val_injective).injOn).subset
  rintro σ ⟨v,hv,hvb⟩
  refine ⟨σ.property,?_⟩
  have hvK := (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
    (show simplexVertices σ.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces from
      ⟨σ.val,σ.property.1,rfl⟩) (intrinsicInterior_subset hv)
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K ⟨v,hvK⟩
  refine ⟨p,?_,?_⟩
  · rw [hp]
    exact support_of_mem_sourceInterior σ.val hv
  · rw [← centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩),hp]
    exact hvb

include hn hK in

lemma ballMass_lt_top
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) [IsFiniteMeasure μ] (B : Set X) (j : ℕ)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤j+1)
    (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    ballMass (n := n) Γ hΓ Q μ B j c b<∞ := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have hzero (σ : SourceTop K n) (hσ : σ∉F) (x : X) :
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
    rw [localOriginalArea_eq_measure]
    have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨⟨_,hv⟩,hr⟩
      exact hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr ⟨v,hv,hr⟩)
    rw [he,measure_empty]
  have hle (x : X) : (∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x) ≤
      ∑ σ∈F,originalArea Γ Q σ j x := by
    rw [tsum_eq_sum (s := F) (fun σ hσ=>hzero σ hσ x)]
    apply Finset.sum_le_sum
    intro σ _
    rw [localOriginalArea_eq_measure,originalArea_eq_measure]
    exact measure_mono Set.inter_subset_left
  apply lt_of_le_of_lt (lintegral_mono hle)
  rw [lintegral_finsetSum F (fun σ _=>(originalArea_locallyConstant Γ Q σ j).continuous.measurable)]
  apply ENNReal.sum_lt_top.mpr
  intro σ _
  apply IsLocallyConstant.lintegral_lt_top (originalArea_locallyConstant Γ Q σ j)
  intro x
  apply originalArea_lt_top Γ Q σ _ j x (hd x)
  obtain ⟨τ,hτ,hστ,hcard,hct⟩ := hK σ.val σ.property.1
  have he : σ.val=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,σ.property.2])
  exact he.symm ▸ hct

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_VolumeBounds
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

/-! Scalar estimates for iterated volume growth and high-dimensional ball bounds. -/

open Finset MeasureTheory intervalIntegral

namespace Sparse

/-! A strict high-dimensional volume margin with radius 4 D² and half-radius 2 D². -/

lemma square_succ_le_two_pow {t : ℕ} (ht : 6 ≤ t) : (t + 1) ^ 2 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [pow_succ (2 : ℕ) t]
      have hsq : (t + 1 + 1) ^ 2 ≤ 2 * (t + 1) ^ 2 := by nlinarith
      omega

lemma real_sqrt_lt_nat_sqrt_succ (n : ℕ) :
    Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' n
  have ht : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

lemma floor_radius_sqrt_bound (D n : ℕ) :
    ⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ ≤
      4 * D ^ 2 * (Nat.sqrt n + 1) := by
  have hnonneg : 0 ≤ (4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ) := by positivity
  have hfloor := Nat.floor_le hnonneg
  have hroot := (real_sqrt_lt_nat_sqrt_succ n).le
  have hmul := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ 4 * (D : ℝ) ^ 2)
  have h : (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤
      4 * (D : ℝ) ^ 2 * ((Nat.sqrt n : ℝ) + 1) := hfloor.trans hmul
  exact_mod_cast h

theorem exponential_volume_margin (D n : ℕ) (hD : 2 ≤ D)
    (hn : volumeThreshold D ≤ n) :
    (n + 1) * D ^ (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) < 2 ^ n := by
  let t := Nat.sqrt n
  have ht : 4 * D ^ 3 + D + 3 ≤ t := Nat.le_sqrt'.mpr hn
  have htp : 6 ≤ t := by
    have hcube : 1 ≤ D ^ 3 := Nat.one_le_pow 3 D (by omega)
    omega
  have hnt : n + 1 ≤ 2 ^ t :=
    (Nat.succ_le_succ_sqrt' n).trans (square_succ_le_two_pow htp)
  have hfloor := floor_radius_sqrt_bound D n
  have hbase : D ≤ 2 ^ D := (Nat.lt_two_pow_self (n := D)).le
  have hexp : t + D * (4 * D ^ 2 * (t + 1) + 1) < t ^ 2 := by
    have h1 : (4 * D ^ 3 + D + 3) * t ≤ t * t := Nat.mul_le_mul_right t ht
    have h2 : 4 * D ^ 3 + D + 3 ≤ 3 * t := by omega
    nlinarith
  calc
    (n + 1) * D ^ (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1)
        ≤ 2 ^ t * (2 ^ D) ^ (4 * D ^ 2 * (t + 1) + 1) := by
          apply Nat.mul_le_mul hnt
          exact (Nat.pow_le_pow_left hbase _).trans
            (Nat.pow_le_pow_right (by positivity) (Nat.add_le_add_right hfloor 1))
    _ = 2 ^ (t + D * (4 * D ^ 2 * (t + 1) + 1)) := by
      rw [← pow_mul, ← pow_add]
    _ < 2 ^ (t ^ 2) := Nat.pow_lt_pow_right (by omega) hexp
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (Nat.sqrt_le' n)

theorem strict_volume_margin (D n : ℕ) (hD : 2 ≤ D)
    (hn : volumeThreshold D ≤ n) :
    ((n + 1 : ℕ) : ℝ) * (D : ℝ) ^
       (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) *
       (D : ℝ) ^ (2 * n) / (n.factorial : ℝ) <
      (2 * (D : ℝ) ^ 2) ^ n / (n.factorial : ℝ) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (div_lt_div_iff_of_pos_right hf).2
  have h := exponential_volume_margin D n hD hn
  have hc : ((n + 1 : ℕ) : ℝ) * (D : ℝ) ^
      (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) < (2 : ℝ) ^ n := by
    exact_mod_cast h
  have hDp : (0 : ℝ) < (D : ℝ) ^ (2 * n) := by positivity
  have hm := mul_lt_mul_of_pos_right hc hDp
  simpa only [mul_pow, pow_mul] using hm

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

omit [DecidableEq Y] [Γ.LocallyFinite] in
include hK in
lemma sourceTop_connected (σ : SourceTop K n) : (Γ.induce (σ.val : Set Y)).Connected := by
  obtain ⟨τ,_,hστ,hcard,hct⟩ := hK σ.val σ.property.1
  have he : σ.val=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,σ.property.2])
  exact he.symm ▸ hct

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BallMass
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceMeasurable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

omit [Γ.LocallyFinite] in
lemma localOriginalArea_eq_zero_of_not_mem_localTops
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (b : ℝ) (σ : SourceTop K n)
    (hσ : σ∉localTops (K := K) (n := n) Γ hΓ c b) (x : X) :
    localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
  rw [localOriginalArea_eq_measure]
  have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro v ⟨⟨_,hv⟩,hr⟩
    exact hσ ⟨v,hv,hr⟩
  rw [he,measure_empty]

include hn hK in
lemma ballIntegrand_locallyConstant
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    IsLocallyConstant (ballIntegrand (n := n) Γ hΓ Q j c b) := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have he (x : X) : ballIntegrand (n := n) Γ hΓ Q j c b x =
      ∑ σ∈F,localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x := by
    apply tsum_eq_sum
    intro σ hσ
    exact localOriginalArea_eq_zero_of_not_mem_localTops Γ hΓ Q j c b σ
      (fun h=>hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr h)) x
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hall : ∀ᶠ y in nhds x,∀ σ∈F,
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} y=
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x :=
    F.eventually_all.mpr fun σ _=>(localOriginalArea_locallyConstant Γ Q σ j _).eventually_eq x
  filter_upwards [hall] with y hy
  rw [he,he]
  exact Finset.sum_congr rfl hy

omit [Γ.LocallyFinite] in
include hK in
lemma localOriginalArea_zero_eq_count
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ 0 W x = Measure.count
      (simplexCoordinates σ.val σ.property.2 '' (Q.P.val x∩(sourceInterior σ.val∩W))) := by
  apply simplexArea_zero _ (simplexGraph_connected Γ σ.val σ.property.2 (sourceTop_connected Γ hK σ))
  rintro _ ⟨v,⟨_,hv,_⟩,rfl⟩
  exact simplexCoordinates_sum _ _ (intrinsicInterior_subset hv)

end

end Sparse.GraphGeometry

/-! Finite clopen partitions and disjoint translates. -/

namespace Sparse.GraphGeometry

lemma ballVolume_strict_margin (D n : ℕ) (hD : 2≤D) (hn : volumeThreshold D≤n) :
    ballVolumeBound D n (4*(D : ℝ)^2)<
      dividedPower n (4*(D : ℝ)^2-2*(D : ℝ)^2) := by
  have he : 4*(D : ℝ)^2-2*(D : ℝ)^2=2*(D : ℝ)^2 := by ring
  simpa [ballVolumeBound,dividedPower,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,he] using
    strict_volume_margin D n hD hn

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ZeroStrata
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.FreeParameter.spaceMeasurable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {Y : Type*} [DecidableEq Y]

lemma affineSpan_simplex_constraints (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈affineSpan ℝ (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))) :
    coefficientSum p=1 ∧ ∀ y∉s,p y=0 := by
  rw [affineSpan_convexHull] at hp
  refine affineSpan_induction (p := fun p : Y →₀ ℝ=>
    coefficientSum p=1 ∧ ∀ y∉s,p y=0) hp ?_ ?_
  · intro q hq
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨by simp,?_⟩
    intro z hz
    simp [show y≠z from fun he=>hz (he ▸ hy)]
  · intro a u v w hu hv hw
    change coefficientSum (a•(u-v)+w)=1 ∧ ∀ y∉s,(a•(u-v)+w) y=0
    constructor
    · simp [map_add,map_smul,map_sub,hu.1,hv.1,hw.1]
    · intro y hy
      simp [hu.2 y hy,hv.2 y hy,hw.2 y hy]

lemma mem_sourceInterior_of_positive (s : Finset Y) (p : FinProbability Y)
    (hs : p.coeff.support⊆s) (hp : ∀ y∈s,0<p.coeff y) :
    p.coeff∈sourceInterior s := by
  let C := convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))
  have hC : C=probabilitySet s := by
    dsimp [C,simplexVertices]
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet]
  have hpC : p.coeff∈C := hC ▸ ⟨p.nonneg,by simpa using p.total,hs⟩
  let q : affineSpan ℝ C := ⟨p.coeff,(subset_affineSpan ℝ C hpC)⟩
  let U : Set (affineSpan ℝ C) := ⋂ y : s,
    (fun v : affineSpan ℝ C=>v.val y.val) ⁻¹' Ioi 0
  have hU : IsOpen U := isOpen_iInter_of_finite fun y=>isOpen_Ioi.preimage
    ((coordinateCLM y.val).continuous.comp continuous_subtype_val)
  have hq : q∈U := Set.mem_iInter.mpr fun y=>hp y.val y.property
  have hUC : U⊆(Subtype.val ⁻¹' C) := by
    intro v hv
    have ha := affineSpan_simplex_constraints s v.property
    change v.val∈C
    apply (Set.ext_iff.mp hC v.val).mpr
    refine ⟨?_,ha.1,?_⟩
    · intro y
      by_cases hy : y∈s
      · exact (Set.mem_iInter.mp hv ⟨y,hy⟩).le
      · rw [ha.2 y hy]
    · intro y hy
      by_contra h
      exact Finsupp.mem_support_iff.mp hy (ha.2 y h)
  exact ⟨q,mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hq) hUC),rfl⟩

lemma probability_mem_own_sourceInterior (p : FinProbability Y) :
    p.coeff∈sourceInterior p.coeff.support :=
  mem_sourceInterior_of_positive _ p subset_rfl fun y hy=>
    lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy))

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

open GraphGeometry

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

variable (hK : ∀ s∈K.faces,s.card≤n+1)

include hK in
lemma zero_mem_sourceTop_interior (x : X) {v : Y →₀ ℝ}
    (hv : v∈(Q.pair 0).P.val x) : ∃ σ : SourceTop K n,v∈sourceInterior σ.val := by
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hv
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hs := pointProbability_face K ⟨v,hvK⟩
  have hf : simplexVertices p.coeff.support∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := ⟨_,hs,rfl⟩
  have hmem : v∈convexHull ℝ (simplexVertices p.coeff.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  have hl := (Q.point x).card_lower_of_mem_zero (i := n) le_rfl hv
    (show simplexVertices p.coeff.support∈((Q.point x).T n).faces by
      change _∈((Q.pair n).T.val x).complex.faces
      rw [Q.top]; exact hf)
    (show convexHull ℝ (simplexVertices p.coeff.support : Set (Y →₀ ℝ))⊆(Q.point x).Z n by
      change _⊆(Q.pair n).P.val x
      rw [Q.top_space]
      exact (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space hf) hmem
  have hlow : n+1≤p.coeff.support.card := hl.trans Finset.card_image_le
  have hcard : p.coeff.support.card=n+1 := le_antisymm (hK _ hs) hlow
  exact ⟨⟨p.coeff.support,hs,hcard⟩,hp ▸ probability_mem_own_sourceInterior p⟩

attribute [local instance] OAI.BassTrace.Sparse.instMeasurableSpaceFinsuppReal_solutions
local instance instBorelSpaceFinsuppReal_solutions : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma count_chart_image {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (E : Set (Y →₀ ℝ)) (hE : ∀ p∈E,p.support⊆s) :
    Measure.count (simplexCoordinates s hs '' E)=Measure.count E := by
  have he : simplexEmbed s hs '' (simplexCoordinates s hs '' E)=E := by
    ext p
    constructor
    · rintro ⟨q,⟨v,hv,rfl⟩,rfl⟩
      rwa [simplexEmbed_coordinates s hs (hE v hv)]
    · intro hp
      exact ⟨simplexCoordinates s hs p,⟨p,hp,rfl⟩,simplexEmbed_coordinates s hs (hE p hp)⟩
  rw [← Measure.count_injective_image (simplexEmbed_injective s hs),he]

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

local instance instCountableSourceTop_5 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMeasurableSpaceFinsuppReal_solutions_1
local instance instBorelSpaceFinsuppReal_solutions_1_re6a042_1 : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
include hK in
lemma zero_count_ball_le (x : X) (c : FinProbability Y) (b : ℝ) :
    Measure.count ((Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c v≤b})≤
      ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c b x := by
  have hd : ∀ s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨τ,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hh : (Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c v≤b}⊆
      ⋃ σ : SourceTop K n,(Q.pair 0).P.val x∩
        (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b}) := by
    rintro v ⟨hv,hb⟩
    obtain ⟨σ,hσ⟩ := zero_mem_sourceTop_interior Q hd x hv
    exact Set.mem_iUnion.mpr ⟨σ,hv,hσ,hb⟩
  calc
    _ ≤ _ := measure_mono hh
    _ ≤ ∑' σ : SourceTop K n,Measure.count ((Q.pair 0).P.val x∩
        (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b})) := measure_iUnion_le _
    _ = _ := by
      unfold ballIntegrand
      apply tsum_congr
      intro σ
      rw [localOriginalArea_zero_eq_count Γ hK,count_chart_image]
      exact fun p hp=>support_of_mem_sourceInterior _ hp.2.1

end

section

variable {Y : Type*} [DecidableEq Y]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected) (hn : 0<n)

include hn in
lemma exists_finite_simplex_ball_cover (σ : SourceTop K n) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset (FinProbability Y),
      (∀ c∈C,c.coeff.support⊆σ.val) ∧
      ∀ v∈convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)),
        ∃ c∈C,centerDistance Γ hΓ K n c v ≤ r := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let S : Set (FinProbability Y) := {p | p.coeff.support⊆σ.val}
  have hSc : IsCompact S := isCompact_probability_simplex σ.val n hn (graphMetric_discrete Γ hΓ)
  have hcover : S⊆⋃ p∈S,Metric.ball p r := by
    intro p hp
    exact Set.mem_iUnion₂.mpr ⟨p,hp,Metric.mem_ball_self hr⟩
  obtain ⟨T,hTS,hT,hcoverT⟩ := hSc.elim_finite_subcover_image
    (fun _ _=>Metric.isOpen_ball) hcover
  refine ⟨hT.toFinset,fun c hc=>hTS (hT.mem_toFinset.mp hc),?_⟩
  intro v hv
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      ⟨σ.val,σ.property.1,rfl⟩ hv
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hps : p.coeff.support⊆σ.val := by
    have hh := hv
    rw [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet,← hp] at hh
    exact hh.2.2
  obtain ⟨c,hc,hpc⟩ := Set.mem_iUnion₂.mp (hcoverT hps)
  refine ⟨c,hT.mem_toFinset.mpr hc,?_⟩
  rw [← hp,centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩)]
  exact (FinProbability.rho_comm n p c) ▸ hpc.le

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_5
local instance instCountableSourceTop_6_re6a042_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMeasurableSpaceFinsuppReal_solutions_2
local instance instBorelSpaceFinsuppReal_solutions_2_re6a042_1 : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
include hi hn hK hΓaut in
lemma expected_zero_count_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hlarge : volumeThreshold D≤n) (σ : SourceTop K n) :
    ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2)
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (∫⁻ x,Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))) ∂μ).toReal≤C*ε := by
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hRp : 0<4*(D : ℝ)^2 := by positivity
  have hrp : 0<2*(D : ℝ)^2 := by positivity
  have hrR : 2*(D : ℝ)^2≤4*(D : ℝ)^2 := by nlinarith [sq_nonneg (D : ℝ)]
  obtain ⟨T,hT,hcover⟩ := exists_finite_simplex_ball_cover Γ hΓ hn σ hrp
  have hc : ∀ c∈T,c.coeff.support.card≤n+1 := fun c hc=>
    (Finset.card_le_card (hT c hc)).trans_eq σ.property.2
  have hh : ∀ c : T,∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2)
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal≤C*ε :=
    fun c=>global_zero_ball_mass_bound_tf Γ hΓ hΓaut hi hn hK μ hμ hRp c.val
      (hc c.val c.property) _ hrp.le hrR D hD hdeg (ballVolume_strict_margin D n hD hlarge)
  choose C hC hbound using hh
  refine ⟨∑ c : T,C c,Finset.sum_nonneg (fun c _=>hC c),?_⟩
  intro ε hε Q hmin
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hf c : ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c (2*(D : ℝ)^2)<⊤ :=
    ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ univ 0 hdim c _ hrp.le
  have hp x : Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))≤
      ∑ c : T,ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c.val (2*(D : ℝ)^2) x := by
    have hsub : (Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))⊆
        ⋃ c : T,(Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c.val v≤2*(D : ℝ)^2} := by
      rintro v ⟨hv,hs⟩
      obtain ⟨c,hc,hcv⟩ := hcover v hs
      exact Set.mem_iUnion.mpr ⟨⟨c,hc⟩,hv,hcv⟩
    exact (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun c _=>zero_count_ball_le Γ hΓ hK Q x c.val _))
  have hint : (∫⁻ x,Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))) ∂μ)≤
      ∑ c : T,ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2) := by
    apply (lintegral_mono hp).trans_eq
    rw [lintegral_finsetSum _ (fun c _=>(ballIntegrand_locallyConstant Γ hΓ hn hK
      (Q.pair 0) 0 c.val _ hrp.le).continuous.measurable)]
    apply Finset.sum_congr rfl
    intro c _
    simp only [ballMass,Measure.restrict_univ,ballIntegrand]
  calc
    _ ≤ (∑ c : T,ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal :=
      ENNReal.toReal_mono (by simp [ne_of_lt (hf _)]) hint
    _ = ∑ c : T,(ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal :=
      ENNReal.toReal_sum (fun c _=>(hf c.val).ne)
    _ ≤ ∑ c : T,C c*ε := Finset.sum_le_sum fun c _=>hbound c ε hε Q hmin
    _ = (∑ c : T,C c)*ε := (Finset.sum_mul ..).symm

end Sparse.GraphGeometry

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_6
local instance instCountableSourceTop_7_re6a042_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMeasurableSpaceFinsuppReal_solutions_3
local instance instBorelSpaceFinsuppReal_solutions_3 : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

include hi hn hK hΓaut in

theorem exists_sparse_zero_strata (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hlarge : volumeThreshold D≤n)
    (F : Finset (Finset Y)) (hF : ∀ s∈F,s∈K.faces)
    (hrep : ∀ s∈K.faces,∃ h : H,∃ τ∈F,s=τ.map (MulAction.toPerm h).toEmbedding) :
    ∃ C : SourceTop K n → ℝ,(∀ σ,0≤C σ) ∧ ∀ ε : ℝ,0<ε →
      ∃ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      ∀ σ : SourceTop K n,
        (∫ x,(Measure.count ((Q.pair 0).P.val x∩
          convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε := by
  have hall := expected_zero_count_bound Γ hΓ hΓaut hi hn hK μ hμ D hD hdeg hlarge
  choose C hC hbound using hall
  refine ⟨C,hC,?_⟩
  intro ε hε
  let := graphMetric Γ hΓ
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hRp : 0<4*(D : ℝ)^2 := by positivity
  obtain ⟨Q,hQ⟩ := exists_normalized_nearMinimal Γ hΓ rfl hn K hK hact.out hi
    F hF hrep μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) hRp hε
  refine ⟨Q,?_⟩
  intro σ
  have hmeas : Measurable (fun x=>Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))) :=
    (((Q.pair 0).P.localConstancy_inter (simplexVertices σ.val) ⟨_,σ.property.1,rfl⟩
      _ subset_rfl).comp (fun A=>Measure.count A)).continuous.measurable
  have hd : ∀ s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨τ,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hfinite' x : Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))<⊤ :=
    Measure.count_apply_lt_top.mpr (zero_inter_simplex_finite Q hd σ x)
  rw [integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall hfinite')]
  exact hbound σ ε hε.le Q hQ

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ClosedPaths
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Paths

open scoped BigOperators

section

variable {G ι : Type*} [Group G] [Fintype ι]

omit [Group G] in
lemma entry_support_subset (e : GroupMatrix (G := G) (ι := ι)) (i j : ι) :
    (e i j).coeff.support ⊆ support e := by
  classical
  intro s hs
  simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i,j,hs⟩

lemma coefficient_mul (e f : GroupMatrix (G := G) (ι := ι)) (t : G) :
    coefficient (e*f) t = ∑ s ∈ support e, coefficient e s * coefficient f (s⁻¹*t) := by
  classical
  ext i j
  simp only [coefficient, Matrix.mul_apply, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Matrix.sum_apply, MonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_subset (entry_support_subset e i k)
  intro s _ hs
  rw [Finsupp.notMem_support_iff.mp hs, zero_mul]

lemma kernel_row_finite (e : GroupMatrix (G := G) (ι := ι)) (h : G) :
    Function.HasFiniteSupport (kernel e h) := by
  classical
  apply (support e).finite_toSet.image (fun s => h*s) |>.subset
  intro k hk
  refine ⟨h⁻¹*k, (mem_support e _).mpr hk, ?_⟩
  simp

lemma kernel_idempotent (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (h k : G) :
    (∑ s ∈ support e, kernel e h (h*s) * kernel e (h*s) k) = kernel e h k := by
  have hh := coefficient_mul e e (h⁻¹*k)
  rw [he] at hh
  simpa only [kernel, mul_inv_rev, inv_mul_cancel_left, mul_assoc] using hh.symm

lemma kernel_idempotent_finsum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (h k : G) :
    (∑ᶠ u, kernel e h u * kernel e u k) = kernel e h k := by
  classical
  have hs : Function.support (fun u => kernel e h u * kernel e u k) ⊆
      (fun s => h*s) '' (support e : Set G) := by
    intro u hu
    refine ⟨h⁻¹*u, (mem_support e _).mpr ?_, by simp⟩
    intro hz
    exact hu (by change coefficient e (h⁻¹*u) * _ = 0; rw [hz, zero_mul])
  rw [finsum_eq_finsetSum_of_support_subset (f := fun u : G => kernel e h u * kernel e u k) (s := (support e).image (fun s => h*s))
    (by simpa only [Finset.coe_image] using hs)]
  rw [Finset.sum_image (fun a _ b _ hab => mul_left_cancel hab)]
  exact kernel_idempotent e he h k

end

section

variable {G : Type*} [Group G]

lemma rotate_castSucc (n : ℕ) (i : Fin n) :
    finRotate (n+1) i.castSucc = i.succ := finRotate_of_lt i.isLt

lemma increment_twist (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    increment g n (twist g n h) = increment g n h ∘ finRotate (n+1) := by
  funext i
  cases n with
  | zero =>
    have hi : i = Fin.last 0 := Fin.ext (by omega)
    subst i
    simp only [Function.comp_apply,finRotate_last,increment_last,twist_last]
    have hz : (0 : Fin 1) = Fin.last 0 := rfl
    rw [hz,increment_last]
    simp [mul_assoc]
    exact twist_last g 0 h
  | succ n =>
    induction i using Fin.lastCases with
    | last =>
      simp only [increment_last,twist_last,Function.comp_apply,finRotate_last]
      have hz : (0 : Fin (n+1+1)) = (0 : Fin (n+1)).castSucc := rfl
      rw [hz,twist_castSucc,increment_castSucc]
      simp [mul_assoc]
    | cast i =>
      rw [increment_castSucc]
      simp only [Function.comp_apply,rotate_castSucc,twist_castSucc]
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.succ_last,twist_last,increment_last,mul_assoc]
      | cast i =>
        rw [← Fin.castSucc_succ,twist_castSucc,increment_castSucc]

variable {ι : Type*} [Fintype ι]

lemma weight_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : weight e g n (twist g n h) = weight e g n h := by
  classical
  simp only [weight,increment_twist,Function.comp_apply]
  rw [List.ofFn_succ',List.ofFn_succ]
  simp only [rotate_castSucc,finRotate_last,List.prod_concat,List.prod_cons]
  exact Matrix.trace_mul_comm _ _

end

variable {G ι : Type*} [Group G] [Fintype ι]

lemma weight_eq_prefix (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : weight e g n h =
      Matrix.trace (prefixProduct e h * kernel e (h (Fin.last n)) (g*h 0)) := by
  classical
  rw [weight,List.ofFn_succ',List.prod_concat]
  simp only [increment_castSucc,increment_last,prefixProduct,kernel,mul_assoc]

lemma prefixProduct_snoc (e : GroupMatrix (G := G) (ι := ι)) (n : ℕ)
    (h : Fin (n+1) → G) (u : G) :
    prefixProduct e (Fin.snoc h u) = prefixProduct e h * kernel e (h (Fin.last n)) u := by
  classical
  unfold prefixProduct
  rw [List.ofFn_succ',List.prod_concat]
  congr 1
  · congr 2
    funext i
    simp [← Fin.castSucc_succ]
  · simp

lemma weight_snoc (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) (u : G) : weight e g (n+1) (Fin.snoc h u) =
    Matrix.trace (prefixProduct e h *
      (kernel e (h (Fin.last n)) u * kernel e u (g*h 0))) := by
  classical
  rw [weight_eq_prefix,prefixProduct_snoc]
  have hz : (0 : Fin (n+1+1)) = (0 : Fin (n+1)).castSucc := rfl
  simp only [Fin.snoc_last,mul_assoc,hz,Fin.snoc_castSucc]

lemma weight_snoc_finsum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    (∑ᶠ u : G, weight e g (n+1) (Fin.snoc h u)) = weight e g n h := by
  classical
  let f : ScalarMatrix (ι := ι) →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap ι ℂ ℂ).comp (LinearMap.mulLeft ℂ (prefixProduct e h))
  have hs : Function.HasFiniteSupport (fun u =>
      kernel e (h (Fin.last n)) u * kernel e u (g*h 0)) := by
    apply (kernel_row_finite e (h (Fin.last n))).subset
    intro u hu hz
    apply hu
    dsimp only
    rw [hz,zero_mul]
  simp only [weight_snoc]
  rw [weight_eq_prefix]
  change (∑ᶠ u : G, f (kernel e (h (Fin.last n)) u * kernel e u (g*h 0))) = _
  rw [← map_finsum f hs,kernel_idempotent_finsum e he]
  rfl

end BassTrace.Paths

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_PathWeights
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Paths

open scoped BigOperators

section

lemma mapDomain_apply_of_fibre {A B C M : Type*} [AddCommMonoid M]
    (v : A →₀ M) (d : A → B) (b : B) (j : C → A)
    (hj : Function.Injective j) (hf : ∀ a, d a = b ↔ a ∈ Set.range j) :
    (v.mapDomain d) b = ∑ᶠ c : C, v (j c) := by
  classical
  have hs : Function.support (fun a => if d a = b then v a else 0) ⊆ (v.support : Set A) := by
    intro a ha
    by_contra hnot
    apply ha
    simp [Finsupp.notMem_support_iff.mp hnot]
  calc
    (v.mapDomain d) b = ∑ a ∈ v.support, if d a = b then v a else 0 := by
      simp [Finsupp.mapDomain,Finsupp.sum,Finsupp.single_apply,eq_comm]
    _ = ∑ᶠ a : A, if d a = b then v a else 0 :=
      (finsum_eq_finsetSum_of_support_subset _ hs).symm
    _ = ∑ᶠ a ∈ Set.range j, v a := by simp only [finsum_eq_if,← hf]
    _ = ∑ᶠ c : C, v (j c) := finsum_mem_range hj

variable {G : Type*} [Group G]

lemma insertOrbit_injective (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    Function.Injective (insertOrbit g n h) := by
  intro u v huv
  obtain ⟨c,hc⟩ := Quotient.exact huv
  have h0 := hc ((0 : Fin (n+1)).castSucc)
  simp only [Fin.snoc_castSucc] at h0
  have hc1 : (c:G) = 1 := mul_right_cancel (h0.trans (one_mul _).symm)
  have hl := hc (Fin.last (n+1))
  simpa only [Fin.snoc_last,hc1,one_mul] using hl

lemma deleteLast_fibre (g : G) (n : ℕ) (h : Fin (n+1) → G) (q : Orbit g (n+1)) :
    deleteLast g n q = Quotient.mk _ h ↔ q ∈ Set.range (insertOrbit g n h) := by
  constructor
  · induction q using Quotient.inductionOn with | _ k =>
      intro hq
      obtain ⟨c,hc⟩ := Quotient.exact hq
      refine ⟨c*k (Fin.last (n+1)), ?_⟩
      apply Eq.symm
      apply Quotient.sound
      refine ⟨c,fun i => ?_⟩
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa only [Fin.snoc_castSucc] using hc i
  · rintro ⟨u,rfl⟩
    exact deleteLast_insertOrbit g n h u

variable {ι : Type*} [Fintype ι]

lemma pathVector_deleteLast (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) :
    (pathVector e g (n+1)).mapDomain (deleteLast g n) = pathVector e g n := by
  classical
  ext q
  induction q using Quotient.inductionOn with | _ h =>
    rw [mapDomain_apply_of_fibre _ _ _ (insertOrbit g n h)
      (insertOrbit_injective g n h) (deleteLast_fibre g n h)]
    change (∑ᶠ u, weight e g (n+1) (Fin.snoc h u)) = weight e g n h
    exact weight_snoc_finsum e he g n h

end

section

variable {G ι : Type*} [Group G] [Fintype ι]

lemma totalWeight_succ (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g (n+1) = totalWeight e g n := by
  unfold totalWeight
  rw [← pathVector_deleteLast e he g n]
  exact (Finsupp.sum_mapDomain_index (h := fun (_ : Orbit g n) (z : ℂ) => z)
    (fun _ => rfl) (fun _ _ _ => rfl)).symm

lemma totalWeight_eq_zeroDegree (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g n = totalWeight e g 0 := by
  induction n with
  | zero => rfl
  | succ n hn => rw [totalWeight_succ e he,hn]

lemma zeroConjugate_mk (g h : G) :
    zeroConjugate g (Quotient.mk _ (fun _ => h)) = h⁻¹*g*h := by
  change increment g 0 (fun _ => h) (Fin.last 0) = _
  exact increment_last g 0 _

lemma zeroConjugate_injective (g : G) : Function.Injective (zeroConjugate g) := by
  intro a b hab
  apply orbitIncrement_injective g 0
  funext i
  have hi : i = (0 : Fin 1) := Fin.ext (by omega)
  subst i
  exact hab

lemma range_zeroConjugate (g : G) : Set.range (zeroConjugate g) = {s | IsConj s g} := by
  ext s
  constructor
  · rintro ⟨q,rfl⟩
    induction q using Quotient.inductionOn with | _ h =>
      change IsConj (increment g 0 h (Fin.last 0)) g
      rw [increment_last]
      apply isConj_iff.mpr
      refine ⟨h 0, ?_⟩
      have hl : Fin.last 0 = (0 : Fin 1) := rfl
      rw [hl]
      group
  · intro hs
    obtain ⟨h,hh⟩ := isConj_iff.mp hs
    refine ⟨Quotient.mk _ (fun _ => h), ?_⟩
    rw [zeroConjugate_mk,← hh]
    group

lemma orbitWeight_zeroDegree (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (q : Orbit g 0) : orbitWeight e g 0 q = Matrix.trace (coefficient e (zeroConjugate g q)) := by
  classical
  induction q using Quotient.inductionOn with | _ h =>
    change weight e g 0 h = _
    simp only [weight,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]
    rfl

lemma totalWeight_finsum (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    totalWeight e g n = ∑ᶠ q, orbitWeight e g n q := by
  classical
  exact (finsum_eq_finsetSum_of_support_subset _ (by
    intro q hq
    exact (Finsupp.mem_support_iff.mpr hq : q ∈ (pathVector e g n).support))).symm

lemma totalWeight_conjugacy (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g n =
    ∑ᶠ s ∈ {s : G | IsConj s g}, Matrix.trace (coefficient e s) := by
  rw [totalWeight_eq_zeroDegree e he,totalWeight_finsum]
  simp only [orbitWeight_zeroDegree]
  rw [← finsum_mem_range (f := fun s => Matrix.trace (coefficient e s)) (zeroConjugate_injective g),range_zeroConjugate]

end

variable {G : Type*} [Group G]

lemma orbitIncrement_twist (g : G) (n : ℕ) (q : Orbit g n) :
    orbitIncrement g n (orbitTwist g n q) = orbitIncrement g n q ∘ finRotate (n+1) := by
  induction q using Quotient.inductionOn with | _ h => exact increment_twist g n h

lemma orbitTwist_injective (g : G) (n : ℕ) : Function.Injective (orbitTwist g n) := by
  intro a b hab
  apply orbitIncrement_injective g n
  have he := congrArg (orbitIncrement g n) hab
  rw [orbitIncrement_twist,orbitIncrement_twist] at he
  funext i
  obtain ⟨j,rfl⟩ := (finRotate (n+1)).surjective i
  exact congrFun he j

lemma twist_surjective (g : G) (n : ℕ) : Function.Surjective (twist g n) := by
  intro h
  refine ⟨Fin.cons (α := fun _ => G) (g⁻¹*h (Fin.last n)) (fun i => h i.castSucc), ?_⟩
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

lemma orbitTwist_surjective (g : G) (n : ℕ) : Function.Surjective (orbitTwist g n) := by
  intro q
  induction q using Quotient.inductionOn with | _ h =>
    obtain ⟨k,rfl⟩ := twist_surjective g n h
    exact ⟨Quotient.mk _ k,rfl⟩

variable {ι : Type*} [Fintype ι]

lemma orbitWeight_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (q : Orbit g n) : orbitWeight e g n (orbitTwist g n q) = orbitWeight e g n q := by
  induction q using Quotient.inductionOn with | _ h => exact weight_twist e g n h

lemma pathVector_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    (pathVector e g n).mapDomain (orbitTwist g n) = pathVector e g n := by
  ext q
  obtain ⟨p,rfl⟩ := orbitTwist_surjective g n q
  rw [Finsupp.mapDomain_apply (orbitTwist_injective g n)]
  exact (orbitWeight_twist e g n p).symm

omit [Fintype ι] in
lemma delete_twist_tuple (g : G) (n : ℕ) (h : Fin (n+2) → G) (i : Fin (n+1)) :
    (fun j => twist g (n+1) h (i.castSucc.succAbove j)) =
      twist g n (fun j => h (i.succ.succAbove j)) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp only [Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i),twist_last,
      Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i)]
  | cast j =>
    rw [Fin.castSucc_succAbove_castSucc]
    simp only [twist_castSucc,Fin.succ_succAbove_succ]

omit [Fintype ι] in
lemma deleteEntry_zero (g : G) (n : ℕ) :
    deleteEntry g n 0 = deleteLast g n ∘ orbitTwist g (n+1) := by
  funext q
  induction q using Quotient.inductionOn with | _ h =>
    change Quotient.mk (pathSetoid g n) (fun j => h j.succ) =
      Quotient.mk (pathSetoid g n) (fun j => twist g (n+1) h j.castSucc)
    simp only [twist_castSucc]

omit [Fintype ι] in
lemma deleteEntry_castSucc_twist (g : G) (n : ℕ) (i : Fin (n+1)) :
    deleteEntry g n i.castSucc ∘ orbitTwist g (n+1) =
      orbitTwist g n ∘ deleteEntry g n i.succ := by
  funext q
  induction q using Quotient.inductionOn with | _ h =>
    change Quotient.mk (pathSetoid g n) (fun j => twist g (n+1) h (i.castSucc.succAbove j)) =
      Quotient.mk (pathSetoid g n) (twist g n (fun j => h (i.succ.succAbove j)))
    rw [delete_twist_tuple]

lemma pathVector_deleteEntry (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (i : Fin (n+2)) :
    (pathVector e g (n+1)).mapDomain (deleteEntry g n i) = pathVector e g n := by
  induction i using Fin.induction with
  | zero =>
    rw [deleteEntry_zero,Finsupp.mapDomain_comp,pathVector_twist,pathVector_deleteLast e he]
  | succ i hi =>
    apply Finsupp.mapDomain_injective (orbitTwist_injective g n)
    rw [← Finsupp.mapDomain_comp,← deleteEntry_castSucc_twist,Finsupp.mapDomain_comp,
      pathVector_twist,hi,pathVector_twist]

end BassTrace.Paths

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ExteriorDetector
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Exterior identities for the lift-independent Pfaffian detector. -/

namespace BassTrace.Detector

open scoped BigOperators

lemma insertCoordinate_topVolume {n : ℕ} (i : Fin (n+1)) :
    insertCoordinate i (topVolume n) = (-1 : ℂ)^i.val • topVolume (n+1) := by
  apply Subtype.ext
  simp only [insertCoordinate, LinearMap.comp_apply, multiplyVector_coe,
    exteriorMap_coe, topVolume, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, Submodule.coe_smul]
  have he : (coordinateMap i.succAbove) ∘ coordinate = fun j => coordinate (i.succAbove j) := by
    funext j
    exact coordinateMap_coordinate _ _
  rw [he]
  have hi : i.insertNth (coordinate i) (fun j => coordinate (i.succAbove j)) = coordinate := by
    exact Fin.insertNth_eq_iff.mpr ⟨rfl, rfl⟩
  have hh := (ExteriorAlgebra.ιMulti ℂ (n+1)).neg_one_pow_smul_map_insertNth i
    (coordinate i) (fun j => coordinate (i.succAbove j))
  rw [hi, ← Int.cast_smul_eq_zsmul ℂ] at hh
  simpa only [ExteriorAlgebra.ιMulti_succ_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.vecTail, Function.comp_def, Int.cast_pow, Int.cast_neg, Int.cast_one] using hh.symm

lemma topCoefficient_insertCoordinate {n : ℕ} (i : Fin (n+1))
    (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    topCoefficient (n+1) (insertCoordinate i x) = (-1 : ℂ)^i.val * topCoefficient n x := by
  conv_lhs => rw [top_scalar n x]
  rw [map_smul, insertCoordinate_topVolume, map_smul, map_smul, topCoefficient_topVolume]
  simp only [smul_eq_mul, one_mul, mul_comm]

end BassTrace.Detector

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_PfaffianDetector
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Detector

open scoped BigOperators

lemma rawTwoForm_map {I J : Type*} [Fintype I] (f : I → J) (B : I → I → ℂ) :
    ExteriorAlgebra.map (coordinateMap f) (rawTwoForm B) =
      ∑ i, ∑ j, B i j • (ExteriorAlgebra.ι ℂ (coordinate (f i)) *
        ExteriorAlgebra.ι ℂ (coordinate (f j))) := by
  simp only [rawTwoForm, map_sum, map_smul, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_coordinate]

lemma twoForm_row {n : ℕ} (B : Fin (n+1) → Fin (n+1) → ℂ)
    (hB : ∀ i j, B i j = -B j i) (i : Fin (n+1)) :
    twoForm B =
      ExteriorAlgebra.map (coordinateMap i.succAbove)
        (twoForm (fun k l => B (i.succAbove k) (i.succAbove l))) +
      ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinateVector (B i)) := by
  let a (k l : Fin (n+1)) : CoordinateAlgebra (Fin (n+1)) :=
    B k l • (ExteriorAlgebra.ι ℂ (coordinate k) * ExteriorAlgebra.ι ℂ (coordinate l))
  have ha (k l) : a k l = a l k := by
    dsimp only [a]
    rw [hB k l, ι_mul_ι_neg (coordinate k) (coordinate l), neg_smul, smul_neg, neg_neg]
  have hai : a i i = 0 := by simp only [a, ExteriorAlgebra.ι_sq_zero, smul_zero]
  have hsum : (∑ k, ∑ l, a k l) =
      (∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l)) +
        (∑ l, a i l) + (∑ l, a i l) := by
    rw [Fin.sum_univ_succAbove (fun k => ∑ l, a k l) i]
    have he : (∑ k : Fin n, ∑ l, a (i.succAbove k) l) =
        (∑ k : Fin n, a (i.succAbove k) i) +
          ∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l) := by
      simp_rw [Fin.sum_univ_succAbove (fun l => a (i.succAbove _) l) i]
      rw [Finset.sum_add_distrib]
    rw [he]
    have hr : (∑ k : Fin n, a (i.succAbove k) i) = ∑ l, a i l := by
      conv_rhs => rw [Fin.sum_univ_succAbove (a i) i, hai, zero_add]
      exact Finset.sum_congr rfl fun k _ => ha _ _
    rw [hr]
    abel
  have hrow : (∑ l, a i l) =
      ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinateVector (B i)) := by
    simp only [coordinateVector, map_sum, map_smul, Finset.mul_sum, mul_smul_comm, a]
  simp only [twoForm, map_smul, rawTwoForm_map]
  change (2 : ℂ)⁻¹ • (∑ k, ∑ l, a k l) = _
  rw [hsum, hrow]
  change (2 : ℂ)⁻¹ • (_ + _ + _) = (2 : ℂ)⁻¹ •
    (∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l)) + _
  module

lemma multiplyVector_pfaffian_minor (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (hB : ∀ i j, B i j = -B j i)
    (i : Fin (2*m+1)) :
    multiplyVector (2*m) (coordinate i) (pfaffianForm m B) =
      insertCoordinate i (pfaffianForm m (fun k l => B (i.succAbove k) (i.succAbove l))) := by
  apply Subtype.ext
  simp only [multiplyVector_coe, insertCoordinate, LinearMap.comp_apply, exteriorMap_coe,
    pfaffianForm, map_smul, map_pow]
  rw [twoForm_row B hB i, mul_smul_comm, mul_smul_comm]
  congr 1
  apply gauge_invariance
  have h := (exteriorPower.map 2 (coordinateMap i.succAbove)
    (⟨twoForm (fun k l => B (i.succAbove k) (i.succAbove l)), twoForm_mem _⟩ :
      ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m))))).property
  simpa only [exteriorMap_coe] using h

lemma detector_pfaffian_sum (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (hB : ∀ i j, B i j = -B j i) :
    detector m B = ∑ i : Fin (2*m+1), (-1 : ℂ)^i.val *
      pfaffian m (fun k l => B (i.succAbove k) (i.succAbove l)) := by
  have he : detectorForm m B = ∑ i : Fin (2*m+1),
      multiplyVector (2*m) (coordinate i) (pfaffianForm m B) := by
    apply Subtype.ext
    simp only [detectorForm, multiplyVector_coe, Submodule.coe_sum, coordinateVector,
      one_smul, map_sum, Finset.sum_mul]
  unfold detector
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [multiplyVector_pfaffian_minor m B hB i, topCoefficient_insertCoordinate]
  rfl

end Detector

/-! Alternating functions on vertex labels extend to oriented exterior chains. -/

/-! The augmented exterior chain complex and contraction on homogeneous exterior submodules. -/

namespace Detector

open scoped BigOperators

open scoped BigOperators

open Oriented ChainHomotopy

variable {Y : Type*} [LinearOrder Y]

lemma cocycle_eq_coboundary (m : ℕ) (β : Y → Y → ℂ)
    (hβ : ∀ y z, β y z = -β z y) :
    cocycle m β = (pfaffianAlt m β).lift.comp (d (2*m)) := by
  apply linearMap_ext_wedge
  intro v
  rw [cocycle_wedge, detector_pfaffian_sum m _ (fun i j => hβ (v i) (v j))]
  simp only [LinearMap.comp_apply, d_wedge, map_sum, map_smul,
    AltFunction.lift_wedge, smul_eq_mul]
  rfl

lemma cocycle_closed (m : ℕ) (β : Y → Y → ℂ)
    (hβ : ∀ y z, β y z = -β z y) (x : Degree Y (2*m+2)) :
    cocycle m β (d (2*m+1) x) = 0 := by
  rw [cocycle_eq_coboundary m β hβ, LinearMap.comp_apply, d_square, map_zero]

end Detector

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_RelativeExponents
attribute [-instance] _root_.OAI.BassTrace.Detector.vertexAction _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Relative exponents use orbit representatives internally, without assuming an equivariant section. -/

namespace RelativeExponents

lemma exists_affine_function {L P : Type*} [Group L] [MulAction L P]
    (χ : L → ℝ) (hχ : ∀ a b, χ (a*b) = χ a + χ b)
    (hstab : ∀ (a : L) (p : P), a • p = p → χ a = 0) :
    ∃ B : P → ℝ, ∀ (a : L) (p : P), B (a • p) = B p + χ a := by
  classical
  let q (p : P) : MulAction.orbitRel.Quotient L P := Quotient.mk _ p
  have ht (p : P) : ∃ a : L, a • (q p).out = p := by
    exact Quotient.exact (Quotient.out_eq (q p)).symm
  let t (p : P) : L := (ht p).choose
  have htp (p : P) : t p • (q p).out = p := (ht p).choose_spec
  have hq (a : L) (p : P) : q (a • p) = q p := Quotient.sound ⟨a, rfl⟩
  have h1 : χ 1 = 0 := by have hh := hχ 1 1; simpa using hh
  have hinv (a : L) : χ a⁻¹ = -χ a := by
    have hh := hχ a⁻¹ a
    rw [inv_mul_cancel, h1] at hh
    linarith
  refine ⟨fun p => χ (t p), ?_⟩
  intro a p
  have he : ((t (a • p))⁻¹ * (a * t p)) • (q p).out = (q p).out := by
    rw [mul_smul, mul_smul, htp]
    have hr := htp (a • p)
    rw [hq] at hr
    calc
      _ = (t (a • p))⁻¹ • (t (a • p) • (q p).out) := congrArg _ hr.symm
      _ = _ := inv_smul_smul _ _
  have hz := hstab _ _ he
  rw [hχ, hχ, hinv] at hz
  linarith

variable {G : Type*} [Group G]

lemma character_mul (g : G) (a b : Positions g) :
    character g (a*b) = character g a + character g b := by
  change (((Multiplicative.toAdd a.1.2 + Multiplicative.toAdd b.1.2 : ℤ) : ℝ) -
    ((Multiplicative.toAdd a.1.1 + Multiplicative.toAdd b.1.1 : ℤ) : ℝ)) = _
  simp only [character, Int.cast_add]
  ring

theorem exists_beta (g : G) (hg : ¬ IsOfFinOrder g) :
    ∃ β : G → G → ℝ,
      (∀ h k, β k h = -β h k) ∧
      (∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
        β (c*h) (c*k) = β h k) ∧
      (∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r) := by
  let : MulAction (Positions g) (G × G) := MulAction.compHom (G × G) (positionHom g)
  have hstab (a : Positions g) (p : G × G) (h : a • p = p) : character g a = 0 := by
    have hleft := congrArg Prod.fst h
    have hright := congrArg Prod.snd h
    change (g ^ Multiplicative.toAdd a.1.1 * a.2) * p.1 = p.1 at hleft
    change (g ^ Multiplicative.toAdd a.1.2 * a.2) * p.2 = p.2 at hright
    have hl : g ^ Multiplicative.toAdd a.1.1 * a.2 = 1 := by simpa only [mul_eq_right] using hleft
    have hr : g ^ Multiplicative.toAdd a.1.2 * a.2 = 1 := by simpa only [mul_eq_right] using hright
    have he : Multiplicative.toAdd a.1.1 = Multiplicative.toAdd a.1.2 :=
      injective_zpow_iff_not_isOfFinOrder.mpr hg (mul_right_cancel (hl.trans hr.symm))
    simp [character, he]
  obtain ⟨B, hB⟩ := exists_affine_function (character g) (character_mul g) hstab
  have hBc (c : Subgroup.centralizer ({g} : Set G)) (h k : G) :
      B (c*h,c*k) = B (h,k) := by
    have he := hB ((1,1),c) (h,k)
    simpa [positionHom, MulAction.compHom_smul_def, character] using he
  have hBp (r s : ℤ) (h k : G) : B (g^r*h,g^s*k) = B (h,k) + s - r := by
    have he := hB ((Multiplicative.ofAdd r,Multiplicative.ofAdd s),1) (h,k)
    simpa [positionHom, MulAction.compHom_smul_def, character, sub_eq_add_neg, add_assoc] using he
  refine ⟨fun h k => (B (h,k) - B (k,h))/2, ?_, ?_, ?_⟩
  · intro h k; ring
  · intro c h k; dsimp only; rw [hBc, hBc]
  · intro r s h k; dsimp only; rw [hBp, hBp]; ring

end RelativeExponents

namespace Detector

section

open scoped BigOperators

open Oriented ChainHomotopy

variable {G : Type*} [Group G]

lemma exists_complex_beta (g : G) (hg : ¬ IsOfFinOrder g) :
    ∃ β : G → G → ℂ,
      (∀ h k, β h k = -β k h) ∧
      (∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
        β (c*h) (c*k) = β h k) ∧
      (∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r) := by
  obtain ⟨β, hβ, hc, hl⟩ := RelativeExponents.exists_beta g hg
  refine ⟨fun h k => (β h k : ℂ), ?_, ?_, ?_⟩
  · intro h k
    simpa only [Complex.ofReal_neg] using congrArg Complex.ofReal (hβ k h)
  · intro c h k
    exact congrArg Complex.ofReal (hc c h k)
  · intro r s h k
    simp only [hl, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_intCast]

end

section

open Oriented ChainHomotopy

variable {G : Type*} [Group G]

lemma cosetCocycle_lifts (g : G) (m : ℕ) (β : G → G → ℂ)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (h : Fin (2*m+1) → G) :
    cosetCocycle g m β (wedge (2*m+1) (project g ∘ h)) =
      detector m (fun i j => β (h i) (h j)) := by
  rw [cosetCocycle_wedge]
  exact detector_section g β hl m h

lemma cosetCocycle_closed (g : G) (m : ℕ) (β : G → G → ℂ)
    (hβ : ∀ y z, β y z = -β z y)
    (x : Degree (Vertex g) (2*m+2)) :
    cosetCocycle g m β (d (2*m+1) x) = 0 := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  unfold cosetCocycle
  exact cocycle_closed m _ (fun y z => hβ _ _) x

end

open scoped BigOperators

lemma square_decomposable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (u v : M) :
    (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
  rw [mul_assoc, ← mul_assoc (ExteriorAlgebra.ι R v), ι_mul_ι_neg v u,
    neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
    zero_mul, zero_mul, neg_zero]

lemma nilpotent_binomial {A : Type*} [Ring A] (b c : A) (hc : Commute c b)
    (hz : c*c = 0) (m : ℕ) :
    (b+c)^(m+1) = b^(m+1) + (m+1) • (c*b^m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlast : c*b^m*c = 0 := by
      rw [(hc.pow_right m).eq, mul_assoc, hz, mul_zero]
    calc
      (b+c)^(m+1+1) = (b^(m+1)+(m+1) • (c*b^m)) * (b+c) := by
        rw [pow_succ, ih]
      _ = b^(m+1+1) + c*b^(m+1) + (m+1) • (c*b^(m+1)) := by
        rw [add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, hlast,
          nsmul_zero, add_zero, ← pow_succ, (hc.pow_right (m+1)).eq.symm]
        simp only [mul_assoc, ← pow_succ]
      _ = b^(m+1+1) + (m+1+1) • (c*b^(m+1)) := by
        simp only [add_nsmul, one_nsmul]
        abel

lemma factorial_cancel (m : ℕ) :
    ((m+1).factorial : ℂ)⁻¹ * (m+1 : ℂ) = (m.factorial : ℂ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
  field_simp

lemma normalized_decomposable_update {I : Type*} (b : CoordinateAlgebra I)
    (hb : b ∈ ⋀[ℂ]^2 (CoordinateSpace I)) (u v : CoordinateSpace I) (m : ℕ) :
    ((m+1).factorial : ℂ)⁻¹ • (b+ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v)^(m+1) =
      ((m+1).factorial : ℂ)⁻¹ • b^(m+1) +
        (m.factorial : ℂ)⁻¹ • (ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v*b^m) := by
  have hc : Commute (ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v) b :=
    (ι_commute_degree_two u hb).mul_left (ι_commute_degree_two v hb)
  rw [nilpotent_binomial _ _ hc (square_decomposable u v), smul_add,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [factorial_cancel]

lemma coordinateVector_minor {n : ℕ} (i : Fin (n+1)) :
    coordinateVector (fun _ : Fin (n+1) => (1 : ℂ)) = coordinate i +
      coordinateMap i.succAbove (coordinateVector (fun _ : Fin n => (1 : ℂ))) := by
  simp only [coordinateVector, one_smul, map_sum, coordinateMap_coordinate]
  exact Fin.sum_univ_succAbove coordinate i

lemma coordinateVector_indicator {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    coordinateVector (fun j => if j = i then (1 : ℂ) else 0) = coordinate i := by
  simp [coordinateVector, ite_smul]

lemma pfaffianForm_lift_basis (m : ℕ)
    (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ)
    (hB : ∀ k l, B k l = -B l k) (i : Fin (2*m+1+1)) :
    pfaffianForm (m+1) (fun k l => B k l + (if l = i then 1 else 0) -
      (if k = i then 1 else 0)) =
      pfaffianForm (m+1) B - insertCoordinate i
        (detectorForm m (fun k l => B (i.succAbove k) (i.succAbove l))) := by
  classical
  apply Subtype.ext
  let b := twoForm (fun k l => B (i.succAbove k) (i.succAbove l))
  let u := coordinateVector (fun _ : Fin (2*m+1+1) => (1 : ℂ))
  let u' := coordinateVector (fun _ : Fin (2*m+1) => (1 : ℂ))
  have hm : ExteriorAlgebra.map (coordinateMap i.succAbove) b ∈
      ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m+1+1))) := by
    have h := (exteriorPower.map 2 (coordinateMap i.succAbove)
      (⟨b, twoForm_mem _⟩ : ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m+1))))).property
    simpa only [exteriorMap_coe] using h
  have hc : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) =
      -(ExteriorAlgebra.ι ℂ (coordinate i) *
        ExteriorAlgebra.ι ℂ (coordinateMap i.succAbove u')) := by
    rw [ι_mul_ι_neg, show u = coordinate i + coordinateMap i.succAbove u' from
      coordinateVector_minor i, map_add, mul_add, ExteriorAlgebra.ι_sq_zero, zero_add]
  have hcorr : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) * (twoForm B)^m =
      -(ExteriorAlgebra.ι ℂ (coordinate i) *
        (ExteriorAlgebra.ι ℂ (coordinateMap i.succAbove u') *
          (ExteriorAlgebra.map (coordinateMap i.succAbove) b)^m)) := by
    rw [mul_assoc, twoForm_row B hB i, gauge_invariance _ _ hm,
      ← mul_assoc, hc, neg_mul, mul_assoc]
  simp only [pfaffianForm, Submodule.coe_sub, insertCoordinate, LinearMap.comp_apply,
    multiplyVector_coe, exteriorMap_coe, detectorForm, map_mul, map_smul, map_pow,
    ExteriorAlgebra.map_apply_ι]
  rw [twoForm_lift_change B (fun k => if k = i then 1 else 0), coordinateVector_indicator,
    normalized_decomposable_update _ (twoForm_mem B)]
  change _ + (m.factorial : ℂ)⁻¹ •
      (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) * (twoForm B)^m) = _
  rw [hcorr, smul_neg, sub_eq_add_neg]
  congr 1
  rw [mul_smul_comm, mul_smul_comm]

lemma pfaffian_lift_basis (m : ℕ)
    (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ)
    (hB : ∀ k l, B k l = -B l k) (i : Fin (2*m+1+1)) :
    pfaffian (m+1) (fun k l => B k l + (if l = i then 1 else 0) -
      (if k = i then 1 else 0)) =
      pfaffian (m+1) B - (-1 : ℂ)^i.val *
        detector m (fun k l => B (i.succAbove k) (i.succAbove l)) := by
  have he := congrArg (topCoefficient (2*(m+1))) (pfaffianForm_lift_basis m B hB i)
  rw [map_sub] at he
  change pfaffian (m+1) _ = pfaffian (m+1) B -
    topCoefficient (2*m+1+1) (insertCoordinate i
      (detectorForm m (fun k l => B (i.succAbove k) (i.succAbove l)))) at he
  rw [topCoefficient_insertCoordinate] at he
  exact he

end Detector

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TwistedPaths
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Detector

open scoped BigOperators

variable {G : Type*} [Group G]

lemma finRotate_castSucc {n : ℕ} (i : Fin n) : finRotate (n+1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

lemma twistedRotation_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    twistedRotation g n h i.castSucc = h i.succ := by
  simp [twistedRotation, Fin.castSucc_ne_last]

lemma twistedRotation_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twistedRotation g n h (Fin.last n) = g*h 0 := by
  simp [twistedRotation]

lemma complex_sign_odd (m : ℕ) : (-1 : ℂ)^(2*m+1) = -1 := by
  rw [pow_add, pow_mul]
  norm_num

lemma rotation_pfaffian (m : ℕ) (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ) :
    pfaffian (m+1) (fun i j => B (finRotate _ i) (finRotate _ j)) =
      -pfaffian (m+1) B := by
  refine (pfaffian_perm (m+1) B (finRotate (2*m+1+1))).trans ?_
  change Equiv.Perm.sign (finRotate (2*m+1+1)) • pfaffian (m+1) B = _
  rw [sign_finRotate]
  have he : 2*m+1+1-1 = 2*m+1 := by omega
  rw [he, pow_add, pow_mul]
  norm_num [Units.smul_def]

lemma twisted_pfaffian (g : G) (β : G → G → ℂ)
    (hβ : ∀ x y, β x y = -β y x)
    (hlift : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y + s - r)
    (m : ℕ) (h : Fin (2*m+1+1) → G) :
    pfaffian (m+1) (fun i j => β (twistedRotation g (2*m+1) h i)
        (twistedRotation g (2*m+1) h j)) =
      -pfaffian (m+1) (fun i j => β (h i) (h j)) +
        detector m (fun i j => β (h i.succ) (h j.succ)) := by
  classical
  let B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ :=
    fun i j => β (h (finRotate _ i)) (h (finRotate _ j))
  have he : (fun i j => β (twistedRotation g (2*m+1) h i)
      (twistedRotation g (2*m+1) h j)) =
      (fun i j => B i j + (if j = Fin.last (2*m+1) then 1 else 0) -
        (if i = Fin.last (2*m+1) then 1 else 0)) := by
    funext i j
    simp only [twistedRotation, hlift, B, Int.cast_ite, Int.cast_one, Int.cast_zero]
  change pfaffian (m+1) ((fun i j => β (twistedRotation g (2*m+1) h i)
    (twistedRotation g (2*m+1) h j)) : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ) = _
  rw [he]
  refine (pfaffian_lift_basis m B (fun i j => hβ _ _) (Fin.last (2*m+1))).trans ?_
  have hm : (fun i j => B ((Fin.last (2*m+1)).succAbove i)
      ((Fin.last (2*m+1)).succAbove j)) = (fun i j => β (h i.succ) (h j.succ)) := by
    simp only [B, Fin.succAbove_last, finRotate_castSucc]
  rw [hm, Fin.val_last, complex_sign_odd, neg_one_mul, sub_neg_eq_add]
  exact congrArg (fun z => z + _) (rotation_pfaffian m (fun i j => β (h i) (h j)))

end Detector

namespace Paths

open scoped BigOperators

lemma weightedSum_congr {A : Type*} (v : A →₀ ℂ) {f g : A → ℂ}
    (h : ∀ a, f a = g a) : weightedSum v f = weightedSum v g := by
  exact congrArg (weightedSum v) (funext h)

lemma weightedSum_add {A : Type*} (v : A →₀ ℂ) (f g : A → ℂ) :
    weightedSum v (fun a => f a+g a) = weightedSum v f+weightedSum v g := by
  simp only [weightedSum,Finsupp.sum,mul_add,Finset.sum_add_distrib]

lemma weightedSum_neg {A : Type*} (v : A →₀ ℂ) (f : A → ℂ) :
    weightedSum v (fun a => -f a) = -weightedSum v f := by
  simp only [weightedSum,Finsupp.sum,mul_neg,Finset.sum_neg_distrib]

lemma weightedSum_sum {A I : Type*} (v : A →₀ ℂ) (s : Finset I) (f : I → A → ℂ) :
    weightedSum v (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, weightedSum v (f i) := by
  simp only [weightedSum,Finsupp.sum,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma weightedSum_const_mul {A : Type*} (v : A →₀ ℂ) (c : ℂ) (f : A → ℂ) :
    weightedSum v (fun a => c*f a) = c*weightedSum v f := by
  simp only [weightedSum,Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma weightedSum_mapDomain {A B : Type*} (v : A →₀ ℂ) (f : A → B) (p : B → ℂ) :
    weightedSum (v.mapDomain f) p = weightedSum v (p ∘ f) := by
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

variable {G ι : Type*} [Group G] [Fintype ι]

lemma weightedSum_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (p : Orbit g n → ℂ) :
    weightedSum (pathVector e g n) (p ∘ orbitTwist g n) = weightedSum (pathVector e g n) p := by
  rw [← weightedSum_mapDomain,pathVector_twist]

lemma weightedSum_deleteEntry (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (i : Fin (n+2)) (p : Orbit g n → ℂ) :
    weightedSum (pathVector e g (n+1)) (p ∘ deleteEntry g n i) =
      weightedSum (pathVector e g n) p := by
  rw [← weightedSum_mapDomain,pathVector_deleteEntry e he]

end Paths

namespace Detector

open scoped BigOperators

open BassTrace.Paths

section

variable {G : Type*} [Group G]

lemma twist_eq_twistedRotation (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twist g n h = twistedRotation g n h := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [twist_last,twistedRotation_last]
  | cast i => simp only [twist_castSucc,twistedRotation_castSucc]

variable (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)

lemma orbitPfaffian_twist (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r)
    (m : ℕ) (q : Orbit g (2*m+1)) :
    orbitPfaffian g β hc m (orbitTwist g (2*m+1) q) =
      -orbitPfaffian g β hc m q +
        orbitDetector g β hc m (deleteEntry g (2*m) 0 q) := by
  induction q using Quotient.inductionOn with | _ h =>
    change pfaffian (m+1) (fun i j => β (twist g (2*m+1) h i) (twist g (2*m+1) h j)) = _
    rw [twist_eq_twistedRotation,twisted_pfaffian g β hβ hl]
    rfl

variable {ι : Type*} [Fintype ι]

lemma pfaffianSum_twist (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    2*pfaffianSum g β hc e (m+1) = detectorSum g β hc e m := by
  have ht := weightedSum_twist e g (2*m+1) (orbitPfaffian g β hc m)
  have hv : weightedSum (pathVector e g (2*m+1))
      ((orbitPfaffian g β hc m) ∘ orbitTwist g (2*m+1)) =
      -pfaffianSum g β hc e (m+1) + detectorSum g β hc e m := by
    simp only [Function.comp_def]
    rw [weightedSum_congr _ (fun q => orbitPfaffian_twist g β hc hβ hl m q),
      weightedSum_add,weightedSum_neg]
    change -pfaffianSum g β hc e (m+1) + weightedSum _
      (orbitDetector g β hc m ∘ deleteEntry g (2*m) 0) = _
    rw [weightedSum_deleteEntry e he]
    rfl
  change _ = pfaffianSum g β hc e (m+1) at ht
  rw [ht] at hv
  linear_combination hv

end

lemma pfaffian_zero (B : Fin (2*0) → Fin (2*0) → ℂ) : pfaffian 0 B = 1 := by
  have ht : (⟨((0 : ℕ).factorial : ℂ)⁻¹ • (twoForm B)^0,
      Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) 0)⟩ :
      ⋀[ℂ]^(2*0) (CoordinateSpace (Fin (2*0)))) = topVolume 0 := by
    apply Subtype.ext
    simp [topVolume]
  exact (congrArg (topCoefficient 0) ht).trans (topCoefficient_topVolume 0)

lemma detector_zero (B : Fin (2*0+1) → Fin (2*0+1) → ℂ)
    (hB : ∀ i j, B i j = -B j i) : detector 0 B = 1 := by
  rw [detector_pfaffian_sum 0 B hB]
  simp [pfaffian_zero]

lemma alternating_sum_odd (m : ℕ) : ∑ i : Fin (2*m+1), (-1:ℂ)^i.val = 1 := by
  induction m with
  | zero => simp
  | succ m hm =>
    change (∑ i : Fin (2*m+1+1+1), (-1:ℂ)^i.val) = 1
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,hm,pow_succ]
    ring

variable {G : Type*} [Group G] (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)

lemma orbitDetector_zero (hβ : ∀ x y, β x y = -β y x) (q : Orbit g 0) :
    orbitDetector g β hc 0 q = 1 := by
  induction q using Quotient.inductionOn with | _ h =>
    exact detector_zero _ (fun i j => hβ _ _)

lemma orbitDetector_succ (hβ : ∀ x y, β x y = -β y x) (m : ℕ)
    (q : Orbit g (2*(m+1))) : orbitDetector g β hc (m+1) q =
      ∑ i : Fin (2*(m+1)+1), (-1:ℂ)^i.val *
        orbitPfaffian g β hc m (deleteEntry g (2*m+1) i q) := by
  induction q using Quotient.inductionOn with | _ h =>
    exact detector_pfaffian_sum (m+1) _ (fun i j => hβ _ _)

variable {ι : Type*} [Fintype ι]

lemma detectorSum_eq_pfaffianSum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x) (m : ℕ) :
    detectorSum g β hc e m = pfaffianSum g β hc e m := by
  cases m with
  | zero =>
    unfold detectorSum
    rw [weightedSum_congr _ (orbitDetector_zero g β hc hβ)]
    simp only [weightedSum,mul_one,pfaffianSum,totalWeight]
  | succ m =>
    unfold detectorSum
    rw [weightedSum_congr _ (orbitDetector_succ g β hc hβ m),weightedSum_sum]
    simp only [weightedSum_const_mul]
    have hv (i : Fin (2*(m+1)+1)) : weightedSum (pathVector e g (2*(m+1)))
        (fun q => orbitPfaffian g β hc m (deleteEntry g (2*m+1) i q)) =
        pfaffianSum g β hc e (m+1) := by
      exact weightedSum_deleteEntry e he g (2*m+1) i (orbitPfaffian g β hc m)
    simp_rw [hv]
    rw [← Finset.sum_mul,alternating_sum_odd,one_mul]

lemma pfaffianSum_recurrence (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    2*pfaffianSum g β hc e (m+1) = pfaffianSum g β hc e m := by
  rw [pfaffianSum_twist g β hc e he hβ hl,detectorSum_eq_pfaffianSum g β hc e he hβ]

lemma pfaffianSum_value (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    pfaffianSum g β hc e m = (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  induction m with
  | zero => simp [pfaffianSum]
  | succ m hm =>
    have hr := pfaffianSum_recurrence g β hc e he hβ hl m
    rw [hm] at hr
    rw [pow_succ]
    linear_combination (1/2:ℂ)*hr

lemma detectorSum_value (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    detectorSum g β hc e m = (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  rw [detectorSum_eq_pfaffianSum g β hc e he hβ,pfaffianSum_value g β hc e he hβ hl]

end Detector

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_PathComplex
attribute [-instance] _root_.OAI.BassTrace.Detector.vertexAction _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.PathChains

section

open scoped BigOperators

open Oriented ChainHomotopy Paths Detector

variable {G : Type*} [Group G]

lemma projected_twist (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    project g ∘ twist g n h = (project g ∘ h) ∘ finRotate (n+1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply,twist_last,finRotate_last]
    apply (project_eq_iff g _ _).mpr
    exact ⟨-1,by simp [← mul_assoc]⟩
  · simp only [Function.comp_apply,twist_castSucc,rotate_castSucc]

lemma pathProjection_twist (g : G) (n : ℕ) (q : Orbit g n) :
    pathProjection g n (orbitTwist g n q) = (-1:ℂ)^n • pathProjection g n q := by
  induction q using Quotient.inductionOn with | _ h =>
    change quotientMap g (n+1) (wedge (n+1) (project g ∘ twist g n h)) = _
    rw [projected_twist,wedge_perm]
    simp [sign_finRotate,Units.smul_def,← Int.cast_smul_eq_zsmul ℂ]

variable {ι : Type*} [Fintype ι]

lemma pathChain_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    pathChain e g n = (-1:ℂ)^n • pathChain e g n := by
  have hv := congrArg (Finsupp.linearCombination ℂ (pathProjection g n))
    (pathVector_twist e g n)
  rw [Finsupp.linearCombination_apply,Finsupp.sum_mapDomain_index] at hv
  swap
  · intro q; simp
  swap
  · intro q a b; exact add_smul a b _
  simp only [pathProjection_twist] at hv
  simp_rw [smul_comm _ ((-1:ℂ)^n)] at hv
  have hh : (pathVector e g n).sum (fun a b =>
      (-1:ℂ)^n • (b • pathProjection g n a)) = (-1:ℂ)^n • pathChain e g n := by
    simp only [pathChain,Finsupp.linearCombination_apply,Finsupp.sum,Finset.smul_sum]
  rw [hh] at hv
  exact hv.symm

lemma pathChain_odd (e : GroupMatrix (G := G) (ι := ι)) (g : G) (m : ℕ) :
    pathChain e g (2*m+1) = 0 := by
  have ht := pathChain_twist e g (2*m+1)
  rw [complex_sign_odd m,neg_one_smul] at ht
  have hz : (2:ℂ) • pathChain e g (2*m+1) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp ht
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end

open scoped BigOperators

open Oriented ChainHomotopy Paths Detector

variable {G : Type*} [Group G]

lemma pathProjection_boundary (g : G) (n : ℕ) (q : Orbit g (n+1)) :
    quotientD g (n+1) (pathProjection g (n+1) q) =
      ∑ i : Fin (n+2), (-1:ℂ)^i.val • pathProjection g n (deleteEntry g n i q) := by
  induction q using Quotient.inductionOn with | _ h =>
    change quotientMap g (n+1) (d (n+1) (wedge (n+2) (project g ∘ h))) = _
    rw [d_wedge,map_sum]
    simp only [map_smul]
    rfl

variable {ι : Type*} [Fintype ι]

lemma pathChain_boundary (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : quotientD g (n+1) (pathChain e g (n+1)) =
      ∑ i : Fin (n+2), (-1:ℂ)^i.val • pathChain e g n := by
  classical
  unfold pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  simp only [Function.comp_apply,pathProjection_boundary,Finsupp.linearCombination_apply,Finsupp.sum]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [smul_comm _ ((-1:ℂ)^i.val)]
  have heq : (Finsupp.linearCombination ℂ ((pathProjection g n) ∘ deleteEntry g n i))
      (pathVector e g (n+1)) = (Finsupp.linearCombination ℂ (pathProjection g n))
      (pathVector e g n) := by
    rw [← Finsupp.linearCombination_mapDomain, pathVector_deleteEntry e he]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Function.comp_apply] at heq
  simpa only [Finset.smul_sum] using congrArg (fun x => (-1:ℂ)^i.val • x) heq

theorem pathChain_even_cycle (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (m : ℕ) : quotientD g (2*m+2) (pathChain e g (2*(m+1))) = 0 := by
  change quotientD g ((2*m+1)+1) (pathChain e g ((2*m+1)+1)) = 0
  rw [pathChain_boundary e he]
  simp only [pathChain_odd,smul_zero,Finset.sum_const_zero]

variable (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k+s-r)

lemma quotientCocycle_pathProjection (m : ℕ) (q : Orbit g (2*m)) :
    quotientCocycle g β hc hl m (pathProjection g (2*m) q) = orbitDetector g β hc m q := by
  induction q using Quotient.inductionOn with | _ h =>
    exact cosetCocycle_lifts g m β hl h

lemma quotientCocycle_pairing (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ h k, β h k = -β k h) (m : ℕ) :
    quotientCocycle g β hc hl m (pathChain e g (2*m)) =
      (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  unfold pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  simp only [Function.comp_apply,quotientCocycle_pathProjection,Finsupp.linearCombination_apply,smul_eq_mul]
  exact detectorSum_value g β hc e he hβ hl m

end BassTrace.PathChains

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CentralizerGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Detector

section

variable {G : Type*} [Group G]

lemma vertex_action_free (g : G) (a : ActingGroup g) (y : Vertex g)
    (ha : a • y = y) : a = 1 := by
  induction a using Quotient.inductionOn with | _ c =>
    induction y using Quotient.inductionOn with | _ h =>
      apply (QuotientGroup.eq_one_iff c).mpr
      change project g ((c:G)*h) = project g h at ha
      obtain ⟨r,hr⟩ := (project_eq_iff g _ _).mp ha
      have he : g^r*(c:G) = 1 := by
        apply mul_right_cancel (b := h)
        simpa only [mul_assoc,one_mul] using hr
      have hc : c = (generator g)^(-r) := by
        apply Subtype.ext
        change (c:G) = g^(-r)
        rw [zpow_neg]
        exact eq_inv_of_mul_eq_one_right he
      rw [hc]
      exact (cyclic g).zpow_mem (Subgroup.mem_zpowers _) _

lemma actingGroup_injective_orbit (g : G) (y : Vertex g) :
    Function.Injective (fun a : ActingGroup g => a • y) := by
  intro a b hab
  change a • y = b • y at hab
  have hh : (b⁻¹*a) • y = y := by rw [mul_smul,hab,inv_smul_smul]
  exact (inv_mul_eq_one.mp (vertex_action_free g _ y hh)).symm

end

open Set Finset

variable {G : Type*} [Group G]

lemma smul_rightMul (g : G) (a : ActingGroup g) (s : G) (y : Vertex g) :
    a • rightMul g s y = rightMul g s (a • y) := by
  induction a using Quotient.inductionOn with | _ c =>
    induction y using Quotient.inductionOn with | _ h =>
      change project g ((c:G)*(h*s)) = project g (((c:G)*h)*s)
      rw [mul_assoc]

lemma supportGraph_adj (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) (y z : Vertex g) :
    (supportGraph g S hS).Adj y z ↔ y ≠ z ∧ ∃ s ∈ S, rightMul g s y = z := Iff.rfl

lemma supportGraph_smul (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (a : ActingGroup g) (y z : Vertex g) :
    (supportGraph g S hS).Adj (a • y) (a • z) ↔ (supportGraph g S hS).Adj y z := by
  simp only [supportGraph_adj,Ne,smul_left_cancel_iff]
  constructor
  · rintro ⟨hne,s,hs,he⟩
    exact ⟨hne,s,hs,(MulAction.injective a) (by change a • rightMul g s y = a • z; rw [smul_rightMul]; exact he)⟩
  · rintro ⟨hne,s,hs,he⟩
    exact ⟨hne,s,hs,by rw [← smul_rightMul,he]⟩

open scoped BassTrace.Detector

lemma supportGraph_degree_le (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (y : Vertex g) : (supportGraph g S hS).degree y ≤ S.card := by
  classical
  calc (supportGraph g S hS).degree y = ((supportGraph g S hS).neighborFinset y).card := rfl
    _ ≤ (S.image (fun s => rightMul g s y)).card := Finset.card_le_card (by
      intro z hz
      obtain ⟨_,s,hs,rfl⟩ := (SimpleGraph.mem_neighborFinset _ _ _).mp hz
      exact Finset.mem_image_of_mem _ hs)
    _ ≤ S.card := Finset.card_image_le

lemma supportGraph_reachable_rightMul (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (s : G) (hs : s ∈ Subgroup.closure (S : Set G)) :
    ∀ y, (supportGraph g S hS).Reachable y (rightMul g s y) := by
  induction hs using Subgroup.closure_induction with
  | mem s hs =>
    intro y
    by_cases he : y = rightMul g s y
    · rw [← he]
    · exact (show (supportGraph g S hS).Adj y (rightMul g s y) from ⟨he,s,hs,rfl⟩).reachable
  | one => intro y; rw [rightMul_one]
  | mul a b ha hb ia ib =>
    intro y
    rw [rightMul_mul]
    exact (ia y).trans (ib (rightMul g a y))
  | inv a ha ia =>
    intro y
    have h := (ia (rightMul g a⁻¹ y)).symm
    simpa [← rightMul_mul] using h

lemma supportGraph_connected (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤) :
    (supportGraph g S hS).Connected := by
  have : Nonempty (Vertex g) := ⟨project g 1⟩
  refine ⟨?_⟩
  intro y z
  induction y using Quotient.inductionOn with | _ a =>
    induction z using Quotient.inductionOn with | _ b =>
      have h := supportGraph_reachable_rightMul g S hS (a⁻¹*b) (by rw [hgen]; trivial) (project g a)
      change (supportGraph g S hS).Reachable (project g a) (project g b)
      simpa [mul_assoc] using h

scoped instance vertexIsCancelSMul (g : G) : IsCancelSMul (ActingGroup g) (Vertex g) where
  left_cancel' a _ _ he := (MulAction.injective a) he
  right_cancel' _ _ x he := (actingGroup_injective_orbit g x) he

end BassTrace.Detector

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FreeParameters
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

noncomputable section

namespace BassTrace.FreeParameter

open Set MeasureTheory

open scoped Pointwise

universe u v

variable {H : Type u} [Group H] (S : Subgroup H)

variable {C : Type v} [Group C] (χ : S →* C)

lemma shift_not_fixed (a : S) (ha : χ a ≠ 1) (ω : Offsets S (C := C)) :
    shift S χ (a : H) ω ≠ ω := by
  intro h
  have he := congrArg (fun η => encode S χ η (a : H)) h
  rw [encode_shift, inv_mul_cancel] at he
  have hm := encode_mul S χ ω 1 a
  simp only [one_mul] at hm
  rw [hm] at he
  exact ha ((mul_left_cancel (a := encode S χ ω 1)) (by simpa using he.symm))

lemma continuous_shift [TopologicalSpace C] [ContinuousMul C] (h : H) :
    Continuous (shift S χ h) := by
  apply continuous_pi
  intro q
  exact (continuous_apply _).mul continuous_const

lemma measurable_shift [MeasurableSpace C] [MeasurableMul₂ C] (h : H) :
    Measurable (shift S χ h) := by
  apply Measurable.of_eval
  intro q
  exact (measurable_pi_apply _).mul measurable_const

section Probability

variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

lemma uniform_map_equiv (e : C ≃ C) :
    (uniform (C := C)).map e = uniform := by
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton c)]
  have he : e ⁻¹' {c} = {e.symm c} := by
    ext x
    exact e.eq_symm_apply.symm
  rw [he]
  change (PMF.uniformOfFintype C).toMeasure {e.symm c} =
    (PMF.uniformOfFintype C).toMeasure {c}
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

omit [MeasurableSingletonClass C] in
lemma reindex_measure (h : H) :
    (offsetMeasure S (C := C)).map (fun ω q => ω (h⁻¹ • q)) = offsetMeasure S := by
  have hr := Measure.infinitePi_map_piCongrLeft
    (fun _ : H ⧸ S => uniform (C := C)) (MulAction.toPerm (β := H ⧸ S) h)
  unfold offsetMeasure
  rw [← hr]
  congr 1
  funext ω q
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

lemma offsetMeasure_shift (h : H) :
    (offsetMeasure S (C := C)).map (shift S χ h) = offsetMeasure S := by
  let m : (H ⧸ S) → C := fun q => χ (residue S (h⁻¹ * q.out))
  have hm : ∀ q, Measurable (fun c : C => c * m q) :=
    fun _ => measurable_of_finite _
  have hp : (offsetMeasure S (C := C)).map (fun ω q => ω q * m q) =
      offsetMeasure S := by
    rw [offsetMeasure, Measure.infinitePi_map_pi _ hm]
    congr 1
    funext q
    exact uniform_map_equiv (Equiv.mulRight (m q))
  have hf : shift S χ h = (fun ω q => ω q * m q) ∘
      (fun ω q => ω (h⁻¹ • q)) := by
    funext ω q
    change ω (QuotientGroup.mk (h⁻¹ * q.out)) * _ = ω (h⁻¹ • q) * _
    rw [show (QuotientGroup.mk (h⁻¹ * q.out) : H ⧸ S) = h⁻¹ • q from
      MulAction.Quotient.mk_smul_out S h⁻¹ q]
  have hm' : Measurable (fun ω : Offsets S (C := C) => fun q => ω q * m q) :=
    Measurable.of_eval (fun q => (hm q).comp (measurable_pi_apply q))
  have hr' : Measurable (fun ω : Offsets S (C := C) => fun q => ω (h⁻¹ • q)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [hf, ← Measure.map_map hm' hr', reindex_measure, hp]

end Probability

attribute [instance] Character.group Character.finite

variable (H)

instance spaceContinuous : ContinuousConstSMul H (Space H) where
  continuous_const_smul h := by
    apply continuous_pi
    intro a
    exact (continuous_shift _ _ h).comp (continuous_apply a)

instance spaceFree : IsCancelSMul H (Space H) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro h ω he
  by_contra hn
  let a : {a : H // a ≠ 1} := ⟨h, hn⟩
  exact shift_not_fixed _ (character h hn).value
    ⟨h, Subgroup.mem_zpowers h⟩ (character h hn).detects (ω a) (congrFun he a)

lemma probability_preserving (h : H) :
    MeasurePreserving (fun ω : Space H => h • ω) (probability H) (probability H) := by
  have hm : ∀ a : {a : H // a ≠ 1},
      Measurable (shift (Subgroup.zpowers a.val) (character a.val a.property).value h) :=
    fun a => measurable_shift _ _ h
  refine ⟨Measurable.of_eval (fun a => (hm a).comp (measurable_pi_apply a)), ?_⟩
  change Measure.map (fun (ω : Space H) (a : {a : H // a ≠ 1}) =>
    shift _ (character a.val a.property).value h (ω a)) _ = _
  rw [probability, Measure.infinitePi_map_pi _ hm]
  congr 1
  funext a
  exact offsetMeasure_shift _ _ h

end BassTrace.FreeParameter

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FiniteGenerators
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace

section

open scoped Classical BigOperators

variable {G : Type*} [Group G]

omit [Group G] in
lemma trace_coeff {ι : Type*} [Fintype ι] (e : Paths.GroupMatrix (G := G) (ι := ι)) (s : G) :
    (Matrix.trace e).coeff s=Matrix.trace (Paths.coefficient e s) := by
  simp only [Matrix.trace,Matrix.diag,MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,Paths.coefficient]

lemma classCoefficient_eq_finsum (g : G) (a : MonoidAlgebra ℂ G) :
    classCoefficient g a=∑ᶠ s∈{s : G|IsConj s g},a.coeff s := by
  unfold classCoefficient
  simp only [Set.mem_ofPred_eq,finsum_eq_if]
  symm
  apply finsum_eq_sum_of_support_subset
  intro s hs
  by_contra h
  have hz := Finsupp.notMem_support_iff.mp h
  simp [hz] at hs

lemma totalWeight_eq_classCoefficient {ι : Type*} [Fintype ι]
    (e : Paths.GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (g : G) :
    Paths.totalWeight e g 0=classCoefficient g (Matrix.trace e) := by
  rw [Paths.totalWeight_conjugacy e he g 0,classCoefficient_eq_finsum]
  simp only [trace_coeff]

lemma sum_conjugacy_invariant_zero (a : MonoidAlgebra ℂ G) (P : G→Prop)
    (hinv : ∀h k,IsConj h k→(P h↔P k))
    (hz : ∀h,P h→classCoefficient h a=0) :
    a.coeff.sum (fun h z=>if P h then z else 0)=0 := by
  rw [Finsupp.sum]
  rw [←Finset.sum_fiberwise_of_maps_to (s := a.coeff.support)
      (t := a.coeff.support.image ConjClasses.mk)
      (fun i hi=>Finset.mem_image_of_mem _ hi)]
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hq
  by_cases hp : P h
  · have he : (∑i∈a.coeff.support with ConjClasses.mk i=ConjClasses.mk h,
        if P i then a.coeff i else 0)=classCoefficient h a := by
      rw [classCoefficient,Finsupp.sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [ConjClasses.mk_eq_mk_iff_isConj]
      by_cases hc : IsConj i h
      · simp only [hc,ite_eq_left,(hinv i h hc).mpr hp]
      · simp only [hc,ite_false, if_false]
    rw [he,hz h hp]
  · apply Finset.sum_eq_zero
    intro i hi
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp (Finset.mem_filter.mp hi).2
    simp only [(hinv i h hc).not.mpr hp,ite_false, if_false]

end

open scoped Classical BigOperators

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]

lemma exists_symmetric_generators [Group.FG G] (e : Paths.GroupMatrix (G := G) (ι := ι)) :
    ∃S : Finset G,(∀s∈S,s⁻¹∈S) ∧ Subgroup.closure (S : Set G)=⊤ ∧ Paths.support e⊆S := by
  obtain ⟨T,hT,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let U := hfin.toFinset ∪ Paths.support e
  let S := U ∪ U.image Inv.inv
  refine ⟨S,?_,?_,?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs|hs
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_union_left _ (by simpa only [inv_inv] using hu)
  · apply top_unique
    rw [←hT]
    apply Subgroup.closure_mono
    intro s hs
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (hfin.mem_toFinset.mpr hs))
  · intro s hs
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hs)

lemma restrictMatrix_map (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (hs : ∀s∈Paths.support e,s∈K) :
    (restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype)=e := by
  apply Matrix.ext
  intro i j
  apply MonoidAlgebra.mapDomain_comapDomain
  intro s hs'
  exact ⟨⟨s,hs s (Paths.entry_support_subset e i j hs')⟩,rfl⟩

lemma restrictMatrix_idempotent (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (he : e*e=e) (hs : ∀s∈Paths.support e,s∈K) :
    restrictMatrix K e * restrictMatrix K e=restrictMatrix K e := by
  have hi := MonoidAlgebra.mapDomain_injective (R := ℂ) (f := (K.subtype : K→G)) Subtype.val_injective
  have hh : (restrictMatrix K e * restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype)=
      (restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype) := by
    rw [Matrix.map_mul,restrictMatrix_map K e hs,he]
  apply Matrix.ext
  intro i j
  apply hi
  exact congrFun (congrFun hh i) j

lemma map_trace_restrict (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (hs : ∀s∈Paths.support e,s∈K) :
    MonoidAlgebra.mapDomainRingHom ℂ K.subtype (Matrix.trace (restrictMatrix K e))=Matrix.trace e := by
  simp only [Matrix.trace,Matrix.diag,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (congrFun (restrictMatrix_map K e hs) i) i

lemma classCoefficient_map_subgroup (K : Subgroup G) (a : MonoidAlgebra ℂ K) (g : G) :
    classCoefficient g (MonoidAlgebra.mapDomainRingHom ℂ K.subtype a)=
      a.coeff.sum (fun h z=>if IsConj (h : G) g then z else 0) := by
  unfold classCoefficient
  rw [MonoidAlgebra.mapDomainRingHom_apply,MonoidAlgebra.coeff_mapDomain]
  apply Finsupp.sum_mapDomain_index
  · intro h; simp
  · intro h z w; split_ifs <;> simp

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SubdivisionWeights
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

section

open Set Finset

open scoped Classical Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

lemma connected_smul (Γ : SimpleGraph Y)
    (ha : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
    (h : H) (t : Finset Y) (hc : (Γ.induce (t : Set Y)).Connected) :
    (Γ.induce (↑(h • t) : Set Y)).Connected := by
  let f : Γ.induce (t : Set Y) →g Γ.induce (↑(h • t) : Set Y) := {
    toFun := fun y=>⟨h•y.val,Finset.smul_mem_smul_finset (a := h) y.property⟩
    map_rel' := fun hy=>(ha h _ _).mpr hy }
  apply hc.map f
  intro y
  obtain ⟨z,hz,he⟩ := Finset.mem_smul_finset.mp y.property
  exact ⟨⟨z,hz⟩,Subtype.ext he⟩

lemma generatedComplex_pure (T : Finset (Finset Y)) (n : ℕ) (Γ : SimpleGraph Y)
    (ha : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
    (hT : ∀t∈T,t.card=n+1 ∧ (Γ.induce (t : Set Y)).Connected) :
    ∀s∈(generatedComplex (H := H) T).faces,∃σ∈(generatedComplex (H := H) T).faces,
      s⊆σ ∧ σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected := by
  intro s hs
  obtain ⟨hne,h,t,ht,hst⟩ := hs
  refine ⟨h•t,⟨hne.mono hst,h,t,ht,subset_rfl⟩,hst,?_,connected_smul Γ ha h t (hT t ht).2⟩
  simpa only [Finset.card_smul_finset] using (hT t ht).1

lemma generatedReps_mem (T : Finset (Finset Y)) {s : Finset Y}
    (hs : s∈generatedReps T) : s∈(generatedComplex (H := H) T).faces := by
  obtain ⟨hs,hne⟩ := Finset.mem_filter.mp hs
  obtain ⟨t,ht,hst⟩ := Finset.mem_biUnion.mp hs
  exact ⟨hne,1,t,ht,by simpa only [one_smul] using Finset.mem_powerset.mp hst⟩

lemma generatedReps_complete (T : Finset (Finset Y)) {s : Finset Y}
    (hs : s∈(generatedComplex (H := H) T).faces) :
    ∃h : H,∃t∈generatedReps T,s=t.map (MulAction.toPerm h).toEmbedding := by
  obtain ⟨hne,h,t,ht,hst⟩ := hs
  refine ⟨h,h⁻¹•s,?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_powerset.mpr ?_⟩,
      Finset.smul_finset_nonempty.mpr hne⟩
    have hh := Finset.smul_finset_subset_smul_finset (a := h⁻¹) hst
    simpa only [inv_smul_smul] using hh
  · rw [←smul_finset_eq_map,smul_inv_smul]

lemma generatedTop_finite (T : Finset (Finset Y)) (n : ℕ)
    (hT : ∀t∈T,t.card=n+1) :
    letI := sourceTopAction (generatedComplex (H := H) T) n (generatedComplex_invariant T)
    Finite (MulAction.orbitRel.Quotient H (SourceTop (generatedComplex (H := H) T) n)) := by
  let := sourceTopAction (generatedComplex (H := H) T) n (generatedComplex_invariant T)
  let f : T → MulAction.orbitRel.Quotient H (SourceTop (generatedComplex (H := H) T) n) :=
    fun t=>Quotient.mk _ ⟨t.val,generatedComplex_top_mem T t.property
      (Finset.card_pos.mp (by rw [hT t t.property]; omega)),hT t t.property⟩
  apply Finite.of_surjective f
  intro q
  induction q using Quotient.inductionOn with | _ σ =>
    obtain ⟨hne,h,t,ht,hst⟩ := σ.property.1
    have he : σ.val=h•t := Finset.eq_of_subset_of_card_le hst (by
      rw [Finset.card_smul_finset,hT t ht,σ.property.2])
    refine ⟨⟨t,ht⟩,Quotient.sound ?_⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨h⁻¹,Subtype.ext ?_⟩
    change h⁻¹ • σ.val=t
    rw [he,inv_smul_smul]

end

open Set Finset

open scoped BassTrace.Sparse Classical

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SparseChains
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.PathChains

section

open Set Finset Oriented ChainHomotopy Paths Detector Sparse BarycentricChains

open scoped Classical Pointwise BassTrace.Detector

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]

lemma tuple_connected {Y : Type*} (Γ : SimpleGraph Y) (n : ℕ) (v : Fin (n+1) → Y)
    (hstep : ∀i : Fin n,v i.castSucc=v i.succ ∨ Γ.Adj (v i.castSucc) (v i.succ)) :
    (Γ.induce (↑(Finset.univ.image v) : Set Y)).Connected := by
  let u (i : Fin (n+1)) : (↑(Finset.univ.image v) : Set Y) :=
    ⟨v i,Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  have hr (i : Fin (n+1)) : (Γ.induce (↑(Finset.univ.image v) : Set Y)).Reachable (u 0) (u i) := by
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ i hi =>
      apply hi.trans
      rcases hstep i with he|ha
      · have he' : u i.castSucc=u i.succ := Subtype.ext he
        rw [he']
      · exact (show (Γ.induce (↑(Finset.univ.image v) : Set Y)).Adj (u i.castSucc) (u i.succ) from ha).reachable
  have : Nonempty (↑(Finset.univ.image v) : Set Y) := ⟨u 0⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp x.property
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp y.property
  have hx : u i=x := Subtype.ext hi
  have hy : u j=y := Subtype.ext hj
  rw [←hx,←hy]
  exact (hr i).symm.trans (hr j)

lemma path_tuple_connected (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (heS : support e⊆S) (n : ℕ)
    (q : Orbit g n) (hq : q∈(pathVector e g n).support) :
    ((supportGraph g S hS).induce (↑(Finset.univ.image (project g ∘ q.out)) : Set (Vertex g))).Connected := by
  apply tuple_connected
  intro i
  by_cases he : project g (q.out i.castSucc)=project g (q.out i.succ)
  · exact Or.inl he
  · apply Or.inr
    refine ⟨he,increment g n q.out i.castSucc,heS ?_,?_⟩
    · apply weight_ne_zero_support e g n q.out
      have hw : orbitWeight e g n q ≠ 0 := Finsupp.mem_support_iff.mp hq
      rw [←Quotient.out_eq q] at hw
      exact hw
    · rw [increment_castSucc]
      change project g (q.out i.castSucc * ((q.out i.castSucc)⁻¹*q.out i.succ))=project g (q.out i.succ)
      rw [mul_inv_cancel_left]

lemma topPaths_card (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    {t : Finset (Vertex g)} (ht : t∈topPaths e g n) : t.card=n+1 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
  rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp hq).2,Finset.card_univ,Fintype.card_fin]

lemma pathSupport_pure (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (heS : support e⊆S) (n : ℕ) :
    ∀s∈(pathSupport e g n).faces,∃σ∈(pathSupport e g n).faces,s⊆σ ∧ σ.card=n+1 ∧
      ((supportGraph g S hS).induce (σ : Set (Vertex g))).Connected := by
  apply generatedComplex_pure
  · exact supportGraph_smul g S hS
  · intro t ht
    refine ⟨topPaths_card e g n ht,?_⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    exact path_tuple_connected e g S hS heS n q (Finset.mem_filter.mp hq).1

lemma liftPath_quotient (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    quotientMap g (n+1) (liftPath e g n)=pathChain e g n := by
  unfold liftPath pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  congr 2
  funext q
  change quotientMap g (n+1) (wedge (n+1) (project g ∘ q.out))=pathProjection g n q
  rw [←pathProjection_mk,Quotient.out_eq]

end

open Oriented ChainHomotopy Paths Detector Sparse BarycentricChains

open scoped Classical BassTrace.Detector

variable {G : Type*} [Group G]

lemma projection_path_relations (g : G) [LinearOrder (Vertex g)]
    (K : Complex (Vertex g)) (hK : K.IsInvariant (H := ActingGroup g)) (n : ℕ)
    (x : Degree (Vertex g) n) (hx : x∈relations g n) :
    K.projection n x∈K.relations hK n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c,z⟩,rfl⟩ := hx
    let h : ActingGroup g := QuotientGroup.mk c
    change K.projection n (relabel n (fun y=>h•y) z-z)∈K.relations hK n
    have hh : K.projection n (relabel n (fun y=>h•y) z-z)=
        (⟨relabel n (fun y=>h•y) (K.projection n z),K.relabel_mem hK n h (K.projection n z).property⟩ : K.chains n)-K.projection n z := by
      apply Subtype.ext
      simp only [map_sub,Submodule.coe_sub,K.projection_relabel hK]
    rw [hh]
    exact Submodule.subset_span ⟨(h,K.projection n z),rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

lemma internal_path_cycle {ι : Type*} [Fintype ι]
    (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (g : G) (m : ℕ)
    [LinearOrder (Vertex g)]
    (hInv : (augmentedComplex (pathSupport e g (2*(m+1)))).IsInvariant (H := ActingGroup g)) :
    (⟨d (2*(m+1)) (liftPath e g (2*(m+1))),
      (augmentedComplex (pathSupport e g (2*(m+1)))).d_mem _ (liftPath_mem e g _)⟩ :
      (augmentedComplex (pathSupport e g (2*(m+1)))).chains (2*(m+1)))∈
      (augmentedComplex (pathSupport e g (2*(m+1)))).relations hInv (2*(m+1)) := by
  let K := augmentedComplex (pathSupport e g (2*(m+1)))
  have hcycle : quotientD g (2*(m+1)) (pathChain e g (2*(m+1)))=0 := by
    convert pathChain_even_cycle e he g m using 1 <;> rfl
    all_goals try with_reducible_and_instances rfl
  have hz : quotientMap g (2*(m+1)) (d (2*(m+1)) (liftPath e g (2*(m+1))))=0 := by
    rw [←quotientD_mk,liftPath_quotient]
    exact hcycle
  have hx := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hp := projection_path_relations g K hInv (2*(m+1)) _ hx
  have hm := K.d_mem (2*(m+1)) (liftPath_mem e g _)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  apply Subtype.ext
  exact (K.projection_self _ hm).symm

end BassTrace.PathChains

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SparseBounds
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse.GraphGeometry

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

open Oriented ChainHomotopy

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [Countable Y] [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_7
local instance instCountableSourceTop_8_re6a042_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem sparse_vanishing (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hlarge : volumeThreshold D≤n)
    (F : Finset (Finset Y)) (hF : ∀ s∈F,s∈K.faces)
    (hrep : ∀ s∈K.faces,∃ h : H,∃ τ∈F,s=τ.map (MulAction.toPerm h).toEmbedding)
    (y₀ : Y) (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) c,ψ (relabel (n+1) (fun y=>h • y) c)=ψ c)
    (hψd : ∀c,ψ (d (n+1) c)=0)
    (c : (augmentedComplex K).chains (n+1))
    (hc : (⟨d n c,(augmentedComplex K).d_mem n c.property⟩ :
      (augmentedComplex K).chains n)∈(augmentedComplex K).relations (augmentedComplex_invariant (H := H)) n) :
    ψ c=0 := by
  obtain ⟨C,hC,hzero⟩ := exists_sparse_zero_strata Γ hΓ hΓaut hi hn hK μ hμ D hD hdeg hlarge F hF hrep
  exact vanishing_of_zero_strata_tf Γ hΓ hK hn (by positivity) y₀ μ
    (augmentedComplex_invariant (H := H)) hμ C hC hzero ψ hψ hψd c hc

end

open scoped Classical

lemma graphMetric_action_isometry {H Y : Type*} [Group H] [MulAction H Y]
    (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
    (hAut : ∀(h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v) (h : H) :
    @Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
      (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y) := by
  let _ := graphMetric Γ hΓ
  have hle (h : H) (u v : Y) : Γ.dist (h•u) (h•v)≤Γ.dist u v := by
    let f : Γ →g Γ := ⟨fun y=>h•y,fun ha=>(hAut h _ _).mpr ha⟩
    obtain ⟨p,hp⟩ := hΓ.exists_walk_length_eq_dist u v
    calc _ ≤ (p.map f).length := SimpleGraph.dist_le _
         _ = _ := by rw [SimpleGraph.Walk.length_map,hp]
  apply Isometry.of_dist_eq
  intro u v
  change (Γ.dist (h•u) (h•v) : ℝ)=(Γ.dist u v : ℝ)
  congr 1
  apply le_antisymm (hle h u v)
  simpa only [inv_smul_smul] using hle h⁻¹ (h•u) (h•v)

end BassTrace.Sparse.GraphGeometry

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MatrixVanishing
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.PathChains

open Set Finset Oriented ChainHomotopy Paths Detector Sparse BarycentricChains Sparse.GraphGeometry

open scoped Classical Pointwise BassTrace.Detector

variable {G : Type*} [Group G] [Countable G] {ι : Type*} [Fintype ι]

lemma totalWeight_zero_of_finite_generators
    (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (hgen : Subgroup.closure (S : Set G)=⊤)
    (heS : support e⊆S) (g : G) (hg : ¬IsOfFinOrder g) : totalWeight e g 0=0 := by
  let H := ActingGroup g
  let Y := Vertex g
  have : Countable Y := inferInstanceAs (Countable (Quotient (QuotientGroup.rightRel (Subgroup.zpowers g))))
  have : Countable H := inferInstanceAs (Countable (ActingGroup g))
  let _ : LinearOrder Y := linearOrderOfSTO WellOrderingRel
  let _ : LinearOrder (Y →₀ ℝ) := linearOrderOfSTO WellOrderingRel
  let D := max 2 S.card
  let M := volumeThreshold D
  let n := 2*(M+1)
  let K := pathSupport e g n
  let _ : Fact (∀(h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces) :=
    ⟨generatedComplex_invariant (topPaths e g n)⟩
  let act : MulAction H (SourceTop K n) := sourceTopAction K n (generatedComplex_invariant (topPaths e g n))
  let _ : Finite (MulAction.orbitRel.Quotient H (SourceTop K n)) :=
    by
      convert generatedTop_finite (H := H) (topPaths e g n) n (fun _ ht=>topPaths_card e g n ht) using 1
      all_goals try with_reducible_and_instances rfl
      congr 3
      dsimp only [act]
      congr 1
      exact Subsingleton.elim _ _
  let Γ := supportGraph g S hS
  have hΓ : Γ.Connected := supportGraph_connected g S hS hgen
  have hAut : ∀(h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v := supportGraph_smul g S hS
  have hK := pathSupport_pure e g S hS heS n
  obtain ⟨β,hβ,hβc,hβl⟩ := exists_complex_beta g hg
  let ψ := cosetCocycle g (M+1) β
  have hInv : (augmentedComplex K).IsInvariant (H := H) := augmentedComplex_invariant
  have hinv (h : H) (c : Degree Y (n+1)) : ψ (relabel (n+1) (fun y=>h•y) c)=ψ c := by
    induction h using Quotient.inductionOn with | _ h =>
      exact cosetCocycle_invariant g (M+1) β hβc hβl h c
  let c : (augmentedComplex K).chains (n+1) := ⟨liftPath e g n,liftPath_mem e g n⟩
  have hv : ψ c=0 := sparse_vanishing (H := H) (X := FreeParameter.Space H)
    Γ hΓ hAut (graphMetric_action_isometry Γ hΓ hAut)
    (by dsimp [n]; omega) hK (FreeParameter.probability H) (FreeParameter.probability_preserving H)
    D (le_max_left _ _) (fun v=>by simpa only [SimpleGraph.card_neighborSet_eq_degree] using
      (supportGraph_degree_le g S hS v).trans (le_max_right 2 _))
    (by dsimp [n,M]; omega)
    (generatedReps (topPaths e g n)) (fun _ hs=>generatedReps_mem _ hs)
    (fun _ hs=>generatedReps_complete _ hs) (project g 1) ψ hinv
    (cosetCocycle_closed g (M+1) β hβ) c (internal_path_cycle e he g M hInv)
  have hp : quotientCocycle g β hβc hβl (M+1) (pathChain e g (2*(M+1)))=0 := by
    rw [←liftPath_quotient]
    exact hv
  rw [quotientCocycle_pairing g β hβc hβl e he hβ (M+1)] at hp
  exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ (inv_ne_zero (by norm_num)))

end BassTrace.PathChains

namespace BassTrace

open scoped Classical BigOperators

lemma classCoefficient_zero_finitely_generated {G : Type*} [Group G] [Countable G] [Group.FG G]
    {ι : Type*} [Fintype ι] (e : Paths.GroupMatrix (G := G) (ι := ι))
    (he : e*e=e) (g : G) (hg : ¬IsOfFinOrder g) :
    classCoefficient g (Matrix.trace e)=0 := by
  obtain ⟨S,hS,hgen,heS⟩ := exists_symmetric_generators e
  rw [←totalWeight_eq_classCoefficient e he]
  exact PathChains.totalWeight_zero_of_finite_generators e he S hS hgen heS g hg

theorem bassTrace {G : Type*} [Group G] {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G))
    (he : e*e=e) (g : G) (hg : ¬IsOfFinOrder g) :
    idempotentTraceCoefficient e g=0 := by
  let K := Subgroup.closure (Paths.support e : Set G)
  have hs : ∀s∈Paths.support e,s∈K := fun _ hs=>Subgroup.subset_closure hs
  let _ : Group.FG K := Group.closure_finset_fg (Paths.support e)
  let _ : Countable K := by
    dsimp [K]
    rw [FreeGroup.closure_eq_range]
    exact (MonoidHom.rangeRestrict_surjective _).countable
  let a := Matrix.trace (restrictMatrix K e)
  change classCoefficient g (Matrix.trace e)=0
  rw [←map_trace_restrict K e hs,classCoefficient_map_subgroup]
  apply sum_conjugacy_invariant_zero a (fun h=>IsConj (h : G) g)
  · intro h k hc
    have hc' := K.subtype.map_isConj hc
    exact ⟨fun hh=>hc'.symm.trans hh,fun hk=>hc'.trans hk⟩
  · intro h hh
    apply classCoefficient_zero_finitely_generated (restrictMatrix K e)
      (restrictMatrix_idempotent K e he hs) h
    intro ho
    exact hg (hh.isOfFinOrder (K.subtype.isOfFinOrder ho))

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MatrixK0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.K0

section

open scoped Classical BigOperators

variable {G : Type*} [_root_.Group G]

lemma classTrace_apply (a : MonoidAlgebra ℂ G) (g : G) :
    classTrace a (ConjClasses.mk g)=classCoefficient g a := by
  unfold classTrace classCoefficient
  simp only [Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.single_apply,
    ConjClasses.mk_eq_mk_iff_isConj]

end

open scoped Classical

end BassTrace.K0

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TraceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical trace, augmentation rank and algebraic K₀. -/

open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass

variable {G : Type*} [Group G]

lemma augmentation_apply (a : MonoidAlgebra ℂ G) :
    augmentation a = a.coeff.sum (fun _ z => z) := by
  simp [augmentation, MonoidAlgebra.lift_apply]

lemma canonicalTrace_eq_classCoefficient (a : MonoidAlgebra ℂ G) :
    canonicalTrace a = BassTrace.classCoefficient 1 a := by
  simp [canonicalTrace, BassTrace.classCoefficient]

lemma matrixTrace_eq_classCoefficient {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) :
    matrixTrace e = BassTrace.classCoefficient 1 (Matrix.trace e) := by
  simp [matrixTrace, Matrix.trace, Matrix.diag, canonicalTrace_eq_classCoefficient]

lemma classTrace_sum (a : MonoidAlgebra ℂ G) :
    (BassTrace.K0.classTrace a).sum (fun _ z => z) = augmentation a := by
  rw [augmentation_apply]
  simp [BassTrace.K0.classTrace, Finsupp.sum_mapDomain_index]

/-- Bass support reduces to the identity conjugacy class in a torsion-free group. -/
lemma matrix_trace_eq_augmentation (hG : TorsionFree G) {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) (he : e * e = e) :
    matrixTrace e = augmentation (Matrix.trace e) := by
  let tr := BassTrace.K0.classTrace (Matrix.trace e)
  have htr (c : ConjClasses G) (hc : c ≠ ConjClasses.mk 1) : tr c = 0 := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    rw [BassTrace.K0.classTrace_apply]
    apply BassTrace.bassTrace e he g
    intro hg
    exact hc (congrArg ConjClasses.mk (hG g hg))
  rw [matrixTrace_eq_classCoefficient, ← BassTrace.K0.classTrace_apply,
    ← classTrace_sum]
  symm
  apply Finsupp.sum_eq_single (ConjClasses.mk (1 : G))
  · intro c _ hc
    exact htr c hc
  · simp

end TorsionFreeBass
end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TorsionFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Idempotent and trace consequences for torsion-free groups. -/

open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass

variable {G : Type*} [Group G]

/-- The scalar specialization of the identity-support trace formula. -/
lemma scalar_trace_eq_augmentation_tf_oai (hG : TorsionFree G)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) : canonicalTrace e = augmentation e := by
  let b : Matrix (Fin 1) (Fin 1) (MonoidAlgebra ℂ G) := fun _ _ => e
  have hb : b * b = b := by
    apply Matrix.ext
    intro i j
    change (∑ _ : Fin 1, e * e) = e
    simpa using he
  simpa [matrixTrace, Matrix.trace, Matrix.diag, b] using matrix_trace_eq_augmentation hG b hb

end TorsionFreeBass
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TorsionFreeBass.scalar_trace_eq_augmentation_tf_oai.{u_1} := @OAI.TorsionFreeBass.scalar_trace_eq_augmentation_tf_oai.{u_1}

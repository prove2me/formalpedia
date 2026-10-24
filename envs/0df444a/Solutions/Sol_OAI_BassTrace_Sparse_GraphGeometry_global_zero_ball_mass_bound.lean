-- Prove2me | solution 1 for OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:18:36.383025+00:00
-- url     : https://prove2.me/submissions/3faf68f3-83ca-4c3c-8791-3f37b0f690f4

import Mathlib
import Definitions.Def_OAIQWBAS002

section
-- module Solutions.OAIQW_BassTrace.LocalCuts
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
-- module Solutions.OAIQW_BassTrace.GeometricSubcomplexes
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
-- module Solutions.OAIQW_BassTrace.Subdivisions
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

end SubdivisionFamily

end

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.MarkedSubdivisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V}

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

lemma outerPatch_marked {S : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : IsMarked (d.onComplex S).globalComplex P) (A : Finset J) :
    IsMarked (d.onComplex S).globalComplex (d.outerPatch P A) := by
  have hh := hP.inter (IsMarked.iUnion (fun j : A => (d.onComplex S).globalComplex_marked_ge j))
  convert hh using 1
  ext x
  simp only [outerPatch,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iUnion,Subtype.exists]
  constructor
  · rintro ⟨hx,j,hj,hh⟩
    exact ⟨hx,j,hj,(LocalCutData.globalComplex_space (d.onComplex S)) ▸ hP.subset_space hx,hh⟩
  · rintro ⟨hx,j,hj,_,hh⟩
    exact ⟨hx,j,hj,hh⟩

end UniversalCuts

end

open Set Finset

open scoped Classical Topology

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.AffinePotentials
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
-- module Solutions.OAIQW_BassTrace.ProbabilityGeometry
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

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.GraphRealization
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
-- module Solutions.OAIQW_BassTrace.OrbitForms
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

lemma distance_ge_iff (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) (t : ℝ) :
    t ≤ FinProbability.rho n (h • c i) p ↔
      ∃ l : ↥(potentialVertices : Finset (S i → ℝ)),
        t ≤ OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff := by
  obtain ⟨l,he,hm⟩ := exists_maximizer S c n hi hc h i p hp
  exact ⟨fun hh => ⟨l,he ▸ hh⟩,fun ⟨l',hh⟩ => hh.trans (hm l')⟩

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
-- module Solutions.OAIQW_BassTrace.BallGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Finite-center selection from compactness of closed original simplices, without a
cocompactness assumption on the continuous ambient space. -/

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
-- module Solutions.OAIQW_BassTrace.SimplexVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Euclidean coordinate simplex volume from the volume of the ℓ¹ ball and sign symmetry. -/

namespace BassTrace.Sparse

open MeasureTheory Set

open scoped ENNReal

lemma measurableSet_standardSolidSimplex (n : ℕ) :
    MeasurableSet (standardSolidSimplex n) := by
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
  apply MeasurableSet.inter
  · simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (show MeasurableSet {x : Fin n → ℝ | 0 ≤ x i} from
        measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (by fun_prop) measurable_const

lemma signReflection_measurePreserving {n : ℕ} (ε : Fin n → Bool) :
    MeasurePreserving (signReflection ε) := by
  unfold signReflection
  apply volume_preserving_pi (f := fun i t => if ε i then t else -t)
  intro i
  cases h : ε i
  · simpa only [h, Bool.false_eq_true, ↓reduceIte] using
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  · simp only [↓reduceIte]
    exact MeasurePreserving.id (volume : Measure ℝ)

lemma measurableSet_signChamber {n : ℕ} (ε : Fin n → Bool) :
    MeasurableSet (signChamber ε) :=
  (signReflection_measurePreserving ε).measurable (measurableSet_standardSolidSimplex n)

lemma volume_signChamber {n : ℕ} (ε : Fin n → Bool) :
    volume (signChamber ε) = volume (standardSolidSimplex n) :=
  (signReflection_measurePreserving ε).measure_preimage
    (measurableSet_standardSolidSimplex n).nullMeasurableSet

lemma signChamber_mem_iff {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℝ) :
    x ∈ signChamber ε ↔
      (∀ i, if ε i then 0 ≤ x i else x i ≤ 0) ∧ x ∈ l1UnitPolytope n := by
  change ((∀ i, 0 ≤ if ε i then x i else -x i) ∧
    ∑ i, (if ε i then x i else -x i) ≤ 1) ↔ _
  have hcond : (∀ i, 0 ≤ if ε i then x i else -x i) ↔
      (∀ i, if ε i then 0 ≤ x i else x i ≤ 0) := by
    apply forall_congr'
    intro i
    cases ε i <;> simp
  rw [hcond]
  constructor
  · rintro ⟨h,hx⟩
    refine ⟨h,?_⟩
    change ∑ i, |x i| ≤ 1
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := h i
    cases he : ε i <;> simp only [he, ↓reduceIte] at hi ⊢
    · exact abs_of_nonpos hi
    · exact abs_of_nonneg hi
  · rintro ⟨h,hx⟩
    refine ⟨h,?_⟩
    change ∑ i, |x i| ≤ 1 at hx
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := h i
    cases he : ε i <;> simp only [he, ↓reduceIte] at hi ⊢
    · exact (abs_of_nonpos hi).symm
    · exact (abs_of_nonneg hi).symm

lemma union_signChamber (n : ℕ) :
    (⋃ ε : Fin n → Bool, signChamber ε) = l1UnitPolytope n := by
  classical
  ext x
  simp only [mem_iUnion,signChamber_mem_iff]
  constructor
  · rintro ⟨ε,_,hx⟩
    exact hx
  · intro hx
    refine ⟨fun i => decide (0 ≤ x i),?_,hx⟩
    intro i
    by_cases hi : 0 ≤ x i
    · simp [hi]
    · simp [hi, (not_le.mp hi).le]

lemma signChamber_aedisjoint {n : ℕ} :
    Pairwise (fun ε η : Fin n → Bool =>
      AEDisjoint (volume : Measure (Fin n → ℝ)) (signChamber ε) (signChamber η)) := by
  intro ε η hne
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
  change volume (signChamber ε ∩ signChamber η) = 0
  apply measure_mono_null (t := {x | x i = 0})
  · intro x hx
    have hε := ((signChamber_mem_iff ε x).mp hx.1).1 i
    have hη := ((signChamber_mem_iff η x).mp hx.2).1 i
    cases he : ε i <;> cases hh : η i <;> simp_all <;> linarith
  · exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i 0

lemma volume_l1UnitPolytope (n : ℕ) :
    volume (l1UnitPolytope n) = ENNReal.ofReal ((2 : ℝ)^n / n.factorial) := by
  cases n with
  | zero =>
    have he : l1UnitPolytope 0 = Set.univ := by ext x; simp [l1UnitPolytope]
    rw [he, Measure.volume_pi_eq_dirac (fun i : Fin 0 => Fin.elim0 i)]
    simp
  | succ n =>
    have h := volume_sum_rpow_le (Fin (n+1)) (p := 1) (by norm_num) 1
    norm_num only [div_one, Real.rpow_one, Fintype.card_fin, ENNReal.ofReal_one,
      one_pow,one_mul] at h
    rw [Real.Gamma_two, mul_one, Real.Gamma_nat_eq_factorial] at h
    exact h

theorem volume_standardSolidSimplex (n : ℕ) :
    volume (standardSolidSimplex n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  have hsum := measure_iUnion₀ (signChamber_aedisjoint (n := n))
    (fun ε => (measurableSet_signChamber ε).nullMeasurableSet)
  rw [union_signChamber, volume_l1UnitPolytope] at hsum
  simp only [volume_signChamber,tsum_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat] at hsum
  have hc : (2 : ℝ≥0∞)^n ≠ 0 := by positivity
  have hf : (2 : ℝ≥0∞)^n ≠ ⊤ := by finiteness
  apply (ENNReal.mul_right_inj hc hf).mp
  rw [← hsum]
  conv_rhs => rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.TreeDeterminants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An oriented incidence matrix of a tree, with its root row deleted, is unimodular,
independently of a planar structure or ordering of children. -/

namespace BassTrace.Sparse

section

open SimpleGraph

open MeasureTheory Set

theorem treeChart_measurePreserving {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : MeasurePreserving (Matrix.toLin' (realTreeIncidence Γ hΓ)) := by
  refine ⟨(Matrix.toLin' (realTreeIncidence Γ hΓ)).continuous_of_finiteDimensional.measurable,?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (realTreeIncidence_det_ne_zero Γ hΓ)]
  have hh := treeIncidence_abs_real_det Γ hΓ
  change |(realTreeIncidence Γ hΓ).det| = 1 at hh
  rw [abs_inv,hh,inv_one,ENNReal.ofReal_one,one_smul]

lemma treeGradient_norm_le_one {n : ℕ} (hn : 0 < n)
    (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ)
    (hℓ : ∀ u v, Γ.Adj u v → |ℓ u - ℓ v| ≤ 1) :
    ‖treeGradient Γ hΓ ℓ‖ ≤ 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, ((treeGradient Γ hΓ ℓ).ofLp i)^2 ≤ ∑ _i : Fin n, (1 : ℝ) / n := by
      apply Finset.sum_le_sum
      intro j _
      dsimp [treeGradient]
      rw [div_pow,Real.sq_sqrt hnR.le]
      apply div_le_div_of_nonneg_right _ hnR.le
      have hj := hℓ ((treeEdgeEquiv Γ hΓ j).val.out.1)
        ((treeEdgeEquiv Γ hΓ j).val.out.2)
        (by
          change s((treeEdgeEquiv Γ hΓ j).val.out.1,
            (treeEdgeEquiv Γ hΓ j).val.out.2) ∈ Γ.edgeSet
          have he : s((treeEdgeEquiv Γ hΓ j).val.out.1,
            (treeEdgeEquiv Γ hΓ j).val.out.2) = (treeEdgeEquiv Γ hΓ j).val :=
              (treeEdgeEquiv Γ hΓ j).val.out_eq
          rw [he]
          exact (treeEdgeEquiv Γ hΓ j).property)
      simpa only [sq_abs,one_pow] using
        (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hj
    _ = 1^2 := by simp [ne_of_gt hnR]

lemma rootCoordinate_potential {n : ℕ} (ℓ : Fin (n+1) → ℝ) (v : Fin (n+1)) :
    (∑ i, (ℓ i.succ - ℓ 0) * (rootCoordinate v i : ℝ)) = ℓ v - ℓ 0 := by
  induction v using Fin.cases with
  | zero => simp [rootCoordinate_zero]
  | succ v => simp [rootCoordinate_succ,Pi.single_apply]

lemma treeChart_potential {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ) (x : Fin n → ℝ) :
    (∑ i, (ℓ i.succ - ℓ 0) * ((Matrix.toLin' (realTreeIncidence Γ hΓ)) x) i) /
      Real.sqrt n =
    ∑ j, (treeGradient Γ hΓ ℓ).ofLp j * x j := by
  simp only [Matrix.toLin'_apply,Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [realTreeIncidence,Matrix.map_apply,treeIncidence,map_sub]
  have hcol (j : Fin n) :
      (∑ i, (ℓ i.succ - ℓ 0) *
        (((rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i : ℝ) -
          (rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i : ℝ)) * x j)) =
      (ℓ ((treeEdgeEquiv Γ hΓ j).val.out.1) -
        ℓ ((treeEdgeEquiv Γ hΓ j).val.out.2)) * x j := by
    simp only [← mul_assoc,← Finset.sum_mul,mul_sub,Finset.sum_sub_distrib,
      rootCoordinate_potential]
    ring
  change (∑ j, ∑ i, (ℓ i.succ - ℓ 0) *
    (((rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i : ℝ) -
      (rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i : ℝ)) * x j)) /
        Real.sqrt n = _
  simp_rw [hcol]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [treeGradient]
  ring

lemma treeSolidSimplex_volume {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : volume (treeSolidSimplex Γ hΓ) =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  rw [treeSolidSimplex, (treeChart_measurePreserving Γ hΓ).measure_preimage
    (measurableSet_standardSolidSimplex n).nullMeasurableSet,
    volume_standardSolidSimplex]

end

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

lemma barycentricParam_mem_simplex {n : ℕ} (x : Fin n → ℝ) :
    barycentricParam x ∈ fullBarycentricSimplex n ↔ x ∈ standardSolidSimplex n := by
  simp only [fullBarycentricSimplex,Set.mem_ofPred_eq,sum_barycentricParam,and_true]
  constructor
  · intro h
    exact ⟨fun i => h i.succ,by have hh := h 0; dsimp at hh; linarith⟩
  · rintro ⟨hx,hs⟩ i
    induction i using Fin.cases with
    | zero => change 0 ≤ 1-∑ i,x i; linarith
    | succ i => exact hx i

lemma treeArea_top_simplex {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    treeArea T hT n (fullBarycentricSimplex n) = ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  have he : (treeParam T hT) ⁻¹' fullBarycentricSimplex n =
      WithLp.ofLp ⁻¹' treeSolidSimplex T hT := by
    ext x
    exact barycentricParam_mem_simplex _
  rw [treeArea,he,EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  rw [(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage]
  · exact treeSolidSimplex_volume T hT
  · exact ((measurableSet_standardSolidSimplex n).preimage
      (Matrix.toLin' (realTreeIncidence T hT)).continuous_of_finiteDimensional.measurable).nullMeasurableSet

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

lemma simplexArea_mono {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (j : ℕ) {Q W : Set (Fin (n+1) → ℝ)} (h : Q ⊆ W) :
    simplexArea Γ j Q ≤ simplexArea Γ j W := by
  apply ENNReal.div_le_div_right
  exact Finset.sum_le_sum fun T _ => treeArea_mono T.val T.property.2 j h

lemma simplexArea_top_simplex {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected) :
    simplexArea Γ n (fullBarycentricSimplex n) = ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  let := nonempty_spanningTree hΓ
  simp only [simplexArea,treeArea_top_simplex,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_comm]; exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)

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
-- module Solutions.OAIQW_BassTrace.TreeArea
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
-- module Solutions.OAIQW_BassTrace.MarkedArea
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

lemma sourceTop_stabilizer_finite {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ.val) := by
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [σ.property.2]; omega : 0<σ.val.card)
  let f : MulAction.stabilizer H σ.val → σ.val := fun h => ⟨h.val • v,by
    have hh := Finset.smul_mem_smul_finset (a := h.val) hv
    rw [h.property] at hh
    exact hh⟩
  apply Finite.of_injective f
  intro h k he
  apply Subtype.ext
  exact IsCancelSMul.right_cancel h.val k.val v (congrArg Subtype.val he)

omit [BorelSpace X] in
lemma normalizedArea_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (hd : ∀ x t, t ∈ (Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ Q.P.val x → t.card ≤ j+1) :
    normalizedArea Γ μ reps Q j < ∞ := by
  apply ENNReal.sum_lt_top.mpr
  intro σ hσ
  apply ENNReal.mul_lt_top
  · let := sourceTop_stabilizer_finite (H := H) σ
    apply ENNReal.inv_lt_top.mpr
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (MulAction.stabilizer H σ.val))
  · exact IsLocallyConstant.lintegral_lt_top (originalArea_locallyConstant Γ Q σ j)
      (fun x => originalArea_lt_top Γ Q σ (hΓ σ hσ) j x (hd x)) μ

omit [BorelSpace X] in
lemma normalizedArea_filtration_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces,s.card ≤ n+1) {j : ℕ} (hj : j ≤ n) :
    normalizedArea Γ μ reps (Q.pair j) j < ∞ := by
  apply normalizedArea_lt_top Γ μ reps hΓ
  intro x t ht htp
  apply (Q.point x).dimension_bound _ hj ht htp
  rintro _ ⟨s,hs,rfl⟩
  exact Finset.card_image_le.trans (hK s hs)

end

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.EquivariantSurgery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.OrbitForms

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X] [MeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] in
lemma step_dimension_bound
    (Q : SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces, s.card ≤ n+1) {j : ℕ} (hj : j<n)
    (A : EquivariantStep ρ R (Q.pair (j+1))) (x : X)
    {t : Finset (Y →₀ ℝ)} (ht : t ∈ (A.result.T.val x).complex.faces)
    (htZ : convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ A.result.P.val x) : t.card ≤ j+1 := by
  obtain ⟨S,hS⟩ := A.step.finer x
  obtain ⟨F,hF,hFP,htF⟩ := S.carrier_marked ((Q.pair (j+1)).P.marked x)
    (hS.symm ▸ ht) (htZ.trans (A.step.subset x))
  have hdrop := A.step.dimensionDrop x F hF hFP t ht (Set.subset_inter htF htZ)
  have hdim := (Q.point x).dimension_bound
    (fun _ hs => by
      obtain ⟨s,hs,rfl⟩ := hs
      exact Finset.card_image_le.trans (hK s hs)) (by omega : j+1 ≤ n) hF hFP
  omega

lemma normalizedArea_step_lt_top
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    (Q : SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces, s.card ≤ n+1) {j : ℕ} (hj : j<n)
    (A : EquivariantStep ρ R (Q.pair (j+1))) :
    normalizedArea Γ μ reps A.result j < ∞ := by
  apply normalizedArea_lt_top Γ μ reps hΓ
  intro x t ht htp
  exact step_dimension_bound Q hK hj A x ht htp

end Sparse.OrbitForms

namespace Sparse.Cuts

open Set Finset

section

variable {V X I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

omit [TopologicalSpace X] in

lemma Subdivision.marked_complement_of_patch (T : Subdivision K)
    (U P O : Set V) (hO : IsMarked T.complex O)
    (hOP : O = P \ U)
    (hpatch : ∀ s ∈ K.faces, (convexHull ℝ (s : Set V) ∩ U).Nonempty →
      convexHull ℝ (s : Set V) ⊆ P) :
    IsMarked T.complex (K.space \ U) := by
  intro p hp
  obtain ⟨s,hs,hps⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp.1
  by_cases hmeet : (convexHull ℝ (s : Set V) ∩ U).Nonempty
  · have hpO : p ∈ O := hOP ▸ ⟨hpatch s hs hmeet hps,hp.2⟩
    obtain ⟨f,hf,hpf,hfO⟩ := hO p hpO
    refine ⟨f,hf,hpf,fun q hq => ⟨?_,?_⟩⟩
    · exact T.space_eq ▸ T.complex.convexHull_subset_space hf hq
    · have h := hfO hq
      rw [hOP] at h
      exact h.2
  · obtain ⟨f,hf,hpf,hfs⟩ := T.marked hs p hps
    exact ⟨f,hf,hpf,fun q hq => ⟨K.convexHull_subset_space hs (hfs hq),
      fun hqU => hmeet ⟨q,hfs hq,hqU⟩⟩⟩

end

end Sparse.Cuts

namespace Sparse.BallOrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [MetricSpace Y] [Fintype C]

variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)

lemma outerPatch_mem (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i)
    (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) (p : FinProbability Y)
    {t : ℝ} (ht : 0<t) :
    p.coeff ∈ ((OrbitForms.cuts (H := H) (data S c n) ht).outerPatch
        (translatedPatch S K h i) (branches S h i)) ↔
      p.coeff ∈ translatedPatch S K h i ∧ t≤FinProbability.rho n (h • c i) p := by
  change (p.coeff ∈ translatedPatch S K h i ∧
    ∃ j ∈ branches S h i, t≤OrbitForms.form (data S c n) j p.coeff) ↔ _
  constructor
  · rintro ⟨hp,j,hj,hle⟩
    obtain ⟨l,rfl⟩ := (mem_branches S h i j).mp hj
    refine ⟨hp,(distance_ge_iff S c n hi hc h i p
      ((translatedPatch_mem S K h i p).mp hp).2 t).mpr ?_⟩
    exact ⟨l,hle⟩
  · rintro ⟨hp,hle⟩
    obtain ⟨l,hl⟩ := (distance_ge_iff S c n hi hc h i p
      ((translatedPatch_mem S K h i p).mp hp).2 t).mp hle
    exact ⟨hp,(h,⟨i,l⟩),(mem_branches S h i _).mpr ⟨l,rfl⟩,hl⟩

end Sparse.BallOrbitForms

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.BallReplacement
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

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [Fintype C]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi

omit [IsCancelSMul H Y] [Fintype C] in

lemma meeting_simplex_patch (c : C → FinProbability Y) (h : H) (i : C)
    {R t : ℝ} (hR : 0≤R) (htR : t≤R)
    (s : Finset Y) (hs : s∈K.faces)
    (hmeet : (convexHull ℝ ((fun y : Y => Finsupp.single y (1:ℝ)) '' (s : Set Y)) ∩
      {v | centerDistance Γ hΓ K n (h • c i) v<t}).Nonempty) :
    convexHull ℝ ((fun y : Y => Finsupp.single y (1:ℝ)) '' (s : Set Y)) ⊆
      BallOrbitForms.translatedPatch (fun i => ballSupport Γ (c i) n R) K h i := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  have hsp : convexHull ℝ ((fun y : Y => Finsupp.single y (1:ℝ)) '' (s : Set Y)) ⊆
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
    rw [← Finset.coe_image]
    exact (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space ⟨s,hs,rfl⟩
  obtain ⟨v,hvs,hvt⟩ := hmeet
  let p := pointProbability K ⟨v,hsp hvs⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hpS : p.coeff.support ⊆ s := by
    have hv := (convexHull_single_eq_probabilitySet s) ▸ hvs
    exact hp.symm ▸ hv.2.2
  have hpK := pointProbability_face K ⟨v,hsp hvs⟩
  have hball : FinProbability.rho n (h • c i) p≤R := by
    change centerDistance Γ hΓ K n (h • c i) v<t at hvt
    rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at hvt
    exact hvt.le.trans htR
  let s' := s.map (MulAction.toPerm h⁻¹).toEmbedding
  obtain ⟨σ,hσ,hsσ,hcard,hconn⟩ := hK s' (hact h⁻¹ s hs)
  have hp' : (h⁻¹ • p).coeff.support ⊆ σ := by
    rw [smul_probability_support]
    exact (Finset.map_subset_map.mpr hpS).trans hsσ
  have hball' : FinProbability.rho n (c i) (h⁻¹ • p)≤R := by
    have he := smul_probability_rho hi h⁻¹ n (h • c i) p
    rw [inv_smul_smul] at he
    exact he.symm ▸ hball
  have hσS : σ ⊆ S i :=
    (meeting_simplex_vertices Γ hΓ hn (c i) (h⁻¹ • p) σ hcard hconn hp' R hR hball').trans
      Finset.subset_union_right
  intro w hw
  let q := pointProbability K ⟨w,hsp hw⟩
  have hq : q.coeff=w := pointProbability_coeff K _
  have hqS : q.coeff.support ⊆ s := by
    have hh := (convexHull_single_eq_probabilitySet s) ▸ hw
    exact hq.symm ▸ hh.2.2
  rw [← hq]
  apply (BallOrbitForms.translatedPatch_mem S K h i q).mpr
  refine ⟨hq.symm ▸ hsp hw,?_⟩
  rw [smul_probability_support]
  exact (Finset.map_subset_map.mpr hqS).trans (hsσ.trans hσS)

lemma ballComplement_marked (c : C → FinProbability Y) (h : H) (i : C)
    {R t : ℝ} (hR : 0≤R) (ht : 0<t) (htR : t≤R)
    (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) :
    let S := fun i => ballSupport Γ (c i) n R
    let D := OrbitForms.cuts (H := H) (BallOrbitForms.data S c n) ht
    Cuts.IsMarked (D.refine T).complex
      ((Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space \
        {v | centerDistance Γ hΓ K n (h • c i) v<t}) := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  let D := OrbitForms.cuts (H := H) (BallOrbitForms.data S c n) ht
  let P := BallOrbitForms.translatedPatch S K h i
  let O := D.outerPatch P (BallOrbitForms.branches S h i)
  apply (D.refine T).marked_complement_of_patch _ P O
  · exact D.outerPatch_marked ((D.refine T).preserves_marked
      (BallOrbitForms.translatedPatch_marked S K h i)) _
  · ext v
    constructor
    · intro hv
      have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := hv.1.1
      let p := pointProbability K ⟨v,hvK⟩
      have hp : p.coeff=v := pointProbability_coeff K _
      rw [← hp] at hv ⊢
      have hh := (BallOrbitForms.outerPatch_mem S c n hi
        (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mp hv
      refine ⟨hh.1,?_⟩
      change ¬centerDistance Γ hΓ K n (h • c i) p.coeff<t
      rw [centerDistance_apply Γ hΓ K n _ p (pointProbability_face K ⟨v,hvK⟩)]
      exact not_lt.mpr hh.2
    · rintro ⟨hv,hout⟩
      have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := hv.1
      let p := pointProbability K ⟨v,hvK⟩
      have hp : p.coeff=v := pointProbability_coeff K _
      rw [← hp] at hv hout ⊢
      apply (BallOrbitForms.outerPatch_mem S c n hi
        (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mpr
      refine ⟨hv,?_⟩
      change ¬centerDistance Γ hΓ K n (h • c i) p.coeff<t at hout
      rw [centerDistance_apply Γ hΓ K n _ p (pointProbability_face K ⟨v,hvK⟩)] at hout
      exact not_lt.mp hout
  · rintro _ ⟨s,hs,rfl⟩ hmeet
    rw [Finset.coe_image] at hmeet ⊢
    exact meeting_simplex_patch Γ hΓ rfl hn K hK hact hi c h i hR htR s hs hmeet

end Sparse.GraphGeometry

namespace Sparse

open Set Finset

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype C]

lemma finite_translated_support_meeting (S : C → Finset Y) (s : Finset Y) :
    {j : H × C | ∃ w ∈ S j.2, j.1 • w ∈ s}.Finite := by
  have hi : (⋃ i : C, (fun h : H => (h,i)) ''
      (⋃ w ∈ (S i : Set Y), {h : H | h • w ∈ s})).Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.Finite.image
    apply Set.Finite.biUnion (S i).finite_toSet
    intro w _
    exact Set.Finite.preimage (fun h _ k _ he => IsCancelSMul.right_cancel h k w he)
      s.finite_toSet
  apply hi.subset
  rintro ⟨h,i⟩ ⟨w,hw,hs⟩
  exact Set.mem_iUnion.mpr ⟨i,h,Set.mem_iUnion₂.mpr ⟨w,hw,hs⟩,rfl⟩

end Sparse

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [Fintype C]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi

lemma finite_ball_incidence (c : C → FinProbability Y) {R : ℝ} (hR : 0≤R)
    (s : Finset (Y →₀ ℝ)) (hs : s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :
    {j : H × C | ({v | centerDistance Γ hΓ K n (j.1 • c j.2) v≤R} ∩
      convexHull ℝ (s : Set (Y →₀ ℝ))).Nonempty}.Finite := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  obtain ⟨σ,hσ,rfl⟩ := hs
  apply (finite_translated_support_meeting (H := H) S σ).subset
  rintro ⟨h,i⟩ ⟨v,hv,hvs⟩
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space ⟨σ,hσ,rfl⟩ hvs
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hpK := pointProbability_face K ⟨v,hvK⟩
  have hpσ : p.coeff.support⊆σ := by
    rw [Finset.coe_image] at hvs
    have hh := (convexHull_single_eq_probabilitySet σ) ▸ hvs
    exact hp.symm ▸ hh.2.2
  have hball : FinProbability.rho n (h • c i) p≤R := by
    change centerDistance Γ hΓ K n (h • c i) v≤R at hv
    rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at hv
    exact hv
  have hsub := ballSupport_inverse Γ hΓ rfl hn K hK hact hi c h i p hpK hR hball
  obtain ⟨y,hy⟩ := p.coeff_support_nonempty
  have hymap := (BallOrbitForms.inverse_support_iff h p (S i)).mp hsub hy
  obtain ⟨w,hw,he⟩ := Finset.mem_map.mp hymap
  refine ⟨w,hw,?_⟩
  have hey : h • w = y := he
  rw [hey]
  exact hpσ hy

end Sparse.GraphGeometry

namespace Sparse.Cuts.SubdivisionFamily

open Set Finset MeasureTheory

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [CompactSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

lemma countable_exceptional_levels (T : SubdivisionFamily X K) (hK : K.faces.Countable)
    {J : Type*} [Countable J] (a : J → V → ℝ) :
    {t : ℝ | ¬∀ x s, s ∈ (T.val x).complex.faces →
      ∀ j y, y ∈ s → a j y ≠ t}.Countable := by
  let bad : Set ℝ := ⋃ j, a j '' (⋃ x, (T.val x).complex.vertices)
  have hb : bad.Countable := Set.countable_iUnion fun j => (T.countable_vertices hK).image (a j)
  apply hb.mono
  intro t ht
  simp only [Set.mem_ofPred_eq,not_forall,not_not] at ht
  obtain ⟨x,s,hs,j,y,hy,he⟩ := ht
  exact Set.mem_iUnion.mpr ⟨j,y,Set.mem_iUnion.mpr ⟨x,
    (T.val x).complex.down_closed hs (Finset.singleton_subset_iff.mpr hy)
      (Finset.singleton_nonempty _)⟩,he⟩

end Sparse.Cuts.SubdivisionFamily

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y] [Fintype C]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi

omit [Countable H] [Countable Y] [CompactSpace X] in

theorem exists_ball_replacement
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T)
    {R t : ℝ} (hR : 0<R) (ht : 0<t) (htR : t≤R)
    (old : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P)
    (hT : OrbitForms.Equivariant (H := H) old.next)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    (hZ : OrbitForms.MarkedEquivariant (H := H) old.zero)
    (c : C → FinProbability Y) (B : C → Set X) (hB : ∀ i, IsClopen (B i))
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces →
      ∀ j : H × BallOrbitForms.Index (fun i => ballSupport Γ (c i) n R),
      ∃ v∈F, OrbitForms.form (BallOrbitForms.data (fun i => ballSupport Γ (c i) n R) c n) j v≠t) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero ∧
      ∀ x, A.zero.val x = Cuts.replacementSet (P.val x) (old.zero.val x)
        (fun j : H × C => {v | centerDistance Γ hΓ K n (j.1 • c j.2) v<t})
        (fun j : H × C => {v | centerDistance Γ hΓ K n (j.1 • c j.2) v=t})
        (fun j : H × C => (fun x => j.1⁻¹ • x) ⁻¹' B j.2) x := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  let d := BallOrbitForms.data S c n
  let D := OrbitForms.cuts (H := H) d ht
  let f := fun j : H × C => centerDistance Γ hΓ K n (j.1 • c j.2)
  let patch := fun j : H × C => BallOrbitForms.translatedPatch S K j.1 j.2
  let branches := fun j : H × C => BallOrbitForms.branches S j.1 j.2
  let act := fun j : H × C => (fun x => j.1⁻¹ • x) ⁻¹' B j.2
  have hsphere (j : H × C) := sphere_eq_patch Γ hΓ rfl hn K hK hact hi c
    j.1 j.2 hR.le ht htR
  have hfin (s) (hs : s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :=
    finite_ball_incidence Γ hΓ rfl hn K hK hact hi c hR.le s hs
  let A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P := by
    refine D.replacementStep T P (realizationDistance Γ hΓ K n) R t old
      f patch branches act (fun j => (hB j.2).preimage (continuous_const_smul j.1⁻¹))
      (fun j => BallOrbitForms.translatedPatch_marked S K j.1 j.2)
      hsphere (fun x j => ballComplement_marked Γ hΓ rfl hn K hK hact hi c
        j.1 j.2 hR.le ht htR (old.next.val x)) (fun _ => rfl) hgeneric ?_ ?_ ?_ ?_ htR
    · intro s hs
      apply (hfin s hs).subset
      rintro j ⟨v,hv,hvs⟩
      exact ⟨v,hv.le.trans htR,hvs⟩
    · intro s hs
      apply (hfin s hs).subset
      rintro j ⟨v,hv,hvs⟩
      rw [← hsphere j] at hv
      refine ⟨v,?_,hvs⟩
      change centerDistance Γ hΓ K n (j.1 • c j.2) v ≤ R
      rw [hv.2]
      exact htR
    · intro j
      apply continuousOn_centerDistance Γ hΓ hn K
        (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,_⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
      intro σ hσ
      obtain ⟨τ,_,hστ,hτ,hconn⟩ := hK σ hσ.1
      have hσcard : σ.card=n+1 := hσ.2
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by omega)
      rw [he]
      exact hconn
    · intro j p hp q hq
      exact realizationDistance_center_triangle Γ hΓ K n (j.1 • c j.2) p hp q hq
  have hPk (x : X) : P.val x ⊆ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
    rw [← (T.val x).space_eq]
    exact (P.marked x).subset_space
  have hval (x : X) : A.zero.val x = Cuts.replacementSet (P.val x) (old.zero.val x)
      (fun j => {v | f j v<t}) (fun j => {v | f j v=t}) act x := by
    change Cuts.replacementSet (P.val x) (old.zero.val x) _
      (fun j => D.spherePatch (patch j) (branches j)) _ _ = _
    unfold Cuts.replacementSet Cuts.activatedUnion
    have hh (j : H × C) : D.spherePatch (patch j) (branches j) =
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∩ {v | f j v=t} :=
      (hsphere j).symm
    simp_rw [hh]
    ext v
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,Set.mem_iUnion]
    constructor
    · rintro (hv | ⟨hp,j,hj⟩)
      · exact Or.inl hv
      · apply Or.inr
        refine ⟨hp,j,?_⟩
        by_cases hh : x∈act j
        · simp only [hh,ite_true] at hj ⊢
          exact hj.2
        · simpa only [hh,ite_false] using hj
    · rintro (hv | ⟨hp,j,hj⟩)
      · exact Or.inl hv
      · apply Or.inr
        refine ⟨hp,j,?_⟩
        by_cases hh : x∈act j
        · simp only [hh,ite_true] at hj ⊢
          exact ⟨hPk x hp,hj⟩
        · simpa only [hh,ite_false] using hj
  refine ⟨A,OrbitForms.refineFamily_equivariant d ht old.next hT,?_,hval⟩
  intro k x v hv
  rw [hval x] at hv
  rw [hval (k • x)]
  have hfk (j : H × C) (hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
      f (k*j.1,j.2) (OrbitForms.push k v)=f j v := by
    dsimp only [f]
    rw [mul_smul,centerDistance_push K hact Γ hΓ hi n k (j.1 • c j.2) v hvK]
  have hactk (j : H × C) : k • x∈act (k*j.1,j.2) ↔ x∈act j := by
    change (k*j.1)⁻¹ • (k • x)∈B j.2 ↔ j.1⁻¹ • x∈B j.2
    rw [mul_inv_rev,mul_smul,inv_smul_smul]
  rcases hv with hv | ⟨hp,hj⟩
  · refine Or.inl ⟨hZ k x v hv.1,?_⟩
    intro hh
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
    by_cases hjx : k • x∈act j
    · simp only [hjx,ite_true] at hj
      apply hv.2
      apply Set.mem_iUnion.mpr
      refine ⟨(k⁻¹*j.1,j.2),?_⟩
      have ha : x∈act (k⁻¹*j.1,j.2) := by
        change (k⁻¹*j.1)⁻¹ • x∈B j.2
        change j.1⁻¹ • (k • x)∈B j.2 at hjx
        simpa only [mul_inv_rev,inv_inv,mul_smul] using hjx
      simp only [ha,ite_true]
      have he := hfk (k⁻¹*j.1,j.2) (hPk x (old.subset x hv.1))
      simp only [mul_inv_cancel_left] at he
      change f j (OrbitForms.push k v)<t at hj
      change f (k⁻¹*j.1,j.2) v<t
      rw [← he]
      exact hj
    · simp only [hjx,ite_false,Set.mem_empty_iff_false] at hj
  · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hj
    refine Or.inr ⟨hP k x v hp,Set.mem_iUnion.mpr ⟨(k*j.1,j.2),?_⟩⟩
    by_cases hjx : x∈act j
    · have hjkx := (hactk j).mpr hjx
      simp only [hjx,ite_true] at hj
      simp only [hjkx,ite_true]
      change f (k*j.1,j.2) (OrbitForms.push k v)=t
      rw [hfk j (hPk x hp)]
      exact hj
    · simp only [hjx,ite_false,Set.mem_empty_iff_false] at hj

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.SimplexMeasures
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

lemma measure_surgery_gain {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (P Z U S : Set E) (hU : MeasurableSet U) :
    μ ((Z \ U) ∪ (P ∩ S)) + μ (Z ∩ U) ≤ μ Z + μ (P ∩ S) := by
  calc
    _ ≤ (μ (Z \ U) + μ (P ∩ S)) + μ (Z ∩ U) :=
      add_le_add_left (measure_union_le _ _) _
    _ = (μ (Z \ U) + μ (Z ∩ U)) + μ (P ∩ S) := by ac_rfl
    _ = _ := by rw [measure_sdiff_add_inter Z hU]

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

section

open Finset Set MeasureTheory

variable {n : ℕ}

lemma sum_relabelCoefficients (e : Equiv.Perm (Fin (n+1))) (p : Fin (n+1) → ℝ) :
    ∑ i, relabelCoefficients e p i = ∑ i,p i := e.symm.sum_comp p

lemma relabelCoefficients_single (e : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    relabelCoefficients e (Pi.single i 1) = Pi.single (e i) 1 := by
  ext j
  change (Pi.single i 1 : Fin (n+1) → ℝ) (e.symm j) = (Pi.single (e i) 1 : Fin (n+1) → ℝ) j
  simp only [Pi.single_apply]
  by_cases h : e.symm j = i
  · have he : j=e i := by simpa using congrArg e h
    simp [he]
  · have he : j≠e i := fun k => h (by simp [k])
    simp [h,he]

lemma sum_edgeVector (u v : Fin (n+1)) : ∑ i, edgeVector u v i = 0 := by
  simp [edgeVector,Pi.sub_apply,Finset.sum_sub_distrib]

lemma relabel_edgeVector (e : Equiv.Perm (Fin (n+1))) (u v : Fin (n+1)) :
    relabelCoefficients e (edgeVector u v) = edgeVector (e u) (e v) := by
  simp only [edgeVector,map_sub,relabelCoefficients_single]

lemma coefficient_ext_total {p q : Fin (n+1) → ℝ}
    (hs : ∑ i,p i = ∑ i,q i) (he : ∀ i : Fin n,p i.succ=q i.succ) : p=q := by
  ext i
  induction i using Fin.cases with
  | zero =>
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ] at hs
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (by rfl : (Finset.univ : Finset (Fin n))=Finset.univ)
      (fun i _ => he i)
    linarith
  | succ i => exact he i

lemma treeParam_difference (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x y : EuclideanSpace ℝ (Fin n)) :
    treeParam T hT x - treeParam T hT y =
      ∑ j, (x.ofLp j-y.ofLp j) • edgeVector
        ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) := by
  apply coefficient_ext_total
  · simp only [Pi.sub_apply,Finset.sum_sub_distrib]
    rw [show (∑ i,treeParam T hT x i)=1 from sum_barycentricParam _,
      show (∑ i,treeParam T hT y i)=1 from sum_barycentricParam _]
    simp only [sub_self,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,sum_edgeVector,mul_zero,Finset.sum_const_zero]
  · intro i
    simp only [treeParam,barycentricParam,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    change (∑ j, realTreeIncidence T hT i j * x.ofLp j) -
      (∑ j, realTreeIncidence T hT i j * y.ofLp j) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hc : realTreeIncidence T hT i j = edgeVector
        ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) i.succ := by
      simp [realTreeIncidence,treeIncidence,rootCoordinate,edgeVector,Pi.single_apply]
    rw [hc]
    ring

lemma treeCoordinates_edgeVector (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (j : Fin n) :
    treeCoordinates T hT (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
      ((treeEdgeEquiv T hT j).val.out.2)) = WithLp.toLp 2 (Pi.single j 1) := by
  have hh := treeParam_difference T hT (WithLp.toLp 2 (Pi.single j 1)) 0
  have hh' : treeParam T hT (WithLp.toLp 2 (Pi.single j 1)) - treeParam T hT 0 =
      edgeVector ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) := by
    simpa only [WithLp.ofLp_zero,Pi.zero_apply,sub_zero,Pi.single_apply,
      ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh
  rw [← hh',map_sub,treeCoordinates_treeParam,treeCoordinates_treeParam,sub_zero]

lemma mapped_treeEdge_out (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (j : Fin n) :
    (e ((treeEdgeEquiv T hT j).val.out.1) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1 ∧
     e ((treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) ∨
    (e ((treeEdgeEquiv T hT j).val.out.1) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2 ∧
     e ((treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1) := by
  apply Sym2.eq_iff.mp
  have ho : s((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1,
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val :=
    (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out_eq
  rw [ho]
  have h : treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j) =
      e.mapEdgeSet (treeEdgeEquiv T hT j) := by simp [treeEdgePermutation]
  rw [h]
  change s(e ((treeEdgeEquiv T hT j).val.out.1),e ((treeEdgeEquiv T hT j).val.out.2)) =
    Sym2.map e ((treeEdgeEquiv T hT j).val)
  have ho' : s((treeEdgeEquiv T hT j).val.out.1,(treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv T hT j).val := (treeEdgeEquiv T hT j).val.out_eq
  exact congrArg (Sym2.map e) ho'

lemma exists_treeEdge_signs (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : ∃ ε : Fin n → ℝ, (∀ j, ε j ^ 2 = 1) ∧ ∀ j,
      relabelCoefficients e.toEquiv (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
        ((treeEdgeEquiv T hT j).val.out.2)) = ε j •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) := by
  classical
  have hh : ∀ j : Fin n, ∃ a : ℝ, a^2=1 ∧
      relabelCoefficients e.toEquiv (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
        ((treeEdgeEquiv T hT j).val.out.2)) = a •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) := by
    intro j
    rw [relabel_edgeVector]
    change ∃ a : ℝ, a^2=1 ∧ edgeVector (e ((treeEdgeEquiv T hT j).val.out.1))
        (e ((treeEdgeEquiv T hT j).val.out.2)) = a •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2)
    rcases mapped_treeEdge_out T U hT hU e j with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · refine ⟨1,by norm_num,?_⟩
      simpa only [one_smul] using congrArg₂ edgeVector h₁ h₂
    · refine ⟨-1,by norm_num,?_⟩
      rw [h₁,h₂]
      simp [edgeVector]
  choose ε hε he using hh
  exact ⟨ε,hε,he⟩

lemma signedEdgeMap_isometry (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j ^ 2 = 1) : Isometry (signedEdgeMap π ε) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  have hsq : ‖signedEdgeMap π ε x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    change (∑ j, (ε (π.symm j) * x.ofLp (π.symm j)) ^ 2) = ∑ j,x.ofLp j ^ 2
    simp_rw [mul_pow,hε,one_mul]
    exact π.symm.sum_comp (fun j : Fin n => x.ofLp j ^ 2)
  nlinarith [norm_nonneg (signedEdgeMap π ε x),norm_nonneg x]

lemma signedEdgeMap_sum (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : signedEdgeMap π ε x =
      ∑ j, (x.ofLp j * ε j) • WithLp.toLp 2 (Pi.single (π j) 1) := by
  ext k
  change ε (π.symm k) * x.ofLp (π.symm k) =
    (∑ j, (x.ofLp j * ε j) • (WithLp.toLp 2 (Pi.single (π j) 1) : EuclideanSpace ℝ (Fin n))).ofLp k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply]
  rw [Finset.sum_eq_single (π.symm k)]
  · simp [mul_comm]
  · intro j _ hj
    have hne : k ≠ π j := fun he => hj (by simpa using congrArg π.symm he.symm)
    simp [hne]
  · simp

lemma treeTransition_sub (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (ε : Fin n → ℝ)
    (he : ∀ j, relabelCoefficients e.toEquiv
      (edgeVector ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2)) =
      ε j • edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2))
    (x y : EuclideanSpace ℝ (Fin n)) :
    treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x)) -
      treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT y)) =
        signedEdgeMap (treeEdgePermutation T U hT hU e) ε (x-y) := by
  rw [← map_sub,← map_sub,treeParam_difference]
  simp_rw [map_sum,map_smul,he,map_smul,treeCoordinates_edgeVector,smul_smul]
  rw [signedEdgeMap_sum]
  rfl

lemma treeTransition_isometry (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : Isometry (fun x =>
      treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x))) := by
  obtain ⟨ε,hε,he⟩ := exists_treeEdge_signs T U hT hU e
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm,treeTransition_sub T U hT hU e ε he,map_sub,← dist_eq_norm]
  exact (signedEdgeMap_isometry _ ε hε).dist_eq x y

lemma treeArea_relabel (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (j : ℕ) (Q : Set (Fin (n+1) → ℝ))
    (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    treeArea U hU j (relabelCoefficients e.toEquiv '' Q) = treeArea T hT j Q := by
  have hQ' : relabelCoefficients e.toEquiv '' Q ⊆ {p | ∑ i,p i=1} := by
    rintro _ ⟨p,hp,rfl⟩
    simpa only [Set.mem_ofPred_eq,sum_relabelCoefficients] using hQ hp
  unfold treeArea
  rw [treeParam_preimage_eq_image U hU _ hQ']
  have hset : treeCoordinates U hU '' (relabelCoefficients e.toEquiv '' Q) =
      (fun x => treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x))) ''
        (treeParam T hT ⁻¹' Q) := by
    ext z
    constructor
    · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
      refine ⟨treeCoordinates T hT p,?_,?_⟩
      · simpa only [Set.mem_preimage,treeParam_treeCoordinates T hT p (hQ hp)] using hp
      · change treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT (treeCoordinates T hT p))) = _
        rw [treeParam_treeCoordinates T hT p (hQ hp)]
    · rintro ⟨x,hx,rfl⟩
      exact ⟨_,⟨treeParam T hT x,hx,rfl⟩,rfl⟩
  rw [hset]
  exact (treeTransition_isometry T U hT hU e).euclideanHausdorffMeasure_image _

end

open MeasureTheory Set Finset

open scoped ENNReal

variable {n : ℕ}

lemma simplexArea_relabel (Γ : SimpleGraph (Fin (n+1)))
    (e : Equiv.Perm (Fin (n+1))) (j : ℕ) (Q : Set (Fin (n+1) → ℝ))
    (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    simplexArea (e.simpleGraph Γ) j (relabelCoefficients e '' Q) = simplexArea Γ j Q := by
  unfold simplexArea
  rw [← Fintype.card_congr (spanningTreeRelabel Γ e)]
  congr 1
  rw [← (spanningTreeRelabel Γ e).sum_comp]
  apply Finset.sum_congr rfl
  intro T _
  exact treeArea_relabel T.val (e.simpleGraph T.val) T.property.2
    (spanningTreeRelabel Γ e T).property.2 (SimpleGraph.Iso.comap e.symm T.val).symm j Q hQ

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.OrbitAreas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

lemma finsuppRelabel_single (e : Y ≃ Z) (y : Y) :
    Finsupp.domLCongr (R := ℝ) e (Finsupp.single y (1 : ℝ)) = Finsupp.single (e y) 1 := by
  ext z
  change (Finsupp.single y (1 : ℝ)) (e.symm z) = (Finsupp.single (e y) 1) z
  simp only [Finsupp.single_apply]
  have hh : y=e.symm z ↔ e y=z := ⟨fun h => by rw [h,Equiv.apply_symm_apply],
    fun h => by rw [←h,Equiv.symm_apply_apply]⟩
  simp [hh]

lemma simplexVertices_relabel (e : Y ≃ Z) (s : Finset Y) :
    (simplexVertices (s.map e.toEmbedding) : Set (Z →₀ ℝ)) =
      Finsupp.domLCongr (R := ℝ) e '' (simplexVertices s : Set (Y →₀ ℝ)) := by
  simp only [simplexVertices,Finset.coe_image,Finset.coe_map,Set.image_image]
  congr 1
  funext y
  exact (finsuppRelabel_single e y).symm

lemma sourceInterior_relabel (e : Y ≃ Z) (s : Finset Y) :
    sourceInterior (s.map e.toEmbedding) = Finsupp.domLCongr (R := ℝ) e '' sourceInterior s := by
  unfold sourceInterior
  rw [simplexVertices_relabel]
  have hh : convexHull ℝ (Finsupp.domLCongr (R := ℝ) e '' (simplexVertices s : Set (Y →₀ ℝ))) =
      (finsuppRelabelIsometry e).toAffineIsometryEquiv.toAffineIsometry ''
        convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) :=
    ((Finsupp.domLCongr (R := ℝ) e).toLinearMap.image_convexHull _).symm
  rw [hh]
  exact (finsuppRelabelIsometry e).toAffineIsometryEquiv.toAffineIsometry.intrinsicInterior_image _

omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexEnumeration_permutation {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (i : Fin (n+1)) :
    (simplexEnumeration (s.map e.toEmbedding) (by simpa using hs)
      (simplexPermutation e s hs i)).val = e (simplexEnumeration s hs i).val := by
  simp [simplexPermutation]

omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexCoordinates_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (p : Y →₀ ℝ) :
    simplexCoordinates (s.map e.toEmbedding) (by simpa using hs) (Finsupp.domLCongr (R := ℝ) e p) =
      relabelCoefficients (simplexPermutation e s hs) (simplexCoordinates s hs p) := by
  ext j
  obtain ⟨i,rfl⟩ := (simplexPermutation e s hs).surjective j
  change p (e.symm (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs i)).val) =
    p (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs i))).val
  rw [simplexEnumeration_permutation,Equiv.symm_apply_apply,Equiv.symm_apply_apply]

omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexGraph_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (Γ : SimpleGraph Y) (Δ : SimpleGraph Z)
    (he : ∀ u v,Δ.Adj (e u) (e v) ↔ Γ.Adj u v) :
    simplexGraph Δ (s.map e.toEmbedding) (by simpa using hs) =
      (simplexPermutation e s hs).simpleGraph (simplexGraph Γ s hs) := by
  ext a b
  obtain ⟨u,rfl⟩ := (simplexPermutation e s hs).surjective a
  obtain ⟨v,rfl⟩ := (simplexPermutation e s hs).surjective b
  change Δ.Adj (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs u)).val
    (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs v)).val ↔
    Γ.Adj (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs u))).val
      (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs v))).val
  rw [simplexEnumeration_permutation,simplexEnumeration_permutation,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact he _ _

omit [DecidableEq Z] in
lemma originalSimplexArea_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (Γ : SimpleGraph Y) (Δ : SimpleGraph Z)
    (he : ∀ u v,Δ.Adj (e u) (e v) ↔ Γ.Adj u v) (j : ℕ)
    (Q : Set (Y →₀ ℝ)) (hQ : Q⊆convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    simplexArea (simplexGraph Δ (s.map e.toEmbedding) (by simpa using hs)) j
      (simplexCoordinates (s.map e.toEmbedding) (by simpa using hs) '' (Finsupp.domLCongr (R := ℝ) e '' Q)) =
      simplexArea (simplexGraph Γ s hs) j (simplexCoordinates s hs '' Q) := by
  rw [simplexGraph_relabel e s hs Γ Δ he,Set.image_image]
  have hi : (fun p => simplexCoordinates (s.map e.toEmbedding) (by simpa using hs)
      (Finsupp.domLCongr (R := ℝ) e p)) =
      (fun p => relabelCoefficients (simplexPermutation e s hs) (simplexCoordinates s hs p)) :=
    funext (simplexCoordinates_relabel e s hs)
  rw [hi,← Set.image_image]
  apply simplexArea_relabel
  rintro _ ⟨p,hp,rfl⟩
  exact simplexCoordinates_sum s hs (hQ hp)

end

open Finset Set

open scoped Pointwise Classical

variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (K : PreAbstractSimplicialComplex Y) (n : ℕ)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

lemma sourceTop_stabilizer_eq (σ : SourceTop K n) :
    letI := sourceTopAction K n hact
    MulAction.stabilizer H σ=MulAction.stabilizer H σ.val := by
  let := sourceTopAction K n hact
  ext h
  change (h • σ=σ) ↔ h • σ.val=σ.val
  exact ⟨fun he => congrArg Subtype.val he,fun he => Subtype.ext he⟩

lemma finite_sourceTop_stabilizer [IsCancelSMul H Y] (σ : SourceTop K n) :
    letI := sourceTopAction K n hact
    Finite (MulAction.stabilizer H σ) := by
  let := sourceTopAction K n hact
  rw [sourceTop_stabilizer_eq K n hact]
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [σ.property.2]; omega : 0<σ.val.card)
  let f : MulAction.stabilizer H σ.val → σ.val := fun h => ⟨h.val • v,by
    have hh := Finset.smul_mem_smul_finset (a := h.val) hv
    rw [h.property] at hh
    exact hh⟩
  apply Finite.of_injective f
  intro h k he
  exact Subtype.ext (IsCancelSMul.right_cancel h.val k.val v (congrArg Subtype.val he))

end Sparse

namespace Sparse.OrbitAreas

section

open scoped BigOperators Pointwise ENNReal

variable {H T : Type*} [Group H] [MulAction H T]

lemma sum_orbit_multiplicity (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (∑' h : H, f (h • a)) =
      (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞) *
        ∑' b : MulAction.orbit H a, f b.val := by
  let := Fintype.ofFinite (MulAction.stabilizer H a)
  rw [← (orbitTimesStabilizer (H := H) a).tsum_eq (fun h => f (h • a))]
  simp only [orbitTimesStabilizer_smul]
  rw [ENNReal.tsum_prod (f := fun (b : MulAction.orbit H a) (_ : MulAction.stabilizer H a) => f b.val)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left,Nat.card_eq_fintype_card]

lemma normalized_orbit_sum (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞)⁻¹ * (∑' h : H, f (h • a)) =
      ∑' b : MulAction.orbit H a, f b.val := by
  rw [sum_orbit_multiplicity,← mul_assoc]
  have hn : Nat.card (MulAction.stabilizer H a) ≠ 0 := Nat.card_pos.ne'
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn) (by simp),one_mul]

lemma normalized_inverse_orbit_sum (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞)⁻¹ * (∑' h : H, f (h⁻¹ • a)) =
      ∑' b : MulAction.orbit H a, f b.val := by
  have he : (∑' h : H, f (h⁻¹ • a)) = ∑' h : H, f (h • a) :=
    (Equiv.inv H).tsum_eq (fun h => f (h • a))
  rw [he]
  exact normalized_orbit_sum a f

lemma normalized_all_orbits (f : T → ℝ≥0∞)
    [∀ a : T, Finite (MulAction.stabilizer H a)] :
    (∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∑' h : H, f (h⁻¹ • o.out)) = ∑' a : T, f a := by
  simp only [normalized_inverse_orbit_sum]
  rw [← ENNReal.tsum_sigma]
  exact (MulAction.selfEquivSigmaOrbits H T).symm.tsum_eq f

end

section

open MeasureTheory Set

open scoped ENNReal

variable {H T X : Type*} [Group H] [MulAction H T] [MulAction H X]
  [Countable H] [Countable T] [MeasurableSpace X]

omit [Countable H] [Countable T] in
lemma measurable_orbitActivated (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a)) (a : T) (h : H) :
    Measurable (orbitActivated B f a h) :=
  ((hf (h⁻¹ • a)).indicator hB).comp (hμ h⁻¹).measurable

omit [Countable H] [Countable T] in
lemma integral_orbitActivated (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a)) (a : T) (h : H) :
    (∫⁻ x,orbitActivated B f a h x ∂μ) = ∫⁻ x in B,f (h⁻¹ • a) x ∂μ := by
  unfold orbitActivated
  rw [(hμ h⁻¹).lintegral_comp ((hf _).indicator hB), lintegral_indicator hB]

lemma normalized_activated_integral (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a))
    [∀ a : T, Finite (MulAction.stabilizer H a)] :
    (∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∫⁻ x,∑' h : H,orbitActivated B f o.out h x ∂μ) =
      ∫⁻ x in B,∑' a : T,f a x ∂μ := by
  calc
    _ = ∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∑' h : H,∫⁻ x in B,f (h⁻¹ • o.out) x ∂μ := by
          apply tsum_congr
          intro o
          congr 1
          rw [lintegral_tsum (fun h => (measurable_orbitActivated μ hμ B hB f hf o.out h).aemeasurable)]
          exact tsum_congr (fun h => integral_orbitActivated μ hμ B hB f hf o.out h)
    _ = ∑' a : T,∫⁻ x in B,f a x ∂μ := normalized_all_orbits (fun a => ∫⁻ x in B,f a x ∂μ)
    _ = _ := (lintegral_tsum (fun a => (hf a).aemeasurable)).symm

end

open Set Finset MeasureTheory

open scoped Pointwise ENNReal Classical

variable {H T : Type*} [Group H] [MulAction H T]

variable [Finite (MulAction.orbitRel.Quotient H T)]

lemma sum_orbitReps (f : T → ℝ≥0∞) :
    (∑ a∈orbitReps (H := H) (T := T), f a) =
      ∑' o : MulAction.orbitRel.Quotient H T,f o.out := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient H T)
  rw [tsum_fintype]
  exact Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)

end Sparse.OrbitAreas

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.AreaSurgery
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

lemma measure_surgery_countable_gain {E A : Type*} [MeasurableSpace E] [Countable A]
    (μ : Measure E) (P Z : Set E) (U S : A → Set E)
    (hU : ∀ a,MeasurableSet (U a))
    (hd : Pairwise (fun a b => Disjoint (U a) (U b))) :
    μ ((Z \ ⋃ a,U a) ∪ (P ∩ ⋃ a,S a)) + ∑' a,μ (Z ∩ U a) ≤
      μ Z + ∑' a,μ (P ∩ S a) := by
  have hc : μ (Z ∩ ⋃ a,U a)=∑' a,μ (Z∩U a) := by
    calc
      μ (Z ∩ ⋃ a,U a) = (μ.restrict Z) (⋃ a,U a) := by
        rw [Measure.restrict_apply (MeasurableSet.iUnion hU),Set.inter_comm]
      _ = ∑' a,(μ.restrict Z) (U a) := measure_iUnion hd hU
      _ = _ := by
        apply tsum_congr
        intro a
        rw [Measure.restrict_apply (hU a),Set.inter_comm]
  rw [← hc]
  apply (measure_surgery_gain μ P Z _ _ (MeasurableSet.iUnion hU)).trans
  apply add_le_add_right
  rw [Set.inter_iUnion]
  exact measure_iUnion_le _

lemma countable_ball_area_jumps {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (Z : Set E) {f : E → ℝ} (hf : Measurable f) :
    {t : ℝ | μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t})}.Countable := by
  have hh := countable_meas_le_ne_meas_lt (μ.restrict Z) (fun p => (-f p : ℝ))
  have hsub : {t : ℝ | μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t})} ⊆
      Neg.neg ⁻¹' {t : ℝ | (μ.restrict Z) {p | t≤ -f p} ≠
        (μ.restrict Z) {p | t < -f p}} := by
    intro t ht
    change μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t}) at ht
    change (μ.restrict Z) {p | -t≤ -f p} ≠ (μ.restrict Z) {p | -t < -f p}
    simpa only [neg_le_neg_iff,neg_lt_neg_iff,
      Measure.restrict_apply (measurableSet_le hf measurable_const),
      Measure.restrict_apply (measurableSet_lt hf measurable_const),Set.inter_comm] using ht
  exact (hh.preimage neg_injective).mono hsub

lemma nearMinimum_local_comparison {I I' M N ε : ℝ≥0∞}
    (hI : I<∞) (hmin : I≤I'+ε) (hgain : I'+M≤I+N) : M≤N+ε := by
  have hh : I+M≤I+(N+ε) := by
    calc
      I+M ≤ (I'+ε)+M := add_le_add_left hmin M
      _ = (I'+M)+ε := by ac_rfl
      _ ≤ (I+N)+ε := add_le_add_left hgain ε
      _ = I+(N+ε) := by ac_rfl
  exact (ENNReal.add_le_add_iff_left hI.ne).mp hh

lemma normalized_integrated_gain {X T : Type*} [MeasurableSpace X]
    (μ : Measure X) (reps : Finset T) (w : T → ℝ≥0∞)
    (old new removed inserted : T → X → ℝ≥0∞)
    (hnew : ∀ σ∈reps,Measurable (new σ))
    (hold : ∀ σ∈reps,Measurable (old σ))
    (hgain : ∀ σ∈reps, ∀ x,new σ x+removed σ x≤old σ x+inserted σ x) :
    (∑ σ∈reps,w σ*∫⁻ x,new σ x ∂μ) + (∑ σ∈reps,w σ*∫⁻ x,removed σ x ∂μ) ≤
      (∑ σ∈reps,w σ*∫⁻ x,old σ x ∂μ) + (∑ σ∈reps,w σ*∫⁻ x,inserted σ x ∂μ) := by
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ hσ
  rw [← mul_add,← mul_add]
  apply mul_le_mul_right
  rw [← lintegral_add_left (hnew σ hσ) _, ← lintegral_add_left (hold σ hσ) _]
  exact lintegral_mono (hgain σ hσ)

lemma ennreal_nearMinimum_of_real {I I' : ℝ≥0∞} {ε : ℝ}
    (hI : I≠∞) (hI' : I'≠∞) (hε : 0≤ε) (hmin : I.toReal≤I'.toReal+ε) :
    I≤I'+ENNReal.ofReal ε := by
  apply (ENNReal.toReal_le_toReal hI (ENNReal.add_ne_top.mpr ⟨hI',ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add hI' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε]
  exact hmin

end

open Finset Set MeasureTheory

open scoped Pointwise Classical BassTrace.Sparse ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.instMulActionSourceTop
omit hact in
lemma markedPair_image (Q : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (h : H) (x : X) :
    Q.P.val (h • x)=OrbitForms.push h '' Q.P.val x := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨OrbitForms.push h⁻¹ p,?_,?_⟩
    · simpa only [inv_smul_smul] using Q.markedEquivariant h⁻¹ (h • x) p hp
    · simpa only [inv_inv] using OrbitForms.push_inv_push h⁻¹ p
  · rintro _ ⟨p,hp,rfl⟩
    exact Q.markedEquivariant h x p hp

omit hact in
lemma localOriginalArea_locallyConstant (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) :
    IsLocallyConstant (localOriginalArea Γ Q σ j W) :=
  Q.P.localArea_locallyConstant _ _ (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    _ (Set.inter_subset_left.trans intrinsicInterior_subset) j

include hact in
lemma localOriginalArea_covariant (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (h : H) (x : X) :
    localOriginalArea Γ Q (h • σ) j (OrbitForms.push h '' W) (h • x) =
      localOriginalArea Γ Q σ j W x := by
  have hi : sourceInterior (h • σ).val=OrbitForms.push h '' sourceInterior σ.val := by
    change sourceInterior (h • σ.val)=_
    rw [smul_finset_eq_map]
    exact sourceInterior_relabel (MulAction.toPerm h) σ.val
  have he : Q.P.val (h • x) ∩ (sourceInterior (h • σ).val ∩ OrbitForms.push h '' W) =
      OrbitForms.push h '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)) := by
    rw [markedPair_image Q h x,hi,Set.image_inter (OrbitForms.push h).injective,
      Set.image_inter (OrbitForms.push h).injective]
  unfold localOriginalArea
  rw [he]
  change simplexArea (simplexGraph Γ (h • σ.val) _) j
    (simplexCoordinates (h • σ.val) _ ''
      (OrbitForms.push h '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)))) = _
  simpa only [← smul_finset_eq_map,OrbitForms.push] using originalSimplexArea_relabel (MulAction.toPerm h) σ.val σ.property.2 Γ Γ
    (hΓ h) j _ (fun _ hp => intrinsicInterior_subset hp.2.1)

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

omit hact in
lemma localOriginalArea_empty (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (x : X) :
    localOriginalArea Γ Q σ j ∅ x=0 := by
  rw [localOriginalArea_eq_measure]
  simp

include hact in
lemma active_area_eq_orbitActivated (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (B : Set X) (W : Set (Y →₀ ℝ)) (h : H) (x : X) :
    localOriginalArea Γ Q σ j (activeWindow B W h x) x =
      OrbitAreas.orbitActivated B (fun σ x => localOriginalArea Γ Q σ j W x) σ h x := by
  by_cases hx : h⁻¹ • x∈B
  · simp only [activeWindow,hx,ite_eq_left,OrbitAreas.orbitActivated,Set.indicator_of_mem hx]
    simpa only [smul_inv_smul] using
      localOriginalArea_covariant Γ hΓ Q (h⁻¹ • σ) j W h (h⁻¹ • x)
  · simp only [activeWindow,hx,OrbitAreas.orbitActivated,Set.indicator_of_notMem hx]
    exact localOriginalArea_empty Γ Q σ j x

omit hact in
lemma localArea_surgery_countable_gain [Countable H] (Γ : SimpleGraph Y)
    (P Z Z' : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (B : Set X) (U S : Set (Y →₀ ℝ)) (x : X)
    (hU : ∀ h : H, @MeasurableSet _ (borel (Y →₀ ℝ)) (activeWindow B U h x))
    (hd : Pairwise (fun h k : H => Disjoint (activeWindow B U h x) (activeWindow B U k x)))
    (hnew : Z'.P.val x = (Z.P.val x \ ⋃ h : H,activeWindow B U h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B S h x)) :
    originalArea Γ Z' σ j x + ∑' h : H,localOriginalArea Γ Z σ j (activeWindow B U h x) x ≤
      originalArea Γ Z σ j x + ∑' h : H,localOriginalArea Γ P σ j (activeWindow B S h x) x := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  simp only [originalArea_eq_measure,localOriginalArea_eq_measure]
  have he : Z'.P.val x ∩ sourceInterior σ.val =
      ((Z.P.val x ∩ sourceInterior σ.val) \ ⋃ h : H,activeWindow B U h x) ∪
      ((P.P.val x ∩ sourceInterior σ.val) ∩ ⋃ h : H,activeWindow B S h x) := by
    rw [hnew]
    ext p
    simp only [Set.mem_inter_iff,Set.mem_union,Set.mem_sdiff]
    tauto
  rw [he]
  exact measure_surgery_countable_gain _ _ _ _ _ hU hd

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [Countable H] [Countable Y] [IsCancelSMul H Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.instMulActionSourceTop_2
local instance instCountableSourceTop : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})

local instance instFiniteSubtypeMemSubgroupStabilizerSourceTop (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ

variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

lemma weighted_activated_originalArea (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (j : ℕ) (B : Set X) (hB : MeasurableSet B) (W : Set (Y →₀ ℝ)) :
    (∑ σ∈OrbitAreas.orbitReps (H := H) (T := SourceTop K n),
      (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹ *
        ∫⁻ x,∑' h : H,OrbitAreas.orbitActivated B
          (fun σ x => localOriginalArea Γ Q σ j W x) σ h x ∂μ) =
      ∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Q σ j W x ∂μ := by
  have hs (σ : SourceTop K n) : MulAction.stabilizer H σ.val=MulAction.stabilizer H σ :=
    (sourceTop_stabilizer_eq K n hact.out σ).symm
  simp_rw [hs]
  rw [OrbitAreas.sum_orbitReps]
  exact OrbitAreas.normalized_activated_integral μ hμ B hB _
    (fun σ => (localOriginalArea_locallyConstant Γ Q σ j W).continuous.measurable)

lemma normalizedArea_surgery_gain (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (P Z Z' : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (j : ℕ) (B : Set X) (hB : MeasurableSet B) (U S : Set (Y →₀ ℝ))
    (hU : ∀ (x : X) (h : H), @MeasurableSet _ (borel (Y →₀ ℝ)) (activeWindow B U h x))
    (hd : ∀ x, Pairwise (fun h k : H => Disjoint (activeWindow B U h x) (activeWindow B U k x)))
    (hnew : ∀ x,Z'.P.val x = (Z.P.val x \ ⋃ h : H,activeWindow B U h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B S h x)) :
    normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) Z' j +
        (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Z σ j U x ∂μ) ≤
      normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) Z j +
        (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ P σ j S x ∂μ) := by
  have hg := normalized_integrated_gain μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n))
    (fun σ => (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹)
    (fun σ x => originalArea Γ Z σ j x) (fun σ x => originalArea Γ Z' σ j x)
    (fun σ x => ∑' h : H,OrbitAreas.orbitActivated B
      (fun σ x => localOriginalArea Γ Z σ j U x) σ h x)
    (fun σ x => ∑' h : H,OrbitAreas.orbitActivated B
      (fun σ x => localOriginalArea Γ P σ j S x) σ h x)
    (fun σ _ => (originalArea_locallyConstant Γ Z' σ j).continuous.measurable)
    (fun σ _ => (originalArea_locallyConstant Γ Z σ j).continuous.measurable)
    (fun σ _ x => by
      simp_rw [← active_area_eq_orbitActivated Γ hΓ]
      exact localArea_surgery_countable_gain Γ P Z Z' σ j B U S x (hU x) (hd x) (hnew x))
  rw [weighted_activated_originalArea Γ Z μ hμ j B hB U,
    weighted_activated_originalArea Γ P μ hμ j B hB S] at hg
  exact hg

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.AffineCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine coarea from product measure and one-dimensional Lebesgue scaling. The transverse
measure may be s-finite; orthonormal coordinates specialize this to affine polyhedral area. -/

namespace BassTrace.Sparse

open MeasureTheory Set

open scoped ENNReal

lemma lintegral_affine_change (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {a : ℝ} (ha : a ≠ 0) (c : ℝ) :
    (∫⁻ t : ℝ, f t) = ENNReal.ofReal |a| * ∫⁻ s : ℝ, f (a * s + c) := by
  calc
    (∫⁻ t : ℝ, f t) = ∫⁻ t : ℝ, f (t + c) :=
      (lintegral_add_right_eq_self f c).symm
    _ = ENNReal.ofReal |a| * ∫⁻ s : ℝ, f (a * s + c) := by
      conv_lhs => rw [← Real.smul_map_volume_mul_left ha]
      have hh : Measurable (fun x : ℝ => f (x + c)) :=
        hf.comp (measurable_id.add_const c)
      rw [lintegral_smul_measure, lintegral_map hh (measurable_const_mul a)]
      rfl

section Product

variable {F : Type*} [MeasurableSpace F] (ν : Measure F) [SFinite ν]

lemma measurable_productSlice {Q : Set (ℝ × F)} (hQ : MeasurableSet Q) (a c : ℝ) :
    Measurable (fun t : ℝ => ν (productSlice Q a c t)) := by
  exact (measurable_measure_prodMk_left hQ).comp ((measurable_id.sub_const c).div_const a)

lemma affine_product_coarea {Q : Set (ℝ × F)} (hQ : MeasurableSet Q)
    {a : ℝ} (ha : 0 < a) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, ν (productSlice Q a c t)) =
      ENNReal.ofReal a * (volume.prod ν)
        (Q ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b}) := by
  classical
  let g : ℝ → ℝ≥0∞ := (Ioo r b).indicator (fun t => ν (productSlice Q a c t))
  have hg : Measurable g := (measurable_productSlice ν hQ a c).indicator measurableSet_Ioo
  have hs : MeasurableSet (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) := by
    exact hQ.inter ((measurableSet_lt measurable_const
      ((measurable_fst.const_mul a).add_const c)).inter
      (measurableSet_lt ((measurable_fst.const_mul a).add_const c) measurable_const))
  rw [← lintegral_indicator measurableSet_Ioo]
  change (∫⁻ t, g t) = _
  rw [lintegral_affine_change g hg (ne_of_gt ha) c, abs_of_pos ha, Measure.prod_apply hs]
  congr 1
  apply lintegral_congr
  intro s
  have he : (a * s + c - c) / a = s := by field_simp; ring
  by_cases h : r < a * s + c ∧ a * s + c < b
  · have hset : Prod.mk s ⁻¹' (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) =
        {z | (s,z) ∈ Q} := by ext z; simp [h]
    have hmem : a * s + c ∈ Ioo r b := h
    simp only [g, Set.indicator_of_mem hmem, productSlice, he, hset]
  · have hset : Prod.mk s ⁻¹' (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) = ∅ := by
      ext z; simp [h]
    have hmem : a * s + c ∉ Ioo r b := h
    simp only [g, Set.indicator_of_notMem hmem, hset, measure_empty]

end Product

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped InnerProductSpace

lemma normalParam_measurePreserving (u : E) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun p : ℝ × (ℝ ∙ u)ᗮ => p.1 • u + (p.2 : E))
      (volume.prod volume) volume := by
  have h := (normalParamIsometry u hu).measurePreserving.comp
    (WithLp.volume_preserving_toLp ℝ (ℝ ∙ u)ᗮ)
  convert! h using 1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma inner_normalParam (u : E) (hu : ‖u‖ = 1) (p : ℝ × (ℝ ∙ u)ᗮ) :
    ⟪u, p.1 • u + (p.2 : E)⟫_ℝ = p.1 := by
  rw [inner_add_right, inner_smul_right,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property,
    real_inner_self_eq_norm_sq, hu]
  ring

lemma euclidean_affine_coarea {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, euclideanSliceArea Q u a c t) =
      ENNReal.ofReal a * volume
        (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
  let φ : ℝ × (ℝ ∙ u)ᗮ → E := fun p => p.1 • u + (p.2 : E)
  have hφ : MeasurePreserving φ (volume.prod volume) volume := normalParam_measurePreserving u hu
  have hset : MeasurableSet
      (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
    have hf : Measurable (fun p => a * ⟪u, p⟫_ℝ + c) := by fun_prop
    exact hQ.inter ((measurableSet_lt measurable_const hf).inter
      (measurableSet_lt hf measurable_const))
  have hpre :
      φ ⁻¹' (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) =
      (φ ⁻¹' Q) ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, φ,
      inner_normalParam u hu p]
  calc
    _ = ENNReal.ofReal a * (volume.prod volume)
        ((φ ⁻¹' Q) ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b}) :=
      affine_product_coarea volume (hφ.measurable hQ) ha c r b
    _ = _ := by rw [← hpre, hφ.measure_preimage hset.nullMeasurableSet]

lemma euclidean_affine_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, euclideanSliceArea Q u a c t) ≤
      volume (Q ∩ {p | a * ⟪u, p⟫_ℝ + c ≤ b}) := by
  rw [euclidean_affine_coarea hQ u hu ha]
  calc
    _ ≤ 1 * volume (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
      gcongr
      simpa using ENNReal.ofReal_le_ofReal ha1
    _ ≤ _ := by
      rw [one_mul]
      exact measure_mono (fun p hp => ⟨hp.1, hp.2.2.le⟩)

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.HausdorffArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Euclidean Hausdorff area, so slices and lower-dimensional interfaces
are measured in the common ambient space, with Mathlib's exact normalization. -/

namespace BassTrace.Sparse

section

open MeasureTheory Set

open scoped ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma orthogonal_unit_rank (u : E) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ = Module.finrank ℝ E - 1 := by
  have hne : u ≠ 0 := by intro h; simp [h] at hu
  have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne] at h
  omega

lemma euclideanSliceArea_eq_area (Q : Set E) (u : E) (hu : ‖u‖ = 1)
    {a : ℝ} (ha : a ≠ 0) (c t : ℝ) :
    euclideanSliceArea Q u a c t =
      μHE[Module.finrank ℝ E - 1] (Q ∩ {p | a * ⟪u,p⟫_ℝ + c = t}) := by
  let φ : (ℝ ∙ u)ᗮ → E := fun z => ((t-c)/a) • u + (z : E)
  have hφ : Isometry φ := (isometry_add_left (((t-c)/a) • u)).comp isometry_subtype_coe
  have himage : φ '' {z | φ z ∈ Q} = Q ∩ {p | a * ⟪u,p⟫_ℝ+c=t} := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨hz,?_⟩
      dsimp [φ]
      rw [inner_normalParam u hu (((t-c)/a),z)]
      field_simp
      ring
    · rintro ⟨hp,ht⟩
      change a * ⟪u,p⟫_ℝ+c=t at ht
      have hpu : ⟪u,p⟫_ℝ = (t-c)/a := by apply (eq_div_iff ha).mpr; linarith
      have hz : p - ((t-c)/a) • u ∈ (ℝ ∙ u)ᗮ := by
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,hpu]
        ring
      refine ⟨⟨p - ((t-c)/a) • u,hz⟩,?_,?_⟩
      · dsimp [φ]
        simpa only [add_sub_cancel] using hp
      · dsimp [φ]
        abel
  rw [← himage,hφ.euclideanHausdorffMeasure_image]
  rw [← orthogonal_unit_rank u hu,InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rfl

lemma euclidean_area_affine_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
      (Q ∩ {p | a * ⟪u,p⟫_ℝ+c=t})) ≤
      μHE[Module.finrank ℝ E] (Q ∩ {p | a * ⟪u,p⟫_ℝ+c ≤ b}) := by
  simp_rw [← euclideanSliceArea_eq_area Q u hu ha.ne',
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact euclidean_affine_coarea_le hQ u hu ha ha1 c r b

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma euclidean_area_constant_slices (Q : Set E) (d : ℕ) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d] (Q ∩ { _p : E | c=t})) = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae ((volume : Measure ℝ).ae_ne c)] with t ht
  have he : { _p : E | c=t} = ∅ := by ext p; simp [Ne.symm ht]
  simp only [he,inter_empty,measure_empty,Pi.zero_apply]

lemma euclidean_area_gradient_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (g : E) (hg : ‖g‖ ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
      (Q ∩ {p | ⟪g,p⟫_ℝ+c=t})) ≤
      μHE[Module.finrank ℝ E] (Q ∩ {p | ⟪g,p⟫_ℝ+c ≤ b}) := by
  by_cases hzero : g = 0
  · subst g
    simp only [inner_zero_left,zero_add]
    rw [euclidean_area_constant_slices]
    exact bot_le
  · let u := (‖g‖⁻¹ : ℝ) • g
    have ha : 0 < ‖g‖ := norm_pos_iff.mpr hzero
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,ha.ne']
    have he (p : E) : ‖g‖ * ⟪u,p⟫_ℝ = ⟪g,p⟫_ℝ := by
      dsimp [u]
      rw [inner_smul_left]
      simp [ha.ne']
    simpa only [he] using euclidean_area_affine_coarea_le hQ u hu ha hg c r b

lemma measurable_euclidean_area_slices {Q : Set E} (hQ : MeasurableSet Q)
    (g : E) (c : ℝ) : Measurable (fun t : ℝ =>
      μHE[Module.finrank ℝ E - 1] (Q ∩ {p | ⟪g,p⟫_ℝ+c=t})) := by
  by_cases hz : g = 0
  · subst g
    have he : (fun t : ℝ => μHE[Module.finrank ℝ E - 1]
        (Q ∩ {p : E | ⟪(0:E),p⟫_ℝ+c=t})) =
        fun t => if t=c then μHE[Module.finrank ℝ E - 1] Q else 0 := by
      funext t
      by_cases ht : t=c
      · simp [ht]
      · simp [ht,Ne.symm ht]
    rw [he]
    exact Measurable.ite (measurableSet_singleton c) measurable_const measurable_const
  · let u := (‖g‖⁻¹ : ℝ) • g
    have ha : 0 < ‖g‖ := norm_pos_iff.mpr hz
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,ha.ne']
    have he (p : E) : ‖g‖ * ⟪u,p⟫_ℝ = ⟪g,p⟫_ℝ := by
      dsimp [u]
      rw [inner_smul_left]
      simp [ha.ne']
    let φ : ℝ × (ℝ ∙ u)ᗮ → E := fun p => p.1 • u + (p.2 : E)
    have hφ : Continuous φ := by fun_prop
    have hm := measurable_productSlice (volume : Measure (ℝ ∙ u)ᗮ)
      (hQ.preimage hφ.measurable) ‖g‖ c
    convert hm using 1
    funext t
    change _ = euclideanSliceArea Q u ‖g‖ c t
    rw [euclideanSliceArea_eq_area Q u hu ha.ne']
    simp_rw [he]

end

section

open MeasureTheory Set

open scoped ENNReal InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in

lemma exists_restricted_gradient (e : F →ᵃⁱ[ℝ] E) (g : E) (c : ℝ) :
    ∃ g' : F, ‖g'‖ ≤ ‖g‖ ∧ ∀ x,
      ⟪g,e x⟫_ℝ+c = ⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
  let l : F →L[ℝ] ℝ := (innerSL ℝ g).comp e.linearIsometry.toContinuousLinearMap
  let g' := (InnerProductSpace.toDual ℝ F).symm l
  have hg' (x : F) : ⟪g',x⟫_ℝ = ⟪g,e.linearIsometry x⟫_ℝ :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨g',?_,?_⟩
  · calc ‖g'‖ = ‖l‖ := (InnerProductSpace.toDual ℝ F).symm.norm_map l
         _ ≤ ‖g‖ := by
           apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
           intro x
           change ‖⟪g,e.linearIsometry x⟫_ℝ‖ ≤ ‖g‖*‖x‖
           simpa only [e.linearIsometry.norm_map] using norm_inner_le_norm g (e.linearIsometry x)
  · intro x
    have he : e x = e.linearIsometry x + e 0 := by
      have hh := e.map_vadd (0:F) x
      simpa only [vadd_eq_add,add_zero] using hh
    rw [he,inner_add_right,hg']
    ring

omit [FiniteDimensional ℝ E] in

lemma euclidean_area_embedded_coarea {Q : Set F} (hQ : MeasurableSet Q)
    (e : F →ᵃⁱ[ℝ] E) (f : E → ℝ) (g : F) (hg : ‖g‖ ≤ 1) (c : ℝ)
    (hbranch : ∀ x ∈ Q, f (e x) = ⟪g,x⟫_ℝ+c) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ F - 1]
      ((e '' Q) ∩ {p | f p=t})) ≤
      μHE[Module.finrank ℝ F] ((e '' Q) ∩ {p | f p ≤ b}) := by
  have hslice (t : ℝ) : (e '' Q) ∩ {p | f p=t} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c=t}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,(hbranch x hx).symm.trans ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(hbranch x hx).trans ht⟩
  have hball : (e '' Q) ∩ {p | f p ≤ b} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c ≤ b}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,by simpa only [Set.mem_ofPred_eq,← hbranch x hx] using ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,by simpa only [Set.mem_ofPred_eq,hbranch x hx] using ht⟩
  simp_rw [hslice,hball,e.isometry.euclideanHausdorffMeasure_image]
  exact euclidean_area_gradient_coarea_le hQ g hg c r b

omit [FiniteDimensional ℝ E] in
lemma measurable_embedded_slices {Q : Set F} (hQ : MeasurableSet Q)
    (e : F →ᵃⁱ[ℝ] E) (f : E → ℝ) (g : F) (c : ℝ)
    (hbranch : ∀ x ∈ Q, f (e x) = ⟪g,x⟫_ℝ+c) :
    Measurable (fun t : ℝ => μHE[Module.finrank ℝ F - 1]
      ((e '' Q) ∩ {p | f p=t})) := by
  have hslice (t : ℝ) : (e '' Q) ∩ {p | f p=t} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c=t}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,(hbranch x hx).symm.trans ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(hbranch x hx).trans ht⟩
  simp_rw [hslice,e.isometry.euclideanHausdorffMeasure_image]
  exact measurable_euclidean_area_slices hQ g c

end

open MeasureTheory Set Finset

open scoped ENNReal InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma extend_subspace_dimension (S : Submodule ℝ E) (d : ℕ)
    (hS : Module.finrank ℝ S ≤ d) (hd : d ≤ Module.finrank ℝ E) :
    ∃ W : Submodule ℝ E, S ≤ W ∧ Module.finrank ℝ W = d := by
  induction d, hS using Nat.le_induction with
  | base => exact ⟨S,le_rfl,rfl⟩
  | succ k hk ih =>
    obtain ⟨W,hSW,hW⟩ := ih (by omega)
    obtain ⟨v,hv⟩ := W.exists_of_finrank_lt (by omega)
    have hvW : v ∉ W := by simpa using hv 1 one_ne_zero
    exact ⟨W ⊔ Submodule.span ℝ {v},hSW.trans le_sup_left,by
      rw [Submodule.finrank_sup_span_singleton hvW,hW]⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma simplex_in_affine_isometry (s : Finset E) (hs : s.Nonempty) (d : ℕ)
    (hsd : s.card ≤ d+1) (hd : d ≤ Module.finrank ℝ E) :
    ∃ e : EuclideanSpace ℝ (Fin d) →ᵃⁱ[ℝ] E,
      convexHull ℝ (s : Set E) ⊆ Set.range e := by
  have hc : Fintype.card s = (s.card-1)+1 := by
    rw [Fintype.card_coe]; have := Finset.card_pos.mpr hs; omega
  have hdim := finrank_vectorSpan_range_le ℝ ((↑) : s → E) hc
  rw [Subtype.range_coe_subtype] at hdim
  obtain ⟨W,hW,hWd⟩ := extend_subspace_dimension (vectorSpan ℝ (s : Set E)) d
    (hdim.trans (by omega)) hd
  obtain ⟨c,hc⟩ := hs
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hWd)
  let l : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] E := W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let e : EuclideanSpace ℝ (Fin d) →ᵃⁱ[ℝ] E :=
    (AffineIsometryEquiv.vaddConst ℝ c).toAffineIsometry.comp l.toAffineIsometry
  refine ⟨e,?_⟩
  intro p hp
  have hspan : p-c ∈ W := by
    apply hW
    have hsp : vectorSpan ℝ (convexHull ℝ (s : Set E)) = vectorSpan ℝ (s : Set E) := by
      rw [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan]
    rw [← hsp]
    exact vsub_mem_vectorSpan ℝ hp (subset_convexHull ℝ (s : Set E) hc)
  refine ⟨b.repr ⟨p-c,hspan⟩,?_⟩
  change (↑(b.repr.symm (b.repr ⟨p-c,hspan⟩)) : E)+c=p
  rw [b.repr.symm_apply_apply]
  simp

lemma simplex_piece_coarea (s : Finset E) (d : ℕ) (hsd : s.card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E) {Q : Set E} (hQ : MeasurableSet Q)
    (hQs : Q ⊆ convexHull ℝ (s : Set E)) (f : E → ℝ) (g : E) (hg : ‖g‖ ≤ 1)
    (c : ℝ) (hf : ∀ p ∈ Q, f p=⟪g,p⟫_ℝ+c) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] (Q ∩ {p | f p=t})) ≤
      μHE[d] (Q ∩ {p | f p ≤ b}) := by
  by_cases hs : s.Nonempty
  · obtain ⟨e,he⟩ := simplex_in_affine_isometry s hs d hsd hd
    have hQr : Q ⊆ Set.range e := hQs.trans he
    have heQ : e '' (e ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset hQr
    obtain ⟨g',hg',hb⟩ := exists_restricted_gradient e g c
    have hbranch : ∀ x ∈ e ⁻¹' Q, f (e x)=⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
      intro x hx; rw [hf _ hx,hb]
    have hh := euclidean_area_embedded_coarea (e.continuous.measurable hQ)
      e f g' (hg'.trans hg) (⟪g,e 0⟫_ℝ+c) hbranch r b
    simpa only [heQ,finrank_euclideanSpace_fin] using hh
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hQe : Q=∅ := by apply Set.eq_empty_of_subset_empty; simpa [he] using hQs
    simp [hQe]

lemma measurable_simplex_piece_slices (s : Finset E) (d : ℕ) (hsd : s.card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E) {Q : Set E} (hQ : MeasurableSet Q)
    (hQs : Q ⊆ convexHull ℝ (s : Set E)) (f : E → ℝ) (g : E)
    (c : ℝ) (hf : ∀ p ∈ Q, f p=⟪g,p⟫_ℝ+c) :
    Measurable (fun t : ℝ => μHE[d-1] (Q ∩ {p | f p=t})) := by
  by_cases hs : s.Nonempty
  · obtain ⟨e,he⟩ := simplex_in_affine_isometry s hs d hsd hd
    have hQr : Q ⊆ Set.range e := hQs.trans he
    have heQ : e '' (e ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset hQr
    obtain ⟨g',_,hb⟩ := exists_restricted_gradient e g c
    have hbranch : ∀ x ∈ e ⁻¹' Q, f (e x)=⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
      intro x hx; rw [hf _ hx,hb]
    have hh := measurable_embedded_slices (e.continuous.measurable hQ)
      e f g' (⟪g,e 0⟫_ℝ+c) hbranch
    simpa only [heQ,finrank_euclideanSpace_fin] using hh
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hQe : Q=∅ := by apply Set.eq_empty_of_subset_empty; simpa [he] using hQs
    simp only [hQe,Set.empty_inter,measure_empty]
    exact measurable_const

lemma finite_polyhedral_coarea {k : ℕ} (s : Fin k → Finset E) (d : ℕ)
    (hs : ∀ i, (s i).card ≤ d+1) (hd : d ≤ Module.finrank ℝ E)
    (Q : Fin k → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E)) (f : E → ℝ)
    (g : Fin k → E) (hg : ∀ i, ‖g i‖ ≤ 1) (c : Fin k → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p=⟪g i,p⟫_ℝ+c i) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  let W := disjointed Q
  have hW (i : Fin k) : MeasurableSet (W i) :=
    disjointedRec (fun _ j ht => ht.diff (hQ j)) (hQ i)
  have hsub (i : Fin k) : W i ⊆ Q i := disjointed_subset Q i
  have hcover : (⋃ i, W i) = ⋃ i, Q i := iUnion_disjointed
  have hdisj : Pairwise fun i j => Disjoint (W i) (W j) := disjoint_disjointed Q
  have hslice (t : ℝ) : ((⋃ i,W i) ∩ {p | f p=t}) =
      ⋃ i, W i ∩ {p | f p=t} := Set.iUnion_inter _ _
  have hball : ((⋃ i,W i) ∩ {p | f p ≤ b}) =
      ⋃ i, W i ∩ {p | f p ≤ b} := Set.iUnion_inter _ _
  have hm (i : Fin k) : MeasurableSet (W i ∩ {p | f p ≤ b}) := by
    have he : W i ∩ {p | f p ≤ b} = W i ∩ {p | ⟪g i,p⟫_ℝ+c i ≤ b} := by
      ext p; constructor <;> rintro ⟨hp,ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,← hf i p (hsub i hp)] using ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,hf i p (hsub i hp)] using ht⟩
    rw [he]
    exact (hW i).inter (measurableSet_le (by fun_prop) measurable_const)
  rw [← hcover]
  calc
    _ ≤ ∫⁻ t in Ioo r b, ∑ i, μHE[d-1] (W i ∩ {p | f p=t}) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [hslice]
      simpa only [tsum_fintype] using measure_iUnion_le (μ := μHE[d-1])
        (fun i => W i ∩ {p | f p=t})
    _ = ∑ i, ∫⁻ t in Ioo r b, μHE[d-1] (W i ∩ {p | f p=t}) := by
      apply lintegral_finsetSum
      intro i _
      exact measurable_simplex_piece_slices (s i) d (hs i) hd (hW i)
        ((hsub i).trans (hQs i)) f (g i) (c i) (fun p hp => hf i p (hsub i hp))
    _ ≤ ∑ i, μHE[d] (W i ∩ {p | f p ≤ b}) := by
      apply Finset.sum_le_sum
      intro i _
      exact simplex_piece_coarea (s i) d (hs i) hd (hW i)
        ((hsub i).trans (hQs i)) f (g i) (hg i) (c i) (fun p hp => hf i p (hsub i hp)) r b
    _ = _ := by
      rw [hball,measure_iUnion]
      · exact (tsum_fintype _).symm
      · intro i j hij
        exact (hdisj hij).mono inter_subset_left inter_subset_left
      · exact hm

lemma finite_affine_coarea {I : Type*} [Fintype I]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : I → E) (hg : ∀ i, ‖g i‖ ≤ 1) (c : I → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  classical
  let e := (Fintype.equivFin I).symm
  have he : (⋃ j, Q (e j)) = ⋃ i, Q i := e.surjective.iUnion_comp Q
  rw [← he]
  exact finite_polyhedral_coarea (fun j => s (e j)) d (fun j => hs (e j)) hd
    (fun j => Q (e j)) (fun j => hQ (e j)) (fun j => hQs (e j)) f
    (fun j => g (e j)) (fun j => hg (e j)) (fun j => c (e j))
    (fun j => hf (e j)) r b

lemma finite_max_coarea {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (g : I → J → E) (hg : ∀ i j, ‖g i j‖ ≤ 1) (c : I → J → ℝ)
    (f : E → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = Finset.univ.sup' Finset.univ_nonempty
      (fun j => ⟪g i j,p⟫_ℝ+c i j)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  classical
  let W (a : I × J) := Q a.1 ∩ ⋂ j, {p | ⟪g a.1 j,p⟫_ℝ+c a.1 j ≤
    ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2}
  have hW (a : I × J) : MeasurableSet (W a) := by
    exact (hQ a.1).inter (MeasurableSet.iInter fun j =>
      measurableSet_le (by fun_prop) (by fun_prop))
  have hWQ (a : I × J) : W a ⊆ Q a.1 := inter_subset_left
  have hcover : (⋃ a, W a) = ⋃ i, Q i := by
    apply Set.Subset.antisymm
    · simp only [iUnion_subset_iff]
      intro a
      exact (hWQ a).trans (subset_iUnion Q a.1)
    · intro p hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j => ⟪g i j,p⟫_ℝ+c i j)
      apply Set.mem_iUnion.mpr
      refine ⟨(i,j),hi,Set.mem_iInter.mpr ?_⟩
      intro l
      change ⟪g i l,p⟫_ℝ+c i l ≤ ⟪g i j,p⟫_ℝ+c i j
      rw [← hj]
      exact Finset.le_sup' (fun j => ⟪g i j,p⟫_ℝ+c i j) (Finset.mem_univ l)
  have hbranch (a : I × J) (p : E) (hp : p ∈ W a) :
      f p = ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2 := by
    rw [hf a.1 p hp.1]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => Set.mem_iInter.mp hp.2 j)
    · exact Finset.le_sup' (fun j => ⟪g a.1 j,p⟫_ℝ+c a.1 j) (Finset.mem_univ a.2)
  rw [← hcover]
  exact finite_affine_coarea (fun a => s a.1) d (fun a => hs a.1) hd W hW
    (fun a => (hWQ a).trans (hQs a.1)) f (fun a => g a.1 a.2)
    (fun a => hg a.1 a.2) (fun a => c a.1 a.2) hbranch r b

lemma measurable_finite_polyhedral_slices {k : ℕ}
    (s : Fin k → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : Fin k → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : Fin k → E) (c : Fin k → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  let W := disjointed Q
  have hW (i : Fin k) : MeasurableSet (W i) :=
    disjointedRec (fun _ j ht => ht.diff (hQ j)) (hQ i)
  have hsub (i : Fin k) : W i ⊆ Q i := disjointed_subset Q i
  have hcover : (⋃ i, W i) = ⋃ i, Q i := iUnion_disjointed
  have hdisj : Pairwise fun i j => Disjoint (W i) (W j) := disjoint_disjointed Q
  have hm (i : Fin k) (t : ℝ) : MeasurableSet (W i ∩ {p | f p=t}) := by
    have he : W i ∩ {p | f p=t} = W i ∩ {p | ⟪g i,p⟫_ℝ+c i=t} := by
      ext p
      constructor <;> rintro ⟨hp,ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,← hf i p (hsub i hp)] using ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,hf i p (hsub i hp)] using ht⟩
    rw [he]
    exact (hW i).inter (measurableSet_eq_fun (by fun_prop) measurable_const)
  have he (t : ℝ) : μHE[d-1] ((⋃ i,Q i) ∩ {p | f p=t}) =
      ∑ i, μHE[d-1] (W i ∩ {p | f p=t}) := by
    rw [← hcover,Set.iUnion_inter,measure_iUnion]
    · exact tsum_fintype _
    · intro i j hij
      exact (hdisj hij).mono inter_subset_left inter_subset_left
    · intro i
      exact hm i t
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  exact measurable_simplex_piece_slices (s i) d (hs i) hd (hW i)
    ((hsub i).trans (hQs i)) f (g i) (c i) (fun p hp => hf i p (hsub i hp))

lemma measurable_finite_affine_slices {I : Type*} [Fintype I]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : I → E) (c : I → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  classical
  let e := (Fintype.equivFin I).symm
  have he : (⋃ j, Q (e j)) = ⋃ i, Q i := e.surjective.iUnion_comp Q
  rw [← he]
  exact measurable_finite_polyhedral_slices (fun j => s (e j)) d (fun j => hs (e j)) hd
    (fun j => Q (e j)) (fun j => hQ (e j)) (fun j => hQs (e j)) f
    (fun j => g (e j)) (fun j => c (e j)) (fun j => hf (e j))

lemma measurable_finite_max_slices {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (g : I → J → E) (c : I → J → ℝ) (f : E → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = Finset.univ.sup' Finset.univ_nonempty
      (fun j => ⟪g i j,p⟫_ℝ+c i j)) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  classical
  let W (a : I × J) := Q a.1 ∩ ⋂ j, {p | ⟪g a.1 j,p⟫_ℝ+c a.1 j ≤
    ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2}
  have hW (a : I × J) : MeasurableSet (W a) := by
    exact (hQ a.1).inter (MeasurableSet.iInter fun j =>
      measurableSet_le (by fun_prop) (by fun_prop))
  have hWQ (a : I × J) : W a ⊆ Q a.1 := inter_subset_left
  have hcover : (⋃ a, W a) = ⋃ i, Q i := by
    apply Set.Subset.antisymm
    · simp only [iUnion_subset_iff]
      intro a
      exact (hWQ a).trans (subset_iUnion Q a.1)
    · intro p hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j => ⟪g i j,p⟫_ℝ+c i j)
      apply Set.mem_iUnion.mpr
      refine ⟨(i,j),hi,Set.mem_iInter.mpr ?_⟩
      intro l
      change ⟪g i l,p⟫_ℝ+c i l ≤ ⟪g i j,p⟫_ℝ+c i j
      rw [← hj]
      exact Finset.le_sup' (fun j => ⟪g i j,p⟫_ℝ+c i j) (Finset.mem_univ l)
  have hbranch (a : I × J) (p : E) (hp : p ∈ W a) :
      f p = ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2 := by
    rw [hf a.1 p hp.1]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => Set.mem_iInter.mp hp.2 j)
    · exact Finset.le_sup' (fun j => ⟪g a.1 j,p⟫_ℝ+c a.1 j) (Finset.mem_univ a.2)
  rw [← hcover]
  exact measurable_finite_affine_slices (fun a => s a.1) d (fun a => hs a.1) hd W hW
    (fun a => (hWQ a).trans (hQs a.1)) f (fun a => g a.1 a.2)
    (fun a => c a.1 a.2) hbranch

end

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.SimplexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open MeasureTheory Set Finset

open scoped ENNReal InnerProductSpace

lemma barycentricParam_potential {n : ℕ} (ℓ : Fin (n+1) → ℝ) (x : Fin n → ℝ) :
    ∑ i, ℓ i * barycentricParam x i = ℓ 0 + ∑ i, (ℓ i.succ-ℓ 0)*x i := by
  rw [Fin.sum_univ_succ]
  simp only [barycentricParam_zero,barycentricParam_succ,sub_mul,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

lemma treeParam_potential {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (ℓ : Fin (n+1) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ℓ i * treeParam T hT x i) / Real.sqrt n =
      ⟪treeGradient T hT ℓ,x⟫_ℝ + ℓ 0 / Real.sqrt n := by
  rw [treeParam,barycentricParam_potential,add_div,treeChart_potential]
  rw [real_inner_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  ring

lemma treeArea_coarea {n : ℕ} (hn : 0<n)
    (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (hℓ : ∀ i j u v, T.Adj u v → |ℓ i j u-ℓ i j v|≤1)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, treeArea T hT (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) ≤
      treeArea T hT d ((⋃ i,Q i) ∩ {p | f p≤b}) := by
  classical
  let s' i := (s i).image (treeCoordinates T hT)
  let Q' i := treeParam T hT ⁻¹' Q i
  have hQs' (i : I) : Q' i ⊆ convexHull ℝ (s' i : Set (EuclideanSpace ℝ (Fin n))) := by
    have hh := Set.preimage_mono (f := treeParam T hT) (hQs i)
    rw [treeParam_preimage_simplex T hT (s i) (hplane i)] at hh
    simpa only [s',Finset.coe_image] using hh
  have hh := finite_max_coarea s' d (fun i => (Finset.card_image_le).trans (hs i))
    (by simpa only [finrank_euclideanSpace_fin] using hd) Q'
    (fun i => (hQ i).preimage (continuous_treeParam T hT).measurable) hQs'
    (fun i j => treeGradient T hT (ℓ i j))
    (fun i j => treeGradient_norm_le_one hn T hT (ℓ i j) (hℓ i j))
    (fun i j => ℓ i j 0 / Real.sqrt n) (f ∘ treeParam T hT)
    (fun i p hp => by
      rw [Function.comp_apply,hf i _ hp]
      congr 1
      funext j
      exact treeParam_potential T hT (ℓ i j) p) r b
  simpa only [treeArea,Set.preimage_inter,Set.preimage_iUnion,Set.preimage_ofPred_eq,
    Function.comp_apply,Q'] using hh

lemma measurable_treeArea_slices {n : ℕ}
    (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) :
    Measurable (fun t => treeArea T hT (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) := by
  classical
  let s' i := (s i).image (treeCoordinates T hT)
  let Q' i := treeParam T hT ⁻¹' Q i
  have hQs' (i : I) : Q' i ⊆ convexHull ℝ (s' i : Set (EuclideanSpace ℝ (Fin n))) := by
    have hh := Set.preimage_mono (f := treeParam T hT) (hQs i)
    rw [treeParam_preimage_simplex T hT (s i) (hplane i)] at hh
    simpa only [s',Finset.coe_image] using hh
  have hh := measurable_finite_max_slices s' d (fun i => (Finset.card_image_le).trans (hs i))
    (by simpa only [finrank_euclideanSpace_fin] using hd) Q'
    (fun i => (hQ i).preimage (continuous_treeParam T hT).measurable) hQs'
    (fun i j => treeGradient T hT (ℓ i j))
    (fun i j => ℓ i j 0 / Real.sqrt n) (f ∘ treeParam T hT)
    (fun i p hp => by
      rw [Function.comp_apply,hf i _ hp]
      congr 1
      funext j
      exact treeParam_potential T hT (ℓ i j) p)
  simpa only [treeArea,Set.preimage_inter,Set.preimage_iUnion,Set.preimage_ofPred_eq,
    Function.comp_apply,Q'] using hh

lemma simplexArea_coarea {n : ℕ} (hn : 0<n)
    (Γ : SimpleGraph (Fin (n+1)))
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (hℓ : ∀ i j u v, Γ.Adj u v → |ℓ i j u-ℓ i j v|≤1)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) ≤
      simplexArea Γ d ((⋃ i,Q i) ∩ {p | f p≤b}) := by
  classical
  have hm (T : SpanningTree Γ) := measurable_treeArea_slices T.val T.property.2
    s d hs hd hplane Q hQ hQs ℓ f hf
  simp only [simplexArea,div_eq_mul_inv]
  rw [lintegral_mul_const _ (Finset.measurable_sum _ (fun T _ => hm T)),
    lintegral_finsetSum _ (fun T _ => hm T)]
  apply mul_le_mul_left
  apply Finset.sum_le_sum
  intro T _
  exact treeArea_coarea hn T.val T.property.2 s d hs hd hplane Q hQ hQs ℓ
    (fun i j u v huv => hℓ i j u v (T.property.1 huv)) f hf r b

lemma measurable_simplexArea_slices {n : ℕ}
    (Γ : SimpleGraph (Fin (n+1)))
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) :
    Measurable (fun t => simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) := by
  classical
  unfold simplexArea
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun T _ => measurable_treeArea_slices T.val T.property.2
    s d hs hd hplane Q hQ hQs ℓ f hf)

end

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y : Type*} [DecidableEq Y]

variable [MetricSpace Y]

lemma chartDistance_apply {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (c : FinProbability Y) (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) :
    chartDistance s hs c p = FinProbability.rho n c (simplexPoint s hs p hp) := by
  simp only [chartDistance,dite_eq_left hp]

omit [MetricSpace Y] in
lemma ballBranch_coordinates {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (l : S→ℝ) (p : Fin (n+1) → ℝ) :
    ballBranch S c n l (simplexEmbed s hs p) =
      (∑ i,(centerBranchValue S c l-l ⟨(simplexEnumeration s hs i).val,
        hsS (simplexEnumeration s hs i).property⟩)*p i)/Real.sqrt n := by
  rw [ballBranch_apply]
  have hm : ∑ y : S,((centerBranchValue S c l-l y)/Real.sqrt n)*simplexEmbed s hs p y =
      ∑ y : s,((centerBranchValue S c l-l ⟨y.val,hsS y.property⟩)/Real.sqrt n)*
        simplexEmbed s hs p y := by
    apply Finset.sum_bij_ne_zero (fun y _ _ => ⟨y.val,by
      by_contra hy
      have hzero := Finsupp.notMem_support_iff.mp
        (fun h => hy (simplexEmbed_support s hs p h))
      simp [hzero] at *⟩)
    · intros; simp
    · intro a ha hna b hb hnb he
      exact Subtype.ext (congrArg (fun z : s => z.val) he)
    · intro y _ hy
      exact ⟨⟨y.val,hsS y.property⟩,by simp,by simpa using hy,rfl⟩
    · intros; rfl
  rw [hm,← (simplexEnumeration s hs).sum_comp]
  simp_rw [show ∀ i, simplexEmbed s hs p (simplexEnumeration s hs i).val=p i from
    fun i=>congrFun (simplexCoordinates_embed s hs p) i,
    div_mul_eq_mul_div,Finset.sum_div]

omit [DecidableEq Y] in
lemma distancePotential_edge {n : ℕ} (s S : Finset Y) (hs : s.card=n+1)
    (hsS : s⊆S) (c : FinProbability Y) (l : S→ℝ) (hl : l∈potentialVertices)
    (u v : Fin (n+1))
    (huv : dist (simplexEnumeration s hs u).val (simplexEnumeration s hs v).val≤1) :
    |distancePotential s S hs hsS c l u-distancePotential s S hs hsS c l v|≤1 := by
  have hh := (potentialVertices_subset l hl).2
    ⟨(simplexEnumeration s hs v).val,hsS (simplexEnumeration s hs v).property⟩
    ⟨(simplexEnumeration s hs u).val,hsS (simplexEnumeration s hs u).property⟩
  unfold distancePotential
  rw [show ∀ a b d : ℝ,(a-b)-(a-d)=d-b from by intros; ring]
  exact hh.trans (by simpa only [Subtype.dist_eq,dist_comm] using huv)

lemma chartDistance_max {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (hc : c.coeff.support⊆S)
    [Nonempty (potentialVertices : Finset (S→ℝ))]
    (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) :
    chartDistance s hs c p=Finset.univ.sup' Finset.univ_nonempty
      (fun l : (potentialVertices : Finset (S→ℝ)) =>
        (∑ i,distancePotential s S hs hsS c l.val i*p i)/Real.sqrt n) := by
  have hpS : (simplexPoint s hs p hp).coeff.support⊆S :=
    (simplexEmbed_support s hs p).trans hsS
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer S c (simplexPoint s hs p hp) hc hpS n
  rw [chartDistance_apply s hs c p hp]
  apply le_antisymm
  · rw [heq]
    change ballBranch S c n l (simplexEmbed s hs p)≤_
    rw [ballBranch_coordinates s S hs hsS]
    change (∑ i,distancePotential s S hs hsS c l i*p i)/Real.sqrt n ≤ _
    exact Finset.le_sup' (fun l : (potentialVertices : Finset (S→ℝ)) =>
      (∑ i,distancePotential s S hs hsS c l.val i*p i)/Real.sqrt n)
      (Finset.mem_univ (⟨l,hl⟩ : (potentialVertices : Finset (S→ℝ))))
  · apply Finset.sup'_le
    intro l _
    have hh := hmax l.val l.property
    change ballBranch S c n l.val (simplexEmbed s hs p)≤_ at hh
    simpa only [ballBranch_coordinates s S hs hsS,distancePotential] using hh

theorem graphBall_coarea {n : ℕ} (hn : 0<n)
    (σ : Finset Y) (hσ : σ.card=n+1) (c : FinProbability Y)
    (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : ∀ u v, Γ.Adj u v →
      dist (simplexEnumeration σ hσ u).val (simplexEnumeration σ hσ v).val≤1)
    {I : Type*} [Fintype I]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i,(s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p,p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i,MeasurableSet (Q i))
    (hQs : ∀ i,Q i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (hfull : ∀ i,Q i⊆fullBarycentricSimplex n) (r b : ℝ) :
    (∫⁻ t in Ioo r b, simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p=t})) ≤
      simplexArea Γ d ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p≤b}) := by
  let S := σ ∪ c.coeff.support
  have hσS : σ⊆S := Finset.subset_union_left
  have hcS : c.coeff.support⊆S := Finset.subset_union_right
  obtain ⟨l,hl,-⟩ := exists_ballBranch_maximizer S c c hcS hcS n
  let : Nonempty (potentialVertices : Finset (S→ℝ)) := ⟨⟨l,hl⟩⟩
  exact simplexArea_coarea hn Γ s d hs hd hplane Q hQ hQs
    (fun _ (l : (potentialVertices : Finset (S→ℝ))) => distancePotential σ S hσ hσS c l.val)
    (fun _ l u v huv => distancePotential_edge σ S hσ hσS c l.val l.property u v (hΓ u v huv))
    (chartDistance σ hσ c) (fun i p hp => chartDistance_max σ S hσ hσS c hcS p (hfull i hp)) r b

lemma measurable_graphBall_slices {n : ℕ}
    (σ : Finset Y) (hσ : σ.card=n+1) (c : FinProbability Y)
    (Γ : SimpleGraph (Fin (n+1))) {I : Type*} [Fintype I]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i,(s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p,p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i,MeasurableSet (Q i))
    (hQs : ∀ i,Q i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (hfull : ∀ i,Q i⊆fullBarycentricSimplex n) :
    Measurable (fun t => simplexArea Γ (d-1)
      ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p=t})) := by
  let S := σ ∪ c.coeff.support
  have hσS : σ⊆S := Finset.subset_union_left
  have hcS : c.coeff.support⊆S := Finset.subset_union_right
  obtain ⟨l,hl,-⟩ := exists_ballBranch_maximizer S c c hcS hcS n
  let : Nonempty (potentialVertices : Finset (S→ℝ)) := ⟨⟨l,hl⟩⟩
  exact measurable_simplexArea_slices Γ s d hs hd hplane Q hQ hQs
    (fun _ (l : (potentialVertices : Finset (S→ℝ))) => distancePotential σ S hσ hσS c l.val)
    (chartDistance σ hσ c) (fun i p hp => chartDistance_max σ S hσ hσS c hcS p (hfull i hp))

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.MeasurableSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma measurable_intrinsicInterior_finite_hull [MeasurableSpace V] [BorelSpace V]
    (s : Finset V) : MeasurableSet (intrinsicInterior ℝ (convexHull ℝ (s : Set V))) := by
  have hA : IsClosed ((affineSpan ℝ (convexHull ℝ (s : Set V))) : Set V) := by
    rw [affineSpan_convexHull]
    let := finiteDimensional_direction_affineSpan_of_finite ℝ s.finite_toSet
    exact (affineSpan ℝ (s : Set V)).closed_of_finiteDimensional
  exact (hA.isClosedEmbedding_subtypeVal.measurableEmbedding.measurableSet_image).mpr
    isOpen_interior.measurableSet

end

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

lemma support_of_mem_original_hull (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) : p.support⊆s := by
  have hprob : p∈probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  exact hprob.2.2

lemma simplexCoordinates_full {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    simplexCoordinates s hs p∈fullBarycentricSimplex n := by
  have hprob : p∈probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  exact ⟨fun i => hprob.1 _,simplexCoordinates_sum s hs hp⟩

lemma marked_chart_pieces (Q : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (d : ℕ) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    ∃ (I : Type) (_ : Fintype I) (s : I → Finset (Fin (n+1) → ℝ))
      (A : I → Set (Fin (n+1) → ℝ)),
      (∀ i,(s i).card≤d+1) ∧
      (∀ i p,p∈s i → ∑ v,p v=1) ∧
      (∀ i,MeasurableSet (A i)) ∧
      (∀ i,A i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ))) ∧
      (∀ i,A i⊆fullBarycentricSimplex n) ∧
      (⋃ i,A i)=simplexCoordinates σ.val σ.property.2 '' (Q.P.val x∩sourceInterior σ.val) := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  let η := simplexCoordinates σ.val σ.property.2
  let e := simplexEmbed σ.val σ.property.2
  let L := Cuts.restrictComplex (Cuts.geometricRestriction (Q.T.val x).complex (Q.P.val x))
    (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))
  have hf : L.faces.Finite := ((Q.T.val x).finite (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩).subset (fun _ h => ⟨h.1.1,h.2⟩)
  let F := hf.toFinset
  let I := Fin F.card
  let α : I ≃ {t // t∈L.faces} :=
    (F.equivFin).symm.trans (Equiv.subtypeEquivProp (by ext t; exact hf.mem_toFinset))
  let s (i : I) := (α i).val.image η
  let A (i : I) := convexHull ℝ (s i : Set (Fin (n+1) → ℝ)) ∩ e ⁻¹' sourceInterior σ.val
  have hsource (i : I) : convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) ⊆
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)) :=
    convexHull_min (α i).property.2 (convex_convexHull ℝ _)
  have himage (i : I) : convexHull ℝ (s i : Set (Fin (n+1) → ℝ)) =
      η '' convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) := by
    change convexHull ℝ (((α i).val.image η : Finset (Fin (n+1) → ℝ)) : Set (Fin (n+1) → ℝ)) = _
    rw [Finset.coe_image,← η.image_convexHull]
  have hin (i : I) {p : Fin (n+1) → ℝ}
      (hp : p∈convexHull ℝ (s i : Set (Fin (n+1) → ℝ))) :
      e p∈convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) := by
    rw [himage i] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 q)∈_
    rw [simplexEmbed_coordinates _ _ (support_of_mem_original_hull _ (hsource i hq))]
    exact hq
  refine ⟨I,inferInstance,s,A,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact Finset.card_image_le.trans (hd _ (α i).property.1.1 (α i).property.1.2)
  · intro i p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact simplexCoordinates_sum _ _ ((α i).property.2 hq)
  · intro i
    exact ((s i).finite_toSet.isCompact_convexHull ℝ).isClosed.measurableSet.inter
      ((measurable_intrinsicInterior_finite_hull (simplexVertices σ.val)).preimage
        e.continuous_of_finiteDimensional.measurable)
  · exact fun _ => Set.inter_subset_left
  · intro i p hp
    have hp' := hp.1
    rw [himage i] at hp'
    obtain ⟨q,hq,rfl⟩ := hp'
    exact simplexCoordinates_full _ _ (hsource i hq)
  · apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨i,hp⟩ := Set.mem_iUnion.mp hp
      refine ⟨e p,⟨(α i).property.1.2 (hin i hp.1),hp.2⟩,?_⟩
      exact simplexCoordinates_embed _ _ p
    · rintro _ ⟨p,hp,rfl⟩
      have hpL : p∈L.space := by
        change p∈(Cuts.restrictComplex (Cuts.geometricRestriction (Q.T.val x).complex (Q.P.val x))
          (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).space
        rw [Q.P.trace_space (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩ x]
        exact ⟨hp.1,intrinsicInterior_subset hp.2⟩
      obtain ⟨t,ht,hpt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hpL
      obtain ⟨i,hi⟩ := α.surjective ⟨t,ht⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i,?_,?_⟩
      · rw [himage i,hi]
        exact ⟨p,hpt,rfl⟩
      · change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 p)∈sourceInterior σ.val
        rw [simplexEmbed_coordinates _ _ (support_of_mem_sourceInterior _ hp.2)]
        exact hp.2

end

open Set MeasureTheory

open scoped ENNReal

lemma IsLocallyConstant.measurable_uncurry {X A Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] {f : X → A} (hf : IsLocallyConstant f)
    (F : A → Y → ℝ≥0∞) (hF : ∀ a∈Set.range f,Measurable (F a)) :
    Measurable (fun p : X×Y => F (f p.1) p.2) := by
  classical
  let S := hf.range_finite.toFinset
  have he : (fun p : X×Y => F (f p.1) p.2) =
      fun p => ∑ a∈S, ({q : X×Y | f q.1=a}.indicator (fun q=>F a q.2)) p := by
    funext p
    rw [Finset.sum_eq_single (f p.1)]
    · simp
    · intro a _ ha
      exact Set.indicator_of_notMem (by exact Ne.symm ha) _
    · intro h
      exact (h (hf.range_finite.mem_toFinset.mpr (Set.mem_range_self _))).elim
  rw [he]
  apply Finset.measurable_sum
  intro a ha
  apply ((hF a (hf.range_finite.mem_toFinset.mp ha)).comp measurable_snd).indicator
  exact ((hf.isClopen_fiber a).isOpen.measurableSet.preimage measurable_fst)

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma chartDistance_coordinates (σ : SourceTop K n) (c : FinProbability Y)
    {p : Y →₀ ℝ} (hp : p∈sourceInterior σ.val) :
    letI := graphMetric Γ hΓ
    chartDistance σ.val σ.property.2 c (simplexCoordinates σ.val σ.property.2 p) =
      centerDistance Γ hΓ K n c p := by
  let := graphMetric Γ hΓ
  have hpK : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨simplexVertices σ.val,⟨σ.val,σ.property.1,rfl⟩,intrinsicInterior_subset hp⟩
  rw [chartDistance_apply _ _ _ _ (simplexCoordinates_full _ _ (intrinsicInterior_subset hp))]
  simp only [centerDistance,dite_eq_left hpK]
  congr 1
  apply FinProbability.ext_coeff
  change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 p) = _
  rw [simplexEmbed_coordinates _ _ (support_of_mem_sourceInterior _ hp),pointProbability_coeff]

omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma coordinates_radius_inter (σ : SourceTop K n) (c : FinProbability Y)
    (A : Set (Y →₀ ℝ)) (hA : A⊆sourceInterior σ.val) (R : Set ℝ) :
    letI := graphMetric Γ hΓ
    simplexCoordinates σ.val σ.property.2 '' (A∩(centerDistance Γ hΓ K n c ⁻¹' R)) =
    (simplexCoordinates σ.val σ.property.2 '' A) ∩
      (chartDistance σ.val σ.property.2 c ⁻¹' R) := by
  let := graphMetric Γ hΓ
  ext p
  constructor
  · rintro ⟨q,⟨hq,hqR⟩,rfl⟩
    refine ⟨⟨q,hq,rfl⟩,?_⟩
    simpa only [Set.mem_preimage,chartDistance_coordinates Γ hΓ σ c (hA hq)] using hqR
  · rintro ⟨⟨q,hq,rfl⟩,hpR⟩
    refine ⟨q,⟨hq,?_⟩,rfl⟩
    simpa only [Set.mem_preimage,chartDistance_coordinates Γ hΓ σ c (hA hq)] using hpR

theorem marked_ball_coarea (hn : 0<n)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) (r b : ℝ) :
    (∫⁻ t in Ioo r b,localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=t} x) ≤
      localOriginalArea Γ Q σ d {v | centerDistance Γ hΓ K n c v≤b} x := by
  let := graphMetric Γ hΓ
  obtain ⟨I,hI,s,A,hs,hplane,hA,hAs,hfull,he⟩ := marked_chart_pieces Q σ d x hd
  let : Fintype I := hI
  have hgraph (u v : Fin (n+1)) (huv : (simplexGraph Γ σ.val σ.property.2).Adj u v) :
      dist (simplexEnumeration σ.val σ.property.2 u).val
        (simplexEnumeration σ.val σ.property.2 v).val≤1 := by
    change (Γ.dist _ _ : ℝ)≤1
    exact_mod_cast (SimpleGraph.dist_eq_one_iff_adj.mpr (show Γ.Adj _ _ from huv)).le
  have hc := graphBall_coarea hn σ.val σ.property.2 c
    (simplexGraph Γ σ.val σ.property.2) hgraph s d hs hdn hplane A hA hAs hfull r b
  rw [he] at hc
  convert hc using 1
  · congr 1
    funext t
    unfold localOriginalArea
    congr 1
    simpa only [Set.inter_assoc, Set.preimage, Set.mem_singleton_iff] using
      coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
        Set.inter_subset_right {t}
  · unfold localOriginalArea
    congr 1
    simpa only [Set.inter_assoc, Set.preimage, Set.mem_Iic] using
      coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
        Set.inter_subset_right (Iic b)

lemma measurable_marked_ball_slices
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    Measurable (fun t => localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=t} x) := by
  let := graphMetric Γ hΓ
  obtain ⟨I,hI,s,A,hs,hplane,hA,hAs,hfull,he⟩ := marked_chart_pieces Q σ d x hd
  let : Fintype I := hI
  have hc := measurable_graphBall_slices σ.val σ.property.2 c
    (simplexGraph Γ σ.val σ.property.2) s d hs hdn hplane A hA hAs hfull
  rw [he] at hc
  convert hc using 1
  funext t
  unfold localOriginalArea
  congr 1
  simpa only [Set.inter_assoc, Set.preimage, Set.mem_singleton_iff] using
    coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
      Set.inter_subset_right {t}

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

lemma measurable_marked_ball_slices_joint
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    Measurable (fun p : X×ℝ => localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=p.2} p.1) := by
  let f (x : X) := Q.P.val x∩sourceInterior σ.val
  have hf : IsLocallyConstant f := Q.P.localConstancy_inter (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩ _ intrinsicInterior_subset
  let F (A : Set (Y →₀ ℝ)) (t : ℝ) := simplexArea (simplexGraph Γ σ.val σ.property.2)
    (d-1) (simplexCoordinates σ.val σ.property.2 ''
      (A ∩ {v | centerDistance Γ hΓ K n c v=t}))
  have hF : ∀ A∈Set.range f,Measurable (F A) := by
    rintro A ⟨x,rfl⟩
    simpa only [F,f,Set.inter_assoc,localOriginalArea] using
      measurable_marked_ball_slices Γ hΓ Q σ c d hdn x (hd x)
  simpa only [F,f,Set.inter_assoc,localOriginalArea] using BassTrace.Sparse.IsLocallyConstant.measurable_uncurry hf F hF

theorem integrated_marked_ball_coarea [Countable Y]
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) [SFinite μ] (B : Set X) (c : FinProbability Y)
    (hn : 0<n) (d : ℕ) (hdn : d≤n)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) (r b : ℝ) :
    (∫⁻ t in Ioo r b, ∫⁻ x in B, ∑' σ : SourceTop K n,
      localOriginalArea Γ Q σ (d-1) {v | centerDistance Γ hΓ K n c v=t} x ∂μ) ≤
      ∫⁻ x in B, ∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ d {v | centerDistance Γ hΓ K n c v≤b} x ∂μ := by
  let : Countable (SourceTop K n) :=
    inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
  have hm (σ : SourceTop K n) := measurable_marked_ball_slices_joint Γ hΓ Q σ c d hdn hd
  rw [← lintegral_lintegral_swap ((Measurable.tsum hm).aemeasurable)]
  apply lintegral_mono
  intro x
  dsimp only
  rw [lintegral_tsum (fun σ => (measurable_marked_ball_slices Γ hΓ Q σ c d hdn x (hd x)).aemeasurable)]
  exact ENNReal.tsum_le_tsum (fun σ => marked_ball_coarea Γ hΓ hn Q σ c d hdn x (hd x) r b)

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.BallComparison
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

section

variable {Y : Type*} [DecidableEq Y] [Countable Y]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMeasurableSpaceFinsuppReal_solutions
local instance instBorelSpaceFinsuppReal_solutions : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

variable (K : PreAbstractSimplicialComplex Y)

lemma measurable_realization : MeasurableSet
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  have he : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      ⋃ s∈K.faces, convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
    ext p
    rw [Geometry.SimplicialComplex.mem_space_iff]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨_,⟨s,hs,rfl⟩,hp⟩
      exact ⟨s,hs,hp⟩
    · rintro ⟨s,hs,hp⟩
      exact ⟨simplexVertices s,⟨s,hs,rfl⟩,hp⟩
  rw [he]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun _ =>
    ((simplexVertices s).finite_toSet.isCompact_convexHull ℝ).isClosed.measurableSet

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable {n : ℕ} (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK in
lemma measurable_centerDistance (c : FinProbability Y) :
    Measurable (centerDistance Γ hΓ K n c) := by
  have hc := continuousOn_centerDistance Γ hΓ hn K
    (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,-⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
    (fun σ hσ => by
      obtain ⟨τ,hτ,hστ,hcard,hconn⟩ := hK σ hσ.1
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,hσ.2])
      exact he.symm ▸ hconn) c
  have hm := hc.measurable_piecewise (continuous_const (y := (0 : ℝ))).continuousOn (measurable_realization K)
  convert hm using 1
  funext p
  by_cases hp : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space
  · simp only [Set.piecewise, hp,ite_eq_left]
  · simp [Set.piecewise,centerDistance,hp]

include hn hK in
lemma measurable_ballWindow (c : FinProbability Y) (J : Set ℝ) (hJ : MeasurableSet J) :
    MeasurableSet (ballWindow K Γ hΓ (n := n) c J) :=
  (measurable_realization K).inter (hJ.preimage (measurable_centerDistance K Γ hΓ hn hK c))

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [MulAction H X]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (n : ℕ)

omit [Countable Y] in
include hact hi in
lemma ballWindow_push (c : FinProbability Y) (J : Set ℝ) (h : H) :
    OrbitForms.push h '' ballWindow K Γ hΓ (n := n) c J =
      ballWindow K Γ hΓ (n := n) (h•c) J := by
  ext p
  constructor
  · rintro ⟨q,⟨hq,hqr⟩,rfl⟩
    refine ⟨space_push K hact h q hq,?_⟩
    simpa only [Set.mem_preimage,centerDistance_push K hact Γ hΓ hi n h c q hq] using hqr
  · rintro ⟨hp,hpr⟩
    have hq := space_push K hact h⁻¹ p hp
    refine ⟨OrbitForms.push h⁻¹ p,⟨hq,?_⟩,?_⟩
    · have he := centerDistance_push K hact Γ hΓ hi n h⁻¹ (h•c) p hp
      rw [inv_smul_smul] at he
      simpa only [Set.mem_preimage,he] using hpr
    · simpa only [inv_inv] using OrbitForms.push_inv_push h⁻¹ p

omit [Countable Y] in
lemma original_marked_subset_space
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (x : X) :
    Q.P.val x⊆(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  intro p hp
  exact (Q.T.val x).space_eq ▸ ((Q.P.marked x).subset_space hp)

omit [Countable Y] in
lemma localOriginalArea_ballWindow
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (c : FinProbability Y) (J : Set ℝ) (x : X) :
    localOriginalArea Γ Q σ j (ballWindow K Γ hΓ (n := n) c J) x =
      localOriginalArea Γ Q σ j (centerDistance Γ hΓ K n c ⁻¹' J) x := by
  unfold localOriginalArea
  congr 2
  ext p
  simp only [ballWindow,Set.mem_inter_iff]
  constructor
  · tauto
  · rintro ⟨hp,hi,hr⟩
    exact ⟨hp,hi,original_marked_subset_space K Q x hp,hr⟩

omit [Countable Y] in
include hact hi in
lemma replacement_ballWindow (P Z : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (c : FinProbability Y) (B : Set X) (t : ℝ) (x : X) :
    Cuts.replacementSet (P.P.val x) (Z.P.val x)
      (fun i : H×Unit => {v | centerDistance Γ hΓ K n (i.1•c) v<t})
      (fun i : H×Unit => {v | centerDistance Γ hΓ K n (i.1•c) v=t})
      (fun i : H×Unit => (fun x=>i.1⁻¹•x)⁻¹' B) x =
    (Z.P.val x \ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c (Iio t)) h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c {t}) h x) := by
  have hw (J : Set ℝ) (p : Y →₀ ℝ)
      (hp : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
      p∈Cuts.activatedUnion (fun i : H×Unit => centerDistance Γ hΓ K n (i.1•c) ⁻¹' J)
        (fun i : H×Unit => (fun x=>i.1⁻¹•x)⁻¹' B) x ↔
      p∈⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c J) h x := by
    simp only [Cuts.activatedUnion,activeWindow,ballWindow_push K hact Γ hΓ hi n,
      Set.mem_iUnion,Prod.exists,Set.mem_preimage]
    constructor
    · rintro ⟨h,u,hh⟩
      refine ⟨h,?_⟩
      split_ifs at hh ⊢ with hx
      · exact ⟨hp,hh⟩
      · exact hh
    · rintro ⟨h,hh⟩
      refine ⟨h,(),?_⟩
      split_ifs at hh ⊢ with hx
      · exact hh.2
      · exact hh
  ext p
  simp only [Cuts.replacementSet,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff]
  constructor
  · rintro (⟨hz,hzout⟩ | ⟨hp,hpin⟩)
    · exact Or.inl ⟨hz,fun hh=>hzout ((hw (Iio t) p (original_marked_subset_space K Z x hz)).mpr hh)⟩
    · exact Or.inr ⟨hp,(hw {t} p (original_marked_subset_space K P x hp)).mp hpin⟩
  · rintro (⟨hz,hzout⟩ | ⟨hp,hpin⟩)
    · exact Or.inl ⟨hz,fun hh=>hzout ((hw (Iio t) p (original_marked_subset_space K Z x hz)).mp hh)⟩
    · exact Or.inr ⟨hp,(hw {t} p (original_marked_subset_space K P x hp)).mpr hpin⟩

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable {n : ℕ} (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK hact hi in

theorem ae_exists_ball_step {R : ℝ} (hR : 0<R)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B) :
    ∀ᵐ t : ℝ, 0<t → t≤R →
      ∃ A : OrbitForms.EquivariantStep (realizationDistance Γ hΓ K n) R (Q.pair (j+1)),
        ∀ x,A.result.P.val x =
          ((Q.pair j).P.val x \ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c (Iio t)) h x) ∪
          ((Q.pair (j+1)).P.val x ∩ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c {t}) h x) := by
  let := graphMetric Γ hΓ
  let S (_ : Unit) := ballSupport Γ c n R
  let d := BallOrbitForms.data S (fun _ : Unit=>c) n
  have hfaces : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces.Countable :=
    (Set.to_countable K.faces).image (fun s=>simplexVertices s)
  have hb := (Q.pair (j+1)).T.countable_exceptional_levels hfaces (fun k : H×BallOrbitForms.Index S => fun v=>OrbitForms.form d k v)
  have hae : ∀ᵐ t : ℝ,∀ x F,F∈((Q.pair (j+1)).T.val x).complex.faces →
      ∀ k y,y∈F → OrbitForms.form d k y≠t := ae_iff.mpr (hb.measure_zero volume)
  filter_upwards [hae] with t htgen
  intro ht htR
  obtain ⟨A,hA,hZ,hval⟩ := exists_ball_replacement Γ hΓ rfl hn K hK hact hi
    (Q.pair (j+1)).T (Q.pair (j+1)).P hR ht htR (Q.admissibleStep hj)
    (Q.pair j).equivariant (Q.pair (j+1)).markedEquivariant (Q.pair j).markedEquivariant
    (fun _ :Unit=>c) (fun _ :Unit=>B) (fun _=>hB) (by
      intro x F hF k
      obtain ⟨v,hv⟩ := ((Q.pair (j+1)).T.val x).complex.nonempty_of_mem_faces hF
      exact ⟨v,hv,htgen x F hF k v hv⟩)
  refine ⟨⟨A,hA,hZ⟩,fun x=>?_⟩
  change A.zero.val x=_
  rw [hval x]
  exact replacement_ballWindow K hact Γ hΓ hi n (Q.pair (j+1)) (Q.pair j) c B t x

end Sparse.GraphGeometry

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

omit [DecidableEq Y] [TopologicalSpace X] in
lemma activeWindow_mono {U V : Set (Y →₀ ℝ)} (hUV : U⊆V) (B : Set X) (h : H) (x : X) :
    activeWindow B U h x⊆activeWindow B V h x := by
  unfold activeWindow
  split_ifs
  · exact Set.image_mono hUV
  · exact Set.Subset.refl _

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop
local instance instCountableSourceTop_rdc6552_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance instFiniteSubtypeMemSubgroupStabilizerSourceTop_rdc6552_1 (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem ae_open_ball_comparison (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x))) :
    ∀ᵐ t : ℝ,0<t → t≤R →
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair j) σ j
        {v | centerDistance Γ hΓ K n c v<t} x ∂μ) ≤
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair (j+1)) σ j
        {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  have hKn (s) (hs : s∈K.faces) : s.card≤n+1 := by
    obtain ⟨τ,hτ,hst,hcard,-⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hcard
  have hconn (σ : SourceTop K n) : (Γ.induce (σ.val : Set Y)).Connected := by
    obtain ⟨τ,hτ,hst,hcard,hct⟩ := hK σ.val σ.property.1
    have he : σ.val=τ := Finset.eq_of_subset_of_card_le hst (by rw [hcard,σ.property.2])
    exact he.symm ▸ hct
  let reps := OrbitAreas.orbitReps (H := H) (T := SourceTop K n)
  have hfinite := normalizedArea_filtration_lt_top Γ μ reps (fun σ _=>hconn σ) Q hKn hj.le
  filter_upwards [ae_exists_ball_step K hact.out Γ hΓ hi hn hK hR Q hj c B hB] with t htgen
  intro ht htR
  obtain ⟨A,hnew⟩ := htgen ht htR
  have hfinite' := OrbitForms.normalizedArea_step_lt_top Γ μ reps (fun σ _=>hconn σ) Q hKn hj A
  have hgain := normalizedArea_surgery_gain (n := n) Γ hΓaut (Q.pair (j+1)) (Q.pair j) A.result
    μ hμ j B hB.isOpen.measurableSet
    (ballWindow K Γ hΓ (n := n) c (Iio t)) (ballWindow K Γ hΓ (n := n) c {t})
    (by
      intro x h
      unfold activeWindow
      split_ifs
      · rw [ballWindow_push K hact.out Γ hΓ hi n]
        exact measurable_ballWindow K Γ hΓ hn hK (h•c) (Iio t) measurableSet_Iio
      · exact MeasurableSet.empty)
    (by
      intro x h k hhk
      have hsub : ballWindow K Γ hΓ (n := n) c (Iio t)⊆ballWindow K Γ hΓ (n := n) c (Iic R) :=
        fun _ hp=>⟨hp.1,hp.2.le.trans htR⟩
      exact (hdisj x hhk).mono (activeWindow_mono hsub B h x) (activeWindow_mono hsub B k x)) hnew
  have hle := nearMinimum_local_comparison hfinite
    (ennreal_nearMinimum_of_real hfinite.ne hfinite'.ne hε (hmin j hj A)) hgain
  simpa only [localOriginalArea_ballWindow,Set.preimage,Set.mem_Iio,Set.mem_singleton_iff] using hle

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK in

lemma ae_local_ball_closed_eq_open
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (j : ℕ) (c : FinProbability Y) :
    ∀ᵐ t : ℝ,∀ (σ : SourceTop K n) x,
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤t} x =
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v<t} x := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  let : Countable (SourceTop K n) :=
    inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
  apply ae_all_iff.mpr
  intro σ
  let f (x : X) := Q.P.val x∩sourceInterior σ.val
  have hf : IsLocallyConstant f := Q.P.localConstancy_inter (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩ _ intrinsicInterior_subset
  let : Finite (Set.range f) := hf.range_finite.to_subtype
  let m := originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
  have ha (A : Set.range f) : ∀ᵐ t : ℝ,
      m (A.val∩{v | centerDistance Γ hΓ K n c v≤t}) =
      m (A.val∩{v | centerDistance Γ hΓ K n c v<t}) := by
    exact ae_iff.mpr ((countable_ball_area_jumps m A.val
      (measurable_centerDistance K Γ hΓ hn hK c)).measure_zero volume)
  filter_upwards [ae_all_iff.mpr ha] with t ht
  intro x
  simpa only [localOriginalArea_eq_measure,f,m] using ht ⟨f x,Set.mem_range_self x⟩

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

lemma ballMass_mono
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (j : ℕ) (c : FinProbability Y) :
    Monotone (ballMass (n := n) Γ hΓ Q μ B j c) := by
  intro s t hst
  unfold ballMass
  apply lintegral_mono
  intro x
  apply ENNReal.tsum_le_tsum
  intro σ
  simp only [localOriginalArea_eq_measure]
  exact measure_mono fun _ hp=>⟨hp.1,hp.2.trans hst⟩

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.GraphCounting
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

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_1
local instance instCountableSourceTop_1_rdc6552_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance instFiniteSubtypeMemSubgroupStabilizerSourceTop_1_rdc6552_1 (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem ballMass_recurrence (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r b : ℝ) (hr : 0≤r) (hb : b≤R) :
    (∫⁻ t in Ioo r b,ballMass (n := n) Γ hΓ (Q.pair j) μ B j c t) ≤
      ballMass (n := n) Γ hΓ (Q.pair (j+1)) μ B (j+1) c b +
        ENNReal.ofReal ε * ENNReal.ofReal (b-r) := by
  have hcomp := ae_open_ball_comparison Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin hj c B hB hdisj
  have heq := ae_local_ball_closed_eq_open Γ hΓ hn hK (Q.pair j) j c
  have hlocal : ∀ᵐ t ∂volume.restrict (Ioo r b),
      ballMass (n := n) Γ hΓ (Q.pair j) μ B j c t ≤
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair (j+1)) σ j
        {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε := by
    filter_upwards [ae_restrict_of_ae hcomp,ae_restrict_of_ae heq,
      ae_restrict_mem measurableSet_Ioo] with t ht he htb
    have hc := ht (hr.trans_lt htb.1) (htb.2.le.trans hb)
    simpa only [ballMass,he] using hc
  have hdim : ∀ x t,t∈((Q.pair (j+1)).T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair (j+1)).P.val x → t.card≤j+1+1 := by
    intro x t ht htp
    apply (Q.point x).dimension_bound _ (by omega) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,hτ,hst,hcard,-⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hco := integrated_marked_ball_coarea Γ hΓ (Q.pair (j+1)) μ B c hn
    (j+1) (by omega) hdim r b
  simp only [Nat.add_sub_cancel] at hco
  calc
    _ ≤ ∫⁻ t in Ioo r b, (∫⁻ x in B,∑' σ : SourceTop K n,
          localOriginalArea Γ (Q.pair (j+1)) σ j
            {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε :=
      lintegral_mono_ae hlocal
    _ = (∫⁻ t in Ioo r b, ∫⁻ x in B,∑' σ : SourceTop K n,
          localOriginalArea Γ (Q.pair (j+1)) σ j
            {v | centerDistance Γ hΓ K n c v=t} x ∂μ) +
        ENNReal.ofReal ε * ENNReal.ofReal (b-r) := by
      rw [lintegral_add_right _ measurable_const,lintegral_const,
        Measure.restrict_apply_univ,Real.volume_Ioo]
    _ ≤ _ := add_le_add hco le_rfl

end

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

namespace Sparse.GraphCounting

open SimpleGraph

variable {Y : Type*} (Γ : SimpleGraph Y)

lemma basedWalk_zero_subsingleton (v : Y) : Subsingleton (BasedWalk Γ v 0) := by
  refine ⟨?_⟩
  rintro ⟨⟨b,p⟩,hp⟩ ⟨⟨c,q⟩,hq⟩
  have hb := p.eq_of_length_eq_zero hp
  have hc := q.eq_of_length_eq_zero hq
  subst b
  subst c
  have he : p = .nil := Walk.eq_nil_iff_nil.mpr (Walk.length_eq_zero_iff.mp hp)
  have hf : q = .nil := Walk.eq_nil_iff_nil.mpr (Walk.length_eq_zero_iff.mp hq)
  subst p
  subst q
  rfl

lemma basedWalkSucc_injective (v : Y) (n : ℕ) :
    Function.Injective (basedWalkSucc Γ v n) := by
  apply Function.LeftInverse.injective (g := basedWalkCons Γ v n)
  rintro ⟨⟨b,p⟩,hp⟩
  cases p with
  | nil => simp at hp
  | cons h p => rfl

lemma basedWalk_finite [Γ.LocallyFinite] (v : Y) (n : ℕ) : Finite (BasedWalk Γ v n) := by
  induction n generalizing v with
  | zero =>
    let := basedWalk_zero_subsingleton Γ v
    infer_instance
  | succ n ih =>
    let : ∀ w : Γ.neighborSet v, Finite (BasedWalk Γ w n) := fun w => ih w
    exact Finite.of_injective _ (basedWalkSucc_injective Γ v n)

lemma basedWalk_card_le [Γ.LocallyFinite] (D : ℕ)
    (hD : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (v : Y) (n : ℕ) :
    Nat.card (BasedWalk Γ v n) ≤ D^n := by
  induction n generalizing v with
  | zero =>
    let := basedWalk_zero_subsingleton Γ v
    rw [Nat.card_of_subsingleton (⟨⟨v,.nil⟩,rfl⟩ : BasedWalk Γ v 0)]
    simp
  | succ n ih =>
    let : ∀ w : Γ.neighborSet v, Fintype (BasedWalk Γ w n) :=
      fun w => @Fintype.ofFinite _ (basedWalk_finite Γ w n)
    have hc := Nat.card_le_card_of_injective _ (basedWalkSucc_injective Γ v n)
    rw [Nat.card_eq_fintype_card (α := (w : Γ.neighborSet v) × BasedWalk Γ w n), Fintype.card_sigma] at hc
    calc Nat.card (BasedWalk Γ v (n+1)) ≤ _ := hc
         _ ≤ ∑ _w : Γ.neighborSet v, D^n := Finset.sum_le_sum fun w _ => by
           simpa only [Nat.card_eq_fintype_card] using ih w
         _ = Fintype.card (Γ.neighborSet v)*D^n := by simp
         _ ≤ D*D^n := Nat.mul_le_mul_right _ (hD v)
         _ = D^(n+1) := by rw [pow_succ, Nat.mul_comm]

lemma connectedSetTour_support [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    (connectedSetTour Γ v n s).support.toFinset=s.val :=
  (connected_set_tour Γ s.val s.property.2.2 v s.property.1 s.property.2.1).choose_spec.2

lemma connectedSetEncoding_injective [DecidableEq Y] (v : Y) (n : ℕ) :
    Function.Injective (connectedSetEncoding Γ v n) := by
  intro s t he
  have hs := congrArg (fun w : BasedWalk Γ v (2*n) => w.val.2.support.toFinset) he
  change (connectedSetTour Γ v n s).support.toFinset =
    (connectedSetTour Γ v n t).support.toFinset at hs
  rw [connectedSetTour_support,connectedSetTour_support] at hs
  exact Subtype.ext hs

lemma connectedSets_finite [Γ.LocallyFinite] (v : Y) (n : ℕ) : Finite (ConnectedSets Γ v n) := by
  classical
  let := basedWalk_finite Γ v (2*n)
  exact Finite.of_injective _ (connectedSetEncoding_injective Γ v n)

theorem connectedSets_card_le [Γ.LocallyFinite] (D : ℕ)
    (hD : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (v : Y) (n : ℕ) :
    Nat.card (ConnectedSets Γ v n) ≤ D^(2*n) := by
  classical
  let := basedWalk_finite Γ v (2*n)
  exact (Nat.card_le_card_of_injective _ (connectedSetEncoding_injective Γ v n)).trans
    (basedWalk_card_le Γ D hD v (2*n))

end Sparse.GraphCounting

namespace Sparse.GraphGeometry

open Set Finset

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

lemma neighborhood_card_bound (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (v : Y) :
    (neighborhood Γ k v).card + 1 ≤ D^(k+1) := by
  induction k generalizing v with
  | zero => simpa [neighborhood] using hD
  | succ k ih =>
    have hi : ((Γ.neighborFinset v).biUnion (neighborhood Γ k)).card ≤
        ∑ w ∈ Γ.neighborFinset v, (neighborhood Γ k w).card := Finset.card_biUnion_le
    have hn : (Γ.neighborFinset v).card ≤ D := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact hdeg v
    have hp := Finset.card_insert_le v ((Γ.neighborFinset v).biUnion (neighborhood Γ k))
    have hexp : 1 ≤ D^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hraw : (neighborhood Γ (k+1) v).card + 1 ≤
        2 + (Γ.neighborFinset v).card * (D^(k+1)-1) := by
      change (insert v ((Γ.neighborFinset v).biUnion (neighborhood Γ k))).card +1 ≤ _
      have hb : (∑ w ∈ Γ.neighborFinset v, (neighborhood Γ k w).card) ≤
          (Γ.neighborFinset v).card * (D^(k+1)-1) := by
        calc
          _ ≤ ∑ _w ∈ Γ.neighborFinset v, (D^(k+1)-1) :=
            Finset.sum_le_sum fun w _ => by have hh := ih w; omega
          _ = _ := by simp
      omega
    calc
      _ ≤ 2 + (Γ.neighborFinset v).card * (D^(k+1)-1) := hraw
      _ ≤ 2 + D * (D^(k+1)-1) := by gcongr
      _ ≤ D * D^(k+1) := by
        have heq : D^(k+1)-1+1 = D^(k+1) := Nat.sub_add_cancel hexp
        nlinarith
      _ = D^(k+1+1) := (pow_succ' D (k+1)).symm

lemma neighborhood_card_le (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (v : Y) :
    (neighborhood Γ k v).card ≤ D^(k+1) := by
  have h := neighborhood_card_bound Γ D hD hdeg k v
  omega

lemma supportNeighborhood_card_le (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (A : Finset Y) :
    (A.biUnion (neighborhood Γ k)).card ≤ A.card * D^(k+1) := by
  calc
    _ ≤ ∑ v ∈ A, (neighborhood Γ k v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ A, D^(k+1) := Finset.sum_le_sum fun v _ =>
      neighborhood_card_le Γ D hD hdeg k v
    _ = _ := by simp

end Sparse.GraphGeometry

namespace Sparse.GraphCounting

open Set Finset

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

omit [DecidableEq Y] [Γ.LocallyFinite] in
lemma throughEncoding_injective (B : Finset Y) (n : ℕ) :
    Function.Injective (throughEncoding Γ B n) := by
  intro s t h
  exact Subtype.ext (congrArg (fun p : (v : B) × ConnectedSets Γ v n => p.2.val) h)

omit [DecidableEq Y] in
lemma connectedThrough_finite (B : Finset Y) (n : ℕ) :
    Finite (ConnectedThrough Γ B n) := by
  let : ∀ v : B, Finite (ConnectedSets Γ v n) := fun v => connectedSets_finite Γ v n
  exact Finite.of_injective _ (throughEncoding_injective Γ B n)

omit [DecidableEq Y] in
theorem connectedThrough_card_le (D : ℕ)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (B : Finset Y) (n : ℕ) :
    Nat.card (ConnectedThrough Γ B n) ≤ B.card * D^(2*n) := by
  let : ∀ v : B, Fintype (ConnectedSets Γ v n) :=
    fun v => @Fintype.ofFinite _ (connectedSets_finite Γ v n)
  have hc := Nat.card_le_card_of_injective _ (throughEncoding_injective Γ B n)
  rw [Nat.card_eq_fintype_card (α := (v : B) × ConnectedSets Γ v n),Fintype.card_sigma] at hc
  calc
    _ ≤ _ := hc
    _ ≤ ∑ _v : B, D^(2*n) := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [Nat.card_eq_fintype_card] using connectedSets_card_le Γ D hdeg v n
    _ = _ := by simp

end Sparse.GraphCounting

namespace Sparse.GraphGeometry

open FinProbability

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

lemma meeting_simplex_contact (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (c p : FinProbability Y) (σ : Finset Y) (hp : p.coeff.support ⊆ σ)
    (s : ℝ) (hs : 0 ≤ s)
    (hball : @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s) :
    ∃ v ∈ c.coeff.support.biUnion (neighborhood Γ ⌊s * Real.sqrt (n : ℝ)⌋₊), v ∈ σ := by
  let : MetricSpace Y := graphMetric Γ hΓ
  obtain ⟨a,ha,v,hv,hav⟩ := support_distance_rho hn c p
  have hle : (Γ.dist a v : ℝ) ≤ s * Real.sqrt (n : ℝ) := by
    change (Γ.dist a v : ℝ) ≤ Real.sqrt (n : ℝ) * rho n c p at hav
    calc _ ≤ Real.sqrt (n : ℝ) * rho n c p := hav
         _ ≤ Real.sqrt (n : ℝ) * s := mul_le_mul_of_nonneg_left hball (Real.sqrt_nonneg _)
         _ = _ := mul_comm _ _
  exact ⟨v,Finset.mem_biUnion.mpr ⟨a,ha,dist_le_mem_neighborhood Γ hΓ
    ((Nat.le_floor_iff (mul_nonneg hs (Real.sqrt_nonneg _))).mpr hle)⟩,hp hv⟩

theorem meetingTops_card_le (hΓ : Γ.Connected) (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (s : ℝ) (hs : 0 ≤ s) :
    Nat.card (MeetingTops Γ hΓ n tops c s) ≤
      c.coeff.support.card * D^(⌊s * Real.sqrt (n : ℝ)⌋₊+1) * D^(2*n) := by
  let B := c.coeff.support.biUnion (neighborhood Γ ⌊s * Real.sqrt (n : ℝ)⌋₊)
  let f : MeetingTops Γ hΓ n tops c s → GraphCounting.ConnectedThrough Γ B n := fun σ =>
    ⟨σ.val,(htop σ.val σ.property.1).1,(htop σ.val σ.property.1).2,by
      obtain ⟨p,hp,hball⟩ := σ.property.2
      exact meeting_simplex_contact Γ hΓ hn c p σ.val hp s hs hball⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    exact congrArg (fun x : GraphCounting.ConnectedThrough Γ B n => x.val) h
  have : Finite (GraphCounting.ConnectedThrough Γ B n) :=
    GraphCounting.connectedThrough_finite Γ B n
  calc
    _ ≤ Nat.card (GraphCounting.ConnectedThrough Γ B n) := Nat.card_le_card_of_injective f hf
    _ ≤ B.card * D^(2*n) := GraphCounting.connectedThrough_card_le Γ D hdeg B n
    _ ≤ _ := Nat.mul_le_mul_right _ (supportNeighborhood_card_le Γ D hD hdeg _ _)

theorem meetingTops_card_le_uniform (hΓ : Γ.Connected) (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (hc : c.coeff.support.card ≤ n+1) (s : ℝ) (hs : 0 ≤ s) :
    Nat.card (MeetingTops Γ hΓ n tops c s) ≤
      (n+1) * D^(⌊s * Real.sqrt (n : ℝ)⌋₊+1) * D^(2*n) := by
  exact (meetingTops_card_le Γ hΓ D hD hdeg hn tops htop c s hs).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.VolumeBounds
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

lemma continuous_dividedPower (n : ℕ) : Continuous (dividedPower n) := by
  unfold dividedPower
  fun_prop

lemma continuous_slicingError (n : ℕ) : Continuous (slicingError n) := by
  unfold slicingError
  exact continuous_finsetSum _ fun _ _ => continuous_dividedPower _

lemma integral_dividedPower (n : ℕ) (b : ℝ) :
    (∫ t in 0..b, dividedPower n t) = dividedPower (n + 1) b := by
  unfold dividedPower
  rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n),
    sub_zero, div_div, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

lemma integral_slicingError (n : ℕ) (b : ℝ) :
    (∫ t in 0..b, slicingError n t) + b = slicingError (n + 1) b := by
  unfold slicingError
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_dividedPower (i + 1)).intervalIntegrable 0 b)]
  simp only [integral_dividedPower]
  rw [Finset.sum_range_succ']
  simp only [zero_add, dividedPower_one]

lemma integral_slicing_lower (n : ℕ) (b c ε : ℝ) :
    (∫ t in 0..b, c * dividedPower n t - ε * slicingError n t) - ε * b =
      c * dividedPower (n + 1) b - ε * slicingError (n + 1) b := by
  have hc : IntervalIntegrable (fun t => c * dividedPower n t) volume 0 b :=
    (continuous_const.mul (continuous_dividedPower n)).intervalIntegrable 0 b
  have he : IntervalIntegrable (fun t => ε * slicingError n t) volume 0 b :=
    (continuous_const.mul (continuous_slicingError n)).intervalIntegrable 0 b
  rw [intervalIntegral.integral_sub hc he,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_dividedPower]
  have h := integral_slicingError n b
  rw [← h]
  ring

theorem iterated_slicing_lower_bound
    (M : ℕ → ℝ → ℝ) (n : ℕ) (L ε : ℝ)
    (hmono : ∀ k, Monotone (M k))
    (hstep : ∀ k < n, ∀ b ∈ Set.Icc 0 L,
      (∫ t in 0..b, M k t) - ε * b ≤ M (k + 1) b) :
    ∀ k ≤ n, ∀ b ∈ Set.Icc 0 L,
      M 0 0 * dividedPower k b - ε * slicingError k b ≤ M k b := by
  intro k
  induction k with
  | zero =>
      intro _ b hb
      simpa using hmono 0 hb.1
  | succ k ih =>
      intro hk b hb
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hm :
          (∫ t in 0..b, M 0 0 * dividedPower k t - ε * slicingError k t) ≤
            ∫ t in 0..b, M k t := by
        apply intervalIntegral.integral_mono_on hb.1
          (((continuous_const.mul (continuous_dividedPower k)).sub
            (continuous_const.mul (continuous_slicingError k))).intervalIntegrable 0 b)
          (hmono k).intervalIntegrable
        intro t ht
        exact ih hk' t ⟨ht.1, ht.2.trans hb.2⟩
      have hs := hstep k (Nat.lt_of_succ_le hk) b hb
      rw [← integral_slicing_lower k b (M 0 0) ε]
      linarith

theorem absorb_nonempty_probability
    (A V μ M ε E : ℝ) (hVA : V < A) (hV : 0 ≤ V)
    (hμM : μ ≤ M) (hbound : A * M ≤ V * μ + ε * E) :
    M ≤ E / (A - V) * ε := by
  have hpos : 0 < A - V := sub_pos.mpr hVA
  have hmul : V * μ ≤ V * M := mul_le_mul_of_nonneg_left hμM hV
  have h : (A - V) * M ≤ ε * E := by nlinarith
  have h' : M ≤ (ε * E) / (A - V) := (le_div_iff₀ hpos).2 (by nlinarith)
  convert h' using 1
  ring

/-! A strict high-dimensional volume margin with radius 4 D² and half-radius 2 D². -/

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

omit [MeasurableSpace X] [Γ.LocallyFinite] in
include hK in
lemma localOriginalArea_top_le
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ n W x ≤ ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  rw [←simplexArea_top_simplex (simplexGraph Γ σ.val σ.property.2)
    (simplexGraph_connected Γ σ.val σ.property.2 (sourceTop_connected Γ hK σ))]
  apply simplexArea_mono
  rintro _ ⟨v,⟨_,hv,_⟩,rfl⟩
  exact simplexCoordinates_full _ _ (intrinsicInterior_subset hv)

include hn hK in
lemma localTops_card_le (D : ℕ) (hD : 2≤D)
    (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (b : ℝ) (hb : 0≤b) :
    Nat.card (localTops (K := K) (n := n) Γ hΓ c b) ≤
      (n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) := by
  let tops : Set (Finset Y) := {s | s∈K.faces ∧ s.card=n+1}
  let f : localTops (K := K) (n := n) Γ hΓ c b → MeetingTops Γ hΓ n tops c b := fun σ=>by
    refine ⟨σ.val.val,σ.val.property,?_⟩
    obtain ⟨v,hv,hvb⟩ := σ.property
    have hvK := (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      (show simplexVertices σ.val.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces from
        ⟨σ.val.val,σ.val.property.1,rfl⟩) (intrinsicInterior_subset hv)
    let p := pointProbability K ⟨v,hvK⟩
    have hp : p.coeff=v := pointProbability_coeff K ⟨v,hvK⟩
    refine ⟨p,?_,?_⟩
    · rw [hp]; exact support_of_mem_sourceInterior _ hv
    · rw [←centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩),hp]
      exact hvb
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun s : MeetingTops Γ hΓ n tops c b=>s.val) h
  have hfin := finitely_many_meeting_top_simplices Γ hΓ hn tops
    (fun s hs=>⟨hs.2,sourceTop_connected Γ hK ⟨s,hs⟩⟩) c b hb
  let : Finite (MeetingTops Γ hΓ n tops c b) := hfin.to_subtype
  exact (Nat.card_le_card_of_injective f hf).trans
    (meetingTops_card_le_uniform Γ hΓ D hD hdeg hn tops
      (fun s hs=>⟨hs.2,sourceTop_connected Γ hK ⟨s,hs⟩⟩) c hc b hb)

include hn hK in
lemma ballMass_top_bound
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (c : FinProbability Y)
    (hc : c.coeff.support.card≤n+1) (b : ℝ) (hb : 0≤b)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D) :
    ballMass (n := n) Γ hΓ Q μ B n c b ≤
      ((n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) : ℕ) *
        ENNReal.ofReal (1/(n.factorial : ℝ)) * μ B := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have hzero (σ : SourceTop K n) (hσ : σ∉F) (x : X) :
      localOriginalArea Γ Q σ n {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
    rw [localOriginalArea_eq_measure]
    have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨⟨_,hv⟩,hr⟩
      exact hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr ⟨v,hv,hr⟩)
    rw [he,measure_empty]
  have hle (x : X) : (∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ n {v | centerDistance Γ hΓ K n c v≤b} x) ≤
      (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ)) := by
    rw [tsum_eq_sum (s := F) (fun σ hσ=>hzero σ hσ x)]
    simpa using Finset.sum_le_sum (s := F) (fun σ _=>localOriginalArea_top_le Γ hK Q σ _ x)
  have hcard : F.card≤(n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) := by
    have h := localTops_card_le Γ hΓ hn hK D hD hdeg c hc b hb
    simpa only [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card _ (localTops_finite Γ hΓ hn hK c b hb),F] using h
  calc
    _ ≤ ∫⁻ _x in B, (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ)) ∂μ := lintegral_mono hle
    _ = (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ))*μ B := by simp
    _ ≤ _ := by gcongr

end Sparse.GraphGeometry

namespace Sparse

open Set MeasureTheory

open scoped ENNReal

lemma real_integral_of_mass_bound (F : ℝ → ℝ≥0∞) (hmono : Monotone F)
    (hfin : ∀ t,F t<∞) (r b ε : ℝ) (hrb : r≤b) (hε : 0≤ε)
    (C : ℝ≥0∞) (hC : C<∞)
    (h : (∫⁻ t in Ioo r b,F t)≤C+ENNReal.ofReal ε*ENNReal.ofReal (b-r)) :
    (∫ t in r..b,(F t).toReal)≤C.toReal+ε*(b-r) := by
  rw [intervalIntegral.integral_of_le hrb,integral_Ioc_eq_integral_Ioo,
    integral_toReal hmono.measurable.aemeasurable (Filter.Eventually.of_forall hfin)]
  have ht : C+ENNReal.ofReal ε*ENNReal.ofReal (b-r)≠∞ := by finiteness
  have hh := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_add hC.ne (by finiteness),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hε,ENNReal.toReal_ofReal (sub_nonneg.mpr hrb)] at hh
  exact hh

theorem iterated_mass_bound (M : ℕ → ℝ → ℝ≥0∞) (n : ℕ) (r R ε : ℝ)
    (hrR : r≤R) (hε : 0≤ε) (hmono : ∀ k,Monotone (M k))
    (hfin : ∀ k t,M k t<∞)
    (hstep : ∀ k<n,∀ b∈Icc r R,
      (∫⁻ t in Ioo r b,M k t)≤M (k+1) b+ENNReal.ofReal ε*ENNReal.ofReal (b-r)) :
    (M 0 r).toReal*dividedPower n (R-r)-ε*slicingError n (R-r)≤(M n R).toReal := by
  let F : ℕ → ℝ → ℝ := fun k t=>(M k (r+t)).toReal
  have hFm k : Monotone (F k) := fun a b hab=>
    ENNReal.toReal_mono (hfin k _).ne (hmono k (add_le_add le_rfl hab))
  have hFs k (hk : k<n) b (hb : b∈Icc 0 (R-r)) :
      (∫ t in 0..b,F k t)-ε*b≤F (k+1) b := by
    have hle := real_integral_of_mass_bound (M k) (hmono k) (hfin k) r (r+b) ε
      (by linarith [hb.1]) hε (M (k+1) (r+b)) (hfin _ _) (hstep k hk _ ⟨by linarith [hb.1],by linarith [hb.2]⟩)
    have he : (∫ t in 0..b,F k t) = ∫ t in r..r+b,(M k t).toReal := by
      simpa only [F,add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := b) (fun t=>(M k t).toReal) r
    rw [he]
    dsimp [F]
    linarith
  have hi := iterated_slicing_lower_bound F n (R-r) ε hFm hFs n le_rfl (R-r)
    ⟨sub_nonneg.mpr hrR,le_rfl⟩
  simpa only [F,add_zero,add_sub_cancel] using hi

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_2
local instance instCountableSourceTop_2_rdc6552_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance instFiniteSubtypeMemSubgroupStabilizerSourceTop_2_rdc6552_1 (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem iterated_ball_volume (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D) :
    dividedPower n (R-r) * (ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r).toReal ≤
      ballVolumeBound D n R * (μ B).toReal + ε*slicingError n (R-r) := by
  have hdim j (hj : j≤n) x t (ht : t∈((Q.pair j).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair j).P.val x) : t.card≤j+1 := by
    apply (Q.point x).dimension_bound _ hj ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  let M : ℕ → ℝ → ℝ≥0∞ := fun j=>
    ballMass (n := n) Γ hΓ (Q.pair (min j n)) μ B (min j n) c
  have hmono j : Monotone (M j) := ballMass_mono Γ hΓ _ _ _ _ _
  have hfin j t : M j t<∞ := by
    apply lt_of_le_of_lt (hmono j (le_max_left t 0))
    exact ballMass_lt_top Γ hΓ hn hK _ μ B _ (hdim _ (min_le_right _ _)) c
      (max t 0) (le_max_right _ _)
  have hstep j (hj : j<n) b (hb : b∈Icc r R) :
      (∫⁻ t in Ioo r b,M j t)≤M (j+1) b+ENNReal.ofReal ε*ENNReal.ofReal (b-r) := by
    simpa only [M,min_eq_left hj.le,min_eq_left (Nat.succ_le_iff.mpr hj)] using
      ballMass_recurrence Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin hj c B hB hdisj r b hr hb.2
  have ht := iterated_mass_bound M n r R ε hrR hε hmono hfin hstep
  have htop := ballMass_top_bound Γ hΓ hn hK (Q.pair n) μ B c hc R hR.le D hD hdeg
  have htop' := ENNReal.toReal_mono (by finiteness) htop
  have hv : (ballMass (n := n) Γ hΓ (Q.pair n) μ B n c R).toReal ≤
      ballVolumeBound D n R * (μ B).toReal := by
    simpa [ballVolumeBound,ENNReal.toReal_mul,ENNReal.toReal_add,div_eq_mul_inv] using htop'
  simp only [M,min_self,zero_min] at ht
  nlinarith

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.BallMass
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

omit [Γ.LocallyFinite] in
include hK in
lemma one_le_ballIntegrand_of_ne_zero
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (c : FinProbability Y) (b : ℝ) (x : X)
    (hx : ballIntegrand (n := n) Γ hΓ Q 0 c b x≠0) :
    1≤ballIntegrand (n := n) Γ hΓ Q 0 c b x := by
  have hex : ∃ σ : SourceTop K n,
      localOriginalArea Γ Q σ 0 {v | centerDistance Γ hΓ K n c v≤b} x≠0 := by
    by_contra! h
    exact hx (by simp only [ballIntegrand,h,tsum_zero])
  obtain ⟨σ,hσ⟩ := hex
  rw [localOriginalArea_zero_eq_count Γ hK] at hσ
  obtain ⟨v,hv⟩ := Measure.count_ne_zero_iff.mp hσ
  calc
    _ = Measure.count ({v} : Set (Fin (n+1) → ℝ)) := (Measure.count_singleton v).symm
    _ ≤ _ := measure_mono (singleton_subset_iff.mpr hv)
    _ = localOriginalArea Γ Q σ 0 {v | centerDistance Γ hΓ K n c v≤b} x :=
      (localOriginalArea_zero_eq_count Γ hK Q σ _ x).symm
    _ ≤ _ := ENNReal.le_tsum (f := fun τ : SourceTop K n =>
      localOriginalArea Γ Q τ 0 {v | centerDistance Γ hΓ K n c v≤b} x) σ

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_3
local instance instCountableSourceTop_3_rdc6552_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance instFiniteSubtypeMemSubgroupStabilizerSourceTop_3_rdc6552_1 (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem zero_ball_mass_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (A : Set X) (hA : IsClopen A)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
    (ballMass (n := n) Γ hΓ (Q.pair 0) μ A 0 c r).toReal ≤
      slicingError n (R-r)/(dividedPower n (R-r)-ballVolumeBound D n R)*ε := by
  let f := ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c r
  let S : Set X := {x | f x≠0}
  have hS : IsClopen S :=
    (ballIntegrand_locallyConstant Γ hΓ hn hK (Q.pair 0) 0 c r hr).isClopen_fiber 0 |>.compl
  let B := A∩S
  have hB : IsClopen B := hA.inter hS
  have hwin (h : H) (x : X) : activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x ⊆
      activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) h x := by
    unfold activeWindow
    split_ifs with hb ha
    · exact subset_rfl
    · exact False.elim (ha hb.1)
    · exact empty_subset _
    · exact subset_rfl
  have hdisjB x : Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)) :=
    fun h k hk=>(hdisj x hk).mono (hwin h x) (hwin k x)
  have he : ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r =
      ballMass (n := n) Γ hΓ (Q.pair 0) μ A 0 c r := by
    have hh := setLIntegral_eq_of_support_subset (μ := μ.restrict A) (s := S) (f := f)
      (show Function.support f⊆S from subset_rfl)
    rw [Measure.restrict_restrict hS.isClosed.measurableSet,inter_comm] at hh
    exact hh
  have hμle : μ B≤ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r := by
    calc
      _ = ∫⁻ _x in B,(1 : ℝ≥0∞) ∂μ := by simp
      _ ≤ _ := setLIntegral_mono' hB.isClosed.measurableSet fun x hx=>
        one_le_ballIntegrand_of_ne_zero Γ hΓ hK (Q.pair 0) c r x hx.2
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hf := ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ B 0 hdim c r hr
  have hμle' := ENNReal.toReal_mono hf.ne hμle
  have hv := iterated_ball_volume Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin c hc
    B hB hdisjB r hr hrR D hD hdeg
  rw [he] at hμle' hv
  exact absorb_nonempty_probability _ _ _ _ _ _ hmargin
    (by unfold ballVolumeBound; positivity) hμle' hv

end Sparse.GraphGeometry

/-! Finite clopen partitions and disjoint translates. -/

namespace Sparse

section

open Set TopologicalSpace

open scoped Pointwise Function

variable {H X : Type*} [Group H] [TopologicalSpace X] [MulAction H X]

lemma exists_clopen_disjoint_translate
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (x : X) (g : H) (hg : g ≠ 1) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ Disjoint U (g • U) := by
  have hne : x ≠ g • x := by
    intro h
    exact hg (IsCancelSMul.eq_one_of_smul h.symm)
  obtain ⟨V, hV, hx, hgx⟩ := exists_isClopen_of_totally_separated hne
  refine ⟨V ∩ (fun y : X => g • y) ⁻¹' Vᶜ,
    hV.inter (hV.compl.preimage (continuous_const_smul g)), ⟨hx, hgx⟩, ?_⟩
  apply Set.disjoint_left.mpr
  intro y hy hgy
  obtain ⟨z, hz, rfl⟩ := hgy
  exact hz.2 hy.1

lemma exists_clopen_disjoint_translates
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (x : X) (s : Finset H) (hs : 1 ∉ s) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ g ∈ s, Disjoint U (g • U) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Set.univ, isClopen_univ, Set.mem_univ _, by simp⟩
  | @insert g s hgs ih =>
      have hgone : g ≠ 1 := by
        intro hg
        exact hs (by simp [hg])
      obtain ⟨U, hU, hxU, hUD⟩ := ih (fun h => hs (Finset.mem_insert_of_mem h))
      obtain ⟨V, hV, hxV, hVD⟩ := exists_clopen_disjoint_translate x g hgone
      refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hVD.mono Set.inter_subset_right (Set.smul_set_mono Set.inter_subset_right)
      · exact (hUD k hk).mono Set.inter_subset_left
          (Set.smul_set_mono Set.inter_subset_left)

theorem exists_separated_clopen_partition
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (s : Finset H) (hs : 1 ∉ s) :
    ∃ (n : ℕ) (W : Fin n → Clopens X),
      (Set.univ : Set X) ⊆ ⋃ j, (W j : Set X) ∧
      Pairwise (Disjoint on W) ∧
      ∀ j g, g ∈ s → Disjoint (W j : Set X) (g • (W j : Set X)) := by
  classical
  choose U hU hx hD using fun x : X => exists_clopen_disjoint_translates x s hs
  let V : X → Opens X := fun x => ⟨U x, (hU x).isOpen⟩
  have hcover : IsOpenCover V := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨n, W, hWsub, hWcover, hWdisj⟩ :=
    hcover.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, hWcover, hWdisj, ?_⟩
  intro j g hg
  obtain ⟨x, hjx⟩ := (hWsub j).2
  exact (hD x g hg).mono hjx (Set.smul_set_mono hjx)

end

open Set Finset

open scoped Pointwise Classical

variable {H Y : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]

lemma finite_push_collisions (W : Finset Y) (U : Set (Y →₀ ℝ))
    (hU : ∀ p∈U,p≠0 ∧ p.support⊆W) :
    {h : H | ¬Disjoint U (OrbitForms.push h '' U)}.Finite := by
  have hf : (⋃ w∈(W : Set Y),{h : H | h•w∈W}).Finite := by
    apply W.finite_toSet.biUnion
    intro w _
    exact Set.Finite.preimage (fun h _ k _ he=>IsCancelSMul.right_cancel h k w he)
      W.finite_toSet
  apply hf.subset
  intro h hh
  obtain ⟨p,hp,q,hq,he⟩ := Set.not_disjoint_iff.mp hh
  obtain ⟨w,hw⟩ := Finsupp.support_nonempty_iff.mpr (hU q hq).1
  apply Set.mem_iUnion₂.mpr
  refine ⟨w,(hU q hq).2 hw,?_⟩
  apply (hU p hp).2
  rw [Finsupp.mem_support_iff,← he,OrbitForms.push_apply,inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hw

variable {X : Type*} [TopologicalSpace X] [MulAction H X]

omit [IsCancelSMul H Y] [TopologicalSpace X] in
lemma activeWindows_disjoint (A : Set X) (U : Set (Y →₀ ℝ))
    (hA : ∀ g : H,g≠1 → ¬Disjoint U (OrbitForms.push g '' U) →
      Disjoint A (g•A)) :
    ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow A U h x) (activeWindow A U k x)) := by
  intro x h k hne
  by_cases hh : h⁻¹•x∈A
  · by_cases hk : k⁻¹•x∈A
    · simp only [activeWindow,hh,hk,ite_eq_left]
      apply Set.disjoint_left.mpr
      rintro p ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
      have hd : h⁻¹*k≠1 := fun he=>hne (inv_mul_eq_one.mp he)
      have hc : ¬Disjoint U (OrbitForms.push (h⁻¹*k) '' U) := by
        apply Set.not_disjoint_iff.mpr
        refine ⟨u,hu,v,hv,?_⟩
        rw [OrbitForms.push_mul,he,OrbitForms.push_inv_push]
      have ha := Set.disjoint_left.mp (hA _ hd hc) hh
      apply ha
      refine ⟨k⁻¹•x,hk,?_⟩
      simp [mul_smul]
    · simp [activeWindow,hk]
  · simp [activeWindow,hh]

-- no instance assumptions on properness of ambient action are needed

lemma exists_disjoint_active_partition
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (W : Finset Y) (U : Set (Y →₀ ℝ))
    (hU : ∀ p∈U,p≠0 ∧ p.support⊆W) :
    ∃ (m : ℕ) (A : Fin m → TopologicalSpace.Clopens X),
      (univ : Set X)⊆⋃ i,(A i : Set X) ∧
      Pairwise (fun i j=>Disjoint (A i : Set X) (A j : Set X)) ∧
      ∀ i x,Pairwise (fun h k : H=>Disjoint
        (activeWindow (A i : Set X) U h x) (activeWindow (A i : Set X) U k x)) := by
  let S := (show ({h : H | ¬Disjoint U (OrbitForms.push h '' U)} \ {1}).Finite from
    (finite_push_collisions W U hU).sdiff).toFinset
  have hS : 1∉S := by simp [S]
  obtain ⟨m,A,hcover,hdisj,hsep⟩ := exists_separated_clopen_partition (X := X) S hS
  refine ⟨m,A,hcover,?_,?_⟩
  · exact fun i j hij=>TopologicalSpace.Clopens.coe_disjoint.mpr (hdisj hij)
  · intro i
    apply activeWindows_disjoint
    intro g hg hc
    exact hsep i g (by simp [S,hg,hc])

end Sparse

namespace Sparse.GraphGeometry

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK in
lemma exists_disjoint_ball_partition (c : FinProbability Y) {R : ℝ} (hR : 0≤R) :
    ∃ (m : ℕ) (A : Fin m → TopologicalSpace.Clopens X),
      (univ : Set X)⊆⋃ i,(A i : Set X) ∧
      Pairwise (fun i j=>Disjoint (A i : Set X) (A j : Set X)) ∧
      ∀ i x,Pairwise (fun h k : H=>Disjoint
        (activeWindow (A i : Set X) (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
        (activeWindow (A i : Set X) (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)) := by
  apply exists_disjoint_active_partition (ballSupport Γ c n R)
  rintro v ⟨hv,hball⟩
  let p := pointProbability K ⟨v,hv⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hpK := pointProbability_face K ⟨v,hv⟩
  change centerDistance Γ hΓ K n c v≤R at hball
  rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at hball
  rw [← hp]
  exact ⟨Finsupp.support_nonempty_iff.mp p.coeff_support_nonempty,
    ballSupport_contains Γ hΓ hn K hK c p hpK hR hball⟩

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_4
local instance instCountableSourceTop_4_rdc6552_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance instFiniteSubtypeMemSubgroupStabilizerSourceTop_4_rdc6552_1 (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem global_zero_ball_mass_bound_oai (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R : ℝ} (hR : 0<R) (c : FinProbability Y) (hc : c.coeff.support.card≤n+1)
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
    ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) R n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) R
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r).toReal≤C*ε := by
  obtain ⟨m,A,hcover,hdisj,hactive⟩ := exists_disjoint_ball_partition (H := H) (X := X) Γ hΓ hn hK c hR.le
  let C := slicingError n (R-r)/(dividedPower n (R-r)-ballVolumeBound D n R)
  have hC : 0≤C := by
    apply div_nonneg _ (sub_pos.mpr hmargin).le
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hrR) _) (Nat.cast_nonneg _)
  refine ⟨m*C,mul_nonneg (Nat.cast_nonneg _) hC,?_⟩
  intro ε hε Q hmin
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hu : (⋃ i,(A i : Set X))=univ := Set.eq_univ_iff_forall.mpr fun x=>hcover (Set.mem_univ x)
  have he : ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r=
      ∑ i : Fin m,ballMass (n := n) Γ hΓ (Q.pair 0) μ (A i : Set X) 0 c r := by
    unfold ballMass
    rw [← hu,lintegral_iUnion (fun i=>(A i).isClosed.measurableSet) hdisj,tsum_fintype]
  rw [he,ENNReal.toReal_sum (fun i _=>(ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ
    (A i : Set X) 0 hdim c r hr).ne)]
  calc
    _ ≤ ∑ _i : Fin m,C*ε := Finset.sum_le_sum fun i _=>
      zero_ball_mass_bound Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin c hc
        (A i : Set X) (A i).isClopen (hactive i) r hr hrR D hD hdeg hmargin
    _ = (m*C)*ε := by simp [mul_assoc]

end

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound_oai.{u_1, u_2, u_3} := @OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound_oai.{u_1, u_2, u_3}

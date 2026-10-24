-- Prove2me | solution 1 for MaxLatticeFree.Geometry.lambdaFree_add_span_recCone
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:54:58.117241+00:00
-- url     : https://prove2.me/submissions/39fbb6a8-255f-4cd5-b129-e6f2e1f3e03c

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_recCone
import Theorems.Thm_MaxLatticeFree_Geometry_exists_lattice_point_near_halfLine

open Pointwise


/- Complete local helper proofs from InteriorAdd.lean. InteriorAdd was supplied by the root worker; other helpers by this worker. -/

open Set Pointwise

namespace MaxLatticeFree.Geometry.RecessionProof

lemma interior_add_submodule_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : Set E) (hA : Convex ℝ A)
    (K : Submodule ℝ E) (hK : K ≤ (affineSpan ℝ A).direction) :
    interior (A + (K : Set E)) ⊆ interior A + (K : Set E) := by
  intro x hx
  have hsub : A + (K : Set E) ⊆ (affineSpan ℝ A : Set E) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    change a + b ∈ affineSpan ℝ A
    rw [add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction (hK hb) (mem_affineSpan ℝ ha)
  have hspan : affineSpan ℝ A = ⊤ := by
    apply top_unique
    have htop := (hA.add K.convex).interior_nonempty_iff_affineSpan_eq_top.mp ⟨x, hx⟩
    rw [← htop]
    exact affineSpan_le.mpr hsub
  have hAne : (interior A).Nonempty := hA.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  let U := interior A + (K : Set E)
  have hUopen : IsOpen U := isOpen_interior.add_right
  have hUconv : Convex ℝ U := hA.interior.add K.convex
  have hUne : U.Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    exact ⟨a + 0, a, ha, 0, K.zero_mem, rfl⟩
  have hcover : A + (K : Set E) ⊆ closure U := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' : a ∈ closure (interior A) := by
      rw [hA.closure_interior_eq_closure_of_nonempty_interior hAne]
      exact subset_closure ha
    have hp : closure (interior A) ⊆ (fun y : E => y + b) ⁻¹' closure U := by
      apply closure_minimal
      · intro y hy
        exact subset_closure ⟨y, hy, b, hb, rfl⟩
      · exact isClosed_closure.preimage (continuous_id.add_const b)
    exact hp ha'
  have hUi : (interior U).Nonempty := by rwa [hUopen.interior_eq]
  have h := interior_mono hcover hx
  rwa [hUconv.interior_closure_eq_interior_of_nonempty_interior hUi, hUopen.interior_eq] at h

end MaxLatticeFree.Geometry.RecessionProof



/- Complete local helper proofs from ConeAlgebra.lean. InteriorAdd was supplied by the root worker; other helpers by this worker. -/

namespace MaxLatticeFree.Geometry.RecessionProof

open Set
open scoped Pointwise

variable {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}

lemma rec_zero : (0 : EuclideanSpace ℝ (Fin n)) ∈ recCone S := by
  intro x hx t ht
  simpa using hx

lemma rec_add {r s : EuclideanSpace ℝ (Fin n)} (hr : r ∈ recCone S)
    (hs : s ∈ recCone S) : r+s ∈ recCone S := by
  intro x hx t ht
  simpa [smul_add, add_assoc] using hs (x+t•r) (hr x hx t ht) t ht

lemma rec_smul {r : EuclideanSpace ℝ (Fin n)} (hr : r ∈ recCone S)
    {a : ℝ} (ha : 0 ≤ a) : a•r ∈ recCone S := by
  intro x hx t ht
  simpa [smul_smul] using hr x hx (t*a) (mul_nonneg ht ha)

lemma span_rec_difference {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Submodule.span ℝ (recCone S)) :
    ∃ r ∈ recCone S, ∃ s ∈ recCone S, v = r-s := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨v, hv, 0, rec_zero, by simp⟩
  | zero => exact ⟨0, rec_zero, 0, rec_zero, by simp⟩
  | add x y _ _ hx hy =>
    rcases hx with ⟨r, hr, s, hs, rfl⟩
    rcases hy with ⟨r', hr', s', hs', rfl⟩
    exact ⟨r+r', rec_add hr hr', s+s', rec_add hs hs', by abel⟩
  | smul a x _ hx =>
    rcases hx with ⟨r, hr, s, hs, rfl⟩
    by_cases ha : 0 ≤ a
    · exact ⟨a•r, rec_smul hr ha, a•s, rec_smul hs ha, smul_sub _ _ _⟩
    · exact ⟨(-a)•s, rec_smul hs (by linarith), (-a)•r,
        rec_smul hr (by linarith), by module⟩

lemma rec_subset_subspace {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (hS : S ⊆ V) (hne : S.Nonempty) : recCone S ⊆ V := by
  obtain ⟨x, hx⟩ := hne
  intro r hr
  have hxr := hS (hr x hx 1 zero_le_one)
  simpa using V.sub_mem hxr (hS hx)

lemma lattice_subset {Λ : AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (hΛ : IsLatticeOf Λ V) :
    (Λ : Set (EuclideanSpace ℝ (Fin n))) ⊆ V := by
  obtain ⟨m, a, ha, hspan, rfl⟩ := hΛ
  change AddSubgroup.closure (Set.range a) ≤ V.toAddSubgroup
  apply (AddSubgroup.closure_le V.toAddSubgroup).mpr
  rintro _ ⟨i, rfl⟩
  exact hspan ▸ Submodule.subset_span (mem_range_self i)

lemma mem_intW_iff (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : V) :
    (x : EuclideanSpace ℝ (Fin n)) ∈ intW (V : Set _) S ↔
      x ∈ interior (((↑) : V → EuclideanSpace ℝ (Fin n)) ⁻¹' S) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  constructor
  · rintro ⟨hx, ε, hε, hb⟩
    refine ⟨ε, hε, ?_⟩
    intro y hy
    exact hb ⟨hy, y.2⟩
  · rintro ⟨ε, hε, hb⟩
    refine ⟨hb (Metric.mem_ball_self hε), ε, hε, ?_⟩
    rintro y ⟨hy, hyV⟩
    exact hb (show (⟨y, hyV⟩ : V) ∈ Metric.ball x ε from hy)

lemma interior_add_rec {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    {x r : EuclideanSpace ℝ (Fin n)} (hx : x ∈ intW (V : Set _) S)
    (hr : r ∈ recCone S) (hrV : r ∈ V) : x+r ∈ intW (V : Set _) S := by
  rcases hx with ⟨hx, ε, hε, hb⟩
  refine ⟨by simpa using hr x hx 1 zero_le_one, ε, hε, ?_⟩
  rintro y ⟨hy, hyV⟩
  have hy' : y-r ∈ Metric.ball x ε ∩ (V : Set _) := by
    refine ⟨?_, V.sub_mem hyV hrV⟩
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    convert hy using 1
    congr 1
    abel
  have hh := hr (y-r) (hb hy') 1 zero_le_one
  simpa using hh

end MaxLatticeFree.Geometry.RecessionProof


/- Complete local helper proofs from SubtypeBridge.lean. InteriorAdd was supplied by the root worker; other helpers by this worker. -/

namespace MaxLatticeFree.Geometry.RecessionProof

open Set
open scoped Pointwise

lemma shift_to_interior {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSV : S ⊆ V) (hS : Convex ℝ S)
    (hne : S.Nonempty)
    (hadd : ∀ A : Set V, Convex ℝ A → ∀ K : Submodule ℝ V,
      K ≤ (affineSpan ℝ A).direction →
      interior (A+(K : Set V)) ⊆ interior A+(K : Set V))
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ intW (V : Set _) (S+(Submodule.span ℝ (recCone S) : Set _))) :
    ∃ r ∈ recCone S, y+r ∈ intW (V : Set _) S := by
  let A : Set V := ((↑) : V → EuclideanSpace ℝ (Fin n)) ⁻¹' S
  let C : Set V := ((↑) : V → EuclideanSpace ℝ (Fin n)) ⁻¹' recCone S
  let K : Submodule ℝ V := Submodule.span ℝ C
  have hrecV : recCone S ⊆ V := rec_subset_subspace hSV hne
  have hspanV : Submodule.span ℝ (recCone S) ≤ V := Submodule.span_le.mpr hrecV
  have hsumV : S+(Submodule.span ℝ (recCone S) : Set _) ⊆ (V : Set _) := by
    rintro _ ⟨x, hx, r, hr, rfl⟩
    exact V.add_mem (hSV hx) (hspanV hr)
  have hyV : y ∈ V := hsumV hy.1
  have hCimage : V.subtype '' C = recCone S := by
    apply Set.ext
    intro r
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hr
      exact ⟨⟨r, hrecV hr⟩, hr, rfl⟩
  have hmap : K.map V.subtype = Submodule.span ℝ (recCone S) := by
    dsimp [K]
    rw [Submodule.map_span, hCimage]
  have hpre : ((↑) : V → EuclideanSpace ℝ (Fin n)) ⁻¹'
      (S+(Submodule.span ℝ (recCone S) : Set _)) = A+(K : Set V) := by
    ext x
    constructor
    · rintro ⟨s, hs, r, hr, hsr⟩
      rw [← hmap] at hr
      obtain ⟨v, hv, rfl⟩ := hr
      refine ⟨⟨s, hSV hs⟩, hs, v, hv, ?_⟩
      exact Subtype.ext hsr
    · rintro ⟨s, hs, r, hr, rfl⟩
      refine ⟨s, hs, r, ?_, rfl⟩
      rw [← hmap]
      exact Submodule.mem_map_of_mem hr
  have hdir : K ≤ (affineSpan ℝ A).direction := by
    apply Submodule.span_le.mpr
    intro r hr
    obtain ⟨x, hx⟩ := hne
    let x₀ : V := ⟨x, hSV hx⟩
    have hx₀ : x₀ ∈ A := hx
    have hxr : x₀+r ∈ A := by
      change x+(r : EuclideanSpace ℝ (Fin n)) ∈ S
      simpa using hr x hx 1 zero_le_one
    have hh := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ A hxr) (subset_affineSpan ℝ A hx₀)
    simpa using hh
  have hA : Convex ℝ A := hS.linear_preimage V.subtype
  have hyint : (⟨y, hyV⟩ : V) ∈ interior (A+(K : Set V)) := by
    rw [← hpre]
    exact (mem_intW_iff V ⟨y, hyV⟩).mp hy
  obtain ⟨x, hx, v, hv, hxy⟩ := hadd A hA K hdir hyint
  have hxint : (x : EuclideanSpace ℝ (Fin n)) ∈ intW (V : Set _) S :=
    (mem_intW_iff V x).mpr hx
  have hvspan : (v : EuclideanSpace ℝ (Fin n)) ∈ Submodule.span ℝ (recCone S) := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hv
  obtain ⟨r, hr, s, hs, hvs⟩ := span_rec_difference hvspan
  refine ⟨s, hs, ?_⟩
  have hxy' : (x : EuclideanSpace ℝ (Fin n)) + v = y := congrArg Subtype.val hxy
  have heq : y+s = (x : EuclideanSpace ℝ (Fin n))+r := by rw [← hxy', hvs]; abel
  rw [heq]
  exact interior_add_rec hxint hr (hrecV hr)

end MaxLatticeFree.Geometry.RecessionProof


/- Complete local helper proofs from LatticeContradiction.lean. InteriorAdd was supplied by the root worker; other helpers by this worker. -/

namespace MaxLatticeFree.Geometry.RecessionProof

open Set

lemma no_forward_interior {n : ℕ} {Λ : AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (hΛ : IsLatticeOf Λ V)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsLambdaFree Λ V S)
    {y r : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Λ) (hr : r ∈ recCone S)
    (hyr : y+r ∈ intW (V : Set _) S) : False := by
  have hnot (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Λ)
      (hzi : z ∈ intW (V : Set _) S) : False := by
    have hh : z ∈ (Λ : Set _) ∩ intW (V : Set _) S := ⟨hz, hzi⟩
    rw [hS.2.2] at hh
    exact hh
  by_cases hr0 : r = 0
  · exact hnot y hy (by simpa [hr0] using hyr)
  have hrV : r ∈ V := rec_subset_subspace hS.1 ⟨_, hyr.1⟩ hr
  rcases hyr with ⟨hyr, ε, hε, hb⟩
  obtain ⟨z, hz, _, hd⟩ := exists_lattice_point_near_halfLine Λ V hΛ y hy r hrV hr0
    (ε/2) (half_pos hε) 1 zero_le_one
  have hne : ({p : EuclideanSpace ℝ (Fin n) | ∃ t : ℝ, 1 ≤ t ∧ p=y+t•r}).Nonempty :=
    ⟨y+r, 1, le_rfl, by simp⟩
  obtain ⟨w, ⟨t, ht, rfl⟩, hdist⟩ := Metric.infDist_lt_iff hne |>.mp hd
  have hzV := lattice_subset hΛ hz
  have hball : Metric.ball z (ε/2) ∩ (V : Set _) ⊆ S := by
    rintro x ⟨hx, hxV⟩
    have hnear : dist x (y+t•r) < ε := by
      have htri := dist_triangle x z (y+t•r)
      have hx' : dist x z < ε/2 := hx
      linarith
    have hshift : x-(t-1)•r ∈ Metric.ball (y+r) ε ∩ (V : Set _) := by
      refine ⟨?_, V.sub_mem hxV (V.smul_mem _ hrV)⟩
      rw [Metric.mem_ball, dist_eq_norm]
      rw [dist_eq_norm] at hnear
      convert hnear using 1
      congr 1
      module
    have hh := hr (x-(t-1)•r) (hb hshift) (t-1) (by linarith)
    simpa using hh
  exact hnot z hz ⟨hball ⟨Metric.mem_ball_self (half_pos hε), hzV⟩,
    ε/2, half_pos hε, hball⟩

end MaxLatticeFree.Geometry.RecessionProof


open MaxLatticeFree.Geometry.RecessionProof

namespace MaxLatticeFree.Geometry

theorem _root_.solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsLambdaFree Λ V S) :
    IsLambdaFree Λ V (S + (Submodule.span ℝ (recCone S) : Set (EuclideanSpace ℝ (Fin n)))) := by
  by_cases hne : S.Nonempty
  · have hspanV : Submodule.span ℝ (recCone S) ≤ V :=
      Submodule.span_le.mpr (rec_subset_subspace hS.1 hne)
    refine ⟨?_, hS.2.1.add (Submodule.convex _), ?_⟩
    · rintro _ ⟨x, hx, r, hr, rfl⟩
      exact V.add_mem (hS.1 hx) (hspanV hr)
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hyΛ, hy⟩
      obtain ⟨r, hr, hyr⟩ := shift_to_interior V hS.1 hS.2.1 hne interior_add_submodule_subset hy
      exact no_forward_interior hΛ hS hyΛ hr hyr
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [hempty, Set.empty_add] using hS


end MaxLatticeFree.Geometry

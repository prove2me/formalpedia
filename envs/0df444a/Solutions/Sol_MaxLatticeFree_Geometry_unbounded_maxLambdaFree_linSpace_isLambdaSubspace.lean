-- Prove2me | solution 1 for MaxLatticeFree.Geometry.unbounded_maxLambdaFree_linSpace_isLambdaSubspace
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:15:34.396152+00:00
-- url     : https://prove2.me/submissions/a6a6a53d-a7ee-4baf-838a-7e3f7b538482

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_recCone
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Theorems.Thm_MaxLatticeFree_Geometry_exists_lattice_point_near_subspace


/- Complete local helper proofs from Geometry.lean; collaboration provenance is retained in the source and verification report. -/

open Set Pointwise

namespace MaxLatticeFree.Geometry.RationalLinealityProof

section
variable {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}

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

end

/- Complete helper supplied by the coordinator for Lemma 16, copied unchanged. -/
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

/- Complete full-dimensional helpers supplied by the classification worker. -/
lemma affineSpan_eq_of_full_dim {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSV : S ⊆ V) (hne : S.Nonempty)
    (hdim : affDim S = (Module.finrank ℝ V : ℤ)) :
    affineSpan ℝ S = V.toAffineSubspace := by
  have hle : affineSpan ℝ S ≤ V.toAffineSubspace := affineSpan_le.mpr hSV
  have hdir : (affineSpan ℝ S).direction ≤ V := by
    simpa only [Submodule.toAffineSubspace_direction] using AffineSubspace.direction_le hle
  have hfin : Module.finrank ℝ (affineSpan ℝ S).direction = Module.finrank ℝ V := by
    simp only [affDim, if_pos hne] at hdim
    exact_mod_cast hdim
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ (hne.affineSpan ℝ) hle
  simpa only [Submodule.toAffineSubspace_direction] using Submodule.eq_of_le_of_finrank_eq hdir hfin

lemma interior_subtype_nonempty_of_full_dim {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSV : S ⊆ V) (hS : Convex ℝ S)
    (hne : S.Nonempty) (hdim : affDim S = (Module.finrank ℝ V : ℤ)) :
    (interior ((Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' S)).Nonempty := by
  have hspan := affineSpan_eq_of_full_dim V S hSV hne hdim
  have hInt := hne.intrinsicInterior hS
  unfold intrinsicInterior at hInt
  rw [hspan] at hInt
  exact Set.image_nonempty.mp hInt


end MaxLatticeFree.Geometry.RationalLinealityProof


/- Complete local helper proofs from Lineality.lean; collaboration provenance is retained in the source and verification report. -/

open Set Pointwise

namespace MaxLatticeFree.Geometry.RationalLinealityProof

lemma mem_linSpace_iff_all {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {r : EuclideanSpace ℝ (Fin n)} :
    r ∈ linSpace S ↔ ∀ x ∈ S, ∀ t : ℝ, x+t•r ∈ S := by
  constructor
  · rintro ⟨hr, hneg⟩ x hx t
    by_cases ht : 0 ≤ t
    · exact hr x hx t ht
    · have h := hneg x hx (-t) (by linarith)
      simpa using h
  · intro h
    refine ⟨fun x hx t _ => h x hx t, fun x hx t _ => ?_⟩
    simpa using h x hx (-t)

def lineality {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := linSpace S
  zero_mem' := mem_linSpace_iff_all.mpr (by simp)
  add_mem' := by
    intro r s hr hs
    rw [mem_linSpace_iff_all] at hr hs ⊢
    intro x hx t
    simpa [smul_add, add_assoc] using hs (x+t•r) (hr x hx t) t
  smul_mem' := by
    intro a r hr
    rw [mem_linSpace_iff_all] at hr ⊢
    intro x hx t
    simpa [smul_smul] using hr x hx (t*a)

lemma lineality_le {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hSV : S ⊆ V) (hne : S.Nonempty) :
    lineality S ≤ V := by
  intro r hr
  obtain ⟨x, hx⟩ := hne
  have h := mem_linSpace_iff_all.mp hr x hx 1
  simpa using V.sub_mem (hSV h) (hSV hx)

lemma interior_add_lineality {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))} {x r : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ intW (V : Set _) S) (hr : r ∈ lineality S) (hrV : r ∈ V) :
    x+r ∈ intW (V : Set _) S :=
  interior_add_rec hx hr.1 hrV

lemma intW_disjoint_closure_group {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsLambdaFree Λ V S) (hne : S.Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ intW (V : Set _) S) :
    x ∉ closure ((Λ ⊔ (lineality S).toAddSubgroup : AddSubgroup _) : Set _) := by
  intro hcl
  obtain ⟨hxS, ε, hε, hball⟩ := hx
  obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.mp hcl (ε/2) (by positivity)
  obtain ⟨a, ha, l, hl, rfl⟩ := AddSubgroup.mem_sup.mp hz
  have hlV : l ∈ V := lineality_le V hS.1 hne hl
  have haV : a ∈ V := lattice_subset hΛ ha
  have hazV : a+l ∈ V := V.add_mem haV hlV
  have hazint : a+l ∈ intW (V : Set _) S := by
    have hdist : dist (a+l) x < ε/2 := by simpa [dist_comm] using hzx
    refine ⟨hball ⟨by simpa using (hdist.trans (by linarith : ε/2 < ε)), hazV⟩,
      ε/2, by positivity, ?_⟩
    rintro y ⟨hy, hyV⟩
    apply hball
    refine ⟨?_, hyV⟩
    change dist y x < ε
    have htri := dist_triangle y (a+l) x
    change dist y (a+l) < ε/2 at hy
    linarith
  have haint := interior_add_lineality hazint ((lineality S).neg_mem hl) (V.neg_mem hlV)
  have hempty : a ∈ (Λ : Set _) ∩ intW (V : Set _) S := ⟨ha, by simpa using haint⟩
  rw [hS.2.2] at hempty
  exact hempty

end MaxLatticeFree.Geometry.RationalLinealityProof


/- Complete local helper proofs from SmallVectors.lean; collaboration provenance is retained in the source and verification report. -/

open Set Filter Topology

namespace MaxLatticeFree.Geometry.RationalLinealityProof

lemma exists_line_in_closure_of_small {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : AddSubgroup E) (K : Submodule ℝ E)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ x ∈ G, x ∈ K ∧ x ≠ 0 ∧ ‖x‖ < ε) :
    ∃ r ∈ K, ‖r‖ = 1 ∧ ∀ t : ℝ, t • r ∈ closure (G : Set E) := by
  have he : ∀ n : ℕ, 0 < (1 : ℝ) / (n+1) := by intro n; positivity
  choose x hxG hxK hx0 hxn using fun n : ℕ => hsmall (1 / ((n : ℝ)+1)) (he n)
  have hnorm : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (hxn n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let v : ℕ → E := fun n => ‖x n‖⁻¹ • x n
  have hvnorm : ∀ n, ‖v n‖ = 1 := by
    intro n
    simp [v, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hx0 n))]
  obtain ⟨r, hr, φ, hφ, hφr⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    (fun n => show v n ∈ Metric.sphere 0 1 by simpa using hvnorm n)
  have hrnorm : ‖r‖ = 1 := by simpa using hr
  have hrK : r ∈ K := K.closed_of_finiteDimensional.mem_of_tendsto hφr
    (Eventually.of_forall (fun n => K.smul_mem _ (hxK (φ n))))
  refine ⟨r, hrK, hrnorm, ?_⟩
  intro t
  let a : ℕ → ℝ := fun n => ‖x (φ n)‖
  have ha : ∀ n, 0 < a n := fun n => norm_pos_iff.mpr (hx0 (φ n))
  have ha0 : Tendsto a atTop (𝓝 0) := hnorm.comp hφ.tendsto_atTop
  let c : ℕ → ℝ := fun n => (⌊t / a n⌋ : ℤ) * a n
  have hc : Tendsto c atTop (𝓝 t) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n => t-a n) atTop (𝓝 t) by simpa using tendsto_const_nhds.sub ha0)
      tendsto_const_nhds
    · intro n
      have h := Int.sub_floor_div_mul_lt t (ha n)
      dsimp [c]
      linarith
    · intro n
      have h := Int.sub_floor_div_mul_nonneg t (ha n)
      dsimp [c]
      linarith
  have hcG : ∀ n, c n • v (φ n) ∈ G := by
    intro n
    have heq : c n • v (φ n) = (⌊t / a n⌋ : ℤ) • x (φ n) := by
      rw [← Int.cast_smul_eq_zsmul ℝ]
      dsimp [c, v, a]
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ (ne_of_gt (ha n)), mul_one]
    rw [heq]
    exact G.zsmul_mem (hxG (φ n)) _
  exact isClosed_closure.mem_of_tendsto (hc.smul hφr)
    (Eventually.of_forall (fun n => subset_closure (hcG n)))

end MaxLatticeFree.Geometry.RationalLinealityProof


/- Complete local helper proofs from Enlargement.lean; collaboration provenance is retained in the source and verification report. -/

open Set Pointwise

namespace MaxLatticeFree.Geometry.RationalLinealityProof

lemma intW_add_subset {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSV : S ⊆ V) (hS : Convex ℝ S)
    (hne : S.Nonempty) (hdim : affDim S = (Module.finrank ℝ V : ℤ))
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hKV : K ≤ V) :
    intW (V : Set _) (S+(K : Set _)) ⊆ intW (V : Set _) S + (K : Set _) := by
  let A : Set V := ((↑) : V → EuclideanSpace ℝ (Fin n)) ⁻¹' S
  let K' : Submodule ℝ V := K.comap V.subtype
  have hpre : ((↑) : V → EuclideanSpace ℝ (Fin n)) ⁻¹' (S+(K : Set _)) =
      A+(K' : Set V) := by
    ext x
    constructor
    · rintro ⟨s, hs, r, hr, hsr⟩
      exact ⟨⟨s, hSV hs⟩, hs, ⟨r, hKV hr⟩, hr, Subtype.ext hsr⟩
    · rintro ⟨s, hs, r, hr, rfl⟩
      exact ⟨s, hs, r, hr, rfl⟩
  have hA : Convex ℝ A := hS.linear_preimage V.subtype
  have hAi : (interior A).Nonempty := interior_subtype_nonempty_of_full_dim V S hSV hS hne hdim
  have hspan : affineSpan ℝ A = ⊤ := hA.interior_nonempty_iff_affineSpan_eq_top.mp hAi
  have hdir : K' ≤ (affineSpan ℝ A).direction := by rw [hspan]; simp
  intro y hy
  have hyV : y ∈ V := by
    obtain ⟨s, hs, r, hr, heq⟩ := hy.1
    rw [← heq]
    exact V.add_mem (hSV hs) (hKV hr)
  have hyi : (⟨y, hyV⟩ : V) ∈ interior (A+(K' : Set V)) := by
    rw [← hpre]
    exact (mem_intW_iff V ⟨y, hyV⟩).mp hy
  obtain ⟨x, hx, k, hk, hxy⟩ := interior_add_submodule_subset A hA K' hdir hyi
  exact ⟨x, (mem_intW_iff V x).mpr hx, k, hk, congrArg Subtype.val hxy⟩

lemma closure_submodule_le_lineality {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ V S)
    (hne : S.Nonempty) (hdim : affDim S = (Module.finrank ℝ V : ℤ))
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hKV : K ≤ V)
    (hK : (K : Set (EuclideanSpace ℝ (Fin n))) ⊆
      closure ((Λ ⊔ (lineality S).toAddSubgroup : AddSubgroup (EuclideanSpace ℝ (Fin n))) :
        Set (EuclideanSpace ℝ (Fin n)))) :
    K ≤ lineality S := by
  let G := Λ ⊔ (lineality S).toAddSubgroup
  have hfree : IsLambdaFree Λ V (S+(K : Set _)) := by
    refine ⟨?_, hS.1.2.1.add K.convex, ?_⟩
    · rintro _ ⟨s, hs, k, hk, rfl⟩
      exact V.add_mem (hS.1.1 hs) (hKV hk)
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hyΛ, hy⟩
      obtain ⟨x, hx, k, hk, hxy⟩ := intW_add_subset V S hS.1.1 hS.1.2.1 hne hdim K hKV hy
      have hyG : y ∈ G.topologicalClosure := G.le_topologicalClosure ((show Λ ≤ G from le_sup_left) hyΛ)
      have hkG : k ∈ G.topologicalClosure := hK hk
      have hxG : x ∈ closure (G : Set _) := by
        have h := G.topologicalClosure.sub_mem hyG hkG
        change x ∈ G.topologicalClosure
        simpa only [← hxy, add_sub_cancel_right] using h
      exact intW_disjoint_closure_group Λ V hΛ S hS.1 hne hx hxG
  have heq : S+(K : Set _) = S := hS.2 _ hfree (by
    intro x hx
    exact ⟨x, hx, 0, K.zero_mem, add_zero x⟩)
  intro r hr
  apply mem_linSpace_iff_all.mpr
  intro x hx t
  rw [← heq]
  exact ⟨x, hx, t•r, K.smul_mem t hr, rfl⟩

end MaxLatticeFree.Geometry.RationalLinealityProof


/- Complete local helper proofs from ProjectedVectors.lean; collaboration provenance is retained in the source and verification report. -/

open Set Pointwise

namespace MaxLatticeFree.Geometry.RationalLinealityProof

lemma small_projected_vectors {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hLV : L ≤ V)
    (hL : ¬ IsLambdaSubspace Λ V L) :
    ∀ ε : ℝ, 0 < ε → ∃ x ∈ (Λ ⊔ L.toAddSubgroup : AddSubgroup _),
      x ∈ Lᗮ ⊓ V ∧ x ≠ 0 ∧ ‖x‖ < ε := by
  intro ε hε
  obtain ⟨y, hyΛ, hyL, hyd⟩ := exists_lattice_point_near_subspace Λ V hΛ L hLV hL ε hε
  obtain ⟨l, hl, hyl⟩ := (Metric.infDist_lt_iff ⟨0, L.zero_mem⟩).mp hyd
  let x := y-L.starProjection y
  have hxO : x ∈ Lᗮ := L.sub_starProjection_mem_orthogonal y
  have hpL : L.starProjection y ∈ L := L.starProjection_apply_mem y
  refine ⟨x, ?_, ⟨hxO, V.sub_mem (lattice_subset hΛ hyΛ) (hLV hpL)⟩, ?_, ?_⟩
  · exact (Λ ⊔ L.toAddSubgroup : AddSubgroup _).sub_mem ((show Λ ≤ Λ ⊔ L.toAddSubgroup from le_sup_left) hyΛ)
      ((show L.toAddSubgroup ≤ Λ ⊔ L.toAddSubgroup from le_sup_right) hpL)
  · intro hx
    have heq : y = L.starProjection y := sub_eq_zero.mp hx
    exact hyL (heq ▸ hpL)
  · have heq : x = Lᗮ.starProjection (y-l) := by
      rw [map_sub, L.starProjection_orthogonal_val,
        Submodule.starProjection_orthogonal_apply_eq_zero hl, sub_zero]
    rw [heq]
    exact (Lᗮ.norm_starProjection_apply_le (y-l)).trans_lt (by simpa [dist_eq_norm] using hyl)

end MaxLatticeFree.Geometry.RationalLinealityProof


open Set Pointwise
open MaxLatticeFree.Geometry.RationalLinealityProof

namespace MaxLatticeFree.Geometry

theorem _root_.solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ V S)
    (hdim : affDim S = (Module.finrank ℝ V : ℤ)) (hunbdd : ¬ Bornology.IsBounded S) :
    ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), (L : Set (EuclideanSpace ℝ (Fin n))) = linSpace S ∧ IsLambdaSubspace Λ V L := by
  have hne : S.Nonempty := by
    by_contra h
    have heq : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    apply hunbdd
    rw [heq]
    exact Bornology.isBounded_empty
  let L := lineality S
  have hLV : L ≤ V := lineality_le V hS.1.1 hne
  refine ⟨L, rfl, ?_⟩
  by_contra hL
  obtain ⟨r, hr, hrnorm, hrcl⟩ := exists_line_in_closure_of_small
    (Λ ⊔ L.toAddSubgroup) (Lᗮ ⊓ V) (small_projected_vectors Λ V hΛ L hLV hL)
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ {r}
  have hKV : K ≤ V := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hr.2)
  have hKcl : (K : Set (EuclideanSpace ℝ (Fin n))) ⊆
      closure ((Λ ⊔ L.toAddSubgroup : AddSubgroup (EuclideanSpace ℝ (Fin n))) : Set _) := by
    intro x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact hrcl t
  have hrL : r ∈ L := closure_submodule_le_lineality Λ V hΛ S hS hne hdim K hKV hKcl
    (Submodule.subset_span (Set.mem_singleton r))
  have hzero : r = 0 := by
    have hbot : r ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :=
      L.orthogonal_disjoint.le_bot ⟨hrL, hr.1⟩
    exact hbot
  simp [hzero] at hrnorm


end MaxLatticeFree.Geometry

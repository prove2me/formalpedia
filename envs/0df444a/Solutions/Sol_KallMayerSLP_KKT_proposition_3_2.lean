-- Prove2me | solution 1 for KallMayerSLP.KKT.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T05:30:21.691206+00:00
-- url     : https://prove2.me/submissions/a6639d64-e35c-4283-a7fe-d40456113e99

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_subdifferential
import Theorems.Thm_ShorNonsmooth_Subdiff_subdifferential_nonempty_bounded_convex_closed
import Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_of_convexOn_of_unique_subgradient_readable
open Set
open scoped RealInnerProductSpace

open KallMayerSLP.KKT
open scoped Matrix

private lemma affine_subgradient_extension {n m : ℕ}
    (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (hψ : ConvexOn ℝ univ ψ)
    (x : EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin n))
    (hh : ∀ v, ⟪h,v⟫ ≤ ψ (x+A v)-ψ x) :
    ∃ g : EuclideanSpace ℝ (Fin m),
      (∀ w, ⟪g,w⟫ ≤ ψ (x+w)-ψ x) ∧
      ∀ v, ⟪g,A v⟫ = ⟪h,v⟫ := by
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  let k : F → ℝ := fun w => ψ (x+w)-ψ x
  let T : E →L[ℝ] F × ℝ := A.prod (InnerProductSpace.toDual ℝ E h)
  let B : Set (F × ℝ) := {p | k p.1 < p.2}
  have hk : ConvexOn ℝ univ k := by
    refine ⟨convex_univ, ?_⟩
    intro u hu v hv a b ha hb hab
    have hc := hψ.2 (mem_univ (x+u)) (mem_univ (x+v)) ha hb hab
    have he : a • (x+u)+b • (x+v) = x+(a • u+b • v) := by
      calc
        _ = (a+b) • x+(a • u+b • v) := by rw [add_smul]; module
        _ = _ := by rw [hab, one_smul]
    rw [he] at hc
    change ψ (x+(a • u+b • v))-ψ x ≤ a*(ψ (x+u)-ψ x)+b*(ψ (x+v)-ψ x)
    simp only [smul_eq_mul] at hc
    have hbase : a*ψ x+b*ψ x=ψ x := by rw [← add_mul,hab,one_mul]
    nlinarith
  have hkc : Continuous k := continuousOn_univ.mp (hk.continuousOn isOpen_univ)
  have hBc : Convex ℝ B := by
    simpa only [mem_univ, true_and] using hk.convex_strict_epigraph
  have hBo : IsOpen B := isOpen_lt (hkc.comp continuous_fst) continuous_snd
  have hdis : Disjoint B (T.range : Set (F × ℝ)) := by
    apply Set.disjoint_left.mpr
    rintro p hp ⟨v,rfl⟩
    change ψ (x+A v)-ψ x < ⟪h,v⟫ at hp
    exact (not_lt_of_ge (hh v)) hp
  obtain ⟨l,u,hB,hA⟩ := geometric_hahn_banach_open hBc hBo T.range.convex hdis
  have hu : u ≤ 0 := by simpa using hA (T 0) ⟨0,rfl⟩
  have hzero (v : E) : l (T v)=0 := by
    by_contra hv
    let r : ℝ := (u-1)/l (T v)
    have hb := hA (T (r • v)) ⟨r • v,rfl⟩
    rw [map_smul, map_smul] at hb
    change u ≤ r*l (T v) at hb
    have hr : r*l (T v)=u-1 := div_mul_cancel₀ _ hv
    rw [hr] at hb
    linarith
  let c : ℝ := l (0,1)
  have hc : c < 0 := by
    have hb := hB (0,1) (by simp [B,k])
    change c < u at hb
    exact hb.trans_le hu
  have split (w : F) (t : ℝ) : l (w,t)=l (w,0)+t*c := by
    have he : (w,t)=(w,0)+t • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  have bound (w : F) : l (w,k w) ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hb := hB (w,k w+ε/(-c)) (by
      change k w < k w+ε/(-c)
      exact lt_add_of_pos_right _ (div_pos hε (neg_pos.mpr hc)))
    rw [split] at hb
    rw [split]
    have he : (ε/(-c))*c = -ε := by field_simp [ne_of_lt hc] <;> ring
    rw [add_mul,he] at hb
    linarith
  let lx : F →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ F ℝ)
  let g : F := (-c⁻¹) • (InnerProductSpace.toDual ℝ F).symm lx
  have hinner (w : F) : c*⟪g,w⟫ = -l (w,0) := by
    simp only [g, real_inner_smul_left, InnerProductSpace.toDual_symm_apply,
      lx, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    field_simp [ne_of_lt hc]
  refine ⟨g, ?_, ?_⟩
  · intro w
    have hb := bound w
    rw [split] at hb
    have hi := hinner w
    change ⟪g,w⟫ ≤ k w
    by_contra hn
    have hm := mul_pos_of_neg_of_neg hc (sub_neg.mpr (lt_of_not_ge hn))
    nlinarith
  · intro v
    have hz := hzero v
    change l (A v,⟪h,v⟫)=0 at hz
    rw [split] at hz
    apply mul_left_cancel₀ (ne_of_lt hc)
    have hi := hinner (A v)
    nlinarith

private lemma transpose_inner {n m : ℕ} (D : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanLin Dᵀ g, v⟫ = ⟪g, Matrix.toEuclideanLin D v⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma subgradient_eq_of_gradient {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {x g q : EuclideanSpace ℝ (Fin n)}
    (hg : HasGradientAt φ g x) (hq : q ∈ subdifferential φ x) : q = g := by
  let L := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
  have hmin : IsLocalMin (fun y => φ y - L q y) x := by
    apply Filter.Eventually.of_forall
    intro y
    have hy := hq y
    simp only [inner_sub_right] at hy
    change φ x - ⟪q,x⟫ ≤ φ y - ⟪q,y⟫
    linarith
  have hd := hg.hasFDerivAt.sub ((L q).hasFDerivAt)
  have hz := hmin.hasFDerivAt_eq_zero hd
  exact (L.injective (sub_eq_zero.mp hz)).symm

theorem solution {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) :
    (∀ x, (subdifferential φ x).Nonempty ∧ Convex ℝ (subdifferential φ x) ∧
        IsClosed (subdifferential φ x) ∧ Bornology.IsBounded (subdifferential φ x)) ∧
    (∀ x ĝ, HasGradientAt φ ĝ x ↔ subdifferential φ x = {ĝ}) ∧
    (∀ (m : ℕ) (ψ : EuclideanSpace ℝ (Fin m) → ℝ), ConvexOn ℝ Set.univ ψ →
      ∀ (d : EuclideanSpace ℝ (Fin m)) (D : Matrix (Fin m) (Fin n) ℝ),
        ConvexOn ℝ Set.univ (fun x => ψ (d + Matrix.toEuclideanLin D x)) ∧
        ∀ x h, h ∈ subdifferential (fun x => ψ (d + Matrix.toEuclideanLin D x)) x ↔
          ∃ g ∈ subdifferential ψ (d + Matrix.toEuclideanLin D x),
            h = Matrix.toEuclideanLin Dᵀ g) := by
  have hgeom (x : EuclideanSpace ℝ (Fin n)) :
      (subdifferential φ x).Nonempty ∧ Convex ℝ (subdifferential φ x) ∧
      IsClosed (subdifferential φ x) ∧ Bornology.IsBounded (subdifferential φ x) := by
    have he : ShorNonsmooth.Subdiff.subdifferential univ φ x = subdifferential φ x := by
      ext g
      simp [ShorNonsmooth.Subdiff.subdifferential, ShorNonsmooth.Subdiff.IsSubgradient,
        subdifferential]
    have h := ShorNonsmooth.Subdiff.subdifferential_nonempty_bounded_convex_closed
      univ φ hφ x (by simp)
    rw [he] at h
    exact ⟨h.1,h.2.2.1,h.2.2.2,h.2.1⟩
  refine ⟨hgeom, ?_, ?_⟩
  · intro x g
    constructor
    · intro hg
      ext q
      constructor
      · intro hq
        exact Set.mem_singleton_iff.mpr (subgradient_eq_of_gradient hg hq)
      · intro hq
        obtain ⟨q₀,hq₀⟩ := (hgeom x).1
        have hqg := subgradient_eq_of_gradient hg hq₀
        have hqg2 := Set.mem_singleton_iff.mp hq
        simpa [hqg,hqg2] using hq₀
    · intro hs
      apply hasGradientAt_iff_hasFDerivAt.mpr
      apply FunctionalInequalities.Analysis.hasFDerivAt_of_convexOn_of_unique_subgradient_readable hφ x g
      · have hg : g ∈ subdifferential φ x := by rw [hs]; simp
        intro y
        have hy := hg y
        linarith
      · intro q hq
        have hqm : q ∈ subdifferential φ x := by
          intro y
          have hy := hq y
          linarith
        rw [hs] at hqm
        exact Set.mem_singleton_iff.mp hqm
  · intro m ψ hψ d D
    let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      (Matrix.toEuclideanLin D).toContinuousLinearMap
    have hA (v : EuclideanSpace ℝ (Fin n)) : A v = Matrix.toEuclideanLin D v := rfl
    refine ⟨?_, ?_⟩
    · refine ⟨convex_univ, ?_⟩
      intro u hu v hv a b ha hb hab
      have hc := hψ.2 (mem_univ (d+A u)) (mem_univ (d+A v)) ha hb hab
      have he : a • (d+A u)+b • (d+A v) = d+A (a • u+b • v) := by
        rw [map_add,map_smul,map_smul]
        calc
          _ = (a+b) • d+(a • A u+b • A v) := by rw [add_smul]; module
          _ = _ := by rw [hab,one_smul]
      rw [he] at hc
      exact hc
    · intro x h
      constructor
      · intro hh
        have hsupport (v : EuclideanSpace ℝ (Fin n)) :
            ⟪h,v⟫ ≤ ψ ((d+A x)+A v)-ψ (d+A x) := by
          have hv := hh (x+v)
          simpa only [hA, add_sub_cancel_left, map_add, ← add_assoc] using hv
        obtain ⟨g,hg,hgA⟩ := affine_subgradient_extension ψ hψ (d+A x) A h hsupport
        refine ⟨g, ?_, ?_⟩
        · intro z
          simpa only [hA, add_sub_cancel] using hg (z-(d+A x))
        · have he : ∀ v, ⟪h,v⟫ = ⟪Matrix.toEuclideanLin Dᵀ g,v⟫ := by
            intro v
            rw [transpose_inner]
            simpa only [hA] using (hgA v).symm
          exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).injective
            (ContinuousLinearMap.ext he)
      · rintro ⟨g,hg,rfl⟩ z
        rw [transpose_inner]
        have hz := hg (d+Matrix.toEuclideanLin D z)
        simpa only [map_sub, add_sub_add_left_eq_sub] using hz

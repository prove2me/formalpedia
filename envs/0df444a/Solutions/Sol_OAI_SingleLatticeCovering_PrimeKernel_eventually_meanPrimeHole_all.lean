-- Prove2me | solution 1 for OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:54:54.860506+00:00
-- url     : https://prove2.me/submissions/a97c8748-368e-4659-8e46-26de6e2b20e5

import Mathlib
import Definitions.Def_OAIQ16Cd002

section
-- module Solutions.OAIQ16_CD.Compat
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Shears
attribute [-instance] _root_.OAI.SingleLatticeCovering.CoverGeometry.torusMeasure_neg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section



noncomputable section
open MeasureTheory MeasureTheory.Measure Set Module
open scoped Pointwise ENNReal

namespace SingleLatticeCovering.Completion

lemma latticeProjection_surjective {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] : Function.Surjective (latticeProjection L) := by
  intro y
  have hy : ∀ i, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = y i :=
    fun i => QuotientAddGroup.mk'_surjective _ (y i)
  choose x hx using hy
  refine ⟨(latticeBasis L).equivFun.symm x, ?_⟩
  ext i
  change (((latticeBasis L).equivFun ((latticeBasis L).equivFun.symm x)) i :
    AddCircle (1 : ℝ)) = y i
  rw [LinearEquiv.apply_symm_apply]
  exact hx i

lemma latticeProjection_eq_zero_iff {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (x : RealSpace n) :
    latticeProjection L x = 0 ↔ x ∈ L := by
  have hspan : Submodule.span ℤ (Set.range (latticeBasis L)) = L :=
    (IsZLattice.basis L).ofZLatticeBasis_span ℝ
  have hcoords : x ∈ L ↔ ∀ i, (latticeBasis L).repr x i ∈ Set.range (algebraMap ℤ ℝ) := by
    conv_lhs => rw [← hspan]
    exact (latticeBasis L).mem_span_iff_repr_mem ℤ x
  rw [hcoords]
  constructor
  · intro h i
    have hi := congr_fun h i
    change (((latticeBasis L).repr x i : ℝ) : AddCircle (1 : ℝ)) = 0 at hi
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
    exact ⟨z, by simpa using hz⟩
  · intro h
    ext i
    change (((latticeBasis L).repr x i : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    obtain ⟨z, hz⟩ := h i
    exact ⟨z, by simpa using hz⟩



end SingleLatticeCovering.Completion

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section









noncomputable section
namespace SingleLatticeCovering.FiniteKernel
open Module Submodule MeasureTheory
open scoped BigOperators Pointwise

variable {ι : Type*} [Fintype ι]

lemma integerCoordinates_cast (x : integerLattice ι) (i : ι) :
    ((integerCoordinates x i : ℤ) : ℝ) = (x : ι → ℝ) i := by
  have h := (Pi.basisFun ℝ ι).restrictScalars_repr_apply ℤ x i
  simpa [integerCoordinates] using h

lemma integerLattice_covolume : ZLattice.covolume (integerLattice ι) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume),
    ZSpan.fundamentalDomain_pi_basisFun]
  simp [measureReal_def, volume_pi, Measure.pi_pi, Real.volume_Ico]

variable {U : Type*} [AddCommGroup U]

lemma mem_kernelLattice_iff (A : integerLattice ι →ₗ[ℤ] U) (x : integerLattice ι) :
    (x : ι → ℝ) ∈ kernelLattice A ↔ A x = 0 := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    have : y=x := Subtype.ext hxy
    subst y
    exact hy
  · intro h
    exact ⟨x,h,rfl⟩

instance kernelLattice_full [Finite U] (A : integerLattice ι →ₗ[ℤ] U) :
    IsZLattice ℝ (kernelLattice A) where
  span_top := by
    classical
    let : Fintype U := Fintype.ofFinite U
    let q := Fintype.card U
    have hqpos : 0 < q := Fintype.card_pos
    apply top_unique
    rw [←(Pi.basisFun ℝ ι).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let z := (Pi.basisFun ℝ ι).restrictScalars ℤ i
    have hz : (q:ℤ) • (z : ι → ℝ) ∈ kernelLattice A := by
      apply (mem_kernelLattice_iff A ((q:ℤ) • z)).mpr
      rw [map_smul]
      simp [q]
    have hh := (Submodule.span ℝ (kernelLattice A : Set (ι → ℝ))).smul_mem
      ((q:ℝ)⁻¹) (Submodule.subset_span hz)
    have hq : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
    have he : (q:ℝ)⁻¹ • ((q:ℤ) • (z : ι → ℝ)) = (Pi.basisFun ℝ ι) i := by
      ext j
      simp [z, hq]
    rwa [he] at hh

lemma kernelLattice_relIndex (A : integerLattice ι →ₗ[ℤ] U) :
    (kernelLattice A).toAddSubgroup.relIndex (integerLattice ι).toAddSubgroup =
      A.toAddMonoidHom.ker.index := by
  have he : (kernelLattice A).toAddSubgroup.comap (integerLattice ι).toAddSubgroup.subtype =
      A.toAddMonoidHom.ker := by
    ext x
    exact mem_kernelLattice_iff A x
  change ((kernelLattice A).toAddSubgroup.comap (integerLattice ι).toAddSubgroup.subtype).index = _
  rw [he]


theorem kernelLattice_covolume [Finite U] (A : integerLattice ι →ₗ[ℤ] U)
    (hA : Function.Surjective A) :
    ZLattice.covolume (kernelLattice A) = Nat.card U := by
  classical
  have h := ZLattice.covolume_div_covolume_eq_relIndex
    (kernelLattice A) (integerLattice ι) (kernelLattice_le A)
  rw [integerLattice_covolume, div_one, kernelLattice_relIndex] at h
  have hi : A.toAddMonoidHom.ker.index = Nat.card U := by
    rw [AddSubgroup.index_ker]
    have hr : A.toAddMonoidHom.range = ⊤ := AddMonoidHom.range_eq_top.mpr hA
    rw [hr]
    exact Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup U) ≃+ U).toEquiv
  simpa [hi] using h




lemma gridRelationForm_surjective {r d q : ℕ} (a : Fin r → ℤ)
    (h : ∃ z : Fin r → ℤ, (∑ i, a i*z i : ZMod q) = 1) :
    Function.Surjective (gridRelationForm (d:=d) q a) := by
  classical
  obtain ⟨z,hz⟩ := h
  intro c
  choose k hk using (fun j => ZMod.intCast_surjective (c j))
  refine ⟨integerCoordinates.symm (fun ij => z ij.1*k ij.2),?_⟩
  ext j
  change (∑ i, (a i : ZMod q) *
    (integerCoordinates (integerCoordinates.symm (fun ij : Fin r × Fin d => z ij.1*k ij.2)) (i,j) : ZMod q)) = c j
  simp only [LinearEquiv.apply_symm_apply, Int.cast_mul, ←mul_assoc, ←Finset.sum_mul]
  rw [hz, one_mul, hk]

lemma primitive_bezout_mod {r : ℕ} (a : Fin (r+1) → ℤ)
    (ha : Finset.univ.gcd a = 1) :
    ∃ z : Fin r → ℤ, (∑ i, a i.succ*z i : ZMod (a 0).natAbs) = 1 := by
  obtain ⟨z,hz⟩ := Finset.gcd_eq_sum_mul Finset.univ a
  rw [ha, Fin.sum_univ_succ] at hz
  refine ⟨fun i => z i.succ,?_⟩
  have hcast := congrArg (fun t : ℤ => (t : ZMod (a 0).natAbs)) hz
  have hzero : (a 0 : ZMod (a 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl (a 0))
  simpa [Int.cast_add, Int.cast_mul, Int.cast_sum, hzero] using hcast.symm


theorem primitive_grid_covolume {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha0 : a 0 ≠ 0) (hprim : Finset.univ.gcd a = 1) :
    ZLattice.covolume (kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ))) =
      |(a 0 : ℝ)|^d := by
  let : NeZero (a 0).natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
  rw [kernelLattice_covolume _ (gridRelationForm_surjective _ (primitive_bezout_mod a hprim)),
    Nat.card_eq_fintype_card, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ZMod.card, Nat.cast_pow]
  simp



end SingleLatticeCovering.FiniteKernel


end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GridCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace SingleLatticeCovering.RealLatticeCount
open Module MeasureTheory Measure Filter Set Bornology
open scoped Pointwise Topology
variable {ι : Type*} [Fintype ι]

lemma convex_dilation_mono {ι : Type*} [Fintype ι] {S : Set (ι → ℝ)} (hS : Convex ℝ S) (h0 : 0 ∈ S)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : x • S ⊆ y • S := by
  rintro _ ⟨u,hu,rfl⟩
  have hy : 0 < y := hx.trans_le hxy
  refine ⟨(x/y) • u, ?_, ?_⟩
  · have h := hS h0 hu (sub_nonneg.mpr ((div_le_one hy).mpr hxy))
      (div_nonneg hx.le hy.le) (by ring : 1-x/y+x/y=1)
    simpa using h
  · change y • ((x/y) • u) = x • u
    rw [smul_smul]
    congr 1
    field_simp



theorem tendsto_real_grid_count (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] {S : Set (ι → ℝ)}
    (hSb : IsBounded S) (hSm : MeasurableSet S)
    (hSf : volume (frontier S) = 0)
    (hSd : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • S ⊆ y • S) :
    Tendsto (fun t : ℝ => (Nat.card ↥(S ∩ t⁻¹ • (L : Set (ι → ℝ))) : ℝ) /
      t ^ Fintype.card ι) atTop (𝓝 (volume.real S / ZLattice.covolume L)) := by
  let b := IsZLattice.basis L
  let f := (b.ofZLatticeBasis ℝ).equivFun
  have hbound : IsBounded (f '' S) := by
    rw [←NormedSpace.isVonNBounded_iff ℝ] at hSb ⊢
    exact hSb.image ((b.ofZLatticeBasis ℝ).equivFunL : (ι → ℝ) →L[ℝ] ι → ℝ)
  have hmeas : MeasurableSet (f '' S) :=
    (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hSm
  have hfront : volume (frontier (f '' S)) = 0 := by
    have hf : frontier (f '' S) = f '' frontier S := by
      rw [LinearEquiv.image_eq_preimage_symm, LinearEquiv.image_eq_preimage_symm]
      exact (Homeomorph.preimage_frontier (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.symm S).symm
    rw [hf, ZLattice.volume_image_eq_volume_div_covolume L b, hSf, ENNReal.zero_div]
  have hdilate : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • (f '' S) ⊆ y • (f '' S) := by
    intro x y hx hxy
    simp_rw [←image_smul_set]
    exact Set.image_mono (hSd hx hxy)
  have hlim := tendsto_card_div_pow_atTop_volume' (f '' S) hbound hmeas hfront hdilate
  have hv : volume.real (f '' S) = volume.real S / ZLattice.covolume L := by
    simp only [measureReal_def]
    rw [ZLattice.volume_image_eq_volume_div_covolume L b, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le]
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  congr 1
  congr 1
  refine Nat.card_congr <| (f.toEquiv.subtypeEquiv (fun x => ?_)).symm
  dsimp only [f]
  simp only [Set.mem_inter_iff, ← b.ofZLatticeBasis_span ℝ, LinearEquiv.coe_toEquiv,
    Basis.equivFun_apply, Set.mem_image, DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_right, Set.mem_inv_smul_set_iff₀ ht.ne',
    ←Finsupp.coe_smul, ←map_smul, SetLike.mem_coe, Basis.mem_span_iff_repr_mem,
    Pi.basisFun_repr]



theorem tendsto_convex_grid_count (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] {S : Set (ι → ℝ)}
    (hSc : IsCompact S) (hSv : Convex ℝ S) (h0 : 0 ∈ S) :
    Tendsto (fun t : ℝ => (Nat.card ↥(S ∩ t⁻¹ • (L : Set (ι → ℝ))) : ℝ) /
      t ^ Fintype.card ι) atTop (𝓝 (volume.real S / ZLattice.covolume L)) :=
  tendsto_real_grid_count L hSc.isBounded hSc.measurableSet
    (hSv.addHaar_frontier volume) (fun _ _ => convex_dilation_mono hSv h0)


end SingleLatticeCovering.RealLatticeCount


noncomputable section
namespace SingleLatticeCovering.GridGeometry
open MeasureTheory Measure Set Bornology
open scoped BigOperators Pointwise



lemma weightedGridConfiguration_convex {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : Convex ℝ J) (c : Fin r → ℝ) : Convex ℝ (weightedGridConfiguration J c) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact hJ (hx.1 i) (hy.1 i) ha hb hab
  · have he : (fun j => ∑ i, c i*(a • x+b • y) (i,j)) =
        a • (fun j => ∑ i, c i*x (i,j)) + b • (fun j => ∑ i, c i*y (i,j)) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact hJ hx.2 hy.2 ha hb hab

lemma weightedGridConfiguration_closed {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : IsClosed J) (c : Fin r → ℝ) : IsClosed (weightedGridConfiguration J c) := by
  have he : weightedGridConfiguration J c =
      (⋂ i, (fun x : Fin r × Fin d → ℝ => fun j => x (i,j)) ⁻¹' J) ∩
      (fun x : Fin r × Fin d → ℝ => fun j => ∑ i, c i*x (i,j)) ⁻¹' J := by
    ext x
    simp [weightedGridConfiguration]
  rw [he]
  exact (isClosed_iInter (fun i => hJ.preimage (by fun_prop))).inter
    (hJ.preimage (by fun_prop))

lemma weightedGridConfiguration_bounded {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : IsBounded J) (c : Fin r → ℝ) : IsBounded (weightedGridConfiguration J c) := by
  obtain ⟨R,hR⟩ := hJ.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max R 0, fun x hx => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (le_max_right R 0)).mpr
  intro ij
  exact (norm_le_pi_norm (fun j => x (ij.1,j)) ij.2).trans
    ((hR _ (hx.1 ij.1)).trans (le_max_left R 0))

lemma weightedGridConfiguration_compact {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (c : Fin r → ℝ) : IsCompact (weightedGridConfiguration J c) :=
  Metric.isCompact_of_isClosed_isBounded
    (weightedGridConfiguration_closed hJ.isClosed c)
    (weightedGridConfiguration_bounded hJ.isBounded c)

lemma zero_mem_weightedGridConfiguration {r d : ℕ} {J : Set (Fin d → ℝ)}
    (h0 : 0 ∈ J) (c : Fin r → ℝ) : 0 ∈ weightedGridConfiguration J c := by
  constructor
  · intro i
    exact h0
  · convert h0 using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    simp



end SingleLatticeCovering.GridGeometry

namespace SingleLatticeCovering.GridLimit
open MeasureTheory Measure Filter Set
open FiniteKernel GridGeometry RealLatticeCount
open scoped Topology Pointwise


theorem primitive_configuration_limit {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha0 : a 0 ≠ 0) (hprim : Finset.univ.gcd a = 1)
    {J : Set (Fin d → ℝ)} (hJc : IsCompact J) (hJv : Convex ℝ J) (h0 : 0 ∈ J) :
    Tendsto (fun t : ℝ =>
      (Nat.card ↥(weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ)) ∩
        t⁻¹ • (kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ)) :
          Set (Fin r × Fin d → ℝ))) : ℝ) / t^(r*d))
      atTop (𝓝 (volume.real (weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ))) /
        |(a 0:ℝ)|^d)) := by
  let : NeZero (a 0).natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
  have h := tendsto_convex_grid_count
    (kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ)))
    (weightedGridConfiguration_compact hJc (fun i => -(a i.succ:ℝ)/(a 0:ℝ)))
    (weightedGridConfiguration_convex hJv _)
    (zero_mem_weightedGridConfiguration h0 _)
  simpa only [Fintype.card_prod, Fintype.card_fin, primitive_grid_covolume a ha0 hprim] using h


end SingleLatticeCovering.GridLimit

namespace SingleLatticeCovering.GridLimit
open MeasureTheory Measure Filter Set
open FiniteKernel GridGeometry RealLatticeCount
open scoped Topology Pointwise BigOperators

lemma projected_grid_relation_mem {r d : ℕ} (a : Fin (r+1) → ℤ)
    (x : Fin (r+1) → Fin d → ℤ) (h : ∀ j, ∑ i, a i*x i j = 0) :
    (fun ij : Fin r × Fin d => (x ij.1.succ ij.2 : ℝ)) ∈
      kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ)) := by
  let z : integerLattice (Fin r × Fin d) := integerCoordinates.symm (fun ij => x ij.1.succ ij.2)
  have he : (z : Fin r × Fin d → ℝ) = (fun ij => (x ij.1.succ ij.2 : ℝ)) := by
    ext ij
    rw [←integerCoordinates_cast]
    simp [z]
  rw [←he, mem_kernelLattice_iff]
  ext j
  have hcast := congrArg (fun t : ℤ => (t : ZMod (a 0).natAbs)) (h j)
  have hzero : (a 0 : ZMod (a 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl (a 0))
  simpa [gridRelationForm,z,Fin.sum_univ_succ,Int.cast_add,Int.cast_mul,Int.cast_sum,hzero]
    using hcast

lemma omitted_vertex_identity {r d : ℕ} (a : Fin (r+1) → ℤ) (ha0 : a 0 ≠ 0)
    (x : Fin (r+1) → Fin d → ℤ) (h : ∀ j, ∑ i, a i*x i j = 0) (t : ℝ) :
    (fun j => ∑ i : Fin r, (-(a i.succ:ℝ)/(a 0:ℝ))*(t⁻¹*(x i.succ j:ℝ))) =
      (fun j => t⁻¹*(x 0 j:ℝ)) := by
  ext j
  have hh := congrArg (fun z : ℤ => (z:ℝ)) (h j)
  simp only [Fin.sum_univ_succ,Int.cast_add,Int.cast_sum,Int.cast_mul,Int.cast_zero] at hh
  have haR : (a 0:ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha0
  apply (mul_left_cancel₀ haR)
  rw [Finset.mul_sum]
  have he (i : Fin r) : (a 0:ℝ)*(-(a i.succ:ℝ)/(a 0:ℝ)*(t⁻¹*(x i.succ j:ℝ))) =
      -t⁻¹*((a i.succ:ℝ)*(x i.succ j:ℝ)) := by field_simp
  simp_rw [he]
  rw [←Finset.mul_sum]
  rw [show (∑ i : Fin r, (a i.succ:ℝ)*(x i.succ j:ℝ)) = -(a 0:ℝ)*(x 0 j:ℝ) by linarith]
  ring




theorem circuit_count_le_primitive_grid {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha0 : a 0 ≠ 0) (J : Set (Fin d → ℝ)) (hJ : IsCompact J)
    (X : Finset (Fin (r+1) → Fin d → ℤ)) {t : ℝ} (ht : 0 < t)
    (hX : ∀ x ∈ X, ∀ i, (fun j => t⁻¹*(x i j:ℝ)) ∈ J)
    (hrel : ∀ x ∈ X, ∀ j, ∑ i, a i*x i j = 0) :
    (X.card:ℝ) / t^(r*d) ≤
      (Nat.card ↥(weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ)) ∩
        t⁻¹ • (kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ)) :
          Set (Fin r × Fin d → ℝ))) : ℝ) / t^(r*d) := by
  classical
  let S := weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ))
  let L := kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ))
  have hfin : (S ∩ t⁻¹ • (L : Set (Fin r × Fin d → ℝ))).Finite :=
    finite_scaled_lattice_inter L (weightedGridConfiguration_compact hJ _) ht.ne'
  let := hfin.fintype
  let f : X → ↥(S ∩ t⁻¹ • (L : Set (Fin r × Fin d → ℝ))) := fun x =>
    ⟨fun ij => t⁻¹*(x.val ij.1.succ ij.2:ℝ), by
      constructor
      · refine ⟨fun i => hX x.val x.property i.succ, ?_⟩
        rw [omitted_vertex_identity a ha0 x.val (hrel x.val x.property) t]
        exact hX x.val x.property 0
      · exact ⟨(fun ij => (x.val ij.1.succ ij.2:ℝ)),
          projected_grid_relation_mem a x.val (hrel x.val x.property),rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hs (i : Fin r) (j : Fin d) : x.val i.succ j = y.val i.succ j := by
      have hh := congrFun (congrArg Subtype.val hxy) (i,j)
      change t⁻¹*(x.val i.succ j:ℝ) = t⁻¹*(y.val i.succ j:ℝ) at hh
      exact Int.cast_injective (mul_left_cancel₀ (inv_ne_zero ht.ne') hh)
    apply Subtype.ext
    funext i j
    refine Fin.cases ?_ (fun i => hs i j) i
    have hx := hrel x.val x.property j
    have hy := hrel y.val y.property j
    rw [Fin.sum_univ_succ] at hx hy
    simp_rw [hs] at hx
    apply mul_left_cancel₀ ha0
    linarith
  apply div_le_div_of_nonneg_right _ (pow_nonneg ht.le _)
  change (X.card:ℝ) ≤ (Nat.card ↥(S ∩ t⁻¹ • (L : Set (Fin r × Fin d → ℝ))) : ℝ)
  apply Nat.cast_le.mpr
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hf


end SingleLatticeCovering.GridLimit







noncomputable section
namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix Filter Topology
open scoped ENNReal BigOperators

lemma simplexForm_zero {r : ℕ} (x : V r) : simplexForm 0 x = -∑ j, x j := by
  simp [simplexForm]
lemma simplexForm_succ {r : ℕ} (j : Fin r) (x : V r) : simplexForm j.succ x = x j := rfl
lemma sum_simplexForm {r : ℕ} (x : V r) : (∑ i, simplexForm i x) = 0 := by
  simp [Fin.sum_univ_succ, simplexForm_zero, simplexForm_succ]

lemma simplexDual_apply {r : ℕ} (u : V (r+1)) (j : Fin r) :
    simplexDual u j = u j.succ - simplexMean u := rfl
lemma simplexForm_dual {r : ℕ} (u : V (r+1)) (i : Fin (r+1)) :
    simplexForm i (simplexDual u) = u i - simplexMean u := by
  refine Fin.cases ?_ (fun j => rfl) i
  rw [simplexForm_zero]
  simp only [simplexDual_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (r+1:ℝ) ≠ 0 := by positivity
  dsimp [simplexMean]
  rw [Fin.sum_univ_succ]
  push_cast
  field_simp [hn]
  ring

lemma simplex_projection_square {r : ℕ} (u : V (r+1)) :
    (∑ i, (simplexForm i (simplexDual u))^2) ≤ ∑ i, (u i)^2 := by
  simp_rw [simplexForm_dual]
  have hex : (∑ i, (u i - simplexMean u)^2) =
      (∑ i, (u i)^2) - (r+1:ℕ) * (simplexMean u)^2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have he : (∑ i, 2 * u i * simplexMean u) = 2 * simplexMean u * (∑ i, u i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [he]
    dsimp [simplexMean]
    field_simp
    ring
  rw [hex]
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

lemma det_diagonal_rankOne {r : ℕ} (a u v : V r) (ha : ∀ i, a i ≠ 0) :
    (Matrix.diagonal a + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v).det =
      (∏ i, a i) * (1 + ∑ i, v i * (a i)⁻¹ * u i) := by
  have hai : Ring.inverse a = fun i => (a i)⁻¹ := by
    let au : (V r)ˣ := ⟨a, (fun i => (a i)⁻¹), by ext i; simp [ha i], by ext i; simp [ha i]⟩
    exact Ring.inverse_unit au
  rw [Matrix.det_add_replicateCol_mul_replicateRow
    (isUnit_iff_ne_zero.mpr (by simpa using Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))),
    Matrix.det_diagonal, Matrix.inv_diagonal, hai, Matrix.det_unique]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

lemma simplexJacobian_apply {r : ℕ} (s : V (r+1)) (j l : Fin r) :
    simplexJacobian s j l = (if j=l then s j.succ else 0) +
      (s 0-s l.succ)/(r+1:ℕ) := by
  simp [simplexJacobian, Matrix.diagonal_apply, Matrix.mul_apply]

lemma simplexJacobian_det {r : ℕ} (s : V (r+1)) (hs : ∀ i, 0 < s i) :
    (simplexJacobian s).det = (∏ i, s i) * ((∑ i, (s i)⁻¹)/(r+1:ℕ)) := by
  rw [simplexJacobian, det_diagonal_rankOne _ _ _ (fun i => (hs i.succ).ne')]
  simp only [mul_one]
  have hsum : (∑ i : Fin r, ((s 0-s i.succ)/(r+1:ℕ)) * (s i.succ)⁻¹) =
      s 0/(r+1:ℕ) * (∑ i : Fin r, (s i.succ)⁻¹) - (r:ℝ)/(r+1:ℕ) := by
    have he (i : Fin r) : ((s 0-s i.succ)/(r+1:ℕ)) * (s i.succ)⁻¹ =
        (s 0/(r+1:ℕ)) * (s i.succ)⁻¹ - 1/(r+1:ℕ) := by
      field_simp [(hs i.succ).ne']
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ←Finset.mul_sum]
    simp [div_eq_mul_inv]
  rw [hsum, Fin.prod_univ_succ, Fin.sum_univ_succ]
  have hn : (r+1:ℕ) ≠ (0:ℝ) := by positivity
  field_simp [(hs 0).ne', hn]
  push_cast
  ring

lemma simplexJacobian_det_ge {r : ℕ} (s : V (r+1)) (hs : ∀ i, 0 < s i) :
    (∏ i, (s i)^((r:ℝ)/(r+1:ℕ))) ≤ (simplexJacobian s).det := by
  have hn : (0:ℝ) < (r+1:ℕ) := by positivity
  have hg := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
    (fun _ : Fin (r+1) => (1:ℝ)/(r+1:ℕ)) (fun i => (s i)⁻¹)
    (fun _ _ => (div_pos zero_lt_one hn).le)
    (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp) (fun i _ => (inv_pos.mpr (hs i)).le)
  have hp : 0 < ∏ i, s i := Finset.prod_pos (fun i _ => hs i)
  have he : (∏ i, (s i)^((r:ℝ)/(r+1:ℕ))) =
      (∏ i, s i) * (∏ i, ((s i)⁻¹)^((1:ℝ)/(r+1:ℕ))) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.inv_rpow (hs i).le, ←div_eq_mul_inv]
    calc
      (s i)^((r:ℝ)/(r+1:ℕ)) = (s i)^((1:ℝ)-1/(r+1:ℕ)) := by
        congr 1; push_cast; field_simp; ring
      _ = (s i)^((1:ℝ)) / (s i)^((1:ℝ)/(r+1:ℕ)) := Real.rpow_sub (hs i) _ _
      _ = _ := by rw [Real.rpow_one]
  rw [he, simplexJacobian_det s hs]
  apply mul_le_mul_of_nonneg_left _ hp.le
  calc
    _ ≤ ∑ i, (1:ℝ)/(r+1:ℕ) * (s i)⁻¹ := hg
    _ = _ := by rw [←Finset.mul_sum]; ring


lemma simplexTransport_injective {r : ℕ} {T : Fin (r+1) → ℝ → ℝ}
    (hT : ∀ i, StrictMono (T i)) : Function.Injective (simplexTransport T) := by
  intro x y hxy
  let u : V (r+1) := fun i => T i (simplexForm i x)-T i (simplexForm i y)
  have hu : simplexDual u = 0 := by
    change simplexDual ((fun i => T i (simplexForm i x)) - (fun i => T i (simplexForm i y))) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have hue (i : Fin (r+1)) : u i = simplexMean u := by
    have h := simplexForm_dual u i
    rw [hu, map_zero] at h
    exact sub_eq_zero.mp h.symm
  have hsum : (∑ i, u i * (simplexForm i x-simplexForm i y)) = 0 := by
    simp_rw [hue, ← map_sub]
    rw [←Finset.mul_sum, sum_simplexForm, mul_zero]
  have hn (i : Fin (r+1)) : 0 ≤ u i*(simplexForm i x-simplexForm i y) := by
    dsimp [u]
    rcases le_total (simplexForm i x) (simplexForm i y) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ((hT i).monotone h)) (sub_nonpos.mpr h)
    · exact mul_nonneg (sub_nonneg.mpr ((hT i).monotone h)) (sub_nonneg.mpr h)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hsum
  ext j
  have h := hzero j.succ (Finset.mem_univ _)
  change (T j.succ (x j)-T j.succ (y j))*(x j-y j)=0 at h
  rcases mul_eq_zero.mp h with h | h
  · exact (hT j.succ).injective (sub_eq_zero.mp h)
  · exact sub_eq_zero.mp h

lemma simplexTransport_hasFDerivAt {r : ℕ} {T T' : Fin (r+1) → ℝ → ℝ}
    (hT : ∀ i t, HasDerivAt (T i) (T' i t) t) (x : V r) :
    HasFDerivAt (simplexTransport T)
      (simplexDerivative (fun i => T' i (simplexForm i x))) x := by
  apply simplexDual.toContinuousLinearMap.hasFDerivAt.comp
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hT i (simplexForm i x)).comp_hasFDerivAt x
    (simplexForm i).toContinuousLinearMap.hasFDerivAt

lemma simplexDerivative_eq {r : ℕ} (s : V (r+1)) :
    (simplexDerivative s).toLinearMap = Matrix.toLin' (simplexJacobian s) := by
  apply LinearMap.ext
  intro x
  ext j
  change s j.succ * simplexForm j.succ x -
    simplexMean (fun i => s i * simplexForm i x) = (simplexJacobian s *ᵥ x) j
  simp only [simplexForm_succ, simplexMean, Fin.sum_univ_succ, simplexForm_zero,
    Matrix.mulVec, dotProduct, simplexJacobian_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [div_mul_eq_mul_div, sub_mul]
  rw [←Finset.sum_div, Finset.sum_sub_distrib, ←Finset.mul_sum]
  ring

lemma simplexDerivative_det {r : ℕ} (s : V (r+1)) :
    (simplexDerivative s).det = (simplexJacobian s).det := by
  change LinearMap.det (simplexDerivative s).toLinearMap = _
  rw [simplexDerivative_eq, LinearMap.det_toLin']

lemma simplex_transport_pointwise {r : ℕ} (u s : V (r+1)) (hs : ∀ i, 0 < s i) :
    (∏ i, (Real.exp (-(u i)^2) * s i) ^ ((r:ℝ)/(r+1:ℕ))) ≤
      |(simplexDerivative s).det| *
        Real.exp (-((r:ℝ)/(r+1:ℕ)) * ∑ i, (simplexForm i (simplexDual u))^2) := by
  have hpow (i : Fin (r+1)) :
      (Real.exp (-(u i)^2) * s i) ^ ((r:ℝ)/(r+1:ℕ)) =
        Real.exp (-((r:ℝ)/(r+1:ℕ))*(u i)^2) * (s i)^((r:ℝ)/(r+1:ℕ)) := by
    rw [Real.mul_rpow (Real.exp_pos _).le (hs i).le, ← Real.exp_mul]
    congr 2; ring
  simp_rw [hpow]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  have hex : Real.exp (∑ i, -((r:ℝ)/(r+1:ℕ))*(u i)^2) ≤
      Real.exp (-((r:ℝ)/(r+1:ℕ)) * ∑ i, (simplexForm i (simplexDual u))^2) := by
    apply Real.exp_le_exp.mpr
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonpos_left (simplex_projection_square u) (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hd := simplexJacobian_det_ge s hs
  have hdn : 0 ≤ (simplexJacobian s).det :=
    (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hs i).le _)).trans hd
  rw [simplexDerivative_det, abs_of_nonneg hdn]
  exact (mul_le_mul hex hd (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hs i).le _))
    (Real.exp_pos _).le).trans_eq (mul_comm _ _)


lemma simplexRoot_mulVec {r : ℕ} (x : V r) (j : Fin r) :
    simplexRoot.mulVec x j = x j + (∑ l, x l)/(Real.sqrt (r+1:ℕ)+1) := by
  rw [simplexRoot, Matrix.add_mulVec, Matrix.one_mulVec]
  simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, ←Finset.mul_sum]
  ring

lemma simplexRoot_det {r : ℕ} :
    (simplexRoot (r:=r)).det = Real.sqrt (r+1:ℕ) := by
  rw [simplexRoot, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : 0 ≤ (r+1:ℕ) := Nat.zero_le _
  have hs : (Real.sqrt (r+1:ℕ))^2 = (r+1:ℕ) := Real.sq_sqrt (by positivity)
  have hd : Real.sqrt (r+1:ℕ)+1 ≠ 0 := by positivity
  push_cast at *
  field_simp
  nlinarith

lemma simplexRoot_square {r : ℕ} (x : V r) :
    (∑ j, (simplexRoot.mulVec x j)^2) = ∑ i, (simplexForm i x)^2 := by
  simp_rw [simplexRoot_mulVec]
  rw [Fin.sum_univ_succ]
  simp only [simplexForm_zero, simplexForm_succ, neg_sq]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs : (∑ j : Fin r, 2*x j*((∑ l, x l)/(Real.sqrt (r+1:ℕ)+1))) =
      2*((∑ l, x l)/(Real.sqrt (r+1:ℕ)+1)) * ∑ j, x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he : (Real.sqrt (r+1:ℕ))^2 = (r+1:ℕ) := Real.sq_sqrt (by positivity)
  have hd : Real.sqrt (r+1:ℕ)+1 ≠ 0 := by positivity
  push_cast at *
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*(∑ j, x j)^2) he]

lemma simplex_gaussian_integral {r : ℕ} (c : ℝ) (hc : 0 < c) :
    (∫⁻ x : V r, ENNReal.ofReal
      (Real.exp (-c * ∑ i : Fin (r+1), (simplexForm i x)^2))) =
      ENNReal.ofReal ((Real.sqrt (Real.pi/c))^r / Real.sqrt (r+1:ℕ)) := by
  let B : V r →ₗ[ℝ] V r := Matrix.toLin' simplexRoot
  have hdet : B.det = Real.sqrt (r+1:ℕ) := by
    rw [LinearMap.det_toLin', simplexRoot_det]
  have hp : 0 < Real.sqrt (r+1:ℕ) := Real.sqrt_pos.mpr (by positivity)
  let g : V r → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-c * ∑ j, (x j)^2))
  have hg : Measurable g := by
    apply Continuous.measurable
    dsimp [g]
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  have he (x : V r) : g (B x) =
      ENNReal.ofReal (Real.exp (-c * ∑ i : Fin (r+1), (simplexForm i x)^2)) := by
    dsimp [g, B]
    rw [simplexRoot_square]
  have hgi : (∫⁻ x, g x) = ENNReal.ofReal ((Real.sqrt (Real.pi/c))^r) := by
    have hex (x : V r) : Real.exp (-c * ∑ j, (x j)^2) =
        ∏ j, Real.exp (-c*(x j)^2) := by rw [Finset.mul_sum, Real.exp_sum]
    dsimp [g]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (show Integrable (fun x : V r => Real.exp (-c * ∑ j, (x j)^2)) volume from by
        simp_rw [hex]
        exact Integrable.fintype_prod (fun i : Fin r => integrable_exp_neg_mul_sq hc))
      (Filter.Eventually.of_forall (fun x : V r => (Real.exp_pos _).le))]
    congr 1
    simp_rw [hex]
    rw [integral_fintype_prod_volume_eq_prod (fun (_ : Fin r) (t : ℝ) => Real.exp (-c*t^2))]
    simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f:=B) (by rw [hdet]; exact hp.ne')
  calc
    _ = ∫⁻ x, g (B x) := by simp_rw [he]
    _ = ∫⁻ y, g y ∂(Measure.map B volume) := (lintegral_map hg B.continuous_of_finiteDimensional.measurable).symm
    _ = _ := by
      rw [hm, lintegral_smul_measure, hgi, hdet, abs_of_pos (inv_pos.mpr hp), smul_eq_mul,
        ←ENNReal.ofReal_mul (inv_pos.mpr hp).le]
      congr 1; ring

lemma simplex_transport_integral {r : ℕ} (hr : 0 < r) {T T' : Fin (r+1) → ℝ → ℝ}
    (hmono : ∀ i, StrictMono (T i))
    (hT : ∀ i t, HasDerivAt (T i) (T' i t) t) (hpos : ∀ i t, 0 < T' i t) :
    (∫⁻ x : V r, ENNReal.ofReal
      (∏ i, (Real.exp (-(T i (simplexForm i x))^2) * T' i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal ((Real.sqrt (Real.pi/((r:ℝ)/(r+1:ℕ))))^r / Real.sqrt (r+1:ℕ)) := by
  let g : V r → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp (-((r:ℝ)/(r+1:ℕ)) * ∑ i, (simplexForm i x)^2))
  calc
    _ ≤ ∫⁻ x : V r, ENNReal.ofReal |(simplexDerivative (fun i => T' i (simplexForm i x))).det| *
        g (simplexTransport T x) := by
      apply lintegral_mono
      intro x
      change _ ≤ ENNReal.ofReal |_| * ENNReal.ofReal _
      rw [←ENNReal.ofReal_mul (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (simplex_transport_pointwise
        (fun i => T i (simplexForm i x)) (fun i => T' i (simplexForm i x)) (fun i => hpos i _))
    _ = ∫⁻ y in simplexTransport T '' Set.univ, g y := by
      symm
      simpa using lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        MeasurableSet.univ (fun x _ => (simplexTransport_hasFDerivAt hT x).hasFDerivWithinAt)
        (simplexTransport_injective hmono).injOn g
    _ ≤ ∫⁻ y, g y := lintegral_mono' Measure.restrict_le_self (le_refl _)
    _ = _ := simplex_gaussian_integral _ (div_pos (Nat.cast_pos.mpr hr) (by positivity))



end SingleLatticeCovering.SimplexYoung





open MeasureTheory Filter Set
open scoped Topology
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.SharpYoung

lemma densityCDF_transport (f g : PositiveDensity) (x : ℝ) :
    densityCDF g (densityTransport f g x) = densityCDF f x := by
  change ((densityCDFIso g) ((densityCDFIso g).symm (densityCDFIso f x)) : ℝ) = _
  simp

lemma densityTransport_hasDerivAt (f g : PositiveDensity) (x : ℝ) :
    HasDerivAt (densityTransport f g) (f x / g (densityTransport f g x)) x := by
  apply HasDerivAt.of_comp_left (densityTransport f g).continuous.continuousAt
    (densityCDF_hasDerivAt g _) (densityCDF_hasDerivAt f x) (ne_of_gt (g.positive _))
  exact Filter.Eventually.of_forall (densityCDF_transport f g)


lemma gaussian_transport_density (f : PositiveDensity) (x : ℝ) :
    Real.exp (-(densityTransport f normalizedGaussianDensity x)^2) *
      (f x / normalizedGaussianDensity (densityTransport f normalizedGaussianDensity x)) =
      Real.sqrt Real.pi * f x := by
  change Real.exp _ * (f x / (Real.exp _ / Real.sqrt Real.pi)) = _
  field_simp



end SingleLatticeCovering.SharpYoung

namespace SingleLatticeCovering.SimplexYoung
open SingleLatticeCovering.SharpYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal


lemma simplexConstant_nonneg (r : ℕ) : 0 ≤ simplexConstant r := by
  unfold simplexConstant; positivity

lemma simplex_positiveDensity_integral {r : ℕ} (hr : 0 < r)
    (f : Fin (r+1) → PositiveDensity) :
    (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal (simplexConstant r) := by
  let T (i : Fin (r+1)) := densityTransport (f i) normalizedGaussianDensity
  let T' (i : Fin (r+1)) (t : ℝ) := f i t / normalizedGaussianDensity (T i t)
  have ht := simplex_transport_integral hr (T := fun i => T i) (T' := T')
    (fun i => (T i).strictMono) (fun i => densityTransport_hasDerivAt (f i) _)
    (fun i t => div_pos ((f i).positive t) (normalizedGaussianDensity.positive _))
  have hpoint (x : V r) :
      (∏ i, (Real.exp (-(T i (simplexForm i x))^2) * T' i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ))) =
        (Real.sqrt Real.pi)^r * ∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)) := by
    change (∏ i, (Real.exp (-(densityTransport (f i) normalizedGaussianDensity
      (simplexForm i x))^2) * (f i (simplexForm i x) /
      normalizedGaussianDensity (densityTransport (f i) normalizedGaussianDensity
        (simplexForm i x)))) ^ ((r:ℝ)/(r+1:ℕ))) = _
    simp_rw [gaussian_transport_density,
      Real.mul_rpow (Real.sqrt_nonneg _) ((f _).positive _).le]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [←Real.rpow_natCast, ←Real.rpow_mul (Real.sqrt_nonneg _), div_mul_cancel₀ _ (by positivity : (r+1:ℕ) ≠ (0:ℝ)), Real.rpow_natCast]
  simp_rw [hpoint, ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) r)] at ht
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at ht
  have hp : 0 < (Real.sqrt Real.pi)^r := pow_pos (Real.sqrt_pos.mpr Real.pi_pos) r
  have hh : (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal ((Real.sqrt (Real.pi/((r:ℝ)/(r+1:ℕ))))^r / Real.sqrt (r+1:ℕ)) /
        ENNReal.ofReal ((Real.sqrt Real.pi)^r) :=
    (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hp)))
      (Or.inl ENNReal.ofReal_ne_top)).mpr (by rw [mul_comm]; exact ht)
  rw [←ENNReal.ofReal_div_of_pos hp] at hh
  have he : ((Real.sqrt (Real.pi/((r:ℝ)/(r+1:ℕ))))^r / Real.sqrt (r+1:ℕ)) /
      (Real.sqrt Real.pi)^r = simplexConstant r := by
    unfold simplexConstant
    rw [Real.sqrt_div Real.pi_pos.le, div_pow]
    have hc : 0 < Real.sqrt ((r:ℝ)/(r+1:ℕ)) := by positivity
    field_simp [hc.ne']
    simp only [←mul_pow, one_div, mul_inv_cancel₀ hc.ne', one_pow]
  simpa only [he] using hh

lemma simplex_positive_integral {r : ℕ} (hr : 0 < r) (f : Fin (r+1) → ℝ → ℝ)
    (hc : ∀ i, Continuous (f i)) (hp : ∀ i x, 0 < f i x)
    (hi : ∀ i, Integrable (f i) volume) :
    (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal (simplexConstant r * ∏ i, (∫ t, f i t) ^ ((r:ℝ)/(r+1:ℕ))) := by
  let g (i : Fin (r+1)) := normalizePositiveDensity (f i) (hc i) (hp i) (hi i)
  have hmass (i : Fin (r+1)) := integral_pos_of_continuous_density (hp i) (hi i)
  have he (i : Fin (r+1)) (x : ℝ) : f i x = (∫ t, f i t) * g i x := by
    dsimp [g, normalizePositiveDensity]
    field_simp [ne_of_gt (hmass i)]
  have hpoint (x : V r) : (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ))) =
      (∏ i, (∫ t, f i t) ^ ((r:ℝ)/(r+1:ℕ))) * ∏ i, (g i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)) := by
    conv_lhs => arg 2; ext i; rw [he i (simplexForm i x)]
    simp_rw [Real.mul_rpow (hmass _).le ((g _).positive _).le]
    rw [Finset.prod_mul_distrib]
  have hn : 0 ≤ ∏ i, (∫ t, f i t) ^ ((r:ℝ)/(r+1:ℕ)) :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hmass i).le _)
  simp_rw [hpoint, ENNReal.ofReal_mul hn]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.ofReal_mul (simplexConstant_nonneg r)]
  rw [mul_comm (ENNReal.ofReal (simplexConstant r))]
  exact mul_le_mul' le_rfl (simplex_positiveDensity_integral hr g)


lemma simplex_nonneg_integral {r : ℕ} (hr : 0 < r) (f : Fin (r+1) → ℝ → ℝ)
    (hc : ∀ i, Continuous (f i)) (hp : ∀ i x, 0 ≤ f i x)
    (hi : ∀ i, Integrable (f i) volume) :
    (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal (simplexConstant r * ∏ i, (∫ t, f i t) ^ ((r:ℝ)/(r+1:ℕ))) := by
  have he (ε : ℝ) (hε : 0 < ε) :
      (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
        ENNReal.ofReal (simplexConstant r * ∏ i, ((∫ t, f i t)+ε) ^ ((r:ℝ)/(r+1:ℕ))) := by
    let F (i : Fin (r+1)) (x : ℝ) := f i x + ε * normalizedGaussianDensity x
    have hcF (i : Fin (r+1)) : Continuous (F i) :=
      (hc i).add (continuous_const.mul normalizedGaussianDensity.continuous)
    have hpF (i : Fin (r+1)) (x : ℝ) : 0 < F i x :=
      add_pos_of_nonneg_of_pos (hp i x) (mul_pos hε (normalizedGaussianDensity.positive x))
    have hiF (i : Fin (r+1)) : Integrable (F i) volume :=
      (hi i).add (normalizedGaussianDensity.integrable.const_mul ε)
    have hmF (i : Fin (r+1)) : ∫ t, F i t = (∫ t, f i t)+ε := by
      dsimp [F]
      rw [integral_add (hi i) (normalizedGaussianDensity.integrable.const_mul ε),
        integral_const_mul, normalizedGaussianDensity.integral_one, mul_one]
    have hmono : (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
        (∫⁻ x : V r, ENNReal.ofReal (∏ i, (F i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      apply Finset.prod_le_prod
      · intro i _
        exact Real.rpow_nonneg (hp i _) _
      · intro i _
        apply Real.rpow_le_rpow (hp i _)
        · exact le_add_of_nonneg_right (mul_nonneg hε.le (normalizedGaussianDensity.positive _).le)
        · positivity
    simpa only [hmF] using hmono.trans (simplex_positive_integral hr F hcF hpF hiF)
  have hct : ContinuousAt
      (fun ε : ℝ => ENNReal.ofReal (simplexConstant r *
        ∏ i, ((∫ t, f i t)+ε) ^ ((r:ℝ)/(r+1:ℕ)))) 0 := by
    apply ENNReal.continuous_ofReal.continuousAt.comp
    fun_prop (disch := positivity)
  have ht := hct.tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simp only [add_zero] at ht
  apply ge_of_tendsto ht
  exact Filter.Eventually.of_forall (fun n => he (1 / ((n:ℝ)+1)) (by positivity))



end SingleLatticeCovering.SimplexYoung


open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace SingleLatticeCovering.SharpYoung

lemma continuous_finTail {d : ℕ} {E : Type*} [TopologicalSpace E] :
    Continuous (Fin.tail : (Fin (d+1) → E) → (Fin d → E)) := by
  exact continuous_pi (fun j => continuous_apply j.succ)

lemma hasCompactSupport_finCons {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : ℝ × (Fin d → ℝ) => f (Fin.cons p.1 p.2)) := by
  apply HasCompactSupport.intro
    (hf.isCompact.image ((continuous_apply 0).prodMk continuous_finTail))
  intro p hp
  by_contra hn
  apply hp
  refine ⟨Fin.cons p.1 p.2, subset_tsupport f hn, ?_⟩
  simp

lemma hasCompactSupport_finSlice {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hf : HasCompactSupport f) (y : Fin d → ℝ) :
    HasCompactSupport (fun t : ℝ => f (Fin.cons t y)) := by
  apply HasCompactSupport.intro (hf.isCompact.image (continuous_apply 0))
  intro t ht
  by_contra hn
  exact ht ⟨Fin.cons t y, subset_tsupport f hn, by simp⟩

lemma hasCompactSupport_finMarginal {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (finMarginal f) := by
  apply HasCompactSupport.intro (hf.isCompact.image continuous_finTail)
  intro y hy
  have hz (t : ℝ) : f (Fin.cons t y) = 0 := by
    by_contra hn
    exact hy ⟨Fin.cons t y, subset_tsupport f hn, by simp⟩
  simp [finMarginal, hz]

lemma continuous_finMarginal {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hc : Continuous f) (hk : HasCompactSupport f) : Continuous (finMarginal f) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (hk.isCompact.image (continuous_apply 0))
  · exact (hc.comp (continuous_snd.finCons continuous_fst)).continuousOn
  · intro y t _ ht
    by_contra hn
    exact ht ⟨Fin.cons t y, subset_tsupport f hn, by simp⟩

lemma finMarginal_nonneg {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hf : 0 ≤ f) : 0 ≤ finMarginal f := fun y => integral_nonneg (fun t => hf (Fin.cons t y))

lemma integral_finMarginal {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hc : Continuous f) (hk : HasCompactSupport f) :
    ∫ y, finMarginal f y = ∫ x, f x := by
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  have he := hm.integral_comp' f
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero] at he
  rw [← he]
  symm
  exact integral_prod_symm (fun p : ℝ × (Fin d → ℝ) => f (Fin.cons p.1 p.2))
    ((hc.comp (continuous_fst.finCons continuous_snd)).integrable_of_hasCompactSupport
      (hasCompactSupport_finCons hk))

lemma lintegral_finCons {d : ℕ} {E : Type*} [MeasureSpace E]
    [SigmaFinite (volume : Measure E)]
    (f : (Fin (d+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ y : Fin d → E, ∫⁻ t : E, f (Fin.cons t y) := by
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => E) 0).symm
  have he := hm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero] at he
  rw [← he]
  apply lintegral_prod_symm _
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero, Function.comp_def, Fin.consEquiv_apply] using
    (hf.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => E) 0).symm.measurable).aemeasurable



end SingleLatticeCovering.SharpYoung

namespace SingleLatticeCovering.SimplexYoung
open SingleLatticeCovering.SharpYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal

lemma continuous_simplexSpatial {r d : ℕ} (i : Fin (r+1)) :
    Continuous (simplexSpatial (d := d) i) := by
  exact continuous_pi (fun j => (simplexForm i).continuous_of_finiteDimensional.comp
    (continuous_apply j))

lemma simplexSpatial_cons {r d : ℕ} (i : Fin (r+1)) (t : V r) (x : Fin d → V r) :
    simplexSpatial i (Fin.cons t x) = Fin.cons (simplexForm i t) (simplexSpatial i x) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [simplexSpatial]




lemma simplex_cc_integral {r : ℕ} (hr : 0 < r) (d : ℕ) (f : Fin (r+1) → (Fin d → ℝ) → ℝ)
    (hc : ∀ i, Continuous (f i)) (hn : ∀ i x, 0 ≤ f i x)
    (hk : ∀ i, HasCompactSupport (f i)) :
    (∫⁻ x : Fin d → V r, ENNReal.ofReal
      (∏ i, (f i (simplexSpatial i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal ((simplexConstant r)^d *
        ∏ i, (∫ t, f i t) ^ ((r:ℝ)/(r+1:ℕ))) := by
  induction d with
  | zero =>
    rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → V r), lintegral_dirac]
    simp_rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ), integral_dirac]
    simp only [pow_zero, one_mul]
    apply le_of_eq
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    exact Subsingleton.elim _ _
  | succ d ih =>
    have hmeas : Measurable (fun x : Fin (d+1) → V r => ENNReal.ofReal
        (∏ i, (f i (simplexSpatial i x)) ^ ((r:ℝ)/(r+1:ℕ)))) := by
      apply Continuous.measurable
      apply ENNReal.continuous_ofReal.comp
      exact continuous_finsetProd _ (fun i _ =>
        (hc i |>.comp (continuous_simplexSpatial i)).rpow_const (fun _ => Or.inr (by positivity)))
    rw [lintegral_finCons _ hmeas]
    let g (i : Fin (r+1)) := finMarginal (f i)
    have hcons (z : Fin d → ℝ) : Continuous (fun t : ℝ => (Fin.cons t z : Fin (d+1) → ℝ)) := by
      apply continuous_pi
      intro j
      exact Fin.cases continuous_id (fun _ => continuous_const) j
    have hinner (y : Fin d → V r) :
        (∫⁻ t : V r, ENNReal.ofReal
          (∏ i, f i (simplexSpatial i (Fin.cons t y)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
        ENNReal.ofReal (simplexConstant r *
          ∏ i, g i (simplexSpatial i y) ^ ((r:ℝ)/(r+1:ℕ))) := by
      simp_rw [simplexSpatial_cons]
      apply simplex_nonneg_integral hr (fun i t => f i (Fin.cons t (simplexSpatial i y)))
      · intro i
        exact (hc i).comp (hcons (simplexSpatial i y))
      · intro i t
        exact hn i _
      · intro i
        exact ((hc i).comp (hcons (simplexSpatial i y))).integrable_of_hasCompactSupport
          (hasCompactSupport_finSlice (hk i) _)
    apply (lintegral_mono hinner).trans
    have hcst : 0 ≤ simplexConstant r := simplexConstant_nonneg r
    simp_rw [ENNReal.ofReal_mul hcst]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hbound := ih g (fun i => continuous_finMarginal (hc i) (hk i))
      (fun i x => finMarginal_nonneg (hn i) x)
      (fun i => hasCompactSupport_finMarginal (hk i))
    have hmass (i : Fin (r+1)) : ∫ t, g i t = ∫ t, f i t := integral_finMarginal (hc i) (hk i)
    simp_rw [hmass] at hbound
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal (simplexConstant r))) hbound
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [← ENNReal.ofReal_mul hcst, pow_succ]
    congr 1
    ring



end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal


lemma simplexConfiguration_measurable {r d : ℕ} {J : Fin (r+1) → Set (Fin d → ℝ)}
    (hJ : ∀ i, MeasurableSet (J i)) : MeasurableSet (simplexConfiguration J) := by
  unfold simplexConfiguration
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (hJ i).preimage (continuous_simplexSpatial i).measurable

lemma simplex_measure_le_cc {r d : ℕ} (hr : 0 < r)
    {J : Fin (r+1) → Set (Fin d → ℝ)} (hJ : ∀ i, MeasurableSet (J i))
    (f : Fin (r+1) → (Fin d → ℝ) → ℝ) (hc : ∀ i, Continuous (f i))
    (hn : ∀ i z, 0 ≤ f i z) (hk : ∀ i, HasCompactSupport (f i))
    (hf : ∀ i, EqOn (f i) 1 (J i)) :
    volume (simplexConfiguration J) ≤
      ENNReal.ofReal ((simplexConstant r)^d * ∏ i, (∫ z, f i z) ^ ((r:ℝ)/(r+1:ℕ))) := by
  apply le_trans _ (simplex_cc_integral hr d f hc hn hk)
  rw [←lintegral_indicator_one (simplexConfiguration_measurable hJ)]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ simplexConfiguration J
  · have hh (i : Fin (r+1)) : f i (simplexSpatial i x) = 1 := hf i (hx i)
    simp [Set.indicator_of_mem hx, hh]
  · simp [Set.indicator_of_notMem hx]




lemma volume_simplexConfiguration_le {r d : ℕ} (hr : 0 < r)
    {J : Fin (r+1) → Set (Fin d → ℝ)} (hJ : ∀ i, IsCompact (J i)) :
    volume (simplexConfiguration J) ≤
      ENNReal.ofReal ((simplexConstant r)^d *
        ∏ i, ((volume (J i)).toReal)^((r:ℝ)/(r+1:ℕ))) := by
  let M (i : Fin (r+1)) := (volume (J i)).toReal
  have hM (i) : 0 ≤ M i := ENNReal.toReal_nonneg
  have hh (ε : ℝ) (hε : 0 < ε) : volume (simplexConfiguration J) ≤
      ENNReal.ofReal ((simplexConstant r)^d * ∏ i, (M i+ε)^((r:ℝ)/(r+1:ℕ))) := by
    have hex (i : Fin (r+1)) : ∃ f : (Fin d → ℝ) → ℝ, Continuous f ∧
        HasCompactSupport f ∧ EqOn f 1 (J i) ∧ (∀ z, 0 ≤ f z) ∧
        ENNReal.ofReal (∫ z, f z) < ENNReal.ofReal (M i+ε) := by
      have hlt : volume (J i) < ENNReal.ofReal (M i+ε) := by
        rw [←ENNReal.ofReal_toReal (hJ i).measure_ne_top]
        apply ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos (hM i) hε) |>.mpr
        dsimp [M]; linarith
      rw [(hJ i).measure_eq_biInf_integral_hasCompactSupport volume] at hlt
      simp only [iInf_lt_iff] at hlt
      obtain ⟨f, hc, hk, heq, hn, hfi⟩ := hlt
      exact ⟨f, hc, hk, heq, hn, hfi⟩
    choose f hc hk heq hn hfi using hex
    apply (simplex_measure_le_cc hr (fun i => (hJ i).measurableSet) f hc hn hk heq).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (simplexConstant_nonneg r) _)
    apply Finset.prod_le_prod
    · intro i _; exact Real.rpow_nonneg (integral_nonneg (hn i)) _
    · intro i _
      apply Real.rpow_le_rpow (integral_nonneg (hn i)) _ (by positivity)
      exact (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos (hM i) hε)).mp (hfi i) |>.le
  have hct : ContinuousAt (fun ε : ℝ => ENNReal.ofReal
      ((simplexConstant r)^d * ∏ i, (M i+ε)^((r:ℝ)/(r+1:ℕ)))) 0 := by
    apply ENNReal.continuous_ofReal.continuousAt.comp
    fun_prop (disch := positivity)
  have ht := hct.tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hle := ge_of_tendsto ht (Filter.Eventually.of_forall
    (fun n => hh (1/((n:ℝ)+1)) (by positivity)))
  simpa only [add_zero, M] using hle


end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix
open scoped ENNReal Pointwise


lemma simplexDiagonal_apply {r d : ℕ} (c : Fin r → ℝ) (x : Fin d → V r)
    (a : Fin d) (j : Fin r) : simplexDiagonal c x a j = c j * x a j := by
  simp [simplexDiagonal, Matrix.mulVec_diagonal]

lemma simplexDiagonal_det {r d : ℕ} (c : Fin r → ℝ) :
    LinearMap.det (simplexDiagonal (d := d) c) = (∏ j, c j)^d := by
  unfold simplexDiagonal
  rw [LinearMap.det_pi]
  have h : LinearMap.det (Matrix.diagonal c).mulVecLin = ∏ j, c j := by
    rw [←Matrix.toLin'_apply', LinearMap.det_toLin', Matrix.det_diagonal]
  simp [h]

lemma scaledCircuitFamily_compact {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (c : Fin r → ℝ) (i : Fin (r+1)) :
    IsCompact (scaledCircuitFamily J c i) := by
  refine Fin.cases ?_ (fun j => ?_) i <;>
    exact hJ.image (by fun_prop)

lemma weightedSimplexConfiguration_preimage {r d : ℕ} (J : Set (Fin d → ℝ))
    (c : Fin r → ℝ) (hc : ∀ j, c j ≠ 0) :
    weightedSimplexConfiguration J c =
      simplexDiagonal c ⁻¹' simplexConfiguration (scaledCircuitFamily J c) := by
  ext x
  change (_ ∧ _) ↔ ∀ i, simplexSpatial i (simplexDiagonal c x) ∈ scaledCircuitFamily J c i
  rw [Fin.forall_fin_succ]
  have h0 : simplexSpatial 0 (simplexDiagonal c x) =
      (-1:ℝ) • (fun a => ∑ j, c j * x a j) := by
    ext a
    simp [simplexSpatial, simplexForm_zero, simplexDiagonal_apply]
  have hs (j : Fin r) : simplexSpatial j.succ (simplexDiagonal c x) =
      c j • (fun a => x a j) := by
    ext a
    simp [simplexSpatial, simplexForm_succ, simplexDiagonal_apply]
  simp only [scaledCircuitFamily, Fin.cons_zero, Fin.cons_succ, h0, hs,
    smul_mem_smul_set_iff₀ (by norm_num : (-1:ℝ) ≠ 0), smul_mem_smul_set_iff₀ (hc _)]
  exact and_comm

lemma volume_scaledCircuitFamily {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    (volume (scaledCircuitFamily J c 0)).toReal = (volume J).toReal ∧
      ∀ j, (volume (scaledCircuitFamily J c j.succ)).toReal =
        |c j|^d * (volume J).toReal := by
  constructor
  · simp [scaledCircuitFamily]
  · intro j
    simp [scaledCircuitFamily, Measure.addHaar_smul, abs_pow,
      ENNReal.toReal_mul]


theorem volume_weightedSimplexConfiguration_le {r d : ℕ} (hr : 0 < r)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (c : Fin r → ℝ) (hc : ∀ j, c j ≠ 0) :
    volume (weightedSimplexConfiguration J c) ≤
      ENNReal.ofReal ((∏ j, |c j|)⁻¹^d * (simplexConstant r)^d *
        ((volume J).toReal^((r:ℝ)/(r+1:ℕ)) *
          ∏ j, (|c j|^d * (volume J).toReal)^((r:ℝ)/(r+1:ℕ)))) := by
  rw [weightedSimplexConfiguration_preimage J c hc,
    addHaar_preimage_linearMap volume (by
      rw [simplexDiagonal_det]; exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun j _ => hc j))),
    simplexDiagonal_det]
  have hb := volume_simplexConfiguration_le hr (scaledCircuitFamily_compact hJ c)
  apply (mul_le_mul_right hb _).trans_eq
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Fin.prod_univ_succ, (volume_scaledCircuitFamily J c).1]
  simp_rw [(volume_scaledCircuitFamily J c).2]
  rw [←inv_pow, abs_pow, abs_inv, Finset.abs_prod]
  ring


end SingleLatticeCovering.SimplexYoung



noncomputable section
namespace SingleLatticeCovering.SimplexYoung
open scoped BigOperators

lemma weightedCircuitFactor {r d : ℕ} (hr : 0 < r) (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (u C : ℝ) (hu : 0 ≤ u) :
    (∏ j, a j)⁻¹^d * C^d *
        (u^((r:ℝ)/(r+1:ℕ)) * ∏ j, (a j^d*u)^((r:ℝ)/(r+1:ℕ))) =
      C^d * (∏ j, a j^(-((d:ℝ)/(r+1:ℕ)))) * u^r := by
  have hn : (r+1:ℝ) ≠ 0 := by positivity
  have hp : 0 < (r:ℝ)/(r+1:ℕ) := div_pos (by exact_mod_cast hr) (by positivity)
  by_cases hz : u = 0
  · rw [hz, Real.zero_rpow hp.ne', zero_mul, mul_zero, zero_pow hr.ne', mul_zero]
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
  let p : ℝ := (r:ℝ)/(r+1:ℕ)
  change _ * _ * (u^p * ∏ j, (a j^d*u)^p) = _
  have hdist (j : Fin r) : (a j^d*u)^p = (a j)^(d*p) * u^p := by
    rw [Real.mul_rpow (pow_nonneg (ha j).le _) hu, ←Real.rpow_natCast, ←Real.rpow_mul (ha j).le]
  simp_rw [hdist]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he : p*(r+1:ℕ) = (r:ℝ) := by
    dsimp [p]; exact div_mul_cancel₀ _ (by positivity)
  have huPow : u^p*(u^p)^r = u^r := by
    rw [←pow_succ', ←Real.rpow_natCast, ←Real.rpow_mul hu, he, Real.rpow_natCast]
  have hprod : (∏ j, a j)⁻¹^d * (∏ j, (a j)^((d:ℝ)*p)) =
      ∏ j, a j^(-((d:ℝ)/(r+1:ℕ))) := by
    rw [←Finset.prod_inv_distrib, ←Finset.prod_pow, ←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [←Real.rpow_natCast, ←Real.rpow_neg_one, ←Real.rpow_mul (ha j).le,
      ←Real.rpow_add (ha j)]
    congr 1
    dsimp [p]
    push_cast
    field_simp
    ring
  calc
    _ = C^d * ((∏ j, a j)⁻¹^d * (∏ j, (a j)^((d:ℝ)*p))) * (u^p*(u^p)^r) := by ring
    _ = _ := by rw [hprod, huPow]


end SingleLatticeCovering.SimplexYoung


end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitVolumes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal



theorem volume_weightedSimplexConfiguration_sharp {r d : ℕ} (hr : 0 < r)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (c : Fin r → ℝ) (hc : ∀ j, c j ≠ 0) :
    volume (weightedSimplexConfiguration J c) ≤
      ENNReal.ofReal ((simplexConstant r)^d *
        (∏ j, |c j|^(-((d:ℝ)/(r+1:ℕ)))) * (volume J).toReal^r) := by
  convert volume_weightedSimplexConfiguration_le hr hJ c hc using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact (weightedCircuitFactor hr (fun j => |c j|) (fun j => abs_pos.mpr (hc j))
    _ _ ENNReal.toReal_nonneg).symm


end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open scoped ENNReal BigOperators

lemma tsum_int_inv_sq_le_four : (∑' z : ℤ, 1/(z:ℝ)^2) ≤ 4 := by
  have hs : Summable (fun z : ℤ => 1/(z:ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (by intro z; simp) hs]
  have he : (∑' z : ℕ+, 1/((z:ℕ):ℝ)^2) = Real.pi^2/6 := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1/(n:ℝ)^2)]
    have hh := hasSum_zeta_two.summable.tsum_eq_zero_add
    simpa only [hasSum_zeta_two.tsum_eq, Nat.cast_zero, zero_pow (by omega : 2 ≠ 0),
      div_zero, zero_add] using hh.symm
  simp only [Int.cast_zero, zero_pow (by omega : 2 ≠ 0), div_zero, zero_add,
    Int.cast_natCast, he, two_smul]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

lemma int_circuit_weight_le_sq (q : ℝ) (hq : 2 ≤ q) (z : ℤ) :
    |(z:ℝ)|^(-q) ≤ 1/(z:ℝ)^2 := by
  by_cases hz : z = 0
  · simp [hz, Real.zero_rpow (by linarith : -q ≠ 0)]
  have habs : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast Int.one_le_abs hz
  calc
    _ ≤ |(z:ℝ)|^(-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le habs (by linarith)
    _ = _ := by rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs, one_div]

lemma tsum_ennreal_int_circuit_weight_le (q : ℝ) (hq : 2 ≤ q) :
    (∑' z : ℤ, ENNReal.ofReal (|(z:ℝ)|^(-q))) ≤ 4 := by
  calc
    _ ≤ ∑' z : ℤ, ENNReal.ofReal (1/(z:ℝ)^2) :=
      ENNReal.tsum_le_tsum (fun z => ENNReal.ofReal_le_ofReal (int_circuit_weight_le_sq q hq z))
    _ = ENNReal.ofReal (∑' z : ℤ, 1/(z:ℝ)^2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
        (Real.summable_one_div_int_pow.mpr (by norm_num))).symm
    _ ≤ 4 := by exact_mod_cast ENNReal.ofReal_le_ofReal tsum_int_inv_sq_le_four

lemma tsum_ennreal_fin_prod (r : ℕ) (f : ℤ → ℝ≥0∞) :
    (∑' a : Fin r → ℤ, ∏ j, f (a j)) = (∑' z, f z)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [←(Fin.consEquiv (fun _ : Fin (r+1) => ℤ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod (f := fun (z : ℤ) (a : Fin r → ℤ) => f z * ∏ j, f (a j))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ih, ENNReal.tsum_mul_right, pow_succ']



theorem tsum_integerCircuitWeight_le (r : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    (∑' a : Fin r → ℤ, ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-q))) ≤ 4^r := by
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)]
  rw [tsum_ennreal_fin_prod r (fun z : ℤ => ENNReal.ofReal (|(z:ℝ)|^(-q)))]
  exact pow_le_pow_left' (tsum_ennreal_int_circuit_weight_le q hq) _


end SingleLatticeCovering.SimplexYoung


namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal BigOperators

lemma rationalCircuitFactor {r d : ℕ} (a : Fin (r+1) → ℝ) (ha : ∀ j, 0 < a j) :
    (a 0)⁻¹^d * (∏ j : Fin r, (a j.succ / a 0)^(-((d:ℝ)/(r+1:ℕ)))) =
      ∏ j : Fin (r+1), a j^(-((d:ℝ)/(r+1:ℕ))) := by
  let s : ℝ := (d:ℝ)/(r+1:ℕ)
  change (a 0)⁻¹^d * (∏ j : Fin r, (a j.succ / a 0)^(-s)) = ∏ j, a j^(-s)
  simp_rw [Real.div_rpow (ha _).le (ha 0).le]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_succ]
  have he : (a 0)⁻¹^d / ((a 0)^(-s))^r = (a 0)^(-s) := by
    rw [←Real.rpow_natCast, ←Real.rpow_neg_one, ←Real.rpow_mul (ha 0).le,
      ←Real.rpow_natCast, ←Real.rpow_mul (ha 0).le, ←Real.rpow_sub (ha 0)]
    congr 1
    dsimp [s]
    push_cast
    field_simp
    ring
  calc
    _ = ((a 0)⁻¹^d / ((a 0)^(-s))^r) * ∏ j : Fin r, a j.succ^(-s) := by ring
    _ = _ := by rw [he]



lemma rationalCircuitVolume_le {r d : ℕ} (hr : 0 < r)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (a : Fin (r+1) → ℤ) :
    rationalCircuitVolume J a ≤ ENNReal.ofReal ((simplexConstant r)^d *
      (∏ j, |(a j:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))) * (volume J).toReal^r) := by
  classical
  unfold rationalCircuitVolume
  split_ifs with ha
  · have hc (j : Fin r) : -(a j.succ:ℝ)/(a 0:ℝ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (Int.cast_ne_zero.mpr (ha j.succ))) (Int.cast_ne_zero.mpr (ha 0))
    have hb := volume_weightedSimplexConfiguration_sharp hr hJ _ hc
    apply (mul_le_mul_right hb _).trans_eq
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp_rw [abs_div, abs_neg]
    calc
      _ = (simplexConstant r)^d *
          (|(a 0:ℝ)|⁻¹^d * (∏ j : Fin r, (|(a j.succ:ℝ)|/|(a 0:ℝ)|)^(-((d:ℝ)/(r+1:ℕ))))) *
          (volume J).toReal^r := by ring
      _ = _ := by rw [rationalCircuitFactor _ (fun j => abs_pos.mpr (Int.cast_ne_zero.mpr (ha j)))]
  · exact bot_le



theorem rationalCircuitVolumeSum_le {r d : ℕ} (hr : 0 < r) (hd : 2*(r+1) ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    rationalCircuitVolumeSum (r := r) J ≤
      ENNReal.ofReal ((4:ℝ)^(r+1) * (simplexConstant r)^d * (volume J).toReal^r) := by
  have hq : (2:ℝ) ≤ (d:ℝ)/(r+1:ℕ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast hd
  let B : ℝ≥0∞ := ENNReal.ofReal ((simplexConstant r)^d * (volume J).toReal^r)
  calc
    _ ≤ ∑' a : Fin (r+1) → ℤ, B * ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply (rationalCircuitVolume_le hr hJ a).trans_eq
      dsimp [B]
      rw [←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (by unfold simplexConstant; positivity) _) (pow_nonneg ENNReal.toReal_nonneg _))]
      congr 1
      ring
    _ = B * (∑' a : Fin (r+1) → ℤ, ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/(r+1:ℕ))))) :=
      ENNReal.tsum_mul_left
    _ ≤ B * 4^(r+1) := mul_le_mul_right (tsum_integerCircuitWeight_le (r+1) _ hq) _
    _ = _ := by
      dsimp [B]
      rw [←ENNReal.ofReal_ofNat, ←ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4),
        ←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (by unfold simplexConstant; positivity) _) (pow_nonneg ENNReal.toReal_nonneg _))]
      congr 1
      ring




end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open scoped ENNReal BigOperators

lemma affine_three_product_abs_ge_two (a : Fin 3 → ℤ)
    (ha : ∀ j, a j ≠ 0) (hs : ∑ j, a j = 0) :
    (2:ℝ) ≤ ∏ j, |(a j:ℝ)| := by
  have hm (j : Fin 3) : (1:ℝ) ≤ |(a j:ℝ)| := by exact_mod_cast Int.one_le_abs (ha j)
  have hl : 2 ≤ |a 0| ∨ 2 ≤ |a 1| ∨ 2 ≤ |a 2| := by
    by_contra h
    push Not at h
    have h0 := le_abs_self (a 0)
    have h0' := neg_le_abs (a 0)
    have h1 := le_abs_self (a 1)
    have h1' := neg_le_abs (a 1)
    have h2 := le_abs_self (a 2)
    have h2' := neg_le_abs (a 2)
    have hz0 := ha 0
    have hz1 := ha 1
    have hz2 := ha 2
    rw [Fin.sum_univ_three] at hs
    omega
  rw [Fin.prod_univ_three]
  have h01 : (1:ℝ) ≤ |(a 0:ℝ)| * |(a 1:ℝ)| := by nlinarith [hm 0,hm 1]
  have h02 : (1:ℝ) ≤ |(a 0:ℝ)| * |(a 2:ℝ)| := by nlinarith [hm 0,hm 2]
  have h12 : (1:ℝ) ≤ |(a 1:ℝ)| * |(a 2:ℝ)| := by nlinarith [hm 1,hm 2]
  rcases hl with hl | hl | hl
  · have hl' : (2:ℝ) ≤ |(a 0:ℝ)| := by exact_mod_cast hl
    nlinarith [mul_le_mul_of_nonneg_left h12 (abs_nonneg (a 0:ℝ))]
  · have hl' : (2:ℝ) ≤ |(a 1:ℝ)| := by exact_mod_cast hl
    nlinarith [mul_le_mul_of_nonneg_left h02 (abs_nonneg (a 1:ℝ))]
  · have hl' : (2:ℝ) ≤ |(a 2:ℝ)| := by exact_mod_cast hl
    nlinarith [mul_le_mul_of_nonneg_right h01 (abs_nonneg (a 2:ℝ))]

lemma prod_circuit_weight_with_saving {r : ℕ} (b : Fin r → ℝ) (hb : ∀ j, 0 < b j)
    {s : ℝ} (hs : 2 ≤ s) (hp : 2 ≤ ∏ j, b j) :
    (∏ j, b j^(-s)) ≤ (2:ℝ)^(2-s) * ∏ j, b j^(-(2:ℝ)) := by
  have hprod : 0 < ∏ j, b j := Finset.prod_pos (fun j _ => hb j)
  rw [Real.finsetProd_rpow _ _ (fun j _ => (hb j).le),
    Real.finsetProd_rpow _ _ (fun j _ => (hb j).le)]
  calc
    _ = (∏ j, b j)^(2-s) * (∏ j, b j)^(-(2:ℝ)) := by
      rw [←Real.rpow_add hprod]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by linarith)) (by positivity)


theorem tsum_affine_three_weight_le {s : ℝ} (hs : 2 ≤ s) :
    (∑' a : Fin 3 → ℤ, if (∀ j, a j ≠ 0) ∧ (∑ j, a j = 0) then
      ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-s)) else 0) ≤
        ENNReal.ofReal ((2:ℝ)^(2-s)) * 4^3 := by
  classical
  calc
    _ ≤ ∑' a : Fin 3 → ℤ, ENNReal.ofReal ((2:ℝ)^(2-s)) *
        ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-(2:ℝ))) := by
      apply ENNReal.tsum_le_tsum
      intro a
      split_ifs with h
      · rw [←ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        exact prod_circuit_weight_with_saving _
          (fun j => abs_pos.mpr (Int.cast_ne_zero.mpr (h.1 j))) hs
          (affine_three_product_abs_ge_two a h.1 h.2)
      · exact bot_le
    _ = ENNReal.ofReal ((2:ℝ)^(2-s)) *
        (∑' a : Fin 3 → ℤ, ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-(2:ℝ)))) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_right (tsum_integerCircuitWeight_le 3 2 le_rfl) _

lemma two_neg_third_le : (2:ℝ)^(-(1:ℝ)/3) ≤ 8/9 := by
  have hc : ((2:ℝ)^(-(1:ℝ)/3))^3 = (1:ℝ)/2 := by
    rw [←Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have hn : 0 ≤ (2:ℝ)^(-(1:ℝ)/3) := by positivity
  nlinarith [sq_nonneg ((2:ℝ)^(-(1:ℝ)/3) - 8/9)]




end SingleLatticeCovering.SimplexYoung
namespace SingleLatticeCovering.SimplexYoung
lemma simplexConstant_sq {r : ℕ} (hr : 0 < r) :
    (simplexConstant r)^2 = (1 + (r:ℝ)⁻¹)^r / (r+1:ℕ) := by
  have h : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  unfold simplexConstant
  rw [div_pow, ←pow_mul, mul_comm r 2, pow_mul, inv_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  congr 1
  congr 1
  push_cast
  field_simp

end SingleLatticeCovering.SimplexYoung
namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal BigOperators

lemma rank_two_saved_constant : simplexConstant 2 * (2:ℝ)^(-(1:ℝ)/3) ≤ simplexConstant 3 := by
  have htwo : (simplexConstant 2)^2 = (3:ℝ)/4 := by rw [simplexConstant_sq (by norm_num)]; norm_num
  have hthree : (simplexConstant 3)^2 = (16:ℝ)/27 := by rw [simplexConstant_sq (by norm_num)]; norm_num
  have he : simplexConstant 2 * (8/9:ℝ) = simplexConstant 3 := by
    have h2 := simplexConstant_nonneg 2
    have h3 := simplexConstant_nonneg 3
    nlinarith
  exact (mul_le_mul_of_nonneg_left two_neg_third_le (simplexConstant_nonneg 2)).trans_eq he

lemma rank_two_saved_power (d : ℕ) :
    (simplexConstant 2)^d * (2:ℝ)^(2-(d:ℝ)/3) ≤ 4*(simplexConstant 3)^d := by
  have he : (2:ℝ)^(2-(d:ℝ)/3) = 4*((2:ℝ)^(-(1:ℝ)/3))^d := by
    rw [←Real.rpow_mul_natCast (by norm_num), ←show (2:ℝ)^(2:ℝ) = 4 by norm_num,
      ←Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [he]
  calc
    _ = 4*(simplexConstant 2 * (2:ℝ)^(-(1:ℝ)/3))^d := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (simplexConstant_nonneg 2) (by positivity)) rank_two_saved_constant d) (by norm_num)



theorem affineRankTwoCircuitVolumeSum_le {d : ℕ} (hd : 6 ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    affineCircuitVolumeSum (r := 2) J ≤
      ENNReal.ofReal (256 * (simplexConstant 3)^d * (volume J).toReal^2) := by
  classical
  have hs : (2:ℝ) ≤ (d:ℝ)/3 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    exact_mod_cast hd
  let B : ℝ≥0∞ := ENNReal.ofReal ((simplexConstant 2)^d * (volume J).toReal^2)
  have h (a : Fin 3 → ℤ) :
      (if ∑ j, a j = 0 then rationalCircuitVolume J a else 0) ≤
        B * (if (∀ j, a j ≠ 0) ∧ ∑ j, a j = 0 then
          ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/3))) else 0) := by
    by_cases ha : ∀ j, a j ≠ 0
    · by_cases hz : ∑ j, a j = 0
      · rw [ite_eq_left hz, ite_eq_left ⟨ha,hz⟩]
        apply (rationalCircuitVolume_le (r := 2) (by norm_num) hJ a).trans_eq
        dsimp [B]
        rw [←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (simplexConstant_nonneg 2) _) (sq_nonneg _))]
        congr 1
        ring
      · simp [hz]
    · simp [rationalCircuitVolume, ha]
  calc
    _ ≤ ∑' a : Fin 3 → ℤ, B * (if (∀ j, a j ≠ 0) ∧ ∑ j, a j = 0 then
          ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/3))) else 0) := ENNReal.tsum_le_tsum h
    _ = B * (∑' a : Fin 3 → ℤ, if (∀ j, a j ≠ 0) ∧ ∑ j, a j = 0 then
          ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/3))) else 0) := ENNReal.tsum_mul_left
    _ ≤ B * (ENNReal.ofReal ((2:ℝ)^(2-(d:ℝ)/3)) * 4^3) :=
      mul_le_mul_right (tsum_affine_three_weight_le hs) _
    _ = ENNReal.ofReal (64*((simplexConstant 2)^d*(2:ℝ)^(2-(d:ℝ)/3))*(volume J).toReal^2) := by
      dsimp [B]
      rw [show (4:ℝ≥0∞)^3 = ENNReal.ofReal (64:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by positivity),
        ←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (simplexConstant_nonneg 2) _) (sq_nonneg _))]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rank_two_saved_power d) (by norm_num : (0:ℝ) ≤ 64))
        (sq_nonneg (volume J).toReal)
      nlinarith only [hh]




end SingleLatticeCovering.SimplexYoung




noncomputable section
namespace SingleLatticeCovering.GridCoordinates
open MeasureTheory Measure Set TopologicalSpace.PositiveCompacts
open scoped BigOperators


lemma flatten_unit_preimage {r d : ℕ} :
    (flatten (r:=r) (d:=d)) ⁻¹' (piIcc01 (Fin r × Fin d) : Set (Fin r × Fin d → ℝ)) =
      Set.pi Set.univ (fun _ : Fin d => Set.pi Set.univ (fun _ : Fin r => Set.Icc (0:ℝ) 1)) := by
  ext x
  simp only [Set.mem_preimage, piIcc01, TopologicalSpace.PositiveCompacts.coe_mk,
    TopologicalSpace.Compacts.coe_mk, Set.mem_univ_pi, flatten, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Prod.forall]
  exact forall_comm



theorem flatten_measurePreserving {r d : ℕ} :
    MeasurePreserving (flatten (r:=r) (d:=d)) volume volume := by
  have hm : Measurable (flatten (r:=r) (d:=d) : (Fin d → Fin r → ℝ) → (Fin r × Fin d → ℝ)) :=
    flatten.toContinuousLinearEquiv.continuous.measurable
  have : IsAddHaarMeasure (volume.map (flatten (r:=r) (d:=d))) :=
    flatten.toContinuousLinearEquiv.isAddHaarMeasure_map volume
  refine ⟨hm, ?_⟩
  have hunit : (volume.map (flatten (r:=r) (d:=d))) (piIcc01 (Fin r × Fin d)) = 1 := by
    rw [Measure.map_apply hm
      (piIcc01 (Fin r × Fin d)).isCompact.measurableSet, flatten_unit_preimage]
    simp only [volume_pi, Measure.pi_pi, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one, Finset.prod_const_one]
  have he := (addHaarMeasure_eq_iff (piIcc01 (Fin r × Fin d))
    (volume.map (flatten (r:=r) (d:=d)))).mpr hunit
  rw [addHaarMeasure_eq_volume_pi] at he
  exact he.symm


end SingleLatticeCovering.GridCoordinates

namespace SingleLatticeCovering.CircuitVolume
open MeasureTheory Measure Set Filter
open GridCoordinates GridGeometry SimplexYoung
open scoped Topology Pointwise BigOperators

lemma configuration_preimage {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    flatten ⁻¹' weightedGridConfiguration J c = weightedSimplexConfiguration J c := rfl

lemma configuration_volume {r d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (c : Fin r → ℝ) :
    volume (weightedGridConfiguration J c) = volume (weightedSimplexConfiguration J c) := by
  have h := (flatten_measurePreserving (r:=r) (d:=d)).measure_preimage
    (weightedGridConfiguration_compact hJ c).measurableSet.nullMeasurableSet
  simpa only [configuration_preimage] using h.symm

lemma rationalCircuitVolume_toReal {r d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (a : Fin (r+1) → ℤ) (ha : ∀ i, a i ≠ 0) :
    (rationalCircuitVolume J a).toReal =
      volume.real (weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ))) /
        |(a 0:ℝ)|^d := by
  rw [rationalCircuitVolume, ite_eq_left ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), measureReal_def, configuration_volume hJ]
  rw [inv_pow, div_eq_mul_inv, mul_comm]

lemma summable_rationalCircuitVolume_toReal {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    Summable (fun a : Fin (r+1) → ℤ => (rationalCircuitVolume J a).toReal) := by
  apply ENNReal.summable_toReal
  exact ne_of_lt (lt_of_le_of_lt (rationalCircuitVolumeSum_le hr hd hJ) ENNReal.ofReal_lt_top)

lemma affineCircuitVolumeSum_ne_top {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    affineCircuitVolumeSum (r:=r) J ≠ ⊤ := by
  have hh : affineCircuitVolumeSum (r:=r) J ≤ rationalCircuitVolumeSum (r:=r) J := by
    apply ENNReal.tsum_le_tsum
    intro a
    split_ifs <;> simp
  exact ne_of_lt (lt_of_le_of_lt (hh.trans (rationalCircuitVolumeSum_le hr hd hJ)) ENNReal.ofReal_lt_top)


lemma primitive_volume_sum_le {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    (∑' a : PrimitiveAffineCoefficients r, (rationalCircuitVolume J a.val).toReal) ≤
      (affineCircuitVolumeSum (r:=r) J).toReal := by
  have hsub : (∑' a : PrimitiveAffineCoefficients r, rationalCircuitVolume J a.val) ≤
      affineCircuitVolumeSum (r:=r) J := by
    have hh := ENNReal.tsum_comp_le_tsum_of_injective
      (Subtype.val_injective (p:=fun a : Fin (r+1) → ℤ =>
        (∀ i, a i ≠ 0) ∧ Finset.univ.gcd a = 1 ∧ ∑ i, a i = 0))
      (fun a : Fin (r+1) → ℤ => if ∑ i, a i = 0 then rationalCircuitVolume J a else 0)
    change (∑' a : PrimitiveAffineCoefficients r,
      if ∑ i, a.val i = 0 then rationalCircuitVolume J a.val else 0) ≤ _ at hh
    have he (a : PrimitiveAffineCoefficients r) :
        (if ∑ i, a.val i = 0 then rationalCircuitVolume J a.val else 0) =
          rationalCircuitVolume J a.val := ite_eq_left a.property.2.2
    simpa only [he,affineCircuitVolumeSum] using hh
  have hn := affineCircuitVolumeSum_ne_top hr hd hJ
  have hsubn : (∑' a : PrimitiveAffineCoefficients r, rationalCircuitVolume J a.val) ≠ ⊤ :=
    ne_top_of_le_ne_top hn hsub
  rw [← ENNReal.tsum_toReal_eq (fun a => ENNReal.ne_top_of_tsum_ne_top hsubn a)]
  exact ENNReal.toReal_mono hn hsub



end SingleLatticeCovering.CircuitVolume





noncomputable section
namespace SingleLatticeCovering.CircuitPacking
open MeasureTheory Module
open scoped ENNReal BigOperators Pointwise

lemma colored_packing_bound {E ι Q : Type*} [MeasurableSpace E] [Fintype Q]
    (μ : Measure E) (S : Finset ι) (color : ι → Q) (P : ι → Set E)
    (U : Set E) (v : ℝ≥0∞)
    (hm : ∀ i ∈ S, MeasurableSet (P i))
    (hv : ∀ i ∈ S, μ (P i) = v)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → color i = color j → Disjoint (P i) (P j))
    (hU : ∀ i ∈ S, P i ⊆ U) :
    (S.card : ℝ≥0∞) * v ≤ (Fintype.card Q : ℝ≥0∞) * μ U := by
  classical
  calc
    _ = ∑ i ∈ S, μ (P i) := by
      symm
      calc
        _ = ∑ _i ∈ S, v := Finset.sum_congr rfl hv
        _ = _ := by simp
    _ = ∑ q : Q, ∑ i ∈ S.filter (fun i => color i = q), μ (P i) :=
      (Finset.sum_fiberwise S color _).symm
    _ ≤ ∑ _q : Q, μ U := by
      apply Finset.sum_le_sum
      intro q _
      rw [←measure_biUnion_finset]
      · apply measure_mono
        simp only [Set.iUnion_subset_iff]
        intro i hi
        exact hU i ((Finset.mem_filter.mp hi).1)
      · intro i hi j hj hne
        obtain ⟨hiS,hiq⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjS,hjq⟩ := Finset.mem_filter.mp hj
        exact hd i hiS j hjS hne (hiq.trans hjq.symm)
      · intro i hi
        exact hm i ((Finset.mem_filter.mp hi).1)
    _ = _ := by simp



lemma fundamental_translate_disjoint {r : ℕ}
    (b : Basis (Fin r) ℝ (Fin r → ℝ)) {x y : Fin r → ℝ}
    (hxy : x-y ∈ Submodule.span ℤ (Set.range b)) (hne : x ≠ y) :
    Disjoint (x +ᵥ ZSpan.fundamentalDomain b) (y +ᵥ ZSpan.fundamentalDomain b) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨u,hu,huz⟩ := hz
  obtain ⟨v,hv,hvz⟩ := hz'
  change x+u=z at huz
  change y+v=z at hvz
  have huv : -u+v=x-y := by
    have hv' : v = -y+(x+u) := by rw [huz, ←hvz]; abel
    rw [hv']
    abel
  have hf := (ZSpan.fract_eq_fract b u v).mpr (huv ▸ hxy)
  rw [(ZSpan.fract_eq_self (b := b)).mpr hu, (ZSpan.fract_eq_self (b := b)).mpr hv] at hf
  apply hne
  simpa [hf] using huz.trans hvz.symm


lemma fundamental_coord_bound {r : ℕ} (b : Basis (Fin r) ℝ (Fin r → ℝ))
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ i j, |b i j| ≤ R)
    {u : Fin r → ℝ} (hu : u ∈ ZSpan.fundamentalDomain b) (j : Fin r) :
    |u j| ≤ r*R := by
  have he : u j = ∑ i, b.repr u i * b i j := by
    simpa using congr_fun (b.sum_repr u).symm j
  rw [he]
  calc
    _ ≤ ∑ i, |b.repr u i * b i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin r, R := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hu i).1]
      exact (mul_le_mul_of_nonneg_left (hb i j) (hu i).1).trans
        (by nlinarith [(hu i).2])
    _ = _ := by simp

lemma sublattice_index_ne_zero {r : ℕ}
    (L0 L : Submodule ℤ (Fin r → ℝ))
    [DiscreteTopology L0] [IsZLattice ℝ L0]
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : L0 ≤ L) :
    (L0.toAddSubgroup.comap L.toAddSubgroup.subtype).index ≠ 0 := by
  have hi := ZLattice.covolume_div_covolume_eq_relIndex L0 L hL
  intro hz
  change (L0.toAddSubgroup.relIndex L.toAddSubgroup) = 0 at hz
  rw [hz, Nat.cast_zero] at hi
  exact (div_ne_zero (ZLattice.covolume_ne_zero L0 volume)
    (ZLattice.covolume_ne_zero L volume)) hi

lemma fundamental_volume {r : ℕ} (b : Basis (Fin r) ℝ (Fin r → ℝ)) :
    volume (ZSpan.fundamentalDomain b) =
      ENNReal.ofReal (ZLattice.covolume (Submodule.span ℤ (Set.range b))) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume)]
  exact (ENNReal.ofReal_toReal
    (ne_of_lt ((ZSpan.fundamentalDomain_isBounded b).measure_lt_top))).symm

lemma cancel_packing_ratio {a b c u : ℝ≥0∞}
    (ha : a ≠ 0) (hat : a ≠ ⊤) (hb : b ≠ 0) (hbt : b ≠ ⊤)
    (h : c*a ≤ a/b*u) : c*b ≤ u := by
  apply (ENNReal.mul_le_mul_iff_right ha hat).mp
  calc
    a*(c*b) = (c*a)*b := by ring
    _ ≤ (a/b*u)*b := mul_le_mul_left h _
    _ = a*u := by rw [mul_right_comm, ENNReal.div_mul_cancel hb hbt]

lemma sublattice_card_ratio {r : ℕ}
    (L0 L : Submodule ℤ (Fin r → ℝ))
    [DiscreteTopology L0] [IsZLattice ℝ L0]
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : L0 ≤ L)
    [Fintype (L ⧸ (L0.toAddSubgroup.comap L.toAddSubgroup.subtype))] :
    (Fintype.card (L ⧸ (L0.toAddSubgroup.comap L.toAddSubgroup.subtype)) : ℝ≥0∞) =
      ENNReal.ofReal (ZLattice.covolume L0) / ENNReal.ofReal (ZLattice.covolume L) := by
  rw [←ENNReal.ofReal_natCast, ←ENNReal.ofReal_div_of_pos (ZLattice.covolume_pos L volume)]
  congr 1
  rw [←Nat.card_eq_fintype_card,
    ZLattice.covolume_div_covolume_eq_relIndex L0 L hL]
  rfl


lemma lattice_coset_packing {r : ℕ}
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin r) ℝ (Fin r → ℝ)) (hbL : ∀ i, b i ∈ L)
    (S : Finset L) (U : Set (Fin r → ℝ))
    (hU : ∀ x ∈ S, (x:Fin r → ℝ) +ᵥ ZSpan.fundamentalDomain b ⊆ U) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume L) ≤ volume U := by
  classical
  let L0 : Submodule ℤ (Fin r → ℝ) := Submodule.span ℤ (Set.range b)
  have hL : L0 ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hbL i)
  let H : AddSubgroup L := L0.toAddSubgroup.comap L.toAddSubgroup.subtype
  let : Fintype (L ⧸ H) := AddSubgroup.fintypeOfIndexNeZero
    (sublattice_index_ne_zero L0 L hL)
  let color : L → L ⧸ H := fun x => QuotientAddGroup.mk x
  let P := ZSpan.fundamentalDomain b
  have hp := colored_packing_bound volume S color (fun x : L => (x:Fin r → ℝ) +ᵥ P) U (volume P)
    (fun x _ => (ZSpan.fundamentalDomain_measurableSet b).const_vadd (x:Fin r → ℝ))
    (fun x _ => measure_vadd volume (x:Fin r → ℝ) P)
    (by
      intro x hx y hy hne hc
      apply fundamental_translate_disjoint b
      · exact (QuotientAddGroup.eq_iff_sub_mem.mp hc : x-y ∈ H)
      · exact fun he => hne (Subtype.ext he)) hU
  rw [fundamental_volume b, sublattice_card_ratio L0 L hL] at hp
  exact cancel_packing_ratio
    (ENNReal.ofReal_ne_zero_iff.mpr (ZLattice.covolume_pos L0 volume))
    ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr (ZLattice.covolume_pos L volume))
    ENNReal.ofReal_ne_top hp


theorem short_basis_lattice_packing {r : ℕ}
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin r) ℝ (Fin r → ℝ)) (hbL : ∀ i, b i ∈ L)
    (S : Finset L) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |b i j| ≤ R) (hS : ∀ x ∈ S, ∀ j, |(x:Fin r → ℝ) j| ≤ R) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume L) ≤
      volume (Set.pi Set.univ (fun _ : Fin r => Set.Icc (-((r+1:ℕ):ℝ)*R) (((r+1:ℕ):ℝ)*R))) := by
  apply lattice_coset_packing L b hbL S
  intro x hx z hz
  obtain ⟨u,hu,rfl⟩ := hz
  intro j _
  have huj := fundamental_coord_bound b hR hb hu j
  have hxj := hS x hx j
  change -((r+1:ℕ):ℝ)*R ≤ (x:Fin r → ℝ) j + u j ∧
    (x:Fin r → ℝ) j + u j ≤ ((r+1:ℕ):ℝ)*R
  have ht := (abs_add_le ((x:Fin r → ℝ) j) (u j)).trans (add_le_add hxj huj)
  have ht' := abs_le.mp ht
  push_cast
  constructor <;> linarith

lemma volume_symmetric_box (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume (Set.pi Set.univ (fun _ : Fin r => Set.Icc (-R) R)) =
      ENNReal.ofReal (2*R)^r := by
  have _ := hR
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc, sub_neg_eq_add, ←two_mul]

lemma short_basis_lattice_count {r : ℕ}
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin r) ℝ (Fin r → ℝ)) (hbL : ∀ i, b i ∈ L)
    (S : Finset L) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |b i j| ≤ R)
    (hS : ∀ x ∈ S, ∀ j, |(x:Fin r → ℝ) j| ≤ R) :
    (S.card : ℝ) * ZLattice.covolume L ≤ (2*(r+1)*R)^r := by
  have h := short_basis_lattice_packing L b hbL S hR hb hS
  simp only [neg_mul] at h
  rw [volume_symmetric_box r (by positivity)] at h
  have h' := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h'
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using h'


end SingleLatticeCovering.CircuitPacking


end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitLattices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.CircuitArithmetic
open Module Submodule MeasureTheory
open scoped BigOperators Pointwise

lemma integerCoordinates_cast {r : ℕ} (x : integerLattice r) (i : Fin r) :
    ((integerCoordinates r x i : ℤ) : ℝ) = (x : Fin r → ℝ) i := by
  have h := (Pi.basisFun ℝ (Fin r)).restrictScalars_repr_apply ℤ x i
  simpa [integerCoordinates] using h

lemma integerLattice_covolume (r : ℕ) : ZLattice.covolume (integerLattice r) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin r)) volume),
    ZSpan.fundamentalDomain_pi_basisFun]
  simp [measureReal_def, volume_pi, Measure.pi_pi, Real.volume_Ico]


lemma mem_congruenceKernel_iff {r q : ℕ} (A : integerLattice r →ₗ[ℤ] ZMod q)
    (x : integerLattice r) :
    (x : Fin r → ℝ) ∈ congruenceKernel A ↔ A x = 0 := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    have : y=x := Subtype.ext hxy
    subst y
    exact hy
  · intro h
    exact ⟨x,h,rfl⟩

instance congruenceKernel_full {r q : ℕ} [NeZero q]
    (A : integerLattice r →ₗ[ℤ] ZMod q) : IsZLattice ℝ (congruenceKernel A) where
  span_top := by
    apply top_unique
    rw [←(Pi.basisFun ℝ (Fin r)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let z := (Pi.basisFun ℝ (Fin r)).restrictScalars ℤ i
    have hz : (q:ℤ) • (z : Fin r → ℝ) ∈ congruenceKernel A := by
      apply (mem_congruenceKernel_iff A ((q:ℤ) • z)).mpr
      rw [map_smul]
      simp
    have hh := (Submodule.span ℝ (congruenceKernel A : Set (Fin r → ℝ))).smul_mem
      ((q:ℝ)⁻¹) (Submodule.subset_span hz)
    have hq : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have he : (q:ℝ)⁻¹ • ((q:ℤ) • (z : Fin r → ℝ)) = (Pi.basisFun ℝ (Fin r)) i := by
      ext j
      simp [z, hq]
    rwa [he] at hh

lemma congruenceKernel_relIndex {r q : ℕ}
    (A : integerLattice r →ₗ[ℤ] ZMod q) :
    (congruenceKernel A).toAddSubgroup.relIndex (integerLattice r).toAddSubgroup =
      A.toAddMonoidHom.ker.index := by
  have he : (congruenceKernel A).toAddSubgroup.comap (integerLattice r).toAddSubgroup.subtype =
      A.toAddMonoidHom.ker := by
    ext x
    exact mem_congruenceKernel_iff A x
  change ((congruenceKernel A).toAddSubgroup.comap (integerLattice r).toAddSubgroup.subtype).index = _
  rw [he]



theorem congruenceKernel_covolume {r q : ℕ} [NeZero q]
    (A : integerLattice r →ₗ[ℤ] ZMod q) (hA : Function.Surjective A) :
    ZLattice.covolume (congruenceKernel A) = q := by
  classical
  have h := ZLattice.covolume_div_covolume_eq_relIndex
    (congruenceKernel A) (integerLattice r) (congruenceKernel_le A)
  rw [integerLattice_covolume, div_one, congruenceKernel_relIndex] at h
  have hi : A.toAddMonoidHom.ker.index = q := by
    rw [AddSubgroup.index_ker]
    have hr : A.toAddMonoidHom.range = ⊤ := AddMonoidHom.range_eq_top.mpr hA
    rw [hr, Nat.card_eq_fintype_card]
    simp
  simpa [hi] using h


lemma relationForm_surjective {r q : ℕ} (a : Fin r → ℤ)
    (h : ∃ z : Fin r → ℤ, (∑ i, a i*z i : ZMod q) = 1) :
    Function.Surjective (relationForm q a) := by
  obtain ⟨z,hz⟩ := h
  have hone : relationForm q a ((integerCoordinates r).symm z) = 1 := by
    simpa [relationForm] using hz
  intro c
  obtain ⟨k,hk⟩ := ZMod.intCast_surjective c
  refine ⟨k • (integerCoordinates r).symm z,?_⟩
  rw [map_smul, hone]
  simpa using hk



lemma primitive_relation_surjective {r : ℕ} (a : Fin (r+1) → ℤ)
    (ha : Finset.univ.gcd a = 1) :
    Function.Surjective (relationForm (a 0).natAbs (fun i => a i.succ)) := by
  apply relationForm_surjective
  obtain ⟨z,hz⟩ := Finset.gcd_eq_sum_mul Finset.univ a
  rw [ha, Fin.sum_univ_succ] at hz
  refine ⟨fun i => z i.succ,?_⟩
  have hcast := congrArg (fun t : ℤ => (t : ZMod (a 0).natAbs)) hz
  have hzero : (a 0 : ZMod (a 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl (a 0))
  simpa [Int.cast_add, Int.cast_mul, Int.cast_sum, hzero] using hcast.symm

lemma primitive_relation_covolume {r : ℕ} (a : Fin (r+1) → ℤ)
    (hzero : a 0 ≠ 0) (ha : Finset.univ.gcd a = 1) :
    ZLattice.covolume (congruenceKernel (relationForm (a 0).natAbs (fun i => a i.succ))) =
      |(a 0 : ℝ)| := by
  let : NeZero (a 0).natAbs := ⟨Int.natAbs_ne_zero.mpr hzero⟩
  rw [congruenceKernel_covolume _ (primitive_relation_surjective a ha)]
  simp

end SingleLatticeCovering.CircuitArithmetic

namespace SingleLatticeCovering.CircuitGrid
open Module Submodule MeasureTheory CircuitPacking CircuitArithmetic
open scoped BigOperators


lemma exists_column_basis {r : ℕ} {κ : Type*} [Finite κ]
    (v : κ → (Fin r → ℝ)) (hv : Submodule.span ℝ (Set.range v) = ⊤) :
    ∃ b : Basis (Fin r) ℝ (Fin r → ℝ), ∀ i, ∃ j, b i = v j := by
  classical
  obtain ⟨ι,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ v
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  let b : Basis ι ℝ (Fin r → ℝ) := Basis.mk hli (by rw [hspan,hv])
  have hc : Fintype.card ι = r := by
    rw [←Module.finrank_eq_card_basis b, Module.finrank_pi, Fintype.card_fin]
  let e : ι ≃ Fin r := Fintype.equivOfCardEq (by simpa using hc)
  refine ⟨b.reindex e, fun i => ⟨a (e.symm i), ?_⟩⟩
  simp [b, Basis.reindex_apply, Basis.coe_mk]

lemma count_of_spanning_columns {r : ℕ} {κ : Type*} [Finite κ]
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : κ → L) (hv : Submodule.span ℝ (Set.range (fun j => (v j : Fin r → ℝ))) = ⊤)
    (S : Finset L) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |(v i : Fin r → ℝ) j| ≤ R)
    (hS : ∀ x ∈ S, ∀ j, |(x:Fin r → ℝ) j| ≤ R) :
    (S.card : ℝ) * ZLattice.covolume L ≤ (2*(r+1)*R)^r := by
  obtain ⟨b,hb'⟩ := exists_column_basis (fun j => (v j : Fin r → ℝ)) hv
  apply short_basis_lattice_count L b (fun i => ?_) S hR (fun i j => ?_) hS
  · obtain ⟨j,hj⟩ := hb' i
    rw [hj]
    exact (v j).property
  · obtain ⟨k,hk⟩ := hb' i
    rw [hk]
    exact hb k j




theorem array_count_of_spanning_columns {r d : ℕ} {κ : Type*} [Finite κ]
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : κ → L) (hv : Submodule.span ℝ (Set.range (fun j => (v j : Fin r → ℝ))) = ⊤)
    (X : Finset (Fin d → L)) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |(v i : Fin r → ℝ) j| ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i : Fin r → ℝ) j| ≤ R) :
    (X.card : ℝ) * (ZLattice.covolume L)^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  let S : Finset L := X.biUnion (fun x => Finset.univ.image x)
  have hS : ∀ x ∈ S, ∀ j, |(x : Fin r → ℝ) j| ≤ R := by
    intro x hx
    obtain ⟨z,hz,hxz⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hxz
    exact hX z hz i
  have hXS : X ⊆ Fintype.piFinset (fun _ : Fin d => S) := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hcard : (X.card : ℝ) ≤ (S.card : ℝ)^d := by
    have hc : X.card ≤ S.card^d := by
      simpa using (Finset.card_le_card hXS)
    exact_mod_cast hc
  have hp := count_of_spanning_columns L v hv S hR hb hS
  have hcpos : 0 ≤ ZLattice.covolume L := (ZLattice.covolume_pos L volume).le
  calc
    (X.card : ℝ)*ZLattice.covolume L^d ≤ (S.card:ℝ)^d*ZLattice.covolume L^d :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hcpos d)
    _ = ((S.card:ℝ)*ZLattice.covolume L)^d := (mul_pow _ _ _).symm
    _ ≤ ((2*(r+1)*R)^r)^d := pow_le_pow_left₀ (by positivity) hp d


lemma mulVec_surjective_of_rowIndependent {F ι κ : Type*} [Field F]
    [Fintype ι] [Fintype κ] (W : Matrix κ ι F)
    (hW : LinearIndependent F W.row) : Function.Surjective W.mulVec := by
  classical
  have hf : Function.Injective W.vecMulLinear := Matrix.vecMul_injective_iff.mpr hW
  intro b
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective hf
    ((dotProductBilin F F) b)
  refine ⟨fun j => g (Pi.single j 1), ?_⟩
  ext i
  have hi := DFunLike.congr_fun hg (Pi.single i 1)
  have hrow : W.vecMulLinear (Pi.single i 1) = W i := by
    ext j
    simp [Matrix.vecMulLinear, Matrix.vecMul, dotProduct, Pi.single_apply]
  change g (W.vecMulLinear (Pi.single i 1)) = _ at hi
  rw [hrow] at hi
  have hsingle (x : ι) : (fun j => if x=j then (1 : F) else 0) = Pi.single x 1 := by
    funext j
    simp [Pi.single_apply,eq_comm]
  have hgi := LinearMap.pi_apply_eq_sum_univ g (W i)
  simp_rw [hsingle] at hgi
  simpa [Matrix.mulVec, dotProduct, dotProductBilin, Pi.single_apply, mul_comm, eq_comm] using hgi.symm.trans hi



lemma span_affine_columns {r d : ℕ} (x : Fin r → Fin d → ℤ)
    (hx : LinearIndependent ℝ (affineRows x).row) :
    Submodule.span ℝ (Set.range (affineRows x).col) = ⊤ := by
  rw [←Matrix.range_mulVecLin]
  exact LinearMap.range_eq_top.mpr (mulVec_surjective_of_rowIndependent _ hx)

lemma integer_array_count {r d : ℕ} {κ : Type*} [Finite κ]
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : κ → L) (hv : Submodule.span ℝ (Set.range (fun j => (v j : Fin r → ℝ))) = ⊤)
    (X : Finset (Fin r → Fin d → ℤ)) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |(v i : Fin r → ℝ) j| ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ R)
    (hL : ∀ x ∈ X, ∀ j, (fun i => (x i j : ℝ)) ∈ L) :
    (X.card : ℝ) * (ZLattice.covolume L)^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  let f : {x // x ∈ X} → Fin d → L := fun x j => ⟨fun i => (x.val i j : ℝ), hL x.val x.property j⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i j
    have hh := congrFun (congrArg (fun z : L => (z : Fin r → ℝ)) (congrFun h j)) i
    exact Int.cast_injective hh
  let Y : Finset (Fin d → L) := X.attach.image f
  have hc : Y.card = X.card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
  have hy : ∀ y ∈ Y, ∀ i j, |(y i : Fin r → ℝ) j| ≤ R := by
    intro y hy
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
    exact fun i j => hX x.val x.property j i
  have h := array_count_of_spanning_columns L v hv Y hR hb hy
  simpa only [hc] using h



theorem integer_affine_grid_count {r d : ℕ}
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (X : Finset (Fin r → Fin d → ℤ)) {R : ℝ} (hR : 1 ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ R)
    (hL : ∀ x ∈ X, ∀ j, (fun i => (x i j : ℝ)) ∈ L)
    (hone : (fun _ : Fin r => (1:ℝ)) ∈ L)
    (hind : ∀ x ∈ X, LinearIndependent ℝ (affineRows x).row) :
    (X.card : ℝ) * (ZLattice.covolume L)^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  by_cases hn : X.Nonempty
  · obtain ⟨x,hx⟩ := hn
    have hcol (j : Fin (d+1)) : (affineRows x).col j ∈ L := by
      refine Fin.cases ?_ (fun j => ?_) j
      · have he : (affineRows x).col 0 = (fun _ : Fin r => (1:ℝ)) := by ext i; rfl
        rw [he]
        exact hone
      · have he : (affineRows x).col j.succ = (fun i : Fin r => (x i j : ℝ)) := by ext i; rfl
        rw [he]
        exact hL x hx j
    let v : Fin (d+1) → L := fun j => ⟨(affineRows x).col j, hcol j⟩
    apply integer_array_count L v (span_affine_columns x (hind x hx)) X (by linarith) ?_ hX hL
    intro j i
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [v, affineRows, Matrix.col, Matrix.transpose] using hR
    · simpa [v, affineRows, Matrix.col, Matrix.transpose] using hX x hx i j
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity

lemma relation_zero_mod {r : ℕ} (a w : Fin (r+1) → ℤ)
    (h : ∑ i, a i*w i = 0) :
    (∑ i : Fin r, (a i.succ : ZMod (a 0).natAbs) * (w i.succ : ZMod (a 0).natAbs)) = 0 := by
  have hcast := congrArg (fun t : ℤ => (t : ZMod (a 0).natAbs)) h
  have hzero : (a 0 : ZMod (a 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl (a 0))
  simpa [Fin.sum_univ_succ, Int.cast_add, Int.cast_mul, Int.cast_sum, hzero] using hcast

lemma projected_relation_mem {r : ℕ} (a w : Fin (r+1) → ℤ)
    (h : ∑ i, a i*w i = 0) :
    (fun i : Fin r => (w i.succ : ℝ)) ∈
      congruenceKernel (relationForm (a 0).natAbs (fun i => a i.succ)) := by
  let z : integerLattice r := (integerCoordinates r).symm (fun i => w i.succ)
  have he : (z : Fin r → ℝ) = (fun i => (w i.succ : ℝ)) := by
    ext i
    rw [←integerCoordinates_cast]
    simp [z]
  rw [←he, mem_congruenceKernel_iff]
  simpa [relationForm, z] using relation_zero_mod a w h





theorem full_circuit_grid_bound {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha0 : a 0 ≠ 0) (hprim : Finset.univ.gcd a = 1) (haff : ∑ i, a i = 0)
    (X : Finset (Fin (r+1) → Fin d → ℤ)) {R : ℝ} (hR : 1 ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ R)
    (hrel : ∀ x ∈ X, ∀ j, ∑ i, a i*x i j = 0)
    (hind : ∀ x ∈ X, LinearIndependent ℝ (affineRows (fun i => x i.succ)).row) :
    (X.card : ℝ) * |(a 0:ℝ)|^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  let : NeZero (a 0).natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
  let L := congruenceKernel (relationForm (a 0).natAbs (fun i => a i.succ))
  let tail : (Fin (r+1) → Fin d → ℤ) → (Fin r → Fin d → ℤ) := fun x i => x i.succ
  let Y := X.image tail
  have htail : Set.InjOn tail (X : Set (Fin (r+1) → Fin d → ℤ)) := by
    intro x hx y hy hxy
    funext i j
    refine Fin.cases ?_ (fun i => congrFun (congrFun hxy i) j) i
    have hxj := hrel x hx j
    have hyj := hrel y hy j
    rw [Fin.sum_univ_succ] at hxj hyj
    have hs : (∑ i : Fin r, a i.succ*x i.succ j) = ∑ i : Fin r, a i.succ*y i.succ j := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : ℤ => a i.succ*z) (congrFun (congrFun hxy i) j)
    rw [hs] at hxj
    apply mul_left_cancel₀ ha0
    linarith
  have hc : Y.card = X.card := Finset.card_image_iff.mpr htail
  have hybound : ∀ y ∈ Y, ∀ i j, |(y i j:ℝ)| ≤ R := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact fun i j => hX x hx i.succ j
  have hyL : ∀ y ∈ Y, ∀ j, (fun i => (y i j:ℝ)) ∈ L := by
    intro y hy j
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact projected_relation_mem a (fun i => x i j) (hrel x hx j)
  have hone : (fun _ : Fin r => (1:ℝ)) ∈ L := by
    simpa using projected_relation_mem a (fun _ => 1) (by simpa using haff)
  have hyind : ∀ y ∈ Y, LinearIndependent ℝ (affineRows y).row := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hind x hx
  have h := integer_affine_grid_count L Y hR hybound hyL hone hyind
  rw [hc] at h
  dsimp [L] at h
  rwa [primitive_relation_covolume a ha0 hprim] at h





end SingleLatticeCovering.CircuitGrid

namespace SingleLatticeCovering.CircuitGrid
open Module Submodule MeasureTheory Matrix
open scoped BigOperators Pointwise

lemma gcd_permute {r : ℕ} (a : Fin (r+1) → ℤ) (e : Equiv.Perm (Fin (r+1))) :
    Finset.univ.gcd (fun i => a (e i)) = Finset.univ.gcd a := by
  classical
  change Finset.univ.gcd (a ∘ e) = _
  rw [←Finset.gcd_image, Finset.image_univ_of_surjective e.surjective]



theorem full_circuit_grid_bound_at {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha : ∀ i, a i ≠ 0) (hprim : Finset.univ.gcd a = 1) (haff : ∑ i, a i = 0)
    (X : Finset (Fin (r+1) → Fin d → ℤ)) {R : ℝ} (hR : 1 ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ R)
    (hrel : ∀ x ∈ X, ∀ j, ∑ i, a i*x i j = 0)
    (hind : ∀ x ∈ X, ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℝ (affineRows (fun i => x (e i.succ))).row)
    (k : Fin (r+1)) :
    (X.card : ℝ) * |(a k:ℝ)|^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  let e := Equiv.swap (0 : Fin (r+1)) k
  let f : (Fin (r+1) → Fin d → ℤ) → (Fin (r+1) → Fin d → ℤ) := fun x i => x (e i)
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun hxy j
  have hc : (X.image f).card = X.card := Finset.card_image_of_injective X hf
  have hprim' : Finset.univ.gcd (fun i => a (e i)) = 1 := by
    rw [gcd_permute, hprim]
  have hsum : (∑ i, a (e i)) = 0 := (Equiv.sum_comp e a).trans haff
  have hb (x) (hx : x ∈ X.image f) (i j) : |(x i j:ℝ)| ≤ R := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hX y hy (e i) j
  have hrel' (x) (hx : x ∈ X.image f) (j) : ∑ i, a (e i)*x i j = 0 := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (Equiv.sum_comp e (fun i => a i*y i j)).trans (hrel y hy j)
  have hind' (x) (hx : x ∈ X.image f) :
      LinearIndependent ℝ (affineRows (fun i => x i.succ)).row := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hind y hy e
  have h := full_circuit_grid_bound (fun i => a (e i)) (ha (e 0)) hprim' hsum
    (X.image f) hR hb hrel' hind'
  simpa only [hc, e, Equiv.swap_apply_left] using h


end SingleLatticeCovering.CircuitGrid

noncomputable section
namespace SingleLatticeCovering.CircuitWeight
open scoped BigOperators ENNReal
lemma tsum_int_inv_sq_le_four : (∑' z : ℤ, 1/(z:ℝ)^2) ≤ 4 := by
  have hs : Summable (fun z : ℤ => 1/(z:ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (by intro z; simp) hs]
  have he : (∑' z : ℕ+, 1/((z:ℕ):ℝ)^2) = Real.pi^2/6 := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1/(n:ℝ)^2)]
    have hh := hasSum_zeta_two.summable.tsum_eq_zero_add
    simpa only [hasSum_zeta_two.tsum_eq, Nat.cast_zero, zero_pow (by omega : 2 ≠ 0),
      div_zero, zero_add] using hh.symm
  simp only [Int.cast_zero, zero_pow (by omega : 2 ≠ 0), div_zero, zero_add,
    Int.cast_natCast, he, two_smul]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

lemma int_circuit_weight_le_sq (q : ℝ) (hq : 2 ≤ q) (z : ℤ) :
    |(z:ℝ)|^(-q) ≤ 1/(z:ℝ)^2 := by
  by_cases hz : z = 0
  · simp [hz, Real.zero_rpow (by linarith : -q ≠ 0)]
  have habs : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast Int.one_le_abs hz
  calc
    _ ≤ |(z:ℝ)|^(-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le habs (by linarith)
    _ = _ := by rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs, one_div]

lemma tsum_ennreal_int_circuit_weight_le (q : ℝ) (hq : 2 ≤ q) :
    (∑' z : ℤ, ENNReal.ofReal (|(z:ℝ)|^(-q))) ≤ 4 := by
  calc
    _ ≤ ∑' z : ℤ, ENNReal.ofReal (1/(z:ℝ)^2) :=
      ENNReal.tsum_le_tsum (fun z => ENNReal.ofReal_le_ofReal (int_circuit_weight_le_sq q hq z))
    _ = ENNReal.ofReal (∑' z : ℤ, 1/(z:ℝ)^2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
        (Real.summable_one_div_int_pow.mpr (by norm_num))).symm
    _ ≤ 4 := by exact_mod_cast ENNReal.ofReal_le_ofReal tsum_int_inv_sq_le_four

lemma tsum_ennreal_fin_prod (r : ℕ) (f : ℤ → ℝ≥0∞) :
    (∑' a : Fin r → ℤ, ∏ j, f (a j)) = (∑' z, f z)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [←(Fin.consEquiv (fun _ : Fin (r+1) => ℤ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod (f := fun (z : ℤ) (a : Fin r → ℤ) => f z * ∏ j, f (a j))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ih, ENNReal.tsum_mul_right, pow_succ']



theorem tsum_integerCircuitWeight_le (r : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    (∑' a : Fin r → ℤ, ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-q))) ≤ 4^r := by
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)]
  rw [tsum_ennreal_fin_prod r (fun z : ℤ => ENNReal.ofReal (|(z:ℝ)|^(-q)))]
  exact pow_le_pow_left' (tsum_ennreal_int_circuit_weight_le q hq) _




lemma height_weight_le {r d : ℕ} {q : ℝ} (hq : 0 < q)
    (a : Fin (r+1) → ℤ) (ha : ∀ i, a i ≠ 0)
    (hmax : ∀ i, |(a i : ℝ)| ≤ q) :
    q⁻¹^d ≤ ∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ))) := by
  have he : q⁻¹^d = ∏ _ : Fin (r+1), q^(-((d:ℝ)/(r+1:ℕ))) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ←Real.rpow_natCast, ←Real.rpow_neg_one, ←Real.rpow_mul hq.le,
      ←Real.rpow_natCast, ←Real.rpow_mul hq.le]
    congr 1
    push_cast
    field_simp
  rw [he]
  apply Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg hq.le _)
  intro i _
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.mpr (Int.cast_ne_zero.mpr (ha i)))
    (hmax i) (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

lemma summable_circuit_weight {r d : ℕ} (hd : 2*(r+1) ≤ d) :
    Summable (fun a : Fin (r+1) → ℤ => ∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))) := by
  have hq : (2:ℝ) ≤ (d:ℝ)/(r+1:ℕ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast hd
  have ht := tsum_integerCircuitWeight_le (r+1) _ hq
  have hn : (∑' a : Fin (r+1) → ℤ, ENNReal.ofReal (∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ))))) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt ht (by finiteness))
  have hp (a : Fin (r+1) → ℤ) : 0 ≤ ∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ))) := by positivity
  simpa only [ENNReal.toReal_ofReal (hp _)] using ENNReal.summable_toReal hn



end SingleLatticeCovering.CircuitWeight

namespace SingleLatticeCovering.CircuitGrid
open scoped BigOperators



theorem normalized_circuit_grid_domination {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha : ∀ i, a i ≠ 0) (hprim : Finset.univ.gcd a = 1) (haff : ∑ i, a i = 0)
    (X : Finset (Fin (r+1) → Fin d → ℤ)) {B t : ℝ} (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ B*t)
    (hrel : ∀ x ∈ X, ∀ j, ∑ i, a i*x i j = 0)
    (hind : ∀ x ∈ X, ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℝ (affineRows (fun i => x (e i.succ))).row) :
    (X.card : ℝ) / t^(r*d) ≤ (2*(r+1)*B)^(r*d) *
      ∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ))) := by
  classical
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |(a i:ℝ)|)
    Finset.univ_nonempty
  have hq : 0 < |(a k:ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (ha k))
  have hBB : 0 ≤ 2*(r+1:ℕ)*B := by positivity
  have htt : 0 < t := by linarith
  have hp := full_circuit_grid_bound_at a ha hprim haff X
    (one_le_mul_of_one_le_of_one_le hB ht) hX hrel hind k
  have hnorm : (X.card:ℝ) / t^(r*d) ≤ (2*(r+1)*B)^(r*d) * |(a k:ℝ)|⁻¹^d := by
    apply (div_le_iff₀ (pow_pos htt _)).mpr
    have hdiv := (le_div_iff₀ (pow_pos hq d)).mpr hp
    calc
      _ ≤ ((2*(r+1)*(B*t))^r)^d / |(a k:ℝ)|^d := hdiv
      _ = (2*(r+1)*B)^(r*d) * |(a k:ℝ)|⁻¹^d * t^(r*d) := by
        rw [←pow_mul, show 2*(r+1)*(B*t) = (2*(r+1)*B)*t by ring, mul_pow]
        rw [inv_pow, div_eq_mul_inv]
        ring
  exact hnorm.trans (mul_le_mul_of_nonneg_left
    (CircuitWeight.height_weight_le hq a ha (fun i => hmax i (Finset.mem_univ i)))
    (by positivity))


end SingleLatticeCovering.CircuitGrid




noncomputable section
namespace SingleLatticeCovering.CircuitLimit
open Filter
open scoped Topology




theorem eventually_tsum_le_of_dominated_comparison {α β : Type*}
    {l : Filter α} [l.NeBot] (f g : α → β → ℝ) (G b : β → ℝ)
    (hb : Summable b) (hb0 : ∀ a, 0 ≤ b a)
    (hg0 : ∀ t a, 0 ≤ g t a) (hG : Summable G)
    (hlim : ∀ a, Tendsto (fun t => g t a) l (𝓝 (G a)))
    (hf : ∀ᶠ t in l, ∀ a, 0 ≤ f t a ∧ f t a ≤ g t a ∧ f t a ≤ b a)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, (∑' a, f t a) < (∑' a, G a)+ε := by
  let H := fun t a => min (g t a) (b a)
  have hH0 (t a) : 0 ≤ H t a := le_min (hg0 t a) (hb0 a)
  have hHbound (t a) : ‖H t a‖ ≤ b a := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 t a)]
    exact min_le_right _ _
  have hHsum (t) : Summable (H t) := hb.of_norm_bounded (hHbound t)
  have hHlim : Tendsto (fun t => ∑' a, H t a) l (𝓝 (∑' a, min (G a) (b a))) :=
    tendsto_tsum_of_dominated_convergence hb (fun a => (hlim a).min tendsto_const_nhds)
      (Eventually.of_forall hHbound)
  have hG0 (a) : 0 ≤ G a := ge_of_tendsto (hlim a) (Eventually.of_forall (fun t => hg0 t a))
  have hminsum : Summable (fun a => min (G a) (b a)) := by
    apply hb.of_norm_bounded
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hG0 a) (hb0 a))]
    exact min_le_right _ _
  have hminle : (∑' a, min (G a) (b a)) ≤ ∑' a, G a :=
    hminsum.tsum_le_tsum (fun _ => min_le_left _ _) hG
  filter_upwards [hf,hHlim.eventually (eventually_lt_nhds
    (show (∑' a, min (G a) (b a)) < (∑' a, G a)+ε by linarith))] with t ht hlt
  have hfs : Summable (f t) := hb.of_norm_bounded (fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ht a).1]
    exact (ht a).2.2)
  exact (hfs.tsum_le_tsum (fun a => le_min (ht a).2.1 (ht a).2.2) (hHsum t)).trans_lt hlt


end SingleLatticeCovering.CircuitLimit


end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.CircuitGridSum
open CircuitVolume SimplexYoung GridGeometry FiniteKernel CircuitGrid
open MeasureTheory Measure Filter
open scoped Topology Pointwise BigOperators




theorem eventually_sum_normalized_circuits_le {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)}
    (hJc : IsCompact J) (hJv : Convex ℝ J) (h0 : 0 ∈ J)
    (X : ℝ → PrimitiveAffineCoefficients r → Finset (Fin (r+1) → Fin d → ℤ))
    {B : ℝ} (hB : 1 ≤ B)
    (hX : ∀ t, 1 ≤ t → ∀ a x, x ∈ X t a → ∀ i j, |(x i j:ℝ)| ≤ B*t)
    (hJ : ∀ t, 1 ≤ t → ∀ a x, x ∈ X t a → ∀ i, (fun j => t⁻¹*(x i j:ℝ)) ∈ J)
    (hrel : ∀ t, 1 ≤ t → ∀ a x, x ∈ X t a → ∀ j, ∑ i, a.val i*x i j = 0)
    (hind : ∀ t, 1 ≤ t → ∀ a x, x ∈ X t a → ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℝ (affineRows (fun i => x (e i.succ))).row)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      (∑' a : PrimitiveAffineCoefficients r, ((X t a).card:ℝ)/t^(r*d)) <
        (affineCircuitVolumeSum (r:=r) J).toReal+ε := by
  let w : PrimitiveAffineCoefficients r → ℝ :=
    fun a => ∏ i, |(a.val i:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))
  have hw : Summable w :=
    (CircuitWeight.summable_circuit_weight hd).comp_injective Subtype.val_injective
  let b : PrimitiveAffineCoefficients r → ℝ := fun a => (2*(r+1)*B)^(r*d)*w a
  have hb : Summable b := hw.mul_left _
  have hb0 (a) : 0 ≤ b a := by dsimp [b,w]; positivity
  let G : PrimitiveAffineCoefficients r → ℝ := fun a => (rationalCircuitVolume J a.val).toReal
  have hG : Summable G :=
    (summable_rationalCircuitVolume_toReal hr hd hJc).comp_injective Subtype.val_injective
  let g : ℝ → PrimitiveAffineCoefficients r → ℝ := fun t a => max 0
    ((Nat.card ↥(weightedGridConfiguration J (fun i => -(a.val i.succ:ℝ)/(a.val 0:ℝ)) ∩
        t⁻¹ • (kernelLattice (gridRelationForm (d:=d) (a.val 0).natAbs (fun i => a.val i.succ)) :
          Set (Fin r × Fin d → ℝ))) : ℝ) / t^(r*d))
  have hlim (a) : Tendsto (fun t => g t a) atTop (𝓝 (G a)) := by
    have hh := GridLimit.primitive_configuration_limit a.val (a.property.1 0)
      a.property.2.1 hJc hJv h0
    rw [←rationalCircuitVolume_toReal hJc a.val a.property.1] at hh
    change Tendsto (fun t => max (0:ℝ) _) atTop (𝓝 _)
    simpa only [max_eq_right ENNReal.toReal_nonneg] using
      (tendsto_const_nhds (x:=(0:ℝ))).max hh
  have hf : ∀ᶠ t : ℝ in atTop, ∀ a : PrimitiveAffineCoefficients r,
      0 ≤ ((X t a).card:ℝ)/t^(r*d) ∧ ((X t a).card:ℝ)/t^(r*d) ≤ g t a ∧
        ((X t a).card:ℝ)/t^(r*d) ≤ b a := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    intro a
    refine ⟨by positivity, ?_, ?_⟩
    · exact (GridLimit.circuit_count_le_primitive_grid a.val (a.property.1 0) J hJc
        (X t a) ht0 (hJ t ht a) (hrel t ht a)).trans (le_max_right _ _)
    · exact normalized_circuit_grid_domination a.val a.property.1 a.property.2.1 a.property.2.2
        (X t a) hB ht (hX t ht a) (hrel t ht a) (hind t ht a)
  have hh := CircuitLimit.eventually_tsum_le_of_dominated_comparison
    (fun t a => ((X t a).card:ℝ)/t^(r*d)) g G b hb hb0 (fun _ _ => le_max_left _ _) hG hlim hf hε
  filter_upwards [hh] with t ht
  apply ht.trans_le
  change (∑' a : PrimitiveAffineCoefficients r, (rationalCircuitVolume J a.val).toReal)+ε ≤ _
  linarith [primitive_volume_sum_le hr hd hJc]


end SingleLatticeCovering.CircuitGridSum




noncomputable section
namespace SingleLatticeCovering.PrimitiveCircuit
open Module Matrix
open scoped BigOperators

lemma integer_relation_of_rat_dependence {s d : ℕ} (v : Fin s → Fin d → ℤ)
    (hdep : ¬LinearIndependent ℚ (fun i => fun j => (v i j : ℚ))) :
    ∃ z : Fin s → ℤ, (∃ i, z i ≠ 0) ∧ ∀ j, ∑ i, z i*v i j = 0 := by
  classical
  obtain ⟨g,hg,i,hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨q,hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) g
  choose z hz using hq
  have hq0 : (q : ℤ) ≠ 0 := nonZeroDivisors.ne_zero q.property
  have hzcast (i) : (z i : ℚ) = (q:ℤ)*g i := by
    simpa only [Algebra.smul_def, eq_intCast, Int.cast_id] using hz i
  refine ⟨z, ⟨i, ?_⟩, ?_⟩
  · intro hzi
    have h := hzcast i
    rw [hzi, Int.cast_zero] at h
    exact (mul_ne_zero (Int.cast_ne_zero.mpr hq0) hi) h.symm
  · intro j
    have hj := congrFun hg j
    have hs : (∑ i, (z i:ℚ)*(v i j:ℚ)) = 0 := by
      simp_rw [hzcast, mul_assoc, ←Finset.mul_sum]
      have he : (∑ i, g i*(v i j:ℚ)) = 0 := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hj
      rw [he, mul_zero]
    exact_mod_cast hs

lemma primitive_normalize {s d : ℕ} (v : Fin s → Fin d → ℤ) (z : Fin s → ℤ)
    (hne : ∃ i, z i ≠ 0) (hrel : ∀ j, ∑ i, z i*v i j = 0) :
    ∃ a : Fin s → ℤ, Finset.univ.gcd a = 1 ∧ (∃ i, a i ≠ 0) ∧
      ∀ j, ∑ i, a i*v i j = 0 := by
  classical
  obtain ⟨i,hi⟩ := hne
  let q := Finset.univ.gcd z
  let a := fun i => z i/q
  have hdiv (j) : q ∣ z j := Finset.gcd_dvd (Finset.mem_univ j)
  have hza (j) : q*a j = z j := by
    dsimp [a]
    exact Int.mul_ediv_cancel' (hdiv j)
  have hq : q ≠ 0 := by
    intro hq
    apply hi
    rw [←hza i,hq,zero_mul]
  refine ⟨a, Finset.gcd_div_eq_one (Finset.mem_univ i) hi, ⟨i, ?_⟩, ?_⟩
  · intro hai
    apply hi
    rw [←hza i,hai,mul_zero]
  · intro j
    apply mul_left_cancel₀ hq
    rw [mul_zero, Finset.mul_sum]
    simpa only [←mul_assoc, hza] using hrel j

lemma coefficients_nonzero_of_delete_independent {r d : ℕ}
    (v : Fin (r+1) → Fin d → ℤ) (a : Fin (r+1) → ℤ)
    (hne : ∃ i, a i ≠ 0) (hrel : ∀ j, ∑ i, a i*v i j = 0)
    (hind : ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℚ (fun i : Fin r => fun j => (v (e i.succ) j : ℚ))) :
    ∀ i, a i ≠ 0 := by
  classical
  intro k hk
  let e := Equiv.swap (0 : Fin (r+1)) k
  have h0 : a (e 0) = 0 := by simpa [e] using hk
  have hz : (∑ i : Fin r, (a (e i.succ):ℚ) • (fun j => (v (e i.succ) j:ℚ))) = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hperm := (Equiv.sum_comp e (fun i => a i*v i j)).trans (hrel j)
    rw [Fin.sum_univ_succ, h0, zero_mul, zero_add] at hperm
    exact_mod_cast hperm
  have hc := Fintype.linearIndependent_iff.mp (hind e) _ hz
  obtain ⟨i,hi⟩ := hne
  obtain ⟨j,rfl⟩ := e.surjective i
  apply hi
  refine Fin.cases h0 (fun j => ?_) j
  exact Int.cast_eq_zero.mp (hc j)



theorem exists_primitive_circuit_relation {r d : ℕ} (v : Fin (r+1) → Fin d → ℤ)
    (hdep : ¬LinearIndependent ℚ (fun i => fun j => (v i j : ℚ)))
    (hind : ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℚ (fun i : Fin r => fun j => (v (e i.succ) j : ℚ))) :
    ∃ a : Fin (r+1) → ℤ, Finset.univ.gcd a = 1 ∧ (∀ i, a i ≠ 0) ∧
      ∀ j, ∑ i, a i*v i j = 0 := by
  obtain ⟨z,hzne,hzrel⟩ := integer_relation_of_rat_dependence v hdep
  obtain ⟨a,hprim,hane,harel⟩ := primitive_normalize v z hzne hzrel
  exact ⟨a,hprim,coefficients_nonzero_of_delete_independent v a hane harel hind,harel⟩


end SingleLatticeCovering.PrimitiveCircuit

noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Matrix

lemma int_det_abs_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) {B : ℕ}
    (hB : ∀ i j, |A i j| ≤ (B : ℤ)) : |A.det| ≤ (k.factorial * B^k : ℕ) := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) hB
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow] using h

lemma intCast_eq_zero_small (p : ℕ) {z : ℤ} (hz : z.natAbs < p) :
    (z : ZMod p)=0 ↔ z=0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hz)
  · rintro rfl
    exact dvd_zero _

lemma det_mod_eq_zero_small {k : ℕ} (p : ℕ) (A : Matrix (Fin k) (Fin k) ℤ) {B : ℕ}
    (hB : ∀ i j, |A i j| ≤ (B : ℤ)) (hp : k.factorial*B^k<p) :
    (A.map (fun z => (z : ZMod p))).det=0 ↔ A.det=0 := by
  rw [←Int.cast_det]
  apply intCast_eq_zero_small
  have h := int_det_abs_le A hB
  have hlt : |A.det| < (p : ℤ) := lt_of_le_of_lt h (by exact_mod_cast hp)
  exact_mod_cast (show (A.det.natAbs : ℤ)<p by rwa [Int.natCast_natAbs])


end SingleLatticeCovering.RogersPreparation


noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Matrix Module Submodule CircuitGrid



lemma exists_column_minor {F : Type*} [Field F] {k n : ℕ}
    (W : Matrix (Fin k) (Fin n) F) (hW : LinearIndependent F W.row) :
    ∃ c : Fin k ↪ Fin n, (W.submatrix id c).det≠0 := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' F W.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have htop : Submodule.span F (Set.range (W.col ∘ a))=⊤ := by
    rw [hspan,←Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr (mulVec_surjective_of_rowIndependent W hW)
  let b : Basis κ F (Fin k → F) := Basis.mk hli (by rw [htop])
  have hcard : Fintype.card κ=k := by
    rw [←Module.finrank_eq_card_basis b,Module.finrank_pi,Fintype.card_fin]
  let e : Fin k ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let c : Fin k ↪ Fin n := ⟨a ∘ e,ha.comp e.injective⟩
  refine ⟨c,Matrix.nonsingular_iff_det_ne_zero.mp ?_⟩
  apply Matrix.Nonsingular.of_linearIndependent_col
  exact hli.comp e e.injective


lemma rowIndependent_of_column_minor {F : Type*} [Field F] {k n : ℕ}
    (W : Matrix (Fin k) (Fin n) F) (c : Fin k → Fin n)
    (hc : (W.submatrix id c).det≠0) : LinearIndependent F W.row := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero hc
  exact h.of_comp (LinearMap.funLeft F F c)

lemma rowIndependent_iff_column_minor {F : Type*} [Field F] {k n : ℕ}
    (W : Matrix (Fin k) (Fin n) F) :
    LinearIndependent F W.row ↔ ∃ c : Fin k ↪ Fin n, (W.submatrix id c).det≠0 :=
  ⟨exists_column_minor W,fun ⟨c,hc⟩ => rowIndependent_of_column_minor W c hc⟩



lemma rowIndependent_mod_iff_rat {k n : ℕ} (p : ℕ) [Fact p.Prime]
    (W : Matrix (Fin k) (Fin n) ℤ) {B : ℕ}
    (hB : ∀ i j, |W i j| ≤ (B : ℤ)) (hp : k.factorial*B^k<p) :
    LinearIndependent (ZMod p) (W.map (fun z => (z : ZMod p))).row ↔
      LinearIndependent ℚ (W.map (fun z => (z : ℚ))).row := by
  rw [rowIndependent_iff_column_minor,rowIndependent_iff_column_minor]
  apply exists_congr
  intro c
  have h : ((W.submatrix id c).map (fun z => (z : ZMod p))).det=0 ↔
      (W.submatrix id c).det=0 := det_mod_eq_zero_small p _ (fun i j => hB i (c j)) hp
  have hq : ((W.submatrix id c).map (fun z => (z : ℚ))).det=0 ↔
      (W.submatrix id c).det=0 := by rw [←Int.cast_det,Int.cast_eq_zero]
  exact not_congr (h.trans hq.symm)


end SingleLatticeCovering.RogersPreparation

namespace SingleLatticeCovering.AffineCircuit
open Matrix CircuitVolume CircuitGrid RogersPreparation
open scoped BigOperators


lemma rowIndependent_real_iff_rat {k n : ℕ} (W : Matrix (Fin k) (Fin n) ℤ) :
    LinearIndependent ℝ (W.map (fun z => (z:ℝ))).row ↔ LinearIndependent ℚ (W.map (fun z => (z:ℚ))).row := by
  rw [rowIndependent_iff_column_minor,rowIndependent_iff_column_minor]
  apply exists_congr
  intro c
  change ((W.submatrix id c).map (Int.cast:ℤ → ℝ)).det ≠ 0 ↔
    ((W.submatrix id c).map (Int.cast:ℤ → ℚ)).det ≠ 0
  simp only [←Int.cast_det,Int.cast_ne_zero]

lemma IsCircuit.real_delete {r d : ℕ} {x : Fin (r+1) → Fin d → ℤ}
    (hx : IsCircuit x) (e : Equiv.Perm (Fin (r+1))) :
    LinearIndependent ℝ (affineRows (fun i => x (e i.succ))).row := by
  have h := (rowIndependent_real_iff_rat (integerRows (fun i => x (e i.succ)))).mpr (hx.2 e)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [affineRows,integerRows]

lemma IsCircuit.primitive_relation {r d : ℕ} {x : Fin (r+1) → Fin d → ℤ}
    (hx : IsCircuit x) : ∃ a : PrimitiveAffineCoefficients r,
      ∀ j, ∑ i, a.val i*x i j = 0 := by
  obtain ⟨a,hg,ha,hrel⟩ := PrimitiveCircuit.exists_primitive_circuit_relation
    (integerRows x) hx.1 hx.2
  have hs : ∑ i, a i = 0 := by simpa [integerRows] using hrel 0
  refine ⟨⟨a,ha,hg,hs⟩,?_⟩
  intro j
  simpa [integerRows] using hrel j.succ


lemma mem_circuits {r d : ℕ} {S : Finset (Fin d → ℤ)} {x : Fin (r+1) → Fin d → ℤ} :
    x ∈ circuits S r ↔ (∀ i, x i ∈ S) ∧ IsCircuit x := by
  classical
  simp only [circuits,Finset.mem_filter,Fintype.mem_piFinset]

lemma mem_coefficientCircuits {r d : ℕ} {S : Finset (Fin d → ℤ)}
    {a : PrimitiveAffineCoefficients r} {x : Fin (r+1) → Fin d → ℤ} :
    x ∈ coefficientCircuits S a ↔ ((∀ i, x i ∈ S) ∧ IsCircuit x) ∧
      ∀ j, ∑ i, a.val i*x i j = 0 := by
  classical
  simp only [coefficientCircuits,Finset.mem_filter,mem_circuits]

lemma circuits_covered {r d : ℕ} {S : Finset (Fin d → ℤ)}
    {x : Fin (r+1) → Fin d → ℤ} (hx : x ∈ circuits S r) :
    ∃ a : PrimitiveAffineCoefficients r, x ∈ coefficientCircuits S a := by
  obtain ⟨a,ha⟩ := (mem_circuits.mp hx).2.primitive_relation
  exact ⟨a,mem_coefficientCircuits.mpr ⟨mem_circuits.mp hx,ha⟩⟩



end SingleLatticeCovering.AffineCircuit



noncomputable section
namespace SingleLatticeCovering.CircuitEnumeration
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]



lemma card_enumerations (B : Finset (Finset ι)) (r : ℕ)
    (hr : ∀ T ∈ B, T.card = r) :
    Fintype.card (Enumerations B r) = B.card*r.factorial := by
  classical
  unfold Enumerations
  rw [Fintype.card_sigma]
  have he (T : B) : Fintype.card (Fin r ≃ T.val) = r.factorial := by
    have hc : Fintype.card (Fin r) = Fintype.card T.val := by
      simp only [Fintype.card_fin,Fintype.card_coe,hr T.val T.property]
    simpa using Fintype.card_equiv (Fintype.equivOfCardEq hc)
  simp [he]

lemma orderedCircuit_injective {ι : Type*} [DecidableEq ι] {r : ℕ} {B : Finset (Finset ι)} (e : B → ι) :
    Function.Injective (orderedCircuit (r:=r) e) := by
  classical
  rintro ⟨T,x⟩ ⟨U,y⟩ h
  have htail (i : Fin r) : (x i).val = (y i).val := by
    exact congrFun h i.succ
  have hTU : T = U := by
    apply Subtype.ext
    apply Finset.coe_injective
    have hx : Set.range (fun i => (x i).val) = (T.val : Set ι) := by
      change Set.range (Subtype.val ∘ x) = _
      rw [x.surjective.range_comp]
      exact Subtype.range_val
    have hy : Set.range (fun i => (y i).val) = (U.val : Set ι) := by
      change Set.range (Subtype.val ∘ y) = _
      rw [y.surjective.range_comp]
      exact Subtype.range_val
    rw [←hx,←hy]
    congr 1
    funext i
    exact htail i
  subst U
  congr 1
  apply Equiv.ext
  intro i
  exact Subtype.ext (htail i)



theorem card_mul_le_tsum_cover {α β : Type*} [DecidableEq β]
    (C : Finset β) (X : α → Finset β)
    (hC : ∀ x ∈ C, ∃ a, x ∈ X a) {u : ℝ} (hu : 0 ≤ u)
    (hs : Summable (fun a => ((X a).card:ℝ)*u)) :
    (C.card:ℝ)*u ≤ ∑' a, ((X a).card:ℝ)*u := by
  classical
  choose a ha using fun x : C => hC x.val x.property
  let A : Finset α := Finset.univ.image a
  have hsub : C ⊆ A.biUnion X := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    exact ⟨a ⟨x,hx⟩,Finset.mem_image.mpr ⟨⟨x,hx⟩,Finset.mem_univ _,rfl⟩,ha ⟨x,hx⟩⟩
  have hc : C.card ≤ ∑ a ∈ A, (X a).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcr : (C.card:ℝ) ≤ ∑ a ∈ A, ((X a).card:ℝ) := by exact_mod_cast hc
  calc
    (C.card:ℝ)*u ≤ (∑ a ∈ A, ((X a).card:ℝ))*u := mul_le_mul_of_nonneg_right hcr hu
    _ = ∑ a ∈ A, ((X a).card:ℝ)*u := by rw [Finset.sum_mul]
    _ ≤ ∑' a, ((X a).card:ℝ)*u := hs.sum_le_tsum A (fun _ _ => by positivity)



end SingleLatticeCovering.CircuitEnumeration

namespace SingleLatticeCovering.AffineCircuit
open CircuitVolume CircuitGrid MeasureTheory Measure Filter
open scoped BigOperators Topology

lemma coefficient_counts_summable {r d : ℕ} (hd : 2*(r+1) ≤ d)
    (S : Finset (Fin d → ℤ)) {B t : ℝ} (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hS : ∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ B*t) :
    Summable (fun a : PrimitiveAffineCoefficients r =>
      ((coefficientCircuits S a).card:ℝ)/t^(r*d)) := by
  have hw := (CircuitWeight.summable_circuit_weight hd).comp_injective
    (Subtype.val_injective (p:=fun a : Fin (r+1) → ℤ =>
      (∀ i, a i ≠ 0) ∧ Finset.univ.gcd a = 1 ∧ ∑ i, a i = 0))
  apply (hw.mul_left ((2*(r+1)*B)^(r*d))).of_nonneg_of_le
  · intro a
    positivity
  · intro a
    exact normalized_circuit_grid_domination a.val a.property.1 a.property.2.1 a.property.2.2
      (coefficientCircuits S a) hB ht
      (fun x hx i j => hS (x i) ((mem_coefficientCircuits.mp hx).1.1 i) j)
      (fun x hx => (mem_coefficientCircuits.mp hx).2)
      (fun x hx => (mem_coefficientCircuits.mp hx).1.2.real_delete)




theorem eventually_circuit_count_le {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)} (hJc : IsCompact J)
    (hJv : Convex ℝ J) (h0 : 0 ∈ J) (S : ℝ → Finset (Fin d → ℤ))
    {B : ℝ} (hB : 1 ≤ B)
    (hS : ∀ t, 1 ≤ t → ∀ z ∈ S t, ∀ j, |(z j:ℝ)| ≤ B*t)
    (hSJ : ∀ t, 1 ≤ t → ∀ z ∈ S t, (fun j => t⁻¹*(z j:ℝ)) ∈ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ((circuits (S t) r).card:ℝ)/t^(r*d) <
      (SimplexYoung.affineCircuitVolumeSum (r:=r) J).toReal+ε := by
  have hh := CircuitGridSum.eventually_sum_normalized_circuits_le hr hd hJc hJv h0
    (fun t a => coefficientCircuits (S t) a) hB
    (fun t ht a x hx i j => hS t ht (x i) ((mem_coefficientCircuits.mp hx).1.1 i) j)
    (fun t ht a x hx i => hSJ t ht (x i) ((mem_coefficientCircuits.mp hx).1.1 i))
    (fun t ht a x hx => (mem_coefficientCircuits.mp hx).2)
    (fun t ht a x hx => (mem_coefficientCircuits.mp hx).1.2.real_delete) hε
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with t hlim ht
  apply lt_of_le_of_lt ?_ hlim
  have hs := coefficient_counts_summable hd (S t) hB ht (hS t ht)
  have hp := CircuitEnumeration.card_mul_le_tsum_cover (circuits (S t) r)
    (coefficientCircuits (S t)) (fun x hx => circuits_covered hx)
    (u:=(t^(r*d))⁻¹) (by positivity) (by simpa only [div_eq_mul_inv] using hs)
  simpa only [div_eq_mul_inv] using hp


end SingleLatticeCovering.AffineCircuit

namespace SingleLatticeCovering.CircuitEnumeration
variable {ι : Type*} [DecidableEq ι]
theorem factorial_count_le_map {κ : Type*} {r : ℕ} {B : Finset (Finset ι)}
    (hr : ∀ T ∈ B, T.card = r) (e : B → ι) (f : ι → κ) (hf : Function.Injective f)
    (C : Finset (Fin (r+1) → κ))
    (hC : ∀ x : Enumerations B r, (fun i => f (orderedCircuit e x i)) ∈ C) :
    B.card*r.factorial ≤ C.card := by
  let g : Enumerations B r → C := fun x => ⟨fun i => f (orderedCircuit e x i),hC x⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply orderedCircuit_injective e
    funext i
    exact hf (congrFun (congrArg Subtype.val hxy) i)
  simpa only [card_enumerations B r hr,Fintype.card_coe] using Fintype.card_le_of_injective g hg


end SingleLatticeCovering.CircuitEnumeration



noncomputable section
namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
open Submodule

variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]



lemma active_mono {v : ι → V} {S T : Finset ι} (hST : S ⊆ T) {e : ι}
    (h : Active (K := K) v S e) : Active (K := K) v T e := by
  apply Submodule.span_mono _ h
  exact Set.image_mono (by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨hST (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩)

lemma NoBrokenCircuit.mono {v : ι → V} {S T : Finset ι}
    (hT : NoBrokenCircuit (K := K) v T) (hST : S ⊆ T) :
    NoBrokenCircuit (K := K) v S := by
  intro e he
  exact hT e (active_mono hST he)

lemma NoBrokenCircuit.linearIndepOn {v : ι → V} {S : Finset ι}
    (h : NoBrokenCircuit (K := K) v S) : LinearIndepOn K v (S : Set ι) := by
  induction S using Finset.induction_on_min with
  | empty => simp
  | insert a S ha ih =>
    have hS := h.mono (Finset.subset_insert a S)
    have hn : v a ∉ Submodule.span K (v '' (S : Set ι)) := by
      have he : (insert a S).filter (fun j => a < j) = S := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hj, haj⟩
          · exact (lt_irrefl _ haj).elim
          · exact hj
        · intro hj
          exact ⟨Or.inr hj, ha j hj⟩
      simpa only [Active, he] using h a
    simpa only [Finset.coe_insert] using (ih hS).insert hn

lemma active_zero {v : ι → V} {S : Finset ι} {e : ι} (L : V →ₗ[K] K)
    (hS : ∀ j ∈ S, L (v j) = 0) (he : Active (K := K) v S e) : L (v e) = 0 := by
  change v e ∈ L.ker
  apply (Submodule.span_le.mpr _) he
  rintro _ ⟨j,hj,rfl⟩
  exact hS j (Finset.mem_filter.mp hj).1




lemma nbc_insert_least_zero {v : ι → V} {S : Finset ι} {a : ι}
    (L : V →ₗ[K] K) (hS : ∀ j ∈ S, L (v j) = 0) (ha : L (v a) = 0)
    (hmin : ∀ j, L (v j) = 0 → a ≤ j) :
    NoBrokenCircuit (K := K) v (insert a S) ↔ NoBrokenCircuit (K := K) v S := by
  constructor
  · exact fun h => h.mono (Finset.subset_insert _ _)
  · intro h e he
    have hz : L (v e) = 0 := active_zero L (by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ha
      · exact hS j hj) he
    have hae : a ≤ e := hmin e hz
    have hfilter : (insert a S).filter (fun j => e < j) = S.filter (fun j => e < j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hel⟩
        · exact (not_lt_of_ge hae hel).elim
        · exact ⟨hj,hel⟩
      · intro hj
        exact ⟨Or.inr hj.1,hj.2⟩
    exact h e (by simpa only [Active,hfilter] using he)

section Cone
variable {α : Type*} [DecidableEq α]



theorem cone_partial_sum (F : Finset (Finset α)) (a : α)
    (hins : ∀ S ∈ F, insert a S ∈ F) (herase : ∀ S ∈ F, S.erase a ∈ F) (k : ℕ) :
    (∑ S ∈ F, if S.card ≤ k then (-1:ℝ)^S.card else 0) =
      (-1:ℝ)^k * ((F.filter (fun S => a ∉ S ∧ S.card = k)).card:ℝ) := by
  let F₀ := F.filter (fun S => a ∉ S)
  have hsplit : F = F₀ ∪ F₀.image (insert a) := by
    ext S
    constructor
    · intro hS
      by_cases ha : a ∈ S
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨S.erase a, Finset.mem_filter.mpr ⟨herase S hS, Finset.notMem_erase _ _⟩,
          Finset.insert_erase ha⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,ha⟩)
    · intro hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact (Finset.mem_filter.mp hS).1
      · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
        exact hins T (Finset.mem_filter.mp hT).1
  have hd : Disjoint F₀ (F₀.image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hS'
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS'
    exact (Finset.mem_filter.mp hS).2 (Finset.mem_insert_self _ _)
  have hi : Set.InjOn (insert a) (↑F₀ : Set (Finset α)) := by
    intro S hS T hT h
    have hS' := (Finset.mem_filter.mp hS).2
    have hT' := (Finset.mem_filter.mp hT).2
    simpa only [Finset.erase_insert hS', Finset.erase_insert hT'] using congrArg (Finset.erase · a) h
  conv_lhs => rw [hsplit, Finset.sum_union hd, Finset.sum_image hi, ←Finset.sum_add_distrib]
  have hterm (S : Finset α) (hS : S ∈ F₀) :
      (if S.card ≤ k then (-1:ℝ)^S.card else 0) +
      (if (insert a S).card ≤ k then (-1:ℝ)^(insert a S).card else 0) =
        if S.card = k then (-1:ℝ)^k else 0 := by
    rw [Finset.card_insert_of_notMem (Finset.mem_filter.mp hS).2]
    rcases lt_trichotomy S.card k with h | h | h
    · rw [ite_eq_left h.le, ite_eq_left (by omega), ite_eq_right (by omega), pow_succ]
      ring
    · simp [h]
    · simp [show ¬S.card≤k by omega, show ¬S.card+1≤k by omega, show S.card≠k by omega]
  rw [Finset.sum_congr rfl hterm]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm]
  simp only [F₀, Finset.filter_filter]




end Cone

section Pointwise
variable [Fintype ι]

lemma mem_zeroFamily {ι : Type*} {K : Type*} {V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V] [Fintype ι] {v : ι → V} {L : V →ₗ[K] K} {e : ι} :
    e ∈ zeroFamily v L ↔ L (v e) = 0 := by
  classical
  simp [zeroFamily]

lemma mem_nbcFaces {ι : Type*} {K : Type*} {V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V] [Fintype ι] {v : ι → V} {Z : Finset ι} {S : Finset ι} :
    S ∈ nbcFaces (K := K) v Z ↔ S ⊆ Z ∧ NoBrokenCircuit (K := K) v S := by
  classical
  simp [nbcFaces]



theorem nbc_alternating_bound (v : ι → V) (L : V →ₗ[K] K) (k : ℕ) :
    0 ≤ (-1:ℝ)^k * (nbcValue v L k - avoidanceIndicator v L) := by
  classical
  by_cases hz : ∀ e, L (v e) ≠ 0
  · have he : zeroFamily v L = ∅ := by
      ext e
      simp [mem_zeroFamily, hz e]
    have hnbc : NoBrokenCircuit (K := K) v ∅ := by
      intro e he
      exact hz e (active_zero L (by simp) he)
    have hn : nbcFaces (K := K) v ∅ = {∅} := by
      ext S
      simp only [mem_nbcFaces, Finset.subset_empty, Finset.mem_singleton]
      constructor
      · exact And.left
      · intro hS
        subst S
        exact ⟨rfl, hnbc⟩
    simp [nbcValue, he, hn, avoidanceIndicator, hz]
  · have hZ : (zeroFamily v L).Nonempty := by
      push Not at hz
      obtain ⟨e,he⟩ := hz
      exact ⟨e,mem_zeroFamily.mpr he⟩
    let a := (zeroFamily v L).min' hZ
    have ha : a ∈ zeroFamily v L := Finset.min'_mem _ _
    have hmin : ∀ j, L (v j) = 0 → a ≤ j := by
      intro j hj
      exact Finset.min'_le _ _ (mem_zeroFamily.mpr hj)
    have hins : ∀ S ∈ nbcFaces (K := K) v (zeroFamily v L),
        insert a S ∈ nbcFaces (K := K) v (zeroFamily v L) := by
      intro S hS
      obtain ⟨hSZ,hN⟩ := mem_nbcFaces.mp hS
      apply mem_nbcFaces.mpr
      refine ⟨Finset.insert_subset ha hSZ, ?_⟩
      exact (nbc_insert_least_zero L (fun j hj => mem_zeroFamily.mp (hSZ hj))
        (mem_zeroFamily.mp ha) hmin).mpr hN
    have herase : ∀ S ∈ nbcFaces (K := K) v (zeroFamily v L),
        S.erase a ∈ nbcFaces (K := K) v (zeroFamily v L) := by
      intro S hS
      obtain ⟨hSZ,hN⟩ := mem_nbcFaces.mp hS
      exact mem_nbcFaces.mpr ⟨(Finset.erase_subset _ _).trans hSZ,
        hN.mono (Finset.erase_subset _ _)⟩
    have hc := cone_partial_sum (nbcFaces (K := K) v (zeroFamily v L)) a hins herase k
    change nbcValue v L k = _ at hc
    have hs : ((-1:ℝ)^k)^2 = 1 := by
      rw [←pow_mul, mul_comm k 2, pow_mul]
      norm_num
    rw [hc, avoidanceIndicator, ite_eq_right hz, sub_zero]
    have hn : (0:ℝ) ≤ ((nbcFaces (K := K) v (zeroFamily v L)).filter
        (fun S => a ∉ S ∧ S.card = k)).card := Nat.cast_nonneg _
    nlinarith only [hs, hn]

lemma nbc_even_bound (v : ι → V) (L : V →ₗ[K] K) (q : ℕ) :
    avoidanceIndicator v L ≤ nbcValue v L (2*q) := by
  have h := nbc_alternating_bound v L (2*q)
  norm_num [pow_mul] at h
  exact h




end Pointwise


section FiniteField
attribute [local instance] Classical.propDecidable
variable {τ κ : Type*} [Fintype τ] [Fintype κ]
lemma mulVec_surjective_of_rowIndependent (W : Matrix κ τ K)
    (hW : LinearIndependent K W.row) : Function.Surjective W.mulVec := by
  classical
  have hf : Function.Injective W.vecMulLinear := Matrix.vecMul_injective_iff.mpr hW
  intro b
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective hf
    ((dotProductBilin K K) b)
  refine ⟨fun j => g (Pi.single j 1), ?_⟩
  ext i
  have hi := DFunLike.congr_fun hg (Pi.single i 1)
  have hrow : W.vecMulLinear (Pi.single i 1) = W i := by
    ext j
    simp [Matrix.vecMulLinear, Matrix.vecMul, dotProduct, Pi.single_apply]
  change g (W.vecMulLinear (Pi.single i 1)) = _ at hi
  rw [hrow] at hi
  have hsingle (x : τ) : (fun j => if x=j then (1 : K) else 0) = Pi.single x 1 := by
    funext j
    simp [Pi.single_apply,eq_comm]
  have hgi := LinearMap.pi_apply_eq_sum_univ g (W i)
  simp_rw [hsingle] at hgi
  simpa [Matrix.mulVec, dotProduct, dotProductBilin, Pi.single_apply, mul_comm, eq_comm] using hgi.symm.trans hi

lemma card_fiber_mul_card_of_surjective
    {V U : Type*} [AddCommGroup V] [AddCommGroup U]
    [Module K V] [Module K U] [Fintype V] [Fintype U]
    (f : V →ₗ[K] U) (hf : Function.Surjective f) (b : U) :
    Fintype.card {x // f x = b} * Fintype.card U = Fintype.card V := by
  classical
  have hc (u : U) : Fintype.card {x // f x = u} = Fintype.card f.ker := by
    exact Fintype.card_congr (f.toAddMonoidHom.fiberEquivKerOfSurjective hf u)
  have hs := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at hs
  simpa only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using hs

lemma fiber_ratio_of_surjective
    {V U : Type*} [AddCommGroup V] [AddCommGroup U]
    [Module K V] [Module K U] [Fintype V] [Fintype U]
    (f : V →ₗ[K] U) (hf : Function.Surjective f) (b : U) :
    (Nat.card {x // f x = b} : ℝ) / Fintype.card V =
      (Fintype.card U : ℝ)⁻¹ := by
  rw [Nat.card_eq_fintype_card]
  have hc := card_fiber_mul_card_of_surjective f hf b
  have hU : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hV : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr : (Fintype.card {x // f x = b} : ℝ) * Fintype.card U = Fintype.card V := by
    exact_mod_cast hc
  field_simp
  nlinarith


variable [Fintype K] [Fintype ι]


lemma independent_joint_probability (v : ι → τ → K) (S : Finset ι)
    (h : LinearIndepOn K v (S : Set ι)) :
    vectorAverage (fun a : τ → K => if ∀ i ∈ S,
      (dotProductBilin K K a) (v i) = 0 then 1 else 0) =
        ((Fintype.card K : ℝ)^S.card)⁻¹ := by
  classical
  let W : Matrix S τ K := fun i => v i
  have hi : LinearIndependent K W.row := h
  have hf := fiber_ratio_of_surjective W.mulVecLin
    (mulVec_surjective_of_rowIndependent W hi) 0
  have he (a : τ → K) : W.mulVecLin a = 0 ↔
      ∀ i ∈ S, (dotProductBilin K K a) (v i) = 0 := by
    constructor
    · intro ha i hi
      change dotProduct a (v i) = 0
      rw [dotProduct_comm]
      exact congrFun ha ⟨i,hi⟩
    · intro ha
      ext i
      change dotProduct (v i) a = 0
      rw [dotProduct_comm]
      exact ha i i.property
  simp_rw [he] at hf
  rw [Nat.card_eq_fintype_card] at hf
  simpa [vectorAverage, Fintype.card_subtype, Finset.sum_ite] using hf



lemma vectorAverage_mono {K : Type*} [Field K] {τ : Type*} [Fintype τ] [Fintype K] {f g : (τ → K) → ℝ} (h : ∀ a, f a ≤ g a) :
    vectorAverage f ≤ vectorAverage g := by
  unfold vectorAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a))
    (Nat.cast_nonneg _)

lemma vectorAverage_sum {K : Type*} [Field K] {τ : Type*} [Fintype τ] [Fintype K] {Ω : Type*} (s : Finset Ω) (f : Ω → (τ → K) → ℝ) :
    vectorAverage (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, vectorAverage (f i) := by
  unfold vectorAverage
  rw [Finset.sum_comm, Finset.sum_div]

lemma vectorAverage_const_mul {K : Type*} [Field K] {τ : Type*} [Fintype τ] [Fintype K] (c : ℝ) (f : (τ → K) → ℝ) :
    vectorAverage (fun a => c * f a) = c * vectorAverage f := by
  unfold vectorAverage
  rw [←Finset.mul_sum]
  ring

lemma vectorAverage_zero {K : Type*} [Field K] {τ : Type*} [Fintype τ] [Fintype K] : vectorAverage (fun _ : τ → K => (0:ℝ)) = 0 := by
  simp [vectorAverage]

lemma nbcFaces_zero_eq {ι : Type*} {K : Type*} {V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Fintype ι] (v : ι → V) (L : V →ₗ[K] K) :
    nbcFaces (K := K) v (zeroFamily v L) =
      (nbcFaces (K := K) v Finset.univ).filter (fun S => ∀ i ∈ S, L (v i) = 0) := by
  classical
  ext S
  simp only [mem_nbcFaces, Finset.mem_filter, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨hS,hN⟩
    exact ⟨hN,fun i hi => mem_zeroFamily.mp (hS hi)⟩
  · rintro ⟨hN,hS⟩
    exact ⟨fun i hi => mem_zeroFamily.mpr (hS i hi),hN⟩

lemma nbcValue_eq (v : ι → V) (L : V →ₗ[K] K) (k : ℕ) :
    nbcValue v L k = ∑ S ∈ nbcFaces (K := K) v Finset.univ,
      if ∀ i ∈ S, L (v i) = 0 then
        (if S.card ≤ k then (-1:ℝ)^S.card else 0) else 0 := by
  rw [nbcValue, nbcFaces_zero_eq, Finset.sum_filter]



lemma average_nbcValue (v : ι → τ → K) (k : ℕ) :
    vectorAverage (fun a : τ → K => nbcValue v (dotProductBilin K K a) k) =
      nbcPolynomial (K := K) v ((Fintype.card K : ℝ)⁻¹) k := by
  simp_rw [nbcValue_eq]
  rw [vectorAverage_sum]
  unfold nbcPolynomial
  apply Finset.sum_congr rfl
  intro S hS
  have hN := (mem_nbcFaces.mp hS).2
  by_cases hc : S.card ≤ k
  · simp only [ite_eq_left hc]
    have he : (fun a : τ → K => if ∀ i ∈ S,
        (dotProductBilin K K a) (v i) = 0 then (-1:ℝ)^S.card else 0) =
        (fun a : τ → K => (-1:ℝ)^S.card *
          (if ∀ i ∈ S, (dotProductBilin K K a) (v i) = 0 then 1 else 0)) := by
      funext a
      split_ifs <;> simp
    rw [he, vectorAverage_const_mul,
      independent_joint_probability v S hN.linearIndepOn, inv_pow]
  · simp only [ite_eq_right hc, ite_self, vectorAverage_zero]



theorem average_avoidance_even_le (v : ι → τ → K) (q : ℕ) :
    vectorAverage (fun a : τ → K => avoidanceIndicator v (dotProductBilin K K a)) ≤
      nbcPolynomial (K := K) v ((Fintype.card K : ℝ)⁻¹) (2*q) := by
  rw [←average_nbcValue]
  exact vectorAverage_mono (fun a => nbc_even_bound v (dotProductBilin K K a) q)





end FiniteField
end SingleLatticeCovering.BrokenCircuit


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_BrokenCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

lemma mem_minimalObstructions {ι : Type*} [DecidableEq ι] {P : Finset ι → Prop} {A T : Finset ι} :
    T ∈ minimalObstructions P A ↔ T ⊆ A ∧ ¬P T ∧ ∀ U, U ⊂ T → P U := by
  classical
  simp [minimalObstructions]

lemma exists_minimalObstruction {P : Finset ι → Prop} {A S : Finset ι}
    (hS : S ⊆ A) (hP : ¬P S) :
    ∃ T ∈ minimalObstructions P A, T ⊆ S := by
  classical
  obtain ⟨T,hTS,hT,hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun T : Finset ι => ¬P T) S hP
  refine ⟨T, mem_minimalObstructions.mpr ⟨hTS.trans hS,hT,?_⟩,hTS⟩
  intro U hUT
  by_contra hn
  exact hUT.2 (hmin hn hUT.1)

lemma sum_powerset_pow_card {ι : Type*} [DecidableEq ι] (A : Finset ι) (t : ℝ) :
    ∑ S ∈ A.powerset, t^S.card = (1+t)^A.card := by
  simpa only [one_pow, mul_one, add_comm t 1] using
    (Finset.sum_pow_mul_eq_add_pow t (1:ℝ) A)


lemma sum_supersets_pow_card (A T : Finset ι) (hTA : T ⊆ A) (t : ℝ) :
    (∑ S ∈ A.powerset.filter (fun S => T ⊆ S), t^S.card) =
      t^T.card * (1+t)^(A.card-T.card) := by
  classical
  rw [←Finset.card_sdiff_of_subset hTA, ←sum_powerset_pow_card, Finset.mul_sum]
  apply Finset.sum_bij (fun S _ => S \ T)
  · intro S hS
    obtain ⟨hSA,hTS⟩ := Finset.mem_filter.mp hS
    apply Finset.mem_powerset.mpr
    exact Finset.sdiff_subset_sdiff_left T (Finset.mem_powerset.mp hSA)
  · intro S hS U hU he
    have hTS := (Finset.mem_filter.mp hS).2
    have hTU := (Finset.mem_filter.mp hU).2
    calc
      S = (S \ T) ∪ T := (Finset.sdiff_union_of_subset hTS).symm
      _ = (U \ T) ∪ T := congrArg (fun X => X ∪ T) he
      _ = U := Finset.sdiff_union_of_subset hTU
  · intro U hU
    have hUA := Finset.mem_powerset.mp hU
    refine ⟨U ∪ T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.union_subset (hUA.trans Finset.sdiff_subset) hTA),
      Finset.subset_union_right⟩, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨hx,hxn⟩ := Finset.mem_sdiff.mp hx
      exact (Finset.mem_union.mp hx).resolve_right hxn
    · intro hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl hx), (Finset.mem_sdiff.mp (hUA hx)).2⟩
  · intro S hS
    have hTS := (Finset.mem_filter.mp hS).2
    rw [←Finset.card_sdiff_add_card_eq_card hTS, pow_add, mul_comm]

attribute [local instance] Classical.propDecidable



theorem bad_subset_sum_le (P : Finset ι → Prop) (A : Finset ι) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ S ∈ A.powerset.filter (fun S => S.card ≤ k ∧ ¬P S), t^S.card) ≤
      (1+t)^A.card *
        ∑ T ∈ (minimalObstructions P A).filter (fun T => T.card ≤ k), t^T.card := by
  classical
  let F := (minimalObstructions P A).filter (fun T => T.card ≤ k)
  have hp (S : Finset ι) : 0 ≤ t^S.card := pow_nonneg ht _
  calc
    _ ≤ ∑ S ∈ A.powerset,
        ∑ T ∈ F, if T ⊆ S then t^S.card else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro S hS
      by_cases hb : S.card ≤ k ∧ ¬P S
      · rw [ite_eq_left hb]
        obtain ⟨T,hT,hTS⟩ := exists_minimalObstruction
          (Finset.mem_powerset.mp hS) hb.2
        have hTF : T ∈ F := Finset.mem_filter.mpr
          ⟨hT,(Finset.card_le_card hTS).trans hb.1⟩
        have hh := Finset.single_le_sum
          (fun U (_ : U ∈ F) => show 0 ≤ (if U ⊆ S then t^S.card else 0) by
            split_ifs <;> positivity) hTF
        simpa only [ite_eq_left hTS] using hh
      · rw [ite_eq_right hb]
        exact Finset.sum_nonneg (fun T _ => by split_ifs <;> positivity)
    _ = ∑ T ∈ F, t^T.card * (1+t)^(A.card-T.card) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      rw [←Finset.sum_filter, sum_supersets_pow_card]
      exact (mem_minimalObstructions.mp (Finset.mem_filter.mp hT).1).1
    _ ≤ ∑ T ∈ F, t^T.card * (1+t)^A.card := by
      apply Finset.sum_le_sum
      intro T hT
      apply mul_le_mul_of_nonneg_left _ (hp T)
      exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+t) (Nat.sub_le _ _)
    _ = _ := by rw [←Finset.sum_mul, mul_comm]




lemma unrestricted_polynomial_eq {ι : Type*} [DecidableEq ι] (A : Finset ι) (t : ℝ) (k : ℕ) :
    truncatedFacesPolynomial (fun _ => True) A t k = binomialPolynomial A.card t k := by
  unfold truncatedFacesPolynomial binomialPolynomial
  rw [Finset.filter_true, Finset.sum_powerset]
  have he (j : ℕ) : (∑ S ∈ Finset.powersetCard j A,
      if S.card ≤ k then (-1:ℝ)^S.card*t^S.card else 0) =
      (A.card.choose j) • (if j ≤ k then (-1:ℝ)^j*t^j else 0) :=
    Finset.sum_powersetCard j A (fun l => if l ≤ k then (-1:ℝ)^l*t^l else 0)
  simp_rw [he]
  simp only [nsmul_eq_mul, mul_ite, mul_zero]
  let f : ℕ → ℝ := fun j => if j ≤ k then (A.card.choose j : ℝ) *
    ((-1:ℝ)^j * t^j) else 0
  change (∑ j ∈ Finset.range (A.card+1), f j) = _
  have hsum : (∑ j ∈ Finset.range (A.card+1), f j) =
      ∑ j ∈ Finset.range (k+1), f j := by
    rcases le_total A.card k with h | h
    · apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h _))
      intro j hj hjn
      have hm : A.card < j := by simp only [Finset.mem_range] at hj hjn; omega
      simp [f, Nat.choose_eq_zero_of_lt hm]
    · symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h _))
      intro j hj hjn
      have hk : ¬j ≤ k := by simp only [Finset.mem_range] at hj hjn; omega
      simp [f,hk]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  have hk : j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  simp only [f,ite_eq_left hk,mul_assoc]

lemma truncated_defect_le_bad_sum (P : Finset ι → Prop) (A : Finset ι) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    |truncatedFacesPolynomial P A t k - binomialPolynomial A.card t k| ≤
      ∑ S ∈ A.powerset.filter (fun S => S.card ≤ k ∧ ¬P S), t^S.card := by
  rw [←unrestricted_polynomial_eq A t k]
  unfold truncatedFacesPolynomial
  rw [Finset.filter_true, Finset.sum_filter, ←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ S ∈ A.powerset,
        |(if P S then (if S.card ≤ k then (-1:ℝ)^S.card*t^S.card else 0) else 0) -
          (if S.card ≤ k then (-1:ℝ)^S.card*t^S.card else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hP : P S <;> by_cases hk : S.card ≤ k <;>
        simp [hP,hk,abs_mul,abs_pow,abs_of_nonneg (pow_nonneg ht S.card)]



theorem truncated_defect_le (P : Finset ι → Prop) (A : Finset ι) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    |truncatedFacesPolynomial P A t k - binomialPolynomial A.card t k| ≤
      (1+t)^A.card *
        ∑ T ∈ (minimalObstructions P A).filter (fun T => T.card ≤ k), t^T.card :=
  (truncated_defect_le_bad_sum P A k ht).trans (bad_subset_sum_le P A k ht)




end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
open Submodule
variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]


lemma minimalObstruction_linearIndepOn {v : ι → V} {A T : Finset ι}
    (hT : T ∈ minimalObstructions (NoBrokenCircuit (K := K) v) A) :
    LinearIndepOn K v (T : Set ι) := by
  have hproper := (mem_minimalObstructions.mp hT).2.2
  induction T using Finset.induction_on_min with
  | empty => simp
  | insert a S ha ih =>
    have han : a ∉ S := fun h => (lt_irrefl a (ha a h))
    have hS : NoBrokenCircuit (K := K) v S :=
      hproper S (Finset.ssubset_insert han)
    have hn : v a ∉ Submodule.span K (v '' (S : Set ι)) := by
      have he : S.filter (fun j => a < j) = S := Finset.filter_true_of_mem ha
      simpa only [Active, he] using hS a
    simpa only [Finset.coe_insert] using hS.linearIndepOn.insert hn



theorem minimalObstruction_has_circuit {v : ι → V} {A T : Finset ι}
    (hT : T ∈ minimalObstructions (NoBrokenCircuit (K := K) v) A) :
    ∃ e : ι, (∀ j ∈ T, e < j) ∧ ∃ c : T → K,
      (∀ i, c i ≠ 0) ∧ ∑ i, c i • v i = v e := by
  classical
  obtain ⟨hTA,hN,hproper⟩ := mem_minimalObstructions.mp hT
  simp only [NoBrokenCircuit, not_forall, not_not] at hN
  obtain ⟨e,he⟩ := hN
  have hf : T.filter (fun j => e < j) = T := by
    by_contra hn
    have hss : T.filter (fun j => e < j) ⊂ T :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,hn⟩
    apply hproper _ hss e
    simpa only [Active, Finset.filter_filter, and_self] using he
  have hlt : ∀ j ∈ T, e < j := by
    intro j hj
    have hm : j ∈ T.filter (fun j => e < j) := by rw [hf]; exact hj
    exact (Finset.mem_filter.mp hm).2
  have hm : v e ∈ Submodule.span K (v '' (T : Set ι)) := by
    simpa only [Active,hf] using he
  obtain ⟨c,hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun K).mp hm
  refine ⟨e,hlt,c,?_,hc⟩
  intro i hci
  have hiT : (T.erase i) ⊂ T := Finset.erase_ssubset i.property
  have hP := hproper (T.erase i) hiT
  apply hP e
  have hfe : (T.erase i).filter (fun j => e < j) = T.erase i :=
    Finset.filter_true_of_mem (fun j hj => hlt j (Finset.mem_of_mem_erase hj))
  change v e ∈ Submodule.span K (v '' (↑((T.erase i).filter (fun j => e < j)) : Set ι))
  rw [hfe, ←hc]
  apply Submodule.sum_mem
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [hci]
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h),j.property⟩,rfl⟩



end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι τ K : Type*} [LinearOrder ι] [Fintype ι] [Fintype τ] [Field K] [Fintype K]



lemma nbcPolynomial_defect_bound {ι : Type*} {τ : Type*} {K : Type*} [LinearOrder ι] [Fintype ι] [Fintype τ] [Field K] [Fintype K] (v : ι → τ → K) (k : ℕ) :
    |nbcPolynomial (K := K) v ((Fintype.card K : ℝ)⁻¹) k -
      binomialPolynomial (Fintype.card ι) ((Fintype.card K : ℝ)⁻¹) k| ≤
        finiteCircuitError v k := by
  simpa only [Finset.card_univ, nbcPolynomial, nbcFaces, truncatedFacesPolynomial, finiteCircuitError] using
    (truncated_defect_le (NoBrokenCircuit (K := K) v) Finset.univ k
      (show (0:ℝ) ≤ (Fintype.card K : ℝ)⁻¹ by positivity))




theorem finite_field_void_upper (v : ι → τ → K) (q : ℕ) :
    vectorAverage (fun a : τ → K => avoidanceIndicator v (dotProductBilin K K a)) ≤
      binomialPolynomial (Fintype.card ι) ((Fintype.card K : ℝ)⁻¹) (2*q) +
        finiteCircuitError v (2*q) := by
  have h1 := average_avoidance_even_le v q
  have h2 := (abs_le.mp (nbcPolynomial_defect_bound v (2*q))).2
  linarith



end
end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]
open Submodule
open scoped BigOperators



theorem minimalObstruction_circuit {v : ι → V} {A T : Finset ι}
    (hT : T ∈ minimalObstructions (NoBrokenCircuit (K := K) v) A) :
    ∃ e : ι, e ∉ T ∧ v e ∈ span K (v '' (T : Set ι)) ∧
      ∀ U : Finset ι, U ⊂ insert e T → LinearIndepOn K v (U : Set ι) := by
  classical
  obtain ⟨e,hlt,c,hc,hrel⟩ := minimalObstruction_has_circuit hT
  have he : e ∉ T := fun h => (lt_irrefl e (hlt e h))
  refine ⟨e,he,?_,?_⟩
  · rw [←hrel]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,i.property,rfl⟩)
  · intro U hU
    by_cases heU : e ∈ U
    · have hsub : U.erase e ⊆ T := by
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        exact (Finset.mem_insert.mp (hU.subset (Finset.mem_of_mem_erase hj))).resolve_left hji
      have hss : U.erase e ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
        intro h
        apply hU.ne
        rw [←h,Finset.insert_erase heU]⟩
      have hP := (mem_minimalObstructions.mp hT).2.2 _ hss
      have hfilter : (U.erase e).filter (fun j => e < j) = U.erase e :=
        Finset.filter_true_of_mem (fun j hj => hlt j (hsub hj))
      have hn : v e ∉ span K (v '' (U.erase e : Set ι)) := by
        simpa only [Active,hfilter] using hP e
      have hi := hP.linearIndepOn.insert hn
      simpa only [←Finset.coe_insert,Finset.insert_erase heU] using hi
    · apply (minimalObstruction_linearIndepOn hT).mono
      intro j hj
      exact (Finset.mem_insert.mp (hU.subset hj)).resolve_left (fun h => heU (h ▸ hj))


end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]
open Submodule



theorem enumerated_circuit {r : ℕ} {v : ι → V} {T : Finset ι} {e : ι}
    (he : e ∉ T) (hspan : v e ∈ span K (v '' (T : Set ι)))
    (hproper : ∀ U : Finset ι, U ⊂ insert e T → LinearIndepOn K v (U : Set ι))
    (b : Fin r ≃ T) :
    let w : Fin (r+1) → ι := Fin.cons e (fun i => (b i).val)
    Function.Injective w ∧ ¬LinearIndependent K (v ∘ w) ∧
      ∀ q : Equiv.Perm (Fin (r+1)),
        LinearIndependent K (fun i : Fin r => v (w (q i.succ))) := by
  classical
  dsimp only
  let w : Fin (r+1) → ι := Fin.cons e (fun i => (b i).val)
  have hw : Function.Injective w := by
    apply Fin.cons_injective_iff.mpr
    refine ⟨?_,Subtype.val_injective.comp b.injective⟩
    intro h
    obtain ⟨i,hi⟩ := h
    exact he (hi ▸ (b i).property)
  have hwmem (i) : w i ∈ insert e T := by
    refine Fin.cases (Finset.mem_insert_self _ _) (fun j => ?_) i
    exact Finset.mem_insert_of_mem (b j).property
  refine ⟨hw,?_,?_⟩
  · intro hli
    have hn := (linearIndependent_finSucc.mp hli).2
    apply hn
    change v e ∈ span K (Set.range (fun i => v ((b i).val)))
    have hr : Set.range (fun i => v ((b i).val)) = v '' (T : Set ι) := by
      ext y
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨b i,(b i).property,rfl⟩
      · rintro ⟨j,hj,rfl⟩
        obtain ⟨i,hi⟩ := b.surjective ⟨j,hj⟩
        exact ⟨i,congrArg (fun z : T => v z.val) hi⟩
    rwa [hr]
  · intro q
    let f : Fin r → ι := fun i => w (q i.succ)
    have hf : Function.Injective f := hw.comp (q.injective.comp (Fin.succ_injective r))
    let U := Finset.univ.image f
    have hsub : U ⊆ insert e T := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact hwmem _
    have hnot : w (q 0) ∉ U := by
      intro h
      obtain ⟨i,hi,hf⟩ := Finset.mem_image.mp h
      have heq := q.injective (hw hf)
      exact Fin.succ_ne_zero i heq
    have hss : U ⊂ insert e T := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
      intro h
      exact hnot (h ▸ hwmem (q 0))⟩
    let g : Fin r → (U : Set ι) := fun i => ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    have hg : Function.Injective g := fun i j h => hf (congrArg Subtype.val h)
    exact (hproper U hss).linearIndependent.comp g hg


end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.PrimeCircuit
open Matrix AffineCircuit CircuitEnumeration RogersPreparation BrokenCircuit
open scoped BigOperators

variable {d r p : ℕ} [Fact p.Prime]

lemma integerRows_bound {s d : ℕ} (x : Fin s → Fin d → ℤ) {B : ℕ} (hB : 1 ≤ B)
    (hx : ∀ i j, |x i j| ≤ (B:ℤ)) : ∀ i j, |integerRows x i j| ≤ (B:ℤ) := by
  intro i j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa [integerRows] using (show (1:ℤ) ≤ B by exact_mod_cast hB)
  · exact hx i j

lemma mapped_integerRows (x : Fin r → Fin d → ℤ) :
    ((integerRows x).map (fun z => (z:ZMod p))).row = fun i => homogeneousRow (p:=p) (x i) := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [integerRows,homogeneousRow]



theorem obstruction_factorial_count (S : Finset (Fin d → ℤ)) [LinearOrder S]
    {B : ℕ} (hB : 1 ≤ B) (hS : ∀ z ∈ S, ∀ j, |z j| ≤ (B:ℤ))
    (hp : (r+1).factorial*B^(r+1) < p) :
    let v : S → Fin (d+1) → ZMod p := fun z => homogeneousRow z.val
    let T := (minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
      (fun T => T.card = r)
    T.card*r.factorial ≤ (circuits S r).card := by
  classical
  dsimp only
  let v : S → Fin (d+1) → ZMod p := fun z => homogeneousRow z.val
  let T := (minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
    (fun T => T.card = r)
  have hT (U : T) : U.val ∈ minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ :=
    (Finset.mem_filter.mp U.property).1
  choose e he hspan hproper using fun U : T => minimalObstruction_circuit (hT U)
  apply factorial_count_le_map (B:=T) (fun U hU => (Finset.mem_filter.mp hU).2)
    e Subtype.val Subtype.val_injective (circuits S r)
  intro y
  let w : Fin (r+1) → S := orderedCircuit e y
  have hw := enumerated_circuit (he y.1) (hspan y.1) (hproper y.1) y.2
  have hwi : Function.Injective w := hw.1
  apply mem_circuits.mpr
  refine ⟨fun i => (w i).property, ?_⟩
  have hbnd : ∀ i j, |(w i).val j| ≤ (B:ℤ) := fun i j => hS _ (w i).property j
  refine ⟨?_,?_⟩
  · have hi := rowIndependent_mod_iff_rat p (integerRows (fun i => (w i).val))
      (integerRows_bound _ hB hbnd) hp
    rw [mapped_integerRows] at hi
    exact mt hi.mpr hw.2.1
  · intro q
    have hsmall : r.factorial*B^r < p :=
      lt_of_le_of_lt (Nat.mul_le_mul (Nat.factorial_le (by omega)) (Nat.pow_le_pow_right hB (by omega))) hp
    have hi := rowIndependent_mod_iff_rat p
      (integerRows (fun i => (w (q i.succ)).val))
      (integerRows_bound _ hB (fun i j => hbnd (q i.succ) j)) hsmall
    rw [mapped_integerRows] at hi
    exact hi.mp (hw.2.2 q)


end SingleLatticeCovering.PrimeCircuit

namespace SingleLatticeCovering.BrokenCircuit
open Submodule
variable {ι τ K : Type*} [LinearOrder ι] [Field K]


lemma minimalObstruction_two_le {v : ι → τ → K} {j : τ}
    (hv : ∀ i, v i j = 1) (hinj : Function.Injective v) {A T : Finset ι}
    (hT : T ∈ minimalObstructions (NoBrokenCircuit (K:=K) v) A) : 2 ≤ T.card := by
  classical
  obtain ⟨e,he,hspan,hproper⟩ := minimalObstruction_circuit hT
  by_contra hh
  have hc : T.card ≤ 1 := by omega
  obtain hzero | hone := Nat.le_one_iff_eq_zero_or_eq_one.mp hc
  · have hTe : T = ∅ := Finset.card_eq_zero.mp hzero
    rw [hTe,Finset.coe_empty,Set.image_empty,Submodule.span_empty,Submodule.mem_bot] at hspan
    have := congrFun hspan j
    simp [hv] at this
  · obtain ⟨i,hTi⟩ := Finset.card_eq_one.mp hone
    rw [hTi,Finset.coe_singleton,Set.image_singleton,Submodule.mem_span_singleton] at hspan
    obtain ⟨c,hc⟩ := hspan
    have hc1 : c = 1 := by simpa [hv] using congrFun hc j
    rw [hc1,one_smul] at hc
    exact he (by rw [hTi]; exact Finset.mem_singleton.mpr (hinj hc).symm)

end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.PrimeCircuit
open AffineCircuit BrokenCircuit RogersPreparation
variable {d p : ℕ} [Fact p.Prime]

lemma homogeneousRow_injective (S : Finset (Fin d → ℤ)) {B : ℕ}
    (hS : ∀ z ∈ S, ∀ j, |z j| ≤ (B:ℤ)) (hp : 2*B < p) :
    Function.Injective (fun z : S => homogeneousRow (p:=p) z.val) := by
  intro z w h
  apply Subtype.ext
  funext j
  have he := congrFun h j.succ
  change (z.val j:ZMod p) = (w.val j:ZMod p) at he
  have hz : (z.val j-w.val j).natAbs < p := by
    have hb : |z.val j-w.val j| ≤ (2*B:ℕ) :=
      (show |z.val j-w.val j| ≤ |z.val j|+|w.val j| by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (z.val j) 0 (w.val j)).trans (by simpa only [Nat.cast_mul,Nat.cast_ofNat,two_mul,Nat.cast_add] using add_le_add (hS _ z.property j) (hS _ w.property j))
    have hh : |z.val j-w.val j| < (p:ℤ) := hb.trans_lt (by exact_mod_cast hp)
    exact_mod_cast (show ((z.val j-w.val j).natAbs:ℤ) < p by rwa [Int.natCast_natAbs])
  apply sub_eq_zero.mp
  apply (intCast_eq_zero_small p hz).mp
  simpa only [Int.cast_sub,sub_eq_zero] using he

lemma obstruction_two_le (S : Finset (Fin d → ℤ)) [LinearOrder S] {B : ℕ}
    (hS : ∀ z ∈ S, ∀ j, |z j| ≤ (B:ℤ)) (hp : 2*B < p)
    {T : Finset S} (hT : T ∈ minimalObstructions
      (NoBrokenCircuit (K:=ZMod p) (fun z : S => homogeneousRow (p:=p) z.val)) Finset.univ) :
    2 ≤ T.card :=
  minimalObstruction_two_le (j:=0) (fun _ => rfl) (homogeneousRow_injective S hS hp) hT



end SingleLatticeCovering.PrimeCircuit

namespace SingleLatticeCovering.PrimeCircuit
open AffineCircuit BrokenCircuit
open scoped BigOperators
variable {d p k : ℕ} [Fact p.Prime]

lemma sum_pow_card_eq {ι : Type*} [DecidableEq ι] (T : Finset (Finset ι))
    (hT : ∀ U ∈ T, 2 ≤ U.card ∧ U.card ≤ k) (x : ℝ) :
    ∑ U ∈ T, x^U.card = ∑ r ∈ Finset.Icc 2 k, ((T.filter (fun U => U.card=r)).card:ℝ)*x^r := by
  rw [← Finset.sum_fiberwise_of_maps_to (s:=T) (t:=Finset.Icc 2 k) (g:=Finset.card)
    (fun U hU => Finset.mem_Icc.mpr (hT U hU)) (fun U => x^U.card)]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = ∑ U ∈ T.filter (fun U => U.card=r), x^r := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [(Finset.mem_filter.mp hU).2]
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]



theorem finiteCircuitError_le (S : Finset (Fin d → ℤ)) [LinearOrder S]
    {B : ℕ} (hB : 1 ≤ B) (hS : ∀ z ∈ S, ∀ j, |z j| ≤ (B:ℤ))
    (hp2 : 2*B < p) (hpk : (k+1).factorial*B^(k+1) < p) :
    finiteCircuitError (K:=ZMod p) (fun z : S => homogeneousRow (p:=p) z.val) k ≤
      (1+(p:ℝ)⁻¹)^S.card * ∑ r ∈ Finset.Icc 2 k,
        ((circuits S r).card:ℝ)/(p:ℝ)^r/(r.factorial:ℝ) := by
  classical
  let v : S → Fin (d+1) → ZMod p := fun z => homogeneousRow z.val
  let T := (minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
    (fun U => U.card ≤ k)
  have hcard : ∀ U ∈ T, 2 ≤ U.card ∧ U.card ≤ k := by
    intro U hU
    have hh := Finset.mem_filter.mp hU
    exact ⟨obstruction_two_le S hS hp2 hh.1,hh.2⟩
  change (1+(Fintype.card (ZMod p):ℝ)⁻¹)^(Fintype.card S)*
    (∑ U ∈ T, ((Fintype.card (ZMod p):ℝ)⁻¹)^U.card) ≤ _
  rw [ZMod.card,Fintype.card_coe,sum_pow_card_eq T hcard]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro r hr
  have hrk := (Finset.mem_Icc.mp hr).2
  have hp : (r+1).factorial*B^(r+1) < p :=
    lt_of_le_of_lt (Nat.mul_le_mul (Nat.factorial_le (by omega))
      (Nat.pow_le_pow_right hB (by omega))) hpk
  have hc := obstruction_factorial_count (r:=r) S hB hS hp
  dsimp only at hc
  have hfilter : T.filter (fun U => U.card=r) =
      (minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
        (fun U => U.card=r) := by
    ext U
    simp only [T,Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,h.2 ▸ hrk⟩,h.2⟩
  rw [hfilter]
  have hcR : ((((minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
      (fun U => U.card=r)).card:ℝ)*(r.factorial:ℝ)) ≤ (circuits S r).card := by
    exact_mod_cast hc
  apply (le_div_iff₀ (by exact_mod_cast r.factorial_pos : (0:ℝ)<(r.factorial:ℝ))).mpr
  rw [div_eq_mul_inv,←inv_pow]
  nlinarith [mul_le_mul_of_nonneg_right hcR (show (0:ℝ) ≤ ((p:ℝ)⁻¹)^r by positivity)]


end SingleLatticeCovering.PrimeCircuit

namespace SingleLatticeCovering.ConvexGrid
open FiniteKernel RealLatticeCount MeasureTheory Measure Filter
open scoped Topology Pointwise

lemma mem_integerGrid {d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    {t : ℝ} (ht : t ≠ 0) {z : Fin d → ℤ} :
    z ∈ integerGrid J hJ t ↔ scaledIntegerPoint t z ∈ J := by
  classical
  simp only [integerGrid,dite_eq_left ht,Set.Finite.mem_toFinset,gridSet,Set.mem_ofPred_eq]

lemma card_integerGrid {d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    {t : ℝ} (ht : t ≠ 0) :
    (integerGrid J hJ t).card = Nat.card ↥(J ∩ t⁻¹ • (integerLattice (Fin d) : Set (Fin d → ℝ))) := by
  classical
  let f : (integerGrid J hJ t) → ↥(J ∩ t⁻¹ • (integerLattice (Fin d) : Set (Fin d → ℝ))) :=
    fun z => ⟨scaledIntegerPoint t z.val,
      (mem_integerGrid hJ ht).mp z.property,
      ⟨fun j => (z.val j:ℝ),integerPoint_mem_lattice z.val,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w h
      exact Subtype.ext (scaledPoint_injective ht (congrArg Subtype.val h))
    · intro y
      obtain ⟨u,hu,hy⟩ := y.property.2
      let z := integerCoordinates (⟨u,hu⟩ : integerLattice (Fin d))
      have he : scaledIntegerPoint t z = y.val := by
        rw [←hy]
        ext j
        simp only [scaledIntegerPoint,Pi.smul_apply,smul_eq_mul]
        rw [integerCoordinates_cast]
      refine ⟨⟨z,(mem_integerGrid hJ ht).mpr (he ▸ y.property.1)⟩,?_⟩
      exact Subtype.ext he
  simpa only [Fintype.card_coe] using (Nat.card_eq_fintype_card (α:=integerGrid J hJ t)).symm.trans
    (Nat.card_congr (Equiv.ofBijective f hf))


theorem normalized_card_limit {d : ℕ} {J : Set (Fin d → ℝ)}
    (hJc : IsCompact J) (hJv : Convex ℝ J) (h0 : 0 ∈ J) :
    Tendsto (fun t : ℝ => ((integerGrid J hJc t).card:ℝ)/t^d) atTop (𝓝 (volume.real J)) := by
  have h := tendsto_convex_grid_count (integerLattice (Fin d)) hJc hJv h0
  simp only [Fintype.card_fin,integerLattice_covolume,div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [card_integerGrid hJc ht.ne']

lemma grid_uniform_bound {d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t, 1 ≤ t → ∀ z ∈ integerGrid J hJ t, ∀ j,
      |(z j:ℝ)| ≤ B*t := by
  obtain ⟨B,hBpos,hB⟩ := hJ.isBounded.exists_pos_norm_le
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro t ht z hz j
  have ht0 : 0 < t := by linarith
  have hmem := (mem_integerGrid hJ ht0.ne').mp hz
  have h := (norm_le_pi_norm (scaledIntegerPoint t z) j).trans (hB _ hmem)
  change |t⁻¹*(z j:ℝ)| ≤ B at h
  rw [abs_mul,abs_of_pos (inv_pos.mpr ht0)] at h
  have hh := mul_le_mul_of_nonneg_left h ht0.le
  rw [←mul_assoc,mul_inv_cancel₀ ht0.ne',one_mul] at hh
  exact hh.trans (by nlinarith [le_max_right (1:ℝ) B])



end SingleLatticeCovering.ConvexGrid





end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_PrimeGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.RogersPreparation
open Filter Topology

lemma eventually_const_mul_rpow_lt {a : ℝ} (ha : a<1) (A : ℝ) :
    ∀ᶠ p : ℕ in atTop, A * (p : ℝ)^a < p := by
  have ht : Tendsto (fun p : ℕ => A * (p : ℝ)^(a-1)) atTop (𝓝 0) := by
    have h : Tendsto (fun p : ℕ => (p : ℝ)^(a-1)) atTop (𝓝 0) := by
      have hcast : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def,neg_sub] using
        (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp hcast
    simpa only [mul_zero] using h.const_mul A
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop 1] with p hp hp1
  have hpR : (0:ℝ)<p := by exact_mod_cast hp1
  have he : (p : ℝ)^a = (p : ℝ)^(a-1)*(p : ℝ) := by
    calc
      _ = (p : ℝ)^((a-1)+1) := by congr 1; ring
      _ = (p : ℝ)^(a-1)*(p : ℝ)^(1:ℝ) := Real.rpow_add hpR _ _
      _ = _ := by rw [Real.rpow_one]
  rw [he,←mul_assoc]
  simpa only [one_mul] using mul_lt_mul_of_pos_right hp hpR

lemma eventually_subcritical_minor_bound {d k : ℕ} (hk : k<d) {C : ℝ} (hC : 1≤C) :
    ∀ᶠ p : ℕ in atTop,
      1 ≤ C * (p : ℝ)^((d : ℝ)⁻¹) ∧
      (k.factorial : ℝ) * (C * (p : ℝ)^((d : ℝ)⁻¹))^k < p := by
  have hd : (0:ℝ)<d := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  have ha : (d : ℝ)⁻¹*k<1 := by
    rw [mul_comm,←div_eq_mul_inv,div_lt_one hd]
    exact_mod_cast hk
  filter_upwards [eventually_const_mul_rpow_lt ha ((k.factorial : ℝ)*C^k),
    eventually_ge_atTop 1] with p hp hp1
  have hpR : (1:ℝ)≤p := by exact_mod_cast hp1
  constructor
  · exact one_le_mul_of_one_le_of_one_le hC
      (Real.one_le_rpow hpR (inv_nonneg.mpr hd.le))
  · rw [mul_pow,←Real.rpow_mul_natCast (by positivity : (0:ℝ)≤p),←mul_assoc]
    exact hp


end SingleLatticeCovering.RogersPreparation

namespace SingleLatticeCovering.ConvexGrid
open MeasureTheory Filter Topology RogersPreparation AffineCircuit
open scoped BigOperators

lemma primeScale_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (primeScale d) atTop atTop :=
  (tendsto_rpow_atTop (inv_pos.mpr (by exact_mod_cast hd))).comp tendsto_natCast_atTop_atTop

lemma primeScale_pos {d p : ℕ} (hp : 0 < p) : 0 < primeScale d p :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp) _

lemma primeScale_pow {d p : ℕ} (hd : 0 < d) : (primeScale d p)^d = p := by
  rw [primeScale,←Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ p),
    inv_mul_cancel₀ (by exact_mod_cast hd.ne' : (d:ℝ) ≠ 0),Real.rpow_one]

lemma primeScale_pow_mul {d p r : ℕ} (hd : 0 < d) : (primeScale d p)^(r*d) = (p:ℝ)^r := by
  rw [Nat.mul_comm r d,pow_mul,primeScale_pow hd]


lemma prime_grid_density {d : ℕ} (hd : 0 < d) {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (hconv : Convex ℝ J) (h0 : 0 ∈ J) :
    Tendsto (fun p : ℕ => ((integerGrid J hJ (primeScale d p)).card:ℝ)/(p:ℝ)) atTop
      (𝓝 (volume.real J)) := by
  simpa only [Function.comp_def,primeScale_pow hd] using
    (normalized_card_limit hJ hconv h0).comp (primeScale_tendsto hd)



lemma eventually_prime_grid_bound {d k : ℕ} (hk : k < d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    ∀ᶠ p : ℕ in atTop, ∃ B : ℕ, 1 ≤ B ∧
      (∀ z ∈ integerGrid J hJ (primeScale d p), ∀ j, |z j| ≤ (B:ℤ)) ∧
      k.factorial*B^k < p := by
  obtain ⟨C,hC,hbound⟩ := grid_uniform_bound hJ
  have h2C : 1 ≤ 2*C := by linarith
  filter_upwards [eventually_subcritical_minor_bound hk h2C,
    (primeScale_tendsto (by omega : 0 < d)).eventually (eventually_ge_atTop (1:ℝ))]
    with p hp ht
  let B : ℕ := ⌈C*primeScale d p⌉₊
  have hCt : 1 ≤ C*primeScale d p := one_le_mul_of_one_le_of_one_le hC ht
  have hB : (1:ℝ) ≤ B := hCt.trans (Nat.le_ceil _)
  have hBC : (B:ℝ) ≤ 2*C*primeScale d p := by
    have hh := (Nat.ceil_lt_add_one (by linarith : 0 ≤ C*primeScale d p)).le
    dsimp only [B]
    nlinarith
  refine ⟨B,by exact_mod_cast hB,?_,?_⟩
  · intro z hz j
    have hh := (hbound _ ht z hz j).trans (Nat.le_ceil _)
    exact_mod_cast hh
  · have hh : (k.factorial:ℝ)*(B:ℝ)^k < (p:ℝ) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg B) hBC k)
        (Nat.cast_nonneg _)).trans_lt hp.2
    exact_mod_cast hh



theorem eventually_prime_circuit_count_le {d r : ℕ} (hr : 0 < r) (hd : 2*(r+1) ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J) (h0 : 0 ∈ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      ((circuits (integerGrid J hJ (primeScale d p)) r).card:ℝ)/(p:ℝ)^r <
        (SimplexYoung.affineCircuitVolumeSum (r:=r) J).toReal+ε := by
  obtain ⟨B,hB,hbound⟩ := grid_uniform_bound hJ
  have hh := eventually_circuit_count_le hr hd hJ hconv h0 (integerGrid J hJ) hB hbound
    (fun t ht z hz => (mem_integerGrid hJ (by linarith : t ≠ 0)).mp hz) hε
  simpa only [primeScale_pow_mul (by omega : 0 < d)] using
    (primeScale_tendsto (by omega : 0 < d)).eventually hh




end SingleLatticeCovering.ConvexGrid


noncomputable section
namespace SingleLatticeCovering.GridProbability
open Filter Topology
open scoped BigOperators

lemma cardinality_tendsto_atTop {M : ℕ → ℕ} {V : ℝ} (hV : 0 < V)
    (hM : Tendsto (fun p => (M p:ℝ)/(p:ℝ)) atTop (𝓝 V)) :
    Tendsto (fun p => (M p:ℝ)) atTop atTop := by
  have hh := hM.pos_mul_atTop hV (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  exact div_mul_cancel₀ _ (by exact_mod_cast (show p ≠ 0 by omega))



lemma normalized_choose_tendsto {M : ℕ → ℕ} {V : ℝ} (hV : 0 < V)
    (hM : Tendsto (fun p => (M p:ℝ)/(p:ℝ)) atTop (𝓝 V)) (j : ℕ) :
    Tendsto (fun p => ((M p).choose j:ℝ)/(p:ℝ)^j) atTop
      (𝓝 (V^j/(j.factorial:ℝ))) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hinv : Tendsto (fun p : ℕ => (j:ℝ)/(p:ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero,div_eq_mul_inv,Pi.inv_apply] using
        (tendsto_natCast_atTop_atTop (R:=ℝ)).inv_tendsto_atTop.const_mul (j:ℝ)
    have ht := (ih.mul (hM.sub hinv)).div_const (j+1:ℝ)
    have hlim : (V^j/(j.factorial:ℝ))*(V-0)/(j+1:ℝ) = V^(j+1)/((j+1).factorial:ℝ) := by
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ,sub_zero]
      field_simp
    rw [hlim] at ht
    apply ht.congr'
    filter_upwards [(cardinality_tendsto_atTop hV hM).eventually (eventually_ge_atTop (j:ℝ)),
      eventually_ge_atTop 1] with p hpj hp1
    have hjM : j ≤ M p := by exact_mod_cast hpj
    have hc :
        (((M p).choose (j+1):ℕ):ℝ)*(j+1:ℝ) =
          (((M p).choose j:ℕ):ℝ)*((M p:ℝ)-(j:ℝ)) := by
      exact_mod_cast Nat.choose_succ_right_eq (M p) j
    have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hj0 : (j+1:ℝ) ≠ 0 := by positivity
    field_simp [hp0,hj0,pow_succ]
    rw [←hc,pow_succ]
    ring

lemma binomial_polynomial_limit {M : ℕ → ℕ} {V : ℝ} (hV : 0 < V)
    (hM : Tendsto (fun p => (M p:ℝ)/(p:ℝ)) atTop (𝓝 V)) (k : ℕ) :
    Tendsto (fun p => ∑ j ∈ Finset.range (k+1), ((M p).choose j:ℝ)*(-1:ℝ)^j*((p:ℝ)⁻¹)^j)
      atTop (𝓝 (∑ j ∈ Finset.range (k+1), (-1:ℝ)^j*V^j/(j.factorial:ℝ))) := by
  have hh := tendsto_finsetSum (Finset.range (k+1))
    (fun j hj => (normalized_choose_tendsto hV hM j).const_mul ((-1:ℝ)^j))
  simpa only [inv_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

lemma binomial_envelope_le_exp (M p : ℕ) :
    (1+(p:ℝ)⁻¹)^M ≤ Real.exp ((M:ℝ)/(p:ℝ)) := by
  calc
    _ ≤ (Real.exp ((p:ℝ)⁻¹))^M :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((p:ℝ)⁻¹)]) M
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1



lemma upper_envelope_limit {α : Type*} {l : Filter α} {f : α → ℝ} {C : ℝ}
    (hf : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, f x < C+ε) :
    Tendsto (fun x => max (f x) C) l (𝓝 C) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall (fun x => hb.trans_le (le_max_right _ _))
  · intro b hb
    filter_upwards [hf (b-C) (sub_pos.mpr hb)] with x hx
    exact max_lt (by linarith) hb




end SingleLatticeCovering.GridProbability

namespace SingleLatticeCovering.ConvexGrid
open MeasureTheory Filter Topology AffineCircuit GridProbability BrokenCircuit PrimeCircuit
open scoped BigOperators



theorem eventually_primeGridVoid_le {d q : ℕ} (hq : 0 < q)
    (hd : 2*(2*q+1) ≤ d) {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (hconv : Convex ℝ J) (h0 : 0 ∈ J)
    (hV : 0 < volume.real J) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      primeGridVoid J hJ p ≤
        (∑ j ∈ Finset.range (2*q+1), (-1:ℝ)^j*(volume.real J)^j/(j.factorial:ℝ)) +
          continuumCircuitError J (2*q)+ε := by
  classical
  let S (p : ℕ) := integerGrid J hJ (primeScale d p)
  let C (r : ℕ) := (SimplexYoung.affineCircuitVolumeSum (r:=r) J).toReal
  let U (p r : ℕ) := max (((circuits (S p) r).card:ℝ)/(p:ℝ)^r) (C r)
  have hU (r : ℕ) (hr : r ∈ Finset.Icc 2 (2*q)) :
      Tendsto (fun p => U p r) atTop (𝓝 (C r)) := by
    apply upper_envelope_limit
    intro δ hδ
    exact eventually_prime_circuit_count_le (by have := (Finset.mem_Icc.mp hr).1; omega)
      (by have := (Finset.mem_Icc.mp hr).2; omega) hJ hconv h0 hδ
  have hsum := tendsto_finsetSum (Finset.Icc 2 (2*q))
    (fun r hr => (hU r hr).div_const (r.factorial:ℝ))
  have hmass := prime_grid_density (by omega : 0 < d) hJ hconv h0
  have hlim := (binomial_polynomial_limit hV hmass (2*q)).add (((Real.continuous_exp.tendsto _).comp hmass).mul hsum)
  have hless :
      (∑ j ∈ Finset.range (2*q+1), (-1:ℝ)^j*(volume.real J)^j/(j.factorial:ℝ)) +
        Real.exp (volume.real J) * ∑ r ∈ Finset.Icc 2 (2*q), C r/(r.factorial:ℝ) <
      (∑ j ∈ Finset.range (2*q+1), (-1:ℝ)^j*(volume.real J)^j/(j.factorial:ℝ)) +
        continuumCircuitError J (2*q)+ε := by
    change _ + continuumCircuitError J (2*q) < _
    exact lt_add_of_pos_right _ hε
  have hevent := hlim.eventually (gt_mem_nhds hless)
  have hminor := eventually_prime_grid_bound (k:=2*q+1) (by omega) hJ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hevent.and hminor)
  refine ⟨N,?_⟩
  intro p hpPrime hpN
  obtain ⟨he,⟨B,hB,hSB,hpB⟩⟩ := hN p hpN
  let : LinearOrder (S p) := (Fintype.equivFin (S p)).linearOrder
  have hp2 : 2*B < p := by
    have hf : 2 ≤ (2*q+1).factorial := by
      simpa using (Nat.factorial_le (show 2 ≤ 2*q+1 by omega))
    have hb : B ≤ B^(2*q+1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ 2*q+1 by omega)
    exact (Nat.mul_le_mul hf hb).trans_lt hpB
  let v : S p → Fin (d+1) → ZMod p := fun z => homogeneousRow z.val
  have hfin := finite_field_void_upper v q
  simp only [ZMod.card,Fintype.card_coe] at hfin
  have herr := finiteCircuitError_le (k:=2*q) (S p) hB hSB hp2 hpB
  have hsn : 0 ≤ ∑ r ∈ Finset.Icc 2 (2*q),
      ((circuits (S p) r).card:ℝ)/(p:ℝ)^r/(r.factorial:ℝ) := by
    apply Finset.sum_nonneg
    intro r hr
    exact div_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)
  have hreplace : ∑ r ∈ Finset.Icc 2 (2*q),
      ((circuits (S p) r).card:ℝ)/(p:ℝ)^r/(r.factorial:ℝ) ≤
        ∑ r ∈ Finset.Icc 2 (2*q), U p r/(r.factorial:ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  have herr' := herr.trans ((mul_le_mul_of_nonneg_right (binomial_envelope_le_exp (S p).card p) hsn).trans
    (mul_le_mul_of_nonneg_left hreplace (Real.exp_pos _).le))
  exact (hfin.trans (add_le_add le_rfl herr')).trans he.le


end SingleLatticeCovering.ConvexGrid

namespace SingleLatticeCovering.SimplexYoung
open scoped BigOperators
lemma simplexConstant_sq_ratio {r : ℕ} (hr : 0 < r) :
    (simplexConstant r)^2 = ((r+1:ℕ):ℝ)^r / ((r:ℝ)^r * (r+1:ℕ)) := by
  have h : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  unfold simplexConstant
  rw [div_pow, ←pow_mul, mul_comm r 2, pow_mul, inv_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), inv_div, div_pow]
  ring

lemma simplexConstant_succ_sq {r : ℕ} (hr : 0 < r) :
    (simplexConstant (r+1))^2 = (simplexConstant r)^2 *
      (1 - 1 / (((r+1:ℕ):ℝ)^2))^r := by
  have h : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have h1 : ((r+1:ℕ):ℝ) ≠ 0 := by positivity
  have h2 : ((r+1+1:ℕ):ℝ) ≠ 0 := by positivity
  rw [simplexConstant_sq_ratio (by omega), simplexConstant_sq_ratio hr]
  have hc : (1 - 1 / (((r+1:ℕ):ℝ)^2)) = (r:ℝ) * (r+2) / (((r+1:ℕ):ℝ)^2) := by
    push_cast
    field_simp
    ring
  rw [hc, div_pow, mul_pow, pow_succ, pow_succ, ←pow_mul]
  push_cast
  rw [show 2*r=r+r by omega, pow_add]
  field_simp
  ring

lemma simplexConstant_succ_le {r : ℕ} (hr : 0 < r) :
    simplexConstant (r+1) ≤ simplexConstant r * Real.exp (-(r:ℝ)/(2*((r+1:ℕ):ℝ)^2)) := by
  have hbase : 0 ≤ 1 - 1 / (((r+1:ℕ):ℝ)^2) := by
    have h : (1:ℝ) ≤ (r+1:ℕ) := by exact_mod_cast (show 1 ≤ r+1 by omega)
    have hsq : (1:ℝ) ≤ ((r+1:ℕ):ℝ)^2 := by nlinarith
    have hi := (div_le_one (by positivity : (0:ℝ)<((r+1:ℕ):ℝ)^2)).mpr hsq
    linarith
  have hexp : (1 - 1 / (((r+1:ℕ):ℝ)^2))^r ≤ Real.exp (-(r:ℝ)/((r+1:ℕ):ℝ)^2) := by
    calc
      _ ≤ (Real.exp (-(1 / (((r+1:ℕ):ℝ)^2))))^r :=
        pow_le_pow_left₀ hbase (by linarith [Real.add_one_le_exp (-(1/(((r+1:ℕ):ℝ)^2)))]) r
      _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring
  apply (sq_le_sq₀ (simplexConstant_nonneg _) (mul_nonneg (simplexConstant_nonneg _) (Real.exp_pos _).le)).mp
  rw [simplexConstant_succ_sq hr, mul_pow, ←Real.exp_nat_mul]
  have he : (2:ℝ) * (-(r:ℝ)/(2*((r+1:ℕ):ℝ)^2)) = -(r:ℝ)/((r+1:ℕ):ℝ)^2 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  exact mul_le_mul_of_nonneg_left hexp (sq_nonneg _)



lemma circuitTerm_nonneg (d r : ℕ) {V : ℝ} (hV : 0 ≤ V) :
    0 ≤ circuitTerm d V r := by
  unfold circuitTerm
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (pow_nonneg (simplexConstant_nonneg _) _)) (pow_nonneg hV _)) (by positivity)

lemma circuitTerm_succ_le {d r : ℕ} (hr : 3 ≤ r) {V : ℝ}
    (hV : 0 ≤ V) (hVd : V ≤ (d:ℝ)/6) :
    circuitTerm d V (r+1) ≤ (3/4:ℝ) * circuitTerm d V r := by
  have hr0 : 0 < r := by omega
  have hden : (0:ℝ) < (r+1:ℕ) := by positivity
  have hgeo := pow_le_pow_left₀ (simplexConstant_nonneg _) (simplexConstant_succ_le hr0) d
  rw [mul_pow, ←Real.exp_nat_mul] at hgeo
  have hexp : -(d:ℝ) * (r:ℝ)/(2*((r+1:ℕ):ℝ)^2) ≤
      -(3:ℝ)/8 * ((d:ℝ)/(r+1:ℕ)) := by
    have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*((r+1:ℕ):ℝ)^2)).mpr
    have he : (-(3:ℝ)/8 * ((d:ℝ)/(r+1:ℕ))) * (2*((r+1:ℕ):ℝ)^2) =
        -(3:ℝ)/4 * (d:ℝ) * ((r+1:ℕ):ℝ) := by field_simp; ring
    rw [he]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0:ℝ)≤d) (sub_nonneg.mpr hrR)]
  have heq : (d:ℝ) * (-(r:ℝ)/(2*((r+1:ℕ):ℝ)^2)) =
      -(d:ℝ) * (r:ℝ)/(2*((r+1:ℕ):ℝ)^2) := by ring
  rw [heq] at hgeo
  have hgeo' := hgeo.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexp) (pow_nonneg (simplexConstant_nonneg _) _))
  have hb : (4*V/(r+1:ℕ))*Real.exp (-(3:ℝ)/8*((d:ℝ)/(r+1:ℕ))) ≤ 3/4 := by
    have ht := Real.mul_exp_neg_le_exp_neg_one ((3:ℝ)/8*((d:ℝ)/(r+1:ℕ)))
    have he : Real.exp (-1) ≤ (27/64:ℝ) := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith [Real.exp_one_gt_d9]
    calc
      _ ≤ ((2:ℝ)/3*((d:ℝ)/(r+1:ℕ)))*Real.exp (-(3:ℝ)/8*((d:ℝ)/(r+1:ℕ))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply (div_le_iff₀ hden).mpr
        have heq : ((2:ℝ)/3*((d:ℝ)/(r+1:ℕ)))*((r+1:ℕ):ℝ) = (2:ℝ)/3*d := by field_simp
        rw [heq]
        linarith
      _ = (16/9:ℝ)*(((3:ℝ)/8*((d:ℝ)/(r+1:ℕ)))*
          Real.exp (-((3:ℝ)/8*((d:ℝ)/(r+1:ℕ))))) := by
        rw [show -(3:ℝ)/8*((d:ℝ)/(r+1:ℕ)) = -((3:ℝ)/8*((d:ℝ)/(r+1:ℕ))) by ring]
        ring
      _ ≤ (16/9:ℝ)*Real.exp (-1) := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ ≤ 3/4 := by linarith
  unfold circuitTerm
  rw [pow_succ, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ((4:ℝ)^r*4) * ((simplexConstant r)^d *
        Real.exp (-(3:ℝ)/8*((d:ℝ)/(r+1:ℕ)))) * (V^r*V) /
        (((r:ℝ)+1)*(r.factorial:ℝ)) := by gcongr
    _ = ((4*V/(r+1:ℕ))*Real.exp (-(3:ℝ)/8*((d:ℝ)/(r+1:ℕ)))) *
        ((4:ℝ)^r*(simplexConstant r)^d*V^r/(r.factorial:ℝ)) := by push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (circuitTerm_nonneg d r hV)


lemma circuitTerm_add_three_le {d : ℕ} {V : ℝ} (hV : 0 ≤ V)
    (hVd : V ≤ (d:ℝ)/6) (s : ℕ) :
    circuitTerm d V (s+3) ≤ (3/4:ℝ)^s * circuitTerm d V 3 := by
  induction s with
  | zero => simp
  | succ s ih =>
    calc
      _ ≤ (3/4:ℝ) * circuitTerm d V (s+3) := circuitTerm_succ_le (by omega) hV hVd
      _ ≤ (3/4:ℝ) * ((3/4:ℝ)^s * circuitTerm d V 3) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring



theorem tsum_circuitTerm_le {d : ℕ} {V : ℝ} (hV : 0 ≤ V)
    (hVd : V ≤ (d:ℝ)/6) :
    ∑' s : ℕ, ENNReal.ofReal (circuitTerm d V (s+3)) ≤
      ENNReal.ofReal (4 * circuitTerm d V 3) := by
  calc
    _ ≤ ∑' s : ℕ, ENNReal.ofReal ((3/4:ℝ)^s * circuitTerm d V 3) :=
      ENNReal.tsum_le_tsum (fun s => ENNReal.ofReal_le_ofReal (circuitTerm_add_three_le hV hVd s))
    _ = ENNReal.ofReal (4 * circuitTerm d V 3) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun s => mul_nonneg (by positivity)
        (circuitTerm_nonneg _ _ hV))
        ((summable_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖ < 1)).mul_right _)]
      rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖ < 1)]
      norm_num




end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
lemma sharpParallelogramConstant_pos : 0 < (4 * (Real.sqrt 3)⁻¹^3 : ℝ) := by positivity

lemma sharpParallelogramConstant_sq : (4 * (Real.sqrt 3)⁻¹^3 : ℝ)^2 = 16/27 := by
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  calc
    _ = 16 / (Real.sqrt 3)^6 := by field_simp; ring
    _ = _ := by rw [show 6 = 2*3 from rfl, pow_mul, hs]; norm_num

lemma sharpParallelogramConstant_exp (d : ℕ) :
    (4 * (Real.sqrt 3)⁻¹^3 : ℝ)^d =
      Real.exp (-(d:ℝ)/2 * Real.log (27/16:ℝ)) := by
  have hp := sharpParallelogramConstant_pos
  have hlog := congrArg Real.log sharpParallelogramConstant_sq
  rw [Real.log_pow] at hlog
  have hi : Real.log (16/27:ℝ) = -Real.log (27/16:ℝ) := by
    rw [← Real.log_inv]; norm_num
  rw [hi] at hlog
  rw [← Real.exp_log hp, ← Real.exp_nat_mul]
  congr 1
  push_cast at hlog
  nlinarith


lemma sourceLog_le_one : Real.log (27/16:ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<27/16)
  linarith

lemma sourceEta_le_dim {d : ℕ} (hd : 1 ≤ d) : sourceEta d ≤ d := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hl : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg hdR
  have hx := sourceLog_le_one
  dsimp [sourceEta]
  nlinarith


lemma log_27_16_le : Real.log (27/16 : ℝ)≤8/15 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ)<27/16)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤8/15) 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith

lemma sourceEta_le_linear (d : ℕ) : sourceEta d≤(2/15 : ℝ)*d := by
  have h := mul_le_mul_of_nonneg_left log_27_16_le (show (0 : ℝ)≤(d : ℝ)/4 by positivity)
  have hlog := Real.log_natCast_nonneg d
  unfold sourceEta
  nlinarith


lemma simplexConstant_three : simplexConstant 3 = 4 * (Real.sqrt 3)⁻¹^3 := by
  unfold simplexConstant
  norm_num [Real.sqrt_div, div_pow]
  ring

lemma circuitTerm_three_source {d : ℕ} (hd : 1 ≤ d) {V : ℝ}
    (hV : 0 ≤ V) (hVeta : V ≤ sourceEta d) :
    Real.exp V * (4 * circuitTerm d V 3) ≤ (128/3:ℝ) * Real.exp (-sourceEta d) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hVd := hVeta.trans (sourceEta_le_dim hd)
  have hpow : V^3 ≤ (d:ℝ)^3 := pow_le_pow_left₀ hV hVd _
  have h : Real.exp V * ((4*(Real.sqrt 3)⁻¹^3:ℝ)^d * V^3) ≤ Real.exp (-sourceEta d) := by
    rw [sharpParallelogramConstant_exp]
    calc
      _ ≤ Real.exp V * (Real.exp (-(d:ℝ)/2*Real.log (27/16:ℝ)) * (d:ℝ)^3) := by gcongr
      _ = Real.exp (V-(d:ℝ)/2*Real.log (27/16:ℝ)+3*Real.log (d:ℝ)) := by
        have he : (d:ℝ)^3 = Real.exp (3*Real.log (d:ℝ)) := by
          simpa only [Nat.cast_ofNat, Real.exp_log hdR] using (Real.exp_nat_mul (Real.log (d:ℝ)) 3).symm
        rw [he, ←Real.exp_add, ←Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hl := Real.log_nonneg (show (1:ℝ)≤d by exact_mod_cast hd)
        dsimp [sourceEta] at hVeta ⊢
        linarith
  unfold circuitTerm
  rw [simplexConstant_three]
  norm_num only [show (4:ℝ)^3=64 by norm_num, show ((3:ℕ).factorial:ℝ)=6 by norm_num]
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤128/3)
  calc
    _ = (128/3:ℝ) * (Real.exp V * ((4*(Real.sqrt 3)⁻¹^3:ℝ)^d * V^3)) := by ring
    _ ≤ _ := hh




end SingleLatticeCovering.SimplexYoung




noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Finset Set
open scoped BigOperators

lemma poissonPartial_zero (k : ℕ) : poissonPartial 0 k=1 := by
  unfold poissonPartial
  rw [sum_range_succ']
  simp

lemma taylor_exp_neg_eq {u : ℝ} (hu : 0 < u) (k : ℕ) :
    taylorWithinEval Real.exp k (uIcc 0 (-u)) 0 (-u)=poissonPartial u k := by
  have hne : (0 : ℝ)≠-u := by linarith
  have hd (j : ℕ) : iteratedDerivWithin j Real.exp (uIcc 0 (-u)) 0=1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      Real.contDiff_exp.contDiffAt (left_mem_uIcc),iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp,Real.exp_zero]
  rw [taylor_within_apply]
  unfold poissonPartial
  apply Finset.sum_congr rfl
  intro j hj
  rw [hd]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]


theorem poissonPartial_error {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    |poissonPartial u k-Real.exp (-u)| ≤ u^(k+1)/(k+1).factorial := by
  rcases hu.eq_or_lt with he | hu
  · subst u
    simp [poissonPartial_zero]
  have hne : (0 : ℝ)≠-u := by linarith
  obtain ⟨c,hc,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := k) hne
    Real.contDiff_exp.contDiffOn
  rw [taylor_exp_neg_eq hu k,iteratedDeriv_eq_iterate,Real.iter_deriv_exp,sub_zero] at he
  have hc0 : c ≤ 0 := by
    have h := hc.2
    simpa only [max_eq_left (neg_nonpos.mpr hu.le)] using h.le
  have hec : Real.exp c ≤ 1 := by simpa using Real.exp_le_exp.mpr hc0
  rw [abs_sub_comm,he,abs_div,abs_mul,abs_pow,abs_neg,abs_of_nonneg hu.le,
    abs_of_pos (Real.exp_pos c),abs_of_nonneg (by positivity : (0 : ℝ)≤(k+1).factorial)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_of_le_one_left (by positivity) hec



theorem poissonPartial_upper {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    poissonPartial u k ≤ Real.exp (-u)+u^(k+1)/(k+1).factorial := by
  have := le_trans (le_abs_self (poissonPartial u k-Real.exp (-u)))
    (poissonPartial_error hu k)
  linarith


end SingleLatticeCovering.RogersPreparation

namespace SingleLatticeCovering.SimplexYoung
open scoped BigOperators
lemma log_four_thirds_ge : (2/7 : ℝ)≤Real.log (4/3 : ℝ) := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ)<4/3)).mpr
  have h := Real.exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ)≤2/7)
    (by norm_num : (2/7 : ℝ)<2)
  norm_num at h ⊢
  exact h

lemma log_three_quarters_le : Real.log (3/4 : ℝ)≤-(2/7 : ℝ) := by
  have he : (3/4 : ℝ)=(4/3 : ℝ)⁻¹ := by norm_num
  rw [he,Real.log_inv]
  linarith [log_four_thirds_ge]

lemma factorial_quotient_chernoff {u : ℝ} (hu : 0≤u) {q : ℕ} (hq : 0<q) :
    u^q/(q.factorial : ℝ)≤(Real.exp 1*u/(q : ℝ))^q := by
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have h := Real.pow_div_factorial_le_exp (q : ℝ) (Nat.cast_nonneg q : (0 : ℝ)≤q) q
  calc
    _ = (u/(q : ℝ))^q*((q : ℝ)^q/(q.factorial : ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ (u/(q : ℝ))^q*Real.exp (q : ℝ) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg (div_nonneg hu hqR.le) _)
    _ = _ := by
      have he : Real.exp (q : ℝ) = Real.exp 1 ^ q := by
        simp
      rw [he, div_pow, div_pow, mul_pow]
      ring



theorem poisson_remainder_circuitCutoff {d : ℕ} (hd : 270≤d) {u : ℝ}
    (hu : 0≤u) (huη : u ≤ sourceEta d) :
    u^(2*(d/4-1)+1)/((2*(d/4-1)+1).factorial : ℝ)≤Real.exp (-sourceEta d) := by
  let q := 2*(d/4-1)+1
  have hq : 0<q := by dsimp [q]; omega
  have hdR : (270 : ℝ)≤d := by exact_mod_cast hd
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hqlo : (d : ℝ)/2-3≤q := by
    have hfloor : d≤4*(d/4)+3 := by omega
    have hcast : (d : ℝ)≤4*(d/4 : ℕ)+3 := by exact_mod_cast hfloor
    have hf : 1 ≤ d/4 := by omega
    simp only [q,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hf,Nat.cast_one]
    linarith
  have hqratio : (22/45 : ℝ)*d≤q := by linarith
  have hqexponent : (7/15 : ℝ)*d≤q := by linarith
  have hue : u≤(2/15 : ℝ)*d := huη.trans (sourceEta_le_linear d)
  have he : Real.exp 1≤(11/4 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hratio : Real.exp 1*u/(q : ℝ)≤(3/4 : ℝ) := by
    apply (div_le_iff₀ hqR).mpr
    have hc := mul_le_mul_of_nonneg_right he hu
    nlinarith
  have hlog : (q : ℝ)*Real.log (3/4 : ℝ)≤-(2/15 : ℝ)*d := by
    have h := mul_le_mul_of_nonneg_left log_three_quarters_le hqR.le
    linarith
  change u^q/(q.factorial : ℝ)≤_
  calc
    _ ≤ (Real.exp 1*u/(q : ℝ))^q := factorial_quotient_chernoff hu hq
    _ ≤ (3/4 : ℝ)^q := pow_le_pow_left₀ (by positivity) hratio q
    _ = Real.exp ((q : ℝ)*Real.log (3/4 : ℝ)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<3/4)]
    _ ≤ Real.exp (-(2/15 : ℝ)*d) := Real.exp_le_exp.mpr hlog
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [sourceEta_le_linear d])


end SingleLatticeCovering.SimplexYoung


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped BigOperators

lemma affineCircuitVolumeSum_le_rational {r d : ℕ} (J : Set (Fin d → ℝ)) :
    affineCircuitVolumeSum (r:=r) J ≤ rationalCircuitVolumeSum (r:=r) J := by
  apply ENNReal.tsum_le_tsum
  intro a
  split_ifs <;> simp

lemma affineCircuit_real_term {r d : ℕ} (hr : 0 < r) (hd : 2*(r+1) ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    (affineCircuitVolumeSum (r:=r) J).toReal / (r.factorial:ℝ) ≤
      4*circuitTerm d (volume.real J) r := by
  have hb := (affineCircuitVolumeSum_le_rational (r:=r) J).trans
    (rationalCircuitVolumeSum_le hr hd hJ)
  have hbr := ENNReal.toReal_mono (by simp) hb
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (mul_nonneg (by positivity) (pow_nonneg (simplexConstant_nonneg r) d))
    (pow_nonneg ENNReal.toReal_nonneg r))] at hbr
  apply (div_le_div_of_nonneg_right hbr (by positivity)).trans_eq
  unfold circuitTerm
  rw [pow_succ,measureReal_def]
  ring

lemma finite_circuitTerm_series_le {d k : ℕ} {V : ℝ}
    (hV : 0 ≤ V) (hVd : V ≤ (d:ℝ)/6) :
    ∑ r ∈ Finset.Icc 3 k, circuitTerm d V r ≤ 4*circuitTerm d V 3 := by
  have hh : (∑ r ∈ Finset.Icc 3 k, ENNReal.ofReal (circuitTerm d V r)) ≤
      ∑' s : ℕ, ENNReal.ofReal (circuitTerm d V (s+3)) := by
    rw [←Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm] using
      (ENNReal.sum_le_tsum (Finset.range (k+1-3))
        (f:=fun s : ℕ => ENNReal.ofReal (circuitTerm d V (s+3))))
  have hb := hh.trans (tsum_circuitTerm_le hV hVd)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => circuitTerm_nonneg _ _ hV)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) (circuitTerm_nonneg _ _ hV))).mp hb

lemma rank_two_source {d : ℕ} (hd : 6 ≤ d) {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (hVeta : volume.real J ≤ sourceEta d) :
    Real.exp (volume.real J) * ((affineCircuitVolumeSum (r:=2) J).toReal/2) ≤
      128 * Real.exp (-sourceEta d) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hV := measureReal_nonneg (μ:=volume) (s:=J)
  have hVd := hVeta.trans (sourceEta_le_dim (by omega))
  have hpow : (volume.real J)^2 ≤ (d:ℝ)^3 := by
    have hh := pow_le_pow_left₀ hV hVd 2
    have hs : (d:ℝ)^2 ≤ (d:ℝ)^3 := by nlinarith [sq_nonneg (d:ℝ)]
    exact hh.trans hs
  have hb := affineRankTwoCircuitVolumeSum_le hd hJ
  have hbr := ENNReal.toReal_mono (by simp) hb
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg (simplexConstant_nonneg 3) d)) (sq_nonneg _))] at hbr
  have hs : Real.exp (volume.real J) * ((simplexConstant 3)^d * (volume.real J)^2) ≤
      Real.exp (-sourceEta d) := by
    rw [simplexConstant_three,sharpParallelogramConstant_exp]
    calc
      _ ≤ Real.exp (volume.real J) * (Real.exp (-(d:ℝ)/2*Real.log (27/16:ℝ)) * (d:ℝ)^3) := by gcongr
      _ = Real.exp (volume.real J-(d:ℝ)/2*Real.log (27/16:ℝ)+3*Real.log (d:ℝ)) := by
        have he : (d:ℝ)^3 = Real.exp (3*Real.log (d:ℝ)) := by
          simpa only [Nat.cast_ofNat,Real.exp_log hdR] using (Real.exp_nat_mul (Real.log (d:ℝ)) 3).symm
        rw [he,←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hl := Real.log_nonneg hd1
        dsimp [sourceEta] at hVeta ⊢
        linarith
  have hh := mul_le_mul_of_nonneg_left hbr (Real.exp_pos (volume.real J)).le
  change Real.exp (volume.real J) * (affineCircuitVolumeSum (r:=2) J).toReal ≤
    Real.exp (volume.real J) * (256*(simplexConstant 3)^d*(volume.real J)^2) at hh
  nlinarith only [hh,hs]




theorem continuum_circuit_error_source {d k : ℕ} (hk : 2 ≤ k)
    (hd : 2*(k+1) ≤ d) {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (hVeta : volume.real J ≤ sourceEta d) :
    Real.exp (volume.real J) * (∑ r ∈ Finset.Icc 2 k,
      (affineCircuitVolumeSum (r:=r) J).toReal/(r.factorial:ℝ)) ≤
        (896/3:ℝ)*Real.exp (-sourceEta d) := by
  classical
  have hV := measureReal_nonneg (μ:=volume) (s:=J)
  have hVd : volume.real J ≤ (d:ℝ)/6 := by
    have hh := hVeta.trans (sourceEta_le_linear d)
    nlinarith [(Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hsum : (∑ r ∈ Finset.Icc 3 k,
      (affineCircuitVolumeSum (r:=r) J).toReal/(r.factorial:ℝ)) ≤
        4*(4*circuitTerm d (volume.real J) 3) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc 3 k, 4*circuitTerm d (volume.real J) r := by
        apply Finset.sum_le_sum
        intro r hr
        obtain ⟨hr3,hrk⟩ := Finset.mem_Icc.mp hr
        exact affineCircuit_real_term (by omega) (by omega) hJ
      _ = 4*(∑ r ∈ Finset.Icc 3 k, circuitTerm d (volume.real J) r) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_circuitTerm_series_le hV hVd) (by norm_num)
  have hs := circuitTerm_three_source (by omega : 1 ≤ d) hV hVeta
  have htwo := rank_two_source (by omega : 6 ≤ d) hJ hVeta
  have he : Finset.Icc 2 k = insert 2 (Finset.Icc 3 k) := by ext r; simp only [Finset.mem_Icc,Finset.mem_insert]; omega
  rw [he,Finset.sum_insert (by simp),show ((2:ℕ).factorial:ℝ)=2 by norm_num,mul_add]
  have hh := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (volume.real J)).le
  linarith



end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.ConvexGrid
open MeasureTheory SimplexYoung RogersPreparation


theorem eventually_primeGridVoid_source {d : ℕ} (hd : 270 ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (h0 : 0 ∈ J) (hV : 0 < volume.real J) (hVeta : volume.real J ≤ sourceEta d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      primeGridVoid J hJ p ≤ Real.exp (-volume.real J)+300*Real.exp (-sourceEta d)+ε := by
  have hq : 0 < d/4-1 := by omega
  have hdq : 2*(2*(d/4-1)+1) ≤ d := by omega
  obtain ⟨N,hN⟩ := eventually_primeGridVoid_le hq hdq hJ hconv h0 hV hε
  refine ⟨N,fun p hp hpN => ?_⟩
  have hb := hN p hpN
  have hc := continuum_circuit_error_source (by omega : 2 ≤ 2*(d/4-1)) hdq hJ hVeta
  have hr := poisson_remainder_circuitCutoff hd hV.le hVeta
  have ht := poissonPartial_upper hV.le (2*(d/4-1))
  have heq : poissonPartial (volume.real J) (2*(d/4-1)) =
      ∑ j ∈ Finset.range (2*(d/4-1)+1), (-1:ℝ)^j*(volume.real J)^j/(j.factorial:ℝ) := by
    unfold poissonPartial
    apply Finset.sum_congr rfl
    intro j hj
    rw [show -volume.real J=(-1:ℝ)*volume.real J by ring,mul_pow]
  rw [heq] at ht
  change continuumCircuitError J (2*(d/4-1)) ≤ _ at hc
  linarith [Real.exp_pos (-sourceEta d)]

end SingleLatticeCovering.ConvexGrid








section











section

noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Horizontal Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise BigOperators

lemma cell_fundamental {m : ℕ} (L : FullLattice m) :
    IsAddFundamentalDomain L.module (cell L) volume :=
  ZLattice.isAddFundamentalDomain (IsZLattice.basis L.module) volume

lemma cell_volume_ne_zero {m : ℕ} (L : FullLattice m) : volume (cell L)≠0 :=
  ZSpan.measure_fundamentalDomain_ne_zero _

lemma cell_volume_ne_top {m : ℕ} (L : FullLattice m) : volume (cell L)≠⊤ :=
  (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne

lemma measurable_periodize {m : ℕ} (L : FullLattice m)
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) : Measurable (periodize L f) := by
  exact Measurable.tsum (fun z => hf.comp (measurable_id.add measurable_const))


instance translateLaw_probability {m : ℕ} (L : FullLattice m) :
    IsProbabilityMeasure (translateLaw L) where
  measure_univ := by
    simp only [translateLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (cell_volume_ne_zero L) (cell_volume_ne_top L)

lemma pointCount_eq_zero {m : ℕ} (L : FullLattice m) (J : Set (Fin m → ℝ))
    (x : Fin m → ℝ) : pointCount L J x=0 ↔ latticeProjection L.module x ∉
      latticeProjection L.module '' J := by
  classical
  rw [pointCount,periodize,ENNReal.tsum_eq_zero]
  constructor
  · intro h ⟨y,hy,hxy⟩
    have hz : y-x ∈ L.module := (latticeProjection_eq_zero_iff L.module _).mp (by
      rw [map_sub,hxy,sub_self])
    have hh := h ⟨y-x,hz⟩
    have he : x+(y-x)=y := by abel
    simp only [he,Set.indicator_of_mem hy,Pi.one_apply,one_ne_zero] at hh
  · intro hx z
    apply Set.indicator_of_notMem
    intro hz
    apply hx
    refine ⟨x+z,hz,?_⟩
    rw [map_add,(latticeProjection_eq_zero_iff L.module _).mpr z.property,add_zero]



end SingleLatticeCovering.RogersPreparation

end
end

section

noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Horizontal Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise BigOperators

lemma integral_periodic_shift {m : ℕ} (L : FullLattice m)
    (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : ∀ (z : L.module) x, f (z+x)=f x) (a : Fin m → ℝ) :
    ∫⁻ x in cell L, f (a+x) = ∫⁻ x in cell L, f x := by
  rw [(measurePreserving_add_left volume a).setLIntegral_comp_emb
    (measurableEmbedding_addLeft a) f (cell L)]
  apply IsAddFundamentalDomain.setLIntegral_eq _ (cell_fundamental L) f hf
  exact (cell_fundamental L).vadd_of_comm a

lemma integral_torus_shift {m : ℕ} (L : FullLattice m)
    (f : Torus m → ℝ≥0∞) (t : Torus m) :
    ∫⁻ x, f (t+latticeProjection L.module x) ∂translateLaw L =
      ∫⁻ x, f (latticeProjection L.module x) ∂translateLaw L := by
  obtain ⟨a,rfl⟩ := latticeProjection_surjective L.module t
  simp only [translateLaw,lintegral_smul_measure]
  congr 1
  simp only [←map_add]
  exact integral_periodic_shift L (fun y => f (latticeProjection L.module y)) (by
    intro z x
    rw [map_add,(latticeProjection_eq_zero_iff L.module _).mpr z.property,zero_add]) a



lemma translateLaw_preserving {m : ℕ} (L : FullLattice m) :
    MeasurePreserving (latticeProjection L.module) (translateLaw L) (torusMeasure m) := by
  let p := latticeProjection L.module
  have hp : Measurable p := p.continuous.measurable
  let ν := (translateLaw L).map p
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hp.aemeasurable
  have hν : ν.IsAddLeftInvariant := by
    constructor
    intro t
    apply Measure.ext_of_lintegral ν
    intro g hg
    have ht : Measurable (fun y : Torus m => t+y) := measurable_const.add measurable_id
    rw [lintegral_map hg ht]
    change (∫⁻ y, g (t+y) ∂(translateLaw L).map p)=∫⁻ y, g y ∂(translateLaw L).map p
    calc
      _ = ∫⁻ x, g (t+p x) ∂translateLaw L := by
        exact lintegral_map (f := fun y => g (t+y)) (g := p) (μ := translateLaw L)
          (hg.comp ht) hp
      _ = ∫⁻ x, g (p x) ∂translateLaw L := integral_torus_shift L g t
      _ = _ := (lintegral_map hg hp).symm
  refine ⟨hp,?_⟩
  have h := Measure.addHaarMeasure_unique ν (⊤ : TopologicalSpace.PositiveCompacts (Torus m))
  simpa only [TopologicalSpace.PositiveCompacts.coe_top,measure_univ,one_smul,torusMeasure] using h

lemma hole_eq_zero_count_probability {m : ℕ} (L : FullLattice m)
    {J : Set (Fin m → ℝ)} (hJ : IsCompact J) :
    L.hole J=translateLaw L {x | pointCount L J x=0} := by
  unfold FullLattice.hole
  have hm : MeasurableSet ((latticeProjection L.module '' J)ᶜ) :=
    (hJ.image (latticeProjection L.module).continuous).measurableSet.compl
  rw [←(translateLaw_preserving L).measure_preimage hm.nullMeasurableSet]
  congr 1
  ext x
  exact (pointCount_eq_zero L J x).symm



end SingleLatticeCovering.RogersPreparation

end
end




noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.PrimeKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma basis_repr (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (x : ι → ℝ) (j : ι) :
    (basis p hp i a).repr x j =
      Function.update x i ((x i+tailForm i a x)/p) j := by
  simp [basis, Basis.ofEquivFun_repr_apply,coordinates]


lemma integer_mem_iff_dvd (p : ℕ) (hp : 0 < p) (i : ι) (a z : ι → ℤ) :
    (fun j => (z j : ℝ)) ∈ lattice p hp i a ↔
      (p : ℤ) ∣ z i+∑ j ∈ Finset.univ.erase i, a j*z j := by
  rw [lattice,(basis p hp i a).mem_span_iff_repr_mem ℤ]
  simp only [basis_repr]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · intro h
    obtain ⟨q,hq⟩ := h i
    have hqi : (q : ℝ) = ((z i : ℝ)+tailForm i a (fun j => (z j : ℝ)))/p := by
      simpa only [Function.update_self, algebraMap_int_eq,Int.coe_castRingHom] using hq
    refine ⟨q,?_⟩
    have he := (eq_div_iff hpR).mp hqi
    exact_mod_cast (show (z i : ℝ)+∑ j ∈ Finset.univ.erase i,
      (a j : ℝ)*(z j : ℝ)=(p : ℝ)*q by simpa [tailForm,mul_comm] using he.symm)
  · rintro ⟨q,hq⟩ j
    by_cases hji : j=i
    · subst j
      refine ⟨q,?_⟩
      simp only [Function.update_self]
      apply (eq_div_iff hpR).mpr
      have hr : (z i : ℝ)+∑ j ∈ Finset.univ.erase i,
          (a j : ℝ)*(z j : ℝ)=(p : ℝ)*q := by exact_mod_cast hq
      simpa [tailForm,mul_comm] using hr.symm
    · exact ⟨z j,by simp [Function.update_of_ne hji]⟩


lemma exists_integer_of_mem (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ)
    {x : ι → ℝ} (hx : x ∈ lattice p hp i a) :
    ∃ z : ι → ℤ, (fun j => (z j : ℝ)) = x := by
  have h := ((basis p hp i a).mem_span_iff_repr_mem ℤ x).mp hx
  choose q hq using h
  have hc : coordinates p hp i a x = (fun j => (q j : ℝ)) := by
    ext j
    simpa only [basis,Basis.ofEquivFun_repr_apply,algebraMap_int_eq,Int.coe_castRingHom] using (hq j).symm
  let z : ι → ℤ := Function.update q i ((p : ℤ)*q i-∑ j ∈ Finset.univ.erase i, a j*q j)
  refine ⟨z,?_⟩
  have he : (fun j => (z j : ℝ)) = (coordinates p hp i a).symm (fun j => (q j : ℝ)) := by
    ext j
    by_cases hji : j=i
    · subst j
      simp [z,coordinates,tailForm]
    · simp [z,coordinates,Function.update_of_ne hji]
  rw [he,←hc,LinearEquiv.symm_apply_apply]

lemma mem_lattice_iff (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (x : ι → ℝ) :
    x ∈ lattice p hp i a ↔ ∃ z : ι → ℤ, (fun j => (z j : ℝ)) = x ∧
      (p : ℤ) ∣ z i+∑ j ∈ Finset.univ.erase i, a j*z j := by
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := exists_integer_of_mem p hp i a hx
    exact ⟨z,hz,(integer_mem_iff_dvd p hp i a z).mp (hz.symm ▸ hx)⟩
  · rintro ⟨z,rfl,hz⟩
    exact (integer_mem_iff_dvd p hp i a z).mpr hz

lemma integer_mem_iff_congruence (p : ℕ) (hp : 0 < p) (i : ι) (a z : ι → ℤ) :
    (fun j => (z j : ℝ)) ∈ lattice p hp i a ↔
      (z i : ZMod p)+∑ j ∈ Finset.univ.erase i, (a j : ZMod p)*(z j : ZMod p)=0 := by
  rw [integer_mem_iff_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add,Int.cast_sum,Int.cast_mul]





end SingleLatticeCovering.PrimeKernel




end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_PrimeKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.PrimeKernel
open LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalizeEquiv_det (p : ℕ) (hp : 0 < p) (i : ι) :
    LinearMap.det (normalizeEquiv (ι := ι) p hp).toLinearMap=(p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
  change LinearMap.det (scaleFactor (ι := ι) p • (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))=_
  rw [LinearMap.det_smul,LinearMap.det_id,mul_one,Module.finrank_pi]
  rw [scaleFactor,←Real.rpow_natCast,←Real.rpow_mul hpR.le]
  have he : -(Fintype.card ι : ℝ)⁻¹*(Fintype.card ι : ℝ) = -1 := by field_simp
  rw [he,Real.rpow_neg_one]

lemma grid_mem_normalized_iff (p : ℕ) (hp : 0 < p) (i : ι) (a z : ι → ℤ) :
    gridMap p hp z ∈ normalized p hp i a ↔ modForm p i a z=0 := by
  change (normalizeEquiv p hp) (fun j => (z j : ℝ)) ∈
    image (lattice p hp i a) (normalizeEquiv p hp) ↔ _
  change (normalizeEquiv p hp).symm ((normalizeEquiv p hp) (fun j => (z j : ℝ))) ∈ lattice p hp i a ↔ _
  rw [LinearEquiv.symm_apply_apply,integer_mem_iff_congruence]
  rfl



end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



lemma mem_rectangularCell_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (i : ι) (x : ι → ℝ) :
    x ∈ rectangularCell p i ↔ ∀ j, 0 ≤ x j ∧ x j < (if j=i then (p:ℝ) else 1) := by
  simp [rectangularCell,Set.mem_pi]

lemma rectangularCell_measurable (p : ℕ) (i : ι) : MeasurableSet (rectangularCell p i) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

lemma integer_displacement_unique {p : ℕ} (hp : 0 < p) (i : ι)
    (a : ι → ℤ) {x y : ι → ℝ} (hx : x ∈ rectangularCell p i)
    (hy : y ∈ rectangularCell p i) (hxy : x-y ∈ lattice p hp i a) : x=y := by
  obtain ⟨z,hz,hdiv⟩ := (mem_lattice_iff p hp i a (x-y)).mp hxy
  have hzj : ∀ j, (z j:ℝ)=x j-y j := fun j => congrFun hz j
  have hxx := (mem_rectangularCell_iff p i x).mp hx
  have hyy := (mem_rectangularCell_iff p i y).mp hy
  have htail (j : ι) (hj : j ≠ i) : z j=0 := by
    have hxj := hxx j
    have hyj := hyy j
    rw [ite_eq_right hj] at hxj hyj
    have hlow : (-1:ℝ) < z j := by linarith [hzj j]
    have hupp : (z j:ℝ) < 1 := by linarith [hzj j]
    have hlowZ : (-1:ℤ) < z j := by exact_mod_cast hlow
    have huppZ : z j < 1 := by exact_mod_cast hupp
    omega
  have hsum : ∑ j ∈ Finset.univ.erase i, a j*z j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [htail j (Finset.mem_erase.mp hj).1,mul_zero]
  rw [hsum,add_zero] at hdiv
  obtain ⟨q,hq⟩ := hdiv
  have hxi := hxx i
  have hyi := hyy i
  simp at hxi hyi
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hzq : (z i:ℝ)=(p:ℝ)*(q:ℝ) := by exact_mod_cast hq
  have hqlo : (-1:ℝ) < q := by nlinarith [hzj i]
  have hqhi : (q:ℝ) < 1 := by nlinarith [hzj i]
  have hqloZ : (-1:ℤ) < q := by exact_mod_cast hqlo
  have hqhiZ : q < 1 := by exact_mod_cast hqhi
  have hq0 : q=0 := by omega
  have hzi : z i=0 := by rw [hq,hq0,mul_zero]
  ext j
  by_cases hj : j=i
  · subst j
    have hh := hzj i
    rw [hzi,Int.cast_zero] at hh
    linarith
  · have hh := hzj j
    rw [htail j hj,Int.cast_zero] at hh
    linarith

lemma rectangularCell_exists_shift (p : ℕ) (hp : 0 < p) (i : ι)
    (a : ι → ℤ) (x : ι → ℝ) :
    ∃ g : lattice p hp i a, (g:ι → ℝ)+x ∈ rectangularCell p i := by
  let f : ι → ℤ := fun j => ⌊x j⌋
  let T : ℤ := f i+∑ j ∈ Finset.univ.erase i, a j*f j
  let b : ℤ := T % (p:ℤ)
  let z : ι → ℤ := Function.update (-f) i (-f i+b)
  have hb0 : 0 ≤ b := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have hbp : b < (p:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  have hzj (j : ι) (hj : j ≠ i) : z j = -f j := by simp [z,Function.update_of_ne hj]
  have hzi : z i = -f i+b := by simp [z]
  have hzlat : (fun j => (z j:ℝ)) ∈ lattice p hp i a := by
    apply (integer_mem_iff_dvd p hp i a z).mpr
    have hs : ∑ j ∈ Finset.univ.erase i, a j*z j = -(∑ j ∈ Finset.univ.erase i, a j*f j) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hzj j (Finset.mem_erase.mp hj).1,mul_neg]
    rw [hzi,hs]
    have he : -f i+b-(∑ j ∈ Finset.univ.erase i, a j*f j) = -(T-b) := by dsimp [T]; ring
    change (p:ℤ) ∣ -f i+b-(∑ j ∈ Finset.univ.erase i, a j*f j)
    rw [he]
    apply dvd_neg.mpr
    exact Int.dvd_self_sub_emod
  refine ⟨⟨fun j => (z j:ℝ),hzlat⟩,?_⟩
  rw [mem_rectangularCell_iff]
  intro j
  have hflo := Int.floor_le (x j)
  have hfhi := Int.lt_floor_add_one (x j)
  change 0 ≤ (z j:ℝ)+x j ∧ (z j:ℝ)+x j < _
  change (f j:ℝ) ≤ x j at hflo
  change x j < (f j:ℝ)+1 at hfhi
  by_cases hj : j=i
  · subst j
    rw [hzi,Int.cast_add,Int.cast_neg,ite_eq_left rfl]
    have hbR : (0:ℝ)≤b := by exact_mod_cast hb0
    have hbpR : (b:ℝ)+1≤p := by exact_mod_cast (show b+1≤(p:ℤ) by omega)
    constructor <;> linarith
  · rw [hzj j hj,Int.cast_neg,ite_eq_right hj]
    constructor <;> linarith

lemma rectangularCell_fundamental (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    IsAddFundamentalDomain (lattice p hp i a) (rectangularCell p i) volume := by
  apply IsAddFundamentalDomain.mk' (rectangularCell_measurable p i).nullMeasurableSet
  intro x
  obtain ⟨g,hg⟩ := rectangularCell_exists_shift p hp i a x
  refine ⟨g,hg,?_⟩
  intro h hh
  apply Subtype.ext
  have he := integer_displacement_unique hp i a hh hg (by
    change ((h:ι → ℝ)+x)-((g:ι → ℝ)+x) ∈ lattice p hp i a
    simpa only [add_sub_add_right_eq_sub] using (lattice p hp i a).sub_mem h.property g.property)
  exact add_right_cancel he


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalizedRectangularCell_fundamental (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    IsAddFundamentalDomain (normalized p hp i a) (normalizedRectangularCell p hp i) volume := by
  let e := normalizeEquiv (ι:=ι) p hp
  let eg : normalized p hp i a ≃ lattice p hp i a :=
    { toFun := fun x => ⟨e.symm x,x.property⟩
      invFun := fun x => ⟨e x,by change e.symm (e x) ∈ lattice p hp i a; simp⟩
      left_inv := fun x => by apply Subtype.ext; exact e.apply_symm_apply x
      right_inv := fun x => by apply Subtype.ext; exact e.symm_apply_apply x }
  have he : LinearMap.det e.symm.toLinearMap ≠ 0 := (LinearEquiv.isUnit_det' e.symm).ne_zero
  have hf := Measure.LinearMap.quasiMeasurePreserving volume e.symm.toLinearMap he
  apply (rectangularCell_fundamental p hp i a).image_of_equiv e.toEquiv hf eg
  intro g x
  change e ((e.symm (g:ι → ℝ))+x)=(g:ι → ℝ)+e x
  rw [map_add,e.apply_symm_apply]

lemma volume_rectangularCell (p : ℕ) (i : ι) : volume (rectangularCell p i)=(p:ℝ≥0∞) := by
  classical
  rw [rectangularCell,volume_pi,Measure.pi_pi]
  simp only [Real.volume_Ico,sub_zero]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

lemma volume_normalizedRectangularCell (p : ℕ) (hp : 0 < p) (i : ι) :
    volume (normalizedRectangularCell p hp i)=1 := by
  change volume ((normalizeEquiv (ι:=ι) p hp).toContinuousLinearEquiv '' rectangularCell p i)=1
  rw [Measure.addHaar_image_continuousLinearEquiv]
  change ENNReal.ofReal |LinearMap.det (normalizeEquiv (ι:=ι) p hp).toLinearMap| * volume (rectangularCell p i)=1
  rw [normalizeEquiv_det p hp i,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),volume_rectangularCell]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp),ENNReal.ofReal_natCast]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne') (by simp)



end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma volume_gridUnitCell {ι : Type*} [Fintype ι] [DecidableEq ι] : volume (gridUnitCell (ι:=ι))=1 := by
  rw [gridUnitCell,volume_pi,Measure.pi_pi]
  simp

lemma volume_offsetCell (p : ℕ) (hp : 0 < p) (i : ι) (b : Fin p) :
    volume (offsetCell p hp i b)=(p:ℝ≥0∞)⁻¹ := by
  change volume ((normalizeEquiv (ι:=ι) p hp).toContinuousLinearEquiv '' _)=_
  rw [Measure.addHaar_image_continuousLinearEquiv]
  change ENNReal.ofReal |LinearMap.det (normalizeEquiv (ι:=ι) p hp).toLinearMap| * volume _ = _
  rw [normalizeEquiv_det p hp i,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),
    measure_vadd,volume_gridUnitCell,mul_one,ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp),
    ENNReal.ofReal_natCast]

lemma rectangularCell_unit_decomposition (p : ℕ) (hp : 0 < p) (i : ι)
    {x : ι → ℝ} (hx : x ∈ rectangularCell p i) :
    ∃ b : Fin p, ∃ u ∈ gridUnitCell, x=(fun j => ((offsetVector i b.val j:ℤ):ℝ))+u := by
  have _ := hp
  have hxj := (mem_rectangularCell_iff p i x).mp hx
  have hxi : 0 ≤ x i ∧ x i < (p:ℝ) := by simpa using hxj i
  let q : ℤ := ⌊x i⌋
  have hq0 : 0 ≤ q := Int.floor_nonneg.mpr hxi.1
  have hqp : q < (p:ℤ) := Int.floor_lt.mpr hxi.2
  let b : Fin p := ⟨q.toNat,by omega⟩
  have hbq : (b.val:ℤ)=q := Int.toNat_of_nonneg hq0
  let o : ι → ℝ := fun j => ((offsetVector i b.val j:ℤ):ℝ)
  refine ⟨b,x-o,?_,by dsimp [o]; abel⟩
  rw [gridUnitCell,Set.mem_pi]
  intro j hj
  change 0 ≤ x j-o j ∧ x j-o j < 1
  by_cases hji : j=i
  · subst j
    have hoi : o i=(q:ℝ) := by simp [o,offsetVector,hbq]
    rw [hoi]
    have hl := Int.floor_le (x i)
    have hu := Int.lt_floor_add_one (x i)
    change (q:ℝ) ≤ x i at hl
    change x i < (q:ℝ)+1 at hu
    constructor <;> linarith
  · have hoj : o j=0 := by simp [o,offsetVector,Pi.single_eq_of_ne hji]
    rw [hoj,sub_zero]
    simpa [hji] using hxj j

lemma normalizedRectangularCell_subset_offsetCells (p : ℕ) (hp : 0 < p) (i : ι) :
    normalizedRectangularCell p hp i ⊆ ⋃ b : Fin p, offsetCell p hp i b := by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨b,u,hu,he⟩ := rectangularCell_unit_decomposition p hp i hx
  apply Set.mem_iUnion.mpr
  refine ⟨b,?_⟩
  apply Set.mem_image_of_mem
  exact ⟨u,hu,he.symm⟩

lemma modForm_offsetVector (p : ℕ) (i : ι) (a : ι → ℤ) (b : ℤ) :
    modForm p i a (offsetVector i b)=(b:ZMod p) := by
  change ((offsetVector i b i:ℤ):ZMod p)+∑ j ∈ Finset.univ.erase i,
    (a j:ZMod p)*((offsetVector i b j:ℤ):ZMod p)=_
  have hs : ∑ j ∈ Finset.univ.erase i, (a j:ZMod p)*((offsetVector i b j:ℤ):ZMod p)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [offsetVector,Pi.single_eq_of_ne (Finset.mem_erase.mp hj).1]
  rw [hs,add_zero]
  simp [offsetVector]



lemma offsetCell_hit (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ)
    (S : Finset (ι → ℤ)) {J : Set (ι → ℝ)}
    (hthick : ∀ z ∈ S, ∀ u ∈ gridUnitCell, gridMap p hp z + normalizeEquiv p hp u ∈ J)
    (b : Fin p) (hb : ∃ z ∈ S, modForm p i a z=(b.val:ZMod p))
    {x : ι → ℝ} (hx : x ∈ offsetCell p hp i b) :
    ∃ l : normalized p hp i a, x+l ∈ J := by
  obtain ⟨z,hz,hzb⟩ := hb
  obtain ⟨y,⟨u,hu,rfl⟩,rfl⟩ := hx
  let w := z-offsetVector i b.val
  have hw : gridMap p hp w ∈ normalized p hp i a := by
    rw [grid_mem_normalized_iff]
    dsimp [w]
    rw [map_sub,modForm_offsetVector,hzb]
    simp
  refine ⟨⟨gridMap p hp w,hw⟩,?_⟩
  have hh := hthick z hz u hu
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  change normalizeEquiv p hp ((fun j => ((offsetVector i b.val j:ℤ):ℝ))+u)+
    normalizeEquiv p hp (fun j => (w j:ℝ)) =
      normalizeEquiv p hp (fun j => (z j:ℝ))+normalizeEquiv p hp u
  rw [←map_add,←map_add]
  apply congrArg (normalizeEquiv p hp)
  ext j
  simp only [Pi.add_apply,w,Pi.sub_apply,Int.cast_sub]
  ring


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cell_hole_le_badOffsets (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ)
    (S : Finset (ι → ℤ)) {J : Set (ι → ℝ)}
    (hthick : ∀ z ∈ S, ∀ u ∈ gridUnitCell, gridMap p hp z + normalizeEquiv p hp u ∈ J) :
    volume (normalizedRectangularCell p hp i ∩ {x | ∀ l : normalized p hp i a, x+l ∉ J}) ≤
      ((badOffsets p i a S).card:ℝ≥0∞)/(p:ℝ≥0∞) := by
  classical
  have hsub : normalizedRectangularCell p hp i ∩ {x | ∀ l : normalized p hp i a, x+l ∉ J} ⊆
      ⋃ b ∈ badOffsets p i a S, offsetCell p hp i b := by
    rintro x ⟨hx,hmiss⟩
    obtain ⟨b,hb⟩ := Set.mem_iUnion.mp (normalizedRectangularCell_subset_offsetCells p hp i hx)
    have hbad : b ∈ badOffsets p i a S := by
      simp only [badOffsets,Finset.mem_filter,Finset.mem_univ,true_and]
      intro z hz hzb
      obtain ⟨l,hl⟩ := offsetCell_hit p hp i a S hthick b ⟨z,hz,hzb⟩ hb
      exact hmiss l hl
    exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hbad,hb⟩⟩
  calc
    _ ≤ volume (⋃ b ∈ badOffsets p i a S, offsetCell p hp i b) := measure_mono hsub
    _ ≤ ∑ b ∈ badOffsets p i a S, volume (offsetCell p hp i b) := measure_biUnion_finset_le _ _
    _ = _ := by simp [volume_offsetCell,div_eq_mul_inv]

end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.RogersPreparation
open Horizontal Completion Set MeasureTheory
open scoped Pointwise ENNReal

lemma pointCount_zero_iff_no_hit {d : ℕ} (L : FullLattice d)
    (J : Set (Fin d → ℝ)) (x : Fin d → ℝ) :
    pointCount L J x=0 ↔ ∀ l : L.module, x+l ∉ J := by
  classical
  simp only [pointCount,periodize,ENNReal.tsum_eq_zero]
  apply forall_congr'
  intro l
  by_cases h : x+l ∈ J <;> simp [h]



lemma hole_eq_unit_fundamental_hole {d : ℕ} (L : FullLattice d)
    {J F : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (hF : IsAddFundamentalDomain L.module F volume) (hvol : volume F=1) :
    L.hole J=volume (F ∩ {x | ∀ l : L.module, x+l ∉ J}) := by
  let H : Set (Fin d → ℝ) := {x | pointCount L J x=0}
  have hH : MeasurableSet H := (measurable_periodize L (measurable_one.indicator hJ.measurableSet)) (.singleton 0)
  have hperiodic (l : L.module) : (fun x => (l:Fin d → ℝ)+x) ⁻¹' H=H := by
    ext x
    change pointCount L J ((l:Fin d → ℝ)+x)=0 ↔ pointCount L J x=0
    rw [pointCount_eq_zero,pointCount_eq_zero,map_add,
      (latticeProjection_eq_zero_iff L.module _).mpr l.property,zero_add]
  have hv : volume (cell L)=1 := (cell_fundamental L).measure_eq hF |>.trans hvol
  rw [hole_eq_zero_count_probability L hJ,translateLaw,hv,inv_one,one_smul,
    Measure.restrict_apply hH]
  change volume (H ∩ cell L)=_
  rw [(cell_fundamental L).measure_set_eq hF hH hperiodic]
  congr 1
  ext x
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,H,pointCount_zero_iff_no_hit,and_comm]

end SingleLatticeCovering.RogersPreparation

namespace SingleLatticeCovering.PrimeKernel
open RogersPreparation Horizontal Set MeasureTheory
open scoped Pointwise ENNReal
variable {d : ℕ}

lemma normalizedFull_hole_le_badOffsets (p : ℕ) (hp : 0 < p) (i : Fin d) (a : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (hthick : ∀ z ∈ S, ∀ u ∈ gridUnitCell, gridMap p hp z + normalizeEquiv p hp u ∈ J) :
    (normalizedFull p hp i a).hole J ≤ ((badOffsets p i a S).card:ℝ≥0∞)/(p:ℝ≥0∞) := by
  rw [hole_eq_unit_fundamental_hole (normalizedFull p hp i a) hJ
    (normalizedRectangularCell_fundamental p hp i a) (volume_normalizedRectangularCell p hp i)]
  exact cell_hole_le_badOffsets p hp i a S hthick

end SingleLatticeCovering.PrimeKernel


noncomputable section
namespace SingleLatticeCovering.AffineVoid
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {n : ℕ} {σ : Type*} [Fintype σ]

lemma fullMiss_nonneg {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ} {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) (w : Fin (n+2) → K) :
    0 ≤ fullMiss v w := by
  classical
  unfold fullMiss
  split_ifs <;> norm_num

lemma normalDual_injective {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ} : Function.Injective
    (fun t : Kˣ × K × (Fin n → K) => normalDual t.1 t.2.1 t.2.2) := by
  rintro ⟨c,b,a⟩ ⟨c',b',a'⟩ he
  have hc : (c:K)=(c':K) := by
    have h := congrFun he ((0:Fin (n+1)).succ)
    simpa [normalDual] using h
  have hcc : c=c' := Units.ext hc
  subst c'
  have hb : b=b' := by
    have h := congrFun he 0
    simp only [normalDual,Fin.cons_zero] at h
    exact mul_left_cancel₀ (neg_ne_zero.mpr c.ne_zero) h
  have ha : a=a' := by
    funext j
    have h := congrFun he j.succ.succ
    simp only [normalDual,Fin.cons_succ] at h
    exact mul_left_cancel₀ c.ne_zero h
  subst b'; subst a'; rfl

lemma normalDual_dot {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ} (c : Kˣ) (b : K) (a : Fin n → K) (z : Fin (n+1) → K) :
    (∑ j, normalDual c b a j * (Fin.cons (1:K) z : Fin (n+2) → K) j) =
      (c:K)*(z 0+∑ j, a j*z j.succ-b) := by
  simp only [normalDual,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_one]
  rw [mul_sub,mul_add,Finset.mul_sum]
  ring_nf

lemma fullMiss_normalDual (v : σ → Fin (n+1) → K) (c : Kˣ) (b : K) (a : Fin n → K) :
    fullMiss v (normalDual c b a)=normalizedMiss v a b := by
  classical
  unfold fullMiss normalizedMiss
  have he : (∀ i, (∑ j, normalDual c b a j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) ≠ 0) ↔
      (∀ i, v i 0+∑ j, a j*v i j.succ ≠ b) := by
    apply forall_congr'
    intro i
    rw [normalDual_dot]
    exact ⟨fun h => sub_ne_zero.mp (mul_ne_zero_iff.mp h).2,
      fun h => mul_ne_zero c.ne_zero (sub_ne_zero.mpr h)⟩
  simp only [he]



lemma raw_conditioning_bound (v : σ → Fin (n+1) → K) :
    (Fintype.card Kˣ:ℝ)*(∑ a : Fin n → K, ∑ b : K, normalizedMiss v a b) ≤
      ∑ w : Fin (n+2) → K, fullMiss v w := by
  classical
  let f := fun t : Kˣ × K × (Fin n → K) => normalDual t.1 t.2.1 t.2.2
  have hs : (∑ t, fullMiss v (f t)) ≤ ∑ w, fullMiss v w := by
    rw [←Finset.sum_image (fun x hx y hy he => normalDual_injective he)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun w hw hwt => fullMiss_nonneg v w)
  have he : (∑ t, fullMiss v (f t)) =
      (Fintype.card Kˣ:ℝ)*(∑ a : Fin n → K, ∑ b : K, normalizedMiss v a b) := by
    simp only [f,Fintype.sum_prod_type,fullMiss_normalDual]
    rw [Finset.sum_const,nsmul_eq_mul]
    congr 1
    exact Finset.sum_comm
  rwa [he] at hs

lemma conditioning_bound (v : σ → Fin (n+1) → K) :
    meanNormalized v ≤ ((Fintype.card K:ℝ)/((Fintype.card K:ℝ)-1))*meanFull v := by
  have hcard : 1 < Fintype.card K := Fintype.one_lt_card
  have hc : (1:ℝ) < Fintype.card K := by exact_mod_cast hcard
  have hc0 : (0:ℝ) < Fintype.card K := by linarith
  have hcm : (0:ℝ) < (Fintype.card K:ℝ)-1 := by linarith
  have hh := raw_conditioning_bound v
  rw [Fintype.card_units,Nat.cast_sub (by omega),Nat.cast_one] at hh
  unfold meanNormalized meanFull
  apply (div_le_iff₀ (pow_pos hc0 _)).mpr
  calc
    _ ≤ (∑ w : Fin (n+2) → K, fullMiss v w)/((Fintype.card K:ℝ)-1) :=
      (le_div_iff₀ hcm).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by
      rw [show (Fintype.card K:ℝ)^(n+2)=(Fintype.card K:ℝ)^(n+1)*(Fintype.card K:ℝ) by rw [show n+2=(n+1)+1 by omega,pow_succ]]
      field_simp [hc0.ne',hcm.ne']


end SingleLatticeCovering.AffineVoid


noncomputable section
namespace SingleLatticeCovering.ConvexCore
open Set MeasureTheory Filter Topology Metric
open scoped Pointwise ENNReal
variable {d : ℕ}

lemma interior_nonempty_of_volume_pos {J : Set (Fin d → ℝ)}
    (hconv : Convex ℝ J) (hV : 0 < volume.real J) : (interior J).Nonempty := by
  by_contra hh
  have hi : interior J = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
  have hs : J ⊆ frontier J := by
    rw [frontier,hi,sdiff_empty]
    exact subset_closure
  have hz : volume J = 0 := measure_mono_null hs (hconv.addHaar_frontier volume)
  simp only [measureReal_def,hz,ENNReal.toReal_zero] at hV
  exact lt_irrefl _ hV

lemma core_subset_interior {J : Set (Fin d → ℝ)} (hconv : Convex ℝ J)
    (h0 : 0 ∈ interior J) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    c • J ⊆ interior J := by
  rintro x ⟨y,hy,rfl⟩
  simpa only [smul_zero,zero_add] using
    hconv.combo_interior_self_mem_interior h0 hy (sub_pos.mpr hc1) hc0 (sub_add_cancel 1 c)

lemma core_compact {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (c : ℝ) :
    IsCompact (c • J) := by
  exact hJ.image (by fun_prop)

lemma core_volume {J : Set (Fin d → ℝ)} {c : ℝ} (hc : 0 ≤ c) :
    volume.real (c • J)=c^d*volume.real J := by
  rw [measureReal_def,Measure.addHaar_smul_of_nonneg volume hc,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hc _)]
  simp only [Module.finrank_pi,Fintype.card_fin]
  rfl

lemma compact_uniform_add {J C : Set (Fin d → ℝ)} (hC : IsCompact C)
    (hsub : C ⊆ interior J) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, ∀ u : Fin d → ℝ, ‖u‖ ≤ δ → x+u ∈ J := by
  obtain ⟨δ,hδ,hs⟩ := hC.exists_cthickening_subset_open isOpen_interior hsub
  refine ⟨δ,hδ,fun x hx u hu => interior_subset (hs ?_)⟩
  apply Metric.mem_cthickening_of_dist_le (x+u) x δ C hx
  simpa only [dist_eq_norm,add_sub_cancel_left] using hu

lemma exists_shrink_exp {V ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ Real.exp (-(c^d*V)) < Real.exp (-V)+ε := by
  have hc : ContinuousAt (fun c : ℝ => Real.exp (-(c^d*V))) 1 := by fun_prop
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  let t := min (δ/2) (1/2:ℝ)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨1-t,by linarith,by linarith,?_⟩
  have hh := hclose (show dist (1-t) 1 < δ by
    simpa only [Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos ht] using htδ)
  simp only [one_pow,one_mul,Real.dist_eq] at hh
  linarith [(abs_lt.mp hh).2]

end SingleLatticeCovering.ConvexCore


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_MeanHoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid BrokenCircuit PrimeCircuit
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma modForm_liftCoeff (p : ℕ) (hp : 0<p) (a : Fin n → ZMod p) (z : Fin (n+1) → ℤ) :
    modForm p 0 (liftCoeff a) z = (z 0 : ZMod p)+
      ∑ j, (z j.succ : ZMod p)*a j := by
  let : NeZero p := ⟨hp.ne'⟩
  change (z 0 : ZMod p) +
    (∑ j ∈ Finset.univ.erase 0, (liftCoeff a j : ZMod p)*(z j : ZMod p)) = _
  congr 1
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp [liftCoeff,Fin.sum_univ_succ,mul_comm]

lemma card_badOffsets (p : ℕ) [Fact p.Prime] (a : Fin n → ZMod p)
    (S : Finset (Fin (n+1) → ℤ)) :
    ((badOffsets p 0 (liftCoeff a) S).card:ℝ) =
      ∑ b : ZMod p, normalizedMiss (fun z : S => fun j => (z.val j:ZMod p)) a b := by
  classical
  unfold badOffsets
  rw [←Finset.sum_boole]
  apply Fintype.sum_equiv (finResidue p)
  intro b
  unfold normalizedMiss
  congr 1
  apply propext
  simp only [finResidue,Equiv.coe_fn_mk,Subtype.forall,modForm_liftCoeff p (Nat.Prime.pos Fact.out),mul_comm]

lemma meanPrimeHole_le_grid (p : ℕ) [Fact p.Prime]
    (S : Finset (Fin (n+1) → ℤ)) {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J)
    (hthick : ∀ z ∈ S, ∀ u ∈ gridUnitCell,
      gridMap p (Nat.Prime.pos Fact.out) z + normalizeEquiv p (Nat.Prime.pos Fact.out) u ∈ J) :
    meanPrimeHole J p ≤ meanNormalized (fun z : S => fun j => (z.val j:ZMod p)) := by
  classical
  have hp : 0<p := Nat.Prime.pos Fact.out
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hs : (∑ a : Fin n → ZMod p, ((ensembleFull p hp a).hole J).toReal) ≤
      ∑ a : Fin n → ZMod p, (∑ b : ZMod p,
        normalizedMiss (fun z : S => fun j => (z.val j:ZMod p)) a b)/(p:ℝ) := by
    apply Finset.sum_le_sum
    intro a ha
    have hh := ENNReal.toReal_mono
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hp.ne'))
      (normalizedFull_hole_le_badOffsets p hp 0 (liftCoeff a) S hJ hthick)
    simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,card_badOffsets] using hh
  unfold meanPrimeHole meanNormalized
  simp only [ZMod.card]
  calc
    _ ≤ (∑ a : Fin n → ZMod p, (∑ b : ZMod p,
        normalizedMiss (fun z : S => fun j => (z.val j:ZMod p)) a b)/(p:ℝ))/(p:ℝ)^n :=
      div_le_div_of_nonneg_right hs (pow_nonneg hpR.le _)
    _ = _ := by rw [←Finset.sum_div,div_div,pow_succ]; congr 1; ring

lemma fintype_sum_irrel {A M : Type*} [AddCommMonoid M] (I₁ I₂ : Fintype A)
    (f g : A → M) (h : ∀ a, f a=g a) :
    @Finset.sum A M _ (@Finset.univ A I₁) f =
    @Finset.sum A M _ (@Finset.univ A I₂) g := by
  have he : I₁=I₂ := Subsingleton.elim _ _
  subst I₂
  exact @Fintype.sum_congr A M I₁ _ f g h

lemma fullMiss_eq_avoidance {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) (w : Fin (n+2) → K) :
    fullMiss v w=avoidanceIndicator (fun z => Fin.cons 1 (v z)) (dotProductBilin K K w) := by
  classical
  have he (i : σ) : (∑ j, w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) =
      (dotProductBilin K K w) (Fin.cons 1 (v i)) := by
    change (∑ j : Fin (n+2), w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) =
      ∑ j : Fin (n+2), w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j
    exact fintype_sum_irrel _ _ _ _ (fun j => rfl)
  unfold fullMiss avoidanceIndicator
  split_ifs with h₁ h₂ h₂
  · rfl
  · exfalso
    apply h₂
    intro i
    exact (he i).symm ▸ h₁ i
  · exfalso
    apply h₁
    intro i
    exact (he i) ▸ h₂ i
  · rfl

lemma meanFull_generic {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) :
    meanFull v=vectorAverage (fun w : Fin (n+2) → K =>
      avoidanceIndicator (fun z => Fin.cons 1 (v z)) (dotProductBilin K K w)) := by
  classical
  unfold meanFull vectorAverage
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  apply congrArg (fun t : ℝ => t/(Fintype.card K:ℝ)^(n+2))
  exact fintype_sum_irrel _ _ _ _ (fullMiss_eq_avoidance v)

lemma meanFull_integerGrid {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J)
    (p : ℕ) [Fact p.Prime] :
    meanFull (fun z : integerGrid J hJ (primeScale (n+1) p) =>
      fun j => (z.val j:ZMod p))=primeGridVoid J hJ p := by
  exact meanFull_generic _

lemma scaleFactor_eq_primeScale_inv (d p : ℕ) :
    scaleFactor (ι:=Fin d) p=(primeScale d p)⁻¹ := by
  simp only [scaleFactor,Fintype.card_fin,primeScale]
  exact Real.rpow_neg (Nat.cast_nonneg _) _

lemma gridMap_eq_scaledIntegerPoint (d p : ℕ) (hp : 0<p) (z : Fin d → ℤ) :
    gridMap p hp z=scaledIntegerPoint (primeScale d p) z := by
  ext j
  change scaleFactor (ι:=Fin d) p*(z j:ℝ)=_
  rw [scaleFactor_eq_primeScale_inv]
  rfl

lemma gridUnitCell_norm_le {d : ℕ} {u : Fin d → ℝ} (hu : u ∈ gridUnitCell) : ‖u‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro j
  have hh := (Set.mem_pi.mp hu) j (Set.mem_univ _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2.le

lemma eventually_grid_thick {d : ℕ} (hd : 0<d) {J C : Set (Fin d → ℝ)}
    (hC : IsCompact C) (hsub : C ⊆ interior J) :
    ∀ᶠ p : ℕ in atTop, ∀ hp : 0<p,
      ∀ z ∈ integerGrid C hC (primeScale d p), ∀ u ∈ gridUnitCell,
        gridMap p hp z + normalizeEquiv p hp u ∈ J := by
  obtain ⟨δ,hδ,hs⟩ := ConvexCore.compact_uniform_add hC hsub
  have ht : Tendsto (fun p => (primeScale d p)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (primeScale_tendsto hd)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with p hpδ hp z hz u hu
  apply hs (gridMap p hp z)
  · rw [gridMap_eq_scaledIntegerPoint]
    exact (mem_integerGrid hC (primeScale_pos hp).ne').mp hz
  · change ‖scaleFactor (ι:=Fin d) p • u‖ ≤ δ
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (scaleFactor_pos p hp)]
    calc
      _ ≤ scaleFactor (ι:=Fin d) p * 1 :=
        mul_le_mul_of_nonneg_left (gridUnitCell_norm_le hu) (scaleFactor_pos p hp).le
      _ ≤ δ := by rw [mul_one,scaleFactor_eq_primeScale_inv]; exact hpδ.le



end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.AffineVoid
open Filter Topology
lemma conditioning_factor_tendsto :
    Tendsto (fun p : ℕ => (p:ℝ)/((p:ℝ)-1)) atTop (𝓝 (1:ℝ)) := by
  have hden : Tendsto (fun p : ℕ => (p:ℝ)-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ => (p:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (b+1))] with p hp
    linarith
  have ht : Tendsto (fun p : ℕ => 1+((p:ℝ)-1)⁻¹) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,add_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_add 1
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hn : (p:ℝ)-1 ≠ 0 := by linarith
  field_simp [hn]
  ring

lemma eventually_factor_mul_lt {A B : ℝ} (hAB : A<B) :
    ∀ᶠ p : ℕ in atTop, ((p:ℝ)/((p:ℝ)-1))*A < B := by
  have ht := conditioning_factor_tendsto.mul_const A
  rw [one_mul] at ht
  exact ht.eventually (gt_mem_nhds hAB)
end SingleLatticeCovering.AffineVoid

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid RogersPreparation ConvexCore SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}



theorem eventually_meanPrimeHole_centered_source (hd : 270 ≤ n+1)
    {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (h0 : 0 ∈ interior J) (hV : 0 < volume.real J)
    (hVeta : volume.real J ≤ sourceEta (n+1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      meanPrimeHole J p ≤ Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+ε := by
  obtain ⟨c,hc0,hc1,hcexp⟩ := exists_shrink_exp (d:=n+1) (V:=volume.real J)
    (show 0<ε/3 by linarith)
  let C := c • J
  have hC : IsCompact C := core_compact hJ c
  have hCconv : Convex ℝ C := hconv.smul c
  have hCsub : C ⊆ interior J := core_subset_interior hconv h0 hc0.le hc1
  have hC0 : 0 ∈ C := ⟨0,interior_subset h0,smul_zero c⟩
  have hCV : volume.real C=c^(n+1)*volume.real J := core_volume hc0.le
  have hCVpos : 0<volume.real C := by rw [hCV]; positivity
  have hCVeta : volume.real C≤ sourceEta (n+1) := by
    rw [hCV]
    exact (mul_le_of_le_one_left hV.le (pow_le_one₀ hc0.le hc1.le)).trans hVeta
  obtain ⟨N₁,hN₁⟩ := eventually_primeGridVoid_source hd hC hCconv hC0 hCVpos hCVeta
    (show 0<ε/3 by linarith)
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp (eventually_grid_thick (Nat.succ_pos n) hC hCsub)
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp (eventually_factor_mul_lt
    (A:=Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+2*ε/3)
    (B:=Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+ε)
    (by linarith))
  refine ⟨max N₁ (max N₂ N₃),fun p hp hpN => ?_⟩
  have hp0 : 0<p := Nat.Prime.pos Fact.out
  have hp1 : (1:ℝ)<p := by exact_mod_cast Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have hpR : (0:ℝ)<p := by linarith
  have hM := meanPrimeHole_le_grid p (integerGrid C hC (primeScale (n+1) p)) hJ
    (hN₂ p ((le_max_left N₂ N₃).trans ((le_max_right N₁ (max N₂ N₃)).trans hpN)) hp0)
  have hcond := conditioning_bound (fun z : integerGrid C hC (primeScale (n+1) p) =>
    fun j => (z.val j:ZMod p))
  rw [ZMod.card,meanFull_integerGrid] at hcond
  have hh := hN₁ p ((le_max_left _ _).trans hpN)
  have hsmall : primeGridVoid C hC p ≤
      Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+2*ε/3 := by
    rw [←hCV] at hcexp
    linarith
  exact hM.trans (hcond.trans ((mul_le_mul_of_nonneg_left hsmall
    (div_nonneg hpR.le (by linarith))).trans
    (hN₃ p ((le_max_right N₂ N₃).trans ((le_max_right N₁ (max N₂ N₃)).trans hpN))).le))


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.Horizontal
open Set MeasureTheory Completion
open scoped Pointwise
lemma FullLattice.hole_vadd {d : ℕ} (L : FullLattice d)
    (v : Fin d → ℝ) (J : Set (Fin d → ℝ)) : L.hole (v+ᵥJ)=L.hole J := by
  have he : latticeProjection L.module '' (v+ᵥJ)=
      latticeProjection L.module v +ᵥ (latticeProjection L.module '' J) := by
    ext y
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨latticeProjection L.module x,⟨x,hx,rfl⟩,(map_add _ _ _).symm⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨v+x,⟨x,hx,rfl⟩,map_add _ _ _⟩
  unfold FullLattice.hole
  rw [he,←vadd_set_compl,measure_vadd]
end SingleLatticeCovering.Horizontal

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid RogersPreparation ConvexCore SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma meanPrimeHole_vadd (v : Fin (n+1) → ℝ) (J : Set (Fin (n+1) → ℝ))
    (p : ℕ) [Fact p.Prime] : meanPrimeHole (v+ᵥJ) p=meanPrimeHole J p := by
  classical
  unfold meanPrimeHole
  simp only [Horizontal.FullLattice.hole_vadd]



theorem eventually_meanPrimeHole_source (hd : 270 ≤ n+1)
    {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (hV : 0 < volume.real J) (hVeta : volume.real J ≤ sourceEta (n+1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      meanPrimeHole J p ≤ Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+ε := by
  obtain ⟨v,hv⟩ := interior_nonempty_of_volume_pos hconv hV
  let C := (-v)+ᵥJ
  have hC : IsCompact C := IsCompact.vadd (-v) hJ
  have hCconv : Convex ℝ C := hconv.vadd (-v)
  have hC0 : 0 ∈ interior C := by
    rw [show interior C=(-v)+ᵥinterior J from interior_vadd (-v) J]
    exact ⟨v,hv,neg_add_cancel v⟩
  have hCV : volume.real C=volume.real J := by
    unfold Measure.real
    rw [measure_vadd]
  obtain ⟨N,hN⟩ := eventually_meanPrimeHole_centered_source hd hC hCconv hC0
    (by rwa [hCV]) (by rwa [hCV]) hε
  refine ⟨N,fun p hp hpN => ?_⟩
  have hh := hN p hpN
  rw [hCV] at hh
  simpa only [C,meanPrimeHole_vadd] using hh


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma meanPrimeHole_le_one (J : Set (Fin (n+1) → ℝ)) (p : ℕ) [Fact p.Prime] :
    meanPrimeHole J p ≤ 1 := by
  classical
  have hp : 0 < p := Nat.Prime.pos Fact.out
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  unfold meanPrimeHole
  apply (div_le_one (pow_pos hpR n)).mpr
  calc
    _ ≤ ∑ _a : Fin n → ZMod p, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hh : (ensembleFull p hp a).hole J ≤ 1 := by
        unfold FullLattice.hole
        exact prob_le_one
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
      Fintype.card_fin,ZMod.card,nsmul_eq_mul,Nat.cast_pow,mul_one]


theorem eventually_meanPrimeHole_all_oai (hd : 270 ≤ n+1)
    {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (hVeta : volume.real J ≤ sourceEta (n+1)) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      meanPrimeHole J p ≤ Real.exp (-volume.real J)+301*Real.exp (-sourceEta (n+1)) := by
  by_cases hV : 0<volume.real J
  · obtain ⟨N,hN⟩ := eventually_meanPrimeHole_source hd hJ hconv hV hVeta
      (Real.exp_pos (-sourceEta (n+1)))
    refine ⟨N,fun p hp hpN => ?_⟩
    linarith [hN p hpN]
  · have hV0 : volume.real J=0 := le_antisymm (not_lt.mp hV) measureReal_nonneg
    refine ⟨0,fun p hp hpN => ?_⟩
    rw [hV0,neg_zero,Real.exp_zero]
    have hh := meanPrimeHole_le_one J p
    linarith [Real.exp_pos (-sourceEta (n+1))]


end SingleLatticeCovering.PrimeKernel

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all_oai := @OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all_oai

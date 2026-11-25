-- Prove2me | solution 1 for GlobalTheory.PowerBasisDiscr.discr_power_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:25.061825+00:00
-- url     : https://prove2.me/submissions/aec552f1-5d05-47cf-abb5-34bc4b175167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DiscrPowerBasis
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_isUnit_det
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PowerBasisDiscr
private theorem val_discr {C : Type} [Field C] (v : Valuation C NNReal) {n : ℕ} (a : Fin n → C) :
    v (discr a) = v ((Matrix.vandermonde a).det ^ 2) := by
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j : Fin n => v (a j - a i))
  rw [Matrix.det_vandermonde, map_pow, Up.discr]
  simp only [map_prod]
  rw [sq, ← Finset.prod_mul_distrib]
  simp only [← Finset.prod_mul_distrib]
  have h2 : ∀ i : Fin n, Finset.univ.erase i = ({i}ᶜ : Finset (Fin n)) := by
    intro i; ext j; simp
  simp only [h2]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Valuation.map_sub_swap v (a i) (a j)]
private theorem inj_of_discr {C : Type} [Field C] {n : ℕ} (a : Fin n → C) (h : discr a ≠ 0) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (i := j) ?_ ?_)
  · simp [Ne.symm hne]
  · rw [hij, sub_self]
private theorem det_change {R M O : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    [Algebra R O] {n : ℕ} (b b' : Module.Basis (Fin n) R M) (f : Fin n → M →ₗ[R] O) :
    ∃ u : O, IsUnit u ∧ (Matrix.of fun i j => f j (b' i)).det = u * (Matrix.of fun i j => f j (b i)).det := by
  refine ⟨algebraMap R O (b.toMatrix b').det, ?_, ?_⟩
  · exact (b.isUnit_det b').map _
  · rw [← Matrix.det_transpose (b.toMatrix b'), RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    conv_lhs => rw [← b.sum_repr (b' i)]
    simp only [map_sum, map_smul, Algebra.smul_def]
end GlobalTheory.PowerBasisDiscr
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowerBasisDiscr
namespace GlobalTheory.PowerBasisDiscr
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow), (∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ)) → Function.Injective (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) ∧ 0 ≤ (w.n : ℝ) * vd ∧ (v (discr fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) : ℝ) = (v (algebraMap O C (p : O)) : ℝ) ^ ((w.n : ℝ) * vd) := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ _ w t vd hvd α b hb
  obtain ⟨b', hb'⟩ := hvd
  obtain ⟨u, hu, hdet⟩ := det_change b b'
    (fun j => (tauExt ((t j : Emb (O := O) w.e) : OE →+* O)).toLinearMap ∘ₗ w.Ow.subtype)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply] at hdet
  have hM : (Matrix.of fun i j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)) =
      (Matrix.vandermonde fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)ᵀ := by
    ext i j
    have h1 : tauExt ((t j : Emb (O := O) w.e) : OE →+* O) w.e = 1 := (t j).2
    simp [hb, h1, Matrix.vandermonde_apply]
  have hvu : v (algebraMap O C u) = 1 := hv.isUnit_iff_valuation_eq_one.1 hu
  have key : v (discr fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) =
      v (algebraMap O C (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b' i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)) := by
    rw [val_discr, hdet, hM, Matrix.det_transpose, mul_pow, map_mul, map_mul, map_pow, map_pow, map_pow,
      hvu, one_pow, _root_.one_mul, map_pow, map_pow, RingHom.map_det]
    congr 3
    ext i j
    simp [Matrix.vandermonde_apply]
  have hq0 : 0 < (v (algebraMap O C (p : O)) : ℝ) := by
    have : v (algebraMap O C (p : O)) ≠ 0 := by
      rw [map_natCast, Valuation.ne_zero_iff]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  have hq1 : (v (algebraMap O C (p : O)) : ℝ) < 1 := by
    have : v (algebraMap O C (p : O)) < 1 :=
      lt_of_le_of_ne (hv.map_le_one _) fun h => hp.out (hv.isUnit_iff_valuation_eq_one.2 h)
    exact_mod_cast this
  refine ⟨?_, ?_, by rw [key, hb']⟩
  · refine Function.Injective.of_comp (f := algebraMap O C) (inj_of_discr _ fun h0 => ?_)
    have h3 := Real.rpow_pos_of_pos hq0 ((w.n : ℝ) * vd)
    rw [← hb', ← key] at h3
    have h4 : discr (fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) = 0 := h0
    rw [h4] at h3
    simp at h3
  · by_contra hneg
    have h3 := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hq0 hq1 (not_le.1 hneg)
    rw [← hb'] at h3
    have h4 := hv.map_le_one (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b' i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)
    exact absurd h4 (not_le.2 (by exact_mod_cast h3))
end GlobalTheory.PowerBasisDiscr

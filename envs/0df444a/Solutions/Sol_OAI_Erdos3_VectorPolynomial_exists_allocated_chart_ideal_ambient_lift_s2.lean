-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_chart_ideal_ambient_lift_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:08:34.244001+00:00
-- url     : https://prove2.me/submissions/f612a204-d403-4ad4-be0f-64fa3ebb9d0a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_masked_cover_factor_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem ambient_nsmul_lipschitz {J : Type*} [Fintype J] (a : ℕ) :
    LipschitzWith (a : ℝ≥0) (fun z : J → UnitAddCircle => a • z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← smul_sub, dist_eq_norm]
  exact norm_nsmul_le

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators NNReal

theorem finite_lipschitz_linear_combination {T X : Type*} [Fintype T] [PseudoMetricSpace X]
    (c : T → ℂ) (f : T → X → ℂ) {L B : ℝ≥0}
    (hf : ∀ t, LipschitzWith L (f t)) (hb : ∀ t x, ‖f t x‖ ≤ B) :
    (∀ x, ‖∑ t, c t * f t x‖ ≤ ((∑ t, ‖c t‖₊) * B : ℝ≥0)) ∧
      LipschitzWith ((∑ t, ‖c t‖₊) * L) (fun x => ∑ t, c t * f t x) := by
  constructor
  · intro x
    calc
      _ ≤ ∑ t, ‖c t * f t x‖ := norm_sum_le _ _
      _ ≤ ∑ t, ‖c t‖ * B := Finset.sum_le_sum (fun t _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb t x) (norm_nonneg _))
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ ∑ t, dist (c t * f t x) (c t * f t y) := dist_sum_sum_le _ _ _
      _ = ∑ t, ‖c t‖ * dist (f t x) (f t y) := by
        simp only [dist_eq_norm, ← mul_sub, norm_mul]
      _ ≤ ∑ t, ‖c t‖ * ((L : ℝ) * dist x y) := Finset.sum_le_sum (fun t _ =>
        mul_le_mul_of_nonneg_left ((hf t).dist_le_mul _ _) (norm_nonneg _))
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul, mul_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealPoint_coordinates (x : EuclideanSpace ℝ D) :
    mixedRealPoint W b o (mixedRealCoordinates W b o x) = x := by
  change (normalizedOrthogonalChart W b).symm
    ((orthonormalChart o) ((orthonormalChart o).symm ((normalizedOrthogonalChart W b) x).1),
      ((normalizedOrthogonalChart W b) x).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoordinateCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem normalizedCoordinateCutoff_spec (D : Type*) [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) :
    ContDiff ℝ ∞ (normalizedCoordinateCutoff D r hr) ∧
      HasCompactSupport (normalizedCoordinateCutoff D r hr) ∧
      (∀ v, 0 ≤ normalizedCoordinateCutoff D r hr v ∧ normalizedCoordinateCutoff D r hr v ≤ 1) ∧
      (∀ v, (∀ d, |v d| ≤ (r : ℝ)) → normalizedCoordinateCutoff D r hr v = 1) ∧
      (∀ v, normalizedCoordinateCutoff D r hr v ≠ 0 → ∀ d, |v d| ≤ 2 * (r : ℝ)) ∧
      LipschitzWith (Fintype.card D * normalizedSiteCutoffBound / (2 * r))
        (normalizedCoordinateCutoff D r hr) :=
  Classical.choose_spec (exists_normalized_site_cutoff (D := D) r hr)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

theorem allocatedFullAmbientSiteCoordinates_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  let pz := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => z ⟨a.1, (), k⟩))
  let pw := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => w ⟨a.1, (), k⟩))
  have hout : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤ dist pz pw := by
    rcases a.2 with i | i
    · exact (dist_le_pi_dist pz.1 pw.1 i).trans (le_max_left _ _)
    · exact (dist_le_pi_dist pz.2 pw.2 i).trans (le_max_right _ _)
  have hrow := ((mixedRealCoordinates_lipschitz (euclideanSubspace (U a.1)) (b a.1) (o a.1) (hC a.1)).comp
    (euclideanFromCoordinates_lipschitz (D := J a.1))).dist_le_mul
      (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩)
  have hin : dist (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mpr (fun k => dist_le_pi_dist z w ⟨a.1, (), k⟩)
  have hc : C a.1 * Fintype.card (J a.1) ≤ ∑ j, C j * Fintype.card (J j) :=
    Finset.single_le_sum (f := fun j => C j * Fintype.card (J j))
      (fun _ _ => by positivity) (Finset.mem_univ a.1)
  have hd : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤
      ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w :=
    (hout.trans hrow).trans ((mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg))
  change |Sum.elim pz.1 pz.2 a.2 / R a.1 - Sum.elim pw.1 pw.2 a.2 / R a.1| ≤ _
  rw [← sub_div, abs_div, abs_of_pos (hR a.1)]
  calc
    _ ≤ (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) / R a.1 :=
      div_le_div_of_nonneg_right hd (hR a.1).le
    _ = (R a.1)⁻¹ * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) := by ring
    _ ≤ (K : ℝ) * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) :=
      mul_le_mul_of_nonneg_right (hK a.1) (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)
    _ = _ := by rw [NNReal.coe_mul, mul_assoc]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedBufferedAmbientCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

theorem allocatedFullAmbientSiteCoordinates_norm_bound
    (hR : ∀ j, 0 < R j) (z : ambient → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ a, |allocatedFullAmbientSiteCoordinates (R := R) U b o z a| ≤ T)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖(EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (T * R j)) := by
  let v := (EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)
  let w := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j) v
  have hu (i : I j) : |w.1 i| ≤ T * R j := by
    have h := hz ⟨j, .inl i⟩
    change |w.1 i / R j| ≤ T at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have hv (i : Fin (n j)) : |w.2 i| ≤ T * R j := by
    have h := hz ⟨j, .inr i⟩
    change |w.2 i / R j| ≤ T at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have h := mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg hT (hR j).le) (hchart j) w.1 w.2 hu hv
  dsimp only [w] at h
  rw [Prod.mk.eta, mixedRealPoint_coordinates] at h
  exact h

variable (r : ℝ≥0) (hr : 0 < r)

theorem allocatedBufferedAmbientCutoff_range (z : ambient → ℝ) :
    0 ≤ allocatedBufferedAmbientCutoff (R := R) U b o r hr z ∧
      allocatedBufferedAmbientCutoff (R := R) U b o r hr z ≤ 1 :=
  (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.1 _

theorem allocatedBufferedAmbientCutoff_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith ((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
      (K * ∑ j, C j * Fintype.card (J j)))
      (allocatedBufferedAmbientCutoff (R := R) U b o r hr) :=
  (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.2.2.comp
    (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR C hC K hK)

theorem allocatedBufferedAmbientCutoff_support (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (z : ambient → ℝ) (hz : allocatedBufferedAmbientCutoff (R := R) U b o r hr z ≠ 0) :
    ∀ a, |z a| ≤ 1 / 4 := by
  have hcoord := (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.2.1
    (allocatedFullAmbientSiteCoordinates (R := R) U b o z) hz
  rintro ⟨j, t, k⟩
  cases t
  have h := (allocatedFullAmbientSiteCoordinates_norm_bound U b o hR z (by positivity)
    hcoord C hC hchart j).trans (hbudget j)
  exact (PiLp.norm_apply_le ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)) k).trans h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_range (x : ambient → UnitAddCircle) :
    0 ≤ allocatedBufferedTorusCutoff (R := R) U b o r hr x ∧
      allocatedBufferedTorusCutoff (R := R) U b o r hr x ≤ 1 := by
  apply smallBoxTorusKernel_range _ zero_le_one (allocatedBufferedAmbientCutoff_range U b o r hr)
  intro z hz i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget z hz i).trans_lt (by norm_num)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_lipschitz
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith ((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
      (K * ∑ j, Cforward j * Fintype.card (J j))) (allocatedBufferedTorusCutoff (R := R) U b o r hr) := by
  apply smallBoxTorusKernel_lipschitz _
    (allocatedBufferedAmbientCutoff_lipschitz U b o r hr hR Cforward hforward K hK)
    (fun z => (allocatedBufferedAmbientCutoff_range U b o r hr z).1)
  intro z hz i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget z hz i).trans_lt (by norm_num)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {O J : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_nsmul_output (d : ℕ) (y : EuclideanJetLayers U O) :
    coveredJetAmbientTorus U d y = d • coveredJetAmbientTorus U 1 y := by
  funext a
  simp [coveredJetAmbientTorus, quotientIntegerCover, map_nsmul]

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_mk (d : ℕ) (v : ∀ j, O j → euclideanSubspace (U j)) :
    coveredJetAmbientTorus U d (fun j t => QuotientAddGroup.mk (v j t)) =
      fun a => (((d : ℝ) * (v a.1 a.2.1).val a.2.2 : ℝ) : UnitAddCircle) := by
  funext a
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (quotientIntegerCover _ d (QuotientAddGroup.mk' _ (v a.1 a.2.1)))) a.2.2 = _
  rw [quotientIntegerCover_mk, euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk,
    euclideanSubspaceArrayEquiv_apply]
  rfl

theorem ambient_nsmul_lipschitz {A : Type*} [Fintype A] (d : ℕ) :
    LipschitzWith (d : ℝ≥0) (fun z : A → UnitAddCircle => d • z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, ← smul_sub]
  simpa only [dist_eq_norm, NNReal.coe_natCast] using (norm_nsmul_le (a := z - w) (n := d))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

omit [Fintype α] in
theorem rowsAmbientSite_eq (s : Finset α) (d : ℕ)
    (y : EuclideanJetLayers U (fun j => {t : Finset α // t ∈ rowSets j})) :
    rowsAmbientSite rowSets s (coveredJetAmbientTorus U d y) =
      coveredJetAmbientTorus U d (coveredRowsSiteValue rowSets U y s) := by
  funext a
  simp only [rowsAmbientSite, coveredRowsSiteValue, coveredJetAmbientTorus,
    map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]

omit [Fintype α] in
theorem rowsAmbientSite_lipschitz (s : Finset α) :
    LipschitzWith (∑ j : Fin m, ((rowSets j).card : ℝ≥0))
      (rowsAmbientSite (J := J) rowSets s) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, t, i⟩
  have hterm (r : {t : Finset α // t ∈ rowSets j}) :
      dist (rowRestrictedSiteMatrix (rowSets j) s r • z ⟨j,r,i⟩)
        (rowRestrictedSiteMatrix (rowSets j) s r • w ⟨j,r,i⟩) ≤ dist z w := by
    simp only [rowRestrictedSiteMatrix, booleanReconstructionMatrix]
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨j,r,i⟩
    · simpa only [zero_zsmul, dist_self] using (dist_nonneg : 0 ≤ dist z w)
  have hc : ((rowSets j).card : ℝ≥0) ≤ ∑ j : Fin m, ((rowSets j).card : ℝ≥0) :=
    Finset.single_le_sum (f := fun j : Fin m => ((rowSets j).card : ℝ≥0))
      (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _r : {t : Finset α // t ∈ rowSets j}, dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun r _ => hterm r))
    _ = ((rowSets j).card : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

theorem exists_allocated_masked_ambient_lift
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lout := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    ∃ F : (ambient → UnitAddCircle) → ℂ,
      LipschitzWith Lout F ∧ (∀ z, ‖F z‖ ≤ 1) ∧
      ∀ y : EuclideanJetLayers U single,
        allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y =
          2 * F (coveredJetAmbientTorus U 1 y) := by
  intro Lcoord Lcut Lout
  obtain ⟨g, hg, hgb, hgv⟩ := exists_allocated_masked_cover_factor_s2 B U b S o hb bW d r hr period
    hdiv hR C hC hchart hbudget Cforward hforward K hK label f hf hf1
  let χ := allocatedBufferedTorusCutoff (R := R) U b o r hr
  have hχ := allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget
  have hχL : LipschitzWith Lcut χ :=
    allocatedBufferedTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget Cforward hforward K hK
  let e := fun z : ambient → UnitAddCircle => fun a : Σ j, J j => z ⟨a.1, (), a.2⟩
  have he : LipschitzWith 1 e := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro a
    simpa only [one_mul] using dist_le_pi_dist z w ⟨a.1, (), a.2⟩
  let F := fun z : ambient → UnitAddCircle =>
    (χ (d • z) : ℂ) * g ((d / period) • e z)
  have hχCL : LipschitzWith (Lcut * d) (fun z : ambient → UnitAddCircle => (χ (d • z) : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp
      (hχL.comp (ambient_nsmul_lipschitz d))
  have hgL : LipschitzWith (max (L * Lcoord * period) (4 * period) * (d / period : ℕ))
      (fun z : ambient → UnitAddCircle => g ((d / period) • e z)) := by
    simpa only [mul_one, Function.comp_def, Lcoord] using hg.comp ((ambient_nsmul_lipschitz (d / period)).comp he)
  have hχb (z : ambient → UnitAddCircle) : ‖(χ (d • z) : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
    exact (hχ _).2
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [one_mul, add_comm] using
      lipschitz_mul_of_bounds _ _ hχCL hgL hχb (Bf := 1) (Bg := 1) (fun z => hgb _)
  · intro z
    exact (norm_mul _ _).trans_le
      ((mul_le_mul (hχb z) (hgb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  · intro y
    choose v hv using fun j => QuotientAddGroup.mk'_surjective
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup (y j ())
    have hy : (fun j (_ : Unit) => QuotientAddGroup.mk (v j)) = y := by
      funext j t
      cases t
      exact hv j
    have hu (j) :
        (QuotientAddGroup.mk ((d : ℝ)⁻¹ • ((d : ℝ) • v j)) :
          euclideanSubspace (U j) ⧸
            (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) = y j () := by
      rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d)), one_smul]
      exact hv j
    have hz : coveredJetAmbientTorus U 1 y =
        fun a => ((v a.1).val a.2.2 : UnitAddCircle) := by
      rw [← hy, coveredJetAmbientTorus_mk]
      simp only [Nat.cast_one, one_mul]
    have hratio : (d : ℝ) / period = (d / period : ℕ) := by
      apply (div_eq_iff (Nat.cast_ne_zero.mpr (NeZero.ne period))).mpr
      exact_mod_cast (Nat.div_mul_cancel hdiv).symm
    have heq : (fun a : Σ j, J j => ((((d : ℝ) • v a.1).val a.2 / period : ℝ) : UnitAddCircle)) =
        (d / period) • e (coveredJetAmbientTorus U 1 y) := by
      rw [hz]
      funext a
      change (((d : ℝ) * (v a.1).val a.2 / period : ℝ) : UnitAddCircle) =
        (d / period) • ((v a.1).val a.2 : UnitAddCircle)
      rw [mul_div_right_comm, hratio]
      simpa only [nsmul_eq_mul] using (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := d / period) (x := (v a.1).val a.2))
    rw [hgv _ y hu, heq, coveredJetAmbientTorus_nsmul_output]
    dsimp only [F]
    ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedChartIdealAmbientLift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem exists_allocated_chart_ideal_ambient_lift_s2_oai
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lsite := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let mass := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ k, ‖(2 : ℂ) ^ Fintype.card (Finset α) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (mass * (Fintype.card (Finset α) * (Lsite * Lrows))) F ∧
      (∀ z, ‖F z‖ ≤ mass) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y =
          F (coveredJetAmbientTorus U 1 y) := by
  intro Lcoord Lcut Lsite Lrows mass
  let Label := Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
  have hex (label : Label) (k : T) (s : Finset α) :=
    exists_allocated_masked_ambient_lift B U b S o hb bW d r hr period
      hdiv hR C hC hchart hbudget Cforward hforward K hK (label s) (f k s) (hf k s) (hf1 k s)
  choose g hg hgb hgv using hex
  let c := fun t : Label × T => (2 : ℂ) ^ Fintype.card (Finset α) *
    allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a t.1 t.2
  let v := fun t : Label × T => fun z : JetAmbientIndex rowTypes J → UnitAddCircle =>
    ∏ s, g t.1 t.2 s (rowsAmbientSite rowSets s z)
  have hv (t : Label × T) : (∀ z, ‖v t z‖ ≤ 1) ∧
      LipschitzWith (Fintype.card (Finset α) * (Lsite * Lrows)) (v t) := by
    have h := bounded_lipschitz_fintype_prod
      (fun s z => g t.1 t.2 s (rowsAmbientSite rowSets s z)) (B := 1) le_rfl
      (fun s => (hg t.1 t.2 s).comp (rowsAmbientSite_lipschitz rowSets s))
      (fun s z => hgb t.1 t.2 s _)
    simpa only [one_pow, mul_one, NNReal.coe_one] using h
  have hsum := finite_lipschitz_linear_combination c v (fun t => (hv t).2) (B := 1)
    (fun t z => (hv t).1 z)
  have hm : (∑ t, ‖c t‖₊) = mass := by
    rw [Fintype.sum_prod_type]
  rw [hm, mul_one] at hsum
  refine ⟨fun z => ∑ t, c t * v t z, hsum.2, hsum.1, ?_⟩
  intro y
  simp only [Fintype.sum_prod_type]
  unfold allocatedProductChartIdealApproximation
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [c, v]
  simp_rw [hgv, rowsAmbientSite_eq U rowSets]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_chart_ideal_ambient_lift_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.exists_allocated_chart_ideal_ambient_lift_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}

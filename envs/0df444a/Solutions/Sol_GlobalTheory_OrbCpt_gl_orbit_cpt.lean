-- Prove2me | solution 1 for GlobalTheory.OrbCpt.gl_orbit_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:04:49.83541+00:00
-- url     : https://prove2.me/submissions/3f19038a-9978-4034-a275-d0fd7309a2a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
import Theorems.Thm_GlobalTheory_OrbCpt_hm_inter
import Theorems.Thm_GlobalTheory_OrbCpt_continuous_hm
import Theorems.Thm_GlobalTheory_OrbCpt_det_hm_self_ne_zero
import Theorems.Thm_GlobalTheory_OrbCpt_isCompact_units_image
import Theorems.Thm_GlobalTheory_ClassParam_Intw_mul
import Theorems.Thm_GlobalTheory_ClassParam_Iso_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}
namespace GlobalTheory.OrbCpt
theorem _root_.solution (A₀ : Matrix (Fin r) (Fin r) k) (hs : A₀.charpoly.Separable)
    (Z : Set (Matrix (Fin r) (Fin r) k)) (hZ : IsCompact Z) :
    ∃ C : Set (GL (Fin r) k), IsCompact C ∧ ∀ g : GL (Fin r) k,
      (g : Matrix (Fin r) (Fin r) k) * A₀ * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) ∈ Z →
      ∃ c ∈ C, ∃ t : GL (Fin r) k,
        (t : Matrix (Fin r) (Fin r) k) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) k) ∧ g = c * t := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, p = A₀.charpoly := ⟨_, rfl⟩
  rw [← hp] at hs
  obtain ⟨cj, hcjdef⟩ : ∃ cj : GL (Fin r) k → Matrix (Fin r) (Fin r) k, ∀ g, cj g =
      (g : Matrix (Fin r) (Fin r) k) * A₀ * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hcjdef]
  have hcj : ∀ g, aeval (cj g) p = 0 := by
    intro g
    have : (cj g).charpoly = p := by
      rw [hcjdef, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hp]
    rw [← this]; exact Matrix.aeval_self_charpoly _
  have hint : ∀ g h : GL (Fin r) k, cj g * (hm p (cj g) (cj h) * (h : Matrix (Fin r) (Fin r) k)) =
      (hm p (cj g) (cj h) * (h : Matrix (Fin r) (Fin r) k)) * A₀ := by
    intro g h
    have e := hm_inter p (cj g) (cj h)
    rw [hcj, hcj, sub_zero, sub_eq_zero] at e
    have e2 : cj h * (h : Matrix (Fin r) (Fin r) k) = h * A₀ := by
      rw [hcjdef]; simp only [mul_assoc, Units.inv_mul, mul_one]
    rw [← mul_assoc, e, mul_assoc, e2, mul_assoc]
  obtain ⟨D, hDdef⟩ : ∃ D : Matrix (Fin r) (Fin r) k → Matrix (Fin r) (Fin r) k → k,
      ∀ X Y, D X Y = (hm p X Y).det := ⟨_, fun _ _ => rfl⟩
  have hD : Continuous fun q : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin r) k => D q.1 q.2 := by
    simp only [hDdef]; exact (continuous_hm p).matrix_det
  have hD1 : ∀ Y, Continuous fun X => D X Y := fun Y =>
    hD.comp (continuous_id.prodMk continuous_const)
  have hD2 : ∀ X, Continuous fun Y => D X Y := fun X =>
    hD.comp (continuous_const.prodMk continuous_id)
  set K := closure (Z ∩ Set.range cj) with hKdef
  have hK : IsCompact K := hZ.closure_of_subset Set.inter_subset_left
  have hKp : ∀ X ∈ K, aeval X p = 0 := by
    have hc : IsClosed {X : Matrix (Fin r) (Fin r) k | aeval X p = 0} :=
      isClosed_eq (Polynomial.continuous_aeval p) continuous_const
    intro X hX
    exact (closure_minimal (fun Y hY => by obtain ⟨g, rfl⟩ := hY.2; exact hcj g) hc) hX
  have hcover : K ⊆ ⋃ g : {g : GL (Fin r) k // cj g ∈ Z}, {X | D X (cj g.1) ≠ 0} := by
    intro X hX
    have h0 : D X X ≠ 0 := by rw [hDdef]; exact det_hm_self_ne_zero hs (hKp X hX)
    have hnb : {Y | D X Y ≠ 0} ∈ 𝓝 X := (isOpen_ne_fun (hD2 X) continuous_const).mem_nhds h0
    obtain ⟨Y, hY1, hY2, ⟨g, rfl⟩⟩ := mem_closure_iff_nhds.mp hX _ hnb
    exact Set.mem_iUnion.mpr ⟨⟨g, hY2⟩, hY1⟩
  obtain ⟨s, hs'⟩ := hK.elim_finite_subcover _
    (fun g => isOpen_ne_fun (hD1 _) continuous_const) hcover
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Matrix (Fin r) (Fin r) k → ℝ, ∀ X, ψ X = ∑ g ∈ s, ‖D X (cj g.1)‖ :=
    ⟨_, fun _ => rfl⟩
  have hψ : Continuous ψ := by
    have : ψ = fun X => ∑ g ∈ s, ‖D X (cj g.1)‖ := funext hψdef
    rw [this]; exact continuous_finsetSum _ fun g _ => (hD1 _).norm
  have hψpos : ∀ X ∈ K, 0 < ψ X := by
    intro X hX
    obtain ⟨g, hg, hgX⟩ := Set.mem_iUnion₂.mp (hs' hX)
    have hgX' : D X (cj g.1) ≠ 0 := hgX
    have h1 : 0 < ‖D X (cj g.1)‖ := norm_pos_iff.mpr hgX'
    have h2 : ‖D X (cj g.1)‖ ≤ ∑ g ∈ s, ‖D X (cj g.1)‖ :=
      Finset.single_le_sum (f := fun i : {g : GL (Fin r) k // cj g ∈ Z} => ‖D X (cj i.1)‖)
        (fun (i : {g : GL (Fin r) k // cj g ∈ Z}) _ => norm_nonneg (D X (cj i.1))) hg
    rw [hψdef]; exact lt_of_lt_of_le h1 h2
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨∅, isCompact_empty, fun g hg => ?_⟩
    have : cj g ∈ K := subset_closure ⟨hg, g, rfl⟩
    rw [hKe] at this; exact absurd this (Set.notMem_empty _)
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hKne hψ.continuousOn
  set δ := ψ x0 / ((s.card : ℝ) + 1) with hδdef
  have hδ : 0 < δ := div_pos (hψpos x0 hx0) (by positivity)
  have hpiece : ∀ X ∈ K, ∃ g ∈ s, δ ≤ ‖D X (cj g.1)‖ := by
    intro X hX
    by_contra hcon
    push_neg at hcon
    have h1 : ψ X ≤ ∑ g ∈ s, δ := by rw [hψdef]; exact Finset.sum_le_sum fun g hg => (hcon g hg).le
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ψ x0 ≤ ψ X := hmin hX
    have hq := hψpos x0 hx0
    have h3 : (s.card : ℝ) * δ < ψ x0 := by
      rw [hδdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hC : ∀ g ∈ s, ∃ C : Set (GL (Fin r) k), IsCompact C ∧
      ∀ X ∈ K ∩ {X | δ ≤ ‖D X (cj g.1)‖},
        ∃ c ∈ C, (c : Matrix (Fin r) (Fin r) k) = hm p X (cj g.1) * (g.1 : Matrix (Fin r) (Fin r) k) := by
    intro g _
    apply isCompact_units_image (hK.inter_right (isClosed_le continuous_const (hD1 _).norm))
      (((continuous_hm p).comp (continuous_id.prodMk continuous_const)).mul continuous_const)
    rintro X ⟨_, hX⟩
    show (hm p X (cj g.1) * (g.1 : Matrix (Fin r) (Fin r) k)).det ≠ 0
    rw [Matrix.det_mul, ← hDdef]
    exact mul_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le hδ hX))
      (Matrix.isUnit_det_of_left_inverse (Units.inv_mul g.1)).ne_zero
  choose! Cg hCg hCgm using hC
  refine ⟨⋃ g ∈ s, Cg g, s.isCompact_biUnion hCg, fun g hg => ?_⟩
  have hgK : cj g ∈ K := subset_closure ⟨hg, g, rfl⟩
  obtain ⟨g', hg's, hδg⟩ := hpiece _ hgK
  obtain ⟨c, hcC, hc⟩ := hCgm g' hg's (cj g) ⟨hgK, hδg⟩
  refine ⟨c, Set.mem_iUnion₂.mpr ⟨g', hg's, hcC⟩, c⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hi := hint g g'.1
  rw [← hc] at hi
  have hA : A₀ * ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) =
      ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * cj g := by
    calc A₀ * ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
        = (((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * c) * A₀ *
            ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by rw [Units.inv_mul, one_mul]
      _ = ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * ((c : Matrix (Fin r) (Fin r) k) * A₀) *
            ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by simp only [mul_assoc]
      _ = ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (cj g * c) *
            ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by rw [hi]
      _ = ((c⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * cj g := by
            simp only [mul_assoc, Units.mul_inv, mul_one]
  rw [Units.val_mul, ← mul_assoc, hA]
  rw [hcjdef]; simp only [mul_assoc, Units.inv_mul, mul_one]
end GlobalTheory.OrbCpt

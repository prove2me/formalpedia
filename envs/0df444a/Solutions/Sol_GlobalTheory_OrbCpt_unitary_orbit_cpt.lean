-- Prove2me | solution 1 for GlobalTheory.OrbCpt.unitary_orbit_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:20.331967+00:00
-- url     : https://prove2.me/submissions/d84c1b2b-de7c-41f8-933c-ae07a430c092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
import Theorems.Thm_GlobalTheory_OrbCpt_gl_orbit_cpt
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
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
namespace GlobalTheory.OrbCpt
theorem _root_.solution (hN : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E))
    (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E) (hH : A₀.IsHermitian)
    (hs : A₀.charpoly.Separable) (Z : Set (Matrix (Fin r) (Fin r) E)) (hZ : IsCompact Z) :
    ∃ C : Set (Matrix.unitaryGroup (Fin r) E), IsCompact C ∧ ∀ g : Matrix.unitaryGroup (Fin r) E,
      g.1 * A₀ * star g.1 ∈ Z → ∃ c ∈ C, ∃ t : Matrix.unitaryGroup (Fin r) E,
        t.1 * A₀ = A₀ * t.1 ∧ g = c * t := by
  classical
  haveI : ContinuousStar E := ⟨by
    have h := AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E))
      (fun x => Unram.norm_star (F := F) x)
    exact h.continuous⟩
  obtain ⟨CE, hCE, hCEg⟩ := gl_orbit_cpt A₀ hs Z hZ

  let sU : GL (Fin r) E → GL (Fin r) E := fun c =>
    ⟨star (c : Matrix (Fin r) (Fin r) E), star ((c⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E),
      by rw [← star_mul, Units.inv_mul, star_one], by rw [← star_mul, Units.mul_inv, star_one]⟩
  have hsU : Continuous sU := by
    rw [Units.continuous_iff]
    exact ⟨continuous_star.comp Units.continuous_val, continuous_star.comp Units.continuous_coe_inv⟩
  let M : Set (GL (Fin r) E) := (fun c => (sU c * c)⁻¹) '' CE
  have hM : IsCompact M := hCE.image ((hsU.mul continuous_id).inv)
  obtain ⟨S, hS, hSt⟩ := hN F E r A₀ hH hs M hM
  let KM : Set (Matrix (Fin r) (Fin r) E) :=
    (fun q : GL (Fin r) E × GL (Fin r) E => ((q.1 * q.2 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) ''
      (CE ×ˢ S)
  have hKM : IsCompact KM := (hCE.prod hS).image (Units.continuous_val.comp continuous_mul)
  have hcl : IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) := by
    have : (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) =
        {A | star A * A = 1} ∩ {A | A * star A = 1} := by
      ext A; exact Unitary.mem_iff
    rw [this]
    exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  refine ⟨Subtype.val ⁻¹' KM, hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKM, ?_⟩
  intro g hg
  have hg1 : g.1 * star g.1 = 1 := Matrix.mem_unitaryGroup_iff.mp g.2
  have hg2 : star g.1 * g.1 = 1 := (Unitary.mem_iff.mp g.2).1
  let gU : GL (Fin r) E := ⟨g.1, star g.1, hg1, hg2⟩
  obtain ⟨c, hc, t, ht, hgct⟩ := hCEg gU hg
  set cm : Matrix (Fin r) (Fin r) E := (c : Matrix (Fin r) (Fin r) E)
  set ci : Matrix (Fin r) (Fin r) E := ((c⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have htv : (t : Matrix (Fin r) (Fin r) E) = ci * g.1 := by
    have : t = c⁻¹ * gU := by rw [hgct, inv_mul_cancel_left]
    rw [this, Units.val_mul]
  have htt : (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = ci * star ci := by
    rw [htv, star_mul, mul_assoc, ← mul_assoc g.1, hg1, one_mul]
  have hmM : (sU c * c)⁻¹ ∈ M := ⟨c, hc, rfl⟩
  have hmv : (((sU c * c)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = ci * star ci := by
    rw [_root_.mul_inv_rev, Units.val_mul]; rfl
  obtain ⟨s, hsS, hsA, hss⟩ := hSt t ht ⟨_, hmM, by rw [htt, hmv]⟩
  rw [htt] at hss
  set sm : Matrix (Fin r) (Fin r) E := (s : Matrix (Fin r) (Fin r) E)
  set si : Matrix (Fin r) (Fin r) E := ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hcs : ((c * s : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ Matrix.unitaryGroup (Fin r) E := by
    rw [Matrix.mem_unitaryGroup_iff, Units.val_mul, star_mul,
      show cm * sm * (star sm * star cm) = cm * (sm * star sm) * star cm by noncomm_ring, hss,
      show cm * (ci * star ci) * star cm = (cm * ci) * star (cm * ci) by rw [star_mul]; noncomm_ring,
      Units.mul_inv, star_one, one_mul]
  have hsi : si * A₀ = A₀ * si := by
    calc si * A₀ = si * A₀ * (sm * si) := by rw [Units.mul_inv, mul_one]
      _ = si * (sm * A₀) * si := by rw [hsA]; noncomm_ring
      _ = A₀ * si := by rw [← mul_assoc si, Units.inv_mul, one_mul]
  have hst : ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ Matrix.unitaryGroup (Fin r) E := by
    rw [Matrix.mem_unitaryGroup_iff, Units.val_mul, star_mul,
      show si * (t : Matrix (Fin r) (Fin r) E) * (star (t : Matrix (Fin r) (Fin r) E) * star si) =
        si * ((t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E)) * star si by noncomm_ring,
      htt, ← hss,
      show si * (sm * star sm) * star si = (si * sm) * star (si * sm) by rw [star_mul]; noncomm_ring,
      Units.inv_mul, star_one, one_mul]
  refine ⟨⟨_, hcs⟩, ⟨(c, s), ⟨hc, hsS⟩, rfl⟩, ⟨_, hst⟩, ?_, ?_⟩
  · show ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * A₀ =
      A₀ * ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
    rw [Units.val_mul, mul_assoc, ht, ← mul_assoc, hsi, mul_assoc]
  · apply Subtype.ext
    show g.1 = ((c * s : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
      ((s⁻¹ * t : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
    rw [← Units.val_mul, mul_assoc, mul_inv_cancel_left, ← hgct]
end GlobalTheory.OrbCpt

-- Prove2me | solution 1 for GlobalTheory.JR.weilAt_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:09.705656+00:00
-- url     : https://prove2.me/submissions/89f846cb-7c46-4c1e-9364-859fc6d4d9c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationExistsEtaleOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (hK : Subsingleton A.K) : WeilAt A := by
  have h01 : (0 : A.L) = 1 := by
    rw [← map_zero (algebraMap A.K A.L), ← map_one (algebraMap A.K A.L), Subsingleton.elim (0 : A.K) 1]
  haveI hL : Subsingleton A.L := subsingleton_of_zero_eq_one h01
  have hpsi : ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ t : A.K, A.psiK ψ t = 1 := by
    intro ψ _ t
    unfold Et.psiK
    rw [Subsingleton.elim t 0, map_zero, AddChar.map_zero_eq_one]
  intro ψ hψ x μ hμ
  haveI := hμ.1
  have hpos : 0 < μ Set.univ := (isOpen_univ.measure_pos μ Set.univ_nonempty)
  have hfin : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  have hreal : μ.real Set.univ ≠ 0 := by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  refine ⟨(μ.real Set.univ : ℂ)⁻¹, fun _ φ => φ, ?_, ?_⟩
  · exact ⟨fun _ _ hf => hf, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  · intro φ _
    refine ⟨?_, ?_, ?_⟩
    · intro z y; simp [hpsi ψ hψ]
    · intro s y
      have he : A.etaK (s : A.K) = 1 := by
        unfold Et.etaK eta
        rw [Subsingleton.elim (s : A.K) 1, map_one]
        rw [if_pos ⟨1, by simp⟩]
      have ha : A.absK (s : A.K) = 1 := by
        unfold Et.absK
        rw [dif_pos s.isUnit]
        rw [Subsingleton.elim (s.isUnit.unit) 1, map_one]
        rfl
      rw [he, ha, Subsingleton.elim ((s : A.K) • y) y]
      simp
    · intro y
      unfold fourB
      have : (fun x' => φ x' * A.kerL ψ x x' y) = fun _ => φ y := by
        funext x'
        unfold Et.kerL
        rw [hpsi ψ hψ, Subsingleton.elim x' y, mul_one]
      rw [this, integral_const, Complex.real_smul]
      show φ y = _
      have hc : ((μ.real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
      field_simp
end GlobalTheory.JR

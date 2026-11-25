-- Prove2me | solution 1 for GlobalTheory.ClassFin.exists_energy_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:08:13.196485+00:00
-- url     : https://prove2.me/submissions/17eb62ad-d2e7-4ed4-8123-464b123562a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MatrixEntriesBoundedOfHermitianLogTraceSqLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEnergyMin
import Theorems.Thm_GlobalTheory_ClassFin_EnergyMin_energy_nonneg
import Theorems.Thm_GlobalTheory_ClassFin_EnergyMin_isCompact_box
import Theorems.Thm_GlobalTheory_ClassFin_EnergyMin_exists_det_one
import Theorems.Thm_GlobalTheory_ClassFin_EnergyMin_inv_eq_adj
import Theorems.Thm_GlobalTheory_T_exists_isHermitianLogOfPosDef_gram
import Theorems.Thm_GlobalTheory_T_isClosed_isHermitianLogOfPosDef
import Theorems.Thm_GlobalTheory_T_matrix_entries_bounded_of_hermitian_log_trace_sq_le
import Theorems.Thm_P2M_GlobalTheory_T_entries_bounded_of_conj_spanning_bounded__a0549da12fe9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory.ClassFin.EnergyMin
namespace GlobalTheory.ClassFin
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), (∀ s, IsUnit (g s).det) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ (P : Matrix ι ι ℂ) (H : σ → Matrix ι ι ℂ), IsUnit P.det ∧ (∀ s, IsLog (H s) ((P * g s * P⁻¹)ᴴ * (P * g s * P⁻¹))) ∧ ∀ (P' : Matrix ι ι ℂ) (H' : σ → Matrix ι ι ℂ), IsUnit P'.det → (∀ s, IsLog (H' s) ((P' * g s * P'⁻¹)ᴴ * (P' * g s * P'⁻¹))) → ∑ s, (Matrix.trace (H s * H s)).re ≤ ∑ s, (Matrix.trace (H' s * H' s)).re := by
  intro ι _ _ σ _ g hg hspan
  choose H₀ hH₀ using fun s => GlobalTheory.T.exists_isHermitianLogOfPosDef_gram ι (g s) (hg s)
  let En : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) → ℝ := fun p => ∑ s, (Matrix.trace (p.2 s * p.2 s)).re
  have hEn : Continuous En := by
    refine continuous_finset_sum _ fun s _ => Complex.continuous_re.comp ?_
    have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
      (continuous_apply s).comp continuous_snd
    exact (h.matrix_mul h).matrix_trace
  let E₀ : ℝ := En (1, H₀)
  let Z : Set (Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) := {p | p.1.det = 1 ∧
    (∀ s, IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))) ∧ En p ≤ E₀}
  have hZc : IsClosed Z := by
    refine IsClosed.inter (isClosed_eq continuous_fst.matrix_det continuous_const)
      (IsClosed.inter ?_ (isClosed_le hEn continuous_const))
    have : IsClosed (⋂ s, {p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) |
        IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))}) := by
      refine isClosed_iInter fun s => ?_
      have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
        (continuous_apply s).comp continuous_snd
      have h2 : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.1 * g s * p.1.adjugate :=
        (continuous_fst.matrix_mul continuous_const).matrix_mul continuous_fst.matrix_adjugate
      exact (GlobalTheory.T.isClosed_isHermitianLogOfPosDef ι).preimage (h.prodMk (h2.matrix_conjTranspose.matrix_mul h2))
    rw [← Set.setOf_forall] at this
    exact this
  obtain ⟨C, hC⟩ := GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le ι E₀
  obtain ⟨C', hC'⟩ := GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' ι σ g hspan C
  have hK : IsCompact ({x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C'} ×ˢ
      (Set.pi Set.univ fun _ : σ => {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C})) :=
    (isCompact_box C').prod (isCompact_univ_pi fun _ => isCompact_box C)
  have hZ : IsCompact Z := by
    refine hK.of_isClosed_subset hZc ?_
    rintro ⟨P, H⟩ ⟨hd, hl, hE⟩
    have hb : ∀ s i j, ‖(P * g s * P.adjugate) i j‖ ≤ C ∧ ‖H s i j‖ ≤ C := by
      intro s
      refine hC _ _ (hl s) (le_trans ?_ hE)
      exact Finset.single_le_sum (f := fun s => (Matrix.trace (H s * H s)).re)
        (fun t _ => energy_nonneg (hl t)) (Finset.mem_univ s)
    refine ⟨hC' P hd fun s i j => ?_, fun s _ i j => (hb s i j).2⟩
    rw [inv_eq_adj hd]
    exact (hb s i j).1
  have h0 : ((1, H₀) : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) ∈ Z := by
    refine ⟨Matrix.det_one, fun s => ?_, le_rfl⟩
    simpa using hH₀ s
  obtain ⟨⟨P, H⟩, ⟨hd, hl, hE⟩, hmin⟩ := hZ.exists_isMinOn ⟨_, h0⟩ hEn.continuousOn
  have hd' : P.det = 1 := hd
  refine ⟨P, H, by rw [hd']; exact isUnit_one, fun s => by rw [inv_eq_adj hd']; exact hl s, ?_⟩
  intro P' H' hP' hl'
  obtain ⟨Q, hQ, hQx⟩ := exists_det_one P' hP'
  change En (P, H) ≤ En (Q, H')
  by_cases hle : En (Q, H') ≤ E₀
  · refine hmin (a := (Q, H')) ⟨hQ, fun s => ?_, hle⟩
    have := hl' s
    rw [← hQx, inv_eq_adj hQ] at this
    exact this
  · exact hE.trans (not_le.mp hle).le
end GlobalTheory.ClassFin

-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.indicator_slice_orbit_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:40.859953+00:00
-- url     : https://prove2.me/submissions/040b919f-b967-44dd-ace2-b64370054bb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceSectionHaarDecomposition
import Theorems.Thm_GlobalTheory_RankFibreKer_minor_mul
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer
namespace GlobalTheory.RankFibreKer
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (K : Subgroup (GL (Fin a) k)), IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a ↔ ∃ J, minor Y J ≠ 0) →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    IsLocallyConstant (Set.indicator {Y : Matrix (Fin a) (Fin d) k | ∃ x ∈ K, ∃ Z ∈ slice k a d, Y = x.val * Z}
      (1 : Matrix (Fin a) (Fin d) k → ℂ)) := by
  intro k _ _ _ _ a d K hKo hKO hrank s hs hsec huniq
  set T : Set (Matrix (Fin a) (Fin d) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice k a d, Y = x.val * Z} with hTdef
  set O : Set (Matrix (Fin a) (Fin d) k) := {Y | Y.rank = a} with hOdef
  have hmc : ∀ J : Fin a ↪ Fin d, Continuous fun Y : Matrix (Fin a) (Fin d) k => minor Y J := fun J => by
    unfold minor
    exact (continuous_id.matrix_submatrix id J).matrix_det

  have hT : ∀ Y ∈ O, (Y ∈ T ↔ s Y ∈ K) := by
    intro Y hY
    constructor
    · rintro ⟨x, hx, Z, hZ, rfl⟩
      have h1 : ((s (x.val * Z))⁻¹ * x).val * Z ∈ slice k a d := by
        rw [Units.val_mul, Matrix.mul_assoc]; exact hsec _ hY
      have h2 := huniq Z _ hZ h1
      have h3 : x = s (x.val * Z) := by
        have := congrArg (fun g => s (x.val * Z) * g) h2
        simpa [← mul_assoc] using this
      rw [← h3]; exact hx
    · intro h
      refine ⟨s Y, h, _, hsec Y hY, ?_⟩
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hTmin : ∀ Y ∈ T, ∃ J, valuation k (minor Y J) = 1 := by
    rintro Y ⟨x, hx, Z, ⟨J, hJ, -⟩, rfl⟩
    refine ⟨J, ?_⟩
    rw [minor_mul, minor, hJ, Matrix.det_one, mul_one]
    have := valuation_gdet_of_mem_KO (hKO hx)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hTO : T ⊆ O := by
    intro Y hY
    obtain ⟨J, hJ⟩ := hTmin Y hY
    refine (hrank Y).2 ⟨J, fun h => ?_⟩
    rw [h, map_zero] at hJ
    exact zero_ne_one hJ
  have hOopen : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro Y hY
    obtain ⟨J, hJ⟩ := (hrank Y).1 hY
    have hv : valuation k (minor Y J) ≠ 0 := by simpa using hJ
    have hn := (valuation k).locally_const hv
    have := (hmc J).continuousAt.preimage_mem_nhds hn
    refine Filter.mem_of_superset this fun Y' hY' => (hrank Y').2 ⟨J, fun h0 => ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq, h0, map_zero] at hY'
    exact hv hY'.symm
  have hKc : IsClosed (K : Set (GL (Fin a) k)) := Subgroup.isClosed_of_isOpen K hKo
  have hTeq : T = O ∩ s ⁻¹' (K : Set (GL (Fin a) k)) := by
    ext Y
    constructor
    · intro h; exact ⟨hTO h, (hT Y (hTO h)).1 h⟩
    · rintro ⟨h1, h2⟩; exact (hT Y h1).2 h2
  have hTopen : IsOpen T := by
    rw [hTeq]; exact hs.isOpen_inter_preimage hOopen hKo
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) := by
    have := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using this
  have hTclosed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro Y hY
    by_cases hYO : Y ∈ O
    · have hsY : s Y ∉ K := fun h => hY ((hT Y hYO).2 h)
      have ho : IsOpen (O ∩ s ⁻¹' (K : Set (GL (Fin a) k))ᶜ) := hs.isOpen_inter_preimage hOopen hKc.isOpen_compl
      refine Filter.mem_of_superset (ho.mem_nhds ⟨hYO, hsY⟩) fun Y' hY' hT' => hY'.2 ?_
      exact (hT Y' hY'.1).1 hT'
    · have hz : ∀ J, minor Y J = 0 := by
        intro J; by_contra hne; exact hYO ((hrank Y).2 ⟨J, hne⟩)
      have hW : (⋂ J : Fin a ↪ Fin d, (fun Y' => minor Y' J) ⁻¹' {x : k | valuation k x < 1}) ∈ nhds Y := by
        refine Filter.iInter_mem.2 fun J => ?_
        refine (hmc J).continuousAt.preimage_mem_nhds ?_
        rw [hz J]; exact h0
      refine Filter.mem_of_superset hW fun Y' hY' hT' => ?_
      obtain ⟨J, hJ⟩ := hTmin Y' hT'
      have := Set.mem_iInter.1 hY' J
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hJ] at this
      exact lt_irrefl _ this
  exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTclosed, hTopen⟩).isLocallyConstant
end GlobalTheory.RankFibreKer

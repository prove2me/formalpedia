-- Prove2me | solution 1 for HunterPDE.Compactness.exists_sobolev_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T16:36:51.690103+00:00
-- url     : https://prove2.me/submissions/3649ffbe-8f03-4c14-92af-174e303c4b6e

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_sub
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_smul
import Mathlib.Analysis.Seminorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.MeanInequalities

open MeasureTheory HunterPDE.Compactness HunterPDE.Shared
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {n k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    ∃ W : Submodule ℝ (EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ f, f ∈ W ↔ MemW k p Ω f) ∧
      ∃ q : Seminorm ℝ W, ∀ f : W,
        ENNReal.ofReal (q f) = sobolevNorm k p Ω f := by
  classical
  have hz (α : Fin n → ℕ) : HasWeakDeriv Ω α 0 0 := by
    refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
    intro φ hφ
    simp
  have hsmul {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemW k p Ω f) (c : ℝ) :
      MemW k p Ω (c • f) := by
    intro α hα
    obtain ⟨g, hg, hgp⟩ := hf α hα
    exact ⟨c • g, hg.smul c, hgp.const_smul c⟩
  have hadd {f g : EuclideanSpace ℝ (Fin n) → ℝ}
      (hf : MemW k p Ω f) (hg : MemW k p Ω g) : MemW k p Ω (f + g) := by
    intro α hα
    obtain ⟨u, hu, hup⟩ := hf α hα
    obtain ⟨v, hv, hvp⟩ := hg α hα
    refine ⟨u + v, ?_, hup.add hvp⟩
    simpa using hu.sub (hv.smul (-1))
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin n) → ℝ) :=
    { carrier := {f | MemW k p Ω f}
      zero_mem' := fun α _ => ⟨0, hz α, by simp⟩
      add_mem' := fun hf hg => hadd hf hg
      smul_mem' := fun c f hf => hsmul hf c }
  have chosen {f g : EuclideanSpace ℝ (Fin n) → ℝ} {α : Fin n → ℕ}
      (hg : HasWeakDeriv Ω α f g) : HasWeakDeriv Ω α f (weakDeriv Ω α f) := by
    unfold weakDeriv
    rw [dif_pos (show ∃ g, HasWeakDeriv Ω α f g from ⟨g, hg⟩)]
    exact Exists.choose_spec _
  have hc (f : W) (α : Fin n → ℕ) (hα : α ∈ multiIndicesLe n k) :
      HasWeakDeriv Ω α f (weakDeriv Ω α f) ∧
        MemLp (weakDeriv Ω α f) p (volume.restrict Ω) := by
    obtain ⟨g, hg, hgp⟩ := f.property α hα
    exact ⟨chosen hg, hgp.ae_eq ((chosen hg).ae_eq hΩ hg).symm⟩
  have hfin (f : W) : sobolevNorm k p Ω f ≠ ∞ := by
    simp only [sobolevNorm, if_neg hp']
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact ENNReal.sum_ne_top.mpr fun α hα =>
      ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (hc f α hα).2.eLpNorm_ne_top
  have htri (f g : W) : sobolevNorm k p Ω (f + g) ≤
      sobolevNorm k p Ω f + sobolevNorm k p Ω g := by
    have coord (α : Fin n → ℕ) (hα : α ∈ multiIndicesLe n k) :
        eLpNorm (weakDeriv Ω α (f + g)) p (volume.restrict Ω) ≤
          eLpNorm (weakDeriv Ω α f) p (volume.restrict Ω) +
            eLpNorm (weakDeriv Ω α g) p (volume.restrict Ω) := by
      have hsum : HasWeakDeriv Ω α (f + g)
          (weakDeriv Ω α f + weakDeriv Ω α g) := by
        simpa using (hc f α hα).1.sub ((hc g α hα).1.smul (-1))
      rw [eLpNorm_congr_ae ((chosen hsum).ae_eq hΩ hsum)]
      exact eLpNorm_add_le (hc f α hα).2.aestronglyMeasurable
        (hc g α hα).2.aestronglyMeasurable hp
    have hpReal : 1 ≤ p.toReal := by
      exact_mod_cast ENNReal.toReal_mono hp' hp
    simp only [sobolevNorm, if_neg hp']
    calc
      _ ≤ (∑ α ∈ multiIndicesLe n k,
          (eLpNorm (weakDeriv Ω α f) p (volume.restrict Ω) +
            eLpNorm (weakDeriv Ω α g) p (volume.restrict Ω)) ^ p.toReal) ^
              (1 / p.toReal) := by
        apply ENNReal.rpow_le_rpow
        · exact Finset.sum_le_sum fun α hα =>
            ENNReal.rpow_le_rpow (coord α hα) ENNReal.toReal_nonneg
        · positivity
      _ ≤ _ := ENNReal.Lp_add_le (multiIndicesLe n k) _ _ hpReal
  have hhom (c : ℝ) (f : W) : sobolevNorm k p Ω (c • f) =
      ENNReal.ofReal ‖c‖ * sobolevNorm k p Ω f := by
    have coord (α : Fin n → ℕ) (hα : α ∈ multiIndicesLe n k) :
        eLpNorm (weakDeriv Ω α (c • f)) p (volume.restrict Ω) =
          ENNReal.ofReal ‖c‖ * eLpNorm (weakDeriv Ω α f) p (volume.restrict Ω) := by
      have hs := (hc f α hα).1.smul c
      rw [eLpNorm_congr_ae ((chosen hs).ae_eq hΩ hs), eLpNorm_const_smul]
      rw [← ofReal_norm]
    have hpReal : 0 < p.toReal := by
      have : 1 ≤ p.toReal := by exact_mod_cast ENNReal.toReal_mono hp' hp
      linarith
    simp only [sobolevNorm, if_neg hp']
    rw [Finset.sum_congr rfl (fun α hα =>
      congrArg (fun a : ℝ≥0∞ => a ^ p.toReal) (coord α hα))]
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
    rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ← ENNReal.rpow_mul, mul_one_div_cancel hpReal.ne', ENNReal.rpow_one]
  refine ⟨W, fun _ => Iff.rfl, ?_⟩
  let q : Seminorm ℝ W := Seminorm.of (fun f : W => (sobolevNorm k p Ω f).toReal)
    (fun f g => by
      change (sobolevNorm k p Ω ((f : EuclideanSpace ℝ (Fin n) → ℝ) + g)).toReal ≤ _
      simpa only [ENNReal.toReal_add (hfin f) (hfin g)] using
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin f, hfin g⟩) (htri f g))
    (fun c f => by
      change (sobolevNorm k p Ω (c • (f : EuclideanSpace ℝ (Fin n) → ℝ))).toReal = _
      simp only [hhom, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg c)])
  exact ⟨q, fun f => ENNReal.ofReal_toReal (hfin f)⟩

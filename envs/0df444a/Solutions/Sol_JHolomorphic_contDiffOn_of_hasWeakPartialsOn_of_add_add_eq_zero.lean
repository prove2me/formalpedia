-- Prove2me | solution 1 for JHolomorphic.contDiffOn_of_hasWeakPartialsOn_of_add_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:22:15.320787+00:00
-- url     : https://prove2.me/submissions/6557bd0b-4b28-42e6-8a05-695ccbd775cc

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_prodMk
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension



/-!
# Q-L, layer L2: regularity of weak solutions of `∂ₛu + J₀ ∂ₜu + m(z, u) = 0`

Graph trick: `z ↦ (z, u z)` is weakly `J`-holomorphic for the smooth almost complex structure
`J(z, y)(a, b) = (i a, J₀ b + Re a · J₀ m(z, y) + Im a · m(z, y))` on `ℂ × F`.
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Set JHolomorphic
open scoped ContDiff ENNReal

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The graph almost complex structure. -/
def graphJ (J₀F : F →L[ℝ] F) (m : ℂ → F → F) (x : ℂ × F) : (ℂ × F) →L[ℝ] (ℂ × F) :=
  ((Complex.I • ContinuousLinearMap.id ℝ ℂ).comp (ContinuousLinearMap.fst ℝ ℂ F)).prod
    (J₀F.comp (ContinuousLinearMap.snd ℝ ℂ F) +
      (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ F)).smulRight (J₀F (m x.1 x.2)) +
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ F)).smulRight (m x.1 x.2))

lemma graphJ_apply (J₀F : F →L[ℝ] F) (m : ℂ → F → F) (x : ℂ × F) (v : ℂ × F) :
    graphJ J₀F m x v = (Complex.I * v.1,
      J₀F v.2 + v.1.re • J₀F (m x.1 x.2) + v.1.im • m x.1 x.2) := by
  simp [graphJ]

lemma isAlmostComplexOn_graphJ (J₀F : F →L[ℝ] F) (hJ : ∀ y, J₀F (J₀F y) = -y)
    (m : ℂ → F → F) (hm : ContDiff ℝ ∞ (fun x : ℂ × F => m x.1 x.2)) :
    IsAlmostComplexOn (graphJ J₀F m) univ := by
  refine ⟨isOpen_univ, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    rw [contDiff_clm_apply_iff]
    intro v
    simp only [graphJ_apply]
    exact contDiff_const.prodMk
      ((contDiff_const.add ((J₀F.contDiff.comp hm).const_smul _)).add (hm.const_smul _))
  · intro x _
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, graphJ_apply, graphJ_apply]
    refine Prod.ext ?_ ?_
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.fst_neg]
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.snd_neg,
        map_add, map_smul, hJ, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_sub, add_zero, smul_neg, neg_smul]
      abel

lemma memLp_pair {r : ℝ≥0∞} {μ : Measure ℂ} {f : ℂ → ℂ} {g : ℂ → F} (hf : MemLp f r μ)
    (hg : MemLp g r μ) : MemLp (fun z => (f z, g z)) r μ := by
  have h := ((ContinuousLinearMap.inl ℝ ℂ F).comp_memLp' hf).add
    ((ContinuousLinearMap.inr ℝ ℂ F).comp_memLp' hg)
  have e : (fun z => (f z, g z)) =
      (⇑(ContinuousLinearMap.inl ℝ ℂ F) ∘ f) + (⇑(ContinuousLinearMap.inr ℝ ℂ F) ∘ g) := by
    funext z; simp
  rw [e]; exact h

/-- L2. Weak solutions of a smooth first-order equation `∂ₛu + J₀ ∂ₜu + m(z, u) = 0` with a
complex structure `J₀` on the values are smooth. -/
theorem contDiffOn_of_weak_eq (J₀F : F →L[ℝ] F) (hJ : ∀ y, J₀F (J₀F y) = -y)
    (m : ℂ → F → F) (hm : ContDiff ℝ ∞ (fun x : ℂ × F => m x.1 x.2))
    (q : ℝ) (hq : 2 < q) (U : Set ℂ) (hU : IsOpen U) (u us ut : ℂ → F)
    (hu : ContinuousOn u U) (hw : HasWeakPartialsOn U u us ut)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp us (ENNReal.ofReal q) (volume.restrict K) ∧ MemLp ut (ENNReal.ofReal q) (volume.restrict K))
    (heq : ∀ᵐ z ∂(volume.restrict U), us z + J₀F (ut z) + m z (u z) = 0) :
    ContDiffOn ℝ ∞ u U := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hid0 := HasWeakPartialsOn.of_contDiffOn hU (contDiff_id (𝕜 := ℝ) (E := ℂ)).contDiffOn
  have hid : HasWeakPartialsOn U (fun z : ℂ => z) (fun _ => (1 : ℂ)) (fun _ => Complex.I) := by
    have h := hid0
    simp at h
    exact h
  have hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn (fun z : ℂ => z) K ∧ IntegrableOn (fun _ : ℂ => (1 : ℂ)) K ∧
        IntegrableOn (fun _ : ℂ => Complex.I) K ∧
        IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K := by
    intro K hKU hK
    haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact ⟨continuousOn_id.integrableOn_compact hK, continuousOn_const.integrableOn_compact hK,
      continuousOn_const.integrableOn_compact hK, (hu.mono hKU).integrableOn_compact hK,
      ((hLp K hKU hK).1).integrable hq1, ((hLp K hKU hK).2).integrable hq1⟩
  have hG := hid.prodMk hw hint
  have hweak : IsWeakJHolomorphicOn q (graphJ J₀F m) univ U (fun z => (z, u z)) := by
    refine ⟨continuousOn_id.prodMk hu, fun _ _ => mem_univ _, _, _, hG,
      fun K hKU hK => ⟨?_, ?_, ?_⟩, ?_⟩
    · exact memLp_of_continuousOn_compact hK ((continuousOn_id.prodMk hu).mono hKU)
    · exact memLp_pair (memLp_of_continuousOn_compact hK continuousOn_const) (hLp K hKU hK).1
    · exact memLp_pair (memLp_of_continuousOn_compact hK continuousOn_const) (hLp K hKU hK).2
    · filter_upwards [heq] with z hz
      rw [graphJ_apply]
      refine Prod.ext ?_ ?_
      · simp [Complex.I_mul_I]
      · simp only [Prod.snd_add, Prod.snd_zero, Complex.I_re, Complex.I_im, zero_smul, add_zero,
          one_smul]
        rw [← add_assoc]
        exact hz
  have hsm := contDiffOn_of_isWeakJHolomorphicOn q hq (graphJ J₀F m) univ
    (isAlmostComplexOn_graphJ J₀F hJ m hm) U hU _ hweak
  exact contDiff_snd.comp_contDiffOn hsm

end

end QL

end FiniteEnergyPlane

open JHolomorphic

open MeasureTheory Set
open scoped ContDiff ENNReal

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (J₀F : F →L[ℝ] F) (hJ : ∀ y, J₀F (J₀F y) = -y)
    (m : ℂ → F → F) (hm : ContDiff ℝ ∞ (fun x : ℂ × F => m x.1 x.2))
    (q : ℝ) (hq : 2 < q) (U : Set ℂ) (hU : IsOpen U) (u us ut : ℂ → F)
    (hu : ContinuousOn u U) (hw : HasWeakPartialsOn U u us ut)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp us (ENNReal.ofReal q) (volume.restrict K) ∧ MemLp ut (ENNReal.ofReal q) (volume.restrict K))
    (heq : ∀ᵐ z ∂(volume.restrict U), us z + J₀F (ut z) + m z (u z) = 0) :
    ContDiffOn ℝ ∞ u U :=
  FiniteEnergyPlane.QL.contDiffOn_of_weak_eq J₀F hJ m hm q hq U hU u us ut hu hw hLp heq

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.block_of_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:17:15.0948+00:00
-- url     : https://prove2.me/submissions/3973e221-a315-4a4d-9f42-ee4c4e660fad

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_det_submatrix_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution {E : Type} [Field E] (M : Matrix ι ι E) (t₀ : Sub ι m)
    (hu : IsUnit (cmp M : Matrix (Sub ι m) (Sub ι m) E).det) (h : ∀ t, t ≠ t₀ → cmp M t t₀ = 0) :
    ∀ r ∉ (t₀.1 : Set ι), ∀ c ∈ (t₀.1 : Set ι), M r c = 0 := by
  intro r hr c hc
  set B : Matrix m m E := M.submatrix (en t₀) (en t₀) with hBdef
  have hB : B.det ≠ 0 := by
    intro h0
    have hz : (cmp M : Matrix (Sub ι m) (Sub ι m) E).det = 0 := by
      refine det_eq_zero_of_column_eq_zero t₀ fun t => ?_
      rcases eq_or_ne t t₀ with rfl | ht
      · exact h0
      · exact h t ht
    rw [hz] at hu
    exact not_isUnit_zero hu
  let v : m → E := fun i => M r (en t₀ i)
  have hr' : ∀ a, en t₀ a ≠ r := fun a e => hr (e ▸ en_mem t₀ a)
  have hcr : ∀ i, Bᵀ.cramer v i = 0 := by
    intro i
    rw [cramer_apply]
    let f : m → ι := Function.update (en t₀) i r
    have hf : Function.Injective f := by
      intro a b hab
      by_cases ha : a = i <;> by_cases hb : b = i
      · rw [ha, hb]
      · subst ha
        simp only [f, Function.update_self, Function.update_of_ne hb] at hab
        exact absurd hab.symm (hr' b)
      · subst hb
        simp only [f, Function.update_self, Function.update_of_ne ha] at hab
        exact absurd hab (hr' a)
      · simp only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact en_injective t₀ hab
    let T : Finset ι := Finset.univ.map ⟨f, hf⟩
    have hT : T.card = Fintype.card m := by simp [T]
    let t : Sub ι m := ⟨T, hT⟩
    have hft : ∀ a, f a ∈ t.1 := fun a => Finset.mem_map.2 ⟨a, Finset.mem_univ _, rfl⟩
    have hne : t ≠ t₀ := by
      intro e
      have h2 : r ∈ t.1 := by
        have := hft i
        simpa [f] using this
      rw [e] at h2
      exact hr h2
    have h3 := det_submatrix_eq_zero M t t₀ f hf hft (h t hne)
    have h4 : Bᵀ.updateCol i v = (M.submatrix f (en t₀))ᵀ := by
      ext a b
      by_cases hb : b = i
      · subst hb
        simp [updateCol_apply, v, f]
      · simp [updateCol_apply, hb, f, Function.update_of_ne hb, hBdef]
    rw [h4, det_transpose, h3]
  have hv : v = 0 := by
    have h5 := mulVec_cramer Bᵀ v
    have h6 : Bᵀ.cramer v = 0 := funext hcr
    rw [h6, mulVec_zero, det_transpose] at h5
    exact (smul_eq_zero.1 h5.symm).resolve_left hB
  have h7 : c ∈ Set.range (en t₀) := by rw [range_en]; exact hc
  obtain ⟨j, rfl⟩ := h7
  exact congrFun hv j
end GlobalTheory.CompanionTheory.Plucker

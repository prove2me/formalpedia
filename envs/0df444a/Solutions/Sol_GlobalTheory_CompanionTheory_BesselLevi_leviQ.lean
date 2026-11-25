-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselLevi.leviQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:21:29.885349+00:00
-- url     : https://prove2.me/submissions/570c93ed-512b-4663-8b1d-ad0bd683be94

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_pr_val
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_Hq_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_mem_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_mul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_diag_mem
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselLevi
namespace GlobalTheory.CompanionTheory.BesselLevi
theorem _root_.solution : LeviQ := by
  intro k r hk s hs htri
  have hz : ∀ i j : Fin (2 * r + k + 1), j.val < i.val → s i j = 0 := fun i j h => htri h
  have hs' := (mem_iff k r s).1 hs
  let mid : Fin (2 * r + k + 1) → Prop := fun i => r ≤ i.val ∧ i.val ≤ r + k
  have hmidp : ∀ i, mid (pr k r i) ↔ mid i := by
    intro i
    have := pr_val k r i
    simp only [mid]
    omega
  let d : Fin (2 * r + k + 1) → ℂ := fun i => if mid i then 1 else s i i
  have hd : ∀ i, conj (d i) * d (pr k r i) = 1 := by
    intro i
    by_cases h : mid i
    · simp [d, h, hmidp]
    · have h2 := hs' i (pr k r i)
      rw [if_pos rfl, Finset.sum_eq_single i] at h2
      · simpa [d, h, hmidp] using h2
      · intro x _ hx
        have e1 := pr_val k r i
        have e2 := pr_val k r x
        have e3 : x.val ≠ i.val := fun e => hx (Fin.ext e)
        simp only [mid] at h
        by_cases hxi : i.val < x.val
        · rw [hz x i hxi]; simp
        · rw [hz (pr k r x) (pr k r i) (by omega)]; simp
      · simp
  have hdn : ∀ i, ‖d i‖ * ‖d (pr k r i)‖ = 1 := by
    intro i
    have := congrArg norm (hd i)
    simpa using this
  have hd0 : ∀ i, ‖d i‖ ≠ 0 := fun i => left_ne_zero_of_mul_eq_one (hdn i)
  have hd0' : ∀ i, ((‖d i‖ : ℝ) : ℂ) ≠ 0 := fun i => by exact_mod_cast hd0 i
  let μ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
    if mid i ∧ mid j then s i j else if i = j then 1 else 0
  have hμ : μ ∈ UH (Hq k r) := by
    rw [mem_iff]
    intro i j
    by_cases hi : mid i
    · by_cases hj : mid j
      · rw [← hs' i j]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : mid x
        · simp [μ, hi, hj, hx, hmidp]
        · have hxi : x ≠ i := fun e => hx (e ▸ hi)
          have e2 := pr_val k r x
          have : conj (s x i) * s (pr k r x) j = 0 := by
            simp only [mid] at hi hj hx
            by_cases hxi : i.val < x.val
            · rw [hz x i hxi]; simp
            · rw [hz (pr k r x) j (by omega)]; simp
          rw [this]
          simp [μ, hx, hxi]
      · have hij : pr k r i ≠ j := fun e => hj (e ▸ (hmidp i).2 hi)
        rw [if_neg hij]
        refine Finset.sum_eq_zero fun x _ => ?_
        by_cases hx : mid x
        · have : pr k r x ≠ j := fun e => hj (e ▸ (hmidp x).2 hx)
          simp [μ, hj, this]
        · have hxi : x ≠ i := fun e => hx (e ▸ hi)
          simp [μ, hx, hxi]
    · rw [Finset.sum_eq_single i]
      · simp [μ, hi, hmidp]
      · intro x _ hx
        simp [μ, hi, hx]
      · simp
  let t : Fin (2 * r + k + 1) → ℝ := fun i => ‖d i‖
  let κ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    Matrix.diagonal fun i => d i / (‖d i‖ : ℂ)
  have hκ : κ ∈ UH (Hq k r) := by
    apply diag_mem
    intro i
    have h1 : ((‖d i‖ : ℝ) : ℂ) * ((‖d (pr k r i)‖ : ℝ) : ℂ) = 1 := by exact_mod_cast hdn i
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, hd, h1, div_one]
  have ht : dg t ∈ UH (Hq k r) := by
    apply diag_mem
    intro i
    rw [Complex.conj_ofReal]
    exact_mod_cast hdn i
  obtain ⟨l, hl⟩ : ∃ l, l = dg t * μ * κ := ⟨_, rfl⟩
  have hlU : l ∈ UH (Hq k r) := hl ▸ mul_mem (mul_mem ht hμ) hκ
  have hle : ∀ i j, l i j = if mid i ∧ mid j then s i j else if i = j then s i i else 0 := by
    intro i j
    have e1 : (dg t * μ) i j = ((‖d i‖ : ℝ) : ℂ) * μ i j :=
      Matrix.diagonal_mul (fun i => ((‖d i‖ : ℝ) : ℂ)) μ i j
    have e2 : (dg t * μ * κ) i j = (dg t * μ) i j * (d j / ((‖d j‖ : ℝ) : ℂ)) :=
      Matrix.mul_diagonal (fun i => d i / ((‖d i‖ : ℝ) : ℂ)) (dg t * μ) i j
    rw [hl, e2, e1]
    by_cases h : mid i ∧ mid j
    · simp [d, μ, h.1, h.2]
    · have hμe : μ i j = if i = j then 1 else 0 := if_neg h
      rw [hμe, if_neg h]
      by_cases e : i = j
      · subst e
        have hi : ¬ mid i := fun hi => h ⟨hi, hi⟩
        have := hd0' i
        rw [if_pos rfl, if_pos rfl, mul_one, mul_div_cancel₀ _ this]
        simp [d, hi]
      · simp [e]
  have hltri : l.BlockTriangular id := by
    intro i j hij
    have hij' : j.val < i.val := hij
    have : i ≠ j := fun e => by subst e; omega
    rw [hle, hz i j hij', if_neg this, ite_self]
  have hinv : (Hq k r * lᴴ * Hq k r) * l = 1 := by
    have : lᴴ * Hq k r * l = Hq k r := hlU
    calc _ = Hq k r * (lᴴ * Hq k r * l) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [this, Hq_sq]
  letI : Invertible l := invertibleOfLeftInverse _ _ hinv
  have hitri : l⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hltri
  have hiz : ∀ i j : Fin (2 * r + k + 1), j.val < i.val → l⁻¹ i j = 0 := fun i j h => hitri h
  have hll : l * l⁻¹ = 1 := Matrix.mul_inv_of_invertible l
  have hiU : l⁻¹ ∈ UH (Hq k r) := by
    have h1 : lᴴ * Hq k r * l = Hq k r := hlU
    change l⁻¹ᴴ * Hq k r * l⁻¹ = Hq k r
    calc _ = l⁻¹ᴴ * (lᴴ * Hq k r * l) * l⁻¹ := by rw [h1]
      _ = (l * l⁻¹)ᴴ * Hq k r * (l * l⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hq k r := by rw [hll]; simp
  have hm : ∀ i j : Fin (2 * r + k + 1), (j.val ≤ i.val ∨ (mid i ∧ mid j)) →
      (s * l⁻¹) i j = if i = j then 1 else 0 := by
    intro i j hij
    rw [← Matrix.one_apply, ← hll, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : j.val < x.val
    · rw [hiz x j h1]; simp
    · by_cases h2 : x.val < i.val
      · rw [hz i x h2, hltri (show id x < id i from h2)]
      · congr 1
        rw [hle]
        by_cases h3 : mid i ∧ mid x
        · rw [if_pos h3]
        · have : i = x := by
            apply Fin.ext
            simp only [mid] at h3 hij
            omega
          subst this
          simp
  have hfix : ∀ x, ¬ mid x → μ *ᵥ bvec x = bvec x := by
    intro x hx
    ext i
    have e1 : (μ *ᵥ bvec x) i = μ i x := by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
    have e2 : μ i x = if i = x then 1 else 0 := by
      have : ¬ (mid i ∧ mid x) := fun h => hx h.2
      exact if_neg this
    rw [e1, e2]
    simp [bvec, Pi.single_apply]
  refine ⟨s * l⁻¹, ⟨mul_mem hs hiU, fun a i hai => hm _ _ (Or.inl hai), fun i j h1 h2 h3 => hm _ _ ?_⟩,
    t, μ, ⟨hμ, fun a => ⟨?_, ?_⟩⟩, κ, hκ, ⟨fun i => ?_, fun i j hi hij => ?_, fun i hi => ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [mid]
    omega
  · have : ¬ mid (eI k r a) := by
      have := a.isLt
      simp only [mid, eI]; omega
    exact hfix _ this
  · have : ¬ mid (esI k r a) := by
      have := a.isLt
      simp only [mid, esI]; omega
    exact hfix _ this
  · exact lt_of_le_of_ne (norm_nonneg _) (hd0 i).symm
  · have : pr k r i = j := by
      have := pr_val k r i
      unfold outer at hi
      apply Fin.ext
      omega
    subst this
    exact hdn i
  · have : mid i := by
      unfold outer at hi
      simp only [mid]; omega
    simp [t, d, this]
  · have : mid (wI k r 0) := by simp [mid, wI]
    simp [t, d, this]
  · have : mid (wI k r 0) := by simp [mid, wI]
    simp [t, d, this]
  · simp only [κ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    have := hd0' i
    simp only [Pi.star_apply, RCLike.star_def]
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.conj_mul']
    field_simp
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (dg t), ← hl, Matrix.mul_assoc,
      Matrix.inv_mul_of_invertible, Matrix.mul_one]
end GlobalTheory.CompanionTheory.BesselLevi

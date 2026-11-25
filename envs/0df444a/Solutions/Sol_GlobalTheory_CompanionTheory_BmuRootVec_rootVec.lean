-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.rootVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:37.487847+00:00
-- url     : https://prove2.me/submissions/0e8b1aa0-5a6f-40d7-b1b6-940c481549ea

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_mul_single_mul_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_ex_of_mul_self_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_dg_Hq
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_rootE_lie
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_rootE_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_dg_rootE
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_norm_conj_rootE
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_col_of_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_frame_row
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_inv_row
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_inv_mulVec_fix
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold
import Theorems.Thm_Formalism_QuantumDeterminants_unitary_group_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuRootVec
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuRootVec
theorem _root_.solution : RootVec := by
  intro k r z Γ c hk hA hc
  obtain ⟨hΓ, hfix, ρ, hρ, hz⟩ := hA
  let κ : Fin r → ℂ := fun a => if a.val + 1 < r then (c a)⁻¹ else ((ρ : ℂ) * c a)⁻¹
  refine ⟨∑ a, 2 * ‖κ a‖, fun a d R hd hR hg => ?_⟩
  have ha := a.isLt
  have hHu : IsUnit (Hpk k r).det :=
    Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1
  obtain ⟨-, hmul, hinv⟩ := unitary_group_holds _ _ hHu
  have hgu := (hinv _ hg).1
  have hΓu : IsUnit Γ.det := by
    rw [det_mul, det_mul] at hgu
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hgu)
  have hR' : R * Rᴴ = 1 := mul_eq_one_comm.1 hR
  have hRq : Rᴴ * Hq k r * R = Hpk k r := by
    have h1 : (Γ * dg d * R)ᴴ * Hpk k r * (Γ * dg d * R) = Hpk k r := hg
    rw [← h1, ← dg_Hq hd, ← hΓ]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  set E := rootE k r a (κ a) with hE
  have hLie : Lie (Hpk k r) (Rᴴ * E * R) := by
    have h1 : Eᴴ * Hq k r + Hq k r * E = 0 := rootE_lie a (κ a)
    unfold Lie
    rw [← hRq]
    calc (Rᴴ * E * R)ᴴ * (Rᴴ * Hq k r * R) + Rᴴ * Hq k r * R * (Rᴴ * E * R)
        = Rᴴ * (Eᴴ * (R * Rᴴ) * Hq k r + Hq k r * (R * Rᴴ) * E) * R := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_add,
            Matrix.add_mul]
      _ = 0 := by rw [hR', Matrix.mul_one, Matrix.mul_one, h1, Matrix.mul_zero, Matrix.zero_mul]
  have hsq : Rᴴ * E * R * (Rᴴ * E * R) = 0 := by
    calc Rᴴ * E * R * (Rᴴ * E * R) = Rᴴ * (E * (R * Rᴴ) * E) * R := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hR', Matrix.mul_one, hE, rootE_sq hk, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨Rᴴ * E * R, hLie, (norm_conj_rootE hR a (κ a)).trans
    (Finset.single_le_sum (f := fun a => 2 * ‖κ a‖) (fun _ _ => by positivity) (Finset.mem_univ a)),
    fun τ => ?_⟩
  have hmem : Γ * dg d * R * ex (Rᴴ * E * R) τ * (Γ * dg d * R)⁻¹ ∈ UH (Hpk k r) :=
    hmul _ (hmul _ hg _ (ex_mem_of_lie hLie τ)) _ (hinv _ hg).2
  set α : ℝ := d (eI k r a) / d (nxt k r a) with hα
  have hform : Γ * dg d * R * ex (Rᴴ * E * R) τ * (Γ * dg d * R)⁻¹ =
      1 + ((α * τ : ℝ) : ℂ) • (Γ * E * Γ⁻¹) := by
    have h1 : Γ * dg d * R * (Rᴴ * E * R) = (α : ℂ) • (Γ * E * Γ⁻¹ * (Γ * dg d * R)) := by
      calc Γ * dg d * R * (Rᴴ * E * R) = Γ * (dg d * ((R * Rᴴ) * E)) * R := by
            simp only [Matrix.mul_assoc]
        _ = (α : ℂ) • (Γ * E * (Γ⁻¹ * Γ) * dg d * R) := by
            rw [hR', Matrix.one_mul, hE, dg_rootE hd, Matrix.nonsing_inv_mul Γ hΓu, Matrix.mul_one,
              Matrix.mul_smul, Matrix.smul_mul]
            simp only [Matrix.mul_assoc, hα]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [ex_of_mul_self_eq_zero _ hsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ hgu, Matrix.mul_smul, h1, smul_smul, Matrix.smul_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hgu]
    congr 2
    push_cast; ring
  have rowS : ∀ (b : Fin r) l, Γ (esI k r b) l = if l = esI k r b then 1 else 0 := fun b =>
    frame_row hΓ (i := eI k r b) (by have := b.isLt; simp only [eI]; omega)
      (by have := b.isLt; simp only [eI, esI]; omega) (hfix b).1
  have rowE : ∀ (b : Fin r) l, Γ (eI k r b) l = if l = eI k r b then 1 else 0 := fun b =>
    frame_row hΓ (i := esI k r b) (by have := b.isLt; simp only [esI]; omega)
      (by have := b.isLt; simp only [eI, esI]; omega) (hfix b).2
  have colI : ∀ (b : Fin r) i, Γ⁻¹ i (eI k r b) = if i = eI k r b then 1 else 0 := fun b =>
    col_of_mulVec (by
      have := inv_mulVec_fix hΓu (bvec (eI k r b))
      rwa [(hfix b).1] at this)
  have hent : ∀ i l, (Γ * E * Γ⁻¹) i l =
      (if i = eI k r a then κ a * Γ⁻¹ (nxt k r a) l else 0) -
        (if l = esI k r a then Γ i (nxtS k r a) * conj (κ a) else 0) := by
    intro i l
    rw [hE, rootE, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, mul_single_mul_entry,
      mul_single_mul_entry, col_of_mulVec (hfix a).1, inv_row hΓu (rowS a)]
    split_ifs <;> simp
  rw [hform] at hmem ⊢
  generalize Γ * E * Γ⁻¹ = M at hent hmem ⊢
  refine ⟨⟨hmem, fun b i hbi => ?_, fun i j h1 h2 h3 => ?_⟩, ?_⟩
  · have hb := b.isLt
    have : M i (eI k r b) = 0 := by
      rw [hent, colI, if_neg (c := eI k r b = esI k r a) (by simp only [eI, esI, Fin.ext_iff]; omega)]
      split_ifs with p q
      · exfalso; simp only [eI, nxt, Fin.ext_iff] at p q; omega
      · simp
      · simp
    simp [this, Matrix.one_apply]
  · have : M i j = 0 := by
      rw [hent, if_neg (by simp only [eI, Fin.ext_iff]; omega),
        if_neg (by simp only [esI, Fin.ext_iff]; omega), sub_zero]
    simp [this, Matrix.one_apply]
  · have hzr : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) →
        (∀ l, Γ i l = if l = i then 1 else 0) → z i = 0 := by
      intro i hi h
      have n1 : i ≠ wI k r 0 := by simp only [wI, Ne, Fin.ext_iff, Fin.val_zero]; omega
      have n2 : i ≠ wI k r (Fin.last k) := by simp only [wI, Ne, Fin.ext_iff, Fin.val_last]; omega
      rw [hz]
      simp [mulVec, dotProduct, h, bvec, n1, n2]
    have hzS : z (esI k r a) = 0 := hzr _ (by simp only [esI]; omega) (rowS a)
    have hell : ∀ b, c b * PI.BesselMapUniq.ellA k r z (1 + ((α * τ : ℝ) : ℂ) • M) b =
        if b = a then ((α * τ : ℝ) : ℂ) else 0 := by
      intro b
      have hb := b.isLt
      have hba : eI k r b = eI k r a ↔ b = a := by simp only [eI, Fin.ext_iff]
      unfold PI.BesselMapUniq.ellA
      by_cases h : b.val + 1 < r
      · rw [dif_pos h, Matrix.add_apply, Matrix.smul_apply, hent, colI,
          if_neg (c := _ = esI k r a) (by simp only [eI, esI, Fin.ext_iff]; omega),
          Matrix.one_apply_ne (by simp only [eI, Ne, Fin.ext_iff]; omega)]
        by_cases e : b = a
        · subst e
          have hn : nxt k r b = eI k r ⟨b.val + 1, h⟩ := rfl
          have := hc b
          simp only [if_true, κ, if_pos h, if_pos hn, smul_eq_mul]
          field_simp
          simp
        · simp [hba, e]
      · have hM : (M *ᵥ z) (eI k r b) = if b = a then κ a * (Γ⁻¹ *ᵥ z) (nxt k r a) else 0 := by
          simp only [mulVec, dotProduct, hent, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
            Finset.sum_ite_eq', Finset.mem_univ, if_true, hzS, mul_zero, sub_zero, hba]
          split_ifs
          · rw [Finset.mul_sum]; simp only [mul_assoc]
          · simp
        rw [dif_neg h, add_mulVec, one_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply, hM,
          hzr _ (by simp only [eI]; omega) (rowE b)]
        by_cases e : b = a
        · subst e
          have n1 : nxt k r b = wI k r 0 := by simp only [wI, nxt, Fin.ext_iff, Fin.val_zero]; omega
          have n2 : wI k r 0 ≠ wI k r (Fin.last k) := by
            simp only [wI, Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]; omega
          have hv : (Γ⁻¹ *ᵥ z) (nxt k r b) = ρ := by
            rw [hz, mulVec_smul, inv_mulVec_fix hΓu, n1]
            simp [bvec, n2]
          have := hc b
          have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
          simp only [if_true, κ, if_neg h, hv, smul_eq_mul]
          field_simp
          simp
        · simp [e]
    unfold PI.BesselMapUniq.psiGen
    simp only [hell, Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.ofReal_re]
end GlobalTheory.CompanionTheory.BmuRootVec

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.cartanQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:19.515111+00:00
-- url     : https://prove2.me/submissions/ab51b234-2cf8-4775-87a2-5eca94dfdd23

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_exists_unitary
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_two_le
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_exists_u
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_Hq_herm
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_Hq_outer
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_Hq_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_dg_bvec
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_dg_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_tor_pair
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_tor_inner
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_dg_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_UH_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_bvec_dot
import Theorems.Thm_CCRuleCW_UH_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCartan
open scoped ComplexOrder
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCartan
theorem _root_.solution : CartanQ := by
  intro k r hk μ hμ
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  have hUH : ∀ {m : ℕ} (H g : Matrix (Fin m) (Fin m) ℂ), g ∈ UH H ↔ gᴴ * H * g = H := fun _ _ => Iff.rfl
  obtain ⟨hμU, hμfix⟩ := hμ
  have hH : (Hq k r)ᴴ = Hq k r := Hq_herm k r
  have hHH : Hq k r * Hq k r = 1 := Hq_sq k r
  have hμU' : μᴴ * Hq k r * μ = Hq k r := (hUH _ _).mp hμU
  have hνμ : (Hq k r * μᴴ * Hq k r) * μ = 1 := by
    calc (Hq k r * μᴴ * Hq k r) * μ = Hq k r * (μᴴ * Hq k r * μ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hμU', hHH]
  have hμν : μ * (Hq k r * μᴴ * Hq k r) = 1 := mul_eq_one_comm.mp hνμ
  have hform : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, gᴴ * Hq k r * g = Hq k r →
      ∀ z z' : Fin (2 * r + k + 1) → ℂ, star (g *ᵥ z) ⬝ᵥ Hq k r *ᵥ (g *ᵥ z') = star z ⬝ᵥ Hq k r *ᵥ z' := by
    intro g hg z z'
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

  have hi0 : ((Formalism.QuantumDeterminants.wI k r 0 : Fin (2 * r + k + 1)) : ℕ) = r := by
    show r + ((0 : Fin (k + 1)) : ℕ) = r
    simp
  have hiL : ((Formalism.QuantumDeterminants.wI k r (Fin.last k) : Fin (2 * r + k + 1)) : ℕ) = r + k := by
    show r + ((Fin.last k : Fin (k + 1)) : ℕ) = r + k
    simp
  set i0 := Formalism.QuantumDeterminants.wI k r 0 with hi0def
  set iL := Formalism.QuantumDeterminants.wI k r (Fin.last k) with hiLdef
  have hne : i0 ≠ iL := fun h => by
    have := congrArg Fin.val h
    omega
  have ho0 : outer k r i0 := by show _ ∨ _; left; omega
  have hoL : outer k r iL := by show _ ∨ _; right; omega
  have hHe0 : Hq k r *ᵥ bvec i0 = bvec iL := Hq_outer k r iL i0 hoL (by omega)
  have hHeL : Hq k r *ᵥ bvec iL = bvec i0 := Hq_outer k r i0 iL ho0 (by omega)
  set v0 : Fin (2 * r + k + 1) → ℂ := bvec i0 - bvec iL with hv0
  have hv0H : star v0 ⬝ᵥ Hq k r *ᵥ v0 = -2 := by
    rw [hv0, Matrix.mulVec_sub, hHe0, hHeL, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      bvec_dot, bvec_dot, bvec_dot, bvec_dot, if_pos rfl, if_pos rfl, if_neg hne, if_neg (Ne.symm hne)]
    norm_num
  set y := (Hq k r * μᴴ * Hq k r) *ᵥ v0 with hy
  have hμy : μ *ᵥ y = v0 := by rw [hy, Matrix.mulVec_mulVec, hμν, Matrix.one_mulVec]
  have hyH : star y ⬝ᵥ Hq k r *ᵥ y = -2 := by
    rw [← hform μ hμU' y y, hμy, hv0H]
  obtain ⟨N, hN2, hyN⟩ := two_le (Hq k r) hH hHH y hyH
  obtain ⟨u, hu0, hu1, huN⟩ := exists_u N hN2
  have hu : u ≠ 0 := ne_of_gt hu0
  have hg1U : dg (tor k r u⁻¹) ∈ UH (Hq k r) := dg_mem k r hk u⁻¹ (inv_ne_zero hu)
  have hg1U' := (hUH _ _).mp hg1U
  have ht0 : tor k r u⁻¹ i0 = u⁻¹ := by
    unfold tor
    rw [if_pos hi0]
  have htL : tor k r u⁻¹ iL = u := by
    unfold tor
    rw [if_neg (by omega), if_pos hiL, inv_inv]
  set xv := dg (tor k r u⁻¹) *ᵥ v0 with hxvdef
  have hxv : xv = ((u⁻¹ : ℝ) : ℂ) • bvec i0 - ((u : ℝ) : ℂ) • bvec iL := by
    rw [hxvdef, hv0, Matrix.mulVec_sub, dg_bvec, dg_bvec, ht0, htL]
  have hxn : star xv ⬝ᵥ xv = star y ⬝ᵥ y := by
    rw [hyN, hxv, star_sub, star_smul, star_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
      smul_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, dotProduct_smul,
      dotProduct_smul, bvec_dot, bvec_dot, bvec_dot, bvec_dot, if_pos rfl, if_pos rfl, if_neg hne, if_neg (Ne.symm hne)]
    simp only [smul_eq_mul, mul_one, mul_zero, sub_zero, zero_sub, sub_neg_eq_add, Complex.star_def,
      Complex.conj_ofReal]
    rw [← huN]
    push_cast
    ring
  have hxH : star xv ⬝ᵥ Hq k r *ᵥ xv = star y ⬝ᵥ Hq k r *ᵥ y := by
    rw [hxvdef, hform _ hg1U' v0 v0, hv0H, hyH]
  obtain ⟨K', hK'u, hK'H, hK'x, hK'f⟩ := exists_unitary (Hq k r) hH hHH xv y hxn hxH
  have hK'u' : K' * K'ᴴ = 1 := mul_eq_one_comm.mp hK'u
  have hK'U : K' ∈ UH (Hq k r) := by
    rw [hUH, Matrix.mul_assoc, hK'H, ← Matrix.mul_assoc, hK'u, Matrix.one_mul]

  have hxz : ∀ j : Fin (2 * r + k + 1), (j : ℕ) ≠ r → (j : ℕ) ≠ r + k → star xv ⬝ᵥ bvec j = 0 := by
    intro j hj1 hj2
    have h1 : i0 ≠ j := fun h => hj1 (by rw [← h]; exact hi0)
    have h2 : iL ≠ j := fun h => hj2 (by rw [← h]; exact hiL)
    rw [hxv, star_sub, star_smul, star_smul, sub_dotProduct, smul_dotProduct, smul_dotProduct, bvec_dot, bvec_dot,
      if_neg h1, if_neg h2, smul_zero, smul_zero, sub_zero]
  have hvz : ∀ j : Fin (2 * r + k + 1), (j : ℕ) ≠ r → (j : ℕ) ≠ r + k → star v0 ⬝ᵥ bvec j = 0 := by
    intro j hj1 hj2
    have h1 : i0 ≠ j := fun h => hj1 (by rw [← h]; exact hi0)
    have h2 : iL ≠ j := fun h => hj2 (by rw [← h]; exact hiL)
    rw [hv0, star_sub, sub_dotProduct, bvec_dot, bvec_dot, if_neg h1, if_neg h2, sub_zero]

  have hfixK : ∀ a : Fin r, K' *ᵥ bvec (Formalism.QuantumDeterminants.eI k r a) = bvec (Formalism.QuantumDeterminants.eI k r a) ∧
      K' *ᵥ bvec (Formalism.QuantumDeterminants.esI k r a) = bvec (Formalism.QuantumDeterminants.esI k r a) := by
    intro a
    have ha := a.isLt
    have he : ((Formalism.QuantumDeterminants.eI k r a : Fin (2 * r + k + 1)) : ℕ) = a := rfl
    have hes : ((Formalism.QuantumDeterminants.esI k r a : Fin (2 * r + k + 1)) : ℕ) = 2 * r + k - a := rfl
    have hoe : outer k r (Formalism.QuantumDeterminants.eI k r a) := by show _ ∨ _; left; omega
    have hoes : outer k r (Formalism.QuantumDeterminants.esI k r a) := by show _ ∨ _; right; omega
    have hHe : Hq k r *ᵥ bvec (Formalism.QuantumDeterminants.eI k r a) = bvec (Formalism.QuantumDeterminants.esI k r a) :=
      Hq_outer k r _ _ hoes (by omega)
    have hHes : Hq k r *ᵥ bvec (Formalism.QuantumDeterminants.esI k r a) = bvec (Formalism.QuantumDeterminants.eI k r a) :=
      Hq_outer k r _ _ hoe (by omega)
    have hye : star y ⬝ᵥ bvec (Formalism.QuantumDeterminants.eI k r a) = 0 := by
      rw [← hHes, ← hform μ hμU' y _, hμy, (hμfix a).2, hHes]
      exact hvz _ (by omega) (by omega)
    have hyes : star y ⬝ᵥ bvec (Formalism.QuantumDeterminants.esI k r a) = 0 := by
      rw [← hHe, ← hform μ hμU' y _, hμy, (hμfix a).1, hHe]
      exact hvz _ (by omega) (by omega)
    constructor
    · exact hK'f _ (hxz _ (by omega) (by omega)) hye (by rw [hHe]; exact hxz _ (by omega) (by omega))
        (by rw [hHe]; exact hyes)
    · exact hK'f _ (hxz _ (by omega) (by omega)) hyes (by rw [hHes]; exact hxz _ (by omega) (by omega))
        (by rw [hHes]; exact hye)
  have hg1fix : ∀ j : Fin (2 * r + k + 1), (j : ℕ) ≠ r → (j : ℕ) ≠ r + k →
      dg (tor k r u⁻¹) *ᵥ bvec j = bvec j := by
    intro j hj1 hj2
    rw [dg_bvec]
    have : tor k r u⁻¹ j = 1 := by
      unfold tor
      rw [if_neg hj1, if_neg hj2]
    rw [this, Complex.ofReal_one, one_smul]
  refine ⟨μ * K' * dg (tor k r u⁻¹), ⟨UH_mul (UH_mul hμU hK'U) hg1U, fun a => ?_⟩, tor k r u, K'ᴴ, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have ha := a.isLt
    have he : ((Formalism.QuantumDeterminants.eI k r a : Fin (2 * r + k + 1)) : ℕ) = a := rfl
    have hes : ((Formalism.QuantumDeterminants.esI k r a : Fin (2 * r + k + 1)) : ℕ) = 2 * r + k - a := rfl
    constructor
    · rw [← Matrix.mulVec_mulVec, hg1fix _ (by omega) (by omega), ← Matrix.mulVec_mulVec, (hfixK a).1,
        (hμfix a).1]
    · rw [← Matrix.mulVec_mulVec, hg1fix _ (by omega) (by omega), ← Matrix.mulVec_mulVec, (hfixK a).2,
        (hμfix a).2]
  · rw [hUH, Matrix.conjTranspose_conjTranspose, ← hK'H, Matrix.mul_assoc, hK'u', Matrix.mul_one]
  · rw [← Matrix.mulVec_mulVec, ← hxvdef, ← Matrix.mulVec_mulVec, hK'x, hμy]
  · refine ⟨fun i => ?_, fun i j hi hij => tor_pair k r hk u hu i j hij, fun i hi => tor_inner k r u i hi, ?_⟩
    · unfold tor
      split_ifs
      · exact hu0
      · exact inv_pos.mpr hu0
      · exact one_pos
    · show tor k r u i0 ≤ 1
      unfold tor
      rw [if_pos hi0]
      exact hu1
  · intro a
    have ha := a.isLt
    have he : ((Formalism.QuantumDeterminants.eI k r a : Fin (2 * r + k + 1)) : ℕ) = a := rfl
    unfold tor
    rw [if_neg (by omega), if_neg (by omega)]
  · rw [Matrix.conjTranspose_conjTranspose, hK'u']
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (dg (tor k r u⁻¹)), dg_mul k r u hu, Matrix.one_mul, hK'u', Matrix.mul_one]
end GlobalTheory.CompanionTheory.BesselCartan

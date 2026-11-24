-- Prove2me | solution 1 for GlobalTheory.ColengthDifferent.colength_dvd_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:06.254083+00:00
-- url     : https://prove2.me/submissions/a85d20a1-38d5-4be7-96f1-d7d5a0af57ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero
import Theorems.Thm_GlobalTheory_ColengthDifferent_injective_of_charZero
import Theorems.Thm_GlobalTheory_ColengthDifferent_exists_mul_traceDual
import Theorems.Thm_GlobalTheory_ColengthDifferent_mul_proj
import Theorems.Thm_GlobalTheory_ColengthDifferent_sum_proj_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ColengthDifferent
theorem _root_.solution (F T : Type) [Field F] [CharZero F] [CommRing T] [IsDomain T]
    [Algebra T F] [IsFractionRing T F] (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι → (𝓞 E →+* T))
    (m : ι → ℕ) (g : ℕ) (e : Fin g ≃ Σ i : ι, Fin (m i)) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T)
    (u : ∀ i, Fin (m i) → (Fin g → T)) (hτ : Function.Injective τ)
    (hcard : Fintype.card ι = Module.finrank ℚ E)
    (hsp : ∀ i (w : Fin g → T), (∀ a, (A a).mulVec w = τ i a • w) →
      ∃ cf : Fin (m i) → T, w = ∑ k, cf k • u i k)
    (δ : ι → 𝓞 E) (hδ : ∀ i, δ i ∈ differentIdeal ℤ (𝓞 E)) (hδ0 : ∀ i, δ i ≠ 0) :
    (Matrix.of fun j k : Fin g => u (e j).1 (e j).2 k).det ∣ ∏ i, τ i (δ i) ^ m i := by
  classical
  set ω := RingOfIntegers.basis E
  choose c hc using fun i k => exists_mul_traceDual (hδ i) k
  let P : ι → Matrix (Fin g) (Fin g) T := fun i => ∑ k, τ i (c i k) • A (ω k)
  have hPv : ∀ i j a, (A a).mulVec ((P i).mulVec (Pi.single j 1)) =
      τ i a • (P i).mulVec (Pi.single j 1) := by
    intro i j a
    rw [Matrix.mulVec_mulVec, mul_proj (τ i) A (hc i) a, Matrix.smul_mulVec]
  choose cf hcf using fun i j => hsp i _ (hPv i j)
  have hF := IsFractionRing.injective T F
  let g' : ι → 𝓞 E →+* F := fun i => (algebraMap T F).comp (τ i)
  have hg' : ∀ i, Function.Injective (g' i) := fun i => injective_of_charZero _
  let σ : ι → E →+* F := fun i => IsFractionRing.lift (hg' i)
  have hσ : ∀ i x, σ i (algebraMap (𝓞 E) E x) = algebraMap T F (τ i x) :=
    fun i x => IsFractionRing.lift_algebraMap _ _
  have hσinj : Function.Injective σ := by
    intro i j h
    apply hτ
    ext x
    apply hF
    rw [← hσ, ← hσ, h]
  let AF : 𝓞 E →+* Matrix (Fin g) (Fin g) F := (algebraMap T F).mapMatrix.comp A
  have hone := sum_proj_eq_one σ hσinj hcard AF δ hδ0 c hc
  simp only [hσ] at hone
  have hPF : ∀ i, (P i).map (algebraMap T F) = ∑ k, algebraMap T F (τ i (c i k)) • AF (ω k) := by
    intro i
    ext r s
    simp only [P]
    rw [Matrix.map_apply, Matrix.sum_apply, Matrix.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, AF, RingHom.comp_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply]
  set d : ι → F := fun i => algebraMap T F (τ i (δ i)) with hd_def
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    simp only [hd_def]
    rw [← hσ, map_ne_zero_iff _ (σ i).injective]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mpr (hδ0 i)
  have hent : ∀ r s, ∑ i, (d i)⁻¹ * algebraMap T F (P i r s) = (1 : Matrix (Fin g) (Fin g) F) r s := by
    intro r s
    rw [← hone, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, ← hPF, Matrix.map_apply, smul_eq_mul]
  have hcol : ∀ i j k, P i k j = ∑ l, cf i j l * u i l k := by
    intro i j k
    have := congrFun (hcf i j) k
    rw [Matrix.mulVec_single_one] at this
    simpa [Finset.sum_apply] using this
  set G : Matrix (Fin g) (Fin g) T := Matrix.of fun j r => cf (e r).1 j (e r).2 with hG
  set U : Matrix (Fin g) (Fin g) T := Matrix.of fun r k => u (e r).1 (e r).2 k with hU
  have hmat : G.map (algebraMap T F) * Matrix.diagonal (fun r => (d (e r).1)⁻¹) *
      U.map (algebraMap T F) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.map_apply, hG, hU, Matrix.of_apply]
    rw [Equiv.sum_comp e (fun x => algebraMap T F (cf x.1 j x.2) * (d x.1)⁻¹ *
      algebraMap T F (u x.1 x.2 k)), Fintype.sum_sigma]
    calc _ = ∑ i, (d i)⁻¹ * algebraMap T F (P i k j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcol, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [map_mul]
          ring
      _ = _ := by
          rw [hent, Matrix.one_apply, Matrix.one_apply]
          simp [eq_comm]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_one,
    ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det,
    Finset.prod_inv_distrib, mul_right_comm,
    mul_inv_eq_one₀ (Finset.prod_ne_zero_iff.mpr fun r _ => hd _)] at hdet
  have hprod : ∏ r : Fin g, τ (e r).1 (δ (e r).1) = ∏ i, τ i (δ i) ^ m i := by
    rw [Equiv.prod_comp e (fun x => τ x.1 (δ x.1)), Fintype.prod_sigma]
    simp
  have hkey : G.det * U.det = ∏ i, τ i (δ i) ^ m i := by
    apply hF
    rw [← hprod, map_mul, map_prod, hdet]
  exact Dvd.intro_left _ hkey
end GlobalTheory.ColengthDifferent

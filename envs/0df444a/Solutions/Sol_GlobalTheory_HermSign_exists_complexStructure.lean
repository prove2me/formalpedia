-- Prove2me | solution 1 for GlobalTheory.HermSign.exists_complexStructure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:59:37.835304+00:00
-- url     : https://prove2.me/submissions/ed45e451-eb70-4170-9ff9-9aac175b169e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_HermSign_trace_real_blocks
import Theorems.Thm_GlobalTheory_HermSign_exists_blocks
import Theorems.Thm_GlobalTheory_HermSign_induction_integers
import Theorems.Thm_GlobalTheory_HermSign_realMap_realAct
import Theorems.Thm_GlobalTheory_HermSign_realMap_surjective
import Theorems.Thm_GlobalTheory_HermSign_baseChange_EF
import Theorems.Thm_GlobalTheory_CMType_eq_zero_of_sum_re_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {r : ℕ}
  (Φ : CMType E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
namespace GlobalTheory.HermSign
theorem _root_.solution (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (hΦ : ∀ σ, σ ∈ Φ ↔ σ (H.rt : E) = H.rt0) (τ : Φ) :
    r = D.p + D.q ∧ ∃ M : Matrix (Fin r) (Fin r) ℂ, M * M = -1 ∧
      (∀ u v : Fin r → ℂ, (τ.1 ξ * ((M *ᵥ u) ⬝ᵥ (Gm.map τ.1) *ᵥ star (M *ᵥ v))).re =
        (τ.1 ξ * (u ⬝ᵥ (Gm.map τ.1) *ᵥ star v)).re) ∧
      (∀ u : Fin r → ℂ, u ≠ 0 → 0 < (τ.1 ξ * ((M *ᵥ u) ⬝ᵥ (Gm.map τ.1) *ᵥ star u)).re) ∧
      M.trace = Complex.I * ((D.p : ℂ) - D.q) := by
  classical
  obtain ⟨J, hJ2, hJinv, hJpos, hJ⟩ := D.dom
  have hform := baseChange_EF D Φ φ ξ Gm hEF
  have hinj : Function.Injective (realMap D Φ φ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    have := hJpos x h
    rw [hform, hx] at this
    simp at this
  let e : ℝ ⊗[ℤ] D.La ≃ₗ[ℝ] (Φ → Fin r → ℂ) :=
    LinearEquiv.ofBijective (realMap D Φ φ) ⟨hinj, realMap_surjective D Φ φ hspan⟩
  have he : ∀ x, e x = realMap D Φ φ x := fun _ => rfl
  have hA : ∀ a : 𝓞 E, J ∘ₗ realAct D a = realAct D a ∘ₗ J ∧
      LinearMap.trace ℝ _ (realAct D a) = 2 * (∑ σ : Φ, ((D.p : ℂ) * σ.1 (a : E) +
        (D.q : ℂ) * conj (σ.1 (a : E)))).re ∧
      LinearMap.trace ℝ _ (J ∘ₗ realAct D a) = -2 * (∑ σ : Φ, ((D.p : ℂ) * σ.1 (a : E) +
        (D.q : ℂ) * conj (σ.1 (a : E)))).im := by
    intro a
    refine hJ a _ _ (fun x => by simp [realAct]) ?_
    exact (Finset.sum_subtype (p := fun σ => σ ∈ Φ) _
      (fun σ => by rw [Finset.mem_filter]; simp [hΦ])
      (fun σ : E →+* ℂ => (D.p : ℂ) * σ (a : E) + (D.q : ℂ) * conj (σ (a : E)))).symm
  have hJe : ∀ x, e.conj J (e x) = e (J x) := fun x => by simp [LinearEquiv.conj_apply]
  have hcomm : ∀ (c : Φ → ℂ) u, e.conj J (c • u) = c • e.conj J u := by
    refine induction_integers Φ _ ?_ ?_ ?_
    · intro a u
      obtain ⟨x, rfl⟩ := e.surjective u
      rw [hJe, he, he, ← realMap_realAct, ← realMap_realAct, ← he, ← he, hJe]
      exact congrArg e (LinearMap.congr_fun (hA a).1 x)
    · intro c c' h h' u
      rw [add_smul, map_add, h, h', add_smul]
    · intro t c h u
      rw [smul_assoc, map_smul, h, smul_assoc]
  obtain ⟨M, hM⟩ := exists_blocks (e.conj J) hcomm
  have hMe : ∀ x σ, realMap D Φ φ (J x) σ = M σ *ᵥ realMap D Φ φ x σ := fun x σ => by
    rw [← he, ← he, ← hJe, hM]
  have hsingle : ∀ u : Fin r → ℂ, realMap D Φ φ (e.symm (Pi.single τ u)) = Pi.single τ u :=
    fun u => e.apply_symm_apply _
  have hsum : ∀ (f : Φ → ℝ), (∀ σ, σ ≠ τ → f σ = 0) → ∑ σ, f σ = f τ := fun f hf =>
    Finset.sum_eq_single τ (fun σ _ h => hf σ h) (by simp)
  clear hJ hcomm
  refine ⟨?_, M τ, ?_, ?_, ?_, ?_⟩
  · have h1 := (hA 1).2.1
    rw [← LinearMap.trace_conj' _ e, trace_real_blocks (fun _ => 1) _ (fun u σ => by
      obtain ⟨x, rfl⟩ := e.surjective u
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      simp [he, realMap_realAct])] at h1
    have hc : (Fintype.card Φ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp at h1
    have : (r : ℝ) = D.p + D.q := mul_left_cancel₀ hc (by linarith)
    exact_mod_cast this
  · refine toLin'.injective (LinearMap.ext fun u => ?_)
    have := hMe (J (e.symm (Pi.single τ u))) τ
    rw [hJ2, hMe, map_neg, hsingle] at this
    simpa [neg_mulVec] using this.symm
  · intro u v
    have := hJinv (e.symm (Pi.single τ u)) (e.symm (Pi.single τ v))
    rw [hform, hform, hsum _ (fun σ h => by simp [hMe, hsingle, h]),
      hsum _ (fun σ h => by simp [hsingle, h]), hMe, hMe, hsingle, hsingle] at this
    simp only [Pi.single_eq_same] at this
    linarith
  · intro u hu
    have := hJpos (e.symm (Pi.single τ u)) (by simpa using hu)
    rw [hform, hsum _ (fun σ h => by simp [hsingle, h]), hMe, hsingle] at this
    simp only [Pi.single_eq_same] at this
    linarith
  · have := Φ.eq_zero_of_sum_re_eq_zero
      (fun σ => (M σ).trace - Complex.I * ((D.p : ℂ) - D.q)) fun a => by
        have h1 := (hA a).2.2
        rw [← LinearMap.trace_conj' _ e, trace_real_blocks (fun σ => σ.1 (a : E) • M σ) _
          (fun u σ => by
            obtain ⟨x, rfl⟩ := e.surjective u
            simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
              LinearEquiv.symm_apply_apply]
            simp only [he, hMe, realMap_realAct, Pi.smul_apply', mulVec_smul, smul_mulVec]), Complex.im_sum, Finset.mul_sum,
          ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
        have h2 : 2 * ∑ σ : Φ, (σ.1 (a : E) *
            ((M σ).trace - Complex.I * ((D.p : ℂ) - D.q))).re = 0 := by
          rw [← h1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp [trace_smul]
          ring
        linarith
    exact sub_eq_zero.1 (congrFun this τ)
end GlobalTheory.HermSign

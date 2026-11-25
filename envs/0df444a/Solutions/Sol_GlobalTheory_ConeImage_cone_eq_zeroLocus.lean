-- Prove2me | solution 1 for GlobalTheory.ConeImage.cone_eq_zeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:02:18.726851+00:00
-- url     : https://prove2.me/submissions/3fa4ddf7-b841-465c-abc0-9f5b6f61ec23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
import Theorems.Thm_GlobalTheory_ConeImage_exists_nhds_subset_range
import Theorems.Thm_GlobalTheory_ConeImage_differentiable_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage
namespace GlobalTheory.ConeImage
theorem _root_.solution {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : ι → E → ℂ} (hf : ∀ c, Differentiable ℂ (f c))
    (h0 : ∀ z, ∃ c, f c z ≠ 0)
    (htan : ∀ (z ξ : E) (γ : ℂ), (∀ c, fderiv ℂ (f c) z ξ = γ * f c z) → ξ = 0)
    (hcl : IsClosed {p : ι → ℂ | ∃ (t : ℂ) (z : E), p = fun c => t * f c z})
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), MvPolynomial.eval (fun c => t * f c z) F = 0)
    [IsDomain (MvPolynomial ι ℂ ⧸ I)] {d : ℕ} (hd : d ≤ Module.finrank ℂ E + 1)
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial ι ℂ ⧸ I) (hj : Function.Injective j)
    (a : MvPolynomial ι ℂ ⧸ I) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q : MvPolynomial (Fin d) ℂ) (hq : q ≠ 0) (hp : p.eval₂ j.toRingHom a = 0)
    (hpq : Polynomial.C q ∈ Ideal.span {p, p.derivative})
    (hb : ∀ b, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a)
    (hconn : ∀ b : MvPolynomial ι ℂ ⧸ I, b ≠ 0 → IsConnected {x : (MvPolynomial ι ℂ ⧸ I) → ℂ |
      ∃ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ = x ∧ x b ≠ 0})
    (hdense : ∀ b : MvPolynomial ι ℂ ⧸ I, b ≠ 0 → {x : (MvPolynomial ι ℂ ⧸ I) → ℂ |
      ∃ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆
      closure {x : (MvPolynomial ι ℂ ⧸ I) → ℂ |
        ∃ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ = x ∧ x b ≠ 0})
    (y : ι → ℂ) (hy : ∀ F ∈ I, MvPolynomial.eval y F = 0) :
    ∃ (t : ℂ) (z : E), y = fun c => t * f c z := by
  let pt : ∀ y : ι → ℂ, (∀ F ∈ I, MvPolynomial.eval y F = 0) → (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ :=
    fun y hy => Ideal.Quotient.liftₐ I (MvPolynomial.aeval y) fun F hF => hy F hF
  have hpt : ∀ y hy F, pt y hy (Ideal.Quotient.mk I F) = MvPolynomial.eval y F := by
    intro y hy F
    rfl
  let Φ : ℂ × E → (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ :=
    fun w => pt (fun c => w.1 * f c w.2) fun F hF => (hI F).mp hF _ _
  have hΦ : ∀ w F, Φ w (Ideal.Quotient.mk I F) = MvPolynomial.eval (fun c => w.1 * f c w.2) F :=
    fun w F => hpt _ _ F
  have hΦX : ∀ w c, Φ w (Ideal.Quotient.mk I (MvPolynomial.X c)) = w.1 * f c w.2 := by
    intro w c; rw [hΦ, MvPolynomial.eval_X]
  have hΦd : ∀ b, Differentiable ℂ fun w => Φ w b := by
    intro b
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [hΦ]
    exact differentiable_eval (fun c => differentiable_fst.mul ((hf c).comp differentiable_snd)) F
  have hne : ∀ b, b ≠ 0 → ∃ w, Φ w b ≠ 0 := by
    intro b hb
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_contra! h
    exact hb (Ideal.Quotient.eq_zero_iff_mem.mpr ((hI F).mpr fun t z => hΦ (t, z) F ▸ h (t, z)))
  obtain ⟨c₀, hc₀⟩ := h0 0
  have hX : Ideal.Quotient.mk I (MvPolynomial.X c₀) ≠ 0 := by
    intro h
    have := hΦX (1, 0) c₀
    rw [h, map_zero, one_mul] at this
    exact hc₀ this.symm
  have hb0 : j q * Ideal.Quotient.mk I (MvPolynomial.X c₀) ≠ 0 :=
    mul_ne_zero (fun h => hq (hj (h.trans (map_zero j).symm))) hX
  set b₀ := j q * Ideal.Quotient.mk I (MvPolynomial.X c₀) with hb₀
  set D := {x : (MvPolynomial ι ℂ ⧸ I) → ℂ |
    ∃ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ = x ∧ x b₀ ≠ 0} with hD
  let Y : Set ((MvPolynomial ι ℂ ⧸ I) → ℂ) :=
    (fun x c => x (Ideal.Quotient.mk I (MvPolynomial.X c))) ⁻¹'
      {p : ι → ℂ | ∃ (t : ℂ) (z : E), p = fun c => t * f c z}
  have hY : IsClosed Y := hcl.preimage (by fun_prop)
  have hYΦ : ∀ w, ⇑(Φ w) ∈ Y := fun w => ⟨w.1, w.2, funext fun c => hΦX w c⟩
  have hYΦ' : ∀ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ ∈ Y → ∃ w, φ = Φ w := by
    rintro φ ⟨t, z, h⟩
    refine ⟨(t, z), Ideal.Quotient.algHom_ext ℂ (MvPolynomial.algHom_ext fun c => ?_)⟩
    exact (congrFun h c).trans (hΦX (t, z) c).symm
  have hDY : D ⊆ Y := by
    haveI : PreconnectedSpace D := Subtype.preconnectedSpace (hconn b₀ hb0).isPreconnected
    have hclopen : IsClopen (Subtype.val ⁻¹' Y : Set D) := by
      refine ⟨hY.preimage continuous_subtype_val, isOpen_iff_mem_nhds.mpr ?_⟩
      rintro ⟨_, φ, rfl, hφ⟩ hφY
      obtain ⟨w₀, rfl⟩ := hYΦ' φ hφY
      have hφ' := hφ
      rw [hb₀, map_mul, hΦX] at hφ'
      have ht : w₀.1 ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hφ')
      obtain ⟨U, hU, hU'⟩ := exists_nhds_subset_range (W := ℂ × E)
        (by rw [Module.finrank_prod, Module.finrank_self, add_comm]; exact hd)
        j a p q hp hpq hb Φ hΦd w₀ (left_ne_zero_of_mul hφ') (by
          intro ξ hξ
          have key : ∀ c, ξ.1 * f c w₀.2 + w₀.1 * fderiv ℂ (f c) w₀.2 ξ.2 = 0 := by
            intro c
            have h1 := hξ (Ideal.Quotient.mk I (MvPolynomial.X c))
            simp only [hΦX] at h1
            have h2 := (hasFDerivAt_fst (𝕜 := ℂ) (p := w₀)).mul
              (((hf c) w₀.2).hasFDerivAt.comp w₀ hasFDerivAt_snd)
            have h3 : fderiv ℂ (fun w : ℂ × E => w.1 * f c w.2) w₀ = _ := h2.fderiv
            rw [h3] at h1
            simp at h1
            linear_combination h1
          have h2 : ξ.2 = 0 := htan w₀.2 ξ.2 (-ξ.1 / w₀.1) fun c => by
            field_simp
            linear_combination key c
          obtain ⟨c, hc⟩ := h0 w₀.2
          have h1 := key c
          rw [h2, map_zero, mul_zero, add_zero] at h1
          exact Prod.ext ((mul_eq_zero.mp h1).resolve_right hc) h2)
      refine mem_of_superset (continuous_subtype_val.continuousAt hU) ?_
      rintro ⟨_, ψ, rfl, hψ⟩ hψU
      obtain ⟨w, rfl⟩ := hU' ψ hψU
      exact hYΦ w
    obtain ⟨w, hw⟩ := hne b₀ hb0
    have := hclopen.eq_univ ⟨⟨Φ w, Φ w, rfl, hw⟩, hYΦ w⟩
    intro x hx
    exact this.ge (Set.mem_univ (⟨x, hx⟩ : D))
  have := closure_minimal hDY hY (hdense b₀ hb0 ⟨pt y hy, rfl, by simp⟩)
  obtain ⟨t, z, h⟩ := this
  refine ⟨t, z, ?_⟩
  rw [← h]
  ext c
  simp only [hpt, MvPolynomial.eval_X]
end GlobalTheory.ConeImage

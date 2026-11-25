-- Prove2me | solution 1 for GlobalTheory.model_in_same_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:57:27.830905+00:00
-- url     : https://prove2.me/submissions/a6c12349-9ac8-4db5-b554-1219318193f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ConjEqNegOfSqEqNegNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace
import Theorems.Thm_P2M_GlobalTheory_OneSpace_rt_sq__7b7c62802849
import Theorems.Thm_GlobalTheory_OneSpace_conj_of_sq
import Theorems.Thm_GlobalTheory_OneSpace_emb_rt_sq
import Theorems.Thm_GlobalTheory_OneSpace_cc_rt
import Theorems.Thm_GlobalTheory_OneSpace_rt_ne
import Theorems.Thm_GlobalTheory_OneSpace_det_gram
import Theorems.Thm_GlobalTheory_OneSpace_gram_conj
import Theorems.Thm_GlobalTheory_OneSpace_cc_det
import Theorems.Thm_GlobalTheory_OneSpace_im_ne
import Theorems.Thm_GlobalTheory_DetIdeal_det_ideal
import Theorems.Thm_GlobalTheory_HermModel_rank_integral_selfDual
import Theorems.Thm_GlobalTheory_T_signature_hermitian_model_of_datum
import Theorems.Thm_GlobalTheory_exists_herm_coord_of_datum
import Theorems.Thm_GlobalTheory_local_norm_of_ideal_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.OneSpace
namespace GlobalTheory
theorem _root_.solution : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ γ : GL (Fin r) E, ∀ x y, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p → D'.q = D.q → FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∃ φ' : D'.La →ₗ[𝓞 E] (Fin r → E), (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y))) := by
  intro hL hH E _ _ _ H D D' r ξ Gm φ hp hq hξ hM
  have hr : r = D'.p + D'.q := by
    rw [hp, hq]
    exact (GlobalTheory.HermModel.rank_integral_selfDual E H D r ξ Gm φ hξ hM).1
  by_cases h0 : ξ = 0
  · obtain ⟨Gm', ψ, hinj, hspan, -, -, -⟩ :=
      GlobalTheory.exists_herm_coord_of_datum E H D' (H.rt : E) (cc_rt H) (rt_ne H) r hr
    obtain ⟨-, hs, hG, hdet, hEF⟩ := hM
    have hz : ∀ x : D.La, x = 0 := by
      intro x
      apply D.unimod.1
      ext y
      have := hEF x y
      rw [h0, zero_mul, map_zero] at this
      rw [map_zero, LinearMap.zero_apply]
      exact_mod_cast this
    have hz' : ∀ v : Fin r → E, v = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range φ) := hs ▸ Submodule.mem_top
      have : Submodule.span E (Set.range φ) ≤ ⊥ := by
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        rw [hz x, map_zero]
        exact Submodule.zero_mem _
      exact (Submodule.mem_bot E).1 (this hv)
    refine ⟨ψ, hinj, hspan, hG, hdet, fun x y => ?_⟩
    have : x = 0 := hinj ((hz' _).trans (hz' _).symm)
    rw [this, h0]
    simp
  obtain ⟨Gm', ψ, hM'⟩ := GlobalTheory.exists_herm_coord_of_datum E H D' ξ hξ h0 r hr
  have hsΨ : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) := by
    intro τ hτ
    have s1 := GlobalTheory.T.signature_hermitian_model_of_datum E H D r ξ Gm φ hξ hM τ hτ
    have s2 := GlobalTheory.T.signature_hermitian_model_of_datum E H D' r ξ Gm' ψ hξ hM' τ hτ
    rw [hp, hq] at s2
    rcases lt_or_gt_of_ne (im_ne τ hξ h0) with h | h
    · exact ⟨_, s1.2 h, s2.2 h⟩
    · exact ⟨_, s1.1 h, s2.1 h⟩
  have hs : ∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) := by
    intro τ
    have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [emb_rt_sq, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact hsΨ τ h
    · obtain ⟨p0, a, b⟩ := hsΨ (ComplexEmbedding.conjugate τ) (by
        rw [ComplexEmbedding.conjugate_coe_eq, conj_of_sq H.d_prime.pos (emb_rt_sq H τ), h, neg_neg])
      exact ⟨p0, gram_conj τ _ _ a, gram_conj τ _ _ b⟩
  have hI := GlobalTheory.DetIdeal.det_ideal E H D D' r ξ Gm φ Gm' ψ hξ hM hM'
  obtain ⟨-, -, hG, hdet, -⟩ := hM
  obtain ⟨hinj, hspan, hG', hdet', hEF⟩ := hM'
  have hx : Gm'.det / Gm.det ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
    have e1 := cc_det Gm hG
    have e2 := cc_det Gm' hG'
    rw [FD.cc] at e1 e2
    rw [e1, e2]
  set x : maximalRealSubfield E := ⟨Gm'.det / Gm.det, hx⟩ with hxdef
  have hx0 : x ≠ 0 := by
    intro h
    exact div_ne_zero hdet' hdet (congrArg Subtype.val h)
  have hloc := GlobalTheory.local_norm_of_ideal_norm E H x hx0 hI
  have hreal : ∀ σ : maximalRealSubfield E →+* ℝ, ∃ a b : ℝ,
      σ x = a ^ 2 - σ (-(H.d : maximalRealSubfield E)) * b ^ 2 := by
    intro σ
    let τ : E →+* ℂ := ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)
    have hτ : τ (Gm'.det / Gm.det) = (σ x : ℂ) :=
      ComplexEmbedding.lift_algebraMap_apply E (Complex.ofRealHom.comp σ) x
    obtain ⟨p0, ⟨Q, hQ, e⟩, ⟨Q', hQ', e'⟩⟩ := hs τ
    have e2 := congrArg Matrix.det (e.trans e'.symm)
    rw [det_gram, det_gram] at e2
    have n1 : τ Gm.det ≠ 0 := by simpa using hdet
    have n2 : ((‖Q'.det‖ : ℝ) : ℂ) ≠ 0 := by simpa using hQ'
    refine ⟨‖Q.det‖ / ‖Q'.det‖, 0, ?_⟩
    apply Complex.ofReal_injective
    rw [← hτ, map_div₀]
    push_cast at e2 ⊢
    field_simp
    linear_combination -e2
  obtain ⟨a, b, hab⟩ := hH (maximalRealSubfield E) (-(H.d : maximalRealSubfield E)) x
    (by simpa using H.d_prime.ne_zero) hx0 hreal hloc
  have hz : ∃ z : E, Gm'.det = z * FD.cc z * Gm.det := by
    refine ⟨(a : E) + (b : E) * (H.rt : E), ?_⟩
    have e1 : FD.cc ((a : E) + (b : E) * (H.rt : E)) = (a : E) - (b : E) * (H.rt : E) := by
      have c := cc_rt H
      rw [FD.cc] at c ⊢
      rw [map_add, map_mul, c, IsCMField.complexConj_apply_eq_self,
        IsCMField.complexConj_apply_eq_self]
      ring
    have e2 : Gm'.det / Gm.det = (a : E) ^ 2 + (H.d : E) * (b : E) ^ 2 := by
      have := congrArg Subtype.val hab
      simpa using this
    rw [e1, (div_eq_iff hdet).1 e2]
    have := rt_sq' H
    linear_combination (b : E) ^ 2 * Gm.det * this
  obtain ⟨γ, hγ⟩ := hL E r Gm Gm' hG hG' hdet hdet' hs hz
  let g : (Fin r → E) ≃ₗ[E] (Fin r → E) := Matrix.toLin'OfInv γ.inv_mul γ.mul_inv
  have hg : ∀ v, g v = (γ : Matrix (Fin r) (Fin r) E) *ᵥ v := fun v => rfl
  refine ⟨(g.toLinearMap.restrictScalars (𝓞 E)).comp ψ, g.injective.comp hinj, ?_, hG, hdet, ?_⟩
  · have : Set.range ((g.toLinearMap.restrictScalars (𝓞 E)).comp ψ) =
        g.toLinearMap '' Set.range ψ := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · intro u v
    rw [hEF, ← hγ, ← hg, ← hg]
    rfl
end GlobalTheory

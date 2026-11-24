-- Prove2me | solution 1 for GlobalTheory.AdLat.exists_linear_approx_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:14.093398+00:00
-- url     : https://prove2.me/submissions/3ae51adf-9295-498f-ad56-8b1521ea6749

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLinearApproxTower
import Theorems.Thm_GlobalTheory_AdLat_Tower_fv_sub
import Theorems.Thm_GlobalTheory_AdLat_Tower_fv_nsmul
import Theorems.Thm_GlobalTheory_AdLat_Tower_exists_div
import Theorems.Thm_GlobalTheory_AdLat_Tower_projective_of_fg
import Theorems.Thm_GlobalTheory_AdLat_Tower_mulVec_nsmul
import Theorems.Thm_GlobalTheory_AdLat_Translate_fv_nsmul
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_adelicCompletion_rational_points_and_approximation
import Theorems.Thm_GlobalTheory_T_exists_lattice_rationalVectorsInAdelicTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory.AdLat.Tower
namespace GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (Λ : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L → ∃ f : ℕ → (L →ₗ[𝓞 E] Λ), (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ (hat F (L : Set (Fin n → E))), fv F (f N a : Fin n → E) = (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ (fv F (a : Fin n → E) + N • w)) ∧ (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) ∧ ∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v := by
  intro F E _ _ _ _ _ n L g Λ hL hsp hΛ
  obtain ⟨Λ', h1, hΛfg, hΛsp, hhat⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hL hsp
  obtain rfl : Λ = Λ' := SetLike.coe_injective (hΛ.trans h1.symm)
  obtain ⟨hLc, hLa, -, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hsp
  obtain ⟨hΛc, hΛa, -, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n Λ hΛfg hΛsp
  set G : Matrix (Fin n) (Fin n) (RA F E) := g.val with hG
  have hto : ∀ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u ∈ hat F (Λ : Set (Fin n → E)) := by
    intro u hu
    rw [← SetLike.mem_coe, hhat]
    exact ⟨u, hu, rfl⟩
  have hfrom : ∀ z ∈ hat F (Λ : Set (Fin n → E)), ∃ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u = z := by
    intro z hz
    rw [← SetLike.mem_coe, hhat] at hz
    exact hz
  have hinj : ∀ u u' : Fin n → RA F E, G *ᵥ u = G *ᵥ u' → u = u' := by
    intro u u' h
    have := congrArg (fun t => ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ t) h
    simp only [hG, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    exact this
  haveI := projective_of_fg L hL
  have key : ∀ N : ℕ, ∃ f : L →ₗ[𝓞 E] Λ, 0 < N → ∀ a : L, ∃ w ∈ hat F (L : Set (Fin n → E)),
      fv F (f a : Fin n → E) = G *ᵥ (fv F (a : Fin n → E) + N • w) := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · exact ⟨0, fun h => absurd h (by omega)⟩
    have hsurj : Function.Surjective
        ((LinearMap.fst (𝓞 E) L Λ).comp (rel L Λ G N).subtype) := by
      intro a
      obtain ⟨x, hx, w, hw, e⟩ := hΛa N hN _ (hto _ ((hLc a).2 a.2))
      obtain ⟨u, hu, rfl⟩ := hfrom w hw
      refine ⟨⟨(a, ⟨x, hx⟩), -u, neg_mem hu, ?_⟩, rfl⟩
      rw [Matrix.mulVec_add, mulVec_nsmul, Matrix.mulVec_neg, e]
      simp
    obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
    refine ⟨(LinearMap.snd (𝓞 E) L Λ).comp ((rel L Λ G N).subtype.comp s), fun _ a => ?_⟩
    obtain ⟨w, hw, e⟩ := (s a).2
    have ha : (s a).1.1 = a := LinearMap.congr_fun hs a
    rw [ha] at e
    exact ⟨w, hw, e⟩
  choose f hf using key
  refine ⟨f, hf, ?_, ?_⟩
  · intro N m hN hm a
    obtain ⟨w, hw, e⟩ := hf N hN a
    obtain ⟨w', hw', e'⟩ := hf (N * m) (Nat.mul_pos hN hm) a
    obtain ⟨v, hv⟩ := exists_div hΛc hN (f (N * m) a - f N a)
      (hto _ (sub_mem (nsmul_mem hw' m) hw)) (by
        rw [Submodule.coe_sub, fv_sub, e, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub,
          mul_smul]
        congr 1
        abel)
    exact ⟨v, by rw [← hv]; abel⟩
  · intro N hN
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, e⟩ := hf N hN a
      obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc v).2 v.2)
      have e2 : fv F (f N a : Fin n → E) = G *ᵥ (N • u) := by
        rw [mulVec_nsmul, eu, ← fv_nsmul, hv]; rfl
      have e3 := hinj _ _ (e.symm.trans e2)
      exact exists_div hLc hN a (sub_mem hu hw) (by rw [smul_sub, ← e3]; abel)
    · rintro ⟨v, rfl⟩
      exact ⟨f N v, map_nsmul _ _ _⟩
    · obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc a').2 a'.2)
      obtain ⟨x, hx, w, hw, rfl⟩ := hLa N hN u hu
      obtain ⟨w', hw', e'⟩ := hf N hN ⟨x, hx⟩
      obtain ⟨v, hv⟩ := exists_div hΛc hN (a' - f N ⟨x, hx⟩) (hto _ (sub_mem hw hw')) (by
        rw [Submodule.coe_sub, fv_sub, ← eu, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub]
        congr 1
        abel)
      exact ⟨⟨x, hx⟩, v, by rw [← hv]; abel⟩
end GlobalTheory.AdLat

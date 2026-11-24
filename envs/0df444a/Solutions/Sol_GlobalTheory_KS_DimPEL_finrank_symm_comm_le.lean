-- Prove2me | solution 1 for GlobalTheory.KS.DimPEL.finrank_symm_comm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:46.532298+00:00
-- url     : https://prove2.me/submissions/c9eabddc-f3ae-4847-a607-027fb94c8a01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankSymmAntilinearCommCMLe
import Theorems.Thm_GlobalTheory_KS_DimPEL_exists_sum_eigen
import Theorems.Thm_GlobalTheory_KS_DimPEL_conj_eq_neg
import Theorems.Thm_GlobalTheory_KS_DimPEL_mem_Eig
import Theorems.Thm_GlobalTheory_KS_DimPEL_theta_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DimPEL
namespace GlobalTheory.KS.DimPEL
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g p q : ℕ) (ρ₀ : ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (S : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ))
    (hρ : ρ₀ ^ 2 = -(H.d : ℂ)) (_hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hdim : ∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = if τ H.rt = ρ₀ then p else q)
    (hS : ∀ Θ ∈ S, IsSymm Hm Θ ∧ ∀ a, Comm Θ (F a)) :
    Module.finrank ℂ S ≤ Module.finrank ℚ E / 2 * p * q := by
  classical
  have hd : 0 < H.d := H.d_prime.pos
  have hρ0 : ρ₀ ≠ 0 := by
    intro h
    rw [h] at hρ
    have : (H.d : ℂ) = 0 := by simpa using hρ
    exact hd.ne' (by exact_mod_cast this)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    intro τ
    have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    simpa using this
  have hconj : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ (H.rt : E) = - τ (H.rt : E) := by
    intro τ
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg (hsq τ) hd
  have hne : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) ≠ ρ₀ := by
    intro τ h h'
    rw [hconj, h] at h'
    apply hρ0
    linear_combination (-1/2 : ℂ) * h'
  have heq : ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) = ρ₀ := by
    intro τ h
    rw [hconj]
    have : τ (H.rt : E) ^ 2 = ρ₀ ^ 2 := by rw [hsq, hρ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]
  have hdim' : ∀ τ : E →+* ℂ, Module.finrank ℂ (Eig F τ) = if τ (H.rt : E) = ρ₀ then p else q :=
    fun τ => hdim (τ.comp (algebraMap (𝓞 E) E))
  let T := {τ : E →+* ℂ // τ (H.rt : E) = ρ₀}
  have hcard : Fintype.card T ≤ Module.finrank ℚ E / 2 := by
    have h1 : Fintype.card T ≤ Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = ρ₀} := by
      refine Fintype.card_le_of_injective
        (fun τ => ⟨ComplexEmbedding.conjugate τ.1, hne τ.1 τ.2⟩) ?_
      intro σ τ h
      have h2 : ComplexEmbedding.conjugate σ.1 = ComplexEmbedding.conjugate τ.1 := congrArg Subtype.val h
      exact Subtype.ext (star_injective h2)
    rw [Fintype.card_subtype_compl, NumberField.Embeddings.card] at h1
    have h3 : Fintype.card T ≤ Fintype.card (E →+* ℂ) := Fintype.card_subtype_le _
    rw [NumberField.Embeddings.card] at h3
    change Fintype.card T ≤ _ - Fintype.card T at h1
    omega
  have hp : ∀ τ : T, Module.finrank ℂ (Eig F τ.1) = p := fun τ => by rw [hdim', if_pos τ.2]
  have hq : ∀ τ : T, Module.finrank ℂ (Eig F (ComplexEmbedding.conjugate τ.1)) = q :=
    fun τ => by rw [hdim', if_neg (hne τ.1 τ.2)]
  let b : ∀ τ : T, Module.Basis (Fin p) ℂ (Eig F τ.1) := fun τ => Module.finBasisOfFinrankEq ℂ _ (hp τ)
  let Ψ : S →ₗ[ℂ] (∀ τ : T, Fin p → Eig F (ComplexEmbedding.conjugate τ.1)) :=
    { toFun := fun Θ τ i => ⟨Θ.1.mulVec (star (b τ i : Fin g → ℂ)), theta_mem F τ.1 Θ.1 (hS Θ.1 Θ.2).2 _ (b τ i).2⟩
      map_add' := fun Θ Θ' => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.add_mulVec]
      map_smul' := fun c Θ => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.smul_mulVec] }
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro Θ hΘ
    obtain ⟨hs, hc⟩ := hS Θ.1 Θ.2
    have k1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ hτ v hv
      have hb : ∀ i, Θ.1.mulVec (star (b ⟨τ, hτ⟩ i : Fin g → ℂ)) = 0 := fun i =>
        congrArg Subtype.val (congrFun (congrFun hΘ ⟨τ, hτ⟩) i)
      have e := congrArg Subtype.val ((b ⟨τ, hτ⟩).sum_repr ⟨v, hv⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e
      rw [← e, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [star_smul, Matrix.mulVec_smul, hb, smul_zero]
    have k2 : ∀ τ : E →+* ℂ, ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ v hv
      by_cases hτ : τ (H.rt : E) = ρ₀
      · exact k1 τ hτ v hv
      · by_contra h0
        have h1 := hpos _ h0
        rw [hs v, k1 _ (heq τ hτ) _ (theta_mem F τ Θ.1 hc v hv)] at h1
        simp [hermForm] at h1
    have k3 : ∀ v : Fin g → ℂ, Θ.1.mulVec (star v) = 0 := by
      intro v
      obtain ⟨w, hw, rfl⟩ := exists_sum_eigen F v
      rw [star_sum, Matrix.mulVec_sum]
      exact Finset.sum_eq_zero fun τ _ => k2 τ _ ((mem_Eig F τ _).2 (hw τ))
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have := k3 (star v)
    rw [star_star] at this
    simpa using this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at hle
  simp only [Module.finrank_pi_fintype, hq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  calc Module.finrank ℂ S ≤ Fintype.card T * (p * q) := hle
    _ ≤ Module.finrank ℚ E / 2 * (p * q) := Nat.mul_le_mul_right _ hcard
    _ = _ := by ring
end GlobalTheory.KS.DimPEL

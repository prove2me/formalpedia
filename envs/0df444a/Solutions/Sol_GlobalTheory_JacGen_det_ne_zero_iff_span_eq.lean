-- Prove2me | solution 1 for GlobalTheory.JacGen.det_ne_zero_iff_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:48:53.519878+00:00
-- url     : https://prove2.me/submissions/43391988-5838-4ffa-a547-dca2f536078b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacGen
open IsLocalRing
namespace GlobalTheory.JacGen
theorem _root_.solution {K S : Type} [Field K] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra K S] {n : ℕ} (u : S →ₐ[K] K) (D : Fin n → S →ₗ[K] K)
    (hD : ∀ k a b, D k (a * b) = u a * D k b + u b * D k a)
    (hinj : ∀ c : Fin n → K, (∀ a, ∑ k, D k a * c k = 0) → c = 0)
    (hsurj : ∀ δ : S →ₗ[K] K, (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
      ∃ c : Fin n → K, ∀ a, δ a = ∑ k, D k a * c k)
    (f : Fin n → S) (hf : ∀ i, u (f i) = 0) :
    (Matrix.of fun i k => D k (f i)).det ≠ 0 ↔ Ideal.span (Set.range f) = maximalIdeal S := by
  have hker : RingHom.ker u = maximalIdeal S := eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective u fun a => ⟨algebraMap K S a, u.commutes a⟩)
  have hmem : ∀ a, a ∈ maximalIdeal S ↔ u a = 0 := fun a => by rw [← hker, RingHom.mem_ker]
  have hsub : ∀ a, a - algebraMap K S (u a) ∈ maximalIdeal S := fun a => by
    simp [hmem]
  have hle : Ideal.span (Set.range f) ≤ maximalIdeal S :=
    Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (hmem _).2 (hf i))
  constructor
  · intro h
    refine le_antisymm hle (Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun a ha => ?_)
    by_contra hn
    obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (p := (Ideal.span (Set.range f) ⊔ maximalIdeal S • maximalIdeal S).restrictScalars K) hn inferInstance
    have hz : ∀ b ∈ Ideal.span (Set.range f) ⊔ maximalIdeal S • maximalIdeal S, l b = 0 := fun b hb =>
      (Submodule.mem_bot K).1 (hl0 ▸ Submodule.mem_map_of_mem hb)
    let δ : S →ₗ[K] K := l ∘ₗ (LinearMap.id - (Algebra.linearMap K S ∘ₗ u.toLinearMap))
    have hδ : ∀ b, δ b = l (b - algebraMap K S (u b)) := fun b => rfl
    obtain ⟨c, hc⟩ := hsurj δ fun a b => by
      have h0 := hz _ (Submodule.mem_sup_right (Submodule.smul_mem_smul (hsub a) (hsub b)))
      rw [hδ, hδ, hδ, ← smul_eq_mul (u a), ← smul_eq_mul (u b), ← map_smul, ← map_smul, ← map_add,
        ← sub_eq_zero, ← map_sub, ← h0]
      congr 1
      rw [smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      ring
    have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero h (funext fun i => by
      have := hc (f i)
      rw [hδ, hf, map_zero, sub_zero,
        hz _ (Submodule.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))] at this
      exact this.symm)
    have := hc a
    rw [hδ, (hmem a).1 ha, map_zero, sub_zero, hc0] at this
    exact hl (by simpa using this)
  · intro h h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine hc (hinj c fun a => ?_)
    have h1 : ∀ k, D k 1 = 0 := fun k => by simpa using hD k 1 1
    have key : ∀ b ∈ Ideal.span (Set.range f), ∑ k, D k b * c k = 0 := fun b hb => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
      simp only [map_sum, hD, hf, zero_mul, add_zero, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum]
      exact mul_eq_zero_of_right _ (congrFun hc0 i)
    have := key _ (h ▸ hsub a)
    simpa [Algebra.algebraMap_eq_smul_one, h1] using this
end GlobalTheory.JacGen

-- Prove2me | solution 1 for GlobalTheory.DetMod.det_baseChange_quot_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:42:56.502939+00:00
-- url     : https://prove2.me/submissions/2b73dadc-4009-4ea7-a7dd-ff6ace1ff2a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOneReductionOfDetOne
import Theorems.Thm_GlobalTheory_DetMod_det_baseChange_of_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.DetMod
namespace GlobalTheory.DetMod
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (I : Ideal R) [Finite (R ⧸ I)] (γ : L →ₗ[R] L), LinearMap.det (LinearMap.baseChange K γ) = 1 → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 := by
  intro R K _ _ _ _ _ L _ _ _ _ I _ γ hγ
  by_cases hI : I = ⊤
  · haveI := Ideal.Quotient.subsingleton_iff.2 hI
    exact Subsingleton.elim _ _
  set r := Module.finrank R L with hr
  haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] L) r (fun P => by
    haveI := P.isMaximal
    letI : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
      ((R ⧸ I) ⧸ P.asIdeal) L).finrank_eq]
    have h1 := Module.rankAtStalk_baseChange (R := R) (M := L) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
    exact h1)
  have hsurj : Function.Surjective (TensorProduct.mk R (R ⧸ I) L 1) :=
    TensorProduct.mk_surjective R L (R ⧸ I) Ideal.Quotient.mk_surjective
  choose x hx using fun j => hsurj (b j)
  have hb : ∀ j, b j = 1 ⊗ₜ x j := fun j => (hx j).symm
  have hsup : (⊤ : Submodule R L) ≤ Submodule.span R (Set.range x) ⊔ I • ⊤ := by
    intro l _
    choose c hc using fun i => Ideal.Quotient.mk_surjective (b.repr (1 ⊗ₜ l) i)
    have h0 : ((1 : R ⧸ I) ⊗ₜ[R] (l - ∑ i, c i • x i)) = 0 := by
      rw [TensorProduct.tmul_sub, TensorProduct.tmul_sum, sub_eq_zero, ← b.sum_repr (1 ⊗ₜ l)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc, TensorProduct.tmul_smul, ← hb, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    have h1 := congrArg (TensorProduct.quotTensorEquivQuotSMul L I) h0
    rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
    have : l = ∑ i, c i • x i + (l - ∑ i, c i • x i) := by abel
    rw [this]
    exact Submodule.add_mem_sup
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) h1
  obtain ⟨s, hs1, hs⟩ : ∃ s : R, s - 1 ∈ I ∧ ∀ l : L, s • l ∈ Submodule.span R (Set.range x) := by
    obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (⊤ : Submodule R (L ⧸ Submodule.span R (Set.range x))) Module.Finite.fg_top (by
        intro q _
        obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hsup (Submodule.mem_top : l ∈ ⊤))
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hu, zero_add]
        refine Submodule.smul_induction_on hv (fun a ha z _ => ?_) (fun u v hu hv => ?_)
        · rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem_smul ha trivial
        · rw [Submodule.Quotient.mk_add]; exact add_mem hu hv)
    refine ⟨s, hs1, fun l => ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hs _ trivial
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using hs1
  have hsK : algebraMap R K s ≠ 0 := fun h => hs0 (IsFractionRing.injective R K (by rw [h, map_zero]))
  choose a ha using fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (hs (γ (x j)))
  have hspan : ⊤ ≤ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[R] x j) := by
    intro t ht
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add u v hu hv => exact add_mem hu hv
    | tmul k l =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hs l)
      have : k ⊗ₜ[R] l = (k * (algebraMap R K s)⁻¹) • ∑ i, algebraMap R K (c i) • ((1 : K) ⊗ₜ[R] x i) := by
        simp only [algebraMap_smul, ← TensorProduct.tmul_smul]
        rw [← TensorProduct.tmul_sum, hc, TensorProduct.tmul_smul, ← algebraMap_smul K s, smul_smul,
          inv_mul_cancel_right₀ hsK, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hrk : Fintype.card (Fin r) = Module.finrank K (K ⊗[R] L) := by
    rw [Fintype.card_fin, hr, (IsLocalizedModule.isBaseChange (nonZeroDivisors R) K (TensorProduct.mk R K L 1)).finrank_eq]
  have hK := det_baseChange_of_rel x (basisOfTopLeSpanOfCardEqFinrank _ hspan hrk) (fun j => by simp) γ s
    (Matrix.of fun i j => a j i) (fun j => (ha j).symm)
  have hQ := det_baseChange_of_rel x b hb γ s (Matrix.of fun i j => a j i) (fun j => (ha j).symm)
  rw [hγ, mul_one, ← map_pow] at hK
  have hs' : algebraMap R (R ⧸ I) s = 1 := by
    rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact hs1
  rw [← IsFractionRing.injective R K hK, map_pow, hs', one_pow, one_mul] at hQ
  exact hQ
end GlobalTheory.DetMod

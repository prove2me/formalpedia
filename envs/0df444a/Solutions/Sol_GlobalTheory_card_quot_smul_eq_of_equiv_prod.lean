-- Prove2me | solution 1 for GlobalTheory.card_quot_smul_eq_of_equiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:08:38.31106+00:00
-- url     : https://prove2.me/submissions/756819d6-a66c-4ecf-bc4b-c24a00987e1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrank
import Theorems.Thm_GlobalTheory_index_range_eq_card_ker_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M D : Type} [AddCommGroup M] [AddCommGroup D] [Finite D]
    {n : ℕ} (e : M ≃+ (Fin n → ℤ) × D) (p : ℕ) (hp : p ≠ 0) :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  let f : D →+ D := zsmulAddGroupHom (p : ℤ)
  have hf : ∀ d, f d = (p : ℤ) • d := fun d => rfl
  have hrank : Module.finrank ℤ M = n := by
    rw [e.toIntLinearEquiv.finrank_eq]
    have hD : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin n → ℤ) D)) = 0 := by
      rw [Module.rank_eq_zero_iff_isTorsion]
      intro x
      refine ⟨⟨(Nat.card D : ℤ), mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
      · exact_mod_cast (Nat.card_pos (α := D)).ne'
      · have hx : x.1.1 = 0 := x.2
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · simp [Submonoid.smul_def, hx]
        · simp [Submonoid.smul_def]
    have : Module.rank ℤ ((Fin n → ℤ) × D) = n := by
      rw [← (LinearMap.fst ℤ (Fin n → ℤ) D).rank_range_add_rank_ker, hD,
        LinearMap.range_eq_top.2 LinearMap.fst_surjective]
      simp
    simp [Module.finrank, this]
  have hker : Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(e x.1).2, ?_⟩
        invFun := fun d => ⟨e.symm (0, d.1), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : (p : ℤ) • x.1 = 0 := x.2
      have := congrArg (fun y => (e y).2) hx
      simpa [hf] using this
    · have hd : (p : ℤ) • d.1 = 0 := d.2
      change (p : ℤ) • e.symm (0, d.1) = 0
      rw [← map_zsmul, Prod.smul_mk, hd, smul_zero]
      exact map_zero _
    · intro x
      have hx : (p : ℤ) • x.1 = 0 := x.2
      have h1 : (p : ℤ) • (e x.1).1 = 0 := by
        have := congrArg (fun y => (e y).1) hx
        simpa only [map_zsmul, map_zero, Prod.smul_fst, Prod.fst_zero] using this
      have h2 : (e x.1).1 = 0 := (smul_eq_zero.1 h1).resolve_left hp'
      apply Subtype.ext
      change e.symm (0, (e x.1).2) = x.1
      rw [← h2]
      exact e.symm_apply_apply _
    · intro d
      apply Subtype.ext
      simp
  have hrange : (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup =
      ((AddSubgroup.pi Set.univ fun _ : Fin n => AddSubgroup.zmultiples (p : ℤ)).prod
        f.range).comap e.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [AddSubgroup.mem_comap]
      change e ((p : ℤ) • y) ∈ _
      rw [map_zsmul]
      refine ⟨fun i _ => ⟨(e y).1 i, ?_⟩, ⟨(e y).2, rfl⟩⟩
      simp [mul_comm]
    · rintro ⟨h1, d, hd⟩
      have h1' : ∀ i, ∃ k : ℤ, k • (p : ℤ) = (e x).1 i := fun i => h1 i (Set.mem_univ i)
      choose k hk using h1'
      refine ⟨e.symm (k, d), ?_⟩
      change (p : ℤ) • e.symm (k, d) = x
      rw [← map_zsmul, AddEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => ?_) hd
      rw [← hk i]
      simp [mul_comm]
  have hq : Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup.index := rfl
  rw [hq, hrange, AddSubgroup.index_comap_of_surjective _ e.surjective, AddSubgroup.index_prod,
    AddSubgroup.index_pi, index_range_eq_card_ker_of_finite, hker, hrank, mul_comm]
  simp [Int.index_zmultiples]
end GlobalTheory

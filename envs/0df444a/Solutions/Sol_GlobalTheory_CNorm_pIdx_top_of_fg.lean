-- Prove2me | solution 1 for GlobalTheory.CNorm.pIdx_top_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:59.099725+00:00
-- url     : https://prove2.me/submissions/6bee4344-6c1a-408d-8ff4-44cfde8f29a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexTopOfGroupFg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
namespace GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem card_quot_range_nsmul_eq_pow_finrank_mul_card_ker (M : Type) [AddCommGroup M]
    [AddGroup.FG M] (p : ℕ) (hp : 0 < p) :
    Nat.card (nsmulAddMonoidHom (α := M) p).ker ≠ 0 ∧
      (nsmulAddMonoidHom (α := M) p).range.index =
        p ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) p).ker := by
  obtain ⟨n, ι, _, q, hq, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (q i ^ e i)) :=
    Finite.of_equiv _ (DirectSum.linearEquivFunOnFintype ℤ ι _).toEquiv.symm
  set D := DirectSum ι fun i => ZMod (q i ^ e i)
  set P := Fin n →₀ ℤ
  have hker : Nat.card (nsmulAddMonoidHom (α := M) p).ker =
      Nat.card (nsmulAddMonoidHom (α := D) p).ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(φ x).2, ?_⟩
        invFun := fun y => ⟨φ.symm (0, y), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := congrArg φ x.2
      rw [nsmulAddMonoidHom_apply, map_nsmul, map_zero] at h
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
      exact congrArg Prod.snd h
    · have h := y.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h ⊢
      rw [← map_nsmul, Prod.smul_mk, smul_zero, h, Prod.mk_zero_zero, map_zero]
    · intro x
      apply Subtype.ext
      apply φ.injective
      have h := congrArg φ x.2
      rw [nsmulAddMonoidHom_apply, map_nsmul, map_zero] at h
      have h1 : p • (φ x).1 = 0 := congrArg Prod.fst h
      have h2 : (φ x).1 = 0 := (smul_eq_zero.mp h1).resolve_left hp.ne'
      simp only [AddEquiv.apply_symm_apply]
      exact Prod.ext h2.symm rfl
    · intro y
      apply Subtype.ext
      simp
  have hrange : (nsmulAddMonoidHom (α := M) p).range =
      AddSubgroup.comap φ.toAddMonoidHom
        ((nsmulAddMonoidHom (α := P) p).range.prod (nsmulAddMonoidHom (α := D) p).range) := by
    ext x
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_comap,
      AddSubgroup.mem_prod, AddEquiv.coe_toAddMonoidHom]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨(φ y).1, by rw [map_nsmul]; rfl⟩, ⟨(φ y).2, by rw [map_nsmul]; rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨φ.symm (a, b), φ.injective ?_⟩
      rw [map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_mk, ha, hb]
  have hindexD : (nsmulAddMonoidHom (α := D) p).range.index =
      Nat.card (nsmulAddMonoidHom (α := D) p).ker := by
    haveI : (nsmulAddMonoidHom (α := D) p).ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite
    exact AddSubgroup.index_range
  have hrank : Module.finrank ℤ M = n := by
    rw [φ.toIntLinearEquiv.finrank_eq]
    have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ P D)
    rw [LinearMap.range_eq_top.mpr fun x => ⟨(x, 0), rfl⟩, LinearMap.ker_fst, rank_top] at h
    have h0 : Module.rank ℤ (LinearMap.inr ℤ P D).range = 0 := by
      rw [rank_eq_zero_iff]
      rintro ⟨x, y, rfl⟩
      refine ⟨(Nat.card D : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
      apply Subtype.ext
      simp only [SetLike.val_smul, LinearMap.coe_inr, Submodule.coe_zero, natCast_zsmul]
      ext
      · simp
      · simpa using card_nsmul_eq_zero' (x := y)
    rw [h0, add_zero, rank_finsupp_self, Cardinal.mk_fin, Cardinal.lift_natCast] at h
    change Module.finrank ℤ (P × D) = n
    rw [Module.finrank, ← h]
    simp
  refine ⟨?_, ?_⟩
  · rw [hker]
    exact Nat.card_pos.ne'
  · rw [hrange, AddSubgroup.index_comap_of_surjective _ φ.surjective, AddSubgroup.index_prod,
      AddSubgroup.index_range_nsmul, Module.finrank_finsupp_self, Fintype.card_fin, hrank,
      hindexD, hker]
end GlobalTheory.CNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped WithZero TensorProduct
namespace GlobalTheory.CNorm
namespace _root_.GlobalTheory.CNorm
theorem _root_.solution : ∀ (p : ℕ) (G : Type) [CommGroup G] [Group.FG G],
    0 < p →
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) ≠ 0 ∧
      _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
        p ^ Module.finrank ℤ (Additive G) * _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) := by
  intro p G _ _ hp
  obtain ⟨h1, h2⟩ := card_quot_range_nsmul_eq_pow_finrank_mul_card_ker (Additive G) p hp
  have htor : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) =
      Nat.card (nsmulAddMonoidHom (α := Additive G) p).ker := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.ofMul x.1, ?_⟩
        invFun := fun y => ⟨y.1.toMul, Subgroup.mem_top _, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, ← ofMul_pow, x.2.2, ofMul_one]
    · have h := y.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h
      rw [← toMul_nsmul, h, toMul_zero]
  have hidx : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
      (nsmulAddMonoidHom (α := Additive G) p).range.index := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right, ← Subgroup.index_toAddSubgroup]
    congr 1
    ext x
    change Additive.toMul x ∈ Subgroup.map (powMonoidHom p) ⊤ ↔ _
    rw [Subgroup.mem_map, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨Additive.ofMul y, by
        rw [nsmulAddMonoidHom_apply, ← ofMul_pow, ← powMonoidHom_apply, hy, ofMul_toMul]⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.toMul y, Subgroup.mem_top _, by
        rw [powMonoidHom_apply, ← toMul_nsmul, ← nsmulAddMonoidHom_apply, hy]⟩
  exact ⟨htor ▸ h1, by rw [hidx, htor]; exact h2⟩
end _root_.GlobalTheory.CNorm
end GlobalTheory.CNorm

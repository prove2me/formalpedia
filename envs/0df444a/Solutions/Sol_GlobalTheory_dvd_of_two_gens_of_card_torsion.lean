-- Prove2me | solution 1 for GlobalTheory.dvd_of_two_gens_of_card_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:35:59.150473+00:00
-- url     : https://prove2.me/submissions/35baa94d-a0f7-4020-a2af-65c7bb27da59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionBasisRelationsDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    Nat.card {x : M // N • x = 0} = N ^ (2 * Module.finrank ℚ F) →
    ∀ p : Fin 2 → M, (∀ i, N • p i = 0) →
    (∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1) →
    ∀ a b : 𝓞 F, a • p 0 + b • p 1 = 0 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  intro F _ _ M _ _ N hN hc p hp hgen a b hab
  classical
  set I : Ideal (𝓞 F) := Ideal.span {(N : 𝓞 F)} with hI
  have hNp : ∀ (c : 𝓞 F) i, ((N : 𝓞 F) * c) • p i = 0 := by
    intro c i
    rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hp i, smul_zero]
  let ψ : 𝓞 F × 𝓞 F →+ M :=
    { toFun := fun x => x.1 • p 0 + x.2 • p 1
      map_zero' := by simp
      map_add' := by intro x y; simp [add_smul]; abel }
  let g : 𝓞 F × 𝓞 F →+ (𝓞 F ⧸ I) × (𝓞 F ⧸ I) :=
    { toFun := fun x => (Ideal.Quotient.mk I x.1, Ideal.Quotient.mk I x.2)
      map_zero' := by simp
      map_add' := by intro x y; simp }
  have hgker : ∀ x y : 𝓞 F, (x, y) ∈ g.ker ↔ (N : 𝓞 F) ∣ x ∧ (N : 𝓞 F) ∣ y := by
    intro x y
    simp only [AddMonoidHom.mem_ker, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hle : g.ker ≤ ψ.ker := by
    rintro ⟨x, y⟩ hx
    rw [hgker] at hx
    obtain ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩ := hx
    simp [ψ, hNp]
  have hrange : (ψ.range : Set M) = {x : M | N • x = 0} := by
    ext y
    simp only [SetLike.mem_coe, AddMonoidHom.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨x1, x2⟩, rfl⟩
      simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_add]
      rw [smul_comm, hp 0, smul_zero, smul_comm, hp 1, smul_zero, add_zero]
    · intro hy
      obtain ⟨a, b, rfl⟩ := hgen y hy
      exact ⟨(a, b), rfl⟩
  have hindψ : ψ.ker.index = N ^ (2 * Module.finrank ℚ F) := by
    rw [AddSubgroup.index_ker, ← hc]
    exact Nat.card_congr (Equiv.setCongr hrange)
  have hcardR : Nat.card (𝓞 F ⧸ I) = N ^ Module.finrank ℚ F := by
    have h1 := Ideal.absNorm_span_singleton (S := 𝓞 F) (N : 𝓞 F)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    rw [hI, h1, ← map_natCast (algebraMap ℤ (𝓞 F)) N, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
    simp
  have hindg : g.ker.index = N ^ (2 * Module.finrank ℚ F) := by
    have hs : Function.Surjective g := by
      rintro ⟨u, v⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
      exact ⟨(x, y), rfl⟩
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs]
    rw [Nat.card_congr (AddSubgroup.topEquiv).toEquiv, Nat.card_prod, hcardR, ← pow_add, two_mul]
  have hrel := AddSubgroup.relIndex_mul_index hle
  rw [hindψ, hindg] at hrel
  have hpos : 0 < N ^ (2 * Module.finrank ℚ F) := pow_pos (by omega) _
  have h1 : g.ker.relIndex ψ.ker = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hpos (hrel.trans (one_mul _).symm)
    exact this
  have hk := AddSubgroup.relIndex_eq_one.mp h1
  have hmem : ((a, b) : 𝓞 F × 𝓞 F) ∈ ψ.ker := hab
  have := hk hmem
  exact (hgker a b).mp this
end GlobalTheory

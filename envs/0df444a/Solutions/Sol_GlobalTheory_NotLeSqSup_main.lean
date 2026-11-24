-- Prove2me | solution 1 for GlobalTheory.NotLeSqSup.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:32:48.508991+00:00
-- url     : https://prove2.me/submissions/07b1f8ed-ddb0-4ea3-a431-66e7e514ca26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotLeSqSup
import Theorems.Thm_GlobalTheory_NotLeSqSup_not_le_sq_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NotLeSqSup
namespace GlobalTheory.NotLeSqSup
theorem _root_.solution : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (aug : A →ₐ[k] k) {I : Ideal A} {n : ℕ}, RingHom.ker aug ^ (n + (1 : ℕ)) = ⊥ → I ≤ RingHom.ker aug → ¬RingHom.ker aug ≤ I → ∃ (φ : A →ₐ[k] DualNumber k), AlgHom.comp (TrivSqZeroExt.fstHom k k k) φ = aug ∧ (∀ a ∈ I, (φ : A → DualNumber k) a = (0 : DualNumber k)) ∧ ∃ a ∈ RingHom.ker aug, (φ : A → DualNumber k) a ≠ (0 : DualNumber k) := by
  intro k A _ _ _ aug I n hn hIm hmI
  have hx : ¬ RingHom.ker aug ≤ RingHom.ker aug ^ 2 ⊔ I := not_le_sq_sup hn hmI
  obtain ⟨x, hxm, hxN⟩ := Set.not_subset.mp hx
  let N : Submodule k A := (RingHom.ker aug ^ 2 ⊔ I).restrictScalars k
  have hq : N.mkQ x ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxN
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k (A ⧸ N), f (N.mkQ x) ≠ 0 := by
    by_contra h; push_neg at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  let g : A →ₗ[k] k := f.comp N.mkQ
  have hgN : ∀ a ∈ RingHom.ker aug ^ 2 ⊔ I, g a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ha
    simp only [g, LinearMap.comp_apply, this, map_zero]
  let D : A →ₗ[k] k := g.comp (LinearMap.id - (Algebra.linearMap k A).comp aug.toLinearMap)
  have hD : ∀ a, D a = g (a - algebraMap k A (aug a)) := fun a => rfl
  have hsub : ∀ a, a - algebraMap k A (aug a) ∈ RingHom.ker aug := by
    intro a; simp [RingHom.mem_ker]
  have hDmul : ∀ a b, D (a * b) = aug a * D b + aug b * D a := by
    intro a b
    have e : a * b - algebraMap k A (aug (a * b)) =
        (a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))
          + aug a • (b - algebraMap k A (aug b)) + aug b • (a - algebraMap k A (aug a)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    have h0 : g ((a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))) = 0 :=
      hgN _ (Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul (hsub a) (hsub b)))
    rw [hD, hD, hD, e, map_add, map_add, h0, map_smul, map_smul, smul_eq_mul, smul_eq_mul, zero_add]
  let L : A →ₗ[k] DualNumber k :=
    (Algebra.linearMap k (DualNumber k)).comp aug.toLinearMap + (TrivSqZeroExt.inrHom k k).comp D
  have hLfst : ∀ a, (L a).fst = aug a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  have hLsnd : ∀ a, (L a).snd = D a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : A →ₐ[k] DualNumber k := AlgHom.ofLinearMap L
    (by ext <;> simp [hLfst, hLsnd, hD])
    (by intro a b; ext <;> simp [hLfst, hLsnd, hDmul] <;> ring)
  have hφ : ∀ a, φ a = L a := fun a => rfl
  refine ⟨φ, ?_, ?_, x, hxm, ?_⟩
  · ext a; simp [hφ, hLfst]
  · intro a ha
    ext
    · simp [hφ, hLfst]; exact hIm ha
    · simp only [hφ, hLsnd, TrivSqZeroExt.snd_zero]
      rw [hD]
      have : aug a = 0 := hIm ha
      rw [this, map_zero, sub_zero]
      exact hgN a (Ideal.mem_sup_right ha)
  · intro h0
    apply hf
    have := congrArg TrivSqZeroExt.snd h0
    rw [hφ, hLsnd, hD, TrivSqZeroExt.snd_zero, (RingHom.mem_ker).mp hxm, map_zero, sub_zero] at this
    exact this
end GlobalTheory.NotLeSqSup

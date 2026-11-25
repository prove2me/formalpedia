-- Prove2me | solution 1 for GlobalTheory.exists_zpow_eq_one_of_isClosed_torusZariski
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:51.42524+00:00
-- url     : https://prove2.me/submissions/4fe8c7e0-d735-4d58-bc09-f3ac84891df6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Theorems.Thm_GlobalTheory_mem_of_isClosed_torusZariski

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
variable [IsDomain R]
namespace GlobalTheory
theorem _root_.solution [Module.Finite ℤ X] {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity R n] {H : Subgroup (Multiplicative X →* Rˣ)}
    (hH : IsClosed[torusZariski R X] (H : Set (Multiplicative X →* Rˣ)))
    (hn : ∀ s ∈ H, s ^ n = 1 → s = 1) : ∃ r : ℤ, (n : ℤ) ∣ r - 1 ∧ ∀ s ∈ H, s ^ r = 1 := by
  let K : Submodule ℤ X := AddSubgroup.toIntSubmodule
    { carrier := {x | ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1}
      add_mem' := fun {a b} ha hb s hs => by rw [ofAdd_add, map_mul, ha s hs, hb s hs, mul_one]
      zero_mem' := fun s _ => map_one s
      neg_mem' := fun {a} ha s hs => by rw [ofAdd_neg, map_inv, ha s hs, inv_one] }
  have hK : ∀ x, x ∈ K ↔ ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1 := fun x => Iff.rfl
  let N : Submodule ℤ X := K ⊔ Ideal.span {(n : ℤ)} • ⊤
  have hnN : ∀ x : X, (n : ℤ) • x ∈ N := fun x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial)
  have hnQ : ∀ q : X ⧸ N, (n : ℤ) • q = 0 := fun q => by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hnN x
  have hnQ' : ∀ q : Multiplicative (X ⧸ N), q ^ n = 1 := fun q => by
    have := hnQ q.toAdd
    rw [natCast_zsmul] at this
    exact congrArg Multiplicative.ofAdd this
  have hN : (⊤ : Submodule ℤ X) ≤ N := by
    intro x _
    by_contra hx
    haveI : Finite (X ⧸ N) := Module.finite_of_fg_torsion _ fun q =>
      ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne n))⟩, hnQ q⟩
    haveI : HasEnoughRootsOfUnity R (Monoid.exponent (Multiplicative (X ⧸ N))) :=
      HasEnoughRootsOfUnity.of_dvd R (Monoid.exponent_dvd_of_forall_pow_eq_one hnQ')
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Multiplicative (X ⧸ N)) R (a := Multiplicative.ofAdd (N.mkQ x))
      (by simpa using hx)
    let t : Multiplicative X →* Rˣ := φ.comp (AddMonoidHom.toMultiplicative N.mkQ.toAddMonoidHom)
    have ht : ∀ y, t y = φ (Multiplicative.ofAdd (N.mkQ y.toAdd)) := fun y => rfl
    have htH : t ∈ H := mem_of_isClosed_torusZariski hH fun y hy => by
      have : N.mkQ y.toAdd = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_sup_left ((hK _).2 hy)
      rw [ht, this, ofAdd_zero, map_one]
    have ht1 : t = 1 := hn t htH (MonoidHom.ext fun y => by
      rw [MonoidHom.pow_apply, ht, ← map_pow, hnQ', map_one, MonoidHom.one_apply])
    exact hφ (by simpa [ht] using DFunLike.congr_fun ht1 (Multiplicative.ofAdd x))
  obtain ⟨r, hr, hrK⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {(n : ℤ)}) (N := K) (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl hN
  refine ⟨r, Ideal.mem_span_singleton.1 hr, fun s hs => MonoidHom.ext fun y => ?_⟩
  have := (hK _).1 (hrK (Submodule.smul_mem_pointwise_smul y.toAdd r ⊤ trivial)) s hs
  rw [ofAdd_zsmul, map_zpow] at this
  exact this
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.TransferCommutator.exists_smul_eq_zero_of_crossed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:01.810548+00:00
-- url     : https://prove2.me/submissions/0739952b-4016-4425-949f-07a57be1a3cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSmulEqZeroOfCrossed

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
open GlobalTheory GlobalTheory.TransferCommutator
namespace GlobalTheory.TransferCommutator
theorem _root_.solution {G : Type} [Group G] [Finite G] {R : Type} [CommRing R] (ε : R →+* ℤ)
    (ρ : G → R) (hρ : ∀ g, ε (ρ g) = 1) {X : Type} [AddCommGroup X] [Module R X] (d : G → X)
    (hd : ∀ g h, d (g * h) = d g + ρ g • d h) :
    ∃ μ : R, (ε μ).natAbs = Nat.card (Abelianization G) ∧ ∀ g, μ • d g = 0 := by
  classical
  have := Fintype.ofFinite G
  let J : Submodule R X := (Submodule.pi Set.univ fun _ : G => RingHom.ker ε).map (Fintype.linearCombination R d)
  let ψ : G →* Multiplicative (X ⧸ J) := MonoidHom.mk' (fun g => Multiplicative.ofAdd (J.mkQ (d g))) fun g h => by
    rw [← ofAdd_add, ← map_add]
    congr 1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hd]
    refine ⟨Pi.single h (ρ g - 1), fun i _ => ?_, ?_⟩
    · by_cases hi : i = h
      · subst hi; simp [RingHom.mem_ker, hρ]
      · simp [hi]
    · rw [Fintype.linearCombination_apply_single, sub_smul, one_smul]; abel
  let ψ' : Additive (Abelianization G) →ₗ[ℤ] X ⧸ J :=
    (MonoidHom.toAdditiveLeft (Abelianization.lift ψ)).toIntLinearMap
  have hψ' : ∀ g, ψ' (Additive.ofMul (Abelianization.of g)) = J.mkQ (d g) := fun g => rfl
  let L : (G → ℤ) →ₗ[ℤ] Additive (Abelianization G) :=
    Fintype.linearCombination ℤ fun g => Additive.ofMul (Abelianization.of g)
  have hL : Function.Surjective L := fun q => by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (s := commutator G) q.toMul
    exact ⟨Pi.single g 1, by rw [Fintype.linearCombination_apply_single, one_smul]; exact congrArg Additive.ofMul hg⟩
  have eq := L.quotKerEquivOfSurjective hL
  have hfin : Finite (Abelianization G) := inferInstanceAs (Finite (G ⧸ commutator G))
  have : Finite ((G → ℤ) ⧸ LinearMap.ker L) := Finite.of_equiv _ eq.symm.toEquiv
  let e : (G → ℤ) ≃ₗ[ℤ] LinearMap.ker L :=
    LinearEquiv.ofFinrankEq _ _ ((Submodule.finiteQuotient_iff _).1 this).symm
  have hdet := Submodule.natAbs_det_equiv (LinearMap.ker L) e
  have hrel : ∀ n : LinearMap.ker L, ∃ ν : G → R, (∀ i, ε (ν i) = n.1 i) ∧ ∑ i, ν i • d i = 0 := fun n => by
    have h0 : ∑ i, n.1 i • d i ∈ J := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      have := congrArg ψ' n.2
      rw [map_zero, Fintype.linearCombination_apply, map_sum] at this
      simpa only [map_zsmul, hψ'] using this
    obtain ⟨ν, hν, hs⟩ := h0
    refine ⟨fun i => (n.1 i : R) - ν i, fun i => ?_, ?_⟩
    · rw [map_sub, (RingHom.mem_ker).1 (hν i trivial)]; simp
    · simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul]
      rw [← hs, Fintype.linearCombination_apply, sub_self]
  choose ν hν hs using hrel
  let M : Matrix G G R := Matrix.of fun j i => ν (e (Pi.single j 1)) i
  refine ⟨M.det, ?_, fun k => ?_⟩
  · rw [RingHom.map_det, ← Matrix.det_transpose, ← Nat.card_congr (eq.toEquiv.trans Additive.toMul), ← hdet,
      ← LinearMap.det_toMatrix']
    congr 2
    ext i j
    simp [M, hν, LinearMap.toMatrix'_apply]
  · have h1 : M.det • d k = ∑ i, (M.adjugate * M) k i • d i := by
      rw [Matrix.adjugate_mul]
      simp [Matrix.one_apply]
    rw [h1]
    simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.smul_sum]
    exact (congrArg _ (hs _)).trans (smul_zero _)
end GlobalTheory.TransferCommutator

-- Prove2me | solution 1 for GlobalTheory.LatticeMinuscule.lattice_elementary_divisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:19.227934+00:00
-- url     : https://prove2.me/submissions/ac5b3fea-202c-488b-9ee9-868ff7a52631

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeElementaryDivisors
import Theorems.Thm_GlobalTheory_SmithBetween_smith_between


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LatticeMinuscule
open Matrix
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
open IsDedekindDomain NumberField
open Matrix
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
namespace GlobalTheory.LatticeMinuscule
namespace _root_.GlobalTheory.LatticeMinuscule
theorem _root_.solution (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (a a' : Matrix (Fin n) (Fin n) K)
    (haa : a * a' = 1) (h1 : ∀ y ∈ Λ, a.mulVec y ∈ Λ)
    (h2 : ∀ y ∈ Λ, ∃ z ∈ Λ, algebraMap R K ϖ • y = a.mulVec z) (u : Rˣ)
    (hdet : a.det = algebraMap R K ϖ ^ k * algebraMap R K (u : R)) :
    ∃ B : Matrix (Fin n) (Fin n) K,
      (∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B.mulVec (fun i => algebraMap R K (z i))) ∧
      (∀ y, (∃ x ∈ Λ, y = a'.mulVec x) ↔ ∃ z : Fin n → R, y = B.mulVec (fun i =>
        algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖ0 : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  haveI : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free R Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R Λ
  have hli : LinearIndependent K (fun i => (b i : Fin n → K)) :=
    (LinearIndependent.iff_fractionRing R K).mp
      (b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ))
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R Λ) = n := by
    have hspan : ⊤ ≤ Submodule.span K (Set.range fun i => (b i : Fin n → K)) := by
      rw [← hsp, Submodule.span_le]
      intro x hx
      rw [← show ((⟨x, hx⟩ : Λ) : Fin n → K) = x from rfl, ← b.sum_repr ⟨x, hx⟩,
        Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, ← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  let B0 : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (b' j : Fin n → K) i
  have key : ∀ z : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      ((b'.equivFun.symm z : Λ) : Fin n → K) := by
    intro z; ext i
    simp [B0, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Submodule.coe_sum,
      Finset.sum_apply, Algebra.smul_def, mul_comm]
  have memL : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B0 *ᵥ (fun i => algebraMap R K (z i)) := by
    intro y; constructor
    · intro hy; refine ⟨b'.equivFun ⟨y, hy⟩, ?_⟩; rw [key, LinearEquiv.symm_apply_apply]
    · rintro ⟨z, rfl⟩; rw [key]; exact Subtype.prop _
  have keyinj : ∀ z w : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      B0 *ᵥ (fun i => algebraMap R K (w i)) → z = w := by
    intro z w h; rw [key, key] at h; exact b'.equivFun.symm.injective (Subtype.coe_injective h)
  have hmap : ∀ (N : Matrix (Fin n) (Fin n) R) (z : Fin n → R),
      N.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (z i)) =
        fun i => algebraMap R K ((N *ᵥ z) i) := by
    intro N z; funext i; exact (RingHom.map_mulVec (algebraMap R K) N z i).symm
  have h1' : ∀ j, ∃ z : Fin n → R,
      a *ᵥ (b' j : Fin n → K) = B0 *ᵥ (fun i => algebraMap R K (z i)) :=
    fun j => (memL _).1 (h1 _ (b' j).2)
  choose zM hzM using h1'
  let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM j i
  have haB : a * B0 = B0 * M.map (algebraMap R K) := by
    ext i j
    have := congrFun (hzM j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, B0, M] using this
  have h2' : ∀ j, ∃ z : Fin n → R, algebraMap R K ϖ • (b' j : Fin n → K) =
      a *ᵥ (B0 *ᵥ (fun i => algebraMap R K (z i))) := by
    intro j
    obtain ⟨x, hx, hxe⟩ := h2 _ (b' j).2
    obtain ⟨z, rfl⟩ := (memL x).1 hx
    exact ⟨z, hxe⟩
  choose zM' hzM' using h2'
  let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM' j i
  have hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    have h := hzM' j
    rw [Matrix.mulVec_mulVec, haB, ← Matrix.mulVec_mulVec, hmap] at h
    have hl : algebraMap R K ϖ • (b' j : Fin n → K) =
        B0 *ᵥ (fun i => algebraMap R K ((ϖ • Pi.single j (1 : R) : Fin n → R) i)) := by
      rw [key, map_smul, Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply, algebraMap_smul]
    have h3 := congrFun (keyinj _ _ (hl.symm.trans h)) i
    rw [show (M * M') i j = (M *ᵥ zM' j) i from rfl, ← h3]
    simp [Matrix.one_apply, Pi.single_apply]
  have hsurj : Function.Surjective B0.mulVec := by
    intro y
    have hy : y ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ Submodule.mem_top
    have hle : Submodule.span K (Λ : Set (Fin n → K)) ≤ LinearMap.range (Matrix.mulVecLin B0) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hle hy
    exact ⟨w, hw⟩
  have hB0 : B0.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B0).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero
  have hdetM : Associated M.det (ϖ ^ k) := by
    have h := congrArg Matrix.det haB
    have hdm : (M.map (algebraMap R K)).det = algebraMap R K M.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, hdet, hdm, ← map_pow, ← map_mul] at h
    have h' := hinj (mul_left_cancel₀ hB0 h)
    exact ⟨u⁻¹, by rw [← h', mul_assoc, Units.mul_inv, mul_one]⟩
  obtain ⟨P, Q, hP, hQ, hMQ⟩ :=
    _root_.GlobalTheory.SmithBetween.smith_between R ϖ hϖ n k hk M M' hMM hdetM
  have haa' : a' * a = 1 := mul_eq_one_comm.mp haa
  have hE : ∀ z : Fin n → R, a *ᵥ ((B0 * Q.map (algebraMap R K)) *ᵥ (fun i =>
      algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) =
        B0 *ᵥ (fun i => algebraMap R K ((P *ᵥ z) i)) := by
    intro z
    have hdw : ((Matrix.diagonal fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ).map
        (algebraMap R K)) *ᵥ (fun i =>
          algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i)) =
        fun i => algebraMap R K (z i) := by
      rw [Matrix.diagonal_map (map_zero _)]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hi : i.1 < n - k <;> simp [hi, hϖ0]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, haB, Matrix.mul_assoc, ← Matrix.map_mul, hMQ,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdw, hmap]
  refine ⟨B0 * Q.map (algebraMap R K), fun y => ?_, fun y => ?_⟩
  · rw [memL]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Q⁻¹ *ᵥ z, ?_⟩
      rw [← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQ,
        Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      exact ⟨Q *ᵥ z, by rw [← Matrix.mulVec_mulVec, hmap]⟩
  · constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      refine ⟨P⁻¹ *ᵥ z, ?_⟩
      have h := hE (P⁻¹ *ᵥ z)
      have hz : P *ᵥ (P⁻¹ *ᵥ z) = z := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
      rw [hz] at h
      rw [← h, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      refine ⟨_, (memL _).2 ⟨P *ᵥ z, rfl⟩, ?_⟩
      rw [← hE z, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]
end _root_.GlobalTheory.LatticeMinuscule
end GlobalTheory.LatticeMinuscule

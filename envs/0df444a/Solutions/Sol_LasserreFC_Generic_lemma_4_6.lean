-- Prove2me | solution 1 for LasserreFC.Generic.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:45:15.235207+00:00
-- url     : https://prove2.me/submissions/2f90915d-ddc3-484d-9b52-38dae226db8f

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting
import Theorems.Thm_LasserreFC_Generic_sonc_1_6

namespace LasserreFC.Generic.L46Red

open MvPolynomial Matrix LasserreFC.Generic

lemma pderiv_comm' {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have : ⁅(pderiv i : Derivation ℝ (MvPolynomial (Fin n) ℝ) (MvPolynomial (Fin n) ℝ)),
      (pderiv j : Derivation ℝ (MvPolynomial (Fin n) ℝ) (MvPolynomial (Fin n) ℝ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply]
    simp only [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have h := congrArg (fun D => D p) this
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.mp h

lemma hess_symm {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) :
    (hess p u)ᵀ = hess p u := by
  ext k s
  simp only [transpose_apply, hess]
  rw [pderiv_comm']

/-- rows of `G(u)` linearly independent ⇒ `G(u)ᵀ w = 0 → w = 0` -/
lemma GT_inj {n m1 m2 : ℕ} (P : POP n m1 m2) (u : Fin n → ℝ) (hcq : CQC P u)
    (w : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} → ℝ)
    (hw : (Gmat P u)ᵀ *ᵥ w = 0) : w = 0 := by
  have hli := Fintype.linearIndependent_iff.mp hcq w
  funext e
  apply hli
  rw [← hw]
  funext k
  simp only [mulVec, dotProduct, transpose_apply, Gmat, of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-- a functional vanishing on `ker G` is a combination of the rows of `G` -/
lemma mem_rowspace {n ι : Type*} [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
    (G : Matrix ι n ℝ) (a : n → ℝ) (ha : ∀ z, G *ᵥ z = 0 → a ⬝ᵥ z = 0) :
    ∃ ν : ι → ℝ, a = Gᵀ *ᵥ ν := by
  let f : (n → ℝ) →ₗ[ℝ] (ι → ℝ) := Matrix.toLin' G
  let φ : Module.Dual ℝ (n → ℝ) := (dotProductBilin ℝ ℝ a)
  have hφ : φ ∈ f.ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    simp only [LinearMap.mem_ker, f, Matrix.toLin'_apply] at hz
    simpa [φ] using ha z hz
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ
  obtain ⟨ψ, hψ⟩ := hφ
  refine ⟨fun e => ψ (Pi.single e 1), ?_⟩
  funext k
  have h1 := LinearMap.congr_fun hψ (Pi.single k 1)
  simp only [LinearMap.dualMap_apply, f, Matrix.toLin'_apply, φ] at h1
  have h2 : G *ᵥ Pi.single k 1 = ∑ e, (G e k) • (Pi.single e 1 : ι → ℝ) := by
    funext e
    simp [mulVec_single, Finset.sum_apply, Pi.single_apply]
  rw [h2, map_sum] at h1
  simp only [map_smul, smul_eq_mul] at h1
  have h3 : (dotProductBilin ℝ ℝ a) (Pi.single k 1) = a k := by
    simp [dotProductBilin]
  rw [h3] at h1
  rw [← h1]
  simp [mulVec, dotProduct, transpose_apply]

end LasserreFC.Generic.L46Red

open MvPolynomial Matrix LasserreFC.Generic LasserreFC.Generic.L46Red in
theorem solution {n m1 m2 : ℕ} (P : POP n m1 m2) (u : Fin n → ℝ) (hu : u ∈ P.K)
    (hmin : IsLocalMinOn (fun x => eval x P.f) P.K u) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ)
    (hkkt : IsKKTMult P u lam mu) (hG : CQC P u) :
    SOSC P u lam mu ↔ (Hmat P u lam mu).det ≠ 0 := by
  classical
  set A := hess (lagr P u lam mu) u with hA
  set G := Gmat P u with hGdef
  -- `G z = 0` iff `z ∈ G(u)^⊥`
  have hGz : ∀ z : Fin n → ℝ, G *ᵥ z = 0 ↔
      ((∀ i, grad (P.h i) u ⬝ᵥ z = 0) ∧ (∀ j, eval u (P.g j) = 0 → grad (P.g j) u ⬝ᵥ z = 0)) := by
    intro z
    constructor
    · intro h
      refine ⟨fun i => ?_, fun j hj => ?_⟩
      · have := congrFun h (Sum.inl i); simpa [G, Gmat, mulVec] using this
      · have := congrFun h (Sum.inr ⟨j, hj⟩); simpa [G, Gmat, mulVec] using this
    · rintro ⟨h1, h2⟩
      funext e
      rcases e with i | ⟨j, hj⟩
      · simpa [G, Gmat, mulVec] using h1 i
      · simpa [G, Gmat, mulVec] using h2 j hj
  have hH : ∀ z, Hmat P u lam mu *ᵥ z =
      Sum.elim (A *ᵥ (z ∘ Sum.inl) + Gᵀ *ᵥ (z ∘ Sum.inr)) (G *ᵥ (z ∘ Sum.inl)) := by
    intro z
    simp only [Hmat, fromBlocks_mulVec, zero_mulVec, add_zero, A, G]
  constructor
  · intro hS hdet
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    rw [hH] at hz
    have hz1 : A *ᵥ (z ∘ Sum.inl) + Gᵀ *ᵥ (z ∘ Sum.inr) = 0 := by
      funext k; exact congrFun hz (Sum.inl k)
    have hz2 : G *ᵥ (z ∘ Sum.inl) = 0 := by
      funext e; exact congrFun hz (Sum.inr e)
    have hv : z ∘ Sum.inl = 0 := by
      by_contra hv
      have hpos := hS _ hv ((hGz _).mp hz2).1 ((hGz _).mp hz2).2
      have : A *ᵥ (z ∘ Sum.inl) = -(Gᵀ *ᵥ (z ∘ Sum.inr)) := eq_neg_of_add_eq_zero_left hz1
      rw [this, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, hz2, zero_dotProduct] at hpos
      simp at hpos
    have hw : z ∘ Sum.inr = 0 := by
      apply GT_inj P u hG
      rw [hv, mulVec_zero, zero_add] at hz1
      exact hz1
    apply hz0
    funext e
    rcases e with k | e
    · exact congrFun hv k
    · exact congrFun hw e
  · intro hdet v hv0 hh hg
    have hsonc := sonc_1_6 P u hu hmin lam mu hkkt hG
    by_contra hle
    have hq : v ⬝ᵥ (A *ᵥ v) = 0 := le_antisymm (not_lt.mp hle) (hsonc v hh hg)
    have hGv : G *ᵥ v = 0 := (hGz v).mpr ⟨hh, hg⟩
    -- `A v` vanishes on `ker G`
    have hperp : ∀ z, G *ᵥ z = 0 → (A *ᵥ v) ⬝ᵥ z = 0 := by
      intro z hz
      have hsym : ∀ x y : Fin n → ℝ, x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
        intro x y
        rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hA, hess_symm]
      have hquad : ∀ t : ℝ, 0 ≤ 2 * t * ((A *ᵥ v) ⬝ᵥ z) + t ^ 2 * (z ⬝ᵥ (A *ᵥ z)) := by
        intro t
        have hw : G *ᵥ (v + t • z) = 0 := by
          rw [mulVec_add, mulVec_smul, hGv, hz, smul_zero, add_zero]
        have := hsonc (v + t • z) ((hGz _).mp hw).1 ((hGz _).mp hw).2
        have e1 : (v + t • z) ⬝ᵥ (A *ᵥ (v + t • z)) =
            v ⬝ᵥ (A *ᵥ v) + t * (v ⬝ᵥ (A *ᵥ z)) + t * (z ⬝ᵥ (A *ᵥ v)) +
              t ^ 2 * (z ⬝ᵥ (A *ᵥ z)) := by
          simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
            dotProduct_smul, smul_eq_mul]
          ring
        rw [e1, hq, hsym v z, dotProduct_comm z (A *ᵥ v)] at this
        linarith
      have hb : 0 ≤ z ⬝ᵥ (A *ᵥ z) := hsonc z ((hGz _).mp hz).1 ((hGz _).mp hz).2
      set a := (A *ᵥ v) ⬝ᵥ z
      set b := z ⬝ᵥ (A *ᵥ z)
      have h1 := hquad (-a / (b + 1))
      have hb1 : 0 < b + 1 := by linarith
      by_contra ha
      have ha2 : 0 < a ^ 2 := by positivity
      have : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b =
          -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
        field_simp
        ring
      rw [this] at h1
      have : 0 < a ^ 2 * (b + 2) / (b + 1) ^ 2 := by positivity
      linarith [neg_div ((b + 1) ^ 2) (a ^ 2 * (b + 2))]
    obtain ⟨ν, hν⟩ := mem_rowspace G (A *ᵥ v) hperp
    apply hdet
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨Sum.elim v (-ν), ?_, ?_⟩
    · intro h0
      apply hv0
      funext k
      exact congrFun h0 (Sum.inl k)
    · rw [hH]
      have e1 : (Sum.elim v (-ν) ∘ Sum.inl : Fin n → ℝ) = v := rfl
      have e2 : (Sum.elim v (-ν) ∘ Sum.inr) = -ν := rfl
      rw [e1, e2, hGv, mulVec_neg, ← hν, add_neg_cancel]
      funext e
      rcases e with k | e <;> rfl

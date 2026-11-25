-- Prove2me | solution 1 for GlobalTheory.flat_quotSMulTop_coker_of_matrix_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:41.348649+00:00
-- url     : https://prove2.me/submissions/9a19c742-8e65-4cf7-865e-832a36930de3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FlatQuotSMulTopCokerOfMatrixWitnesses
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_id
import Theorems.Thm_GlobalTheory_IsGradedMap_liftQ
import Theorems.Thm_GlobalTheory_IsGradedMap_pi
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (r a b : ℕ) (g : Fin r → S) (u : S) (Φ : Matrix (Fin a) (Fin b) S), Module.Flat R (S ⧸ Ideal.span (Set.range g)) → (∃ c : Fin r → S, u = ∑ k, c k * g k) → (∀ k, ∃ (C : Matrix (Fin b) (Fin a) S) (C' : Matrix (Fin a) (Fin a) S), g k • (1 : Matrix (Fin a) (Fin a) S) = Φ * C + u • C') → (∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S), Φ * Ψ * Φ = Φ + ∑ k, g k • E k) → Module.Flat R (QuotSMulTop u ((Fin a → S) ⧸ LinearMap.range Φ.mulVecLin)) := by
  intro R S _ _ _ r a b g u Φ hflat hu hker hreg
  obtain ⟨c, hc⟩ := hu
  obtain ⟨Ψ, E, hΨ⟩ := hreg
  let I : Ideal S := Ideal.span (Set.range g)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have huI : u ∈ I := by
    rw [hc]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hgI k)
  have hmv : ∀ {m : ℕ} (A : Matrix (Fin a) (Fin m) S), (∀ j i, A j i ∈ I) →
      ∀ y j, (Matrix.mulVec A y) j ∈ I := by
    intro m A hA y j
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hA j i)
  let K := LinearMap.range Φ.mulVecLin
  let M := (Fin a → S) ⧸ K
  let T : Submodule S M := u • (⊤ : Submodule S M)
  let pr : (Fin a → S) →ₗ[S] QuotSMulTop u M := T.mkQ ∘ₗ K.mkQ
  have hK : ∀ y, pr (Matrix.mulVec Φ y) = 0 := by
    intro y
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    have hy : K.mkQ (Matrix.mulVec Φ y) = 0 := (Submodule.Quotient.mk_eq_zero K).2 ⟨y, rfl⟩
    rw [hy, Submodule.Quotient.mk_zero]
  have hU : ∀ z, pr (u • z) = 0 := by
    intro z
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [map_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hG : ∀ k x, g k • pr x = 0 := by
    intro k x
    obtain ⟨C, C', h⟩ := hker k
    have hx : g k • x = Matrix.mulVec Φ (Matrix.mulVec C x) + u • Matrix.mulVec C' x := by
      have := congrArg (fun A => Matrix.mulVec A x) h
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec] at this
      exact this
    rw [← map_smul, hx, map_add, hK, hU, add_zero]
  have hI : ∀ s ∈ I, ∀ x, s • pr x = 0 := by
    intro s hs x
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hs
    simp only [Finset.sum_smul, smul_eq_mul, mul_smul, hG, smul_zero, Finset.sum_const_zero]
  let q : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) :=
    LinearMap.pi fun j => (Submodule.mkQ I) ∘ₗ LinearMap.proj j
  have hq : ∀ v, (∀ j, v j ∈ I) → q v = 0 := by
    intro v hv
    funext j
    exact (Submodule.Quotient.mk_eq_zero I).2 (hv j)
  have hqI : ∀ s ∈ I, ∀ w : Fin a → S ⧸ I, s • w = 0 := by
    intro s hs w
    funext j
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective I (w j)
    rw [Pi.smul_apply, ← ht, ← Submodule.Quotient.mk_smul, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hs
  have hE : ∀ j i, (∑ k, g k • E k) j i ∈ I := by
    intro j i
    rw [Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hgI k)
  let f0 : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) := q ∘ₗ (LinearMap.id - (Φ * Ψ).mulVecLin)
  have h1 : K ≤ LinearMap.ker f0 := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [f0, LinearMap.comp_apply]
    apply hq
    intro j
    have hy : Φ.mulVecLin y - (Φ * Ψ).mulVecLin (Φ.mulVecLin y) = -(Matrix.mulVec (∑ k, g k • E k) y) := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hΨ, Matrix.add_mulVec]
      abel
    rw [LinearMap.sub_apply, LinearMap.id_apply, hy, Pi.neg_apply]
    exact Submodule.neg_mem _ (hmv _ hE y j)
  let f1 : M →ₗ[S] (Fin a → S ⧸ I) := K.liftQ f0 h1
  have h2 : T ≤ LinearMap.ker f1 := by
    intro m hm
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    rw [LinearMap.mem_ker, map_smul]
    exact hqI u huI _
  let i : QuotSMulTop u M →ₗ[S] (Fin a → S ⧸ I) := T.liftQ f1 h2
  let p : (Fin a → S ⧸ I) →ₗ[S] QuotSMulTop u M :=
    ∑ j, (Submodule.liftQ I (LinearMap.toSpanSingleton S _ (pr (Pi.single j 1)))
      (fun s hs => by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
        exact hI s hs _)) ∘ₗ LinearMap.proj j
  have hpq : ∀ v, p (q v) = pr v := by
    intro v
    simp only [p, q, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply]
    conv_rhs => rw [← Finset.univ_sum_single v, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    refine congrArg pr ?_
    funext k
    by_cases h : k = j <;> simp [h]
  have hpi : p ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun n => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective T n
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K m
    show p (q (x - (Φ * Ψ).mulVecLin x)) = pr x
    rw [hpq, map_sub, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hK, sub_zero]
  have := hflat
  have : Module.Flat R (Fin a → S ⧸ I) :=
    Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin a => S ⧸ I)).symm
  exact Module.Flat.of_retract (i.restrictScalars R) (p.restrictScalars R)
    (LinearMap.ext fun n => LinearMap.congr_fun hpi n)
end GlobalTheory

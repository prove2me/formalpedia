-- Prove2me | solution 1 for HomogeneousLocalization.Away.isPushout_map_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/edc7f6c7-af77-5bf9-880e-891d30010922

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HomogeneousLocalization_Away_isPushout_map_of_isBaseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open scoped TensorProduct

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hbc : ∀ n, IsBaseChange S' ((ϑ.toLinearMap.restrict (p := 𝓡 n) (q := (𝓡' n).restrictScalars S) (hϑdeg n))
      : 𝓡 n →ₗ[S] (𝓡' n).restrictScalars S))
    {d : ℕ} (r : R) (hr : r ∈ 𝓡 d) :
    IsPushout
      (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom 𝓡 (Submonoid.powers r)).comp
        ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))
      (CommRingCat.ofHom (algebraMap S S'))
      (CommRingCat.ofHom (HomogeneousLocalization.Away.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') r))
      (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom 𝓡'
          (Submonoid.powers (({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') r))).comp
        ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R')))) := by
  classical
  set θ : 𝓡 →+*ᵍ 𝓡' := { ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } with hθdef
  have hθ : ∀ x, θ x = ϑ x := fun _ => rfl
  have hθr : θ r ∈ 𝓡' d := hϑdeg _ _ hr
  have hz : ∀ s : S, (GradedRing.projZeroRingHom' 𝓡 (algebraMap S R s) : R) = algebraMap S R s := fun s => by
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_same 𝓡 (SetLike.algebraMap_mem_graded 𝓡 s)]
  have hz' : ∀ s : S', (GradedRing.projZeroRingHom' 𝓡' (algebraMap S' R' s) : R') = algebraMap S' R' s := fun s => by
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_same 𝓡' (SetLike.algebraMap_mem_graded 𝓡' s)]

  let toA : S →+* HomogeneousLocalization.Away 𝓡 r :=
    (HomogeneousLocalization.fromZeroRingHom 𝓡 (Submonoid.powers r)).comp
      ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))
  let toB : S' →+* HomogeneousLocalization.Away 𝓡' (θ r) :=
    (HomogeneousLocalization.fromZeroRingHom 𝓡' (Submonoid.powers (θ r))).comp
      ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R'))
  let m : HomogeneousLocalization.Away 𝓡 r →+* HomogeneousLocalization.Away 𝓡' (θ r) := HomogeneousLocalization.Away.map θ r
  have val_toA : ∀ s : S, (toA s).val = Localization.mk (algebraMap S R s) 1 := fun s => by
    show (HomogeneousLocalization.mk _).val = _
    rw [HomogeneousLocalization.val_mk]
    exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by simp [hz]))
  have val_toB : ∀ s : S', (toB s).val = Localization.mk (algebraMap S' R' s) 1 := fun s => by
    show (HomogeneousLocalization.mk _).val = _
    rw [HomogeneousLocalization.val_mk]
    exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by simp [hz']))

  letI iSA : Algebra S (HomogeneousLocalization.Away 𝓡 r) :=
    { algebraMap := toA
      commutes' := fun _ _ => mul_comm _ _
      smul_def' := fun s y => by
        obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
        apply HomogeneousLocalization.val_injective
        rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul, val_toA,
          HomogeneousLocalization.val_mk, Localization.smul_mk, Localization.mk_mul]
        exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by simp [Algebra.smul_def])) }
  letI iS'B : Algebra S' (HomogeneousLocalization.Away 𝓡' (θ r)) :=
    { algebraMap := toB
      commutes' := fun _ _ => mul_comm _ _
      smul_def' := fun s y => by
        obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
        apply HomogeneousLocalization.val_injective
        rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul, val_toB,
          HomogeneousLocalization.val_mk, Localization.smul_mk, Localization.mk_mul]
        exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by simp [Algebra.smul_def])) }
  letI iAB : Algebra (HomogeneousLocalization.Away 𝓡 r) (HomogeneousLocalization.Away 𝓡' (θ r)) := m.toAlgebra
  letI iSB : Algebra S (HomogeneousLocalization.Away 𝓡' (θ r)) := (toB.comp (algebraMap S S')).toAlgebra
  haveI : IsScalarTower S S' (HomogeneousLocalization.Away 𝓡' (θ r)) :=
    (IsScalarTower.of_algebraMap_eq (R := S) (S := S') (A := HomogeneousLocalization.Away 𝓡' (θ r))
      (fun _ => rfl) :)
  have hsq : ∀ s : S, m (toA s) = toB (algebraMap S S' s) := by
    intro s
    apply HomogeneousLocalization.val_injective
    rw [val_toB]
    show (HomogeneousLocalization.Away.map θ r (HomogeneousLocalization.mk _)).val = _
    rw [HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
    refine Localization.mk_eq_mk_iff.2 (Localization.r_of_eq ?_)
    simp [hz, hθ, IsScalarTower.algebraMap_apply S S' R']
  haveI : IsScalarTower S (HomogeneousLocalization.Away 𝓡 r) (HomogeneousLocalization.Away 𝓡' (θ r)) :=
    (IsScalarTower.of_algebraMap_eq (R := S) (S := HomogeneousLocalization.Away 𝓡 r)
      (A := HomogeneousLocalization.Away 𝓡' (θ r)) (fun s => (hsq s).symm) :)

  let φ : S' ⊗[S] HomogeneousLocalization.Away 𝓡 r →ₗ[S'] HomogeneousLocalization.Away 𝓡' (θ r) :=
    (Algebra.TensorProduct.lift (Algebra.ofId S' (HomogeneousLocalization.Away 𝓡' (θ r))) (IsScalarTower.toAlgHom S (HomogeneousLocalization.Away 𝓡 r) (HomogeneousLocalization.Away 𝓡' (θ r)))
      (fun _ _ => Commute.all _ _)).toLinearMap
  have φ_tmul : ∀ (s : S') (a : HomogeneousLocalization.Away 𝓡 r), φ (s ⊗ₜ[S] a) = s • m a := fun s a => by
    change (Algebra.TensorProduct.lift (Algebra.ofId S' (HomogeneousLocalization.Away 𝓡' (θ r))) (IsScalarTower.toAlgHom S (HomogeneousLocalization.Away 𝓡 r) (HomogeneousLocalization.Away 𝓡' (θ r)))
      (fun _ _ => Commute.all _ _)) (s ⊗ₜ[S] a) = s • m a
    rw [Algebra.TensorProduct.lift_tmul, @Algebra.smul_def _ _ _ _ iS'B]
    rfl

  have hμ : ∀ (n n₂ : ℕ), n ≤ n₂ → ∀ x : R, x ∈ 𝓡 (n • d) → r ^ (n₂ - n) * x ∈ 𝓡 (n₂ • d) := by
    intro n n₂ h x hx
    have := SetLike.mul_mem_graded (SetLike.pow_mem_graded (n₂ - n) hr) hx
    rwa [← add_nsmul, Nat.sub_add_cancel h] at this

  let μ : ∀ (n n₂ : ℕ), n ≤ n₂ → (↥(𝓡 (n • d)) →ₗ[S] ↥(𝓡 (n₂ • d))) := fun n n₂ h =>
    { toFun := fun x => ⟨r ^ (n₂ - n) * x, hμ n n₂ h x x.2⟩
      map_add' := fun x y => by ext; simp only [Submodule.coe_add, mul_add]
      map_smul' := fun s x => by ext; simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have μ_coe : ∀ (n n₂ : ℕ) (h : n ≤ n₂) (x : ↥(𝓡 (n • d))), ((μ n n₂ h x : ↥(𝓡 (n₂ • d))) : R) = r ^ (n₂ - n) * x :=
    fun _ _ _ _ => rfl

  let mkA : ∀ k : ℕ, (↥(𝓡 (k • d)) →ₗ[S] HomogeneousLocalization.Away 𝓡 r) := fun k =>
    { toFun := fun x => HomogeneousLocalization.Away.mk 𝓡 hr k x x.2
      map_add' := fun x y => by
        apply HomogeneousLocalization.val_injective
        rw [HomogeneousLocalization.val_add]
        simp only [HomogeneousLocalization.Away.val_mk, Submodule.coe_add, Localization.add_mk_self]
      map_smul' := fun s x => by
        apply HomogeneousLocalization.val_injective
        rw [RingHom.id_apply, HomogeneousLocalization.val_smul]
        simp only [HomogeneousLocalization.Away.val_mk, Submodule.coe_smul, Localization.smul_mk] }
  have mkA_apply : ∀ (k : ℕ) (x : ↥(𝓡 (k • d))), mkA k x = HomogeneousLocalization.Away.mk 𝓡 hr k x x.2 :=
    fun _ _ => rfl

  let mkB : ∀ k : ℕ, (↥((𝓡' (k • d)).restrictScalars S) →ₗ[S'] HomogeneousLocalization.Away 𝓡' (θ r)) := fun k =>
    { toFun := fun y => HomogeneousLocalization.Away.mk 𝓡' hθr k y y.2
      map_add' := fun x y => by
        apply HomogeneousLocalization.val_injective
        rw [HomogeneousLocalization.val_add]
        simp only [HomogeneousLocalization.Away.val_mk, Submodule.coe_add, Localization.add_mk_self]
      map_smul' := fun s y => by
        apply HomogeneousLocalization.val_injective
        rw [RingHom.id_apply, HomogeneousLocalization.val_smul]
        simp only [HomogeneousLocalization.Away.val_mk, Localization.smul_mk]
        rfl }
  have mkA_μ : ∀ (n n₂ : ℕ) (h : n ≤ n₂) (x : ↥(𝓡 (n • d))), mkA n₂ (μ n n₂ h x) = mkA n x := by
    intro n n₂ h x
    apply HomogeneousLocalization.val_injective
    rw [mkA_apply, mkA_apply, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
    refine Localization.mk_eq_mk_iff.2 (Localization.r_of_eq ?_)
    simp only [μ_coe]
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

  let E : ∀ k : ℕ, (S' ⊗[S] ↥(𝓡 (k • d)) ≃ₗ[S'] ↥((𝓡' (k • d)).restrictScalars S)) := fun k => (hbc (k • d)).equiv
  have coe_smul' : ∀ (k : ℕ) (s : S') (y : ↥((𝓡' (k • d)).restrictScalars S)), ((s • y : ↥((𝓡' (k • d)).restrictScalars S)) : R') = s • (y : R') :=
    fun _ _ _ => rfl
  have E_tmul : ∀ (k : ℕ) (s : S') (x : ↥(𝓡 (k • d))), ((E k (s ⊗ₜ[S] x) : ↥((𝓡' (k • d)).restrictScalars S)) : R') = algebraMap S' R' s * ϑ x := by
    intro k s x
    show (((hbc (k • d)).equiv (s ⊗ₜ[S] x) : ↥((𝓡' (k • d)).restrictScalars S)) : R') = _
    rw [IsBaseChange.equiv_tmul, coe_smul', Algebra.smul_def]
    rfl

  let τ : ∀ k : ℕ, (S' ⊗[S] ↥(𝓡 (k • d)) →ₗ[S'] S' ⊗[S] HomogeneousLocalization.Away 𝓡 r) := fun k => (mkA k).baseChange S'
  have hτμ : ∀ (n n₂ : ℕ) (h : n ≤ n₂) (t : S' ⊗[S] ↥(𝓡 (n • d))), τ n₂ ((μ n n₂ h).baseChange S' t) = τ n t := by
    intro n n₂ h t
    have hc : mkA n₂ ∘ₗ μ n n₂ h = mkA n := LinearMap.ext (mkA_μ n n₂ h)
    show (mkA n₂).baseChange S' ((μ n n₂ h).baseChange S' t) = (mkA n).baseChange S' t
    rw [← hc, LinearMap.baseChange_comp]
    rfl

  have hφτ : ∀ (k : ℕ) (t : S' ⊗[S] ↥(𝓡 (k • d))), φ (τ k t) = mkB k (E k t) := by
    intro k
    have : φ ∘ₗ τ k = mkB k ∘ₗ (E k).toLinearMap := by
      refine TensorProduct.AlgebraTensorModule.ext fun s x => ?_
      show φ ((mkA k).baseChange S' (s ⊗ₜ[S] x)) = mkB k ((hbc (k • d)).equiv (s ⊗ₜ[S] x))
      rw [LinearMap.baseChange_tmul, φ_tmul, IsBaseChange.equiv_tmul, map_smul, mkA_apply]
      congr 1
      show HomogeneousLocalization.Away.map θ r _ = _
      rw [HomogeneousLocalization.Away.map_mk]
      rfl
    intro t
    exact congrArg (fun f => f t) (congrArg DFunLike.coe this)

  have hcommon : ∀ u : S' ⊗[S] HomogeneousLocalization.Away 𝓡 r, ∃ (n : ℕ) (t : S' ⊗[S] ↥(𝓡 (n • d))), τ n t = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, map_zero _⟩
    | tmul s a =>
      obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝓡 hr a
      refine ⟨n, s ⊗ₜ[S] ⟨x, hx⟩, ?_⟩
      show (mkA n).baseChange S' _ = _
      rw [LinearMap.baseChange_tmul]
      rfl
    | add u v hu hv =>
      obtain ⟨n, t, rfl⟩ := hu
      obtain ⟨n', t', rfl⟩ := hv
      refine ⟨n + n', (μ n (n + n') (Nat.le_add_right n n')).baseChange S' t +
        (μ n' (n + n') (Nat.le_add_left n' n)).baseChange S' t', ?_⟩
      rw [map_add, hτμ n (n + n') (Nat.le_add_right n n'), hτμ n' (n + n') (Nat.le_add_left n' n)]

  have hmkB0 : ∀ (n : ℕ) (y : ↥((𝓡' (n • d)).restrictScalars S)), mkB n y = 0 → ∃ N : ℕ, θ r ^ N * (y : R') = 0 := by
    intro n y hy
    have hv := congrArg HomogeneousLocalization.val hy
    rw [HomogeneousLocalization.val_zero] at hv
    change (HomogeneousLocalization.Away.mk 𝓡' hθr n y y.2).val = 0 at hv
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hv
    obtain ⟨⟨c, ⟨N, hc⟩⟩, hc0⟩ := hv
    exact ⟨N, by simpa [← hc] using hc0⟩

  have hEμ : ∀ (n n₂ : ℕ) (h : n ≤ n₂) (t : S' ⊗[S] ↥(𝓡 (n • d))),
      ((E n₂ ((μ n n₂ h).baseChange S' t) : ↥((𝓡' (n₂ • d)).restrictScalars S)) : R') = θ r ^ (n₂ - n) * ((E n t : ↥((𝓡' (n • d)).restrictScalars S)) : R') := by
    intro n n₂ h t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, ZeroMemClass.coe_zero, mul_zero]
    | tmul s x =>
      rw [LinearMap.baseChange_tmul, E_tmul, E_tmul, μ_coe n n₂ h, map_mul, map_pow, hθ r]
      ring
    | add u v hu hv =>
      simp only [map_add, AddMemClass.coe_add, mul_add, hu, hv]
  have φ_bij : Function.Bijective φ := by
    refine ⟨(injective_iff_map_eq_zero φ).2 fun u hu => ?_, fun b => ?_⟩
    · obtain ⟨n, t, rfl⟩ := hcommon u
      rw [hφτ] at hu
      obtain ⟨N, hN⟩ := hmkB0 n _ hu
      have h2 : E (n + N) ((μ n (n + N) (Nat.le_add_right n N)).baseChange S' t) = 0 := by
        apply Subtype.ext
        rw [hEμ n (n + N) (Nat.le_add_right n N), Nat.add_sub_cancel_left, hN, ZeroMemClass.coe_zero]
      have h3 : (μ n (n + N) (Nat.le_add_right n N)).baseChange S' t = 0 := (E (n + N)).map_eq_zero_iff.mp h2
      rw [← hτμ n (n + N) (Nat.le_add_right n N) t, h3, map_zero]
    · obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝓡' hθr b
      refine ⟨τ n ((E n).symm ⟨y, hy⟩), ?_⟩
      rw [hφτ, LinearEquiv.apply_symm_apply]
      rfl
  let e : S' ⊗[S] HomogeneousLocalization.Away 𝓡 r ≃ₗ[S'] HomogeneousLocalization.Away 𝓡' (θ r) := LinearEquiv.ofBijective φ φ_bij
  haveI : Algebra.IsPushout S S' (HomogeneousLocalization.Away 𝓡 r) (HomogeneousLocalization.Away 𝓡' (θ r)) :=
    ⟨IsBaseChange.of_equiv e (fun a => by
      show φ ((1 : S') ⊗ₜ a) = m a
      rw [φ_tmul, one_smul])⟩
  exact (CommRingCat.isPushout_of_isPushout S S' (HomogeneousLocalization.Away 𝓡 r) (HomogeneousLocalization.Away 𝓡' (θ r))).flip

end S_HomogeneousLocalization_Away_isPushout_map_of_isBaseChange
end P2MW
export P2MW.S_HomogeneousLocalization_Away_isPushout_map_of_isBaseChange (solution)

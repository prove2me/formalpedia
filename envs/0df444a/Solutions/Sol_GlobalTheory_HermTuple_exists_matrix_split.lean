-- Prove2me | solution 1 for GlobalTheory.HermTuple.exists_matrix_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:16:59.48585+00:00
-- url     : https://prove2.me/submissions/6d427545-f6ac-45be-b95f-7d9465442d35

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEquivOfRetractions
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HermTuple
open Matrix Module
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in
private theorem exists_inv_pair_mul_eq_of_mul_eq {K n m : Type*} [Field K] [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] (X Y : Matrix n m K) (A A' : Matrix m n K)
    (hM : IsUnit (A * X).det) (h : A' * Y = A * X) :
    ∃ T T' : Matrix n n K, T * T' = 1 ∧ T' * T = 1 ∧ T * X = Y ∧ A' * T = A := by
  obtain ⟨N, hN1, hN2⟩ : ∃ N : Matrix m m K, A * X * N = 1 ∧ N * (A * X) = 1 :=
    ⟨(A * X)⁻¹, Matrix.mul_nonsing_inv _ hM, Matrix.nonsing_inv_mul _ hM⟩
  have hAXN : ∀ w, A *ᵥ (X *ᵥ (N *ᵥ w)) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN1, Matrix.one_mulVec]
  have hAYN : ∀ w, A' *ᵥ (Y *ᵥ (N *ᵥ w)) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, hN1, Matrix.one_mulVec]
  have hNAX : ∀ w, N *ᵥ (A *ᵥ (X *ᵥ w)) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hN2, Matrix.one_mulVec]
  have hsurj : Function.Surjective (Matrix.mulVecLin A) := fun w =>
    ⟨X *ᵥ (N *ᵥ w), by rw [Matrix.mulVecLin_apply, hAXN]⟩
  have hsurj' : Function.Surjective (Matrix.mulVecLin A') := fun w =>
    ⟨Y *ᵥ (N *ᵥ w), by rw [Matrix.mulVecLin_apply, hAYN]⟩
  have hrank : Module.finrank K (LinearMap.ker (Matrix.mulVecLin A)) =
      Module.finrank K (LinearMap.ker (Matrix.mulVecLin A')) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
    have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A')
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
    rw [LinearMap.range_eq_top.mpr hsurj', finrank_top] at h2
    omega
  let ψ := LinearEquiv.ofFinrankEq _ _ hrank
  let p : (n → K) →ₗ[K] LinearMap.ker (Matrix.mulVecLin A) :=
    LinearMap.codRestrict _ (LinearMap.id - Matrix.mulVecLin (X * N * A)) fun v => by
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, LinearMap.sub_apply,
        LinearMap.id_apply, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, hAXN, sub_self]
  let p' : (n → K) →ₗ[K] LinearMap.ker (Matrix.mulVecLin A') :=
    LinearMap.codRestrict _ (LinearMap.id - Matrix.mulVecLin (Y * N * A')) fun v => by
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, LinearMap.sub_apply,
        LinearMap.id_apply, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, hAYN, sub_self]
  let φ : (n → K) →ₗ[K] (n → K) := Matrix.mulVecLin (Y * N * A) +
    (LinearMap.ker (Matrix.mulVecLin A')).subtype ∘ₗ ψ.toLinearMap ∘ₗ p
  let φ' : (n → K) →ₗ[K] (n → K) := Matrix.mulVecLin (X * N * A') +
    (LinearMap.ker (Matrix.mulVecLin A)).subtype ∘ₗ ψ.symm.toLinearMap ∘ₗ p'
  have hker : ∀ k : LinearMap.ker (Matrix.mulVecLin A'), A' *ᵥ (k : n → K) = 0 := fun k => k.2
  have hker' : ∀ k : LinearMap.ker (Matrix.mulVecLin A), A *ᵥ (k : n → K) = 0 := fun k => k.2
  have hφ_eq : ∀ v, φ v = Y *ᵥ (N *ᵥ (A *ᵥ v)) + (ψ (p v) : n → K) := fun v => by
    simp only [φ, LinearMap.add_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Submodule.subtype_apply, LinearEquiv.coe_coe, ← Matrix.mulVec_mulVec]
  have hφ'_eq : ∀ u, φ' u = X *ᵥ (N *ᵥ (A' *ᵥ u)) + (ψ.symm (p' u) : n → K) := fun u => by
    simp only [φ', LinearMap.add_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Submodule.subtype_apply, LinearEquiv.coe_coe, ← Matrix.mulVec_mulVec]
  have hp_eq : ∀ v, (p v : n → K) = v - X *ᵥ (N *ᵥ (A *ᵥ v)) := fun v => by
    simp only [p, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  have hp'_eq : ∀ u, (p' u : n → K) = u - Y *ᵥ (N *ᵥ (A' *ᵥ u)) := fun u => by
    simp only [p', LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  have hAφ : ∀ v, A' *ᵥ φ v = A *ᵥ v := fun v => by
    rw [hφ_eq, Matrix.mulVec_add, hAYN, hker, add_zero]
  have hAφ' : ∀ u, A *ᵥ φ' u = A' *ᵥ u := fun u => by
    rw [hφ'_eq, Matrix.mulVec_add, hAXN, hker', add_zero]
  have hpφ : ∀ v, p' (φ v) = ψ (p v) := fun v => by
    apply Subtype.ext
    rw [hp'_eq, hAφ, hφ_eq, add_sub_cancel_left]
  have hpφ' : ∀ u, p (φ' u) = ψ.symm (p' u) := fun u => by
    apply Subtype.ext
    rw [hp_eq, hAφ', hφ'_eq, add_sub_cancel_left]
  have hleft : ∀ v, φ' (φ v) = v := fun v => by
    rw [hφ'_eq, hpφ, hAφ, LinearEquiv.symm_apply_apply, hp_eq, add_sub_cancel]
  have hright : ∀ u, φ (φ' u) = u := fun u => by
    rw [hφ_eq, hpφ', hAφ', LinearEquiv.apply_symm_apply, hp'_eq, add_sub_cancel]
  have hφX : ∀ w, φ (X *ᵥ w) = Y *ᵥ w := fun w => by
    have hpX : p (X *ᵥ w) = 0 := by
      apply Subtype.ext
      rw [hp_eq, hNAX, sub_self, ZeroMemClass.coe_zero]
    rw [hφ_eq, hpX, map_zero, ZeroMemClass.coe_zero, add_zero, hNAX]
  refine ⟨LinearMap.toMatrix' φ, LinearMap.toMatrix' φ', ?_, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext hright
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext hleft
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply,
      Matrix.toLin'_apply, hφX]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply,
      Matrix.toLin'_apply, hAφ]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in
private theorem matrix_eq_of_map_fst_snd {K E p q : Type*} [Field K] [CommRing E]
    (e : E ≃+* K × K) {P Q : Matrix p q E}
    (h₁ : P.map ((RingHom.fst K K).comp e.toRingHom) = Q.map ((RingHom.fst K K).comp e.toRingHom))
    (h₂ : P.map ((RingHom.snd K K).comp e.toRingHom) = Q.map ((RingHom.snd K K).comp e.toRingHom)) :
    P = Q := by
  ext a b
  apply e.injective
  exact Prod.ext (congrFun (congrFun h₁ a) b) (congrFun (congrFun h₂ a) b)
end GlobalTheory.HermTuple
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HermTuple
open Matrix Module
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
open Matrix Module
namespace GlobalTheory.HermTuple
namespace _root_.GlobalTheory.HermTuple
theorem _root_.solution {K E n m : Type*} [Field K] [CommRing E]
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (c : E →+* E) (e : E ≃+* K × K) (he : ∀ x, e (c x) = (e x).swap)
    (G : Matrix n n E) (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) (X Y : Matrix n m E)
    (hu : IsUnit (Xᵀ * G * X.map c).det) (h : Yᵀ * G * Y.map c = Xᵀ * G * X.map c) :
    ∃ γ : Matrix n n E, γᵀ * G * γ.map c = G ∧ γ * X = Y := by
  set f₁ : E →+* K := (RingHom.fst K K).comp e.toRingHom with hf₁
  set f₂ : E →+* K := (RingHom.snd K K).comp e.toRingHom with hf₂
  have hc₁ : ∀ z, f₁ (c z) = f₂ z := fun z => by
    simp only [hf₁, hf₂, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he, Prod.fst_swap]
  have hc₂ : ∀ z, f₂ (c z) = f₁ z := fun z => by
    simp only [hf₁, hf₂, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he, Prod.snd_swap]
  have hXc₁ : (X.map c).map f₁ = X.map f₂ := by ext; simp [hc₁]
  have hYc₁ : (Y.map c).map f₁ = Y.map f₂ := by ext; simp [hc₁]
  have hG₂ : G.map f₂ = (G.map f₁)ᵀ := by
    ext a b
    rw [Matrix.map_apply, ← hG b a, hc₂]
    rfl
  have hG₁ : IsUnit (G.map f₁).det := by
    have := hdet.map f₁
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at this
  have hM : IsUnit ((G.map f₁ * X.map f₂)ᵀ * X.map f₁).det := by
    have := hu.map f₁
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, hXc₁] at this
    rw [Matrix.transpose_mul, ← Matrix.det_transpose]
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have h₁ : (Y.map f₁)ᵀ * G.map f₁ * Y.map f₂ = (X.map f₁)ᵀ * G.map f₁ * X.map f₂ := by
    have := congrArg (fun P => Matrix.map P f₁) h
    simpa only [Matrix.map_mul, Matrix.transpose_map, hXc₁, hYc₁] using this
  have hA : (G.map f₁ * Y.map f₂)ᵀ * Y.map f₁ = (G.map f₁ * X.map f₂)ᵀ * X.map f₁ := by
    have := congrArg Matrix.transpose h₁
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  obtain ⟨T, T', hTT', hT'T, hTX, hAT⟩ :=
    exists_inv_pair_mul_eq_of_mul_eq (X.map f₁) (Y.map f₁) _ _ hM hA
  have hGG : G.map f₁ * (G.map f₁)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG₁
  have hGG' : (G.map f₁)⁻¹ * G.map f₁ = 1 := Matrix.nonsing_inv_mul _ hG₁
  let γ : Matrix n n E := Matrix.of fun a b => e.symm (T a b, ((G.map f₁)⁻¹ * T'ᵀ * G.map f₁) a b)
  have hγ₁ : γ.map f₁ = T := by ext; simp [γ, hf₁]
  have hγ₂ : γ.map f₂ = (G.map f₁)⁻¹ * T'ᵀ * G.map f₁ := by ext; simp [γ, hf₂]
  have hγc₁ : (γ.map c).map f₁ = γ.map f₂ := by ext; simp only [Matrix.map_apply, hc₁]
  have hγc₂ : (γ.map c).map f₂ = γ.map f₁ := by ext; simp only [Matrix.map_apply, hc₂]
  have key : Tᵀ * G.map f₁ * ((G.map f₁)⁻¹ * T'ᵀ * G.map f₁) = G.map f₁ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (G.map f₁), ← Matrix.mul_assoc (G.map f₁), hGG,
      Matrix.one_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hT'T, Matrix.transpose_one,
      Matrix.one_mul]
  have hTY : Tᵀ * (G.map f₁ * Y.map f₂) = G.map f₁ * X.map f₂ := by
    have := congrArg Matrix.transpose hAT
    simpa [Matrix.transpose_mul] using this
  refine ⟨γ, matrix_eq_of_map_fst_snd e ?_ ?_, matrix_eq_of_map_fst_snd e ?_ ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hγ₁, hγc₁, hγ₂, key]
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hγ₂, hγc₂, hγ₁, hG₂]
    have := congrArg Matrix.transpose key
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · rw [Matrix.map_mul, hγ₁, hTX]
  · rw [Matrix.map_mul, hγ₂, Matrix.mul_assoc, Matrix.mul_assoc, ← hTY, ← Matrix.mul_assoc T'ᵀ,
      ← Matrix.transpose_mul, hTT', Matrix.transpose_one, Matrix.one_mul, ← Matrix.mul_assoc,
      hGG', Matrix.one_mul]
end _root_.GlobalTheory.HermTuple
end GlobalTheory.HermTuple

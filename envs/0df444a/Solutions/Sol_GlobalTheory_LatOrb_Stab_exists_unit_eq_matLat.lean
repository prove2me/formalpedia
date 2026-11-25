-- Prove2me | solution 1 for GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:51.262876+00:00
-- url     : https://prove2.me/submissions/1e36dcf0-e7a8-4511-8078-cb1233fb8efe

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitEqOfStableLattices
import Theorems.Thm_GlobalTheory_LatOrb_Stab_polyStable
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_LatOrb_matLat_mul
import Theorems.Thm_GlobalTheory_LatOrb_mem_matLat
import Theorems.Thm_GlobalTheory_T_integral_aeval_eq_aeval_map_of_coprime_charpoly
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLatDVR_isPrincipalIdealRing_integralClosure
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_eq_mulLat_of_isPrincipalIdealRing
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_isPrincipalIdealRing_integralClosure
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_P2M_GlobalTheory_T_exists_cyclicVector_of_separable_charpoly__05aee84c212b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
noncomputable section
open GlobalTheory GlobalTheory.LatOrb GlobalTheory.LatOrb.Stab
namespace GlobalTheory.LatOrb.Stab
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ M₁ M₂ : Submodule O (Fin n → K), IsLatV O M₁ → IsLatV O M₂ →
    (∀ v ∈ M₁, γ *ᵥ v ∈ M₁) → (∀ v ∈ M₂, γ *ᵥ v ∈ M₂) →
    ∃ p : K[X], IsUnit (aeval γ p) ∧ M₂ = matLat O (aeval γ p) M₁ := by
  intro O K _ _ _ _ _ _ _ n P₀ hcop γ hchar M₁ M₂ hL₁ hL₂ hs₁ hs₂
  have hsep : γ.charpoly.Separable := by rw [hchar]; exact Polynomial.Separable.map hcop
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.T.exists_cyclicVector_of_separable_charpoly' n γ hsep
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra K (Matrix (Fin n) (Fin n) K), A = Algebra.adjoin K {γ} :=
    ⟨_, rfl⟩
  have memA : ∀ a : Matrix (Fin n) (Fin n) K, a ∈ A ↔ ∃ p : K[X], aeval γ p = a := by
    intro a; rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; rfl
  have commA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, rfl⟩ := (memA a).1 ha
    obtain ⟨q, rfl⟩ := (memA b).1 hb
    rw [← map_mul, ← map_mul, mul_comm]
  letI : CommRing A := { A.toRing with mul_comm := fun x y => Subtype.ext (commA _ x.2 _ y.2) }
  haveI : Module.Finite K A := inferInstance
  haveI : IsReduced A := by
    refine ⟨fun a ⟨m, hm⟩ => ?_⟩
    obtain ⟨f, hf⟩ := (memA a).1 a.2
    have h0 : aeval γ (f ^ m) = 0 := by
      rw [map_pow, hf]
      exact congrArg Subtype.val hm
    have hsq : Squarefree (minpoly K γ) :=
      (hsep.of_dvd (Matrix.minpoly_dvd_charpoly γ)).squarefree
    have h1 : minpoly K γ ∣ f := hsq.isRadical m f (minpoly.dvd K γ h0)
    apply Subtype.ext
    rw [← hf]
    exact (minpoly.dvd_iff).1 h1

  let φ : A →ₗ[K] (Fin n → K) :=
    { toFun := fun a => (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  have hφ : ∀ a : A, φ a = (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀ := fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    rw [hφ] at ha
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    obtain ⟨p, rfl⟩ := hv₀ u
    obtain ⟨q, hq⟩ := (memA a).1 a.2
    change (a : Matrix (Fin n) (Fin n) K) *ᵥ (aeval γ p *ᵥ v₀) = (0 : Matrix (Fin n) (Fin n) K) *ᵥ _
    rw [Matrix.mulVec_mulVec, ← hq, ← map_mul, mul_comm, map_mul, hq, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_zero, Matrix.zero_mulVec]
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨p, rfl⟩ := hv₀ u
    exact ⟨⟨aeval γ p, (memA _).2 ⟨p, rfl⟩⟩, rfl⟩
  let e : A ≃ₗ[K] (Fin n → K) := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ a : A, e a = (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀ := fun _ => rfl
  let eO : A ≃ₗ[O] (Fin n → K) := e.restrictScalars O
  let J : Submodule O (Fin n → K) → Submodule O A := fun M => M.map (eO.symm : (Fin n → K) →ₗ[O] A)
  have memJ : ∀ M y, y ∈ J M ↔ (y : Matrix (Fin n) (Fin n) K) *ᵥ v₀ ∈ M := by
    intro M y
    simp only [J, Submodule.mem_map_equiv]
    rfl
  have latJ : ∀ M, IsLatV O M → GlobalTheory.UnitLemma.IsLat O K (J M) := by
    intro M hM
    refine ⟨hM.1.map _, ?_⟩
    have hcoe : ((J M : Submodule O A) : Set A) = (e.symm : (Fin n → K) →ₗ[K] A) '' (M : Set _) := by
      ext y; simp [J, Submodule.mem_map]; rfl
    rw [hcoe, Submodule.span_image, hM.2, Submodule.map_top, LinearEquiv.range]
  have stJ : ∀ M, (∀ v ∈ M, γ *ᵥ v ∈ M) →
      ∀ a ∈ integralClosure O A, ∀ y ∈ J M, a * y ∈ J M := by
    intro M hM a ha y hy
    have hint : IsIntegral O (a : Matrix (Fin n) (Fin n) K) :=
      (ha : IsIntegral O a).map (A.val.restrictScalars O)
    obtain ⟨p, hp⟩ := (memA _).1 a.2
    rw [← hp] at hint
    obtain ⟨r, hr⟩ := GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly n P₀ hcop γ hchar p hint
    rw [memJ] at hy ⊢
    change ((a : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) *ᵥ v₀ ∈ M
    rw [← Matrix.mulVec_mulVec, ← hp, hr]
    exact polyStable γ M hM r _ hy
  haveI : IsPrincipalIdealRing (integralClosure O A) :=
    GlobalTheory.UnitLemma.PrincipalLatDVR.isPrincipalIdealRing_integralClosure (E := K)
  set Λ : Submodule O A := Subalgebra.toSubmodule (integralClosure O A)

  have back : ∀ M (c : Aˣ), J M = GlobalTheory.UnitLemma.mulLat O (c : A) Λ →
      M = matLat O ((c : A) : Matrix (Fin n) (Fin n) K) (Λ.map (eO : A →ₗ[O] (Fin n → K))) := by
    intro M c hc
    ext v
    obtain ⟨y, rfl⟩ := hsurj v
    rw [mem_matLat]
    have h1 : φ y ∈ M ↔ y ∈ J M := by rw [memJ]; rfl
    rw [h1, hc]
    simp only [GlobalTheory.UnitLemma.mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨eO l, ⟨l, hl, rfl⟩, ?_⟩
      change ((c : A) : Matrix (Fin n) (Fin n) K) *ᵥ ((l : Matrix (Fin n) (Fin n) K) *ᵥ v₀) =
        (((c : A) * l : A) : Matrix (Fin n) (Fin n) K) *ᵥ v₀
      rw [Matrix.mulVec_mulVec]; rfl
    · rintro ⟨_, ⟨l, hl, rfl⟩, hv⟩
      refine ⟨l, hl, hinj ?_⟩
      rw [← hv]
      change (((c : A) * l : A) : Matrix (Fin n) (Fin n) K) *ᵥ v₀ =
        ((c : A) : Matrix (Fin n) (Fin n) K) *ᵥ ((l : Matrix (Fin n) (Fin n) K) *ᵥ v₀)
      rw [Matrix.mulVec_mulVec]; rfl
  obtain ⟨a₁, h₁⟩ :=
    GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_of_isPrincipalIdealRing (E := K) (J M₁) (latJ M₁ hL₁) (stJ M₁ hs₁)
  obtain ⟨a₂, h₂⟩ :=
    GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_of_isPrincipalIdealRing (E := K) (J M₂) (latJ M₂ hL₂) (stJ M₂ hs₂)
  obtain ⟨p, hp⟩ := (memA _).1 ((a₂ * a₁⁻¹ : Aˣ) : A).2
  refine ⟨p, ?_, ?_⟩
  · rw [hp]; exact (Units.isUnit (a₂ * a₁⁻¹)).map A.val
  · rw [back M₂ a₂ h₂, back M₁ a₁ h₁, ← matLat_mul, hp]
    congr 1
    change ((a₂ : A) : Matrix (Fin n) (Fin n) K) = (((a₂ * a₁⁻¹ : Aˣ) : A) * (a₁ : A) : A).1
    rw [← Units.val_mul, inv_mul_cancel_right]
end GlobalTheory.LatOrb.Stab

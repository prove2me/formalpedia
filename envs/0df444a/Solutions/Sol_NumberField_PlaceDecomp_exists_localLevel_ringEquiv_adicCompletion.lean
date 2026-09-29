-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/572b2258-0e4c-51c0-9495-c10ff92e044f

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory groupCohomology ExtCitation.LocalLevel IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 800000

namespace C8Bridge

noncomputable section

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

def vQ : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.under (𝓞 ℚ) w

def qOf : ℕ := (Rat.HeightOneSpectrum.primesEquiv (vQ K w) : Nat.Primes)
scoped instance qOf_prime : Fact (qOf K w).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv (vQ K w)).2⟩

def WExt : (vQ K w).Extension (𝓞 K) := ⟨w, rfl⟩
theorem WExt_val : (WExt K w).1 = w := rfl

scoped instance algQv : Algebra ((vQ K w).adicCompletion ℚ) (w.adicCompletion K) :=
  (inferInstance : Algebra ((vQ K w).adicCompletion ℚ) ((WExt K w).1.adicCompletion K))

scoped instance finQv : Module.Finite ((vQ K w).adicCompletion ℚ) (w.adicCompletion K) :=
  (inferInstance : Module.Finite ((vQ K w).adicCompletion ℚ) ((WExt K w).1.adicCompletion K))

def padicIso : ℚ_[qOf K w] ≃+* (vQ K w).adicCompletion ℚ :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (vQ K w)).symm.toAlgEquiv.toRingEquiv

scoped instance algPadicQv : Algebra ℚ_[qOf K w] ((vQ K w).adicCompletion ℚ) := (padicIso K w).toRingHom.toAlgebra

scoped instance algPadic : Algebra ℚ_[qOf K w] (w.adicCompletion K) :=
  ((algebraMap ((vQ K w).adicCompletion ℚ) (w.adicCompletion K)).comp (padicIso K w).toRingHom).toAlgebra

scoped instance towerPadic : IsScalarTower ℚ_[qOf K w] ((vQ K w).adicCompletion ℚ) (w.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance finPadicQv : Module.Finite ℚ_[qOf K w] ((vQ K w).adicCompletion ℚ) :=
  Module.Finite.of_surjective (Algebra.linearMap ℚ_[qOf K w] ((vQ K w).adicCompletion ℚ))
    (padicIso K w).surjective

scoped instance finPadic : Module.Finite ℚ_[qOf K w] (w.adicCompletion K) :=
  Module.Finite.trans ((vQ K w).adicCompletion ℚ) (w.adicCompletion K)

def iota : w.adicCompletion K →ₐ[ℚ_[qOf K w]] PadicAlgCl (qOf K w) :=
  haveI : Algebra.IsAlgebraic ℚ_[qOf K w] (w.adicCompletion K) := Algebra.IsAlgebraic.of_finite _ _
  IsAlgClosed.lift

end

noncomputable section
variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

def Limg : IntermediateField ℚ_[qOf K w] (PadicAlgCl (qOf K w)) := (iota K w).fieldRange

def PhiIso : w.adicCompletion K ≃ₐ[ℚ_[qOf K w]] Limg K w := AlgEquiv.ofInjectiveField (iota K w)

scoped instance finLimg : FiniteDimensional ℚ_[qOf K w] (Limg K w) :=
  Module.Finite.equiv (PhiIso K w).toLinearEquiv

variable (E : Type) [Field E] [Algebra E K]

@[reducible] def actImg : MulSemiringAction (NumberField.PlaceDecomp.decomp E K w) (Limg K w) where
  smul σ y := PhiIso K w (σ • (PhiIso K w).symm y)
  one_smul y := by show PhiIso K w ((1 : NumberField.PlaceDecomp.decomp E K w) • (PhiIso K w).symm y) = y; rw [one_smul, AlgEquiv.apply_symm_apply]
  mul_smul σ τ y := by
    show PhiIso K w ((σ * τ) • (PhiIso K w).symm y) = PhiIso K w (σ • (PhiIso K w).symm (PhiIso K w (τ • (PhiIso K w).symm y)))
    rw [AlgEquiv.symm_apply_apply, mul_smul]
  smul_zero σ := by show PhiIso K w (σ • (PhiIso K w).symm 0) = 0; rw [map_zero, smul_zero, map_zero]
  smul_add σ x y := by
    show PhiIso K w (σ • (PhiIso K w).symm (x + y)) = PhiIso K w (σ • (PhiIso K w).symm x) + PhiIso K w (σ • (PhiIso K w).symm y)
    rw [map_add, smul_add, map_add]
  smul_one σ := by show PhiIso K w (σ • (PhiIso K w).symm 1) = 1; rw [map_one, smul_one, map_one]
  smul_mul σ x y := by
    show PhiIso K w (σ • (PhiIso K w).symm (x * y)) = PhiIso K w (σ • (PhiIso K w).symm x) * PhiIso K w (σ • (PhiIso K w).symm y)
    rw [map_mul, MulSemiringAction.smul_mul, map_mul]

theorem actImg_smul_def (σ : NumberField.PlaceDecomp.decomp E K w) (y : Limg K w) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K w E).toSMul) σ y = PhiIso K w (σ • (PhiIso K w).symm y) := rfl

theorem PhiIso_smul (σ : NumberField.PlaceDecomp.decomp E K w) (x : w.adicCompletion K) :
    PhiIso K w (σ • x) = @HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K w E).toSMul) σ (PhiIso K w x) := by
  rw [actImg_smul_def, AlgEquiv.symm_apply_apply]

theorem smul_coe (σ : NumberField.PlaceDecomp.decomp E K w) (k : K) :
    σ • ((WithVal.toVal (w.valuation K) k : WithVal (w.valuation K)) : w.adicCompletion K) =
      ((WithVal.toVal (w.valuation K) ((σ : K ≃ₐ[E] K) k) : WithVal (w.valuation K)) : w.adicCompletion K) := by
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl

theorem faithful_Kw : FaithfulSMul (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K) := by
  refine ⟨fun {σ τ} h => ?_⟩
  apply Subtype.ext
  apply AlgEquiv.ext
  intro k
  have hk := h ((WithVal.toVal (w.valuation K) k : WithVal (w.valuation K)) : w.adicCompletion K)
  rw [smul_coe, smul_coe] at hk
  have := UniformSpace.Completion.coe_injective _
    (congrArg IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion hk)
  exact congrArg WithVal.ofVal this

theorem continuous_algebraMap_padic : Continuous (algebraMap ℚ_[qOf K w] (w.adicCompletion K)) := by
  show Continuous (fun x => algebraMap ((vQ K w).adicCompletion ℚ) (w.adicCompletion K) (padicIso K w x))
  apply Continuous.comp
  · exact IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ K (WExt K w)
  · exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (vQ K w)).symm.continuous

theorem algebraMap_padic_ratCast (r : ℚ) :
    algebraMap ℚ_[qOf K w] (w.adicCompletion K) (r : ℚ_[qOf K w]) = (r : w.adicCompletion K) := by
  rw [map_ratCast]

theorem smul_ratCast (σ : NumberField.PlaceDecomp.decomp E K w) (r : ℚ) :
    σ • (r : w.adicCompletion K) = (r : w.adicCompletion K) := by
  rw [NumberField.PlaceDecomp.smul_def, map_ratCast]

theorem smul_algebraMap_padic (σ : NumberField.PlaceDecomp.decomp E K w) (x : ℚ_[qOf K w]) :
    σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) x = algebraMap ℚ_[qOf K w] (w.adicCompletion K) x := by
  have hcont := continuous_algebraMap_padic K w
  have h1 : Continuous (fun x : ℚ_[qOf K w] => σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) x) := by
    have : (fun x : ℚ_[qOf K w] => σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) x) =
        (NumberField.PlaceDecomp.actRingEquiv σ) ∘ (algebraMap ℚ_[qOf K w] (w.adicCompletion K)) := by
      funext x; exact NumberField.PlaceDecomp.smul_def σ _
    rw [this]
    exact (NumberField.PlaceDecomp.continuous_actRingEquiv σ).comp hcont
  have key := DenseRange.equalizer (Padic.denseRange_ratCast (qOf K w)) h1 hcont (by
    funext r
    show σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) (r : ℚ_[qOf K w]) = algebraMap ℚ_[qOf K w] (w.adicCompletion K) (r : ℚ_[qOf K w])
    rw [algebraMap_padic_ratCast, smul_ratCast])
  exact congrFun key x

theorem natCast_qOf_mem : ((qOf K w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff (vQ K w) (n := qOf K w)).1 (dvd_refl _)
  rw [Ideal.mem_map_of_equiv] at h
  obtain ⟨x, hx, hxq⟩ := h

  have hx' : algebraMap (𝓞 ℚ) (𝓞 K) x ∈ w.asIdeal := hx
  have hxe : x = ((qOf K w : ℕ) : 𝓞 ℚ) := by
    apply (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective
    rw [hxq, map_natCast]
  rw [hxe, map_natCast] at hx'
  exact hx'

theorem faithful_img : @FaithfulSMul (NumberField.PlaceDecomp.decomp E K w) (Limg K w) (actImg K w E).toSMul := by
  refine @FaithfulSMul.mk _ _ (actImg K w E).toSMul (fun {σ τ} h => ?_)
  haveI := faithful_Kw K w E
  apply FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion K)
  intro x
  apply (PhiIso K w).injective
  rw [PhiIso_smul, PhiIso_smul]
  exact h _

end

end C8Bridge
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion.C8Bridge"

open C8Bridge in
open NumberField.PlaceDecomp in
theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (q : ℕ) (_ : Fact q.Prime) (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L')
      (_ : MulSemiringAction (decomp E K w) L') (_ : FaithfulSMul (decomp E K w) L')
      (_ : MulDistribMulAction (decomp E K w) (↥L')ˣ)
      (Φ : w.adicCompletion K ≃+* L'),
      (∀ (g : decomp E K w) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x) ∧
      (∀ (g : decomp E K w) (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L')) ∧
      (∀ (g : decomp E K w) (x : w.adicCompletion K), Φ (g • x) = g • Φ x) ∧
      ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  letI act : MulSemiringAction (decomp E K w) (Limg K w) := actImg K w E
  letI actU : MulDistribMulAction (decomp E K w) (↥(Limg K w))ˣ := Units.mulDistribMulActionRight
  refine ⟨qOf K w, qOf_prime K w, Limg K w, finLimg K w, act, faithful_img K w E, actU,
    (PhiIso K w).toRingEquiv, ?_, ?_, ?_, natCast_qOf_mem K w⟩
  ·
    intro g x
    show PhiIso K w (g • (PhiIso K w).symm (algebraMap ℚ_[qOf K w] (Limg K w) x)) = algebraMap ℚ_[qOf K w] (Limg K w) x
    rw [show (PhiIso K w).symm (algebraMap ℚ_[qOf K w] (Limg K w) x) = algebraMap ℚ_[qOf K w] (w.adicCompletion K) x from
      (PhiIso K w).symm.commutes x, smul_algebraMap_padic, AlgEquiv.commutes]
  ·
    intro g u
    rfl
  ·
    intro g x
    exact PhiIso_smul K w E g x

end S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion (solution)

-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/070b6169-c54f-55be-b36e-42ff951cbed1

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 800000

namespace C8tBridge

noncomputable section

variable (K : Type) [Field K] [NumberField K] (v₀ : HeightOneSpectrum (𝓞 ℚ)) (W : v₀.Extension (𝓞 K))

def qOf : ℕ := (Rat.HeightOneSpectrum.primesEquiv v₀ : Nat.Primes)
scoped instance qOf_prime : Fact (qOf v₀).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v₀).2⟩

scoped instance algQv : Algebra (v₀.adicCompletion ℚ) (W.1.adicCompletion K) := inferInstance
scoped instance finQv : Module.Finite (v₀.adicCompletion ℚ) (W.1.adicCompletion K) := inferInstance

def padicIso : ℚ_[qOf v₀] ≃+* v₀.adicCompletion ℚ :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v₀).symm.toAlgEquiv.toRingEquiv

scoped instance algPadicQv : Algebra ℚ_[qOf v₀] (v₀.adicCompletion ℚ) := (padicIso v₀).toRingHom.toAlgebra

scoped instance algPadic : Algebra ℚ_[qOf v₀] (W.1.adicCompletion K) :=
  ((algebraMap (v₀.adicCompletion ℚ) (W.1.adicCompletion K)).comp (padicIso v₀).toRingHom).toAlgebra

scoped instance towerPadic : IsScalarTower ℚ_[qOf v₀] (v₀.adicCompletion ℚ) (W.1.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance finPadicQv : Module.Finite ℚ_[qOf v₀] (v₀.adicCompletion ℚ) :=
  Module.Finite.of_surjective (Algebra.linearMap ℚ_[qOf v₀] (v₀.adicCompletion ℚ)) (padicIso v₀).surjective

scoped instance finPadic : Module.Finite ℚ_[qOf v₀] (W.1.adicCompletion K) :=
  Module.Finite.trans (v₀.adicCompletion ℚ) (W.1.adicCompletion K)

theorem algebraMap_padic_apply (x : ℚ_[qOf v₀]) :
    algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K) x =
      HeightOneSpectrum.Extension.adicCompletionSemialgHom ℚ K W (padicIso v₀ x) := rfl

def iota : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀) :=
  haveI : Algebra.IsAlgebraic ℚ_[qOf v₀] (W.1.adicCompletion K) := Algebra.IsAlgebraic.of_finite _ _
  IsAlgClosed.lift

def phi (f : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀)) : W.1.adicCompletion K ≃ₐ[ℚ_[qOf v₀]] f.fieldRange :=
  AlgEquiv.ofInjectiveField f

theorem coe_phi (f : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀)) (x : W.1.adicCompletion K) :
    ((phi K v₀ W f x : f.fieldRange) : PadicAlgCl (qOf v₀)) = f x := rfl

scoped instance finImg (f : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀)) : FiniteDimensional ℚ_[qOf v₀] f.fieldRange :=
  Module.Finite.equiv (phi K v₀ W f).toLinearEquiv

variable (E : Type) [Field E] [Algebra E K]

@[reducible] def actImg (f : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀)) :
    MulSemiringAction (NumberField.PlaceDecomp.decomp E K W.1) (f.fieldRange) where
  smul σ y := phi K v₀ W f (σ • (phi K v₀ W f).symm y)
  one_smul y := by
    show phi K v₀ W f ((1 : NumberField.PlaceDecomp.decomp E K W.1) • (phi K v₀ W f).symm y) = y
    rw [one_smul, AlgEquiv.apply_symm_apply]
  mul_smul σ τ y := by
    show phi K v₀ W f ((σ * τ) • (phi K v₀ W f).symm y) =
      phi K v₀ W f (σ • (phi K v₀ W f).symm (phi K v₀ W f (τ • (phi K v₀ W f).symm y)))
    rw [AlgEquiv.symm_apply_apply, mul_smul]
  smul_zero σ := by
    show phi K v₀ W f (σ • (phi K v₀ W f).symm 0) = 0
    rw [map_zero, smul_zero, map_zero]
  smul_add σ x y := by
    show phi K v₀ W f (σ • (phi K v₀ W f).symm (x + y)) =
      phi K v₀ W f (σ • (phi K v₀ W f).symm x) + phi K v₀ W f (σ • (phi K v₀ W f).symm y)
    rw [map_add, smul_add, map_add]
  smul_one σ := by
    show phi K v₀ W f (σ • (phi K v₀ W f).symm 1) = 1
    rw [map_one, smul_one, map_one]
  smul_mul σ x y := by
    show phi K v₀ W f (σ • (phi K v₀ W f).symm (x * y)) =
      phi K v₀ W f (σ • (phi K v₀ W f).symm x) * phi K v₀ W f (σ • (phi K v₀ W f).symm y)
    rw [map_mul, MulSemiringAction.smul_mul, map_mul]

theorem actImg_smul_def (f : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀))
    (σ : NumberField.PlaceDecomp.decomp E K W.1) (y : f.fieldRange) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K v₀ W E f).toSMul) σ y =
      phi K v₀ W f (σ • (phi K v₀ W f).symm y) := rfl

theorem phi_smul (f : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀))
    (σ : NumberField.PlaceDecomp.decomp E K W.1) (x : W.1.adicCompletion K) :
    phi K v₀ W f (σ • x) = @HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K v₀ W E f).toSMul) σ (phi K v₀ W f x) := by
  rw [actImg_smul_def, AlgEquiv.symm_apply_apply]

theorem smul_coe (σ : NumberField.PlaceDecomp.decomp E K W.1) (k : K) :
    σ • ((WithVal.toVal (W.1.valuation K) k : WithVal (W.1.valuation K)) : W.1.adicCompletion K) =
      ((WithVal.toVal (W.1.valuation K) ((σ : K ≃ₐ[E] K) k) : WithVal (W.1.valuation K)) : W.1.adicCompletion K) := by
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl

theorem faithful_Kw : FaithfulSMul (NumberField.PlaceDecomp.decomp E K W.1) (W.1.adicCompletion K) := by
  refine ⟨fun {σ τ} h => ?_⟩
  apply Subtype.ext
  apply AlgEquiv.ext
  intro k
  have hk := h ((WithVal.toVal (W.1.valuation K) k : WithVal (W.1.valuation K)) : W.1.adicCompletion K)
  rw [smul_coe, smul_coe] at hk
  have := UniformSpace.Completion.coe_injective _
    (congrArg IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion hk)
  exact congrArg WithVal.ofVal this

theorem faithful_img (f : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀)) :
    @FaithfulSMul (NumberField.PlaceDecomp.decomp E K W.1) f.fieldRange (actImg K v₀ W E f).toSMul := by
  refine @FaithfulSMul.mk _ _ (actImg K v₀ W E f).toSMul (fun {σ τ} h => ?_)
  haveI := faithful_Kw K v₀ W E
  apply FaithfulSMul.eq_of_smul_eq_smul (α := W.1.adicCompletion K)
  intro x
  apply (phi K v₀ W f).injective
  rw [phi_smul, phi_smul]
  exact h _

theorem continuous_algebraMap_padic : Continuous (algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K)) := by
  show Continuous (fun x => algebraMap (v₀.adicCompletion ℚ) (W.1.adicCompletion K) (padicIso v₀ x))
  apply Continuous.comp
  · exact IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ K W
  · exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v₀).symm.continuous

theorem smul_ratCast (σ : NumberField.PlaceDecomp.decomp E K W.1) (r : ℚ) :
    σ • (r : W.1.adicCompletion K) = (r : W.1.adicCompletion K) := by
  rw [NumberField.PlaceDecomp.smul_def, map_ratCast]

theorem smul_algebraMap_padic (σ : NumberField.PlaceDecomp.decomp E K W.1) (x : ℚ_[qOf v₀]) :
    σ • algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K) x = algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K) x := by
  have hcont := continuous_algebraMap_padic K v₀ W
  have h1 : Continuous (fun x : ℚ_[qOf v₀] => σ • algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K) x) := by
    have : (fun x : ℚ_[qOf v₀] => σ • algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K) x) =
        (NumberField.PlaceDecomp.actRingEquiv σ) ∘ (algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K)) := by
      funext x; exact NumberField.PlaceDecomp.smul_def σ _
    rw [this]
    exact (NumberField.PlaceDecomp.continuous_actRingEquiv σ).comp hcont
  have key := DenseRange.equalizer (Padic.denseRange_ratCast (qOf v₀)) h1 hcont (by
    funext r
    show σ • algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K) (r : ℚ_[qOf v₀]) = algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K) (r : ℚ_[qOf v₀])
    rw [map_ratCast, smul_ratCast])
  exact congrFun key x

theorem smul_algebraMap_img (f : W.1.adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀))
    (σ : NumberField.PlaceDecomp.decomp E K W.1) (x : ℚ_[qOf v₀]) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K v₀ W E f).toSMul) σ (algebraMap ℚ_[qOf v₀] f.fieldRange x) =
      algebraMap ℚ_[qOf v₀] f.fieldRange x := by
  rw [actImg_smul_def, show (phi K v₀ W f).symm (algebraMap ℚ_[qOf v₀] f.fieldRange x) =
      algebraMap ℚ_[qOf v₀] (W.1.adicCompletion K) x from (phi K v₀ W f).symm.commutes x,
    smul_algebraMap_padic, AlgEquiv.commutes]

theorem natCast_qOf_mem : ((qOf v₀ : ℕ) : 𝓞 K) ∈ W.1.asIdeal := by
  have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff v₀ (n := qOf v₀)).1 (dvd_refl _)
  rw [Ideal.mem_map_of_equiv] at h
  obtain ⟨x, hx, hxq⟩ := h
  have hxe : x = ((qOf v₀ : ℕ) : 𝓞 ℚ) := by
    apply (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective
    rw [hxq, map_natCast]
  rw [hxe] at hx
  have hx2 : ((qOf v₀ : ℕ) : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) W.1).asIdeal := by rw [W.2]; exact hx
  have hx' : algebraMap (𝓞 ℚ) (𝓞 K) ((qOf v₀ : ℕ) : 𝓞 ℚ) ∈ W.1.asIdeal := hx2
  rwa [map_natCast] at hx'

end

end C8tBridge
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower.C8tBridge"

open C8tBridge NumberField.PlaceDecomp in
theorem solution
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K''] [IsGalois E K]
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    ∃ (q : ℕ) (_ : Fact q.Prime) (L L'' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : L ≤ L'')
      (_ : FiniteDimensional ℚ_[q] L) (_ : FiniteDimensional ℚ_[q] L'')
      (_ : MulSemiringAction (decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) L)
      (_ : FaithfulSMul (decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) L)
      (_ : MulDistribMulAction (decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (↥L)ˣ)
      (_ : MulSemiringAction (decomp E K'' w'') L'') (_ : FaithfulSMul (decomp E K'' w'') L'')
      (_ : MulDistribMulAction (decomp E K'' w'') (↥L'')ˣ)
      (Φ : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K ≃+* L) (Φ'' : w''.adicCompletion K'' ≃+* L''),
      (∀ (g : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (x : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K),
          Φ (g • x) = g • Φ x) ∧
      (∀ (g : decomp E K'' w'') (x : w''.adicCompletion K''), Φ'' (g • x) = g • Φ'' x) ∧
      (∀ (g : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) ∧
      (∀ (g : decomp E K'' w'') (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x) ∧
      (∀ (g : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)) ∧
      (∀ (g : decomp E K'' w'') (u : (↥L'')ˣ), ((g • u : (↥L'')ˣ) : L'') = g • (u : L'')) ∧
      (∀ x : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K,
        ((Φ'' (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
            (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')) x) : L'') : PadicAlgCl q) =
          ((Φ x : L) : PadicAlgCl q)) ∧
      ((q : ℕ) : 𝓞 K'') ∈ w''.asIdeal := by
  classical
  let v₀ : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.under (𝓞 ℚ) (HeightOneSpectrum.under (𝓞 K) w'')
  have h'' : HeightOneSpectrum.under (𝓞 ℚ) w'' = v₀ :=
    (IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers ℚ K K'' w'').symm
  let WK : v₀.Extension (𝓞 K) := ⟨HeightOneSpectrum.under (𝓞 K) w'', rfl⟩
  let WK'' : v₀.Extension (𝓞 K'') := ⟨w'', h''⟩
  letI aK : Algebra ℚ_[qOf v₀] ((HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K) := algPadic K v₀ WK
  letI aK'' : Algebra ℚ_[qOf v₀] (w''.adicCompletion K'') := algPadic K'' v₀ WK''
  let ι'' : w''.adicCompletion K'' →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀) := iota K'' v₀ WK''

  let j : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K →ₐ[ℚ_[qOf v₀]] w''.adicCompletion K'' :=
    { (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
          (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K''))).toRingHom with
      commutes' := fun x => by
        show HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
            (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K''))
            (algebraMap ℚ_[qOf v₀] ((HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K) x) =
          algebraMap ℚ_[qOf v₀] (w''.adicCompletion K'') x
        rw [algebraMap_padic_apply K v₀ WK, algebraMap_padic_apply K'' v₀ WK'']
        exact IsDedekindDomain.HeightOneSpectrum.adicCompletionSemialgHom_comp_of_tower ℚ K K'' w'' h'' (padicIso v₀ x) }
  have hj : ∀ x, j x = HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
      (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')) x := fun _ => rfl
  let ιK : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K →ₐ[ℚ_[qOf v₀]] PadicAlgCl (qOf v₀) := ι''.comp j
  have hLL : ιK.fieldRange ≤ ι''.fieldRange := by
    rintro _ ⟨x, rfl⟩
    exact ⟨j x, rfl⟩
  letI actK : MulSemiringAction (decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) ιK.fieldRange := actImg K v₀ WK E ιK
  letI actK'' : MulSemiringAction (decomp E K'' w'') ι''.fieldRange := actImg K'' v₀ WK'' E ι''
  letI uK : MulDistribMulAction (decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) (↥ιK.fieldRange)ˣ :=
    Units.mulDistribMulActionRight
  letI uK'' : MulDistribMulAction (decomp E K'' w'') (↥ι''.fieldRange)ˣ := Units.mulDistribMulActionRight
  refine ⟨qOf v₀, qOf_prime v₀, ιK.fieldRange, ι''.fieldRange, hLL, finImg K v₀ WK ιK, finImg K'' v₀ WK'' ι'',
    actK, faithful_img K v₀ WK E ιK, uK, actK'', faithful_img K'' v₀ WK'' E ι'', uK'',
    (phi K v₀ WK ιK).toRingEquiv, (phi K'' v₀ WK'' ι'').toRingEquiv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, natCast_qOf_mem K'' v₀ WK''⟩
  · intro g x; exact phi_smul K v₀ WK E ιK g x
  · intro g x; exact phi_smul K'' v₀ WK'' E ι'' g x
  · intro g x; exact smul_algebraMap_img K v₀ WK E ιK g x
  · intro g x; exact smul_algebraMap_img K'' v₀ WK'' E ι'' g x
  · intro g u; rfl
  · intro g u; rfl
  · intro x; rfl

end S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower (solution)

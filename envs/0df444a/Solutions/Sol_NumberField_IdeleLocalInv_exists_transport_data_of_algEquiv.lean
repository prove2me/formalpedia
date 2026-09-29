-- Prove2me | solution 1 for NumberField.IdeleLocalInv.exists_transport_data_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0f3db8b2-8897-5739-a123-a3b0eb428ef8

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleLocalInv_exists_transport_data_of_algEquiv
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_IdeleLocalInv_exists_transport_data_of_algEquiv.NumberField IsDedekindDomain M4aHerbrand"
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NumberField
p2m_export "NumberField" "AdeleRing PlaceDecomp.decomp PlaceDecomp.actRingEquiv PlaceDecomp.actRingEquiv_coe PlaceDecomp.continuous_actRingEquiv PlaceDecomp.smul_def PlaceTransport.mem_smul_asIdeal_iff PlaceTransport.valuation_smul_apply PlaceTransport.valuation_apply_of_smul_eq PlaceTransport.transport PlaceTransport.transport_coe PlaceTransport.continuous_transport PlaceTransport.stabilizer_eq_decomp"
namespace IdeleLocalInv
namespace SigmaTransport
p2m_open "NumberField.IdeleLocalInv NumberField"

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
  (σK : K ≃ₐ[ℚ] K) (τ : E ≃+* E) (hστ : ∀ x : E, σK (algebraMap E K x) = algebraMap E K (τ x))

include hστ in
theorem symm_algebraMap (x : E) : σK.symm (algebraMap E K x) = algebraMap E K (τ.symm x) := by
  apply σK.injective
  rw [AlgEquiv.apply_symm_apply, hστ, RingEquiv.apply_symm_apply]

noncomputable def conjAlgEquiv (g : K ≃ₐ[E] K) : K ≃ₐ[E] K :=
  AlgEquiv.ofRingEquiv (f := (σK.symm.toRingEquiv.trans (g : K ≃+* K)).trans σK.toRingEquiv) (fun x => by
    show σK (g (σK.symm (algebraMap E K x))) = algebraMap E K x
    rw [symm_algebraMap σK τ hστ, AlgEquiv.commutes, hστ, RingEquiv.apply_symm_apply])

theorem conjAlgEquiv_apply (g : K ≃ₐ[E] K) (y : K) : conjAlgEquiv σK τ hστ g y = σK (g (σK.symm y)) := rfl

noncomputable def conjAlgEquivInv (g : K ≃ₐ[E] K) : K ≃ₐ[E] K :=
  AlgEquiv.ofRingEquiv (f := (σK.toRingEquiv.trans (g : K ≃+* K)).trans σK.symm.toRingEquiv) (fun x => by
    show σK.symm (g (σK (algebraMap E K x))) = algebraMap E K x
    rw [hστ, AlgEquiv.commutes, symm_algebraMap σK τ hστ, RingEquiv.symm_apply_apply])

theorem conjAlgEquivInv_apply (g : K ≃ₐ[E] K) (y : K) : conjAlgEquivInv σK τ hστ g y = σK.symm (g (σK y)) := rfl

noncomputable def conj : (K ≃ₐ[E] K) ≃* (K ≃ₐ[E] K) where
  toFun := conjAlgEquiv σK τ hστ
  invFun := conjAlgEquivInv σK τ hστ
  left_inv g := AlgEquiv.ext fun y => by simp [conjAlgEquiv_apply, conjAlgEquivInv_apply]
  right_inv g := AlgEquiv.ext fun y => by simp [conjAlgEquiv_apply, conjAlgEquivInv_apply]
  map_mul' a b := AlgEquiv.ext fun y => by simp [conjAlgEquiv_apply, AlgEquiv.mul_apply]

theorem conj_apply (g : K ≃ₐ[E] K) (y : K) : conj σK τ hστ g y = σK (g (σK.symm y)) := rfl
theorem conj_symm_apply (g : K ≃ₐ[E] K) (y : K) : (conj σK τ hστ).symm g y = σK.symm (g (σK y)) := rfl

theorem restrictScalars_conj (g : K ≃ₐ[E] K) :
    (conj σK τ hστ g).restrictScalars ℚ = σK * g.restrictScalars ℚ * σK.symm := AlgEquiv.ext fun y => rfl

theorem restrictScalars_conj_symm (g : K ≃ₐ[E] K) :
    ((conj σK τ hστ).symm g).restrictScalars ℚ = σK.symm * g.restrictScalars ℚ * σK := AlgEquiv.ext fun y => rfl

end NumberField.IdeleLocalInv.SigmaTransport

open NumberField.IdeleLocalInv.SigmaTransport in
set_option maxHeartbeats 6400000 in

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

    (σK : K ≃ₐ[ℚ] K) (τ : E ≃+* E) (hστ : ∀ x : E, σK (algebraMap E K x) = algebraMap E K (τ x))

    (D : IdeleGaloisDescent (𝓞 K) E K) [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (z : (AdeleRing (𝓞 K) K)ˣ), g • z = D.unitsAct g z) :
    ∃ (c : (K ≃ₐ[E] K) ≃* (K ≃ₐ[E] K))
      (pl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K))
      (hcd : ∀ (w : HeightOneSpectrum (𝓞 K)) (g : K ≃ₐ[E] K), g ∈ NumberField.PlaceDecomp.decomp E K w → c g ∈ NumberField.PlaceDecomp.decomp E K (pl w))
      (Tc : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K ≃+* (pl w).adicCompletion K)
      (ψ : Rep.res c.symm.toMonoidHom (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ),

      (∀ (g : K ≃ₐ[E] K) (y : K), c g (σK y) = σK (g y)) ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), (pl w).valuation K (σK y) = w.valuation K y) ∧
      Function.Bijective pl ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), Tc w (y : w.adicCompletion K) = ((σK y : K) : (pl w).adicCompletion K)) ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K),
          Tc w (g • y) = (⟨c g, hcd w g g.2⟩ : ↥(NumberField.PlaceDecomp.decomp E K (pl w))) • Tc w y) ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ),
          finPart (pl w) (Additive.toMul (ψ.hom (Additive.ofMul z))) = Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K) (finPart w z)) := by
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let c := conj σK τ hστ
  let pl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K) := fun w => σK • w
  have hpl : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), (pl w).valuation K (σK y) = w.valuation K y :=
    fun w y => NumberField.PlaceTransport.valuation_smul_apply σK w y

  have hcd : ∀ (w : HeightOneSpectrum (𝓞 K)) (g : K ≃ₐ[E] K), g ∈ NumberField.PlaceDecomp.decomp E K w →
      c g ∈ NumberField.PlaceDecomp.decomp E K (pl w) := by
    intro w g hg
    have hg' : g⁻¹ • w = w := by
      have : g⁻¹ ∈ MulAction.stabilizer (K ≃ₐ[E] K) w := by
        rw [NumberField.PlaceTransport.stabilizer_eq_decomp]; exact inv_mem hg
      exact this
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp, MulAction.mem_stabilizer_iff]
    apply HeightOneSpectrum.ext
    ext r
    have key : (pl w).valuation K (algebraMap (𝓞 K) K ((c g)⁻¹ • r)) = (pl w).valuation K (algebraMap (𝓞 K) K r) := by
      show (pl w).valuation K ((c g)⁻¹ (r : K)) = (pl w).valuation K (r : K)
      rw [← map_inv, show c g⁻¹ (r : K) = σK (g⁻¹ (σK.symm (r : K))) from rfl, hpl,
        NumberField.PlaceTransport.valuation_apply_of_smul_eq hg', ← hpl w (σK.symm (r : K)), AlgEquiv.apply_symm_apply]
    rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), key]
  let Tc : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K ≃+* (pl w).adicCompletion K :=
    fun w => NumberField.PlaceTransport.transport σK (rfl : σK • w = pl w)
  have hTc : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), Tc w (y : w.adicCompletion K) = ((σK y : K) : (pl w).adicCompletion K) :=
    fun w y => NumberField.PlaceTransport.transport_coe σK rfl _

  have hTcs : ∀ (w : HeightOneSpectrum (𝓞 K)) (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K),
      Tc w (g • y) = (⟨c g, hcd w g g.2⟩ : ↥(NumberField.PlaceDecomp.decomp E K (pl w))) • Tc w y := by
    intro w g y
    rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
    obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w y
    induction y using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (((NumberField.PlaceTransport.continuous_transport σK rfl).comp
          (NumberField.PlaceDecomp.continuous_actRingEquiv g)).comp
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
        (((NumberField.PlaceDecomp.continuous_actRingEquiv _).comp
          (NumberField.PlaceTransport.continuous_transport σK rfl)).comp
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
    | ih a =>
    have := (show Tc w (NumberField.PlaceDecomp.actRingEquiv g (a : w.adicCompletion K)) =
          NumberField.PlaceDecomp.actRingEquiv (⟨c g, hcd w g g.2⟩ : ↥(NumberField.PlaceDecomp.decomp E K (pl w))) (Tc w (a : w.adicCompletion K)) from by
        show Tc w (NumberField.PlaceDecomp.actRingEquiv g (a : w.adicCompletion K)) =
          NumberField.PlaceDecomp.actRingEquiv (⟨c g, hcd w g g.2⟩ : ↥(NumberField.PlaceDecomp.decomp E K (pl w))) (Tc w (a : w.adicCompletion K))
        rw [NumberField.PlaceDecomp.actRingEquiv_coe, NumberField.PlaceTransport.transport_coe, NumberField.PlaceTransport.transport_coe,
          NumberField.PlaceDecomp.actRingEquiv_coe]
        simp only [WithVal.congr_apply]
        congr 1
        congr 1
        refine congrArg (WithVal.toVal (HeightOneSpectrum.valuation K (pl w))) ?_
        show σK ((g : K ≃ₐ[E] K) (WithVal.ofVal a)) = σK ((g : K ≃ₐ[E] K) (σK.symm (σK (WithVal.ofVal a))))
        rw [AlgEquiv.symm_apply_apply])
    exact this

  let Dℚ := M4aHerbrand.GenuineDescent.genuineDescentDatum ℚ K
  let rs : (K ≃ₐ[E] K) →* (K ≃ₐ[ℚ] K) :=
    { toFun := fun g => g.restrictScalars ℚ, map_one' := rfl, map_mul' := fun a b => rfl }
  let D₂ : IdeleGaloisDescent (𝓞 K) E K :=
    { act := Dℚ.act.comp rs
      compat := fun g x => Dℚ.compat (g.restrictScalars ℚ) x
      continuous_act := fun g => Dℚ.continuous_act (g.restrictScalars ℚ) }
  have hD : D = D₂ := by
    haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 K) E K
    exact Subsingleton.elim _ _
  have hact : ∀ (g : K ≃ₐ[E] K) (z : (AdeleRing (𝓞 K) K)ˣ), g • z = Dℚ.unitsAct (g.restrictScalars ℚ) z := by
    intro g z
    rw [hactI, hD]
    rfl

  let ψ : Rep.res c.symm.toMonoidHom (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
      Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ :=
    Rep.ofHom ⟨(MonoidHom.toAdditive (Dℚ.unitsAct σK).toMonoidHom).toIntLinearMap, fun g => LinearMap.ext fun z => by
      change Additive.ofMul (Dℚ.unitsAct σK ((c.symm g) • (Additive.toMul z : (AdeleRing (𝓞 K) K)ˣ))) =
        Additive.ofMul (g • Dℚ.unitsAct σK (Additive.toMul z : (AdeleRing (𝓞 K) K)ˣ))
      rw [hact, hact, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul, restrictScalars_conj_symm]
      congr 2
      congr 1
      show σK * (σK⁻¹ * g.restrictScalars ℚ * σK) = g.restrictScalars ℚ * σK
      group⟩
  have hψ : ∀ (w : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ),
      finPart (pl w) (Additive.toMul (ψ.hom (Additive.ofMul z))) = Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K) (finPart w z) := by
    intro w z
    apply Units.ext
    show ((Dℚ.act σK (z : AdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K).2 (pl w) = Tc w (((z : AdeleRing (𝓞 K) K)).2 w)
    exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply ℚ K σK (z : AdeleRing (𝓞 K) K) rfl
  refine ⟨c, pl, hcd, Tc, ψ, fun g y => ?_, hpl, MulAction.bijective σK, hTc, hTcs, hψ⟩
  show σK (g (σK.symm (σK y))) = σK (g y)
  rw [AlgEquiv.symm_apply_apply]

end S_NumberField_IdeleLocalInv_exists_transport_data_of_algEquiv
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_exists_transport_data_of_algEquiv (solution)

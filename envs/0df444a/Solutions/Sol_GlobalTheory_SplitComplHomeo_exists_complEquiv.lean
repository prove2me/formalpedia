-- Prove2me | solution 1 for GlobalTheory.SplitComplHomeo.exists_complEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:39.577519+00:00
-- url     : https://prove2.me/submissions/cdb492aa-c8a8-45c8-85a2-492e85c956fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsComplEquiv
import Theorems.Thm_PI_CompAtExist_stepA
import Theorems.Thm_ReciprocityTheory_Aut_SplitPlace_w_under


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open GlobalTheory GlobalTheory.SplitComplHomeo
open scoped WithZeroTopology
namespace GlobalTheory.SplitComplHomeo
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L,
      Continuous i ∧ Continuous i.symm ∧ ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro E _ _ _ s
  have : s.w.asIdeal.LiesOver s.v.asIdeal := ⟨s.w_under.symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (maximalRealSubfield E) E s.v s.w).continuous
  let φ : s.v.adicCompletion (maximalRealSubfield E) →+* s.w.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E s.w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv (maximalRealSubfield E) s.v).toRingHom
  have hφ : ∀ x : maximalRealSubfield E, φ (algebraMap (maximalRealSubfield E) _ x) =
      algebraMap E _ (algebraMap (maximalRealSubfield E) E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E s.w).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion (maximalRealSubfield E) s.v))
  have hi : ∀ x : E, φ (s.i x) = algebraMap E (s.w.adicCompletion E) x := fun x => by
    have key : ∀ y, Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x) := fun y =>
      (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) s.v).induction_on
        (p := fun y => Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x)) y
        (isClosed_eq
          ((Valued.continuous_valuation_of_surjective (s.w.valuedAdicCompletion_surjective E)).comp
            (hcont.sub continuous_const))
          ((Valued.continuous_valuation_of_surjective (s.v.valuedAdicCompletion_surjective _)).comp
            (continuous_id.sub continuous_const))) fun k => by
        rw [hφ, ← map_sub, ← PI.CompAtExist.stepA s, map_sub, AlgHom.commutes]
    have h0 := key (s.i x)
    rw [sub_self, map_zero, map_eq_zero, sub_eq_zero] at h0
    exact h0
  letI : Algebra (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) := φ.toAlgebra
  haveI : ContinuousSMul (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ hcont
  letI : NontriviallyNormedField (s.v.adicCompletion (maximalRealSubfield E)) :=
    Valued.toNontriviallyNormedField _ _
  have hs : Function.Surjective φ := by
    have hcl : IsClosed (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E)) := Submodule.closed_of_finiteDimensional _
    intro y
    exact (HeightOneSpectrum.denseRange_algebraMap E s.w).induction_on
      (p := fun y => y ∈ (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E))) y hcl fun x => ⟨s.i x, hi x⟩
  let e : s.v.adicCompletion (maximalRealSubfield E) ≃ₗ[s.v.adicCompletion (maximalRealSubfield E)]
      s.w.adicCompletion E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) ⟨φ.injective, hs⟩
  haveI : FiniteDimensional (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    e.finiteDimensional
  have hinv : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  refine ⟨RingEquiv.ofBijective φ ⟨φ.injective, hs⟩, hcont, hinv.congr fun y => ?_, hi⟩
  exact (RingEquiv.symm_apply_eq _).2 (e.apply_symm_apply y).symm |>.symm
end GlobalTheory.SplitComplHomeo

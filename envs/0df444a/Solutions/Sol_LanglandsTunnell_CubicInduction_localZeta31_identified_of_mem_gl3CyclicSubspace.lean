-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.localZeta31_identified_of_mem_gl3CyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/dab323d4-25c9-5634-8766-7acc3464ffaa

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_localZeta31_identified_of_mem_gl3CyclicSubspace

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open LanglandsTunnell.TateLocal

namespace Ws23IdCyc

section Fibre
variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

theorem ringHom_ratInt_ext {T : Type*} [NonAssocSemiring T] (f g : 𝓞 ℚ →+* T) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  ext x
  have h2 := RingHom.congr_fun h (Rat.ringOfIntegersEquiv x)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply] at h2
  exact h2

theorem algebraMap_OO_injective : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) := by
  have h := ringHom_ratInt_ext (algebraMap (𝓞 ℚ) (𝓞 K))
    ((algebraMap ℤ (𝓞 K)).comp Rat.ringOfIntegersEquiv.toRingHom)
  rw [h]
  exact (algebraMap ℤ (𝓞 K)).injective_int.comp Rat.ringOfIntegersEquiv.injective

theorem isTorsionFree_OO : Module.IsTorsionFree (𝓞 ℚ) (𝓞 K) :=
  (Module.isTorsionFree_iff_algebraMap_injective).2 (algebraMap_OO_injective K)

theorem mem_primeFibre_iff (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    𝔓 ∈ primeFibre ℚ K p ↔ 𝔓.asIdeal ∈ p.asIdeal.primesOver (𝓞 K) := by
  rw [mem_primeFibre]
  constructor
  · intro h
    refine ⟨𝔓.isPrime, (Ideal.liesOver_iff _ _).2 ?_⟩
    rw [← h, HeightOneSpectrum.under_asIdeal]
  · rintro ⟨-, hover⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, ← (Ideal.liesOver_iff _ _).1 hover]

theorem primeFibre_finite (p : HeightOneSpectrum (𝓞 ℚ)) : (primeFibre ℚ K p).Finite := by
  haveI := p.isMaximal
  haveI := isTorsionFree_OO K
  have h : primeFibre ℚ K p = (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) ⁻¹' p.asIdeal.primesOver (𝓞 K) := by
    ext 𝔓; exact mem_primeFibre_iff K p 𝔓
  rw [h]
  exact (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)).preimage
    fun _ _ _ _ h => HeightOneSpectrum.ext h

theorem absNorm_eq_pow_of_mem_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 K))
    (h𝔓 : 𝔓 ∈ primeFibre ℚ K p) :
    Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm p.asIdeal ^ Ideal.inertiaDeg' p.asIdeal 𝔓.asIdeal := by
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  haveI : 𝔓.asIdeal.LiesOver p.asIdeal := ((mem_primeFibre_iff K p 𝔓).1 h𝔓).2
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal p.asIdeal p.isPrime p.ne_bot

theorem factor_monomial (q : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K)) (hw : w ∈ primeFibre ℚ K q)
    (e : ℂ) (a : ℤ) :
    ∃ (c : ℂ) (k : ℤ), ∀ s : ℂ,
      e * ((((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ a) =
        c * (Ideal.absNorm q.asIdeal : ℂ) ^ ((k : ℂ) * s) := by
  have hN : (Ideal.absNorm q.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.mpr q.ne_bot)
  set f : ℕ := Ideal.inertiaDeg' q.asIdeal w.asIdeal with hf
  refine ⟨e * (Ideal.absNorm q.asIdeal : ℂ) ^ (((a * f : ℤ) : ℂ) / 2), -(a * f), fun s => ?_⟩
  have hNw : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) = (Ideal.absNorm q.asIdeal : ℂ) ^ f := by
    rw [absNorm_eq_pow_of_mem_primeFibre K q w hw, Nat.cast_pow]
  rw [hNw, ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_int_mul, mul_assoc,
    ← Complex.cpow_add _ _ hN]
  congr 2
  push_cast
  ring

theorem fibre_monomial (q : HeightOneSpectrum (𝓞 ℚ)) (ε : HeightOneSpectrum (𝓞 K) → ℂ) (a : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ (C : ℂ) (k : ℤ), ∀ s : ℂ,
      (∏ᶠ w ∈ primeFibre ℚ K q, ε w * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (a w)) =
        C * (Ideal.absNorm q.asIdeal : ℂ) ^ ((k : ℂ) * s) := by
  classical
  have hN : (Ideal.absNorm q.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.mpr q.ne_bot)
  have hfin := primeFibre_finite K q

  suffices h : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), (↑T : Set (HeightOneSpectrum (𝓞 K))) ⊆ primeFibre ℚ K q →
      ∃ (C : ℂ) (k : ℤ), ∀ s : ℂ,
        (∏ w ∈ T, ε w * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (a w)) =
          C * (Ideal.absNorm q.asIdeal : ℂ) ^ ((k : ℂ) * s) by
    obtain ⟨C, k, hCk⟩ := h hfin.toFinset (by simp)
    exact ⟨C, k, fun s => by rw [finprod_mem_eq_finite_toFinset_prod _ hfin]; exact hCk s⟩
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, 0, fun s => by simp⟩
  | insert w T hwT ih =>
    intro hsub
    rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
    obtain ⟨C, k, hCk⟩ := ih hsub.2
    obtain ⟨c, k', hck⟩ := factor_monomial K q w hsub.1 (ε w) (a w)
    refine ⟨c * C, k' + k, fun s => ?_⟩
    rw [Finset.prod_insert hwT, hck s, hCk s, mul_mul_mul_comm, ← Complex.cpow_add _ _ hN]
    congr 2
    push_cast
    ring

end Fibre

end Ws23IdCyc

open Ws23IdCyc in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (q : HeightOneSpectrum (𝓞 ℚ))
    (W₃ : LocalGL3 q → ℂ) (lam : ℂ)
    (hId :
      ∀ b : ℕ,
        (∀ w ∈ primeFibre ℚ K q,
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ (η : (q.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ q η cη → cη ≤ b →
          ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
            NumberField.TateGlobal.localChar ηA q = η →
            LanglandsTunnell.Converse.IsAdmissibleTwist K
              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
            ∀ g : LocalGL3 q,
              letI := LanglandsTunnell.TateLocal.localBorel ℚ q
              ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                IsLocalZeta30ConvergentAbove q
                  (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                  W₃ η g σ₀ ∧
                (∀ s : ℂ, σ₀ < s.re →
                  localZeta30 q
                      (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                      W₃ η s g *
                    Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                IsLocalZeta31ConvergentAbove q
                  (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                  (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) (dualWhittakerFn3 W₃) η⁻¹
                  (weylPrime3 * transposeInv3 g) σ₁ ∧
                (∀ s : ℂ, σ₁ < (1 - s).re →
                  localZetaDual31 q
                      (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                      (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) W₃ η (1 - s) g *
                    Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                    (lam *
                      (∏ᶠ w ∈ primeFibre ℚ K q,
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ primeFibre ℚ K q,
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))))
    (W : LocalGL3 q → ℂ) (hW : W ∈ gl3CyclicSubspace W₃) :
    ∀ b : ℕ,
      (∀ w ∈ primeFibre ℚ K q,
        2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
          LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
      ∀ (η : (q.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ q η cη → cη ≤ b →
        ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
          NumberField.TateGlobal.localChar ηA q = η →
          LanglandsTunnell.Converse.IsAdmissibleTwist K
            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
          ∀ g : LocalGL3 q,
            letI := LanglandsTunnell.TateLocal.localBorel ℚ q
            ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
              IsLocalZeta30ConvergentAbove q
                (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                W η g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 q
                    (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                    W η s g *
                  Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
              IsLocalZeta31ConvergentAbove q
                (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) (dualWhittakerFn3 W) η⁻¹
                (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 q
                    (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) W η (1 - s) g *
                  Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                  (lam *
                    (∏ᶠ w ∈ primeFibre ℚ K q,
                      ((NumberField.TateGlobal.localChar
                        (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                    (∏ᶠ w ∈ primeFibre ℚ K q,
                      (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                          (NumberField.TateGlobal.localChar
                            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                        (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                          (LanglandsTunnell.Converse.pinnedExp K
                            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))) := by
  intro b hb η cη hη hcb ηA hηA hloc hBC g
  obtain ⟨C, k, hCk⟩ := fibre_monomial K q
    (fun w => LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))
    (fun w => LanglandsTunnell.Converse.pinnedExp K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)

  have hconst : ∀ s : ℂ,
      lam * (∏ᶠ w ∈ primeFibre ℚ K q,
                  ((NumberField.TateGlobal.localChar
                    (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * (∏ᶠ w ∈ primeFibre ℚ K q,
                  (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                      (NumberField.TateGlobal.localChar
                        (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                    (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                      (LanglandsTunnell.Converse.pinnedExp K
                        (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))) =
        (lam * (∏ᶠ w ∈ primeFibre ℚ K q,
                    ((NumberField.TateGlobal.localChar
                      (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * C) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((k : ℂ) * s) := by
    intro s
    rw [hCk s]
    ring
  have h31 := LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe q W₃ η
    (lam * (∏ᶠ w ∈ primeFibre ℚ K q,
                    ((NumberField.TateGlobal.localChar
                      (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) * C) k
    (fun g' => by
      obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, h1, h2, h3, h4⟩ := hId b hb η cη hη hcb ηA hηA hloc hBC g'
      exact ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, h1, h2, h3, fun s hs => by rw [h4 s hs, hconst s]⟩)
  obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, h1, h2, h3, h4⟩ := h31 W hW g
  exact ⟨Q₁, Q₂, n, σ₀, σ₁, hQ, h1, h2, h3, fun s hs => by rw [h4 s hs, hconst s]⟩

end S_LanglandsTunnell_CubicInduction_localZeta31_identified_of_mem_gl3CyclicSubspace
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_localZeta31_identified_of_mem_gl3CyclicSubspace (solution)
